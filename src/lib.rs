use cranelift_codegen::ir;
use cranelift_codegen::ir::InstBuilder;
use cranelift_codegen::isa;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use wit_parser::{Parser as WitParser, Section};

pub trait Environment {
    type Instance;
    type HostFunction;

    fn interface(&self, instance: &Self::Instance) -> &Interface;
    fn function_type(&self, instance: &Self::Instance, func_idx: FunctionIdx) -> Type;

    fn emit_call_core(
        &self,
        instance: &Self::Instance,
        func_idx: FunctionIdx,
        params: &[Val],
        builder: &mut FunctionBuilder,
    ) -> Vec<Val>;

    fn emit_call_host(
        &self,
        instance: &Self::Instance,
        func: &Self::HostFunction,
        params: &[Val],
        builder: &mut FunctionBuilder,
    ) -> Vec<Val>;

    fn host_export_signature(&self, ty: &Type) -> ir::Signature;
    fn host_export_prologue(&self, ty: &Type, builder: &mut FunctionBuilder) -> Vec<Val>;
    fn host_export_epilogue(&self, ty: &Type, results: &[Val], builder: &mut FunctionBuilder);
}

pub type TypeIdx = usize;
pub type ImportIdx = usize;
pub type ExportIdx = usize;
pub type AdapterIdx = usize;
pub type ImplementIdx = usize;
pub type ArgumentIdx = usize;
pub type FunctionIdx = usize;
pub type MemoryIdx = usize;

pub const WASM_CALL_CONV: isa::CallConv = isa::CallConv::BaldrdashSystemV;
pub const POINTER_TYPE: ir::Type = ir::types::I64;
pub const POINTER_SIZE: usize = 8;
pub const REF_TYPE: ir::Type = ir::types::R64;

pub enum ImportValue<'a, E: Environment> {
    Wasm(ExportIdx, &'a E::Instance),
    Host(&'a E::HostFunction),
}

#[derive(Debug, Clone, Default)]
pub struct Interface {
    pub types: Vec<Type>,
    pub imports: Vec<Import>,
    pub exports: Vec<Export>,
    pub adapters: Vec<AdapterFunction>,
    pub implements: Vec<Implement>,
}

impl Interface {
    pub fn parse(offset: usize, bytes: &[u8]) -> Result<Self, String> {
        let mut parser = WitParser::new(offset, bytes).unwrap();
        let mut interface = Interface::default();

        while !parser.is_empty() {
            let section = parser.section().unwrap();

            match section {
                Section::Type(types) => {
                    interface.types = types.map(|x| x.unwrap().into()).collect();
                }
                Section::Import(imports) => {
                    interface.imports = imports.map(|x| x.unwrap().into()).collect();
                }
                Section::Export(exports) => {
                    interface.exports = exports.map(|x| x.unwrap().into()).collect();
                }
                Section::Func(funcs) => {
                    interface.adapters = funcs.map(|x| x.unwrap().into()).collect();
                }
                Section::Implement(implements) => {
                    interface.implements = implements.map(|x| x.unwrap().into()).collect();
                }
            }
        }

        eprintln!("{:#?}", interface);
        Ok(interface)
    }

    /// Emits an adapted function that implements a core-import for this interface and follows the Wasm ABI.
    pub fn emit_core_import<E: Environment>(
        &self,
        instance: &E::Instance,
        core_func_idx: FunctionIdx,
        import_values: &[ImportValue<E>],
        env: &E,
    ) -> ir::Function {
        let adapter_func_idx = self
            .implements
            .iter()
            .find(|x| x.core_func_idx == core_func_idx)
            .unwrap()
            .adapter_func_idx;
        let adapter = self.local_adapter_func(adapter_func_idx);
        let adapter_ty = &self.types[adapter.ty_idx];

        assert!(adapter_ty.is_core());

        let signature = adapter_ty.wasm_signature();

        let name = ir::ExternalName::user(0, 0);

        let mut func = ir::Function::with_name_signature(name, signature);

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry_block = builder.create_ebb();

        builder.append_ebb_params_for_function_params(entry_block);
        builder.append_ebb_params_for_function_returns(entry_block);

        builder.seal_block(entry_block);
        builder.switch_to_block(entry_block);

        builder.set_srcloc(ir::SourceLoc::new(0));

        let mut caller_params = Vec::new();
        for (i, ty) in adapter_ty.params.iter().enumerate() {
            let value = builder.ebb_params(entry_block)[i];
            caller_params.push(Val::from_core_ty_and_ir(*ty, value));
        }

        let caller_results = self.emit_adapter(
            &mut builder,
            InterfaceSide::Caller,
            instance,
            import_values,
            adapter,
            &caller_params,
            env,
        );
        let caller_results: Vec<_> = caller_results.iter().map(Val::core_to_ir).collect();
        builder.ins().fallthrough_return(&caller_results);

        builder.finalize();

        func
    }

    /// Emits an adapted function that wraps an interface-export for this interface and follows the Host ABI.
    pub fn emit_host_export<E: Environment>(
        &self,
        instance: &E::Instance,
        export: ExportIdx,
        env: &E,
    ) -> ir::Function {
        let export = &self.exports[export];
        let adapter = self.local_adapter_func(export.adapter_idx);
        let adapter_ty = &self.types[adapter.ty_idx];

        let signature = env.host_export_signature(adapter_ty);

        let name = ir::ExternalName::user(0, 0);
        let mut func = ir::Function::with_name_signature(name, signature);

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut builder_ctx);

        let entry_block = builder.create_ebb();

        builder.append_ebb_params_for_function_params(entry_block);
        // builder.append_ebb_params_for_function_returns(entry_block);

        builder.seal_block(entry_block);
        builder.switch_to_block(entry_block);

        builder.set_srcloc(ir::SourceLoc::new(0));

        let caller_params = env.host_export_prologue(adapter_ty, &mut builder);
        let caller_results = self.emit_adapter(
            &mut builder,
            InterfaceSide::Callee,
            instance,
            &[],
            adapter,
            &caller_params,
            env,
        );
        env.host_export_epilogue(adapter_ty, &caller_results, &mut builder);

        builder.finalize();

        func
    }

    fn emit_adapter<E: Environment>(
        &self,
        builder: &mut FunctionBuilder,
        side: InterfaceSide,
        instance: &E::Instance,
        import_values: &[ImportValue<E>],
        adapter: &AdapterFunction,
        params: &[Val],
        env: &E,
    ) -> Vec<Val> {
        assert!(side == InterfaceSide::Caller || import_values.is_empty());

        let mut stack = Vec::new();

        for instr in &adapter.instrs {
            match instr {
                Instruction::End => {
                    break;
                }
                Instruction::ArgGet(arg_idx) => stack.push(params[*arg_idx]),

                Instruction::MemoryToString(mem_idx) => {
                    let len = stack.pop().unwrap();
                    let base = stack.pop().unwrap();
                    assert!(len.ty() == ValType::I32);
                    assert!(base.ty() == ValType::I32);
                    stack.push(
                        StringVal {
                            mem_idx: *mem_idx,
                            base: base.core_to_ir(),
                            len: len.core_to_ir(),
                        }
                        .into(),
                    )
                }
                Instruction::StringToMemory(_string_to_memory) => {
                    let string = stack.pop().unwrap();
                    assert!(string.ty() == ValType::String);
                    unimplemented!()
                }

                Instruction::CallCore(func_idx) => {
                    let func_ty = env.function_type(instance, *func_idx);

                    assert!(stack.len() >= func_ty.params.len());
                    let params = &stack[(stack.len() - func_ty.params.len())..stack.len()];

                    let mut results = env.emit_call_core(instance, *func_idx, params, builder);

                    for _ in 0..func_ty.params.len() {
                        stack.pop();
                    }

                    assert!(results.len() == func_ty.results.len());
                    stack.append(&mut results);
                }
                Instruction::CallAdapter(adapter_idx) => {
                    assert!(side == InterfaceSide::Caller);
                    assert!(self.adapter_func_is_imported(*adapter_idx));

                    let imported_adapter =
                        self.imported_adapter_func::<E>(*adapter_idx, import_values);
                    let imported_ty = &self.types[self.imports[*adapter_idx].ty_idx];

                    assert!(stack.len() >= imported_ty.params.len());
                    let params = &stack[(stack.len() - imported_ty.params.len())..stack.len()];

                    let mut results = match imported_adapter {
                        ImportValue::Wasm(export_idx, instance) => {
                            let interface: &Interface = env.interface(instance);
                            let adapter =
                                &interface.adapters[interface.exports[*export_idx].adapter_idx];
                            let adapter_ty = &interface.types[adapter.ty_idx];
                            assert!(imported_ty == adapter_ty);

                            interface.emit_adapter::<E>(
                                builder,
                                InterfaceSide::Callee,
                                instance,
                                &[],
                                adapter,
                                params,
                                env,
                            )
                        }
                        ImportValue::Host(host_func) => {
                            env.emit_call_host(instance, host_func, params, builder)
                        }
                    };

                    for _ in 0..imported_ty.params.len() {
                        stack.pop();
                    }
                    assert!(results.len() == imported_ty.results.len());
                    stack.append(&mut results);
                }

                _ => unimplemented!(),
            }
        }

        assert!(stack.len() == self.types[adapter.ty_idx].results.len());
        stack
    }

    fn adapter_func_is_imported(&self, idx: AdapterIdx) -> bool {
        idx < self.imports.len()
    }

    fn local_adapter_func(&self, idx: AdapterIdx) -> &AdapterFunction {
        assert!(!self.adapter_func_is_imported(idx));
        &self.adapters[idx - self.imports.len()]
    }

    fn imported_adapter_func<'a, E: Environment>(
        &self,
        idx: AdapterIdx,
        import_values: &'a [ImportValue<'a, E>],
    ) -> &'a ImportValue<'a, E> {
        assert!(self.adapter_func_is_imported(idx));
        &import_values[idx]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
enum InterfaceSide {
    Caller,
    Callee,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum ValType {
    // Core types
    I32,
    I64,
    F32,
    F64,
    Anyref,
    // Interface types
    S8,
    S16,
    S32,
    S64,
    U8,
    U16,
    U32,
    U64,
    // Complex interface types
    String,
}

impl ValType {
    pub fn is_core(&self) -> bool {
        match self {
            ValType::I32 | ValType::I64 | ValType::F32 | ValType::F64 | ValType::Anyref => true,
            _ => false,
        }
    }

    pub fn is_interface(&self) -> bool {
        !self.is_core()
    }

    pub fn is_simple(&self) -> bool {
        !self.is_complex()
    }

    pub fn is_complex(&self) -> bool {
        match self {
            ValType::String => true,
            _ => false,
        }
    }

    pub fn ir_type(&self) -> ir::Type {
        assert!(self.is_simple());
        match self {
            ValType::U8 | ValType::S8 => ir::types::I8,
            ValType::U16 | ValType::S16 => ir::types::I16,
            ValType::I32 | ValType::U32 | ValType::S32 => ir::types::I32,
            ValType::I64 | ValType::U64 | ValType::S64 => ir::types::I64,
            ValType::F32 => ir::types::F32,
            ValType::F64 => ir::types::F64,
            ValType::Anyref => REF_TYPE,
            _ => unreachable!(),
        }
    }

    pub fn ir_argument(&self) -> ir::AbiParam {
        let arg = self.ir_type();
        match self {
            ValType::S8 | ValType::S16 | ValType::S32 => ir::AbiParam::new(arg).sext(),
            ValType::U8 | ValType::U16 | ValType::U32 | ValType::I32 => {
                ir::AbiParam::new(arg).uext()
            }
            _ => ir::AbiParam::new(arg),
        }
    }

    pub fn ir_return(&self) -> ir::AbiParam {
        let arg = self.ir_type();
        match self {
            ValType::S8 | ValType::S16 | ValType::S32 => ir::AbiParam::new(arg).sext(),
            ValType::U8 | ValType::U16 | ValType::U32 | ValType::I32 => {
                ir::AbiParam::new(arg).uext()
            }
            _ => ir::AbiParam::new(arg),
        }
    }
}

impl From<wit_parser::ValType> for ValType {
    fn from(val: wit_parser::ValType) -> ValType {
        match val {
            wit_parser::ValType::I32 => ValType::I32,
            wit_parser::ValType::I64 => ValType::I64,
            wit_parser::ValType::F32 => ValType::F32,
            wit_parser::ValType::F64 => ValType::F64,
            wit_parser::ValType::Anyref => ValType::Anyref,
            wit_parser::ValType::S8 => ValType::S8,
            wit_parser::ValType::S16 => ValType::S16,
            wit_parser::ValType::S32 => ValType::S32,
            wit_parser::ValType::S64 => ValType::S64,
            wit_parser::ValType::U8 => ValType::U8,
            wit_parser::ValType::U16 => ValType::U16,
            wit_parser::ValType::U32 => ValType::U32,
            wit_parser::ValType::U64 => ValType::U64,
            wit_parser::ValType::String => ValType::String,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Val {
    // Core types
    I32(ir::Value),
    I64(ir::Value),
    F32(ir::Value),
    F64(ir::Value),
    Anyref(ir::Value),
    // Interface types
    S8(ir::Value),
    S16(ir::Value),
    S32(ir::Value),
    S64(ir::Value),
    U8(ir::Value),
    U16(ir::Value),
    U32(ir::Value),
    U64(ir::Value),
    // Complex interface types
    String(StringVal),
}

impl Val {
    fn from_core_ty_and_ir(ty: ValType, ir: ir::Value) -> Val {
        assert!(ty.is_core());
        match ty {
            ValType::I32 => Val::I32(ir),
            ValType::I64 => Val::I64(ir),
            ValType::F32 => Val::F32(ir),
            ValType::F64 => Val::F64(ir),
            ValType::Anyref => Val::Anyref(ir),
            _ => unreachable!(),
        }
    }

    fn core_to_ir(&self) -> ir::Value {
        assert!(self.ty().is_core());
        match self {
            Val::I32(val) | Val::I64(val) | Val::F32(val) | Val::F64(val) | Val::Anyref(val) => {
                *val
            }
            _ => unreachable!(),
        }
    }

    pub fn ty(&self) -> ValType {
        match self {
            Val::I32(..) => ValType::I32,
            Val::I64(..) => ValType::I64,
            Val::F32(..) => ValType::F32,
            Val::F64(..) => ValType::F64,
            Val::Anyref(..) => ValType::Anyref,
            Val::S8(..) => ValType::S8,
            Val::S16(..) => ValType::S16,
            Val::S32(..) => ValType::S32,
            Val::S64(..) => ValType::S64,
            Val::U8(..) => ValType::U8,
            Val::U16(..) => ValType::U16,
            Val::U32(..) => ValType::U32,
            Val::U64(..) => ValType::U64,
            Val::String(..) => ValType::String,
        }
    }

    pub fn as_simple_ir(&self) -> Option<ir::Value> {
        match self {
            Val::I32(val)
            | Val::I64(val)
            | Val::F32(val)
            | Val::F64(val)
            | Val::Anyref(val)
            | Val::S8(val)
            | Val::S16(val)
            | Val::S32(val)
            | Val::S64(val)
            | Val::U8(val)
            | Val::U16(val)
            | Val::U32(val)
            | Val::U64(val) => Some(*val),
            _ => None,
        }
    }
}

impl From<StringVal> for Val {
    fn from(string: StringVal) -> Val {
        Val::String(string)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct StringVal {
    pub mem_idx: MemoryIdx,
    pub base: ir::Value,
    pub len: ir::Value,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

impl From<wit_parser::Type> for Type {
    fn from(ty: wit_parser::Type) -> Type {
        Type {
            params: ty.params.into_iter().map(|x| x.into()).collect(),
            results: ty.results.into_iter().map(|x| x.into()).collect(),
        }
    }
}

impl Type {
    pub fn is_core(&self) -> bool {
        self.params.iter().all(ValType::is_core) && self.results.iter().all(ValType::is_core)
    }

    pub fn is_interface(&self) -> bool {
        self.params.iter().all(ValType::is_interface)
            && self.results.iter().all(ValType::is_interface)
    }

    pub fn signature(&self, call_conv: isa::CallConv) -> ir::Signature {
        let mut signature = ir::Signature::new(call_conv);

        for arg in &self.params {
            signature.params.push(arg.ir_argument());
        }

        for ret in &self.results {
            signature.returns.push(ret.ir_return());
        }

        signature
    }

    pub fn wasm_signature(&self) -> ir::Signature {
        let mut sig = self.signature(WASM_CALL_CONV);

        sig.params.push(ir::AbiParam::special(
            POINTER_TYPE,
            ir::ArgumentPurpose::VMContext,
        ));

        sig
    }
}

#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub ty_idx: TypeIdx,
}

impl<'a> From<wit_parser::Import<'a>> for Import {
    fn from(import: wit_parser::Import) -> Import {
        Import {
            module: import.module.to_owned(),
            name: import.name.to_owned(),
            ty_idx: import.ty as usize,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub adapter_idx: AdapterIdx,
}

impl<'a> From<wit_parser::Export<'a>> for Export {
    fn from(export: wit_parser::Export) -> Export {
        Export {
            name: export.name.to_owned(),
            adapter_idx: export.func as usize,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AdapterFunction {
    ty_idx: TypeIdx,
    instrs: Vec<Instruction>,
}

impl<'a> From<wit_parser::Func<'a>> for AdapterFunction {
    fn from(func: wit_parser::Func) -> AdapterFunction {
        AdapterFunction {
            ty_idx: func.ty as usize,
            instrs: func.instrs().map(|x| x.unwrap().into()).collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Implement {
    core_func_idx: FunctionIdx,
    adapter_func_idx: AdapterIdx,
}

impl From<wit_parser::Implement> for Implement {
    fn from(implement: wit_parser::Implement) -> Implement {
        Implement {
            core_func_idx: implement.core_func as usize,
            adapter_func_idx: implement.adapter_func as usize,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Instruction {
    ArgGet(ArgumentIdx),
    CallCore(FunctionIdx),
    End,
    MemoryToString(MemoryIdx),
    StringToMemory(StringToMemory),
    CallAdapter(AdapterIdx),
    DeferCallCore(FunctionIdx),

    I32ToS8,
    I32ToS8X,
    I32ToU8,
    I32ToS16,
    I32ToS16X,
    I32ToU16,
    I32ToS32,
    I32ToU32,
    I32ToS64,
    I32ToU64,

    I64ToS8,
    I64ToS8X,
    I64ToU8,
    I64ToS16,
    I64ToS16X,
    I64ToU16,
    I64ToS32,
    I64ToS32X,
    I64ToU32,
    I64ToS64,
    I64ToU64,

    S8ToI32,
    U8ToI32,
    S16ToI32,
    U16ToI32,
    S32ToI32,
    U32ToI32,
    S64ToI32,
    S64ToI32X,
    U64ToI32,
    U64ToI32X,

    S8ToI64,
    U8ToI64,
    S16ToI64,
    U16ToI64,
    S32ToI64,
    U32ToI64,
    S64ToI64,
    U64ToI64,
}

impl From<wit_parser::Instruction> for Instruction {
    fn from(instr: wit_parser::Instruction) -> Instruction {
        match instr {
            wit_parser::Instruction::ArgGet(x) => Instruction::ArgGet(x as usize),
            wit_parser::Instruction::CallCore(x) => Instruction::CallCore(x as usize),
            wit_parser::Instruction::End => Instruction::End,
            wit_parser::Instruction::MemoryToString(x) => Instruction::MemoryToString(x as usize),
            wit_parser::Instruction::StringToMemory(x) => Instruction::StringToMemory(x.into()),
            wit_parser::Instruction::CallAdapter(x) => Instruction::CallAdapter(x as usize),
            wit_parser::Instruction::DeferCallCore(x) => Instruction::DeferCallCore(x as usize),

            wit_parser::Instruction::I32ToS8 => Instruction::I32ToS8,
            wit_parser::Instruction::I32ToS8X => Instruction::I32ToS8X,
            wit_parser::Instruction::I32ToU8 => Instruction::I32ToU8,
            wit_parser::Instruction::I32ToS16 => Instruction::I32ToS16,
            wit_parser::Instruction::I32ToS16X => Instruction::I32ToS16X,
            wit_parser::Instruction::I32ToU16 => Instruction::I32ToU16,
            wit_parser::Instruction::I32ToS32 => Instruction::I32ToS32,
            wit_parser::Instruction::I32ToU32 => Instruction::I32ToU32,
            wit_parser::Instruction::I32ToS64 => Instruction::I32ToS64,
            wit_parser::Instruction::I32ToU64 => Instruction::I32ToU64,

            wit_parser::Instruction::I64ToS8 => Instruction::I64ToS8,
            wit_parser::Instruction::I64ToS8X => Instruction::I64ToS8X,
            wit_parser::Instruction::I64ToU8 => Instruction::I64ToU8,
            wit_parser::Instruction::I64ToS16 => Instruction::I64ToS16,
            wit_parser::Instruction::I64ToS16X => Instruction::I64ToS16X,
            wit_parser::Instruction::I64ToU16 => Instruction::I64ToU16,
            wit_parser::Instruction::I64ToS32 => Instruction::I64ToS32,
            wit_parser::Instruction::I64ToS32X => Instruction::I64ToS32X,
            wit_parser::Instruction::I64ToU32 => Instruction::I64ToU32,
            wit_parser::Instruction::I64ToS64 => Instruction::I64ToS64,
            wit_parser::Instruction::I64ToU64 => Instruction::I64ToU64,

            wit_parser::Instruction::S8ToI32 => Instruction::S8ToI32,
            wit_parser::Instruction::U8ToI32 => Instruction::U8ToI32,
            wit_parser::Instruction::S16ToI32 => Instruction::S16ToI32,
            wit_parser::Instruction::U16ToI32 => Instruction::U16ToI32,
            wit_parser::Instruction::S32ToI32 => Instruction::S32ToI32,
            wit_parser::Instruction::U32ToI32 => Instruction::U32ToI32,
            wit_parser::Instruction::S64ToI32 => Instruction::S64ToI32,
            wit_parser::Instruction::S64ToI32X => Instruction::S64ToI32X,
            wit_parser::Instruction::U64ToI32 => Instruction::U64ToI32,
            wit_parser::Instruction::U64ToI32X => Instruction::U64ToI32X,

            wit_parser::Instruction::S8ToI64 => Instruction::S8ToI64,
            wit_parser::Instruction::U8ToI64 => Instruction::U8ToI64,
            wit_parser::Instruction::S16ToI64 => Instruction::S16ToI64,
            wit_parser::Instruction::U16ToI64 => Instruction::U16ToI64,
            wit_parser::Instruction::S32ToI64 => Instruction::S32ToI64,
            wit_parser::Instruction::U32ToI64 => Instruction::U32ToI64,
            wit_parser::Instruction::S64ToI64 => Instruction::S64ToI64,
            wit_parser::Instruction::U64ToI64 => Instruction::U64ToI64,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StringToMemory {
    malloc: FunctionIdx,
    mem: MemoryIdx,
}

impl From<wit_parser::StringToMemory> for StringToMemory {
    fn from(string_to_memory: wit_parser::StringToMemory) -> StringToMemory {
        StringToMemory {
            malloc: string_to_memory.malloc as usize,
            mem: string_to_memory.mem as usize,
        }
    }
}
