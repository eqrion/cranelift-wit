(module
  (memory $mem 1)
  (data (i32.const 10) "hello, world")
  (func $log_ (import "" "log_") (param i32 i32))
  (func $run_ (export "run_")
    i32.const 10
    i32.const 12
    call $log_
  )

  (@interface func $log (import "" "log") (param $arg string))
  (@interface implement (import "" "log_") (param $ptr i32) (param $len i32)
    arg.get $ptr
    arg.get $len
    memory-to-string $mem
    call-adapter $log
  )
  (@interface func (export "run")
    call-core $run_
  )
)
