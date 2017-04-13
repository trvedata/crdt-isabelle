open Core.Std
open Async.Std
open Counter

exception Error

let integer_of_int (Arith.Int_of_integer k) = k;;

let state = ref (Arith.Int_of_integer Big_int.zero_big_int)
let update = function
  | Some s -> state := s
  | None -> ()
let string_of_state () = Big_int.string_of_big_int (integer_of_int !state)

let choose_msg () =
  match Random.int 2 with
  | 0 -> "inc\n"
  | 1 -> "dec\n"

let loop id input =
  let interp input =
    match input with
    | "inc\n" -> Some Counter.Increment
    | "dec\n" -> Some Counter.Decrement
    | _ -> None
  in
  let run_op input =
    match interp input with
    | Some op -> update (Counter.counter_op op !state)
    | None -> ()
  in
  let log () =
    let str = "Node " ^ string_of_int id ^ ": " ^ string_of_state () in
    print_endline str
  in
  let msg = choose_msg () in
  run_op input;
  print_string input;
  log ();
  run_op msg;
  print_string msg;
  log ();
  msg

let init r w =
  let msg = choose_msg () in
  Writer.write_line w msg;
  Pipe.transfer (Reader.pipe r) (Writer.pipe w) ~f:(loop 1)

let port = 8765

let run ~client=
  let host_and_port ()=
    Tcp.Server.create
      ~on_handler_error:`Raise
      (Tcp.on_port port)
      (fun _addr r w ->
         Pipe.transfer (Reader.pipe r) (Writer.pipe w) ~f:(loop 0))
  in
  let listen () =
    Tcp.with_connection
      (Tcp.to_host_and_port "128.232.87.162" 8765)
      (fun _ r w -> init r w)
  in
  if client then
    ignore (listen ())
  else
    ignore (host_and_port () : (Socket.Address.Inet.t, int) Tcp.Server.t Deferred.t);
  Deferred.never()

let () =
  Random.init 5;
  Command.async_basic
    ~summary:"Start and echo server"
    Command.Spec.(
      empty
     (* +> flag "-id" (required int)
        ~doc:" Node id" *)
      +> flag "-client" no_arg
        ~doc:"client"
    )
    (fun client () -> run ~client)
  |> Command.run