open Core.Std
open Async.Std
open Counter.Arith
open Counter.Counter

exception Error

let integer_of_int (Int_of_integer k) = k;;

let state = ref (Int_of_integer Big_int.zero_big_int)
let update = function
  | Some s -> state := s
  | None -> ()
let string_of_state () = Big_int.string_of_big_int (integer_of_int !state)

let choose_msg () =
  match Random.int 2 with
  | 0 -> "inc"
  | 1 -> "dec"
  | _ -> raise Error

let log id =
  let str = "Node " ^ string_of_int id ^ ": " ^ string_of_state () in
  print_endline str

let broadcast hps m =
  let send m (h, p) =
    try_with (fun () ->
      Tcp.connect (Tcp.to_host_and_port h p)
      >>= fun (_, _, w) ->
      (*print_endline ("Send to: " ^ h ^ ":" ^ string_of_int p ^ ": " ^ m);*)
      return (Writer.write_line w m)
      ) >>= return
  in
  List.iter hps ~f:(fun hp -> ignore (send m hp))

let random_msg hps =
  Clock.every (sec (Random.float 5.0))
    (fun () -> broadcast hps (choose_msg ()))

let rec deliver id hps r =
  let update_state op = update (counter_op op !state) in
  let update_state res =
    match res with
    | `Ok m ->
      (*print_endline ("Deliver " ^ string_of_int id ^ ": " ^ m);*)
      begin match m with
        | "inc" -> update_state Increment
        | "dec" -> update_state Decrement
        | "log" -> log id
        | "showall" -> broadcast hps "log"
        | s -> print_endline ("Unknown action: " ^ s)
      end
    | `Eof -> ()
  in
  Reader.read_line r
  >>= fun res ->
  update_state res;
  deliver id hps r

let get_host_and_port nodes =
  let list_to_hp = function
    | [a; b] -> (a, int_of_string b)
    | _ -> raise Error
  in
  let hps = String.split_on_chars ~on:[';'] nodes in
  List.map hps ~f:
    begin fun node ->
      String.split_on_chars ~on:[':'] node
      |> list_to_hp
    end

let run ~id ~port ~nodes =
  let hps = get_host_and_port nodes in
  let host_and_port =
    Tcp.Server.create
      ~on_handler_error:`Raise
      (Tcp.on_port port)
      (fun _ r _ -> deliver id hps r)
  in
  ignore host_and_port;
  ignore (random_msg hps);
  Deferred.never()

let () =
  Command.async
    ~summary:"Start a test node"
    Command.Spec.(
      empty
     +> flag "-id" (required int)
        ~doc:" Node id"
     +> flag "-port" (required int)
        ~doc:" Node port"
     +> flag "-nodes" (required string)
        ~doc:" Other nodes in the network"
    )
    (fun id port nodes () -> run ~id ~port ~nodes)
  |> Command.run