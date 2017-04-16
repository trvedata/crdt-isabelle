module Arith : sig
  type int = Int_of_integer of Big_int.big_int
  type num = One | Bit0 of num | Bit1 of num
  val plus_int : int -> int -> int
  val minus_int : int -> int -> int
end = struct

type int = Int_of_integer of Big_int.big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec plus_int
  k l = Int_of_integer
          (Big_int.add_big_int (integer_of_int k) (integer_of_int l));;

let rec minus_int
  k l = Int_of_integer
          (Big_int.sub_big_int (integer_of_int k) (integer_of_int l));;

end;; (*struct Arith*)

module Counter : sig
  type operation = Increment | Decrement
  val counter_op : operation -> Arith.int -> Arith.int option
end = struct

type operation = Increment | Decrement;;

let rec counter_op
  xa0 x = match xa0, x with
    Increment, x ->
      Some (Arith.plus_int x (Arith.Int_of_integer (Big_int.big_int_of_int 1)))
    | Decrement, x ->
        Some (Arith.minus_int x
               (Arith.Int_of_integer (Big_int.big_int_of_int 1)));;

end;; (*struct Counter*)
