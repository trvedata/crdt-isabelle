module Arith : sig
  type num
  type int
  val one_int : int
  val plus_int : int -> int -> int
  val minus_int : int -> int -> int
end = struct

type num = One | Bit0 of num | Bit1 of num;;

type int = Zero_int | Pos of num | Neg of num;;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec uminus_int = function Neg m -> Pos m
                     | Pos m -> Neg m
                     | Zero_int -> Zero_int;;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let one_int : int = Pos One;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_int
    | Bit1 m, Bit0 n -> plus_int (dup (sub m n)) one_int
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_int k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
               | Neg m, Pos n -> sub n m
               | Pos m, Neg n -> sub m n
               | Pos m, Pos n -> Pos (plus_num m n)
               | Zero_int, l -> l
               | k, Zero_int -> k
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_int l
                | k, Zero_int -> k;;

end;; (*struct Arith*)

module Counter : sig
  type operation = Increment | Decrement
  val counter_op : operation -> Arith.int -> Arith.int option
end = struct

type operation = Increment | Decrement;;

let rec counter_op
  xa0 x = match xa0, x with
    Increment, x -> Some (Arith.plus_int x Arith.one_int)
    | Decrement, x -> Some (Arith.minus_int x Arith.one_int);;

end;; (*struct Counter*)
