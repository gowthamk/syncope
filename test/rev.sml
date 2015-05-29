exception Catalyst;

fun ('a) synth hole_f = 
    let
      val rec concat = fn (l1:'a list) => fn (l2:'a list) => 
        case l1 of [] => l2
         |  x::xs => hole_f ()
    in 
      true
    end
(*
fun concat l1 l2 = case l1 of
    [] => l2
  | x::xs => x::(concat xs l2)

fun rev l = case l of
    [] => []
  | x::xs => ??

fun snoc n l = case l of
    [] => [n]
  | x::xs => x::(snoc n xs)
*)
