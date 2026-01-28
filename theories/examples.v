From ILAL Require Import language.

(* Examples from the incorrectness logic paper *)

Definition loop0 : stmt := <{
  "n" := nondet();;
  "x" := 0;;
  while (fun s => s "n" > 0) do
    "x" := (fun s => s "x" + s "n") ;;
    "n" := nondet()
  done
  }>.

Definition client0 : stmt := <{
  loop0 ;;
  if (fun s => s "x" = 2000000) then
    error()
  else
    skip
  done
  }>.

Definition loop1 : stmt := <{
  "x" := 0;;
  ("x" := (fun s => s "x" + 1)) **
  }>.

Definition client1 : stmt := <{
  loop1;;
  if (fun s => s "x" = 2000000) then
    error()
  else
    skip
  done
  }>.

Definition loop2 : stmt := <{
  "x" := 0;;
  (if (fun s => s "x" = 2000000) then
    error()
   else
    skip
   done;;
   "x" := (fun s => s "x" + 1)
  )**
  }>.