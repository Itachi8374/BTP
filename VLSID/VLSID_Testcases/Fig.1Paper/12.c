/*
;; Function main (main, funcdef_no=0, decl_uid=1830, cgraph_uid=0, symbol_order=0)

;; 2 loops found
;;
;; Loop 0
;;  header 0, latch 1
;;  depth 0, outer -1
;;  nodes: 0 1 2 3 4 5 6 7 8
;;
;; Loop 1
;;  header 5, latch 4
;;  depth 1, outer 0
;;  nodes: 5 4
;; 2 succs { 3 7 }
;; 3 succs { 5 }
;; 4 succs { 5 }
;; 5 succs { 4 6 }
;; 6 succs { 8 }
;; 7 succs { 8 }
;; 8 succs { 1 }
*/
int main ()
{
  int out;
  int n;
  int y;
  int x;
  int i;

  bb2:
  if (n >= 0)
    goto bb3;
  else
    goto bb7;

  bb3:
  i = 0;
  x = 0;
  y = 0;
  goto bb5;

  bb4:
  x = 5;
  y = y + i;
  i = i + 1;

  bb5:
  if (i <= n)
    goto bb4;
  else
    goto bb6;

  bb6:
  out = x + y;
  goto bb8;

  bb7:
  out = -1;

  bb8:
  return 0;

}


