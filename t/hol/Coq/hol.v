Parameter htype: Type.
Parameter o: htype.
Parameter arrow: htype -> htype -> htype.


(* Terms *)

Parameter hterm: htype -> Type.
Parameter Lam: forall a: htype, forall b: htype, (hterm a -> hterm b) -> hterm (arrow a b).
Parameter App: forall a: htype, forall b: htype, hterm (arrow a b) -> hterm a -> hterm b.
Parameter Imp: hterm (arrow o (arrow o o)).
Parameter Forall: forall a: htype, hterm (arrow (arrow a o) o).
Parameter Eq: forall a: htype, hterm (arrow a (arrow a o)).
Parameter False: hterm o.
Parameter True: hterm o.
Parameter Not: hterm (arrow o o).
Parameter Or: hterm (arrow o (arrow o o)).
Parameter And: hterm (arrow o (arrow o o)).
Parameter Exists: forall a: htype, hterm (arrow (arrow a o) o).

(* β-rule *)

Axiom ax1 : forall a: htype,
forall b: htype,
forall f: hterm a -> hterm b,
forall x: hterm a, App a b (Lam a b f) x = f x.

Hint Rewrite ax1 : re.


(* eps *)

Parameter eps: hterm o -> Type.

Axiom ax6 : forall a: hterm o,
forall b: hterm o, eps (App o o (App o (arrow o o) Imp a) b) = (eps a -> eps b).

Hint Rewrite ax6 : re.

Axiom ax7 : forall a: htype,
forall f: hterm a -> hterm o, eps (App (arrow a o) o (Forall a) (Lam a o f)) = (forall b: hterm a, eps (f b)).

Hint Rewrite ax7 : re.

Axiom ax8 : forall a: htype,
forall x: hterm a,
forall y: hterm a, eps (App a o (App a (arrow a o) (Eq a) x) y) = (forall P: hterm (arrow a o), eps (App a o P x) -> eps (App a o P y)).

Hint Rewrite ax8 : re.

Axiom ax9 : eps False = forall P: hterm o, eps P.

Hint Rewrite ax9 : re.

Axiom ax10 : eps True = forall P: hterm o, eps P -> eps P.

Hint Rewrite ax10 : re.

Axiom ax11 : forall P, eps (App o o Not P) = eps P -> eps False.

Hint Rewrite ax11 : re.

Axiom ax12 : forall A B, eps (App o o (App o (arrow o o) Or A) B) =
  forall P: hterm o, (eps A -> eps P) -> (eps B -> eps P) -> eps P.

Hint Rewrite ax12 : re.

Axiom ax13 : forall A B, eps (App o o (App o (arrow o o) And A) B) =
  forall P: hterm o, (eps A -> eps B -> eps P) -> eps P.

Hint Rewrite ax13 : re.

Axiom ax14 : forall a f, eps (App (arrow a o) o (Exists a) (Lam a o f)) =
  forall P: hterm o, (forall x: hterm a, eps (f x) -> eps P) -> eps P.

Hint Rewrite ax14 : re.


(* Extensionality *)

Parameter fun_ext: forall a: htype, forall b: htype, forall f: hterm (arrow a b), forall g: hterm (arrow a b),
    (forall x: hterm a, eps (App b o (App b (arrow b o) (Eq b) (App a b f x)) (App a b g x))) -> eps (App (arrow a b) o (App (arrow a b) (arrow (arrow a b) o) (Eq (arrow a b)) f) g).

Parameter prop_ext: forall p: hterm o, forall q: hterm o, eps (App o o (App o (arrow o o) Imp p) q) -> eps (App o o (App o (arrow o o) Imp q) p) -> eps (App o o (App o (arrow o o) (Eq o) p) q).


(* Rules *)

Definition refl: forall a: htype, forall x: hterm a, eps (App a o (App a (arrow a o) (Eq a) x) x).
intros a x. autorewrite with re. intros P h. exact h.
Defined.


Definition sym: forall a: htype, forall x: hterm a, forall y: hterm a, eps (App a o (App a (arrow a o) (Eq a) x) y) -> eps (App a o (App a (arrow a o) (Eq a) y) x).
intros a x y Hxy. autorewrite with re in *. intros P Hy.
pose (H1 := (Hxy (Lam a o (fun z: hterm a => App o o (App o (arrow o o) Imp (App a o P z)) (App a o P x))))). autorewrite with re in H1. exact (H1 (fun H: eps (App a o P x) => H) Hy).
Defined.


Definition trans: forall a: htype, forall s: hterm a, forall t: hterm a, forall u: hterm a, eps (App a o (App a (arrow a o) (Eq a) s) t) -> eps (App a o (App a (arrow a o) (Eq a) t) u) -> eps (App a o (App a (arrow a o) (Eq a) s) u).
intros a s t u Hst Htu. autorewrite with re in *. intros P Hs. exact (Htu P (Hst P Hs)).
Defined.


Definition beta: forall a: htype, forall b: htype, forall f: (hterm a -> hterm b), forall u: hterm a, eps (App b o (App b (arrow b o) (Eq b) (App a b (Lam a b f) u)) (f u)).
intros a b f u. autorewrite with re. intros P H. exact H.
Defined.


Definition mk_comb: forall a: htype, forall b: htype, forall s: hterm (arrow a b), forall t: hterm (arrow a b), forall u: hterm a, forall v: hterm a,
  eps (App (arrow a b) o (App (arrow a b) (arrow (arrow a b) o) (Eq (arrow a b)) s) t) -> eps (App a o (App a (arrow a o) (Eq a) u) v) -> eps (App b o (App b (arrow b o) (Eq b) (App a b s u)) (App a b t v)).
intros a b s t u v Hst Huv. autorewrite with re in *. intros P Hsu.
pose (H1 := Hst (Lam (arrow a b) o (fun s: hterm (arrow a b) => App b o P (App a b s v)))). autorewrite with re in H1. apply H1. pose (H2 := (Huv (Lam a o (fun u: hterm a => App b o P (App a b s u))))). autorewrite with re in H2. apply H2. exact Hsu.
Defined.


Definition eq_mp : forall p: hterm o, forall q: hterm o,
  eps (App o o (App o (arrow o o) (Eq o) p) q) -> eps p -> eps q.
intros p q Hpq Hp. autorewrite with re in *. pose (H := Hpq (Lam o o (fun q' => q'))). autorewrite with re in H. exact (H Hp).
Defined.


(* HOL-Light's definitions of logical connectives is provable in our
   logical framework *)

Definition hollight_DEF_T : eps (App o o (App o (arrow o o) (Eq o) True) (App (arrow o o) o (App (arrow o o) (arrow (arrow o o) o) (Eq (arrow o o)) (Lam o o (fun x1: hterm o => x1))) (Lam o o (fun x1: hterm o => x1)))).
Proof.
  apply prop_ext.
  autorewrite with re. intros H1 P H. exact H.
  autorewrite with re. intros H1 P H. exact H.
Defined.
