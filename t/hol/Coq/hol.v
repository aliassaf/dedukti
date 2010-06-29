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


(* β-rule *)

Axiom ax1 : forall a: htype,
forall b: htype,
forall f: hterm a -> hterm b,
forall x: hterm a, App a b (Lam a b f) x = f x.

Hint Rewrite ax1 : re.


(* Facilities *)

Parameter himp: hterm o -> hterm o -> hterm o.
Axiom ax2 : forall a: hterm o,
forall b: hterm o, App o o (App o (arrow o o) Imp a) b = himp a b.

Hint Rewrite ax2 : re.


Parameter hforall: forall a: htype, hterm (arrow a o) -> hterm o.
Axiom ax3: forall a: htype,
forall P: hterm (arrow a o), App (arrow a o) o (Forall a) P = hforall a P.

Hint Rewrite ax3 : re.


Parameter heq: forall a: htype, hterm a -> hterm a -> hterm o.
Axiom ax4 : forall a: htype,
forall x: hterm a,
forall y: hterm a, App a o (App a (arrow a o) (Eq a) x) y = heq a x y.

Hint Rewrite ax4 : re.


Parameter hequiv: hterm o -> hterm o -> hterm o.
Axiom ax5: heq o = hequiv.

Hint Rewrite ax5 : re.


(* eps *)

Parameter eps: hterm o -> Type.

Axiom ax6 : forall a: hterm o,
forall b: hterm o, eps (himp a b) = (eps a -> eps b).

Hint Rewrite ax6 : re.

Axiom ax7 : forall a: htype,
forall f: hterm a -> hterm o, eps (hforall a (Lam a o f)) = (forall b: hterm a, eps (f b)).

Hint Rewrite ax7 : re.

Axiom ax8 : forall a: htype,
forall x: hterm a,
forall y: hterm a, eps (heq a x y) = (forall P: hterm (arrow a o), eps (App a o P x) -> eps (App a o P y)).

Hint Rewrite ax8 : re.


(* Extensionality *)

Parameter fun_ext: forall a: htype, forall b: htype, forall f: hterm (arrow a b), forall g: hterm (arrow a b),
    (forall x: hterm a, eps (heq b (App a b f x) (App a b g x))) -> eps (heq (arrow a b) f g).

Parameter prop_ext: forall p: hterm o, forall q: hterm o, eps (himp p q) -> eps (himp q p) -> eps (hequiv p q).


(* Rules *)

Definition refl: forall a: htype, forall x: hterm a, eps (heq a x x).
intros a x. autorewrite with re. intros P h. exact h.
Defined.


Definition sym: forall a: htype, forall x: hterm a, forall y: hterm a, eps (heq a x y) -> eps (heq a y x).
intros a x y Hxy. autorewrite with re in *. intros P Hy.
pose (H1 := (Hxy (Lam a o (fun z: hterm a => himp (App a o P z) (App a o P x))))). autorewrite with re in H1. exact (H1 (fun H: eps (App a o P x) => H) Hy).
Defined.


Definition trans: forall a: htype, forall s: hterm a, forall t: hterm a, forall u: hterm a, eps (heq a s t) -> eps (heq a t u) -> eps (heq a s u).
intros a s t u Hst Htu. autorewrite with re in *. intros P Hs. exact (Htu P (Hst P Hs)).
Defined.


Definition beta: forall a: htype, forall b: htype, forall f: (hterm a -> hterm b), forall u: hterm a, eps (heq b (App a b (Lam a b f) u) (f u)).
intros a b f u. autorewrite with re. intros P H. exact H.
Defined.


Definition mk_comb: forall a: htype, forall b: htype, forall s: hterm (arrow a b), forall t: hterm (arrow a b), forall u: hterm a, forall v: hterm a,
  eps (heq (arrow a b) s t) -> eps (heq a u v) -> eps (heq b (App a b s u) (App a b t v)).
intros a b s t u v Hst Huv. autorewrite with re in *. intros P Hsu.
pose (H1 := Hst (Lam (arrow a b) o (fun s: hterm (arrow a b) => App b o P (App a b s v)))). autorewrite with re in H1. apply H1. pose (H2 := (Huv (Lam a o (fun u: hterm a => App b o P (App a b s u))))). autorewrite with re in H2. apply H2. exact Hsu.
Defined.


Definition eq_mp : forall p: hterm o, forall q: hterm o,
  eps (hequiv p q) -> eps p -> eps q.
intros p q Hpq Hp. rewrite <- ax5 in Hpq. rewrite <- ax4 in Hpq. autorewrite with re in *. pose (H := Hpq (Lam o o (fun q' => q'))). autorewrite with re in H. exact (H Hp).
Defined.
