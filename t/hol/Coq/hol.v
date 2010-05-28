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
forall b: hterm o, eps (himp a b) = eps a -> eps b.

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


(* Beta rule *)

Definition beta: forall a: htype, forall b: htype, forall f: (hterm a -> hterm b), forall u: hterm a, eps (heq b (App a b (Lam a b f) u) (f u)).
intros a b f u. autorewrite with re. intros P H. exact H.
Defined.


(* ;; Rules *)

(* refl: a: htype -> x: hterm a -> eps (heq a x x). *)
(* [a: htype, *)
(*  x: hterm a] refl a x --> P: hterm (arrow a o) => h: eps (App a o P x) => h. *)


(* sym: a: htype -> x: hterm a -> y: hterm a -> eps (heq a x y) -> eps (heq a y x). *)
(* [a: htype, *)
(*  x: hterm a, *)
(*  y: hterm a, *)
(*  Hxy: eps (heq a x y)] *)
(* sym a x y Hxy --> P: hterm (arrow a o) => Hy: eps (App a o P y) => Hxy (Lam a o (z: hterm a => himp (App a o P z) (App a o P x))) (H: eps (App a o P x) => H) Hy. *)


(* trans: a: htype -> s: hterm a -> t: hterm a -> u: hterm a -> eps (heq a s t) -> eps (heq a t u) -> eps (heq a s u). *)
(* [a: htype, *)
(*  s: hterm a, *)
(*  t: hterm a, *)
(*  u: hterm a, *)
(*  Hst: P: hterm (arrow a o) -> eps (App a o P s) -> eps (App a o P t), *)
(*  Htu: P: hterm (arrow a o) -> eps (App a o P t) -> eps (App a o P u)] *)
(* trans a s t u Hst Htu --> P: hterm (arrow a o) => Hs: eps (App a o P s) => Htu P (Hst P Hs). *)


(* mk_comb: a: htype -> b: htype -> s: hterm (arrow a b) -> t: hterm (arrow a b) -> u: hterm a -> v: hterm a -> *)
(*   eps (heq (arrow a b) s t) -> eps (heq a u v) -> eps (heq b (App a b s u) (App a b t v)). *)
(* ;; [a: htype, *)
(* ;;  b: htype, *)
(* ;;  s: hterm (arrow a b), *)
(* ;;  t: hterm (arrow a b), *)
(* ;;  u: hterm a, *)
(* ;;  v: hterm a, *)
(* ;;  Hst: eps (heq (arrow a b) s t), ; = P: hterm (arrow (arrow a b) o) -> Hs: eps (App (arrow a b) o P s) -> eps (App (arrow a b) o P y) *)
(* ;;  Huv: eps (heq a u v)] ; = P: hterm (arrow a o) -> Hu: eps (App a o P u) -> eps (App a o P v) *)
(* ;; mk_comb a b s t u v Hst Huv --> P: hterm (arrow b o) => Hsu: eps (App b o P (App a b s u)) => *)
(* ;;   ; eps (App b o P (App a b t v)) *)


(* ;; Abs cannot be written (meta-rule), we can only write instances of it *)


(* ;; Liste des règles de HOL-Light qui fonctionnent : *)
(* ;; - refl *)
(* ;; - trans *)
(* ;; - sym *)
