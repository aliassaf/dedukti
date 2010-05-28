Require hol.

Definition hollight_test_beta : hol.eps (hol.App (hol.arrow hol.o hol.o) hol.o (hol.Forall hol.o) (hol.Lam hol.o hol.o (fun x1: hol.hterm hol.o => (hol.App (hol.arrow hol.o hol.o) hol.o (hol.App (hol.arrow hol.o hol.o) (hol.arrow (hol.arrow hol.o hol.o) hol.o) (hol.Eq (hol.arrow hol.o hol.o)) (hol.App hol.o (hol.arrow hol.o hol.o) (hol.Lam hol.o (hol.arrow hol.o hol.o) (fun x1: hol.hterm hol.o => (hol.Lam hol.o hol.o (fun x2: hol.hterm hol.o => (hol.App hol.o hol.o (hol.App hol.o (hol.arrow hol.o hol.o) (hol.Eq hol.o) x1) x2))))) x1)) (hol.Lam hol.o hol.o (fun x2: hol.hterm hol.o => (hol.App hol.o hol.o (hol.App hol.o (hol.arrow hol.o hol.o) (hol.Eq hol.o) x1) x2))))))).
autorewrite with re. intro x1.
exact (hol.beta hol.o (hol.arrow hol.o hol.o) (x1: hol.o => (hol.Lam hol.o hol.o (x2: hol.hterm hol.o => (hol.App hol.o hol.o (hol.App hol.o (hol.arrow hol.o hol.o) (hol.Eq hol.o) x1) x2)))) x1).
