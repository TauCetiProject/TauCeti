/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.CoxeterElement
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation

/-!
# Conjugacy of the Coxeter elements of a Weyl group

The Dynkin diagram of a base of a finite reduced crystallographic root system is a forest
(`RootPairing.isAcyclic_graph_coxeterMatrixOfBase`), so the conjugacy of Coxeter elements on a
forest (`CoxeterSystem.isConj_wordProd_of_perm`) applies to the Coxeter system
`TauCeti.weylCoxeterSystem` of the Weyl group: any two products of the simple reflections of a set
of simple roots, each taken once, are conjugate in the Weyl group. In particular all Coxeter
elements of the Weyl group are conjugate, so their common order and their eigenvalues on the
reflection representation depend only on the root system.

## Main results

* `RootPairing.isConj_wordProd_of_perm`: for a reduced root system, rearranging a product of
  distinct simple reflections gives a conjugate element of the Weyl group; in particular all
  Coxeter elements of the Weyl group are conjugate.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 1, and Ch. VI, §4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  (b : P.Base)

/-- **The Coxeter elements of a Weyl group are conjugate.** For a base of a finite reduced
crystallographic root system, rearranging a word in the simple reflections with no repeated letter
gives a conjugate element of the Weyl group. In particular any two products of all the simple
reflections, each exactly once, are conjugate. -/
theorem isConj_wordProd_of_perm [P.IsRootSystem] [P.IsReduced] {l l' : List b.support}
    (hl : l.Nodup) (h : l.Perm l') : IsConj (wordProd P b l) (wordProd P b l') := by
  rw [← weylCoxeterSystem_wordProd, ← weylCoxeterSystem_wordProd]
  exact (weylCoxeterSystem P b).isConj_wordProd_of_perm hl
    ((isAcyclic_graph_coxeterMatrixOfBase P b).induce _) h

end RootPairing
