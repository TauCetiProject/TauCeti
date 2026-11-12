/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SpecialNodePermutations
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# Based automorphisms of nonsimply-laced irreducible root systems

An irreducible finite reduced crystallographic root system with a multiple edge has
no nontrivial based automorphism. The classification reduces this to rigidity of the
oriented numbered Cartan matrices of `Bₙ`, `Cₙ`, `F₄`, and `G₂`. A length exchange is
not a counterexample: it transposes rather than preserves the Cartan matrix.

`RootPairing.Base.indexEquiv_eq_self_of_multiple_edge` fixes every root index,
not just the simple indices. It applies over any characteristic-zero domain with
the native root-system hypotheses; no choice of real coordinates is involved.
This is the nonsimply-laced branch in reducing finite diagram folding to simply-laced
components and cycles of components.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §4 and plates II–IV, VIII–IX.
-/

public section

namespace TauCeti.DynkinType

/-- A nonsimply-laced numbered Dynkin diagram has no nonidentity permutation
preserving its oriented Cartan matrix. -/
theorem eq_one_of_cartanMatrix_of_not_isSimplyLaced {t : DynkinType}
    (hsl : ¬ t.IsSimplyLaced) {ρ : Equiv.Perm (Fin t.rank)}
    (h : ∀ i j, t.cartanMatrix (ρ i) (ρ j) = t.cartanMatrix i j) : ρ = 1 := by
  cases t with
  | A n => exact (hsl (isSimplyLaced_A n)).elim
  | B n => exact eq_one_of_cartanMatrix_B h
  | C n => exact eq_one_of_cartanMatrix_C h
  | D n => exact (hsl (isSimplyLaced_D n)).elim
  | E6 => exact (hsl isSimplyLaced_E6).elim
  | E7 => exact (hsl isSimplyLaced_E7).elim
  | E8 => exact (hsl isSimplyLaced_E8).elim
  | F4 => exact eq_one_of_cartanMatrix_F4 h
  | G2 => exact eq_one_of_cartanMatrix_G2 h

end TauCeti.DynkinType

namespace RootPairing.Base

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
  [Finite ι] [IsDomain R] [CharZero R] [P.IsRootSystem] [P.IsReduced]
  [P.IsCrystallographic] [P.IsIrreducible]

/-- A based automorphism of an irreducible finite root system with a multiple edge
fixes every root index. The based condition is preservation of the simple support in
both directions. -/
theorem indexEquiv_eq_self_of_multiple_edge (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i, σ.indexEquiv i ∈ b.support ↔ i ∈ b.support)
    (hsl : ¬ b.cartanMatrix.IsSimplyLaced) (i : ι) : σ.indexEquiv i = i := by
  classical
  obtain ⟨t, ⟨ht, hb⟩, -⟩ := existsUnique_dynkinType b
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp hb
  let s := Equiv.Perm.subtypePerm σ.indexEquiv hσ
  let ρ : Equiv.Perm (Fin t.rank) := e.symm.trans (s.trans e)
  have hρ : ∀ j k, t.cartanMatrix (ρ j) (ρ k) = t.cartanMatrix j k := by
    intro j k
    simp only [ρ, Equiv.trans_apply]
    calc
      _ = b.cartanMatrix (s (e.symm j)) (s (e.symm k)) := (he _ _).symm
      _ = b.cartanMatrix (e.symm j) (e.symm k) := by
        simp only [s, Equiv.Perm.subtypePerm_apply, cartanMatrix, cartanMatrixIn_def]
        exact RootPairing.Hom.pairingIn_indexEquiv σ.toHom ℤ _ _
      _ = t.cartanMatrix j k := by simpa only [e.apply_symm_apply] using he (e.symm j) (e.symm k)
  have hρone := DynkinType.eq_one_of_cartanMatrix_of_not_isSimplyLaced
    (fun hc ↦ hsl ((hb.isSimplyLaced_iff_of_valid ht).mpr hc)) hρ
  have hsimple : ∀ j ∈ b.support, σ.indexEquiv j = j := by
    intro j hj
    have hj' := congrArg (fun p : Equiv.Perm (Fin t.rank) ↦ p (e ⟨j, hj⟩)) hρone
    have hs : s ⟨j, hj⟩ = ⟨j, hj⟩ := e.injective (by simpa [ρ] using hj')
    exact congrArg Subtype.val hs
  have hσone : σ = 1 := b.eq_one_of_forall_indexEquiv_eq hsimple
  simp [hσone]

end RootPairing.Base
