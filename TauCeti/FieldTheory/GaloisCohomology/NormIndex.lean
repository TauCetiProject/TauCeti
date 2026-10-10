/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Cyclic
public import TauCeti.RingTheory.Norm.Equiv

/-!
# The Herbrand quotient as a norm index

For a finite cyclic Galois extension `L/K`, Hilbert 90 and two-periodicity identify the
Herbrand quotient of `Lˣ` with the index of `N(Lˣ)` in `Kˣ`. This is a numerical consequence
of `TauCeti.cyclicNormQuotientEquiv` and `TauCeti.natCard_H2_units_eq_herbrandQuotient`;
it does not use reciprocity or assume that the index equals the extension degree.
For finite extensions of an algebraically closed field the quotient is one, since
such an extension is isomorphic to the identity extension.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, §4.
-/

public noncomputable section

namespace TauCeti

/-- The Herbrand quotient of the multiplicative group of a finite cyclic Galois extension
is the index of its norm group in the ground field's units. -/
@[simp]
theorem herbrandQuotient_units_eq_index_normGroup {K L : Type} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) =
      (normGroup K L).index := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [← natCard_H2_units_eq_herbrandQuotient, Subgroup.index]
  exact congrArg (Nat.cast : ℕ → ℚ)
    (Nat.card_congr (cyclicNormQuotientEquiv hg).toEquiv).symm

/-- A finite extension of an algebraically closed field has multiplicative-group Herbrand
quotient one. In particular, a complex place contributes the factor one. -/
@[simp]
theorem herbrandQuotient_units_eq_one_of_isAlgClosed (K L : Type) [Field K] [Field L]
    [Algebra K L] [IsAlgClosed K] [FiniteDimensional K L] :
    TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) = 1 := by
  let e := AlgEquiv.ofBijective (Algebra.ofId K L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))
  have : IsGalois K L := IsGalois.of_algEquiv e
  have : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_injective e.symm.autCongr.toMonoidHom e.symm.autCongr.injective
  rw [herbrandQuotient_units_eq_index_normGroup, normGroup_eq_top_of_isAlgClosed,
    Subgroup.index_top, Nat.cast_one]


end TauCeti
