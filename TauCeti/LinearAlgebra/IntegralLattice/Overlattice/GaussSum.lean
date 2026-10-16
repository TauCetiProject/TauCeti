/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.GaussSum
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.OrthogonalQuotient.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Restriction

/-!
# Gauss sums of even overlattices

For even nondegenerate lattices `L ≤ M` in the same rational quadratic space, the Gauss
sums of their discriminant forms satisfy `G(q_L) = [M : L] G(q_M)`. Their Gauss-sum
invariants are consequently equal. The discriminant form of `M` is the orthogonal
quotient along the quadratic-isotropic subgroup `M / L`, so these are applications of
isotropic reduction to the canonical discriminant modules.

The invariance permits comparisons of discriminant Gauss sums through even overlattices
without changing the rational quadratic space, as needed when comparing them to signature.
Read from the other side, it says that restricting an even lattice to a full sublattice
(`TauCeti.IntegralLattice.restrictFull`) does not change the Gauss-sum invariant.
No definiteness hypothesis is required.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti.IntegralLattice.IntermediateCarrier

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {L : IntegralLattice V} [L.IsNondegenerate] {M : L.IntermediateCarrier}

/-- The Gauss sum of the discriminant form of an even lattice is the index of an even
overlattice times the Gauss sum of that overlattice's discriminant form. -/
theorem gaussSum_discriminantQuadraticModule_eq_index_mul (hL : L.IsEven) (hM : IsEven M) :
    (L.discriminantQuadraticModule hL).gaussSum = index M *
      (hM.isIntegral.toIntegralLattice.discriminantQuadraticModule
        hM.isEven_toIntegralLattice).gaussSum := by
  rw [index_eq_natCard_discriminantSubgroup]
  have hH := (isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM
  rw [(L.discriminantQuadraticModule hL).gaussSum_eq_card_mul_gaussSum_orthogonalQuotient hH,
    ← (discriminantOrthogonalQuotientIsometry hL hM).gaussSum_eq]
  rfl

/-- Passing to an even overlattice preserves the Gauss-sum invariant of the discriminant
quadratic form. -/
@[simp]
theorem gaussSign_discriminantQuadraticModule (hL : L.IsEven) (hM : IsEven M) :
    (hM.isIntegral.toIntegralLattice.discriminantQuadraticModule
      hM.isEven_toIntegralLattice).gaussSign = (L.discriminantQuadraticModule hL).gaussSign := by
  rw [(discriminantOrthogonalQuotientIsometry hL hM).gaussSign_eq]
  exact (L.discriminantQuadraticModule hL).gaussSign_orthogonalQuotient
    (L.isNondegenerate_discriminantQuadraticModule hL)
    ((isEven_iff_isIsotropic_discriminantSubgroup hL M).mp hM)

end TauCeti.IntegralLattice.IntermediateCarrier

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Passing to a full sublattice preserves the Gauss-sum invariant of the discriminant quadratic
form of an even nondegenerate lattice. -/
@[simp]
theorem gaussSign_discriminantQuadraticModule_restrictFull (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) (N : Submodule ℤ V) (hN : N ≤ L.carrier)
    [N.IsLattice ℚ] :
    ((L.restrictFull N hN).discriminantQuadraticModule (isEven_restrictFull hL N hN)).gaussSign =
      (L.discriminantQuadraticModule hL).gaussSign := by
  set K := L.restrictFull N hN
  have hle : K.carrier ≤ L.carrier := by rwa [restrictFull_carrier]
  have hdual : L.carrier ≤ K.dualCarrier := fun x hx ↦ by
    rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [restrictFull_form]
    exact L.form_mem_one ⟨x, hx⟩ ⟨y, hle hy⟩
  let M : K.IntermediateCarrier := ⟨L.carrier, hle, hdual⟩
  have hM : IntermediateCarrier.IsEven M := IntermediateCarrier.isEven_def.mpr fun x hx ↦ by
    obtain ⟨z, hz⟩ := hL.exists_norm_eq_two_mul ⟨x, hx⟩
    exact ⟨z, by rwa [norm_apply, restrictFull_form, ← norm_apply]⟩
  have hLM : hM.isIntegral.toIntegralLattice = L := IntegralLattice.ext
    (IntermediateCarrier.IsIntegral.toIntegralLattice_carrier _)
    ((IntermediateCarrier.IsIntegral.toIntegralLattice_form _).trans (restrictFull_form _ _ _))
  rw [← IntermediateCarrier.gaussSign_discriminantQuadraticModule _ hM,
    ((Isometry.ofEq hLM).discriminantQuadraticIsometry hM.isEven_toIntegralLattice).gaussSign_eq]

end TauCeti.IntegralLattice
