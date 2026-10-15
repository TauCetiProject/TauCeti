/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic

/-!
# Scalar extension of pinned root-space trivializations

The chosen trivializations of two simple root spaces identify the scalar extension
of the first with the second, preserving scalar coordinates and chosen generators.
The pinnings and roots may be arbitrary; this rank-one identification alone does not
assert that the second group is the base change of the first. For the standard
special-linear and symplectic pinnings, their `Pinning.BaseChange` modules prove
that this identification agrees with geometric tangent base change.

## References

* `SpecialLinear.Pinning.BaseChange` and `Symplectic.Pinning.BaseChange`:
  the standard pinned root-space comparisons.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Pinning

universe u v

noncomputable section

variable {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
  {H : CommHopfAlgCat.{u} R} {H' : CommHopfAlgCat.{v} K}
  [Algebra.FiniteType R H] [Algebra.FiniteType K H']
  [Algebra.Smooth R H] [Algebra.Smooth K H']
  [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum K)]
  {r s : ℕ} (P : Pinning R H r) (Q : Pinning K H' s)
  (α : {α // P.torus.IsSimpleRoot P.borel α})
  (β : {β // Q.torus.IsSimpleRoot Q.borel β})

/-- Identify a scalar-extended simple root space with another pinned simple root
space using their chosen trivializations. -/
def rootSpaceBaseChangeEquiv :
    K ⊗[R] Derivation.adjointWeightSpace P.torus.coordinateMap.hom
        (Multiplicative.ofAdd α.val) ≃ₗ[K]
      Derivation.adjointWeightSpace Q.torus.coordinateMap.hom
        (Multiplicative.ofAdd β.val) :=
  ((P.rootSpaceEquiv α).symm.baseChange R K _ _).trans
    ((TensorProduct.AlgebraTensorModule.rid R K K).trans (Q.rootSpaceEquiv β))

/-- The root-space comparison preserves the chosen scalar coordinates. -/
@[simp↓]
theorem rootSpaceBaseChangeEquiv_tmul (c : K) (b : R) :
    P.rootSpaceBaseChangeEquiv Q α β (c ⊗ₜ[R] P.rootSpaceEquiv α b) =
      Q.rootSpaceEquiv β (c * algebraMap R K b) := by
  simp only [rootSpaceBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rw [mul_comm]

/-- The inverse comparison expresses a chosen vector as its scalar coordinate
times the chosen generator over the original base. -/
@[simp↓]
theorem rootSpaceBaseChangeEquiv_symm_apply (c : K) :
    (P.rootSpaceBaseChangeEquiv Q α β).symm (Q.rootSpaceEquiv β c) =
      c ⊗ₜ[R] P.rootSpaceEquiv α 1 := by
  apply (P.rootSpaceBaseChangeEquiv Q α β).symm_apply_eq.mpr
  rw [rootSpaceBaseChangeEquiv_tmul, map_one, mul_one]

end

end TauCeti.Pinning
