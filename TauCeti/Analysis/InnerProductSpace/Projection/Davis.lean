/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Analysis.InnerProductSpace.PositiveSquareRoot

/-!
# Davis's intertwining unitary

Two complete orthogonal projection families describe two orthogonal decompositions of a
finite-dimensional Hilbert space. If each target projection is injective on the corresponding
source range, a single unitary carries all source summands to the corresponding target summands.

The overlap operator `D = ∑ i, Q i * P i` intertwines the projections. Nondegeneracy makes it
invertible, and its unitary polar factor still intertwines them: its positive factor commutes
with every source projection. The existence theorem also specifies `U |D| = D`, which determines
the unitary uniquely and identifies its restriction to each summand with the block polar factor.
Zero summands and an empty indexing type are allowed.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl. **6**
  (1963), 159–173.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.3.1.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Fintype ι]

/-- A finite family of orthogonal projections with mutually orthogonal ranges and sum equal
to the identity. Orthogonality is expressed by vanishing products of distinct projections. -/
structure IsCompleteOrthogonalProjectionFamily (P : ι → E →ₗ[𝕜] E) : Prop where
  /-- Each member is an orthogonal projection. -/
  isStarProjection : ∀ i, IsStarProjection (P i)
  /-- Distinct projections annihilate each other. -/
  mul_eq_zero : ∀ i j, i ≠ j → P i * P j = 0
  /-- The ranges exhaust the ambient space. -/
  sum_eq_one : ∑ i, P i = 1

/-- The overlap between two projection families, with each source block sent into the
corresponding target block. -/
noncomputable def projectionFamilyOverlap (P Q : ι → E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  ∑ i, Q i * P i

omit [FiniteDimensional 𝕜 E] in
/-- The overlap operator is the sum of the matched projection products. -/
theorem projectionFamilyOverlap_def (P Q : ι → E →ₗ[𝕜] E) :
    projectionFamilyOverlap P Q = ∑ i, Q i * P i := (rfl)

/-- Davis nondegeneracy: every target projection is injective on the matching source range. -/
def ProjectionFamilyNondegenerate (P Q : ι → E →ₗ[𝕜] E) : Prop :=
  ∀ i, Set.InjOn (Q i) (P i).range

omit [FiniteDimensional 𝕜 E] [Fintype ι] in
/-- Pointwise characterization of nondegeneracy of matched projection blocks. -/
theorem projectionFamilyNondegenerate_iff (P Q : ι → E →ₗ[𝕜] E) :
    ProjectionFamilyNondegenerate P Q ↔ ∀ i, Set.InjOn (Q i) (P i).range := Iff.rfl

namespace IsCompleteOrthogonalProjectionFamily

variable {P Q : ι → E →ₗ[𝕜] E}

/-- The diagonal product is the projection itself, and every other product is zero. -/
theorem mul_eq_ite [DecidableEq ι] (hP : IsCompleteOrthogonalProjectionFamily P) (i j : ι) :
    P i * P j = if i = j then P i else 0 := by
  classical
  split_ifs with h
  · subst j
    exact (hP.isStarProjection i).isIdempotentElem.eq
  · exact hP.mul_eq_zero i j h

/-- Summing the projected components reconstructs a vector. -/
@[simp]
theorem sum_apply (hP : IsCompleteOrthogonalProjectionFamily P) (x : E) :
    ∑ i, P i x = x := by
  simpa using LinearMap.congr_fun hP.sum_eq_one x

/-- Restricting the overlap operator to a source block retains just its matched product. -/
@[simp]
theorem overlap_mul (hP : IsCompleteOrthogonalProjectionFamily P) (Q : ι → E →ₗ[𝕜] E)
    (i : ι) : projectionFamilyOverlap P Q * P i = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.sum_mul, mul_assoc, hP.mul_eq_ite, mul_ite]

/-- Projecting the overlap operator onto a target block retains just its matched product. -/
@[simp]
theorem mul_overlap (hQ : IsCompleteOrthogonalProjectionFamily Q) (P : ι → E →ₗ[𝕜] E)
    (i : ι) : Q i * projectionFamilyOverlap P Q = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.mul_sum, ← mul_assoc, hQ.mul_eq_ite, ite_mul]

/-- Nondegenerate matched overlaps give an injective overlap operator. -/
theorem overlap_injective (hP : IsCompleteOrthogonalProjectionFamily P)
    (hQ : IsCompleteOrthogonalProjectionFamily Q) (hPQ : ProjectionFamilyNondegenerate P Q) :
    Function.Injective (projectionFamilyOverlap P Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hzero (i : ι) : P i x = 0 := by
    apply hPQ i (LinearMap.mem_range_self _ _) (Submodule.zero_mem _)
    have hi := LinearMap.congr_fun (hQ.mul_overlap P i) x
    simpa [Module.End.mul_apply, hx] using hi.symm
  rw [← hP.sum_apply x]
  simp [hzero]

/-- Every source projection commutes with the modulus of the overlap operator. -/
theorem commute_operatorAbs_overlap (hP : IsCompleteOrthogonalProjectionFamily P)
    (hQ : IsCompleteOrthogonalProjectionFamily Q) (i : ι) :
    Commute (P i) (projectionFamilyOverlap P Q).operatorAbs := by
  let D := projectionFamilyOverlap P Q
  have hD : D * P i = Q i * D := by simp [D, hP.overlap_mul, hQ.mul_overlap]
  have hD' : P i * star D = star D * Q i := by
    simpa only [star_mul, (hP.isStarProjection i).isSelfAdjoint.star_eq,
      (hQ.isStarProjection i).isSelfAdjoint.star_eq] using congrArg star hD
  have hcomm' : Commute (P i) (star D * D) := by
    calc P i * (star D * D) = star D * (Q i * D) := by rw [← mul_assoc, hD', mul_assoc]
         _ = (star D * D) * P i := by rw [← hD, mul_assoc]
  have hcomm : Commute (P i) (D.adjoint ∘ₗ D) := by
    simpa only [LinearMap.star_eq_adjoint, Module.End.mul_eq_comp] using hcomm'
  exact D.commute_operatorAbs_of_commute_adjoint_comp_self hcomm

/-- **Davis's intertwining unitary.** Nondegenerate overlaps between two complete orthogonal
projection families admit a unitary intertwining all their matched projections simultaneously.
The unitary is the polar factor of their overlap operator `D`, characterized by `U |D| = D`. -/
theorem exists_intertwining_linearIsometryEquiv (hP : IsCompleteOrthogonalProjectionFamily P)
    (hQ : IsCompleteOrthogonalProjectionFamily Q) (hPQ : ProjectionFamilyNondegenerate P Q) :
    ∃ U : E ≃ₗᵢ[𝕜] E,
      U.toLinearMap ∘ₗ (projectionFamilyOverlap P Q).operatorAbs = projectionFamilyOverlap P Q ∧
      ∀ i, U.toLinearMap ∘ₗ P i = Q i ∘ₗ U.toLinearMap := by
  let D := projectionFamilyOverlap P Q
  have hS : Function.Surjective D.operatorAbs := by
    apply LinearMap.surjective_of_injective
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_operatorAbs]
    exact LinearMap.ker_eq_bot.mpr (hP.overlap_injective hQ hPQ)
  have hinner (x y : E) : ⟪D.operatorAbs x, D.operatorAbs y⟫_𝕜 = ⟪D x, D y⟫_𝕜 := by
    rw [← D.isSymmetric_operatorAbs, ← LinearMap.comp_apply, D.operatorAbs_sq,
      LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_inner_eq hinner
  refine ⟨U, LinearMap.ext hU, fun i ↦ LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hS x
  have hcomm := LinearMap.congr_fun (hP.commute_operatorAbs_overlap hQ i).eq y
  have hD : D (P i y) = Q i (D y) := by
    simpa only [Module.End.mul_apply] using
      LinearMap.congr_fun ((hP.overlap_mul Q i).trans (hQ.mul_overlap P i).symm) y
  simp only [Module.End.mul_apply] at hcomm hD
  exact (congrArg U hcomm).trans ((hU (P i y)).trans
    (hD.trans (congrArg (Q i) (hU y).symm)))

end IsCompleteOrthogonalProjectionFamily

end TauCeti
