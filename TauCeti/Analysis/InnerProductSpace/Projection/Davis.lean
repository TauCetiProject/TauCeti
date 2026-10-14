/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.ProjectionFamily
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

variable {𝕜 E ι : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- Davis nondegeneracy: every target projection is injective on the matching source range. -/
def ProjectionFamilyNondegenerate (P Q : ι → E →ₗ[𝕜] E) : Prop :=
  ∀ i, Set.InjOn (Q i) (P i).range

/-- Pointwise characterization of nondegeneracy of matched projection blocks. -/
theorem projectionFamilyNondegenerate_iff (P Q : ι → E →ₗ[𝕜] E) :
    ProjectionFamilyNondegenerate P Q ↔ ∀ i, Set.InjOn (Q i) (P i).range := Iff.rfl

end TauCeti

namespace CompleteOrthogonalIdempotents

open TauCeti

variable {𝕜 E ι : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [Fintype ι] {P Q : ι → E →ₗ[𝕜] E}

/-- Nondegenerate matched overlaps give an injective overlap operator. -/
theorem projectionFamilyOverlap_injective (hP : CompleteOrthogonalIdempotents P)
    (hQ : OrthogonalIdempotents Q) (hPQ : ProjectionFamilyNondegenerate P Q) :
    Function.Injective (projectionFamilyOverlap P Q : E →ₗ[𝕜] E) := by
  intro x y hxy
  have hcomponents (i : ι) : P i x = P i y := by
    apply hPQ i (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← hQ.mul_projectionFamilyOverlap P i]
    simpa only [Module.End.mul_apply] using congrArg (Q i) hxy
  rw [← hP.sum_apply_eq_self x, ← hP.sum_apply_eq_self y]
  exact Finset.sum_congr rfl fun i _ ↦ hcomponents i

end CompleteOrthogonalIdempotents

namespace TauCeti.IsCompleteOrthogonalProjectionFamily

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Fintype ι] {P Q : ι → E →ₗ[𝕜] E}

/-- Every source projection commutes with the modulus of the overlap operator. -/
theorem commute_operatorAbs_projectionFamilyOverlap (hP : IsCompleteOrthogonalProjectionFamily P)
    (hQ : IsCompleteOrthogonalProjectionFamily Q) (i : ι) :
    Commute (P i) (projectionFamilyOverlap P Q).operatorAbs := by
  let D := projectionFamilyOverlap P Q
  have hD : D * P i = Q i * D :=
    hP.toOrthogonalIdempotents.projectionFamilyOverlap_mul_eq_mul_projectionFamilyOverlap
      hQ.toOrthogonalIdempotents i
  have hD' : P i * star D = star D * Q i := by
    simpa only [star_mul, (hP.isSelfAdjoint i).star_eq,
      (hQ.isSelfAdjoint i).star_eq] using congrArg star hD
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
    exact LinearMap.ker_eq_bot.mpr
      (hP.toCompleteOrthogonalIdempotents.projectionFamilyOverlap_injective
        hQ.toOrthogonalIdempotents hPQ)
  have hinner (x y : E) : ⟪D.operatorAbs x, D.operatorAbs y⟫_𝕜 = ⟪D x, D y⟫_𝕜 := by
    rw [← D.isSymmetric_operatorAbs, ← LinearMap.comp_apply, D.operatorAbs_sq,
      LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_of_inner_eq hinner
  refine ⟨U, LinearMap.ext hU, fun i ↦ LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hS x
  have hcomm := LinearMap.congr_fun (hP.commute_operatorAbs_projectionFamilyOverlap hQ i).eq y
  have hD : D (P i y) = Q i (D y) := by
    simpa only [Module.End.mul_apply] using
      LinearMap.congr_fun
        (hP.toOrthogonalIdempotents.projectionFamilyOverlap_mul_eq_mul_projectionFamilyOverlap
          hQ.toOrthogonalIdempotents i) y
  simp only [Module.End.mul_apply] at hcomm hD
  exact (congrArg U hcomm).trans ((hU (P i y)).trans
    (hD.trans (congrArg (Q i) (hU y).symm)))

end TauCeti.IsCompleteOrthogonalProjectionFamily
