/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.TestFunction.Continuity
public import TauCeti.Geometry.Lie.TestFunction.RightDeriv
import TauCeti.Geometry.Lie.Adjoint.Smooth

/-!
# Continuity of right differentiation of test functions

Let `G` be a Lie group with finite-dimensional Lie algebra. The right differentiation
`R(X) a (g) = d/dt|₀ a (g exp(tX))` (`TauCeti.LieTestFunction.rightDeriv`) differentiates along
the left-invariant vector field `X^L`, while the fixed-support seminorms are built from the left
differentiations `L_Y`, which differentiate along right-invariant vector fields. The two kinds of
fields are related by the adjoint action: `X^L(g) = (Ad_g X)^R(g)`, because right translation by
`g` after conjugation by `g` is left translation by `g`
(`TauCeti.Lie.mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint`). Hence
`R(X) a (g) = L_{Ad_g X} a (g)`.

Since `L_Y` and `R(X)` commute, `L_w (R(X) a) = R(X) (L_w a)` for every word `w`. Expanding
`Ad_g X = ∑ᵢ cᵢ(g) Yᵢ` in a basis `Yᵢ`, with coefficients `cᵢ` continuous in `g`, bounds
`|L_w (R(X) a)|` on a compact set `C` by a constant times the fixed-support seminorms of `a` along
the words `Yᵢ :: w`. So `R(X)` is a continuous linear map on the fixed-support space of a compact
set, and continuous for the LF topology.

## Main definitions

* `TauCeti.LieTestFunction.FixedSupport.rightDeriv`: right differentiation `R(X)` as a continuous
  linear map on the fixed-support space of a compact set.

## Main results

* `TauCeti.Lie.mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint`:
  `X^L(g) = (Ad_g X)^R(g)`.
* `TauCeti.LieTestFunction.rightDeriv_apply_eq_leftDeriv_adjoint`:
  `R(X) a (g) = L_{Ad_g X} a (g)`.
* `TauCeti.LieTestFunction.leftDerivWord_rightDeriv`: `L_w (R(X) a) = R(X) (L_w a)`.
* `TauCeti.LieTestFunction.exists_fixedSupportSeminorm_rightDeriv_le`: the seminorm bound on a
  compact set.
* `TauCeti.LieTestFunction.continuous_rightDeriv`: `R(X)` is continuous for the LF topology.

## References

* J. Getz, *An introduction to automorphic representations*, course notes, §3.3, pp. 17–18.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

open Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace Lie

/-- **Left-invariant fields through the adjoint action**: the left-invariant vector field of `X`
at `g` is the right-invariant vector field of `Ad_g X` at `g`, `X^L(g) = (Ad_g X)^R(g)`, since
`(g x g⁻¹) g = g x`. -/
theorem mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint
    (X : GroupLieAlgebra I G) (g : G) :
    mulInvariantVectorField X g =
      mulRightInvariantVectorField (adjointContinuousLinearMap (I := I) g X) g := by
  have hreg : (1 : ℕ∞ω) ≠ 0 := by simp
  have hfun : (fun x : G ↦ x * g) ∘ (conjDiffeomorph (I := I) (n := 1) g) = (g * ·) := by
    funext x
    simp [mul_assoc]
  have h := congrArg (fun f : G → G ↦ mfderiv I I f 1 X) hfun
  rw [mfderiv_comp_apply (I := I) (I' := I) (I'' := I)] at h
  · rw [mfderiv_congr_point (I := I) (I' := I) (f := fun x : G ↦ x * g)
      (x := conjDiffeomorph (I := I) (n := 1) g 1) (x' := 1) (by simp)] at h
    rw [GroupLieAlgebra.mulInvariantVectorField_apply, mulRightInvariantVectorField_apply,
      adjointContinuousLinearMap_apply]
    exact h.symm
  · exact (contMDiff_mul_right (I := I) (n := ∞) (a := g)).contMDiffAt.mdifferentiableAt
      (by simp)
  · exact ((conjDiffeomorph (I := I) (n := 1) g).mdifferentiable hreg) _

end Lie

namespace LieTestFunction

/-- **Right differentiation is pointwise a left differentiation**:
`R(X) a (g) = L_{Ad_g X} a (g)`. -/
theorem rightDeriv_apply_eq_leftDeriv_adjoint (X : GroupLieAlgebra I G) (a : LieTestFunction I G)
    (g : G) : rightDeriv X a g = leftDeriv (adjointContinuousLinearMap (I := I) g X) a g := by
  rw [rightDeriv_apply, leftDeriv_apply,
    mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint]

/-- Iterated left differentiation commutes with right differentiation:
`L_w (R(X) a) = R(X) (L_w a)`. -/
theorem leftDerivWord_rightDeriv [CompleteSpace E] (w : List (GroupLieAlgebra I G))
    (X : GroupLieAlgebra I G) (a : LieTestFunction I G) :
    leftDerivWord w (rightDeriv X a) = rightDeriv X (leftDerivWord w a) := by
  induction w with
  | nil => simp
  | cons Y w ih => rw [leftDerivWord_cons, LinearMap.comp_apply, ih, leftDeriv_rightDeriv]; rfl

/-- Pointwise expansion of a left differentiation in a basis of the Lie algebra. -/
theorem leftDeriv_apply_eq_sum_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (GroupLieAlgebra I G)) (Y : GroupLieAlgebra I G)
    (a : LieTestFunction I G) (g : G) :
    leftDeriv Y a g = ∑ i, ((b.repr Y i : ℝ) : ℂ) * leftDeriv (b i) a g := by
  have h := congrArg (fun T ↦ toFunction I G (T a) g) (leftDeriv_eq_sum_basis b Y)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, toFunction_apply, smul_eq_mul] using h

variable [FiniteDimensional ℝ E]

/-- The coordinates of `Ad_g X` in a basis of the Lie algebra are continuous in `g`. -/
theorem continuous_repr_adjoint {ι : Type*} (b : Module.Basis ι ℝ (GroupLieAlgebra I G))
    (X : GroupLieAlgebra I G) (i : ι) :
    Continuous fun g : G ↦ b.repr (adjointContinuousLinearMap (I := I) g X) i := by
  have hAd : Continuous fun g : G ↦ show E from adjointContinuousLinearMap (I := I) g X :=
    (contMDiff_adjointContinuousLinearMap (I := I) (G := G)).continuous.clm_apply
      continuous_const
  exact (LinearMap.continuous_of_finiteDimensional (b.coord i : E →ₗ[ℝ] ℝ)).comp hAd

/-- **The seminorm bound for right differentiation.** On test functions supported in a compact
set `C`, each fixed-support seminorm of `R(X) a` along a word `w` is bounded by a constant, which
depends only on `C` and `X`, times the sum of the fixed-support seminorms of `a` along the words
`b i :: w`, for a basis `b` of the Lie algebra. -/
theorem exists_fixedSupportSeminorm_rightDeriv_le {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (GroupLieAlgebra I G)) {C : Set G} (hC : IsCompact C)
    (X : GroupLieAlgebra I G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : List (GroupLieAlgebra I G)) (a : LieTestFunction I G),
      tsupport a ⊆ C →
        fixedSupportSeminorm w (rightDeriv X a) ≤
          K * ∑ i, fixedSupportSeminorm (b i :: w) a := by
  -- A bound `K` for the sum of the absolute coordinates of `Ad_g X` on `C`.
  let c (g : G) : ℝ := ∑ i, ‖b.repr (adjointContinuousLinearMap (I := I) g X) i‖
  have hc : Continuous c := continuous_finsetSum _ fun i _ ↦
    (continuous_repr_adjoint b X i).norm
  obtain ⟨K, hK⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun w a ha ↦ ?_⟩
  have hS : 0 ≤ ∑ i, fixedSupportSeminorm (b i :: w) a :=
    Finset.sum_nonneg fun i _ ↦ apply_nonneg _ _
  refine fixedSupportSeminorm_le_of_tsupport_subset w
    ((tsupport_rightDeriv_subset X a).trans ha) (mul_nonneg (le_max_right _ _) hS)
    fun g hg ↦ ?_
  have := FiniteDimensional.completeSpace ℝ E
  rw [leftDerivWord_rightDeriv, rightDeriv_apply_eq_leftDeriv_adjoint,
    leftDeriv_apply_eq_sum_basis b]
  calc ‖∑ i, ((b.repr (adjointContinuousLinearMap (I := I) g X) i : ℝ) : ℂ) *
          leftDeriv (b i) (leftDerivWord w a) g‖
      ≤ ∑ i, ‖b.repr (adjointContinuousLinearMap (I := I) g X) i‖ *
          ∑ j, fixedSupportSeminorm (b j :: w) a := norm_sum_le_of_le _ fun i _ ↦ by
        rw [norm_mul, Complex.norm_real]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hi := norm_leftDerivWord_le (b i :: w) a g
        rw [leftDerivWord_cons, LinearMap.comp_apply] at hi
        refine hi.trans ?_
        exact Finset.single_le_sum (f := fun j ↦ fixedSupportSeminorm (b j :: w) a)
          (fun j _ ↦ apply_nonneg _ _) (Finset.mem_univ i)
    _ = c g * ∑ j, fixedSupportSeminorm (b j :: w) a := (Finset.sum_mul _ _ _).symm
    _ ≤ max K 0 * ∑ j, fixedSupportSeminorm (b j :: w) a := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        have := hK g hg
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)] at this
        exact this.trans (le_max_left _ _)

namespace FixedSupport

/-- **Right differentiation** `R(X)` on the fixed-support space of a compact set `C`, a
continuous linear map, by the seminorm bound
`TauCeti.LieTestFunction.exists_fixedSupportSeminorm_rightDeriv_le`. -/
def rightDeriv {C : Set G} (hC : IsCompact C) (X : GroupLieAlgebra I G) :
    FixedSupport I G C →L[ℂ] FixedSupport I G C :=
  let f : FixedSupport I G C →ₗ[ℂ] FixedSupport I G C :=
    { toFun a := mk (LieTestFunction.rightDeriv X (inclusion I G C a))
        ((tsupport_rightDeriv_subset X _).trans (tsupport_inclusion_subset a))
      map_add' a b := ext (by simp)
      map_smul' c a := ext (by simp) }
  ⟨f, (withSeminorms I G C).continuous_of_isBounded (withSeminorms I G C) f
    (Seminorm.IsBounded.of_real fun w ↦ by
      classical
      let n := Module.finrank ℝ (GroupLieAlgebra I G)
      let b := Module.finBasis ℝ (GroupLieAlgebra I G)
      obtain ⟨K, hK0, hK⟩ := exists_fixedSupportSeminorm_rightDeriv_le b hC X
      refine ⟨Finset.univ.image fun i ↦ b i :: w, K * (n : ℝ), fun a ↦ ?_⟩
      have hsum : ∑ i, fixedSupportSeminorm (b i :: w) (inclusion I G C a) ≤
          (n : ℝ) *
            ((Finset.univ.image fun i ↦ b i :: w).sup (seminormFamily I G C)) a := by
        rw [← nsmul_eq_mul, ← Fintype.card_fin n, ← Finset.card_univ]
        refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
        rw [← seminormFamily_apply]
        exact Seminorm.le_finset_sup_apply (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      calc seminormFamily I G C w (f a)
          = fixedSupportSeminorm w (LieTestFunction.rightDeriv X (inclusion I G C a)) := by
            rw [seminormFamily_apply]
            simp [f]
        _ ≤ K * ∑ i, fixedSupportSeminorm (b i :: w) (inclusion I G C a) :=
            hK w _ (tsupport_inclusion_subset a)
        _ ≤ K * ((n : ℝ) *
            ((Finset.univ.image fun i ↦ b i :: w).sup (seminormFamily I G C)) a) :=
            mul_le_mul_of_nonneg_left hsum hK0
        _ = _ := (mul_assoc _ _ _).symm)⟩

@[simp]
theorem inclusion_rightDeriv {C : Set G} (hC : IsCompact C) (X : GroupLieAlgebra I G)
    (a : FixedSupport I G C) :
    inclusion I G C (rightDeriv hC X a) = LieTestFunction.rightDeriv X (inclusion I G C a) :=
  inclusion_mk _ _

end FixedSupport

/-- **Right differentiation `R(X)` is continuous for the LF topology.** -/
theorem continuous_rightDeriv (X : GroupLieAlgebra I G) :
    Continuous (rightDeriv (I := I) (G := G) X) :=
  continuous_of_fixedSupport_lift _ fun C ↦
    ⟨C, FixedSupport.rightDeriv C.isCompact X, FixedSupport.inclusion_rightDeriv C.isCompact X⟩

end LieTestFunction

end TauCeti
