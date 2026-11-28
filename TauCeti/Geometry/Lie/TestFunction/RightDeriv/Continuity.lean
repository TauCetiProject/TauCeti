/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.TestFunction.Continuity
public import TauCeti.Geometry.Lie.TestFunction.RightDeriv.Basic
import TauCeti.Geometry.Lie.Adjoint.Smooth

/-!
# Continuity of right differentiation of test functions

Let `G` be a Lie group with finite-dimensional Lie algebra. The right differentiation
`R(X) a (g) = d/dt|₀ a (g exp(tX))` (`TauCeti.LieTestFunction.rightDeriv`) differentiates along
the left-invariant vector field `X^L`, while the fixed-support seminorms are built from the left
differentiations `L_Y`, which differentiate along right-invariant vector fields. The two kinds of
fields are related by the adjoint action, `X^L(g) = (Ad_g X)^R(g)`
(`TauCeti.Lie.mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint`). Hence
`R(X) a (g) = L_{Ad_g X} a (g)`.

Since `L_Y` and `R(X)` commute, `L_w (R(X) a) = R(X) (L_w a)` for every word `w`
(`TauCeti.LieTestFunction.leftDerivWord_rightDeriv`). Expanding `Ad_g X = ∑ᵢ cᵢ(g) Yᵢ` in a basis
`Yᵢ`, with coefficients `cᵢ` continuous in `g` (`TauCeti.Lie.continuous_repr_adjoint`), bounds
`|L_w (R(X) a)|` on a compact set `C` by a constant times the fixed-support seminorms of `a` along
the words `Yᵢ :: w`. So `R(X)` is a continuous linear map on the fixed-support space of a compact
set, and continuous for the LF topology.

## Main definitions

* `TauCeti.LieTestFunction.FixedSupport.rightDeriv`: right differentiation `R(X)` as a continuous
  linear map on the fixed-support space of a compact set.

## Main results

* `TauCeti.LieTestFunction.rightDeriv_apply_eq_leftDeriv_adjoint`:
  `R(X) a (g) = L_{Ad_g X} a (g)`.
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

namespace LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- **Right differentiation is pointwise a left differentiation**:
`R(X) a (g) = L_{Ad_g X} a (g)`. -/
theorem rightDeriv_apply_eq_leftDeriv_adjoint (X : GroupLieAlgebra I G) (a : LieTestFunction I G)
    (g : G) : rightDeriv X a g = leftDeriv (adjointContinuousLinearMap (I := I) g X) a g := by
  rw [rightDeriv_apply, leftDeriv_apply,
    mulInvariantVectorField_eq_mulRightInvariantVectorField_adjoint]

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
  -- The basis `b` is finite, so the Lie algebra, which is the model space `E`, is
  -- finite-dimensional.
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  have := FiniteDimensional.completeSpace ℝ E
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

variable [FiniteDimensional ℝ E]

namespace FixedSupport

/-- **Right differentiation** `R(X)` on the fixed-support space of a compact set `C`, a
continuous linear map, by the seminorm bound
`TauCeti.LieTestFunction.exists_fixedSupportSeminorm_rightDeriv_le`. -/
def rightDeriv {C : Set G} (hC : IsCompact C) (X : GroupLieAlgebra I G) :
    FixedSupport I G C →L[ℂ] FixedSupport I G C :=
  mkCLM (LieTestFunction.rightDeriv X) (fun a ha ↦ (tsupport_rightDeriv_subset X a).trans ha)
    fun w ↦ by
      let b := Module.finBasis ℝ (GroupLieAlgebra I G)
      obtain ⟨K, -, hK⟩ := exists_fixedSupportSeminorm_rightDeriv_le b hC X
      refine ⟨Finset.univ.map ⟨fun i ↦ b i :: w, fun i j h ↦ b.injective (List.cons.inj h).1⟩,
        K, fun a ha ↦ ?_⟩
      rw [Finset.sum_map]
      exact hK w a ha

@[simp]
theorem inclusion_rightDeriv {C : Set G} (hC : IsCompact C) (X : GroupLieAlgebra I G)
    (a : FixedSupport I G C) :
    inclusion I G C (rightDeriv hC X a) = LieTestFunction.rightDeriv X (inclusion I G C a) :=
  inclusion_mkCLM _ _ _ a

end FixedSupport

/-- **Right differentiation `R(X)` is continuous for the LF topology.** -/
theorem continuous_rightDeriv (X : GroupLieAlgebra I G) :
    Continuous (rightDeriv (I := I) (G := G) X) :=
  continuous_of_fixedSupport_lift _ fun C ↦
    ⟨C, FixedSupport.rightDeriv C.isCompact X, FixedSupport.inclusion_rightDeriv C.isCompact X⟩

end LieTestFunction

end TauCeti
