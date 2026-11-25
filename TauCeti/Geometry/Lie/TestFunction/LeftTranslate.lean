/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.TestFunction.Continuity

/-!
# Continuity of left translation of test functions on a Lie group

Left translation `λ_g a (x) = a (g⁻¹ x)` does not commute with left differentiation
`L_X a (y) = d/dt|₀ a (exp(tX) y)`: since `g⁻¹ exp(tX) y = exp(t Ad(g⁻¹) X) g⁻¹ y`,

`L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)` (`TauCeti.LieTestFunction.leftDeriv_leftTranslate`).

On vector fields this is the statement that the derivative of left multiplication by `g` carries
the right-invariant field of `X` to that of `Ad(g) X`: the right-invariant fields are the
fundamental vector fields of `G` acting on itself by left multiplication
(`TauCeti.fundamentalVectorField_eq_mulRightInvariantVectorField`), and these are equivariant
(`TauCeti.mfderiv_smul_fundamentalVectorField`).

Consequently the fixed-support seminorm of `λ_g a` along a word `w` is that of `a` along the word
`Ad(g⁻¹) w` (`TauCeti.LieTestFunction.fixedSupportSeminorm_leftTranslate`), and left translation
is a continuous linear map from the test functions supported in `C` to those supported in `g C`
(`TauCeti.LieTestFunction.FixedSupport.leftTranslate`), hence continuous for the LF topology
(`TauCeti.LieTestFunction.continuous_leftTranslate`).

## Main results

* `TauCeti.LieTestFunction.leftDeriv_leftTranslate`: `L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)`.
* `TauCeti.LieTestFunction.fixedSupportSeminorm_leftTranslate`: the seminorms of a left translate.
* `TauCeti.LieTestFunction.FixedSupport.leftTranslate`: left translation on fixed-support spaces.
* `TauCeti.LieTestFunction.continuous_leftTranslate`: left translation is continuous for the LF
  topology.

## References

* J. Getz, *An introduction to automorphic representations*, course notes, §3.3, pp. 17–18.
-/

public section

open scoped ContDiff Manifold Topology Pointwise

namespace TauCeti

open TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace LieTestFunction

/-- **Left differentiation of a left translate**: `L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)`. -/
theorem leftDeriv_leftTranslate (X : GroupLieAlgebra I G) (g : G) (a : LieTestFunction I G) :
    leftDeriv X (leftTranslate g a) =
      leftTranslate g (leftDeriv (adjointContinuousLinearMap (I := I) g⁻¹ X) a) := by
  have hreg : (1 : ℕ∞ω) ≠ 0 := by simp
  ext y
  have hcoe : ⇑(leftTranslate g a) = a ∘ (g⁻¹ * ·) := funext fun x ↦ leftTranslate_apply g a x
  have : ContMDiffSMul I I 1 G G := ⟨contMDiff_mul I 1⟩
  -- For `G` acting on itself by left multiplication, right-invariant fields are fundamental
  -- vector fields, which left multiplication by `g⁻¹` transports through `Ad(g⁻¹)`.
  have h := mfderiv_smul_fundamentalVectorField (M := G) (I' := I) g⁻¹ X y
  rw [fundamentalVectorField_eq_mulRightInvariantVectorField,
    fundamentalVectorField_eq_mulRightInvariantVectorField] at h
  rw [leftDeriv_apply, leftTranslate_apply, leftDeriv_apply, hcoe,
    mvfderiv_comp_apply y (a.contMDiff.mdifferentiableAt (by simp))
      (contMDiffAt_mul_left.mdifferentiableAt hreg)]
  -- `g⁻¹ • x` is `g⁻¹ * x` by definition of the action of a monoid on itself.
  exact congrArg _ h

/-- Iterated left differentiation of a left translate:
`L_{X_w} (λ_g a) = λ_g (L_{Ad(g⁻¹) X_w} a)`. -/
theorem leftDerivWord_leftTranslate (w : List (GroupLieAlgebra I G)) (g : G)
    (a : LieTestFunction I G) :
    leftDerivWord w (leftTranslate g a) =
      leftTranslate g (leftDerivWord (w.map (adjointContinuousLinearMap (I := I) g⁻¹)) a) := by
  induction w with
  | nil => simp
  | cons X w ih =>
    rw [leftDerivWord_cons, LinearMap.comp_apply, ih, leftDeriv_leftTranslate, List.map_cons,
      leftDerivWord_cons, LinearMap.comp_apply]

/-- **The seminorms of a left translate**: the fixed-support seminorm of `λ_g a` along `w` is
that of `a` along `Ad(g⁻¹) w`. -/
@[simp]
theorem fixedSupportSeminorm_leftTranslate (w : List (GroupLieAlgebra I G)) (g : G)
    (a : LieTestFunction I G) :
    fixedSupportSeminorm w (leftTranslate g a) =
      fixedSupportSeminorm (w.map (adjointContinuousLinearMap (I := I) g⁻¹)) a := by
  refine le_antisymm ((fixedSupportSeminorm_le_iff w _ (apply_nonneg _ _)).2 fun x ↦ ?_)
    ((fixedSupportSeminorm_le_iff _ _ (apply_nonneg _ _)).2 fun x ↦ ?_)
  · rw [leftDerivWord_leftTranslate, leftTranslate_apply]
    exact norm_leftDerivWord_le _ a _
  · have h := norm_leftDerivWord_le w (leftTranslate g a) (g * x)
    rwa [leftDerivWord_leftTranslate, leftTranslate_apply, inv_mul_cancel_left] at h

namespace FixedSupport

variable {C : Set G}

/-- **Left translation** by `g`, from the fixed-support space of `C` to that of `g C`, a
continuous linear map: the seminorm along `w` of a translate is the seminorm along `Ad(g⁻¹) w`. -/
noncomputable def leftTranslate (g : G) : FixedSupport I G C →L[ℂ] FixedSupport I G (g • C) :=
  mkCLM (LieTestFunction.leftTranslate g)
    (fun a ha ↦ by
      rw [tsupport_leftTranslate]
      exact Set.smul_set_mono ha)
    fun w ↦ ⟨{w.map (adjointContinuousLinearMap (I := I) g⁻¹)}, 1, fun a _ ↦ by
      rw [Finset.sum_singleton, one_mul]
      exact (fixedSupportSeminorm_leftTranslate w g a).le⟩

@[simp]
theorem inclusion_leftTranslate (g : G) (a : FixedSupport I G C) :
    inclusion I G (g • C) (leftTranslate g a) =
      LieTestFunction.leftTranslate g (inclusion I G C a) :=
  inclusion_mkCLM _ _ _ a

end FixedSupport

/-- **Left translation is continuous** for the LF topology. -/
theorem continuous_leftTranslate (g : G) :
    Continuous (leftTranslate (I := I) (G := G) g) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact continuous_of_fixedSupport_lift _ fun C ↦
    ⟨⟨g • (C : Set G), C.isCompact.smul _⟩, FixedSupport.leftTranslate g,
      FixedSupport.inclusion_leftTranslate g⟩

end LieTestFunction

end TauCeti
