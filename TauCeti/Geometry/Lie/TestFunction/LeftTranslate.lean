/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.TestFunction.Continuity

/-!
# Continuity of left translation of test functions on a Lie group

Left translation `λ_g a (x) = a (g⁻¹ x)` does not commute with left differentiation
`L_X a (y) = d/dt|₀ a (exp(tX) y)`: since `g⁻¹ exp(tX) y = exp(t Ad(g⁻¹) X) g⁻¹ y`,

`L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)` (`TauCeti.LieTestFunction.leftDeriv_leftTranslate`).

On vector fields this is the statement that the derivative of left multiplication by `g` carries
the right-invariant field of `X` to that of `Ad(g) X`
(`TauCeti.mfderiv_mul_left_mulRightInvariantVectorField`): `g x y = (g x g⁻¹) (g y)`, so left
multiplication by `g` after right multiplication by `y` is conjugation by `g` followed by right
multiplication by `g y`.

Consequently the fixed-support seminorm of `λ_g a` along a word `w` is that of `a` along the word
`Ad(g⁻¹) w` (`TauCeti.LieTestFunction.fixedSupportSeminorm_leftTranslate`), and left translation
is a continuous linear map from the test functions supported in `C` to those supported in `g C`
(`TauCeti.LieTestFunction.FixedSupport.leftTranslate`), hence continuous for the LF topology
(`TauCeti.LieTestFunction.continuous_leftTranslate`).

## Main results

* `TauCeti.mfderiv_mul_left_mulRightInvariantVectorField`: left multiplication by `g` transports
  `X^R` to `(Ad(g) X)^R`.
* `TauCeti.LieTestFunction.leftDeriv_leftTranslate`: `L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)`.
* `TauCeti.LieTestFunction.fixedSupportSeminorm_leftTranslate`: the seminorms of a left translate.
* `TauCeti.LieTestFunction.FixedSupport.leftTranslate`: left translation on fixed-support spaces.
* `TauCeti.LieTestFunction.continuous_leftTranslate`: left translation is continuous for the LF
  topology.
-/

public section

open scoped ContDiff Manifold Topology Pointwise

namespace TauCeti

open TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- **Left multiplication transports right-invariant fields through the adjoint action.** The
derivative at `y` of `x ↦ g * x` sends the right-invariant field of `X` at `y` to the
right-invariant field of `Ad(g) X` at `g * y`. -/
theorem mfderiv_mul_left_mulRightInvariantVectorField (g y : G) (X : GroupLieAlgebra I G) :
    mfderiv I I (g * ·) y (mulRightInvariantVectorField X y) =
      mulRightInvariantVectorField (adjointContinuousLinearMap (I := I) g X) (g * y) := by
  have hreg : (1 : ℕ∞ω) ≠ 0 := by simp
  let C := conjDiffeomorph (I := I) (n := 1) g
  -- `g * (x * y) = (g * x * g⁻¹) * (g * y)`.
  have hfun : (fun x : G ↦ g * x) ∘ (· * y) = (· * (g * y)) ∘ C := by
    funext x
    simp [C, mul_assoc]
  rw [mulRightInvariantVectorField_apply, mulRightInvariantVectorField_apply,
    adjointContinuousLinearMap_apply,
    ← mfderiv_comp_apply_of_eq (1 : G) (contMDiffAt_mul_left.mdifferentiableAt hreg)
      (mdifferentiableAt_mul_right (a := y) (b := 1)) (one_mul y), hfun]
  have hD : HasMFDerivAt I I ((· * (g * y)) ∘ C) 1
      ((mfderiv I I (· * (g * y)) (C 1)).comp (mfderiv I I C 1)) :=
    (mdifferentiableAt_mul_right (a := g * y) (b := C 1)).hasMFDerivAt.comp 1
      ((C.mdifferentiable (by simp)) 1).hasMFDerivAt
  rw [hD.mfderiv]
  change mfderiv I I (· * (g * y)) (C 1) (mfderiv I I C 1 X) = _
  rw [show C 1 = 1 by simp [C]]

namespace LieTestFunction

/-- **Left differentiation of a left translate**: `L_X (λ_g a) = λ_g (L_{Ad(g⁻¹) X} a)`. -/
theorem leftDeriv_leftTranslate (X : GroupLieAlgebra I G) (g : G) (a : LieTestFunction I G) :
    leftDeriv X (leftTranslate g a) =
      leftTranslate g (leftDeriv (adjointContinuousLinearMap (I := I) g⁻¹ X) a) := by
  have hreg : (1 : ℕ∞ω) ≠ 0 := by simp
  ext y
  have hcoe : ⇑(leftTranslate g a) = a ∘ (g⁻¹ * ·) := funext fun x ↦ leftTranslate_apply g a x
  rw [leftDeriv_apply, leftTranslate_apply, leftDeriv_apply, hcoe,
    mvfderiv_comp_apply y (a.contMDiff.mdifferentiableAt (by simp))
      (contMDiffAt_mul_left.mdifferentiableAt hreg),
    mfderiv_mul_left_mulRightInvariantVectorField]

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
    fun w ↦ ⟨w.map (adjointContinuousLinearMap (I := I) g⁻¹),
      fun a _ ↦ (fixedSupportSeminorm_leftTranslate w g a).le⟩

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
