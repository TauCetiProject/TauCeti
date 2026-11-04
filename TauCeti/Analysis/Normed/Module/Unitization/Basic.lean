/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Unitized bounded actions and Banach left modules

A bounded bilinear action extends to the ℓ¹ unitization without an associativity assumption
via `ContinuousLinearMap.unitizationActionL`. Its norm is at most `1 + ‖L‖`.

Let `A` be a possibly nonunital normed algebra acting on a normed space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`. The action extends
to a unital algebra homomorphism from the `ℓ¹` unitization `A⁺ = WithLp 1 (Unitization 𝕜 A)` to
`E →L[𝕜] E`, sending `(λ, a)` to `λ • id + L a`. This file constructs it and records its apply
formula, its norm bound, and the invariance under `A⁺` of the points where a left approximate
identity converges.

## Main declarations

* `ContinuousLinearMap.unitizationActionL`: the bounded unital extension of a bilinear action.
* `ContinuousLinearMap.unitizationAction`: the unital action of `A⁺` extending `L`.
* `ContinuousLinearMap.unitizationAction_apply`: `(λ, a) · z = λ • z + L a z`.
* `ContinuousLinearMap.norm_unitizationAction_apply_le`: `‖u · z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖`.
* `ContinuousLinearMap.tendsto_apply_unitizationAction`,
  `ContinuousLinearMap.unitizationAction_apply_mem_closure`: if a left approximate identity
  converges at `x`, it converges at every `u · x`, and `u · x` lies in the closure of `A · x`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3 and 2.8.
-/

public section

open Filter Topology Unitization WithLp

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Extend a bounded bilinear action to the ℓ¹ unitization by letting its new identity
act as the identity on `E`. The algebra argument comes first, also for right actions. -/
noncomputable def unitizationActionL (M : A →L[𝕜] E →L[𝕜] E) :
    WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E :=
  let f : WithLp 1 (Unitization 𝕜 A) →ₗ[𝕜] E →L[𝕜] E :=
    ((fstHom 𝕜 A).toLinearMap.smulRight (ContinuousLinearMap.id 𝕜 E) +
      M.toLinearMap.comp (sndHom 𝕜 𝕜 A)).comp (unitizationAlgEquiv 𝕜).toLinearMap
  f.mkContinuous (1 + ‖M‖) fun u ↦ by
    -- The linear-map expression above computes to the sum of the two coordinate actions.
    dsimp [f]
    calc
      ‖(ofLp u).fst • ContinuousLinearMap.id 𝕜 E + M (ofLp u).snd‖ ≤
          ‖(ofLp u).fst‖ * 1 + ‖M‖ * ‖(ofLp u).snd‖ := by
        exact (norm_add_le _ _).trans (add_le_add
          ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
            (norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1) (norm_nonneg _)))
          (M.le_opNorm _))
      _ ≤ (1 + ‖M‖) * ‖u‖ := by
        rw [unitization_norm_def]
        nlinarith [norm_nonneg (ofLp u).fst, norm_nonneg (ofLp u).snd,
          mul_nonneg (norm_nonneg M) (norm_nonneg (ofLp u).fst)]

/-- The coordinate formula for the unitized bounded action. -/
@[simp]
theorem unitizationActionL_apply (M : A →L[𝕜] E →L[𝕜] E)
    (u : WithLp 1 (Unitization 𝕜 A)) (x : E) :
    M.unitizationActionL u x = (ofLp u).fst • x + M (ofLp u).snd x := (rfl)

/-- Restricting the unitized action to the original algebra recovers the action. -/
@[simp]
theorem unitizationActionL_toLp_inr (M : A →L[𝕜] E →L[𝕜] E) (a : A) :
    M.unitizationActionL (toLp 1 (a : Unitization 𝕜 A)) = M a := by
  ext x
  simp

/-- The new identity acts as the identity, even if the original action was degenerate. -/
@[simp]
theorem unitizationActionL_one (M : A →L[𝕜] E →L[𝕜] E) :
    M.unitizationActionL 1 = ContinuousLinearMap.id 𝕜 E := by
  ext x
  simp

/-- The bounded extension need not be contractive; its norm is at most `1 + ‖M‖`. -/
theorem norm_unitizationActionL_le (M : A →L[𝕜] E →L[𝕜] E) :
    ‖M.unitizationActionL‖ ≤ 1 + ‖M‖ := by
  unfold unitizationActionL
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- The unital action on `E` of the `ℓ¹` unitization of `A` extending the left action `L`. -/
noncomputable def unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) :
    WithLp 1 (Unitization 𝕜 A) →ₐ[𝕜] (E →L[𝕜] E) :=
  (NonUnitalAlgHom.toAlgHom
    { toFun := L
      map_smul' := map_smul L
      map_zero' := map_zero L
      map_add' := map_add L
      map_mul' := fun a b ↦ ContinuousLinearMap.ext fun z ↦ hL a b z }).comp
    (unitizationAlgEquiv 𝕜).toAlgHom

/-- The unitized action of `(λ, a)` is `λ • id + L a`. -/
@[simp]
lemma unitizationAction_apply (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (u : WithLp 1 (Unitization 𝕜 A)) (z : E) :
    unitizationAction L hL u z = (ofLp u).fst • z + L (ofLp u).snd z := by
  simp [unitizationAction, Algebra.algebraMap_eq_smul_one]

/-- The unitized action agrees with `L` on `A`. -/
@[simp]
lemma unitizationAction_toLp_inr (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (a : A) :
    unitizationAction L hL (toLp 1 (a : Unitization 𝕜 A)) = L a := by
  ext z
  simp

/-- For an associative left action, the bounded extension agrees with its unital
algebra-homomorphism extension. -/
theorem unitizationActionL_eq_unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (u : WithLp 1 (Unitization 𝕜 A)) :
    L.unitizationActionL u = L.unitizationAction hL u := by
  ext x
  simp

/-- The unitized action is bounded: `‖u · z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖`. -/
lemma norm_unitizationAction_apply_le (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (u : WithLp 1 (Unitization 𝕜 A)) (z : E) :
    ‖unitizationAction L hL u z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖ := by
  rw [← unitizationActionL_eq_unitizationAction]
  exact (L.unitizationActionL.le_opNorm₂ u z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right L.norm_unitizationActionL_le (norm_nonneg u))
      (norm_nonneg z))

/-- If a left approximate identity converges at `x`, it converges at every `u · x` with `u` in the
unitization. -/
lemma tendsto_apply_unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A}
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {x : E} (hlx : Tendsto (fun e ↦ L e x) l (𝓝 x))
    (u : WithLp 1 (Unitization 𝕜 A)) :
    Tendsto (fun e ↦ L e (unitizationAction L hL u x)) l (𝓝 (unitizationAction L hL u x)) := by
  simp only [unitizationAction_apply, map_add, map_smul, ← hL]
  exact (hlx.const_smul _).add (((L.flip x).continuous.tendsto _).comp (hl _))

/-- If a left approximate identity converges at `x`, then every `u · x` with `u` in the
unitization lies in the closure of `A · x`. -/
lemma unitizationAction_apply_mem_closure (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {x : E}
    (hlx : Tendsto (fun e ↦ L e x) l (𝓝 x)) (u : WithLp 1 (Unitization 𝕜 A)) :
    unitizationAction L hL u x ∈ closure (Set.range fun b ↦ L b x) := by
  have : Tendsto (fun e ↦ L ((ofLp u).fst • e + (ofLp u).snd) x) l
      (𝓝 (unitizationAction L hL u x)) := by
    simpa using (hlx.const_smul (ofLp u).fst).add_const (L (ofLp u).snd x)
  exact mem_closure_of_tendsto this (.of_forall fun e ↦ ⟨_, rfl⟩)

end ContinuousLinearMap
