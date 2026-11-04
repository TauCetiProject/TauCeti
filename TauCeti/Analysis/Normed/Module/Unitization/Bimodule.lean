/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Unitization.Basic

/-!
# Unitizing bounded bimodule actions

A bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E` extends uniquely to a bounded
bilinear action of the external ℓ¹ unitization, with `(λ,a)` acting as `λ • id + M a`.
This construction does not require an associativity law. It therefore applies to both
left and right actions, with the algebra argument first in both cases.

The left associativity, right associativity, and commuting-action laws hold for the
extensions exactly when they hold for the original actions. Thus a bounded bimodule
over a possibly nonunital algebra is equivalently a compatible unital bounded bimodule
over its unitization. No contractivity or completeness assumption is needed. The
uniqueness and intertwining results allow module maps to pass between these descriptions.

The existing `ContinuousLinearMap.unitizationAction` is the algebra-homomorphism form
of the same extension for associative left actions.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3 and 2.8.
-/

public section

open Unitization WithLp

namespace ContinuousLinearMap

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

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

/-- A unital bounded action is uniquely determined by its restriction to `A`. -/
theorem eq_unitizationActionL (Φ : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E)
    (M : A →L[𝕜] E →L[𝕜] E) (h1 : Φ 1 = ContinuousLinearMap.id 𝕜 E)
    (hM : ∀ a : A, Φ (toLp 1 (a : Unitization 𝕜 A)) = M a) :
    Φ = M.unitizationActionL := by
  ext u x
  have hu : u = (ofLp u).fst • 1 + toLp 1 ((ofLp u).snd : Unitization 𝕜 A) := by
    apply (unitizationAlgEquiv 𝕜).injective
    ext <;> simp
  rw [hu, map_add, map_smul, h1, hM]
  simp

/-- For an associative left action, the bounded extension agrees with its unital
algebra-homomorphism extension. -/
theorem unitizationActionL_eq_unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (u : WithLp 1 (Unitization 𝕜 A)) :
    L.unitizationActionL u = L.unitizationAction hL u := by
  ext x
  simp

/-- Left associativity is preserved and reflected by unitization. -/
theorem unitizationActionL_mul_iff (L : A →L[𝕜] E →L[𝕜] E) :
    (∀ u v x, L.unitizationActionL (u * v) x =
      L.unitizationActionL u (L.unitizationActionL v x)) ↔
    ∀ a b x, L (a * b) x = L a (L b x) := by
  constructor
  · intro h a b x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) (toLp 1 (b : Unitization 𝕜 A)) x
  · intro h u v x
    rw [unitizationActionL_eq_unitizationAction L h,
      map_mul, mul_apply_eq_comp,
      unitizationActionL_eq_unitizationAction L h,
      unitizationActionL_eq_unitizationAction L h]

/-- Right associativity is preserved and reflected by unitization. Here `R a x`
means `x · a`, so the order of the nested actions is reversed. -/
theorem unitizationActionL_mul_right_iff (R : A →L[𝕜] E →L[𝕜] E) :
    (∀ u v x, R.unitizationActionL (u * v) x =
      R.unitizationActionL v (R.unitizationActionL u x)) ↔
    ∀ a b x, R (a * b) x = R b (R a x) := by
  constructor
  · intro h a b x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) (toLp 1 (b : Unitization 𝕜 A)) x
  · intro h u v x
    simp [unitizationActionL_apply, snd_mul, map_add, map_smul, smul_add,
      smul_smul, h, add_assoc, add_comm, add_left_comm]

/-- The extended left and right actions commute exactly when the original ones do. -/
theorem unitizationActionL_comm_iff (L R : A →L[𝕜] E →L[𝕜] E) :
    (∀ u v x, L.unitizationActionL u (R.unitizationActionL v x) =
      R.unitizationActionL v (L.unitizationActionL u x)) ↔
    ∀ a b x, L a (R b x) = R b (L a x) := by
  constructor
  · intro h a b x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) (toLp 1 (b : Unitization 𝕜 A)) x
  · intro h u v x
    simp [map_add, map_smul, smul_add, smul_smul, h,
      mul_comm, add_assoc, add_comm, add_left_comm]

/-- A bounded linear map intertwines the unitized actions exactly when it intertwines
the original actions. Apply this separately to the left and right actions of a bimodule. -/
theorem intertwines_unitizationActionL_iff (T : E →L[𝕜] F)
    (M : A →L[𝕜] E →L[𝕜] E) (N : A →L[𝕜] F →L[𝕜] F) :
    (∀ u x, T (M.unitizationActionL u x) = N.unitizationActionL u (T x)) ↔
    ∀ a x, T (M a x) = N a (T x) := by
  constructor
  · intro h a x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) x
  · intro h u x
    simp [h]

end ContinuousLinearMap
