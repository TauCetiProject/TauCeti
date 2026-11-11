/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Unitized bounded actions and Banach left modules

A bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E` of a possibly nonunital normed algebra
extends to the ℓ¹ unitization `A⁺ = WithLp 1 (Unitization 𝕜 A)` without an associativity
assumption via `ContinuousLinearMap.unitizationActionL`, sending `(λ, a)` to `λ • id + M a`.
This file records its apply formula, identity action, norm bound `1 + ‖M‖`, and uniqueness,
and characterizes intertwining maps and left associativity by iff statements. For associative
left actions, `ContinuousLinearMap.unitizationAction` is the algebra-homomorphism form of the
same extension, with an explicit comparison lemma. The approximate-identity lemmas show that
the points where a left approximate identity converges are invariant under `A⁺`, and that
each unitized orbit lies in the closure of the original orbit at such a point. Composing a
bounded derivation with the nonunital coordinate projection extends its Leibniz rule to
unital bimodule actions.

## Main declarations

* `ContinuousLinearMap.unitizationActionL`: the bounded unital extension of a bilinear action.
* `ContinuousLinearMap.eq_unitizationActionL`: uniqueness of the unital extension.
* `ContinuousLinearMap.unitizationActionL_mul_iff`: preservation and reflection of associativity.
* `ContinuousLinearMap.intertwines_unitizationActionL_iff`: characterization of intertwining maps.
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

/-- A unital bounded action is uniquely determined by its restriction to `A`. -/
theorem eq_unitizationActionL (Φ : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E)
    (M : A →L[𝕜] E →L[𝕜] E) (h1 : Φ 1 = ContinuousLinearMap.id 𝕜 E)
    (hM : ∀ a : A, Φ (toLp 1 (a : Unitization 𝕜 A)) = M a) :
    Φ = M.unitizationActionL := by
  ext u x
  rw [Φ.unitization_apply_eq_fst_smul_add u, h1, hM]
  simp

/-- A bounded linear map intertwines the unitized actions exactly when it intertwines
the original actions. Apply this separately to the left and right actions of a bimodule. -/
theorem intertwines_unitizationActionL_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (M : A →L[𝕜] E →L[𝕜] E) (N : A →L[𝕜] F →L[𝕜] F) :
    (∀ u x, T (M.unitizationActionL u x) = N.unitizationActionL u (T x)) ↔
    ∀ a x, T (M a x) = N a (T x) := by
  constructor
  · intro h a x
    simpa using h (toLp 1 (a : Unitization 𝕜 A)) x
  · intro h u x
    simp [h]

/-- The unital action on `E` of the `ℓ¹` unitization of `A` extending the left action `L`. -/
noncomputable def unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) :
    WithLp 1 (Unitization 𝕜 A) →ₐ[𝕜] (E →L[𝕜] E) :=
  AlgHom.ofLinearMap L.unitizationActionL.toLinearMap L.unitizationActionL_one fun u v ↦ by
    ext x
    simp [snd_mul, map_add, map_smul, smul_add, smul_smul, hL,
      mul_comm, add_assoc, add_comm, add_left_comm]

/-- The unitized action of `(λ, a)` is `λ • id + L a`. -/
@[simp]
lemma unitizationAction_apply (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (u : WithLp 1 (Unitization 𝕜 A)) (z : E) :
    unitizationAction L hL u z = (ofLp u).fst • z + L (ofLp u).snd z := (rfl)

/-- The unitized action agrees with `L` on `A`. -/
@[simp]
lemma unitizationAction_toLp_inr (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (a : A) :
    unitizationAction L hL (toLp 1 (a : Unitization 𝕜 A)) = L a :=
  L.unitizationActionL_toLp_inr a

/-- For an associative left action, the bounded extension agrees with its unital
algebra-homomorphism extension. -/
theorem unitizationActionL_eq_unitizationAction (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (u : WithLp 1 (Unitization 𝕜 A)) :
    L.unitizationActionL u = L.unitizationAction hL u := (rfl)

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

/-- Composing a bounded derivation with the nonunital coordinate projection extends its
Leibniz rule to unital actions of the ℓ¹ unitization. -/
theorem comp_unitizationSndL_mul (D : A →L[𝕜] E)
    (L R : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E)
    (h1L : ∀ x, L 1 x = x) (h1R : ∀ x, R 1 x = x)
    (hD : ∀ a b, D (a * b) =
      L (WithLp.toLp 1 (a : Unitization 𝕜 A)) (D b) +
      R (WithLp.toLp 1 (b : Unitization 𝕜 A)) (D a))
    (u v : WithLp 1 (Unitization 𝕜 A)) :
    (D ∘L WithLp.unitizationSndL 𝕜 A) (u * v) =
      L u ((D ∘L WithLp.unitizationSndL 𝕜 A) v) +
      R v ((D ∘L WithLp.unitizationSndL 𝕜 A) u) := by
  rw [L.unitization_apply_eq_fst_smul_add u, R.unitization_apply_eq_fst_smul_add v]
  simp only [comp_apply, WithLp.unitizationSndL_apply, WithLp.unitization_mul,
    Unitization.snd_mul, map_add, map_smul, hD, add_apply, smul_apply, h1L, h1R]
  abel

end ContinuousLinearMap
