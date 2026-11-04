/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The unitized action on a Banach left module

Let `A` be a possibly nonunital normed algebra acting on a normed space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`. The action extends
to a unital algebra homomorphism from the `ℓ¹` unitization `A⁺ = WithLp 1 (Unitization 𝕜 A)` to
`E →L[𝕜] E`, sending `(λ, a)` to `λ • id + L a`. This file constructs it and records its apply
formula, its norm bound, and the invariance under `A⁺` of the points where a left approximate
identity converges. It also proves that composing a bounded derivation with the nonunital
coordinate projection extends its Leibniz rule to unital bimodule actions.

## Main declarations

* `ContinuousLinearMap.unitizationAction`: the unital action of `A⁺` extending `L`.
* `ContinuousLinearMap.unitizationAction_apply`: `(λ, a) · z = λ • z + L a z`.
* `ContinuousLinearMap.norm_unitizationAction_apply_le`: `‖u · z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖`.
* `ContinuousLinearMap.tendsto_apply_unitizationAction`,
  `ContinuousLinearMap.unitizationAction_apply_mem_closure`: if a left approximate identity
  converges at `x`, it converges at every `u · x`, and `u · x` lies in the closure of `A · x`.
-/

public section

open Filter Topology Unitization WithLp

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

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

/-- The unitized action is bounded: `‖u · z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖`. -/
lemma norm_unitizationAction_apply_le (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) (u : WithLp 1 (Unitization 𝕜 A)) (z : E) :
    ‖unitizationAction L hL u z‖ ≤ (1 + ‖L‖) * ‖u‖ * ‖z‖ := by
  rw [unitizationAction_apply, unitization_norm_def]
  calc ‖(ofLp u).fst • z + L (ofLp u).snd z‖
      ≤ ‖(ofLp u).fst‖ * ‖z‖ + ‖L‖ * ‖(ofLp u).snd‖ * ‖z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_smul_le _ _) (L.le_opNorm₂ _ _))
    _ ≤ (1 + ‖L‖) * (‖(ofLp u).fst‖ + ‖(ofLp u).snd‖) * ‖z‖ := by
        nlinarith [norm_nonneg (ofLp u).fst, norm_nonneg (ofLp u).snd, norm_nonneg z,
          norm_nonneg L,
          mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (ofLp u).fst)) (norm_nonneg z)]

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
