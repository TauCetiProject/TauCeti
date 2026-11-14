/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import TauCeti.Analysis.Normed.Ring.WithAbs

/-!
# Completion maps along extensions and isomorphisms of absolute values

If `w` is an absolute value on `L` lying over an absolute value `v` on `K`, the completion map
`AbsoluteValue.Completion.map v w : v.Completion →+* w.Completion` is an isometry, so it preserves
the norm (`AbsoluteValue.Completion.norm_map`).

In addition, a field isomorphism `σ : K ≃+* L` carrying a real absolute value `v` on `K` to a
real absolute value `w` on `L` (`w (σ x) = v x`) is an isometry `WithAbs v → WithAbs w`, so it
extends by continuity to an isometric ring isomorphism of completions
`AbsoluteValue.Completion.congr σ hσ : v.Completion ≃+* w.Completion`. This is the real-valued
counterpart of `Valuation.Completion.congr`, and supplies both the action of field automorphisms on
archimedean completions and the transport of archimedean completions along field isomorphisms across
universes.

## Main definitions

* `AbsoluteValue.Completion.congr`: the ring isomorphism `v.Completion ≃+* w.Completion` extending
  `σ : K ≃+* L` when `∀ x, w (σ x) = v x`.
* `AbsoluteValue.Completion.isometryEquivCongr`: the same map bundled as an isometric equivalence
  `v.Completion ≃ᵢ w.Completion`.

## Main results

* `AbsoluteValue.Completion.norm_map`: `AbsoluteValue.Completion.map` preserves the norm.
* `AbsoluteValue.Completion.congr_coe`, `AbsoluteValue.Completion.congr_algebraMap`:
  `AbsoluteValue.Completion.congr` extends `σ` on `WithAbs v` and on `K`.
* `AbsoluteValue.Completion.isometry_congr`, `AbsoluteValue.Completion.norm_congr`,
  `AbsoluteValue.Completion.continuous_congr`,
  `AbsoluteValue.Completion.continuous_congr_symm`: `congr` is an isometry, preserves the norm, and
  is continuous in both directions.
* `AbsoluteValue.Completion.eq_congr_of_continuous`: `congr` is the unique continuous map
  `v.Completion → w.Completion` extending `σ`.
* `AbsoluteValue.Completion.congr_refl`, `AbsoluteValue.Completion.congr_trans`,
  `AbsoluteValue.Completion.congr_trans_apply`, `AbsoluteValue.Completion.congr_symm`,
  `AbsoluteValue.Completion.isometryEquivCongr_refl`,
  `AbsoluteValue.Completion.isometryEquivCongr_trans`,
  `AbsoluteValue.Completion.isometryEquivCongr_symm`: functoriality.
-/

public section

namespace AbsoluteValue.Completion

section LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ} [w.LiesOver v]

/-- The completion map along an extension of absolute values preserves the norm. -/
@[simp]
theorem norm_map (x : v.Completion) : ‖map v w x‖ = ‖x‖ :=
  (isometry_map v w).norm_map_of_map_zero (map_zero _) x

end LiesOver

section Congr

variable {K L M : Type*} [Field K] [Field L] [Field M]
  {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ} {u : AbsoluteValue M ℝ}

/-- The ring isomorphism of completions `v.Completion ≃+* w.Completion` extending a field
isomorphism `σ : K ≃+* L` that carries `v` to `w`. -/
noncomputable def congr (σ : K ≃+* L) (hσ : ∀ x, w (σ x) = v x) :
    v.Completion ≃+* w.Completion :=
  (equiv v).trans <|
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr v w σ)
      (WithAbs.isometry_congr σ hσ).continuous
      (WithAbs.congr_symm v w σ ▸ (WithAbs.isometry_congr σ.symm
        fun y ↦ by rw [← hσ, σ.apply_symm_apply]).continuous)).trans
      (equiv w).symm

variable {σ : K ≃+* L} (hσ : ∀ x, w (σ x) = v x)

/-- On the underlying uniform-space completions, `AbsoluteValue.Completion.congr` is
`UniformSpace.Completion.map (WithAbs.congr v w σ)`. -/
@[simp]
theorem toCompletion_congr (x : v.Completion) :
    (congr σ hσ x).toCompletion =
      UniformSpace.Completion.map (WithAbs.congr v w σ) x.toCompletion := by
  rw [congr, RingEquiv.trans_apply, RingEquiv.trans_apply, equiv_apply, equiv_symm_apply,
    toCompletion_ofCompletion, UniformSpace.Completion.mapRingEquiv_apply]

/-- `AbsoluteValue.Completion.congr` extends `WithAbs.congr v w σ` on `WithAbs v`. -/
@[simp]
theorem congr_coe (x : WithAbs v) :
    congr σ hσ (x : v.Completion) = (WithAbs.congr v w σ x : w.Completion) := by
  apply toCompletion_injective w
  rw [toCompletion_congr, toCompletion_coe, toCompletion_coe,
    UniformSpace.Completion.map_coe (WithAbs.isometry_congr σ hσ).uniformContinuous]

/-- `AbsoluteValue.Completion.congr` intertwines the canonical algebra maps from `K` and `L`. -/
@[simp]
theorem congr_algebraMap (x : K) :
    congr σ hσ (algebraMap K v.Completion x) = algebraMap L w.Completion (σ x) := by
  rw [algebraMap_def, algebraMap_def, congr_coe, WithAbs.algebraMap_right_apply,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply,
    WithAbs.congr_apply, WithAbs.ofAbs_toAbs]

/-- `AbsoluteValue.Completion.congr` is an isometry. -/
theorem isometry_congr : Isometry (congr σ hσ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [← norm_toCompletion, toCompletion_congr, ← norm_toCompletion]
    exact (UniformSpace.Completion.isometry_mapRingHom (f := (WithAbs.congr v w σ).toRingHom)
      (WithAbs.isometry_congr σ hσ)).norm_map_of_map_zero (map_zero _) x.toCompletion

/-- `AbsoluteValue.Completion.congr` bundled as an isometric equivalence
`v.Completion ≃ᵢ w.Completion`. -/
noncomputable def isometryEquivCongr (σ : K ≃+* L) (hσ : ∀ x, w (σ x) = v x) :
    v.Completion ≃ᵢ w.Completion where
  toEquiv := (congr σ hσ).toEquiv
  isometry_toFun := isometry_congr hσ

/-- The underlying map of `isometryEquivCongr σ hσ` is `congr σ hσ`. -/
@[simp]
theorem coe_isometryEquivCongr : ⇑(isometryEquivCongr σ hσ) = congr σ hσ :=
  (rfl)

/-- The bijection underlying `isometryEquivCongr σ hσ` is `(congr σ hσ).toEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivCongr :
    (isometryEquivCongr σ hσ).toEquiv = (congr σ hσ).toEquiv :=
  (rfl)

/-- `AbsoluteValue.Completion.congr` preserves the norm. -/
@[simp]
theorem norm_congr (x : v.Completion) : ‖congr σ hσ x‖ = ‖x‖ :=
  (isometry_congr hσ).norm_map_of_map_zero (map_zero _) x

/-- `AbsoluteValue.Completion.congr` is continuous. -/
@[continuity, fun_prop]
theorem continuous_congr : Continuous (congr σ hσ) :=
  (isometry_congr hσ).continuous

/-- The inverse of `AbsoluteValue.Completion.congr` is continuous. -/
@[continuity, fun_prop]
theorem continuous_congr_symm : Continuous (congr σ hσ).symm :=
  (isometryEquivCongr σ hσ).symm.continuous

/-- `AbsoluteValue.Completion.congr` is the only continuous map `v.Completion → w.Completion`
extending `σ`. -/
theorem eq_congr_of_continuous {f : v.Completion → w.Completion} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K v.Completion x) = algebraMap L w.Completion (σ x)) :
    f = congr σ hσ :=
  ext hf (continuous_congr hσ) fun x ↦ by
    have hx : (x : v.Completion) = algebraMap K v.Completion x.ofAbs := by
      rw [algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
        WithAbs.toAbs_ofAbs]
    rw [hx, hfK, congr_algebraMap]

/-- `AbsoluteValue.Completion.congr` of the identity is the identity. -/
@[simp]
theorem congr_refl (h : ∀ x, v (RingEquiv.refl K x) = v x := fun _ ↦ rfl) :
    congr (RingEquiv.refl K) h = RingEquiv.refl v.Completion :=
  DFunLike.coe_injective (eq_congr_of_continuous h continuous_id fun _ ↦ rfl).symm

/-- `AbsoluteValue.Completion.congr` is compatible with composition of field isomorphisms. -/
@[simp]
theorem congr_trans {τ : L ≃+* M} (hτ : ∀ y, u (τ y) = w y) :
    (congr σ hσ).trans (congr τ hτ) =
      congr (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) :=
  DFunLike.coe_injective <| eq_congr_of_continuous _
    ((continuous_congr hτ).comp (continuous_congr hσ)) fun x ↦ by
      rw [RingEquiv.coe_trans, Function.comp_apply, congr_algebraMap, congr_algebraMap,
        RingEquiv.trans_apply]

/-- Pointwise composition of `AbsoluteValue.Completion.congr`. -/
@[simp]
theorem congr_trans_apply {τ : L ≃+* M} (hτ : ∀ y, u (τ y) = w y) (x : v.Completion) :
    congr τ hτ (congr σ hσ x) =
      congr (σ.trans τ) (fun a ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) x :=
  DFunLike.congr_fun (congr_trans hσ hτ) x

/-- The inverse of `AbsoluteValue.Completion.congr` is `AbsoluteValue.Completion.congr` of the
inverse isomorphism. -/
@[simp]
theorem congr_symm :
    (congr σ hσ).symm = congr σ.symm (fun y ↦ by rw [← hσ, σ.apply_symm_apply]) :=
  DFunLike.coe_injective <| eq_congr_of_continuous _
    (continuous_congr_symm hσ) fun y ↦ by
      rw [RingEquiv.symm_apply_eq, congr_algebraMap, σ.apply_symm_apply]

/-- `AbsoluteValue.Completion.isometryEquivCongr` of the identity is the identity. -/
@[simp]
theorem isometryEquivCongr_refl (h : ∀ x, v (RingEquiv.refl K x) = v x := fun _ ↦ rfl) :
    isometryEquivCongr (RingEquiv.refl K) h = IsometryEquiv.refl v.Completion :=
  IsometryEquiv.ext fun x ↦ by
    rw [coe_isometryEquivCongr, congr_refl]
    rfl

/-- `AbsoluteValue.Completion.isometryEquivCongr` is compatible with composition of field
isomorphisms. -/
@[simp]
theorem isometryEquivCongr_trans {τ : L ≃+* M} (hτ : ∀ y, u (τ y) = w y) :
    (isometryEquivCongr σ hσ).trans (isometryEquivCongr τ hτ) =
      isometryEquivCongr (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) :=
  IsometryEquiv.ext fun x ↦ by
    rw [IsometryEquiv.trans_apply, coe_isometryEquivCongr, coe_isometryEquivCongr,
      coe_isometryEquivCongr, congr_trans_apply]

/-- The inverse of `isometryEquivCongr σ hσ` is `isometryEquivCongr` of `σ.symm`. -/
@[simp]
theorem isometryEquivCongr_symm :
    (isometryEquivCongr σ hσ).symm =
      isometryEquivCongr σ.symm (fun y ↦ by rw [← hσ, σ.apply_symm_apply]) :=
  IsometryEquiv.ext fun x ↦ by
    rw [IsometryEquiv.symm_apply_eq, coe_isometryEquivCongr, coe_isometryEquivCongr,
      ← RingEquiv.symm_apply_eq, congr_symm]

end Congr

end AbsoluteValue.Completion
