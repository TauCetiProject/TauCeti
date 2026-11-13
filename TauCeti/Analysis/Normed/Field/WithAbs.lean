/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import TauCeti.Algebra.Order.AbsoluteValue.RingEquiv
public import TauCeti.Analysis.Normed.Ring.WithAbs
import TauCeti.Topology.Algebra.UniformRing

/-!
# Completion maps and isomorphisms for fields with an absolute value

If `w` is an absolute value on `L` lying over an absolute value `v` on `K`, the completion map
`AbsoluteValue.Completion.map v w : v.Completion →+* w.Completion` is an isometry, so it preserves
the norm (`AbsoluteValue.Completion.norm_map`).

More generally, let `σ : K ≃+* L` be a ring isomorphism of fields carrying `v : AbsoluteValue K ℝ`
to `w : AbsoluteValue L ℝ`, in the sense that `w (σ x) = v x`. Then `WithAbs.congr v w σ` and its
inverse are isometries, so `σ` extends by continuity to an isometric ring isomorphism of the
completions `AbsoluteValue.Completion.congr σ hσ : v.Completion ≃+* w.Completion`. This is the
absolute-value counterpart of `Valuation.Completion.congr` in
`TauCeti/Topology/Algebra/Valued/WithVal.lean`; the completion-isomorphism construction is
extracted and generalized from `NumberField.InfinitePlace.completionRingEquiv` in
`TauCeti/NumberTheory/NumberField/InfinitePlace/Completion/DecompositionGroup.lean`.

## Main definitions

* `AbsoluteValue.Completion.congr`: the ring isomorphism `v.Completion ≃+* w.Completion` extending
  an absolute-value-preserving isomorphism `σ : K ≃+* L`.

## Main results

* `AbsoluteValue.Completion.norm_map`: `AbsoluteValue.Completion.map` preserves the norm.
* `AbsoluteValue.Completion.congr_coe`, `AbsoluteValue.Completion.congr_algebraMap`: `congr`
  extends `σ`.
* `AbsoluteValue.Completion.continuous_congr`, `AbsoluteValue.Completion.norm_congr`,
  `AbsoluteValue.Completion.isometry_congr`: `congr` is continuous, norm-preserving, and an
  isometry.
* `AbsoluteValue.Completion.eq_congr_of_continuous`: `congr` is the unique continuous ring
  homomorphism extending `σ`.
* `AbsoluteValue.Completion.congr_refl`, `AbsoluteValue.Completion.congr_trans`,
  `AbsoluteValue.Completion.congr_symm`: functoriality of `congr`.
* `AbsoluteValue.Completion.congr_map`: compatibility of `congr` with
  `AbsoluteValue.Completion.map` along extensions of absolute values.
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

/-- **The isomorphism of completions extending `σ`**: a ring isomorphism `σ : K ≃+* L` carrying the
absolute value `v` to `w` extends by continuity to `v.Completion ≃+* w.Completion`. -/
noncomputable def congr (σ : K ≃+* L) (hσ : ∀ x, w (σ x) = v x) :
    v.Completion ≃+* w.Completion :=
  (equiv v).trans <|
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr v w σ)
      (WithAbs.isometry_congr σ hσ).continuous
      ((WithAbs.congr_symm v w σ).symm ▸
        (WithAbs.isometry_congr σ.symm
          (AbsoluteValue.apply_symm_eq_of_apply_eq hσ)).continuous)).trans
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

/-- `AbsoluteValue.Completion.congr` intertwines `ofCompletion` with
`UniformSpace.Completion.map (WithAbs.congr v w σ)`. -/
@[simp]
theorem congr_ofCompletion (x : UniformSpace.Completion (WithAbs v)) :
    congr σ hσ (ofCompletion x) =
      ofCompletion (UniformSpace.Completion.map (WithAbs.congr v w σ) x) := by
  apply toCompletion_injective w
  rw [toCompletion_congr, toCompletion_ofCompletion, toCompletion_ofCompletion]

/-- `AbsoluteValue.Completion.congr` extends `WithAbs.congr v w σ` along the coercion from
`WithAbs`. -/
@[simp]
theorem congr_coe (x : WithAbs v) :
    congr σ hσ (x : v.Completion) = (WithAbs.congr v w σ x : w.Completion) := by
  apply toCompletion_injective w
  rw [toCompletion_congr, toCompletion_coe, toCompletion_coe,
    UniformSpace.Completion.map_coe (WithAbs.isometry_congr σ hσ).uniformContinuous]

/-- `AbsoluteValue.Completion.congr` extends `σ` along `algebraMap`. -/
@[simp]
theorem congr_algebraMap (x : K) :
    congr σ hσ (algebraMap K v.Completion x) = algebraMap L w.Completion (σ x) := by
  rw [algebraMap_def, algebraMap_def, congr_coe, WithAbs.algebraMap_right_apply,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
    Algebra.algebraMap_self_apply, WithAbs.congr_apply, WithAbs.ofAbs_toAbs]

/-- `AbsoluteValue.Completion.congr` is continuous. -/
@[fun_prop, continuity]
theorem continuous_congr : Continuous (congr σ hσ) := by
  have h : ⇑(congr σ hσ) =
      ofCompletion ∘ UniformSpace.Completion.map (WithAbs.congr v w σ) ∘ toCompletion := by
    ext x
    rw [Function.comp_apply, Function.comp_apply, ← toCompletion_congr hσ,
      ofCompletion_toCompletion]
  rw [h]
  exact (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion v)

/-- `AbsoluteValue.Completion.congr` preserves the norm on the completion. -/
@[simp]
theorem norm_congr (x : v.Completion) : ‖congr σ hσ x‖ = ‖x‖ := by
  induction x using induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_congr hσ)) continuous_norm
  | ih a => rw [congr_coe, norm_coe, norm_coe, WithAbs.congr_apply, WithAbs.ofAbs_toAbs, hσ]

/-- `AbsoluteValue.Completion.congr` is an isometry. -/
theorem isometry_congr : Isometry (congr σ hσ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_congr hσ)

/-- **`AbsoluteValue.Completion.congr` is the only continuous ring homomorphism extending `σ`.** -/
theorem eq_congr_of_continuous {f : v.Completion →+* w.Completion} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K v.Completion x) = algebraMap L w.Completion (σ x)) :
    f = (congr σ hσ).toRingHom :=
  DFunLike.coe_injective <| ext hf (continuous_congr hσ) fun x ↦ by
    have hx : (x : v.Completion) = algebraMap K v.Completion x.ofAbs := by
      rw [algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
        WithAbs.toAbs_ofAbs]
    rw [hx, hfK, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, congr_algebraMap]

/-- `AbsoluteValue.Completion.congr` depends only on the ring isomorphism, not on the proof that it
intertwines the absolute values. -/
private theorem congr_congr {σ' : K ≃+* L} (hσσ' : σ = σ') (hσ' : ∀ x, w (σ' x) = v x) :
    congr σ hσ = congr σ' hσ' := by
  subst hσσ'
  rfl

/-- `AbsoluteValue.Completion.congr` of the identity is the identity. -/
@[simp]
theorem congr_refl : congr (RingEquiv.refl K) (fun _ ↦ rfl) = RingEquiv.refl v.Completion :=
  RingEquiv.toRingHom_injective
    (eq_congr_of_continuous (fun _ ↦ rfl) (f := RingHom.id _) continuous_id fun _ ↦ rfl).symm

/-- `AbsoluteValue.Completion.congr` is compatible with composition. -/
@[simp]
theorem congr_trans {τ : L ≃+* M} (hτ : ∀ y, u (τ y) = w y) :
    (congr σ hσ).trans (congr τ hτ) =
      congr (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) := by
  refine RingEquiv.toRingHom_injective <| eq_congr_of_continuous _
    ((continuous_congr hτ).comp (continuous_congr hσ)) fun x ↦ ?_
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    congr_algebraMap, congr_algebraMap, RingEquiv.trans_apply]

/-- The inverse of `AbsoluteValue.Completion.congr` is `AbsoluteValue.Completion.congr` of the
inverse. -/
@[simp]
theorem congr_symm :
    (congr σ hσ).symm = congr σ.symm (AbsoluteValue.apply_symm_eq_of_apply_eq hσ) := by
  refine RingEquiv.ext fun y ↦ ?_
  rw [RingEquiv.symm_apply_eq, ← RingEquiv.trans_apply, congr_trans,
    congr_congr _ (RingEquiv.symm_trans_self σ) (fun _ ↦ rfl), congr_refl, RingEquiv.refl_apply]

/-- The inverse of `AbsoluteValue.Completion.congr` is continuous. -/
@[fun_prop, continuity]
theorem continuous_congr_symm : Continuous (congr σ hσ).symm :=
  congr_symm hσ ▸ continuous_congr (AbsoluteValue.apply_symm_eq_of_apply_eq hσ)

/-- `AbsoluteValue.Completion.congr` commutes with `AbsoluteValue.Completion.map` along commuting
isomorphisms of field extensions. -/
theorem congr_map {K₀ L₀ : Type*} [Field K₀] [Field L₀] [Algebra K₀ K] [Algebra L₀ L]
    {v₀ : AbsoluteValue K₀ ℝ} {w₀ : AbsoluteValue L₀ ℝ} [v.LiesOver v₀] [w.LiesOver w₀]
    {σ₀ : K₀ ≃+* L₀} (hσ₀ : ∀ x, w₀ (σ₀ x) = v₀ x)
    (hcomm : ∀ x : K₀, σ (algebraMap K₀ K x) = algebraMap L₀ L (σ₀ x))
    (x : v₀.Completion) :
    congr σ hσ (map v₀ v x) = map w₀ w (congr σ₀ hσ₀ x) := by
  refine congrFun (ext ((continuous_congr hσ).comp (continuous_map v₀ v))
    ((continuous_map w₀ w).comp (continuous_congr hσ₀)) fun a ↦ ?_) x
  rw [Function.comp_apply, Function.comp_apply, map_coe, congr_coe, congr_coe, map_coe]
  congr 1
  apply WithAbs.ofAbs_injective
  simp [hcomm]

end Congr

end AbsoluteValue.Completion
