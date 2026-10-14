/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.WithVal
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Valuation-preserving isomorphisms extend to the completions

Let `σ : K ≃+* K'` be an isomorphism of fields carrying a valuation `v` on `K` to a valuation `w`
on `K'`, in the sense that `w (σ x) = v x`. Then `σ` is uniformly continuous for the uniform
structures that `v` and `w` define, so it extends to an isomorphism of the completions
`v.Completion ≃+* w.Completion`. This is how an automorphism of a field fixing a place acts on the
completion at that place.

## Main definitions

* `Valuation.Completion.congr`: the isomorphism of completions `v.Completion ≃+* w.Completion`
  extending `σ`.

## Main results

* `WithVal.uniformContinuous_congr`: if every value of `v` is attained, the map
  `WithVal.congr v w σ : WithVal v ≃+* WithVal w` is uniformly continuous.
* `Valuation.Completion.continuous_valued`: if every value of `v` is attained, the completed
  valuation on `v.Completion` is continuous.
* `Valuation.Completion.congr_coe`: `Valuation.Completion.congr` extends `σ`.
* `Valuation.Completion.eq_congr_of_continuous`: it is the only continuous ring homomorphism
  extending `σ`.
* `Valuation.Completion.valued_congr`: it preserves the completed valuations.
* `Valuation.Completion.congr_refl`, `Valuation.Completion.congr_trans` and
  `Valuation.Completion.congr_symm`: functoriality.
-/

public section

open Filter WithZeroTopology

namespace WithVal

variable {K K' : Type*} [Field K] [Field K'] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {w : Valuation K' Γ₀}

/-- **A valuation-preserving isomorphism is uniformly continuous.** If `σ : K ≃+* K'` carries the
valuation `v` to `w`, and every value of `v` is attained, then `σ` is uniformly continuous as a
map `WithVal v → WithVal w`. -/
theorem uniformContinuous_congr (hv : Function.Surjective v) (σ : K ≃+* K')
    (hσ : ∀ x, w (σ x) = v x) : UniformContinuous (WithVal.congr v w σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  -- the preimage of a valuation ball is the valuation ball of the same radius
  have hcont : Continuous (Valued.v : Valuation (WithVal v) Γ₀) :=
    Valued.continuous_valuation_of_surjective fun δ ↦
      let ⟨a, ha⟩ := hv δ
      ⟨toVal v a, ha⟩
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_injective).mpr γ.ne_zero
  filter_upwards [hcont.continuousAt.preimage_mem_nhds <| by
    simpa using Iio_mem_nhds_zero hγ] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa [hσ, WithVal.apply_ofVal] using hx

end WithVal

namespace Valuation.Completion

variable {K K' K'' : Type*} [Field K] [Field K'] [Field K''] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {w : Valuation K' Γ₀}
  {u : Valuation K'' Γ₀}

/-- **The completed valuation is continuous.** If every value of `v` is attained, the extension of
`v` to the completion `v.Completion` is continuous. -/
theorem continuous_valued (hv : Function.Surjective v) :
    Continuous (Valued.v : Valuation v.Completion Γ₀) :=
  Valued.continuous_valuation_of_surjective fun γ ↦
    let ⟨x, hx⟩ := hv γ
    ⟨(x : v.Completion), (Valued.valuedCompletion_apply (WithVal.toVal v x)).trans hx⟩

/-- If `σ` carries `v` to `w` and every value of `v` is attained, every value of `w` is attained. -/
private theorem surjective_of_apply_eq (hv : Function.Surjective v) {σ : K ≃+* K'}
    (hσ : ∀ x, w (σ x) = v x) : Function.Surjective w := fun γ ↦
  let ⟨x, hx⟩ := hv γ
  ⟨σ x, (hσ x).trans hx⟩

/-- The inverse of an isomorphism carrying `v` to `w` carries `w` to `v`. -/
private theorem symm_apply_eq {σ : K ≃+* K'} (hσ : ∀ x, w (σ x) = v x) (y : K') :
    v (σ.symm y) = w y := by
  rw [← hσ, RingEquiv.apply_symm_apply]

/-- **The isomorphism of completions extending `σ`**: an isomorphism `σ : K ≃+* K'` carrying the
valuation `v` to `w`, with every value of `v` attained, extends by continuity to
`v.Completion ≃+* w.Completion`. -/
noncomputable def congr (hv : Function.Surjective v) (σ : K ≃+* K') (hσ : ∀ x, w (σ x) = v x) :
    v.Completion ≃+* w.Completion :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr v w σ)
    (WithVal.uniformContinuous_congr hv σ hσ).continuous
    (WithVal.uniformContinuous_congr (surjective_of_apply_eq hv hσ) σ.symm
      (symm_apply_eq hσ)).continuous

variable (hv : Function.Surjective v) {σ : K ≃+* K'} (hσ : ∀ x, w (σ x) = v x)

/-- `Valuation.Completion.congr` is the completion of `WithVal.congr v w σ`. -/
theorem congr_apply (x : v.Completion) :
    congr hv σ hσ x = UniformSpace.Completion.map (WithVal.congr v w σ) x :=
  UniformSpace.Completion.mapRingEquiv_apply _ _ _ x

/-- `Valuation.Completion.congr` extends `σ`. -/
@[simp]
theorem congr_coe (x : K) : congr hv σ hσ (x : v.Completion) = (σ x : w.Completion) := by
  rw [congr_apply, UniformSpace.Completion.map_coe (WithVal.uniformContinuous_congr hv σ hσ)]
  rfl

/-- `Valuation.Completion.congr` is continuous. -/
theorem continuous_congr : Continuous (congr hv σ hσ) :=
  UniformSpace.Completion.continuous_mapRingEquiv _ _ _

/-- **`Valuation.Completion.congr` is the only continuous extension of `σ`.** -/
theorem eq_congr_of_continuous {f : v.Completion →+* w.Completion} (hf : Continuous f)
    (hfK : ∀ x : K, f (x : v.Completion) = (σ x : w.Completion)) :
    f = (congr hv σ hσ).toRingHom :=
  DFunLike.coe_injective <| UniformSpace.Completion.ext hf (continuous_congr hv hσ) fun x ↦
    (hfK (WithVal.ofVal x)).trans (congr_coe hv hσ (WithVal.ofVal x)).symm

/-- `Valuation.Completion.congr` preserves the completed valuations. -/
@[simp]
theorem valued_congr (x : v.Completion) : Valued.v (congr hv σ hσ x) = Valued.v x := by
  refine congrFun (UniformSpace.Completion.ext
    ((continuous_valued (surjective_of_apply_eq hv hσ)).comp (continuous_congr hv hσ))
    (continuous_valued hv) fun y ↦ ?_) x
  refine (congrArg Valued.v (congr_coe hv hσ (WithVal.ofVal y))).trans ?_
  rw [Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, WithVal.valued_toVal, hσ,
    WithVal.apply_ofVal]

/-- `Valuation.Completion.congr` of the identity is the identity. -/
@[simp]
theorem congr_refl : congr hv (RingEquiv.refl K) (fun _ ↦ rfl) = RingEquiv.refl v.Completion :=
  RingEquiv.toRingHom_injective
    (eq_congr_of_continuous hv (fun _ ↦ rfl) (f := RingHom.id _) continuous_id fun _ ↦ rfl).symm

/-- `Valuation.Completion.congr` is compatible with composition. -/
@[simp]
theorem congr_trans (hw : Function.Surjective w) {τ : K' ≃+* K''} (hτ : ∀ y, u (τ y) = w y) :
    (congr hv σ hσ).trans (congr hw τ hτ) =
      congr hv (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) := by
  refine RingEquiv.toRingHom_injective <| eq_congr_of_continuous _ _
    ((continuous_congr hw hτ).comp (continuous_congr hv hσ)) fun x ↦ ?_
  change congr hw τ hτ (congr hv σ hσ (x : v.Completion)) = _
  rw [congr_coe, congr_coe, RingEquiv.trans_apply]

/-- The inverse of `Valuation.Completion.congr` is `Valuation.Completion.congr` of the inverse. -/
@[simp]
theorem congr_symm :
    (congr hv σ hσ).symm = congr (fun γ ↦ (hv γ).elim fun x hx ↦ ⟨σ x, (hσ x).trans hx⟩) σ.symm
      (fun y ↦ by rw [← hσ, RingEquiv.apply_symm_apply]) := by
  refine RingEquiv.toRingHom_injective <| eq_congr_of_continuous _ _
    (UniformSpace.Completion.continuous_mapRingEquiv_symm _ _ _) fun y ↦ ?_
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, congr_coe,
    RingEquiv.apply_symm_apply]

end Valuation.Completion
