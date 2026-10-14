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

Let `σ : K ≃+* K'` be a ring isomorphism carrying a valuation `v` on `K` to a valuation `w`
on `K'`, in the sense that `w (σ x) = v x`. Then `σ` is uniformly continuous for the uniform
structures that `v` and `w` define, so it extends to an isomorphism of the completions
`v.Completion ≃+* w.Completion`. This is how an automorphism of a field fixing a place acts on the
completion at that place.

## Main definitions

* `Valuation.Completion.congr`: the isomorphism of completions `v.Completion ≃+* w.Completion`
  extending `σ`.

## Main results

* `WithVal.uniformContinuous_congr`: the map
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

open Filter WithZeroTopology MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

namespace WithVal

variable {K K' : Type*} [Ring K] [Ring K'] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {w : Valuation K' Γ₀}

/-- **A valuation-preserving isomorphism is uniformly continuous.** If `σ : K ≃+* K'` carries the
valuation `v` to `w`, then `σ` is uniformly continuous as a map `WithVal v → WithVal w`. -/
theorem uniformContinuous_congr (σ : K ≃+* K')
    (hσ : ∀ x, w (σ x) = v x) : UniformContinuous (WithVal.congr v w σ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  -- Transport a representative quotient for the target value-group radius back along `σ`.
  have hγ : (WithVal.valueGroupOrderIso₀ w γ.1) ≠ 0 := by simp
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (WithVal.valueGroupOrderIso₀ w γ.1).zero_or_exists_mk.resolve_left hγ
  have hva : v (σ.symm a) ≠ 0 := by simpa [← hσ]
  have hvb : v (σ.symm b) ≠ 0 := by simpa [← hσ]
  let δ : v.ValueGroup₀ := valueGroup.mk (v : K →*₀ Γ₀) (σ.symm a) (σ.symm b) hva hvb
  have hδ : δ ≠ 0 := by simp [δ]
  let γ' : (Valued.v (R := WithVal v)).ValueGroup₀ˣ :=
    Units.mk0 ((WithVal.valueGroupOrderIso₀ v).symm δ) (by simp [hδ])
  refine ⟨γ', trivial, ?_⟩
  intro x hx
  rw [Set.mem_ofPred_eq] at hx ⊢
  apply (WithVal.strictMono_valueGroupOrderIso₀ w).lt_iff_lt.mp
  -- `Valued.v` on `WithVal w` is `WithVal.valuation w` by definition of the instance, and
  -- `rw` does not see through the instance, so restate the goal before rewriting.
  change (WithVal.valueGroupOrderIso₀ w) ((WithVal.valuation w).restrict _) < _
  rw [WithVal.valueGroupOrderIso₀_restrict, hab, Valuation.restrict_lt_iff_lt_embedding]
  have hx' := (WithVal.strictMono_valueGroupOrderIso₀ v).lt_iff_lt.mpr hx
  -- As above, for `Valued.v` on `WithVal v`.
  change (WithVal.valueGroupOrderIso₀ v) ((WithVal.valuation v).restrict x) < _ at hx'
  rw [WithVal.valueGroupOrderIso₀_restrict, Units.val_mk0, OrderMonoidIso.apply_symm_apply,
    Valuation.restrict_lt_iff_lt_embedding] at hx'
  have haeq : w a = v (σ.symm a) := by rw [← hσ, RingEquiv.apply_symm_apply]
  have hbeq : w b = v (σ.symm b) := by rw [← hσ, RingEquiv.apply_symm_apply]
  simpa [δ, valueGroup.mk, ValueGroup₀.embedding_apply, WithVal.congr_apply, hσ, haeq, hbeq]
    using hx'

end WithVal

namespace Valuation.Completion

variable {K K' K'' : Type*} [Ring K] [Ring K'] [Ring K''] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {w : Valuation K' Γ₀}
  {u : Valuation K'' Γ₀}

/-- **The completed valuation is continuous.** If every value of `v` is attained, the extension of
`v` to the completion `v.Completion` is continuous. -/
theorem continuous_valued {L : Type*} [Field L] {q : Valuation L Γ₀}
    (hq : Function.Surjective q) : Continuous (Valued.v : Valuation q.Completion Γ₀) :=
  Valued.continuous_valuation_of_surjective <|
    Valued.valuedCompletion_surjective_iff.mpr (.of_comp hq)

/-- The inverse of an isomorphism carrying `v` to `w` carries `w` to `v`. -/
private theorem symm_apply_eq {σ : K ≃+* K'} (hσ : ∀ x, w (σ x) = v x) (y : K') :
    v (σ.symm y) = w y := by
  rw [← hσ, RingEquiv.apply_symm_apply]

/-- **The isomorphism of completions extending `σ`**: an isomorphism `σ : K ≃+* K'` carrying the
valuation `v` to `w` extends by continuity to
`v.Completion ≃+* w.Completion`. -/
noncomputable def congr (σ : K ≃+* K') (hσ : ∀ x, w (σ x) = v x) :
    v.Completion ≃+* w.Completion :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr v w σ)
    (WithVal.uniformContinuous_congr σ hσ).continuous
    (WithVal.uniformContinuous_congr σ.symm (symm_apply_eq hσ)).continuous

variable {σ : K ≃+* K'} (hσ : ∀ x, w (σ x) = v x)

/-- `Valuation.Completion.congr` is the completion of `WithVal.congr v w σ`. -/
theorem congr_apply (x : v.Completion) :
    congr σ hσ x = UniformSpace.Completion.map (WithVal.congr v w σ) x :=
  UniformSpace.Completion.mapRingEquiv_apply _ _ _ x

/-- `Valuation.Completion.congr` extends `σ`. -/
@[simp]
theorem congr_coe (x : K) : congr σ hσ (x : v.Completion) = (σ x : w.Completion) := by
  rw [congr_apply, UniformSpace.Completion.map_coe (WithVal.uniformContinuous_congr σ hσ)]
  rfl

/-- `Valuation.Completion.congr` is continuous. -/
theorem continuous_congr : Continuous (congr σ hσ) :=
  UniformSpace.Completion.continuous_mapRingEquiv _ _ _

/-- **`Valuation.Completion.congr` is the only continuous extension of `σ`.** -/
theorem eq_congr_of_continuous {f : v.Completion →+* w.Completion} (hf : Continuous f)
    (hfK : ∀ x : K, f (x : v.Completion) = (σ x : w.Completion)) :
    f = (congr σ hσ).toRingHom :=
  DFunLike.coe_injective <| UniformSpace.Completion.ext hf (continuous_congr hσ) fun x ↦
    (hfK (WithVal.ofVal x)).trans (congr_coe hσ (WithVal.ofVal x)).symm

/-- `Valuation.Completion.congr` preserves the completed valuations. -/
@[simp]
theorem valued_congr {L L' : Type*} [Field L] [Field L'] {q : Valuation L Γ₀}
    {q' : Valuation L' Γ₀} (hq : Function.Surjective q) {τ : L ≃+* L'}
    (hτ : ∀ x, q' (τ x) = q x) (x : q.Completion) : Valued.v (congr τ hτ x) = Valued.v x := by
  refine congrFun (UniformSpace.Completion.ext
    ((continuous_valued (.of_comp (g := τ) (by simpa [Function.comp_def, hτ]))).comp
      (continuous_congr hτ)) (continuous_valued hq) fun y ↦ ?_) x
  refine (congrArg Valued.v (congr_coe hτ (WithVal.ofVal y))).trans ?_
  rw [Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, WithVal.valued_toVal, hτ,
    WithVal.apply_ofVal]

/-- `Valuation.Completion.congr` of the identity is the identity. -/
@[simp]
theorem congr_refl : congr (RingEquiv.refl K) (fun _ ↦ rfl) = RingEquiv.refl v.Completion :=
  RingEquiv.toRingHom_injective
    (eq_congr_of_continuous (fun _ ↦ rfl) (f := RingHom.id _) continuous_id fun _ ↦ rfl).symm

/-- `Valuation.Completion.congr` is compatible with composition. -/
@[simp]
theorem congr_trans {τ : K' ≃+* K''} (hτ : ∀ y, u (τ y) = w y) :
    (congr σ hσ).trans (congr τ hτ) =
      congr (σ.trans τ) (fun x ↦ by rw [RingEquiv.trans_apply, hτ, hσ]) := by
  refine RingEquiv.toRingHom_injective <| eq_congr_of_continuous _
    ((continuous_congr hτ).comp (continuous_congr hσ)) fun x ↦ ?_
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply]
  rw [congr_coe, congr_coe, RingEquiv.trans_apply]

/-- The inverse of `Valuation.Completion.congr` is `Valuation.Completion.congr` of the inverse. -/
@[simp]
theorem congr_symm :
    (congr σ hσ).symm = congr σ.symm
      (fun y ↦ by rw [← hσ, RingEquiv.apply_symm_apply]) := by
  refine RingEquiv.toRingHom_injective <| eq_congr_of_continuous _
    (UniformSpace.Completion.continuous_mapRingEquiv_symm _ _ _) fun y ↦ ?_
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, congr_coe,
    RingEquiv.apply_symm_apply]

end Valuation.Completion
