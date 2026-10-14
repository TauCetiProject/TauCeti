/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.Topology.Algebra.UniformRing
public import TauCeti.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Transporting completions along isomorphisms

Let `σ : F ≃ₐ[k] F'` be an isomorphism carrying a place `P` of `F` to a place `Q` of `F'`, in the
sense that `v_Q (σ x) = v_P (x)`. Then `σ` is uniformly continuous for the two valuations and
extends by continuity to an isomorphism of completions `F_P ≃ₐ[k] F'_Q`, `Place.completionCongr`.
It is the only continuous extension of `σ`, it preserves the completed valuations, and it is
functorial: the identity extends to the identity, composites to composites, inverses to inverses.

For an automorphism `σ` of `F` fixing `P`, the extension preserves the completed valuation ring,
so it lies in the decomposition group of the completed place. This is how the decomposition group
of a place in a Galois extension acts on the completion.

## Main definitions

* `TauCeti.Place.completionCongr`: the isomorphism of completions `F_P ≃ₐ[k] F'_Q` extending `σ`.

## Main results

* `TauCeti.Place.completionCongr_completionEmbedding`: `completionCongr` extends `σ`.
* `TauCeti.Place.eq_completionCongr_of_continuous`: it is the only continuous ring homomorphism
  extending `σ`.
* `TauCeti.Place.valuation_completionCongr`: it preserves the completed valuations.
* `TauCeti.Place.completionCongr_refl`, `TauCeti.Place.completionCongr_trans` and
  `TauCeti.Place.completionCongr_symm`: functoriality.
* `TauCeti.Place.completionCongr_mem_decompositionSubgroup`: for an automorphism fixing `P`, the
  extension lies in the decomposition group of the completed valuation ring.
-/

public section

open scoped Pointwise

open WithZeroTopology

open scoped WithZero

namespace TauCeti.Place

variable {k F F' F'' : Type*} [Field k] [Field F] [Field F'] [Field F''] [Algebra k F]
  [Algebra k F'] [Algebra k F''] {P : Place k F} {Q : Place k F'} {R : Place k F''}

/-- An isomorphism carrying `v_P` to `v_Q` is uniformly continuous for the two valuations. -/
private theorem uniformContinuous_withValCongr (σ : F ≃ₐ[k] F')
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) :
    UniformContinuous (WithVal.congr P.valuation Q.valuation σ.toRingEquiv) :=
  WithVal.uniformContinuous_congr P.valuation_surjective _ hσ

/-- The inverse of an isomorphism carrying `v_P` to `v_Q` carries `v_Q` to `v_P`. -/
private theorem valuation_symm_apply {σ : F ≃ₐ[k] F'}
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) (y : F') :
    P.valuation (σ.symm y) = Q.valuation y := by
  rw [← hσ, AlgEquiv.apply_symm_apply]

/-- The ring isomorphism of completions underlying `TauCeti.Place.completionCongr`. -/
private noncomputable def completionRingEquiv (σ : F ≃ₐ[k] F')
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) : P.Completion ≃+* Q.Completion :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr P.valuation Q.valuation σ.toRingEquiv)
    (uniformContinuous_withValCongr σ hσ).continuous
    (uniformContinuous_withValCongr σ.symm (valuation_symm_apply hσ)).continuous

private theorem completionRingEquiv_completionEmbedding (σ : F ≃ₐ[k] F')
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) (x : F) :
    completionRingEquiv σ hσ (P.completionEmbedding x) = Q.completionEmbedding (σ x) := by
  rw [completionEmbedding_apply, completionEmbedding_apply]
  -- `WithVal.congr` sends `WithVal.toVal P.valuation x` to `WithVal.toVal Q.valuation (σ x)`
  exact UniformSpace.Completion.mapRingHom_coe
    (f := (WithVal.congr P.valuation Q.valuation σ.toRingEquiv).toRingHom)
    (uniformContinuous_withValCongr σ hσ).continuous (WithVal.toVal P.valuation x)

variable (P Q) in
/-- **The isomorphism of completions extending `σ`**: an isomorphism `σ : F ≃ₐ[k] F'` carrying
`v_P` to `v_Q` extends by continuity to `F_P ≃ₐ[k] F'_Q`. -/
noncomputable def completionCongr (σ : F ≃ₐ[k] F')
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) : P.Completion ≃ₐ[k] Q.Completion :=
  AlgEquiv.ofRingEquiv (f := completionRingEquiv σ hσ) fun c ↦ by
    rw [← P.completionEmbedding.commutes, completionRingEquiv_completionEmbedding,
      AlgEquiv.commutes, Q.completionEmbedding.commutes]

variable {σ : F ≃ₐ[k] F'} (hσ : ∀ x, Q.valuation (σ x) = P.valuation x)

/-- `completionCongr` extends `σ`. -/
@[simp]
theorem completionCongr_completionEmbedding (x : F) :
    completionCongr P Q σ hσ (P.completionEmbedding x) = Q.completionEmbedding (σ x) :=
  completionRingEquiv_completionEmbedding σ hσ x

/-- `completionCongr` is continuous. -/
theorem continuous_completionCongr : Continuous (completionCongr P Q σ hσ) :=
  UniformSpace.Completion.continuous_mapRingEquiv _ (uniformContinuous_withValCongr σ hσ).continuous
    (uniformContinuous_withValCongr σ.symm (valuation_symm_apply hσ)).continuous

/-- Two continuous maps out of a completion into a Hausdorff space that agree on the original
field are equal. -/
private theorem eq_of_continuous_of_completionEmbedding {X : Type*} [TopologicalSpace X]
    [T2Space X] {f g : P.Completion → X} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : F, f (P.completionEmbedding x) = g (P.completionEmbedding x)) : f = g :=
  P.denseRange_completionEmbedding.equalizer hf hg (funext h)

variable (P) in
/-- The valuation of the completed field is continuous. -/
private theorem continuous_valued_completion :
    Continuous (Valued.v : Valuation P.Completion ℤᵐ⁰) :=
  Valued.continuous_valuation_of_surjective fun γ ↦
    let ⟨y, hy⟩ := P.valuation_surjective γ
    ⟨P.completionEmbedding y, by rw [valuation_completionEmbedding, hy]⟩

/-- **`completionCongr` is the only continuous extension of `σ`.** -/
theorem eq_completionCongr_of_continuous {f : P.Completion →+* Q.Completion} (hf : Continuous f)
    (hfF : ∀ x : F, f (P.completionEmbedding x) = Q.completionEmbedding (σ x)) :
    f = (completionCongr P Q σ hσ : P.Completion →+* Q.Completion) :=
  DFunLike.coe_injective <| eq_of_continuous_of_completionEmbedding hf
    (continuous_completionCongr hσ) fun x ↦ by
      rw [hfF, RingHom.coe_coe, completionCongr_completionEmbedding]

/-- `completionCongr` preserves the completed valuations. -/
@[simp]
theorem valuation_completionCongr (x : P.Completion) :
    Valued.v (completionCongr P Q σ hσ x) = Valued.v x := by
  refine congrFun (eq_of_continuous_of_completionEmbedding
    ((continuous_valued_completion Q).comp (continuous_completionCongr hσ))
    (continuous_valued_completion P) fun y ↦ ?_) x
  simp [hσ]

/-- `completionCongr` maps the completed valuation ring of `P` into that of `Q`, and only it. -/
theorem completionCongr_mem_integers_iff {x : P.Completion} :
    completionCongr P Q σ hσ x ∈ Q.completionPlace.integers ↔ x ∈ P.completionPlace.integers := by
  simp only [mem_integers_iff, completionPlace_valuation, valuation_completionCongr]

variable (P) in
/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_refl :
    completionCongr P P (AlgEquiv.refl : F ≃ₐ[k] F) (fun _ ↦ by rw [AlgEquiv.coe_refl, id]) =
      AlgEquiv.refl :=
  AlgEquiv.ext <| congrFun <|
    eq_of_continuous_of_completionEmbedding (continuous_completionCongr _) continuous_id
      fun x ↦ by simp only [completionCongr_completionEmbedding, AlgEquiv.coe_refl, id_eq]

/-- `completionCongr` is compatible with composition. -/
@[simp]
theorem completionCongr_trans {τ : F' ≃ₐ[k] F''} (hτ : ∀ y, R.valuation (τ y) = Q.valuation y) :
    (completionCongr P Q σ hσ).trans (completionCongr Q R τ hτ) =
      completionCongr P R (σ.trans τ) (fun x ↦ by rw [AlgEquiv.trans_apply, hτ, hσ]) :=
  AlgEquiv.ext <| congrFun <| eq_of_continuous_of_completionEmbedding
    ((continuous_completionCongr hτ).comp (continuous_completionCongr hσ))
    (continuous_completionCongr _) fun x ↦ by simp

/-- The inverse of `completionCongr` is `completionCongr` of the inverse. -/
@[simp]
theorem completionCongr_symm :
    (completionCongr P Q σ hσ).symm =
      completionCongr Q P σ.symm (fun y ↦ by rw [← hσ, AlgEquiv.apply_symm_apply]) :=
  AlgEquiv.ext <| congrFun <| eq_of_continuous_of_completionEmbedding
    (UniformSpace.Completion.continuous_mapRingEquiv_symm _
      (uniformContinuous_withValCongr σ hσ).continuous
      (uniformContinuous_withValCongr σ.symm (valuation_symm_apply hσ)).continuous)
    (continuous_completionCongr _) fun y ↦ by
      rw [AlgEquiv.symm_apply_eq, completionCongr_completionEmbedding,
        completionCongr_completionEmbedding, AlgEquiv.apply_symm_apply]

variable (σ : F ≃ₐ[k] F) (hσ : ∀ x, P.valuation (σ x) = P.valuation x)

/-- For an automorphism `σ` fixing `P`, the extension of `σ` to the completion lies in the
decomposition group of the completed valuation ring. -/
theorem completionCongr_mem_decompositionSubgroup :
    completionCongr P P σ hσ ∈ P.completionPlace.integers.decompositionSubgroup k := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv,
    ← completionCongr_mem_integers_iff hσ, AlgEquiv.apply_symm_apply]

end TauCeti.Place
