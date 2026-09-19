/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# The decomposition group acts on the completion

Let `L/K` be an extension of number fields, `v` a finite place of `K`, and `w` a finite place of
`L` above `v`. An automorphism `σ ∈ Aut(L/K)` carries `w` to the place `σ • w`, and extends by
continuity to an isomorphism of completions `L_w ≃ₐ[K_v] L_{σ • w}`. This file constructs that
isomorphism, `completionCongr`, and restricts it to the decomposition group, the stabilizer of
`w`, to obtain the homomorphism

```text
decompositionHom v w : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (L_w ≃ₐ[K_v] L_w).
```

The target place of `completionCongr` is an arbitrary `w'` together with the equation
`w'.asIdeal = σ • w.asIdeal`, so that no transport along an equality of places is needed.
Both completions carry the canonical `K_v`-algebra structure of `completionAlgHom`, which is
available in the `AdicCompletionExtension` scope.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.completionCongr`: the isomorphism `L_w ≃ₐ[K_v] L_{w'}`
  induced by `σ` when `w' = σ • w`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom`: the action of the decomposition group
  of `w` on `L_w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul`: `σ` carries the
  `w`-adic valuation to the `σ • w`-adic valuation.
* `IsDedekindDomain.HeightOneSpectrum.completionCongr_algebraMap` and
  `IsDedekindDomain.HeightOneSpectrum.eq_completionCongr_of_continuous`: `completionCongr`
  extends `σ`, uniquely among continuous ring homomorphisms.
* `IsDedekindDomain.HeightOneSpectrum.valued_completionCongr`: `completionCongr` preserves the
  completion valuations.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_algebraMap`: the defining property
  `decompositionHom v w τ x = τ x` for `x ∈ L`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_injective`: the decomposition group
  embeds into `Aut(L_w/K_v)`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_conj`: compatibility with the action of
  `Aut(L/K)` on the places above `v`; conjugating by `σ` corresponds to transporting along
  `completionCongr σ`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §9.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField Pointwise AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- An automorphism `σ` of `L/K` carries the `w`-adic valuation to the `w'`-adic valuation
when `w' = σ • w`. -/
theorem valuation_apply_eq_of_asIdeal_eq_smul (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝒪 L)} (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    w'.valuation L (σ x) = w.valuation L x := by
  let e := MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝒪 L) σ
  have hσ : (IsFractionRing.ringEquivOfRingEquiv e : L ≃+* L) = σ.toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝒪 L)) (S := L) (RingHom.ext fun r ↦ ?_)
    simp [e]
  have hw : w'.asIdeal = Ideal.map e w.asIdeal := by
    rw [h, Ideal.pointwise_smul_def]
    -- `e` and `MulSemiringAction.toRingHom _ _ σ` bundle the same map, as an equivalence and as
    -- a homomorphism respectively
    rfl
  rw [← valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hw x, hσ, AlgEquiv.coe_ringEquiv]

variable [NumberField K] (v : HeightOneSpectrum (𝒪 K))

/-- The isomorphism of completions `L_w ≃ₐ[K_v] L_{w'}` induced by an automorphism `σ` of `L/K`
carrying `w` to `w'`: the continuous extension of `σ`. -/
def completionCongr (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝒪 L)}
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w'.asIdeal = σ • w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := adicCompletionCongr w w' σ.toRingEquiv
    (valuation_apply_eq_of_asIdeal_eq_smul σ h)) fun a ↦ by
    -- both sides are continuous in `a` and extend `K → L`, so they are the canonical map
    have := eq_completionAlgHom_of_continuous v w'
      ((adicCompletionCongr w w' σ.toRingEquiv
        (valuation_apply_eq_of_asIdeal_eq_smul σ h)).toRingHom.comp
          (completionAlgHom v w).toRingHom)
      ((continuous_adicCompletionCongr _).comp (continuous_completionAlgHom v w)) fun x ↦ by
        simp [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    rw [algebraMap_eq_completionAlgHom, algebraMap_eq_completionAlgHom]
    exact congr($this a)

variable {v}

section completionCongr

variable {w w' : HeightOneSpectrum (𝒪 L)} [w.asIdeal.LiesOver v.asIdeal]
  [w'.asIdeal.LiesOver v.asIdeal]

/-- `completionCongr v σ h` extends `σ`. -/
@[simp]
theorem completionCongr_algebraMap (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    completionCongr v σ h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) := by
  rw [completionCongr, AlgEquiv.ofRingEquiv_apply, adicCompletionCongr_algebraMap,
    AlgEquiv.coe_ringEquiv]

variable (v) in
/-- `completionCongr` is continuous. -/
theorem continuous_completionCongr (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) :
    Continuous (completionCongr v σ h) :=
  continuous_adicCompletionCongr _

/-- `completionCongr` is the only continuous ring homomorphism `L_w →+* L_{w'}` extending `σ`. -/
theorem eq_completionCongr_of_continuous (σ : L ≃ₐ[K] L)
    (h : w'.asIdeal = σ • w.asIdeal) {f : w.adicCompletion L →+* w'.adicCompletion L}
    (hf : Continuous f)
    (hfL : ∀ x : L, f (algebraMap L _ x) = algebraMap L (w'.adicCompletion L) (σ x)) :
    f = (completionCongr v σ h).toRingEquiv.toRingHom := by
  apply eq_adicCompletionCongr_of_continuous
  · exact hf
  · exact hfL

/-- `completionCongr` preserves the valuations of the completions. -/
@[simp]
theorem valued_completionCongr (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (completionCongr v σ h x) = Valued.v x :=
  valued_adicCompletionCongr _ x

/-- `completionCongr` depends only on the automorphism, not on the proof that it carries `w`
to `w'`. -/
private theorem completionCongr_congr {σ σ' : L ≃ₐ[K] L} (hσσ' : σ = σ')
    (h : w'.asIdeal = σ • w.asIdeal) (h' : w'.asIdeal = σ' • w.asIdeal) :
    completionCongr v σ h = completionCongr v σ' h' := by
  subst hσσ'
  rfl

/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_one :
    completionCongr (w := w) (w' := w) v (1 : L ≃ₐ[K] L)
      (by simp) = AlgEquiv.refl :=
  AlgEquiv.coe_ringEquiv_injective adicCompletionCongr_one

/-- `completionCongr` is multiplicative: transporting along `σ` and then along `τ` is
transporting along `τ * σ`. -/
@[simp]
theorem completionCongr_trans {w'' : HeightOneSpectrum (𝒪 L)} [w''.asIdeal.LiesOver v.asIdeal]
    (σ τ : L ≃ₐ[K] L) (hσ : w'.asIdeal = σ • w.asIdeal) (hτ : w''.asIdeal = τ • w'.asIdeal) :
    (completionCongr v σ hσ).trans (completionCongr v τ hτ) =
      completionCongr v (τ * σ) (by rw [hτ, hσ, mul_smul]) :=
  AlgEquiv.coe_ringEquiv_injective (adicCompletionCongr_trans _ _ _ _)

/-- The inverse of `completionCongr v σ h` is `completionCongr` of `σ⁻¹`. -/
@[simp]
theorem completionCongr_symm (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) :
    (completionCongr v σ h).symm =
      completionCongr v σ⁻¹
        (by rw [h, inv_smul_smul]) :=
  AlgEquiv.coe_ringEquiv_injective (adicCompletionCongr_symm _)

end completionCongr

variable (v) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The action of the decomposition group of `w` on the completion `L_w`: each element of the
stabilizer of `w` extends by continuity to a `K_v`-algebra automorphism of `L_w`. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      w.adicCompletion L) where
  toFun τ := completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm
  map_one' := completionCongr_one
  map_mul' σ τ := (completionCongr_trans (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp τ.2).symm
      (MulAction.mem_stabilizer_iff.mp σ.2).symm).symm

variable {v w}

/-- An element of the decomposition group acts on `L_w` by `completionCongr`. -/
theorem decompositionHom_apply (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    decompositionHom v w τ =
      completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm :=
  (rfl)

/-- The defining property of `decompositionHom`: on `L` it is the action of the automorphism. -/
@[simp]
theorem decompositionHom_algebraMap (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : L) :
    decompositionHom v w τ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((τ : L ≃ₐ[K] L) x) := by
  rw [decompositionHom_apply, completionCongr_algebraMap]

variable (v) in
/-- Each element of the decomposition group acts continuously on `L_w`. -/
theorem continuous_decompositionHom (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    Continuous (decompositionHom v w τ) := by
  rw [decompositionHom_apply]
  exact continuous_completionCongr v _ _

variable (v w) in
/-- The decomposition group of `w` acts faithfully on `L_w`. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext x
  have := congr($hτ (algebraMap L (w.adicCompletion L) x))
  rw [decompositionHom_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this

/-- **Compatibility of `decompositionHom` with the action on places.** If `σ` carries `w` to
`w'` and `τ` stabilizes `w`, then the action of `σ τ σ⁻¹` on `L_{w'}` is the action of `τ` on
`L_w` transported along `completionCongr σ`. -/
theorem decompositionHom_conj {w' : HeightOneSpectrum (𝒪 L)} [w'.asIdeal.LiesOver v.asIdeal]
    (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    (τ' : MulAction.stabilizer (L ≃ₐ[K] L) w'.asIdeal)
    (hτ : (τ' : L ≃ₐ[K] L) = σ * τ * σ⁻¹) :
    decompositionHom v w' τ' =
      (completionCongr v σ h).symm.trans
        ((decompositionHom v w τ).trans (completionCongr v σ h)) := by
  rw [decompositionHom_apply, decompositionHom_apply, completionCongr_symm, completionCongr_trans,
    completionCongr_trans]
  exact completionCongr_congr (by rw [hτ, mul_assoc]) _ _

end IsDedekindDomain.HeightOneSpectrum
