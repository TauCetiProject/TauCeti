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
* `IsDedekindDomain.HeightOneSpectrum.completionCongr_algebraMap`: `completionCongr` extends `σ`.
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
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
          IsScalarTower.algebraMap_apply K L (w.adicCompletion L), RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, adicCompletionCongr_algebraMap, AlgEquiv.coe_ringEquiv,
          AlgEquiv.commutes]
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

/-- Two continuous maps out of `L_w` that agree on `L` are equal. -/
private theorem algEquiv_ext_of_continuous {w'' : HeightOneSpectrum (𝒪 L)}
    [w''.asIdeal.LiesOver v.asIdeal]
    {f g : w.adicCompletion L ≃ₐ[v.adicCompletion K] w''.adicCompletion L}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  AlgEquiv.coe_toAlgHom_injective <| AlgHom.coe_fn_injective <|
    (w.denseRange_algebraMap L).equalizer hf hg (funext hfg)

/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_one (h : w.asIdeal = (1 : L ≃ₐ[K] L) • w.asIdeal) :
    completionCongr v (1 : L ≃ₐ[K] L) h = AlgEquiv.refl :=
  algEquiv_ext_of_continuous (continuous_completionCongr v _ h) continuous_id fun x ↦ by simp

/-- `completionCongr` is multiplicative: transporting along `σ` and then along `τ` is
transporting along `τ * σ`. -/
theorem completionCongr_trans {w'' : HeightOneSpectrum (𝒪 L)} [w''.asIdeal.LiesOver v.asIdeal]
    (σ τ : L ≃ₐ[K] L) (hσ : w'.asIdeal = σ • w.asIdeal) (hτ : w''.asIdeal = τ • w'.asIdeal)
    (hτσ : w''.asIdeal = (τ * σ) • w.asIdeal) :
    (completionCongr v σ hσ).trans (completionCongr v τ hτ) = completionCongr v (τ * σ) hτσ :=
  algEquiv_ext_of_continuous (v := v)
    ((continuous_completionCongr v τ hτ).comp (continuous_completionCongr v σ hσ))
    (continuous_completionCongr v _ hτσ) fun x ↦ by simp

/-- The inverse of `completionCongr v σ h` is `completionCongr` of `σ⁻¹`. -/
theorem completionCongr_symm (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (h' : w.asIdeal = σ⁻¹ • w'.asIdeal) :
    (completionCongr v σ h).symm = completionCongr v σ⁻¹ h' := by
  have hid : (completionCongr v σ⁻¹ h').trans (completionCongr v σ h) = AlgEquiv.refl :=
    algEquiv_ext_of_continuous (v := v)
      ((continuous_completionCongr v σ h).comp (continuous_completionCongr v σ⁻¹ h'))
      continuous_id fun x ↦ by simp
  refine AlgEquiv.ext fun y ↦ ?_
  rw [AlgEquiv.symm_apply_eq, ← AlgEquiv.trans_apply, hid, AlgEquiv.coe_refl, id]

end completionCongr

variable (v) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The action of the decomposition group of `w` on the completion `L_w`: each element of the
stabilizer of `w` extends by continuity to a `K_v`-algebra automorphism of `L_w`. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      w.adicCompletion L) where
  toFun τ := completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm
  map_one' := completionCongr_one _
  map_mul' σ τ := (completionCongr_trans (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp τ.2).symm (MulAction.mem_stabilizer_iff.mp σ.2).symm
      (MulAction.mem_stabilizer_iff.mp (σ * τ).2).symm).symm

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
  have h' : w.asIdeal = σ⁻¹ • w'.asIdeal := by rw [h, inv_smul_smul]
  rw [completionCongr_symm σ h h']
  refine algEquiv_ext_of_continuous (continuous_decompositionHom v τ')
    ((continuous_completionCongr v σ h).comp ((continuous_decompositionHom v τ).comp
      (continuous_completionCongr v σ⁻¹ h'))) fun x ↦ ?_
  simp [hτ]

end IsDedekindDomain.HeightOneSpectrum
