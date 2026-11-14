/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.TFAE
import TauCeti.Algebra.Algebra.Hom
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer.Basic
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import TauCeti.RingTheory.Unramified.Field

/-!
# Kummer elimination and characterization of tamely ramified extensions

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. This file proves that adjoining an `n`-th root of `π`, where `n`
is a multiple of every ramification index of `L` over `A`, eliminates tame ramification (Stacks,
Lemma 15.116.4 (0BRM), finite separable case) and deduces the Kummer characterization of tame
ramification (Stacks, Lemma 15.116.7 (0EXW)).

The elimination step follows SGA 1, Exposé X, Lemme 3.6 via the local structure of the Abhyankar
model (`TauCeti.exists_algEquiv_localization_abhyankarModel`). If `L / K` is tamely ramified with
respect to `A` and `n` is a multiple of every ramification index over `A`, passing to any factor
field `E` of `K₁ ⊗[K] L` for a Kummer extension `K₁ = K(α₀)` (`α₀ ^ n = π`) produces a finite
separable extension `E / K₁` that is unramified with respect to the discrete valuation ring
`integralClosure A K₁`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_surjective_of_pow_eq_of_irreducible`):
each localization of the integral closure of `A[α₀]` in `E` at a maximal ideal is isomorphic to a
localization of the Abhyankar model over the corresponding discrete valuation ring of `L`, so `α₀`
remains a uniformizer there and the residue extension remains separable. Taking `e₀` to be the
common tame exponent (`TauCeti.Algebra.IsTamelyRamifiedWRT.exists_ramificationIdx_dvd`) gives an
exponent invertible in `κ_A`, and any further tame multiple `d * e₀` works the same way inside a
separable closure. Together with the converse
`TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible`,
this gives the three-way equivalence of Lemma 15.116.7 (`TauCeti.Algebra.isTamelyRamifiedWRT_tfae`).

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_surjective_of_pow_eq_of_irreducible`,
  `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible`, and
  `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_of_pow_eq_of_irreducible`: adjoining
  an `n`-th root of a uniformizer, where every ramification index of `L` over `A` divides `n`,
  eliminates tame ramification on every factor field of the base change.
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae`,
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`,
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_forall_kummer`, and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_adjoin_root`: the Kummer characterizations of
  tame ramification (Stacks, Lemma 15.116.7).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

universe u

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing

namespace TauCeti.Algebra

section EliminateRamification

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- Local Abhyankar elimination step at a single maximal ideal `M'` of `C'` lying over the closed
point of `A₁`: localizing `C` at `M' ∩ C` and `C'` at `M'` puts `M'` in the setting of
`TauCeti.exists_algEquiv_localization_abhyankarModel`, yielding ramification index one and
separable residue extension over `A₁`. -/
private theorem ramificationIdx_eq_one_and_isSeparable_at_maximal
    {A K L A₁ C C' E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [Algebra.IsIntegral A A₁]
    [CommRing C] [IsDedekindDomain C] [Algebra A C] [Algebra.IsIntegral A C] [Algebra C L]
    [IsScalarTower A C L] [IsFractionRing C L]
    [CommRing C'] [IsDedekindDomain C'] [Algebra A₁ C'] [Algebra A C'] [Algebra C C']
    [IsScalarTower A A₁ C'] [IsScalarTower A C C'] [Algebra.IsIntegral C C']
    [Field E] [Algebra A E] [Algebra L E] [Algebra A₁ E] [Algebra C E] [Algebra C' E]
    [IsScalarTower A L E] [IsScalarTower A₁ C' E] [IsScalarTower C C' E] [IsScalarTower C L E]
    [FaithfulSMul A₁ E] [IsFractionRing C' E]
    {π : A} (hπ : Irreducible π) {α₁ : A₁} (hα₁ : Irreducible α₁)
    {n : ℕ} (hn : n ≠ 0) (hβ : (algebraMap A₁ E α₁) ^ n = algebraMap A E π)
    (hβ_alg : IsAlgebraic L (algebraMap A₁ E α₁))
    (hgenE : L⟮algebraMap A₁ E α₁⟯ = ⊤)
    (htame : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (C ⧸ P) ∧
        IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A))
    (hdvd : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)], P.ramificationIdx A ∣ n)
    (M' : Ideal C') [M'.IsMaximal] [M'.LiesOver (maximalIdeal A₁)] :
    M'.ramificationIdx A₁ = 1 ∧ Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (C' ⧸ M') := by
  let P : Ideal C := M'.under C
  have : M'.LiesOver P := ⟨rfl⟩
  have : P.IsMaximal := Ideal.IsMaximal.under C M'
  have : P.LiesOver (maximalIdeal A) := ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  have : (maximalIdeal A₁).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : M'.LiesOver (maximalIdeal A) := .trans M' (maximalIdeal A₁) (maximalIdeal A)
  have : FaithfulSMul A C := .of_field_isFractionRing A C K L
  have : FaithfulSMul C C' := .of_field_isFractionRing C C' L E
  have : FaithfulSMul A₁ C' := .tower_bot A₁ C' E
  let B_loc := Localization.AtPrime P
  let S_loc := Localization.AtPrime M'
  have : IsDiscreteValuationRing B_loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C
      (Ideal.ne_bot_of_liesOver_of_ne_bot (_root_.IsDiscreteValuationRing.not_a_field A) P) B_loc
  have : IsDiscreteValuationRing S_loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C'
      (Ideal.ne_bot_of_liesOver_of_ne_bot (_root_.IsDiscreteValuationRing.not_a_field A₁) M') S_loc
  let : Algebra B_loc E := ((algebraMap L E).comp (algebraMap B_loc L)).toAlgebra
  have : IsScalarTower B_loc L E := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower C B_loc E := .to₁₂₄ C B_loc L E
  have : IsScalarTower A₁ S_loc E := .to₁₃₄ A₁ C' S_loc E
  have : IsScalarTower B_loc S_loc E :=
    Localization.AtPrime.isScalarTower_of_isScalarTower (C := C) (C' := C') P M'
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B_loc
  obtain ⟨u, hu_eq⟩ :=
    TauCeti.IsDiscreteValuationRing.exists_unit_mul_pow_ramificationIdx_localization hπ P hϖ
  have he_A : IsUnit (P.ramificationIdx A : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact (htame P).2)
  have he_B : IsUnit (P.ramificationIdx A : B_loc) := by simpa using he_A.map (algebraMap A B_loc)
  obtain ⟨d, hd_eq⟩ := hdvd P
  have hd : d ≠ 0 := right_ne_zero_of_mul (hd_eq ▸ hn)
  have hβ_SE : algebraMap S_loc E (algebraMap A₁ S_loc α₁) = algebraMap A₁ E α₁ :=
    (IsScalarTower.algebraMap_apply A₁ S_loc E α₁).symm
  have hβ_pow : (algebraMap A₁ S_loc α₁) ^ (P.ramificationIdx A * d) =
      algebraMap B_loc S_loc (↑u * ϖ ^ P.ramificationIdx A) :=
    IsFractionRing.injective S_loc E (by
      rw [map_pow, hβ_SE, ← hd_eq, hβ, ← hu_eq, IsScalarTower.algebraMap_apply A C B_loc,
        ← IsScalarTower.algebraMap_apply B_loc S_loc E, IsScalarTower.algebraMap_apply B_loc L E,
        ← IsScalarTower.algebraMap_apply C B_loc L,
        ← IsScalarTower.algebraMap_apply A C L, ← IsScalarTower.algebraMap_apply A L E])
  have hgenS := TauCeti.IntermediateField.exists_multiple_mem_adjoin_of_adjoin_simple_eq_top
    (A := B_loc) (K := L) (hβ_SE ▸ hβ_alg) (hβ_SE ▸ hgenE)
  have hβ_irr : Irreducible (algebraMap A₁ S_loc α₁) :=
    irreducible_of_pow_eq_unit_mul_pow hϖ u.isUnit he_B hd hβ_pow hgenS
  have hmapA₁ : (maximalIdeal A₁).map (algebraMap A₁ S_loc) = maximalIdeal S_loc ^ 1 := by
    rw [pow_one, hα₁.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hβ_irr.maximalIdeal_eq]
  refine ⟨Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) M' 1 hmapA₁, ?_⟩
  have := (htame P).1
  have := isSeparable_residueField_of_pow_eq_unit_mul_pow hϖ u.isUnit he_B hd hβ_pow hgenS
  have : Algebra.IsSeparable (maximalIdeal A).ResidueField M'.ResidueField :=
    .trans _ P.ResidueField _
  have := Algebra.isSeparable_tower_top_of_isSeparable (maximalIdeal A).ResidueField
    (maximalIdeal A₁).ResidueField M'.ResidueField
  exact inferInstance

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Eliminating tame ramification on a factor of a Kummer base change.** Let `L / K` be a finite
separable extension tamely ramified with respect to a discrete valuation ring `A` with fraction
field `K` and uniformizer `π`, and let `n` be a multiple of every ramification index of `L` over
`A`. If `K₁ = K(α₀)` is generated over `K` by an `n`-th root `α₀` of `π` and `E` is any field
receiving a surjective `K₁`-algebra homomorphism from `K₁ ⊗[K] L`, then `integralClosure A K₁` is a
discrete valuation ring and `E` is a finite separable extension of `K₁` that is unramified with
respect to `integralClosure A K₁`.

No invertibility assumption on `n` itself is needed: `n` may be a wild multiple of the tame
ramification indices. This is the finite separable case of Abhyankar's lemma for discrete valuation
rings (SGA 1, Exposé X, Lemme 3.6; Stacks, Lemma 15.116.4 (0BRM)). -/
@[stacks 0BRM "finite separable case, factor field of Kummer base change"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_of_surjective_of_pow_eq_of_irreducible
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {K₁ E : Type*} [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [Field E] [Algebra K₁ E]
    {α₀ : K₁} (hα₀ : α₀ ^ n = algebraMap A K₁ π) (hgenK₁ : K⟮α₀⟯ = ⊤)
    (φ : K₁ ⊗[K] L →ₐ[K₁] E) (hφ : Function.Surjective φ) :
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K₁) E ∧
        FiniteDimensional K₁ E ∧ Algebra.IsSeparable K₁ E := by
  have := FaithfulSMul.trans A K K₁
  have hn : n ≠ 0 := Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A K₁) hπ.ne_one hα₀
  let : Algebra K E := ((algebraMap K₁ E).comp (algebraMap K K₁)).toAlgebra
  let : Algebra A E := ((algebraMap K₁ E).comp (algebraMap A K₁)).toAlgebra
  have : IsScalarTower K K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K E := .to₁₂₄ A K K₁ E
  let jL : L →ₐ[K] E := (φ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra L E := jL.toAlgebra
  have : IsScalarTower K L E := .of_algHom jL
  have : IsScalarTower A L E := .to₁₃₄ A K L E
  let A₁ := integralClosure A K₁
  have hDVR : IsDiscreteValuationRing A₁ :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hα₀ hgenK₁
  have hdegK₁ := TauCeti.IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hα₀ hgenK₁
  have : FiniteDimensional K K₁ :=
    Module.finite_of_finrank_pos (hdegK₁ ▸ Nat.pos_of_ne_zero hn)
  have : IsFractionRing A₁ K₁ := IsIntegralClosure.isFractionRing_of_finite_extension A K K₁ _
  have : FaithfulSMul A₁ E := .trans A₁ K₁ E
  obtain ⟨hfinE, hsepE⟩ := φ.finiteDimensional_and_isSeparable_of_surjective_of_isSeparable hφ
  have hα₀_mem : α₀ ∈ A₁ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα₀ ▸ isIntegral_algebraMap)
  let α₁ : A₁ := ⟨α₀, hα₀_mem⟩
  have hα₁ : Irreducible α₁ :=
    TauCeti.IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hα₀ hgenK₁ hα₀_mem
  have hα₁_E : algebraMap A₁ E α₁ = algebraMap K₁ E α₀ :=
    IsScalarTower.algebraMap_apply A₁ K₁ E α₁
  have hβ : (algebraMap A₁ E α₁) ^ n = algebraMap A E π := by
    rw [hα₁_E, ← map_pow, hα₀, ← IsScalarTower.algebraMap_apply A K₁ E]
  have hβ_intL : IsIntegral L (algebraMap A₁ E α₁) :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hβ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hgenE : L⟮algebraMap A₁ E α₁⟯ = ⊤ := by
    rw [hα₁_E]
    have htop : _root_.IntermediateField.adjoin L
        (Set.range (IsScalarTower.toAlgHom K K₁ E)) = ⊤ := by
      refine eq_top_iff.mpr fun y _ ↦ ?_
      obtain ⟨t, rfl⟩ := hφ y
      refine TensorProduct.inductionOn t (fun k₁ l ↦ ?_)
        (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
      have htmul : φ (k₁ ⊗ₜ[K] l) = algebraMap K₁ E k₁ * algebraMap L E l := by
        have hk : k₁ ⊗ₜ[K] l = k₁ • ((1 : K₁) ⊗ₜ[K] l) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hk, map_smul, Algebra.smul_def]
        simp [jL, RingHom.algebraMap_toAlgebra]
      rw [htmul]
      exact mul_mem (subset_adjoin L _ ⟨k₁, rfl⟩) (_root_.algebraMap_mem _ l)
    simpa using ((IsScalarTower.toAlgHom K K₁ E).adjoin_range_eq_adjoin_image (F := L)
      hgenK₁).symm.trans htop
  let C := integralClosure A L
  let C' := integralClosure A₁ E
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K L
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L _
  have : IsDedekindDomain C' := integralClosure.isDedekindDomain A₁ K₁ E
  have : IsFractionRing C' E := IsIntegralClosure.isFractionRing_of_finite_extension A₁ K₁ E _
  let := integralClosureMapAlgebra A L A₁ E
  have := isScalarTower_integralClosureMapAlgebra_left A L A₁ E
  have := isScalarTower_integralClosureMapAlgebra_right A L A₁ E
  have : Algebra.IsIntegral A C' := Algebra.IsIntegral.trans A₁
  have : Algebra.IsIntegral C C' := .tower_top A
  exact ⟨hDVR, isUnramifiedWRT_def.mpr fun M' _ _ ↦
    ramificationIdx_eq_one_and_isSeparable_at_maximal (K := K) (L := L) (C := C) (C' := C')
      hπ hα₁ hn hβ hβ_intL.isAlgebraic hgenE (isTamelyRamifiedWRT_def.mp h) hdvd M',
    hfinE, hsepE⟩

/-- **Eliminating tame ramification over an adjoined Kummer subfield.** Let `L` be a finite
separable extension of the fraction field `K` of a discrete valuation ring `A` that is tamely
ramified with respect to `A`. Let `π` be a uniformizer of `A`, and let `n` be a multiple of every
ramification index of `L` over `A`. If `E` is generated over `L` by an `n`-th root `β` of `π`, then
`integralClosure A K(β)` is a discrete valuation ring and `E` is a finite separable extension of
`K(β)` that is unramified with respect to `integralClosure A K(β)`. -/
@[stacks 0BRM "finite separable case over a Kummer subfield"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {E : Type*} [Field E] [Algebra A E] [Algebra K E] [Algebra L E]
    [IsScalarTower A K E] [IsScalarTower K L E] {β : E}
    (hβ : β ^ n = algebraMap A E π) (hgen : L⟮β⟯ = ⊤) :
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
        FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E := by
  have : IsScalarTower A L E := .to₁₃₄ A K L E
  have := FaithfulSMul.trans A K E
  have hn : n ≠ 0 := Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A E) hπ.ne_one hβ
  have hβ_int : IsIntegral L β :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hβ ▸ isIntegral_algebraMap (R := A))).tower_top
  obtain ⟨ψ, hψ⟩ := TauCeti.IntermediateField.exists_surjective_tensorProduct_of_adjoin_eq_top
    (K := K) (K₁ := K⟮β⟯) (α₀ := AdjoinSimple.gen K β) hβ_int.isAlgebraic hgen
  exact h.isUnramifiedWRT_of_surjective_of_pow_eq_of_irreducible hπ hdvd
    ((AdjoinSimple.gen_pow_eq_algebraMap_iff K).mpr hβ)
    (adjoin_adjoinSimple_gen_eq_top β) ψ hψ

/-- **Adjoining a root of a uniformizer to eliminate tame ramification.** In an ambient extension
field `Ω` of `L`, adjoining an `n`-th root `α` of a uniformizer `π` of `A` to both `K` and `L`,
where every ramification index of `L` over `A` divides `n`, makes `integralClosure A K(α)` a
discrete valuation ring and `L(α)` a finite separable extension of `K(α)` that is unramified with
respect to `integralClosure A K(α)`. -/
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_of_pow_eq_of_irreducible
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω]
    [Algebra A Ω] [IsScalarTower K L Ω] [IsScalarTower A K Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {α : Ω} (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ ∧
        FiniteDimensional K⟮α⟯ L⟮α⟯ ∧ Algebra.IsSeparable K⟮α⟯ L⟮α⟯ := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have : IsScalarTower A L Ω := .to₁₃₄ A K L Ω
  have := FaithfulSMul.trans A K Ω
  have hn : n ≠ 0 := Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A Ω) hπ.ne_one hα
  have hα_int : IsIntegral L α :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap (R := A))).tower_top
  exact h.isUnramifiedWRT_of_surjective_of_pow_eq_of_irreducible hπ hdvd
    ((AdjoinSimple.gen_pow_eq_algebraMap_iff K).mpr hα)
    (adjoin_adjoinSimple_gen_eq_top α)
    (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α)
    (TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hα_int)

end EliminateRamification

section KummerCharacterization

variable {A K : Type*} {L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Helper packaging `L(α)` inside an abstract separably closed overfield `Ω : Type u` as an
existential witness for `isTamelyRamifiedWRT_tfae`. -/
private theorem exists_kummer_witness_of_dvd {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra L Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hn_unit : IsUnit (n : A ⧸ maximalIdeal A))
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
      (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E),
      β ^ n = algebraMap A E π ∧
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
            FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E := by
  let : Algebra K Ω := ((algebraMap L Ω).comp (algebraMap K L)).toAlgebra
  let : Algebra A Ω := ((algebraMap L Ω).comp (algebraMap A L)).toAlgebra
  have : IsScalarTower K L Ω := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun _ ↦ rfl
  have hn_A : IsUnit (n : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact hn_unit)
  have : NeZero (n : Ω) := ⟨hn_A.natCast_ne_zero_of_algebra⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap A Ω π) n
  have : IsScalarTower A K L⟮α⟯ := .to₁₂₄ A K L L⟮α⟯
  let β : L⟮α⟯ := AdjoinSimple.gen L α
  have hβ : β ^ n = algebraMap A L⟮α⟯ π :=
    (AdjoinSimple.gen_pow_eq_algebraMap_iff L).mpr hα
  exact ⟨L⟮α⟯, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, β, hβ,
    h.isUnramifiedWRT_of_pow_eq_of_irreducible hπ hdvd hβ (adjoin_adjoinSimple_gen_eq_top α)⟩

/-- **Kummer characterization of tame ramification** (Stacks, Lemma 15.116.7). Let `A` be a
discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K` be a finite
separable extension. The following are equivalent:

1. `L` is tamely ramified with respect to `A`;
2. there exist `e ≥ 1` invertible in `κ_A` and an extension `E` of `L` containing an `e`-th root
   `β` of `π` such that `integralClosure A K(β)` is a discrete valuation ring and `E / K(β)` is
   finite separable and unramified with respect to `integralClosure A K(β)`;
3. there exists `e₀ ≥ 1` invertible in `κ_A` such that for every `d` invertible in `κ_A`, clause
   (2) holds at exponent `d * e₀`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae {π : A} (hπ : Irreducible π) :
    List.TFAE
      [IsTamelyRamifiedWRT A L,
        ∃ e : ℕ, 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
          ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
            (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E),
            β ^ e = algebraMap A E π ∧
              ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
                letI := hDVR
                IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
                  FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E,
        ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
          ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
            ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
              (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E),
              β ^ (d * e₀) = algebraMap A E π ∧
                ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
                  letI := hDVR
                  IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
                    FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E] := by
  tfae_have 1 → 3 := fun h ↦ by
    obtain ⟨e₀, he₀_pos, he₀_unit, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
    refine ⟨e₀, he₀_pos, he₀_unit, fun d hd_unit ↦ ?_⟩
    exact exists_kummer_witness_of_dvd (K := K) (Ω := SeparableClosure L) h hπ
      (by rw [Nat.cast_mul]; exact hd_unit.mul he₀_unit)
      (fun P _ _ ↦ dvd_mul_of_dvd_right (hdvd P) d)
  tfae_have 3 → 2 := by
    rintro ⟨e₀, he₀_pos, he₀_unit, h3⟩
    refine ⟨e₀, he₀_pos, he₀_unit, ?_⟩
    simpa [one_mul] using h3 1 (by simp)
  tfae_have 2 → 1 := by
    rintro ⟨e, -, he_unit, E, _, _, _, _, _, _, β, hβ, hDVR, hunr, -, -⟩
    let := hDVR
    exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he_unit hβ hunr
  tfae_finish

/-- **Kummer characterization of tame ramification, existential form** (Stacks, Lemma 15.116.7,
(1) ⇔ (2)): `L` is tamely ramified with respect to `A` iff it embeds over `K` into a finite
separable extension of some tame Kummer extension `K(π ^ (1 / e))` that is unramified with respect
to the discrete valuation ring `A[π ^ (1 / e)]`. -/
@[stacks 0EXW "(1) ⇔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ e : ℕ, 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
        ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
          (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E),
          β ^ e = algebraMap A E π ∧
            ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
              letI := hDVR
              IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
                FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E :=
  (isTamelyRamifiedWRT_tfae (K := K) (L := L) hπ).out 1 2

/-- **Kummer characterization of tame ramification, universal-multiple form** (Stacks, Lemma
15.116.7, (1) ⇔ (3)): `L` is tamely ramified with respect to `A` iff there exists `e₀ ≥ 1`
invertible in `κ_A` admitting an unramified Kummer witness at every tame multiple `d * e₀`. -/
@[stacks 0EXW "(1) ⇔ (3)"]
theorem isTamelyRamifiedWRT_iff_exists_forall_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
        ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
          ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
            (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E),
            β ^ (d * e₀) = algebraMap A E π ∧
              ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
                letI := hDVR
                IsUnramifiedWRT (integralClosure A K⟮β⟯) E ∧
                  FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E :=
  (isTamelyRamifiedWRT_tfae (K := K) (L := L) hπ).out 1 3

/-- Inside a separably closed ambient extension `Ω` of `L`, `L` is tamely ramified with respect to
`A` iff there exist `e ≥ 1` invertible in `κ_A` and an `e`-th root `α ∈ Ω` of `π` such that
`integralClosure A K(α)` is a discrete valuation ring and `L(α)` is finite, separable, and
unramified over `K(α)` with respect to `integralClosure A K(α)`. -/
theorem isTamelyRamifiedWRT_iff_exists_adjoin_root {Ω : Type*} [Field Ω] [IsSepClosed Ω]
    [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω] [IsScalarTower A K Ω]
    {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (α : Ω), 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
        α ^ e = algebraMap A Ω π ∧
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ ∧
            FiniteDimensional K⟮α⟯ L⟮α⟯ ∧ Algebra.IsSeparable K⟮α⟯ L⟮α⟯ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e₀, he₀_pos, he₀_unit, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
    have he₀_A : IsUnit (e₀ : A) :=
      (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact he₀_unit)
    have : NeZero (e₀ : Ω) := ⟨he₀_A.natCast_ne_zero_of_algebra⟩
    obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap A Ω π) e₀
    exact ⟨e₀, α, he₀_pos, he₀_unit, hα,
      h.isUnramifiedWRT_adjoin_of_pow_eq_of_irreducible hπ hdvd hα⟩
  · rintro ⟨e, α, -, he_unit, hα, hDVR, hunr, -, -⟩
    let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    let := hDVR
    have : IsScalarTower A L Ω := .to₁₃₄ A K L Ω
    have : IsScalarTower A K L⟮α⟯ := .to₁₂₄ A K L L⟮α⟯
    have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
      IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
    have hK₁ : IsTamelyRamifiedWRT A K⟮α⟯ :=
      (TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_iff_of_pow_eq_of_irreducible
        hπ hα).mpr he_unit
    exact (hK₁.trans hunr.isTamelyRamifiedWRT).tower_bot K

end KummerCharacterization

end TauCeti.Algebra
