/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.ValuationRing
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.LocalRing.Localization
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.Unramified

/-!
# Tamely ramified extensions become unramified over a Kummer extension

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension, tamely ramified with respect to `A`. Let `n` be nonzero in `K` and
divisible by every ramification index of the integral closure of `A` in `L`, and let `α` be an
`n`-th root of `π` in an extension `Ω` of `L`. Then `L(α)` is unramified with respect to the
integral closure `A₁ = A[α]` of `A` in the Kummer extension `K(α)`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`). This is Abhyankar's lemma
for discrete valuation rings (SGA 1, Exposé X, Lemme 3.6; Stacks, Lemma 15.116.4) for the Kummer
extensions `K(π ^ (1 / n))`, stated for the field extension rather than for one maximal ideal.

The proof checks unramifiedness at each maximal ideal `P` of the integral closure `C` of `A` in
`L(α)`. Below `P` lies a maximal ideal `m` of the integral closure `B₀` of `A` in `L`, whose
localization `B` is a discrete valuation ring in which `π = u ϖ ^ e`, with `e` the ramification
index of `m`; thus `e` divides `n`, and `e` is invertible in `B` by tameness. The local ring
`C_P` is a valuation ring over `B`, and each of its elements is a polynomial in `α` over `B`
divided by a nonzero element of `B`. So `C_P` is a quotient of a local ring of the Abhyankar
model, and it is formally unramified over `A[α]` (`TauCeti.formallyUnramified_of_valuationRing`).

Taking for `n` a multiple of the product of the ramification indices gives the implications
(1) ⇒ (2) and (1) ⇒ (3) of Stacks, Lemma 15.116.7. Conversely `K(α)` is tamely ramified with
respect to `A` when `n` is invertible in the residue field, so a subfield of an extension of `K(α)`
unramified with respect to `A[α]` is tamely ramified. Together these characterize tamely ramified
extensions by unramified Kummer witnesses (`TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`).

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`: a tamely ramified extension
  becomes unramified after adjoining an `n`-th root of a uniformizer, for every `n` nonzero in
  `K` and divisible by all ramification indices, even when `n` is divisible by the residue
  characteristic.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.exists_forall_isUnramifiedWRT_adjoin_root`: there is an
  invertible `e₀` such that this holds for every exponent `d e₀` with `d` invertible.
* `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: in an algebraically closed field `Ω`,
  `L` is tamely ramified iff some invertible exponent gives an unramified extension `L(α)`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

open Polynomial IsLocalRing
open _root_.IntermediateField

namespace TauCeti.Algebra

section Local

variable {A A₁ B₀ C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing A₁] [Algebra A A₁]
  [CommRing B₀] [IsDedekindDomain B₀] [Algebra A B₀] [Module.Finite A B₀] [FaithfulSMul A B₀]
  [CommRing C] [IsDedekindDomain C] [Algebra A C] [Algebra A₁ C] [Algebra B₀ C]
  [IsScalarTower A A₁ C] [IsScalarTower A B₀ C] [FaithfulSMul B₀ C]

/-- Let `C` be a Dedekind domain over the Dedekind domain `B₀`, finite over the discrete valuation
ring `A`, and over a ring `A₁` receiving the Kummer ring `A[T]/(T ^ n − π)`, with `n ≠ 0`.
Suppose that `B₀` is tamely ramified over `A` at its maximal ideals, that their ramification
indices divide `n`, and that the elements of `C` and their inverses lie in
`B₀[τ]` up to nonzero elements of `B₀`, where `τ` is the image of `T`. Then the localization of
`C` at every maximal ideal over the closed point of `A` is formally unramified over `A₁`. -/
private theorem formallyUnramified_localization_atPrime {π : A} (hπ : Irreducible π) {n : ℕ}
    (hn : n ≠ 0) (g : standardTameCover A π n →ₐ[A] A₁)
    (htame : ∀ (m : Ideal B₀) [m.IsMaximal] [m.LiesOver (maximalIdeal A)],
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (B₀ ⧸ m) ∧
        IsUnit ((m.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A))
    (hdvd : ∀ (m : Ideal B₀) [m.IsMaximal], m.ramificationIdx A ∣ n)
    (hgen₁ : ∀ c : C, ∃ r : B₀, r ≠ 0 ∧
      algebraMap B₀ C r * c ∈ Algebra.adjoin B₀ {algebraMap A₁ C (g (AdjoinRoot.root _))})
    (hgen₂ : ∀ c : C, c ≠ 0 → ∃ r : B₀, r ≠ 0 ∧
      ∃ q ∈ Algebra.adjoin B₀ {algebraMap A₁ C (g (AdjoinRoot.root _))},
        q * c = algebraMap B₀ C r)
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.FormallyUnramified A₁ (Localization.AtPrime P) := by
  set τ := algebraMap A₁ C (g (AdjoinRoot.root _))
  have : FaithfulSMul A C := .trans A B₀ C
  have hπ0 : algebraMap A C π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A C)).mpr hπ.ne_zero
  have hπP : algebraMap A C π ∈ P := by
    rw [← Ideal.mem_comap, ← Ideal.under_def, ← P.over_def (maximalIdeal A)]
    exact hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  -- The prime `m` of `B₀` below `P`, and the discrete valuation rings `B = (B₀)_m`, `S = C_P`.
  let m := P.under B₀
  have : m.LiesOver (maximalIdeal A) := ⟨by rw [Ideal.under_under, ← P.over_def (maximalIdeal A)]⟩
  have hm0 : m ≠ ⊥ := by
    refine fun h ↦ hπ0 ?_
    have : algebraMap A B₀ π ∈ m := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hπP
    rw [h, Ideal.mem_bot] at this
    rw [IsScalarTower.algebraMap_apply A B₀ C, this, map_zero]
  have : m.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hm0
  have hP0 : P ≠ ⊥ := fun h ↦ hπ0 (by rwa [h, Ideal.mem_bot] at hπP)
  let B := Localization.AtPrime m
  let S := Localization.AtPrime P
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B₀ hm0 B
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP0 S
  -- `B → S` is the induced local map of localizations; it is injective.
  let := (Localization.localRingHom m P (algebraMap B₀ C) rfl).toAlgebra
  have : IsLocalHom (algebraMap B S) := Localization.isLocalHom_localRingHom m P _ rfl
  have hBS (r : B₀) : algebraMap B S (algebraMap B₀ B r) = algebraMap C S (algebraMap B₀ C r) :=
    Localization.localRingHom_to_map m P _ rfl r
  have hinjB := IsLocalization.injective B m.primeCompl_le_nonZeroDivisors
  have : FaithfulSMul B S := (faithfulSMul_iff_algebraMap_injective B S).mpr
    (localRingHom_injective m P rfl (FaithfulSMul.algebraMap_injective B₀ C))
  have : IsScalarTower A B S := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B₀ B, hBS, ← IsScalarTower.algebraMap_apply A B₀ C,
      ← IsScalarTower.algebraMap_apply A C S]
  have : IsScalarTower B₀ B S := .of_algebraMap_eq fun r ↦ by
    rw [hBS, ← IsScalarTower.algebraMap_apply]
  have : IsLocalHom (algebraMap A B) := by
    apply ((local_hom_tfae _).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A B₀ B, ← Ideal.comap_comap, ← Ideal.under_def B₀,
      IsLocalization.AtPrime.under_maximalIdeal B m, ← Ideal.under_def,
      ← Ideal.over_def m (maximalIdeal A)]
  have := isSeparable_residueField_localization m (htame m).1
  -- Write `π = w ϖ ^ k` in `B`; the exponent `k` is the ramification index of `m`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπB0 : algebraMap A B π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B₀ B, ne_eq, map_eq_zero_iff _ hinjB]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B₀)).mpr hπ.ne_zero
  obtain ⟨k, w, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπB0 hϖ
  have hkm : m.ramificationIdx A = k := by
    refine Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) m k ?_
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hk, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit w.isUnit]
  obtain ⟨d, rfl⟩ : k ∣ n := hkm ▸ hdvd m
  have hd : d ≠ 0 := right_ne_zero_of_mul hn
  have he : IsUnit (k : B) := by
    have hkA := (isUnit_map_iff (IsLocalRing.residue A) (k : A)).mp
      (by rw [map_natCast, ← hkm]; exact (htame m).2)
    simpa using hkA.map (algebraMap A B)
  -- Elements of `B₀[τ]` map into `B[t]`, where `t` is the image of `τ` in `S`.
  let f : standardTameCover A π (k * d) →ₐ[A] S := (IsScalarTower.toAlgHom A A₁ S).comp g
  have hft : f (AdjoinRoot.root _) = algebraMap C S τ := IsScalarTower.algebraMap_apply A₁ C S _
  have hmap {q : C} (hq : q ∈ Algebra.adjoin B₀ {τ}) :
      algebraMap C S q ∈ Algebra.adjoin B {f (AdjoinRoot.root _)} := by
    have hq' : algebraMap C S q ∈ (Algebra.adjoin B₀ {τ}).map (IsScalarTower.toAlgHom B₀ C S) :=
      Subalgebra.mem_map.mpr ⟨q, hq, rfl⟩
    rw [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', ← hft] at hq'
    exact Algebra.adjoin_le (S := (Algebra.adjoin B {f (AdjoinRoot.root _)}).restrictScalars B₀)
      (Set.singleton_subset_iff.mpr (Algebra.subset_adjoin rfl)) hq'
  -- Every element `c / s` of `S` lies in `B[t]` after multiplication by a nonzero element.
  have hgen (z : S) : ∃ b : B, b ≠ 0 ∧
      algebraMap B S b * z ∈ Algebra.adjoin B {f (AdjoinRoot.root _)} := by
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    have hs0 : (s : C) ≠ 0 := fun h ↦ s.2 (h ▸ P.zero_mem)
    obtain ⟨r₁, hr₁, hq₁⟩ := hgen₁ c
    obtain ⟨r₂, hr₂, q₂, hq₂, hq₂s⟩ := hgen₂ s hs0
    refine ⟨algebraMap B₀ B (r₁ * r₂), (map_ne_zero_iff _ hinjB).mpr (mul_ne_zero hr₁ hr₂), ?_⟩
    have key : algebraMap B S (algebraMap B₀ B (r₁ * r₂)) * IsLocalization.mk' S c s =
        algebraMap C S (algebraMap B₀ C r₁ * c) * algebraMap C S q₂ := by
      rw [hBS, map_mul, ← hq₂s, map_mul, map_mul, map_mul, mul_assoc, mul_assoc,
        IsLocalization.mk'_spec']
      ring
    rw [key]
    exact mul_mem (hmap hq₁) (hmap hq₂)
  have hf := formallyUnramified_of_valuationRing hπ hϖ w.isUnit he hd hk f hgen
  exact RingHom.formallyUnramified_algebraMap.mp (RingHom.FormallyUnramified.of_comp hf)

end Local

section FieldSetup

variable {A K L Ω : Type*} [CommRing A] [Field K] [Algebra A K] [Field L] [Algebra A L]
  [Algebra K L] [IsScalarTower A K L] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω]
  [IsScalarTower K L Ω] [IsScalarTower A K Ω]

variable (K) in
include K in
/-- The tower `A → L → Ω` induced by `A → K → L → Ω`. -/
private theorem isScalarTower_left : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
  simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply K L Ω]

omit [IsScalarTower A K Ω] in
/-- The tower `A → K → L(α)`. -/
private theorem isScalarTower_adjoin [IsScalarTower A L Ω] (α : Ω) : IsScalarTower A K L⟮α⟯ :=
  .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]

/-- The tower `A → K(α) → L(α)`, for the canonical inclusion `K(α) → L(α)`. -/
private theorem isScalarTower_adjoinBaseChange [IsScalarTower A L Ω] (α : Ω) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    IsScalarTower A K⟮α⟯ L⟮α⟯ :=
  letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  haveI := isScalarTower_adjoin (A := A) (K := K) (L := L) α
  .of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)

/-- An `n`-th root `α` of `π` in `Ω` gives the `n`-th root `AdjoinSimple.gen K α` of `π` in
`K(α)`. -/
private theorem adjoinSimple_gen_pow {π : A} {n : ℕ} {α : Ω} (hα : α ^ n = algebraMap A Ω π) :
    AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
  Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
    IsScalarTower.algebraMap_apply A K Ω] using hα)

end FieldSetup

section Field

variable {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
  [IsScalarTower A K Ω]

attribute [local instance] integralClosureMapAlgebra isScalarTower_integralClosureMapAlgebra_left
  isScalarTower_integralClosureMapAlgebra_right

/-- **Abhyankar's lemma for Kummer extensions of a discrete valuation ring.** Let `L` be a finite
separable extension of the fraction field `K` of a discrete valuation ring `A`, tamely ramified
with respect to `A`. Let `α` be an `n`-th root of a uniformizer `π` of `A`, where `n` is nonzero in
`K` and divisible by the ramification index of every maximal ideal of the integral closure of `A`
in `L`; `n` need not be invertible in the residue field. Then the integral closure of `A` in
`K(α)` is a discrete valuation ring, and `L(α)` is unramified with respect to it. The algebra
structure on `L(α)` is induced by the canonical inclusion `K(α) → L(α)`. -/
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root (h : IsTamelyRamifiedWRT A L) {π : A}
    (hπ : Irreducible π) {n : ℕ} (hn : (n : K) ≠ 0)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n)
    {α : Ω} (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : IsScalarTower A L Ω := isScalarTower_left K
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  -- The base: `K₁ = K(α)` is a Kummer extension, and `A₁ = A[α]` is a discrete valuation ring.
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π := adjoinSimple_gen_pow hα
  have hgen : K⟮AdjoinSimple.gen K α⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  have := IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
    hπ hαK hgen
  have hdegree := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hαK hgen
  have : FiniteDimensional K K⟮α⟯ :=
    Module.finite_of_finrank_pos (hdegree ▸ Nat.pos_of_ne_zero hn0)
  have : IsFractionRing (integralClosure A K⟮α⟯) K⟮α⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α⟯ _
  have : IsScalarTower A K L⟮α⟯ := isScalarTower_adjoin α
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ := isScalarTower_adjoinBaseChange α
  refine ⟨inferInstance, ?_⟩
  -- `E = L(α)` is finite separable over `K`: `α` is a root of the separable `X ^ n − π`.
  have hαint : IsIntegral A α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hα ▸ isIntegral_algebraMap)
  have : FaithfulSMul A L := .trans A K L
  have hsepα : IsSeparable L α := by
    refine (separable_X_pow_sub_C (algebraMap A L π)
      (by simpa using (algebraMap K L).injective.ne hn)
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A L)).mpr hπ.ne_zero)).of_dvd
      (minpoly.dvd L α ?_)
    simp [hα, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable L L⟮α⟯ := (isSeparable_adjoin_simple_iff_isSeparable L Ω).mpr hsepα
  have : FiniteDimensional L L⟮α⟯ := adjoin.finiteDimensional hαint.tower_top
  have : FiniteDimensional K L⟮α⟯ := .trans K L L⟮α⟯
  have : Algebra.IsSeparable K L⟮α⟯ := .trans K L L⟮α⟯
  -- The normalizations `B₀` of `A` in `L`, and `C` of `A` (equivalently of `A₁`) in `E`.
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : IsDedekindDomain (integralClosure A L⟮α⟯) := integralClosure.isDedekindDomain A K L⟮α⟯
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite A (integralClosure A L⟮α⟯) := IsIntegralClosure.finite A K L⟮α⟯ _
  have : IsIntegralClosure (integralClosure A L⟮α⟯) (integralClosure A K⟮α⟯) L⟮α⟯ :=
    IsIntegralClosure.tower_top (R := A)
  have : Module.Finite (integralClosure A K⟮α⟯) (integralClosure A L⟮α⟯) :=
    .of_restrictScalars_finite A _ _
  have : FaithfulSMul A (integralClosure A L) := .tower_bot A _ L
  have : FaithfulSMul (integralClosure A L) (integralClosure A L⟮α⟯) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y hxy ↦
      Subtype.ext ((algebraMap L L⟮α⟯).injective (congrArg Subtype.val hxy))
  -- The Kummer ring maps to `A₁` by sending its root to the generator `α`.
  let αA₁ : integralClosure A K⟮α⟯ :=
    ⟨AdjoinSimple.gen K α, IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hαK ▸ isIntegral_algebraMap)⟩
  let g : standardTameCover A π n →ₐ[A] integralClosure A K⟮α⟯ :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) αA₁ (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      exact Subtype.ext hαK)
  have hgα : ((algebraMap (integralClosure A K⟮α⟯) (integralClosure A L⟮α⟯)
      (g (AdjoinRoot.root _)) : L⟮α⟯)) = AdjoinSimple.gen L α := by
    simp [g, αA₁, RingHom.algebraMap_toAlgebra]
  set τ := algebraMap (integralClosure A K⟮α⟯) (integralClosure A L⟮α⟯) (g (AdjoinRoot.root _))
  -- Every element of `E = L[α]` lies in `B₀[α]` after multiplication by a nonzero element of `B₀`.
  have hF (w : L⟮α⟯) : ∃ r : integralClosure A L, r ≠ 0 ∧
      ∃ q ∈ Algebra.adjoin (integralClosure A L) {τ},
        (q : L⟮α⟯) = algebraMap L L⟮α⟯ r * w := by
    have : IsFractionRing (integralClosure A L) L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L _
    obtain ⟨p, rfl⟩ := (adjoin.powerBasis hαint.tower_top).exists_eq_aeval' w
    obtain ⟨b, hb, hbp⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors (integralClosure A L)) p
    set q₀ := IsLocalization.integerNormalization (nonZeroDivisors (integralClosure A L)) p
    refine ⟨b, nonZeroDivisors.ne_zero hb, aeval τ q₀, aeval_mem_adjoin_singleton _ _, ?_⟩
    have h1 : ((aeval τ q₀ : integralClosure A L⟮α⟯) : L⟮α⟯) = aeval (τ : L⟮α⟯) q₀ :=
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom (integralClosure A L)
        (integralClosure A L⟮α⟯) L⟮α⟯) τ _).symm
    rw [h1, hgα, adjoin.powerBasis_gen, ← Polynomial.aeval_map_algebraMap L, hbp,
      AlgHom.map_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (integralClosure A L) L L⟮α⟯, Subalgebra.algebraMap_apply]
  -- At each maximal ideal of `C`, the localization is formally unramified over `A₁`.
  rw [isUnramifiedWRT_iff_of_isIntegralClosure (integralClosure A L⟮α⟯)]
  intro P _ _
  have : (maximalIdeal (integralClosure A K⟮α⟯)).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : P.LiesOver (maximalIdeal A) := .trans P (maximalIdeal (integralClosure A K⟮α⟯)) _
  refine (Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_quotient
    (maximalIdeal _) P).mp ?_
  refine formallyUnramified_localization_atPrime (B₀ := integralClosure A L) hπ hn0 g
    (isTamelyRamifiedWRT_def.mp h) (fun m _ ↦ hdvd m) (fun c ↦ ?_) (fun c hc ↦ ?_) P
  · obtain ⟨r, hr, q, hq, hqc⟩ := hF c
    refine ⟨r, hr, ?_⟩
    convert hq using 1
    exact Subtype.ext (by simp [hqc])
  · have hc' : (c : L⟮α⟯) ≠ 0 := fun h ↦ hc (Subtype.ext h)
    obtain ⟨r, hr, q, hq, hqc⟩ := hF (c : L⟮α⟯)⁻¹
    exact ⟨r, hr, q, hq, Subtype.ext (by simp [hqc, hc'])⟩

/-- **Tame extensions have an unramified Kummer witness at every invertible multiple.** If `L` is
tamely ramified with respect to `A`, there is `e₀`, invertible in the residue field, such that for
every `d` invertible in the residue field and every `(d e₀)`-th root `α` of a uniformizer `π`,
`L(α)` is unramified with respect to the integral closure of `A` in `K(α)`. -/
@[stacks 0EXW "(1) ⇒ (3)"]
theorem IsTamelyRamifiedWRT.exists_forall_isUnramifiedWRT_adjoin_root
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) :
    ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧ ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
      ∀ α : Ω, α ^ (d * e₀) = algebraMap A Ω π →
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  obtain ⟨e₀, he₀, hdvd⟩ := h.exists_isUnit_forall_ramificationIdx_dvd (K := K)
  refine ⟨e₀, he₀, fun d hd α hα ↦ ?_⟩
  have hn : IsUnit ((d * e₀ : ℕ) : A) := (isUnit_map_iff (IsLocalRing.residue A) _).mp
    (by rw [map_natCast, Nat.cast_mul]; exact hd.mul he₀)
  exact h.isUnramifiedWRT_adjoin_root hπ
    (by simpa using ((hn.map (algebraMap A K)).ne_zero))
    (fun P _ ↦ (hdvd P).trans (dvd_mul_left e₀ d)) hα

/-- **Tame extensions are those with an unramified Kummer witness.** Let `L` be a finite separable
extension of the fraction field `K` of a discrete valuation ring `A` with uniformizer `π`, inside
an algebraically closed field `Ω`. Then `L` is tamely ramified with respect to `A` iff for some `n`
invertible in the residue field and some `n`-th root `α` of `π`, the field `L(α)` is unramified
with respect to the integral closure `A[α]` of `A` in `K(α)`. -/
@[stacks 0EXW "(1) ⇔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer [IsAlgClosed Ω] {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔ ∃ n : ℕ, IsUnit (n : A ⧸ maximalIdeal A) ∧
      ∃ α : Ω, α ^ n = algebraMap A Ω π ∧
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  constructor
  · intro h
    obtain ⟨e₀, he₀, hall⟩ := h.exists_forall_isUnramifiedWRT_adjoin_root (K := K) (Ω := Ω) hπ
    have he₀0 : e₀ ≠ 0 := by
      rintro rfl
      simp at he₀
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) (Nat.pos_of_ne_zero he₀0)
    refine ⟨e₀, he₀, α, hα, hall 1 (by simp) α ?_⟩
    rwa [one_mul]
  rintro ⟨n, hn, α, hα, hDVR, hL⟩
  -- Conversely `K(α)` is a tame Kummer extension, so `L(α)`, and hence `L`, is tame.
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have : IsScalarTower A L Ω := isScalarTower_left K
  have : IsScalarTower A K L⟮α⟯ := isScalarTower_adjoin α
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ := isScalarTower_adjoinBaseChange α
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π := adjoinSimple_gen_pow hα
  have hK₁ : IsTamelyRamifiedWRT A K⟮α⟯ :=
    (IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ hαK
      (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α)).mpr hn
  exact (hK₁.trans hL.isTamelyRamifiedWRT).tower_bot K

end Field

end TauCeti.Algebra
