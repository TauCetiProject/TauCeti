/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore
public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Discriminant boxes in the Eisenstein region

Let `K` be a nonarchimedean local field with residue cardinality `q`, and fix `n, j : ℕ`. Writing
`j = a * n + b` with `0 ≤ b < n` and `ν_h = oreCoefficientDepth K n j h`, the *discriminant box*
`TauCeti.eisensteinBox K n j` in the coefficient space `Fin n → K` is empty unless
`IsOreAdmissible K n j`, and otherwise consists of the coefficient vectors `v` such that:

* `v 0 ∈ 𝓂[K] \ 𝓂[K] ^ 2` (so `monicOfCoeff v` is Eisenstein);
* `v h ∈ 𝓂[K] ^ ν_h` for every `0 < h < n`;
* when `b > 0`, `v b ∉ 𝓂[K] ^ (ν_b + 1)` (so `v_K(v b) = ν_b = a + 1 - v_K(b)`).

By the derivative-infimum characterization in
`TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore`, a polynomial `monicOfCoeff v` in the
Eisenstein region lies in `eisensteinBox K n j` if and only if its derivative infimum is `j`.
Consequently:

* the boxes `eisensteinBox K n j` are pairwise disjoint subsets of `eisensteinSet K n`;
* every polynomial in `eisensteinBox K n j` is separable, and for `0 < n` the union
  `⋃ j, eisensteinBox K n j` is precisely the set of separable Eisenstein polynomials, hence has
  full Haar measure in `eisensteinSet K n`;
* every root `x` of `monicOfCoeff v` for `v ∈ eisensteinBox K n j` generates a member
  `K⟮x⟯ ∈ σ_K(n)` with wild exponent `j`, so for `L ∈ σ_K(n)` the root count `L.rootCount`
  vanishes on `eisensteinSet K n \ eisensteinBox K n L.wildExponent`, and on `eisensteinBox K n j`
  the root counts over `{L ∈ σ_K(n) | L.wildExponent = j}` sum to `n`;
* for any left-invariant measure normalized on the integer box, each admissible box has volume
  `q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹)` when `n ∣ j`, and
  `q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹) ^ 2` when `¬ n ∣ j`.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the discriminant box in `Fin n → K`.

## Main results

* `TauCeti.eisensteinBox_subset_eisensteinSet`: every discriminant box lies in the Eisenstein
  region.
* `TauCeti.pairwiseDisjoint_eisensteinBox`: the boxes for distinct wild exponents are disjoint.
* `TauCeti.separable_monicOfCoeff_of_mem_eisensteinBox`: every polynomial in a discriminant box is
  separable.
* `TauCeti.iUnion_eisensteinBox_eq`: for `0 < n`, the union of the discriminant boxes is the set
  of separable Eisenstein coefficient vectors.
* `TauCeti.ae_mem_iUnion_eisensteinBox`: the union of the discriminant boxes has full Haar measure
  in the Eisenstein region.
* `TauCeti.adjoin_mem_totallyRamifiedOfDegree_and_wildExponent_eq_of_mem_eisensteinBox`: roots of
  polynomials in `eisensteinBox K n j` generate members of `σ_K(n)` of wild exponent `j`.
* `TauCeti.tsum_rootCount_wildExponent_eq_of_mem_eisensteinBox`: on `eisensteinBox K n j`, the
  root counts over `{L ∈ σ_K(n) | L.wildExponent = j}` sum to `n`.
* `TauCeti.measurableSet_eisensteinBox`: every discriminant box is measurable.
* `TauCeti.measure_eisensteinBox`: the normalized volume of an admissible discriminant box.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, §6.
-/

public section
noncomputable section

open Polynomial ValuativeRel IsDiscreteValuationRing MeasureTheory TauCeti.Polynomial
open scoped IntermediateField ENNReal

namespace TauCeti

section DiscreteValuationRing

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- The discriminant box in coefficient space `Fin n → K` attached to degree `n` and wild exponent
`j`. It is empty unless `IsOreAdmissible K n j`; when `IsOreAdmissible K n j`, it consists of all
coefficient vectors `a` with `a i ∈ 𝓂[K] ^ ν_i` for every `i : Fin n` and `a i ∉ 𝓂[K] ^ (ν_i + 1)`
at `i = 0` and (when `0 < j % n`) at `i = j % n`, where `ν_i = oreCoefficientDepth K n j i`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | IsOreAdmissible K n j ∧
    (∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1)) ∧
    (∀ i : Fin n, i.1 = 0 ∨ i.1 = j % n →
      a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1)))}

/-- Membership in the discriminant box, unfolded. -/
theorem mem_eisensteinBox {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧
        (∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1)) ∧
        (∀ i : Fin n, i.1 = 0 ∨ i.1 = j % n →
          a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1))) :=
  Iff.rfl

/-- An inadmissible wild exponent gives an empty discriminant box. -/
theorem eisensteinBox_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ha ↦ h ha.1

/-- In degree `0`, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_of_not_isOreAdmissible (not_isOreAdmissible_zero j)

/-- A box of maximal-ideal powers in `Fin n → K`. -/
private abbrev idealBox (K : Type*) [Field K] [ValuativeRel K] {n : ℕ} (e : Fin n → ℕ) :
    Set (Fin n → K) :=
  Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)

/-- Every discriminant box is contained in the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n := by
  rintro a ⟨hadm, hmem, hnot⟩
  have hn := hadm.pos
  rw [eisensteinSet_eq_sdiff hn]
  refine ⟨fun i _ ↦ ?_, fun h2 ↦ ?_⟩
  · have hpow : 𝓂[K] ^ oreCoefficientDepth K n j i.1 ≤ 𝓂[K] :=
      (Ideal.pow_le_pow_right (I := 𝓂[K])
        (one_le_oreCoefficientDepth (K := K) n j i.1)).trans_eq (pow_one 𝓂[K])
    exact Set.image_mono hpow (hmem i)
  · apply hnot ⟨0, hn⟩ (Or.inl rfl)
    have h0 := h2 ⟨0, hn⟩ (Set.mem_univ _)
    simpa [Function.update_self, oreCoefficientDepth_zero] using h0

/-- For an integral element `c : 𝒪[K]`, its coercion lies in the image of `𝓂[K] ^ m` iff
`m ≤ addVal 𝒪[K] c`. -/
private theorem coe_mem_image_maximalIdeal_pow_iff {c : 𝒪[K]} {m : ℕ} :
    (c : K) ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ m) ↔ (m : ℕ∞) ≤ addVal 𝒪[K] c := by
  rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
  constructor
  · rintro ⟨d, hd, hdc⟩
    obtain rfl : d = c := Subtype.ext hdc
    exact hd
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- Exact valuation in `ℕ∞` as membership in `𝓂[K] ^ m \ 𝓂[K] ^ (m + 1)`. -/
private theorem addVal_eq_natCast_iff_mem_and_notMem {c : 𝒪[K]} {m : ℕ} :
    addVal 𝒪[K] c = (m : ℕ∞) ↔
      (c : K) ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ m) ∧
        (c : K) ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (m + 1)) := by
  rw [coe_mem_image_maximalIdeal_pow_iff, coe_mem_image_maximalIdeal_pow_iff]
  cases hv : addVal 𝒪[K] c with
  | top => simp
  | coe v =>
    rw [Nat.cast_inj, Nat.cast_le, Nat.cast_le]
    omega

omit [IsDiscreteValuationRing 𝒪[K]] in
/-- An integral polynomial mapping to `monicOfCoeff a` is monic of degree `n`. -/
private theorem monic_and_natDegree_of_map_eq_monicOfCoeff {n : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) : f.Monic ∧ f.natDegree = n :=
  ⟨(FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr (hf ▸ monic_monicOfCoeff a), by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]⟩

/-- Given an Eisenstein polynomial `f ∈ 𝒪[K][X]` mapping to `monicOfCoeff a` of positive degree `n`,
the vector `a` belongs to `eisensteinBox K n j` if and only if the derivative infimum of `f` is
`j`. -/
theorem mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq {n j : ℕ} {a : Fin n → K} {f : 𝒪[K][X]}
    (hn : 0 < n) (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) (he : f.IsEisensteinAt 𝓂[K]) :
    a ∈ eisensteinBox K n j ↔ (⨅ k : Fin n, oreDerivativeTerm K f n k) = (j : ℕ∞) := by
  have hdeg : f.natDegree = n := (monic_and_natDegree_of_map_eq_monicOfCoeff hf).2
  have hcoeff (i : Fin n) : (f.coeff i.1 : K) = a i := by
    have h := congrArg (fun p : K[X] ↦ p.coeff i.1) hf
    rwa [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_monicOfCoeff a i] at h
  have hf0 : addVal 𝒪[K] (f.coeff 0) = 1 := by
    have h1 : f.coeff 0 ∈ 𝓂[K] := he.mem (hdeg ▸ hn)
    have h2 : f.coeff 0 ∉ 𝓂[K] ^ 2 := he.notMem
    rw [← Nat.cast_one, addVal_eq_natCast_iff_mem_and_notMem]
    exact ⟨⟨f.coeff 0, by simpa using h1, rfl⟩, fun ⟨d, hd, hdc⟩ ↦ h2 (Subtype.ext hdc ▸ hd)⟩
  rw [iInf_oreDerivativeTerm_eq_iff hn fun h _ ↦ he.mem (lt_of_lt_of_eq h.isLt hdeg.symm),
    mem_eisensteinBox]
  constructor
  · rintro ⟨hadm, hmem, hnot⟩
    refine ⟨hadm, fun _ ↦ ?_, fun h _ ↦ ?_⟩
    · set ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
      rw [addVal_eq_natCast_iff_mem_and_notMem, hcoeff ib]
      exact ⟨hmem ib, hnot ib (Or.inr rfl)⟩
    · rw [← coe_mem_image_maximalIdeal_pow_iff, hcoeff h]
      exact hmem h
  · rintro ⟨hadm, hmod, hle⟩
    refine ⟨hadm, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rw [← hcoeff i, coe_mem_image_maximalIdeal_pow_iff]
      rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
      · rw [h0, oreCoefficientDepth_zero, hf0]
        rfl
      · exact hle i hpos
    · rw [← hcoeff i]
      rcases hi with h0 | hbmod
      · have h0' : (f.coeff i.1 : K) ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 2) := by
          rw [h0]
          exact ((addVal_eq_natCast_iff_mem_and_notMem (m := 1)).mp hf0).2
        simpa [h0, oreCoefficientDepth_zero] using h0'
      · rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
        · have hi0 : i.1 = 0 := hbmod.trans hb0
          have h0' : (f.coeff i.1 : K) ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ 2) := by
            rw [hi0]
            exact ((addVal_eq_natCast_iff_mem_and_notMem (m := 1)).mp hf0).2
          simpa [hi0, oreCoefficientDepth_zero] using h0'
        · rw [hbmod]
          exact (addVal_eq_natCast_iff_mem_and_notMem.mp (hmod hbpos)).2

/-- Distinct wild exponents give disjoint discriminant boxes. -/
theorem pairwiseDisjoint_eisensteinBox (n : ℕ) :
    Pairwise (Function.onFun Disjoint (eisensteinBox K n)) := by
  intro j₁ j₂ hne
  refine Set.disjoint_left.2 fun a ha₁ ha₂ ↦ hne ?_
  have hn := ha₁.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet n j₁ ha₁)
  have h₁ := (mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he).mp ha₁
  have h₂ := (mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he).mp ha₂
  exact_mod_cast h₁.symm.trans h₂

/-- Every polynomial in a discriminant box is separable. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have hn := ha.1.pos
  have haE := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp haE
  obtain ⟨hmonic, hdeg⟩ := monic_and_natDegree_of_map_eq_monicOfCoeff hf
  have hiInf := (mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he).mp ha
  have hderiv : derivative (monicOfCoeff a) ≠ 0 := by
    rw [← hf]
    exact (derivative_map_ne_zero_iff_iInf_oreDerivativeTerm_ne_top hmonic hdeg hn).2
      (hiInf.symm ▸ ENat.natCast_ne_top j)
  exact (Polynomial.separable_iff_derivative_ne_zero
    (irreducible_monicOfCoeff_of_mem_eisensteinSet hn haE)).2 hderiv

/-- For positive degree, the union of the discriminant boxes is precisely the set of separable
Eisenstein coefficient vectors. -/
theorem iUnion_eisensteinBox_eq {n : ℕ} (hn : 0 < n) :
    (⋃ j, eisensteinBox K n j) = {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨eisensteinBox_subset_eisensteinSet n j hj,
      separable_monicOfCoeff_of_mem_eisensteinBox hj⟩
  · rintro ⟨haE, hsep⟩
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp haE
    obtain ⟨hmonic, hdeg⟩ := monic_and_natDegree_of_map_eq_monicOfCoeff hf
    have hderiv : derivative (f.map (algebraMap 𝒪[K] K)) ≠ 0 := by
      rw [hf]
      exact (Polynomial.separable_iff_derivative_ne_zero
        (irreducible_monicOfCoeff_of_mem_eisensteinSet hn haE)).1 hsep
    have hne := (derivative_map_ne_zero_iff_iInf_oreDerivativeTerm_ne_top hmonic hdeg hn).1 hderiv
    cases hv : (⨅ k : Fin n, oreDerivativeTerm K f n k) with
    | top => exact absurd hv hne
    | coe j =>
      exact ⟨j, (mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he).2 hv⟩

/-- When `n ∣ j`, an admissible discriminant box is the difference of two ideal boxes. -/
private theorem eisensteinBox_eq_sdiff_of_dvd {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : j % n = 0) :
    let e : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    eisensteinBox K n j = idealBox K e \ idealBox K (Function.update e i₀ (e i₀ + 1)) := by
  intro e i₀
  ext a
  simp only [mem_eisensteinBox, Set.mem_sdiff, idealBox, Set.mem_univ_pi, hadm, true_and]
  refine and_congr_right fun hmem ↦ ⟨fun hnot hup ↦ ?_, fun hnot i hi hai ↦ hnot fun k ↦ ?_⟩
  · have h0 := hup i₀
    rw [Function.update_self] at h0
    exact hnot i₀ (Or.inl rfl) h0
  · have hi0 : i = i₀ := Fin.ext (hi.elim id fun h ↦ h.trans hb)
    subst hi0
    rcases eq_or_ne k i₀ with rfl | hne
    · simpa [Function.update_self] using hai
    · simpa [Function.update_of_ne hne] using hmem k

/-- When `0 < j % n`, an admissible discriminant box is the difference of two single-coordinate
box differences, with the second contained in the first. -/
private theorem eisensteinBox_eq_sdiff_of_mod_pos {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    let e : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    let ib : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    let eb : Fin n → ℕ := Function.update e ib (e ib + 1)
    eisensteinBox K n j =
      (idealBox K e \ idealBox K (Function.update e i₀ (e i₀ + 1))) \
        (idealBox K eb \ idealBox K (Function.update eb i₀ (eb i₀ + 1))) := by
  intro e i₀ ib eb
  have hne : ib ≠ i₀ := fun h ↦ hb.ne' (congrArg Fin.val h)
  have heb0 : eb i₀ = e i₀ := Function.update_of_ne hne.symm ..
  ext a
  simp only [mem_eisensteinBox, Set.mem_sdiff, idealBox, Set.mem_univ_pi, hadm, true_and]
  constructor
  · rintro ⟨hmem, hnot⟩
    refine ⟨⟨hmem, fun h0 ↦ hnot i₀ (Or.inl rfl) (by simpa [Function.update_self] using h0 i₀)⟩,
      fun ⟨hbmem, _⟩ ↦ hnot ib (Or.inr rfl) (by simpa [eb, Function.update_self] using hbmem ib)⟩
  · rintro ⟨⟨hmem, hnot0⟩, hnotb⟩
    refine ⟨hmem, fun i hi hai ↦ ?_⟩
    rcases hi with hi0 | hib
    · apply hnot0
      intro k
      rcases eq_or_ne k i₀ with rfl | hk
      · rw [Function.update_self]
        have heq : i = i₀ := Fin.ext hi0
        exact heq ▸ hai
      · rw [Function.update_of_ne hk]
        exact hmem k
    · apply hnotb
      refine ⟨fun k ↦ ?_, fun h0b ↦ hnot0 fun k ↦ ?_⟩
      · rcases eq_or_ne k ib with rfl | hk
        · dsimp only [eb]
          rw [Function.update_self]
          have heq : i = ib := Fin.ext hib
          exact heq ▸ hai
        · dsimp only [eb]
          rw [Function.update_of_ne hk]
          exact hmem k
      · rcases eq_or_ne k i₀ with rfl | hk
        · rw [Function.update_self]
          simpa [Function.update_self, heb0] using h0b i₀
        · rw [Function.update_of_ne hk]
          exact hmem k

end DiscreteValuationRing

/-! ### Local-field root counts, measurability, and normalized volumes -/

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every root in `SeparableClosure K` of a polynomial in `eisensteinBox K n j` generates a member
of `σ_K(n)` with wild exponent `j`. -/
theorem adjoin_mem_totallyRamifiedOfDegree_and_wildExponent_eq_of_mem_eisensteinBox
    {n j : ℕ} {a : Fin n → K} (ha : a ∈ eisensteinBox K n j)
    {x : SeparableClosure K} (hx : aeval x (monicOfCoeff a) = 0) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n ∧ (K⟮x⟯).wildExponent = j := by
  have hn := ha.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
    (eisensteinBox_subset_eisensteinSet n j ha)
  obtain ⟨hmonic, hdeg⟩ := monic_and_natDegree_of_map_eq_monicOfCoeff hf
  have hxf : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf.symm ▸ hx
  refine ⟨adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hxf, ?_⟩
  rw [← Nat.cast_inj (R := ℕ∞),
    natCast_wildExponent_adjoin_eq_iInf_of_eisenstein hmonic he hdeg hn hxf,
    (mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he).mp ha]

/-- If `L ∈ σ_K(n)` has at least one root of an Eisenstein polynomial `monicOfCoeff a`, then `a`
lies in `eisensteinBox K n L.wildExponent`. -/
theorem mem_eisensteinBox_of_rootCount_ne_zero {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) (hrc : L.rootCount a ≠ 0) :
    a ∈ eisensteinBox K n L.wildExponent := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ by simp [h, totallyRamifiedOfDegree_zero] at hL
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  obtain ⟨hmonic, hdeg⟩ := monic_and_natDegree_of_map_eq_monicOfCoeff hf
  have hne : ((monicOfCoeff a).aroots L).card ≠ 0 := by rwa [IntermediateField.rootCount_def] at hrc
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hne)
  have hyroot : aeval (y : SeparableClosure K) (monicOfCoeff a) = 0 := by
    have hLroot : aeval y (monicOfCoeff a) = 0 := (mem_aroots.mp hy).2
    simpa [aeval_algHom_apply] using congrArg L.val hLroot
  have hxf : aeval (y : SeparableClosure K) (f.map (algebraMap 𝒪[K] K)) = 0 := hf.symm ▸ hyroot
  have hgen : K⟮(y : SeparableClosure K)⟯ = L := by
    have hle : K⟮(y : SeparableClosure K)⟯ ≤ L := IntermediateField.adjoin_simple_le_iff.mpr y.2
    have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hxf
    have := (mem_totallyRamifiedOfDegree_iff.mp hL).2.finite
    have hrank : Module.finrank K K⟮(y : SeparableClosure K)⟯ = Module.finrank K L :=
      (mem_totallyRamifiedOfDegree_iff.mp hmem).1.trans
        (mem_totallyRamifiedOfDegree_iff.mp hL).1.symm
    exact IntermediateField.eq_of_le_of_finrank_eq hle hrank
  rw [mem_eisensteinBox_iff_iInf_oreDerivativeTerm_eq hn hf he, ← hgen]
  exact (natCast_wildExponent_adjoin_eq_iInf_of_eisenstein hmonic he hdeg hn hxf).symm

/-- For `L ∈ σ_K(n)`, `L.rootCount` vanishes on
`eisensteinSet K n \ eisensteinBox K n L.wildExponent`. -/
theorem rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) (hnot : a ∉ eisensteinBox K n L.wildExponent) :
    L.rootCount a = 0 :=
  by_contra fun hne ↦ hnot (mem_eisensteinBox_of_rootCount_ne_zero hL ha hne)

/-- For `L ∈ σ_K(n)` with `L.wildExponent ≠ j`, `L.rootCount` vanishes on `eisensteinBox K n j`. -/
theorem rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) (hne : L.wildExponent ≠ j) :
    L.rootCount a = 0 :=
  rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL
    (eisensteinBox_subset_eisensteinSet n j ha) fun haL ↦
    Set.disjoint_left.mp (pairwiseDisjoint_eisensteinBox (K := K) n hne) haL ha

/-- On `eisensteinBox K n j`, the root counts over `{L ∈ σ_K(n) | L.wildExponent = j}` sum to
`n`. -/
theorem tsum_rootCount_wildExponent_eq_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) :
    ∑' L : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j},
      (L.1.rootCount a : ℝ≥0∞) = n := by
  have haE := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp haE
  have htot := tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)
  rw [← htot]
  let S : Set (totallyRamifiedOfDegree K n) := {L | L.1.wildExponent = j}
  have hsupp : Function.support (fun L : totallyRamifiedOfDegree K n ↦ (L.1.rootCount a : ℝ≥0∞)) ⊆
      S := by
    intro L hL
    by_contra hne
    have h0 := rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne L.2 ha hne
    exact hL (by simp [h0])
  have hsub := tsum_subtype_eq_of_support_subset hsupp
  rw [← hsub]
  let e : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} ≃ S :=
    { toFun L := ⟨⟨L.1, L.2.1⟩, L.2.2⟩
      invFun L := ⟨L.1.1, L.1.2, L.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact e.tsum_eq fun L ↦ (L.1.1.rootCount a : ℝ≥0∞)

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hadm : IsOreAdmissible K n j
  · rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
    · rw [eisensteinBox_eq_sdiff_of_dvd hadm hb0]
      exact (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    · rw [eisensteinBox_eq_sdiff_of_mod_pos hadm hbpos]
      exact ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)).diff
        ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow _))
  · rw [eisensteinBox_of_not_isOreAdmissible hadm]
    exact MeasurableSet.empty

/-- Almost every point of the Eisenstein region lies in some discriminant box. -/
theorem ae_mem_iUnion_eisensteinBox {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    ∀ᵐ a ∂μ.restrict (eisensteinSet K n), a ∈ ⋃ j, eisensteinBox K n j := by
  rw [iUnion_eisensteinBox_eq hn]
  filter_upwards [ae_restrict_mem measurableSet_eisensteinSet,
    ae_separable_monicOfCoeff_restrict_eisensteinSet hn μ] with a ha hsep
  exact ⟨ha, hsep⟩

/-- Incrementing one coordinate of a tuple `e : Fin n → ℕ` increases its sum by `1`. -/
private theorem sum_update_succ {n : ℕ} (e : Fin n → ℕ) (k : Fin n) :
    ∑ i, Function.update e k (e k + 1) i = (∑ i, e i) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ e (Finset.mem_univ k)]
  omega

/-- Volume of an ideal box with one coordinate restricted to an exact valuation shell. -/
private theorem measure_idealBox_sdiff_update {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) (e : Fin n → ℕ) (k : Fin n) :
    μ (idealBox K e \ idealBox K (Function.update e k (e k + 1))) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set e' := Function.update e k (e k + 1)
  have hsub : idealBox K e' ⊆ idealBox K e :=
    univ_pi_image_maximalIdeal_pow_subset (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩)
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e'
  rw [hμ, mul_one] at h₁ h₂
  rw [sum_update_succ e k] at h₂
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [measure_sdiff hsub (measurableSet_univ_pi_image_maximalIdeal_pow e').nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq0)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq0), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt))]

/-- **Volume of an admissible discriminant box**: for a left-invariant measure on `Fin n → K`
normalized on the integer box, an admissible discriminant box `eisensteinBox K n j` has volume
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹)` when `n ∣ j`, and
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) * (1 - q⁻¹) ^ 2` when `¬ n ∣ j`. -/
theorem measure_eisensteinBox {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ^ (if j % n = 0 then 1 else 2) := by
  have hn := hadm.pos
  set e : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
  set i₀ : Fin n := ⟨0, hn⟩
  have hsum_e : ∑ i : Fin n, e i = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
    have hrange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext h
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [Fin.sum_univ_eq_sum_range (fun h ↦ oreCoefficientDepth K n j h) n, hrange,
      Finset.sum_insert (by simp), oreCoefficientDepth_zero]
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · rw [eisensteinBox_eq_sdiff_of_dvd hadm hb0, measure_idealBox_sdiff_update μ hμ e i₀,
      hsum_e, ite_eq_left hb0, pow_one]
  · set ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
    set eb : Fin n → ℕ := Function.update e ib (e ib + 1)
    have hne : ib ≠ i₀ := fun h ↦ hbpos.ne' (congrArg Fin.val h)
    have heb0 : eb i₀ = e i₀ := Function.update_of_ne hne.symm ..
    have hsum_eb : ∑ i, eb i = (∑ i, e i) + 1 := sum_update_succ e ib
    have hsub : idealBox K eb \ idealBox K (Function.update eb i₀ (eb i₀ + 1)) ⊆
        idealBox K e \ idealBox K (Function.update e i₀ (e i₀ + 1)) := by
      rintro a ⟨hab, hnot⟩
      refine ⟨univ_pi_image_maximalIdeal_pow_subset
        (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩) hab, fun ha0 ↦ hnot fun k _ ↦ ?_⟩
      rcases eq_or_ne k i₀ with rfl | hk
      · simpa [Function.update_self, heb0] using ha0 i₀ (Set.mem_univ _)
      · simpa [Function.update_of_ne hk] using hab k (Set.mem_univ _)
    have hmeas : MeasurableSet (idealBox K eb \ idealBox K (Function.update eb i₀ (eb i₀ + 1))) :=
      (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    have hm1 := measure_idealBox_sdiff_update μ hμ e i₀
    have hm2 := measure_idealBox_sdiff_update μ hμ eb i₀
    rw [hsum_eb] at hm2
    have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
    have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    have hfin : μ (idealBox K eb \ idealBox K (Function.update eb i₀ (eb i₀ + 1))) ≠ ∞ := by
      rw [hm2]
      exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq0))
        (ENNReal.sub_ne_top ENNReal.one_ne_top)
    rw [eisensteinBox_eq_sdiff_of_mod_pos hadm hbpos,
      measure_sdiff hsub hmeas.nullMeasurableSet hfin, hm1, hm2, hsum_e,
      ite_eq_right hbpos.ne', pow_two]
    set S := 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
    have hpow0 : q ^ S ≠ 0 := pow_ne_zero _ hq0
    have hpowt : q ^ S ≠ ∞ := ENNReal.pow_ne_top hqt
    have hfac : 1 / q ^ (S + 1) * (1 - 1 / q) = 1 / q ^ S * (1 - 1 / q) * (1 / q) := by
      simp only [one_div, pow_succ]
      rw [ENNReal.mul_inv (.inl hpow0) (.inl hpowt)]
      ring
    have hfinA : 1 / q ^ S * (1 - 1 / q) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hpow0)
        (ENNReal.sub_ne_top ENNReal.one_ne_top)
    rw [hfac]
    calc 1 / q ^ S * (1 - 1 / q) - 1 / q ^ S * (1 - 1 / q) * (1 / q)
        = 1 / q ^ S * (1 - 1 / q) * 1 - 1 / q ^ S * (1 - 1 / q) * (1 / q) := by rw [mul_one]
      _ = 1 / q ^ S * (1 - 1 / q) * (1 - 1 / q) := (ENNReal.mul_sub fun _ _ ↦ hfinA).symm
      _ = 1 / q ^ S * ((1 - 1 / q) * (1 - 1 / q)) := mul_assoc ..

/-- An inadmissible discriminant box has measure zero. -/
theorem measure_eisensteinBox_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] (μ : Measure (Fin n → K)) :
    μ (eisensteinBox K n j) = 0 := by
  rw [eisensteinBox_of_not_isOreAdmissible h, measure_empty]

end LocalField

end TauCeti
