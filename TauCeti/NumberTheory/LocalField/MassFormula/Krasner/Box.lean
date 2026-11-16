/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore
import Mathlib.Data.ENat.Lattice
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The discriminant box of Eisenstein polynomials and Ore's realizability theorem

Each Ore-admissible wild exponent `j` in degree `n` carves out a *discriminant box*
`TauCeti.eisensteinBox K n j` inside the Eisenstein region `TauCeti.eisensteinSet K n` of
coefficient space `Fin n → K`: the constant term lies in `𝓂[K] \ 𝓂[K] ^ 2`, each coefficient
at index `h` (`1 ≤ h < n`) lies in `𝓂[K] ^ ν_h` where `ν_h = oreCoefficientDepth K n j h`, and
when `b = j % n > 0` the coefficient at index `b` lies strictly outside `𝓂[K] ^ (ν_b + 1)`.

The central algebraic fact is `TauCeti.iInf_addVal_derivative_eq_iff_mem_eisensteinBox`: for an
Eisenstein polynomial `f` of positive degree `n` over `𝒪[K]` with coefficient vector `a`, the
minimum valuation of the terms of its derivative in the power basis of a root equals `n - 1 + j`
precisely when `a ∈ eisensteinBox K n j`. Everything else follows directly:

* the boxes are pairwise disjoint and partition the separable Eisenstein coefficient vectors;
* a root in `SeparableClosure K` of an Eisenstein polynomial generates a member of `σ_K(n)` of
  wild exponent `j` precisely when its coefficient vector lies in `eisensteinBox K n j`;
* **Ore's realizability theorem** (`TauCeti.ore_realizability`): `σ_K(n)` has a member of wild
  exponent `j` exactly when `IsOreAdmissible K n j`, in both mixed and equal characteristic;
* for a left-invariant measure on `Fin n → K` normalized on the integer box, `eisensteinBox K n j`
  is a difference of ideal-power boxes and has volume
  `q ^ (-(1 + ∑_{1 ≤ h < n} ν_h)) * (1 - q⁻¹) * (1 - q⁻¹) ^ [j % n ≠ 0]`.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the discriminant box in `Fin n → K`.

## Main results

* `TauCeti.iInf_addVal_derivative_eq_iff_mem_eisensteinBox`: the derivative-term infimum of an
  Eisenstein polynomial equals `n - 1 + j` iff its coefficient vector lies in `eisensteinBox K n j`.
* `TauCeti.disjoint_eisensteinBox`, `TauCeti.iUnion_eisensteinBox_eq`,
  `TauCeti.separable_monicOfCoeff_of_mem_eisensteinBox`, `TauCeti.nonempty_eisensteinBox_iff`:
  disjointness, exhaustion of separable Eisenstein polynomials, separability, and nonemptiness.
* `TauCeti.mem_eisensteinBox_iff_wildExponent_eq`: roots of an Eisenstein polynomial generate
  extensions of wild exponent `j` iff its coefficient vector lies in `eisensteinBox K n j`.
* `TauCeti.ore_realizability`: Ore's realizability theorem for `totallyRamifiedOfDegree K n`.
* `TauCeti.measurableSet_eisensteinBox`, `TauCeti.measure_eisensteinBox`: measurability and exact
  Haar volume of the discriminant box.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open Polynomial MeasureTheory ValuativeRel IsDiscreteValuationRing TauCeti.Polynomial
open scoped ENNReal IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

section DiscreteValuationRing

variable [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **The discriminant box** `eisensteinBox K n j` in coefficient space `Fin n → K`: empty unless
`IsOreAdmissible K n j`, and otherwise consisting of coefficient vectors `a` with
`a i ∈ 𝓂[K] ^ ν_i` for all `i : Fin n`, `a 0 ∉ 𝓂[K] ^ 2`, and (when `0 < j % n`)
`a (j % n) ∉ 𝓂[K] ^ (ν_{j % n} + 1)`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | IsOreAdmissible K n j ∧
    (∀ i : Fin n,
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1)) ∧
    (∀ i : Fin n, i.1 = 0 ∨ i.1 = j % n →
      a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1)))}

/-- Unfolded membership in `eisensteinBox`. -/
theorem mem_eisensteinBox_iff {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧
      (∀ i : Fin n,
        a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1)) ∧
      (∀ i : Fin n, i.1 = 0 ∨ i.1 = j % n →
        a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1))) :=
  Iff.rfl

/-- An inadmissible discriminant box is empty. -/
theorem eisensteinBox_eq_empty_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ha ↦ h ha.1

/-- In degree zero, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero_left (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_eq_empty_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

/-- Every discriminant box lies inside the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n := by
  intro a ⟨hadm, hmem, hnot⟩
  have hn : 0 < n := hadm.pos
  rw [eisensteinSet_eq_sdiff hn]
  refine ⟨fun i _ ↦ ?_, fun h2 ↦ ?_⟩
  · obtain ⟨c, hc, hca⟩ := hmem i
    have hpos : oreCoefficientDepth K n j i.1 ≠ 0 :=
      (Nat.zero_lt_one.trans_le (one_le_oreCoefficientDepth n j i.1)).ne'
    exact ⟨c, Ideal.pow_le_self hpos hc, hca⟩
  · apply hnot ⟨0, hn⟩ (Or.inl rfl)
    simpa [Function.update_self] using h2 ⟨0, hn⟩ (Set.mem_univ _)

/-- For `c : 𝒪[K]`, membership of `(c : K)` in the image of `𝓂[K] ^ k` is `k ≤ v_K(c)`. -/
private theorem coe_mem_image_maximalIdeal_pow_iff {c : 𝒪[K]} {k : ℕ} :
    (c : K) ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) ↔ (k : ℕ∞) ≤ addVal 𝒪[K] c := by
  constructor
  · rintro ⟨d, hd, hdc⟩
    obtain rfl : d = c := Subtype.ext hdc
    exact TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.1 hd
  · intro h
    exact ⟨c, TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.2 h, rfl⟩

/-- Arithmetic comparison for a single term of the derivative of an Eisenstein polynomial:
for `1 ≤ h < n`, `n + j ≤ n • V + h` in `ℕ∞` iff `j / n + 1 + [h < j % n] ≤ V`. -/
private theorem natCast_add_le_nsmul_add_iff {n j h : ℕ} (hh0 : 0 < h) (hhn : h < n)
    (V : ℕ∞) :
    ((n + j : ℕ) : ℕ∞) ≤ n • V + (h : ℕ∞) ↔
      ((j / n + 1 + (if h < j % n then 1 else 0) : ℕ) : ℕ∞) ≤ V := by
  have hn : 0 < n := hh0.trans hhn
  have hdiv := Nat.div_add_mod j n
  have hmod := Nat.mod_lt j hn
  cases V with
  | top => simp [nsmul_eq_mul, hn.ne']
  | coe m =>
    rw [nsmul_eq_mul]
    norm_cast
    split_ifs with hlt <;> constructor <;> intro H
    · by_contra hlt'
      have hmul : n * m ≤ n * (j / n + 1) := Nat.mul_le_mul_left n (by omega)
      rw [mul_add_one] at hmul
      omega
    · have hmul : n * (j / n + 2) ≤ n * m := Nat.mul_le_mul_left n (by omega)
      rw [mul_add] at hmul
      omega
    · by_contra hlt'
      have hmul : n * m ≤ n * (j / n) := Nat.mul_le_mul_left n (by omega)
      omega
    · have hmul : n * (j / n + 1) ≤ n * m := Nat.mul_le_mul_left n (by omega)
      rw [mul_add_one] at hmul
      omega

/-- Forward half of `iInf_addVal_derivative_eq_iff_mem_eisensteinBox`, shifted by `+ 1`. -/
private theorem mem_eisensteinBox_of_iInf_addVal_derivative_succ_eq {n j : ℕ} (hn : 0 < n)
    {a : Fin n → K} {f : 𝒪[K][X]} (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (he : f.IsEisensteinAt 𝓂[K]) (hcoeff : ∀ i : Fin n, (f.coeff i.1 : K) = a i)
    (hiInf : (⨅ i : Fin n,
      n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + ((i.1 + 1 : ℕ) : ℕ∞)) =
        ((n + j : ℕ) : ℕ∞)) :
    a ∈ eisensteinBox K n j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let t (i : Fin n) : ℕ∞ :=
    n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + ((i.1 + 1 : ℕ) : ℕ∞)
  have hmem_one (i : Fin n) : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i.1) := by
    have h := he.mem (n := i.1) (by omega)
    rw [← pow_one 𝓂[K],
      TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at h
    simpa using h
  have hcoeff0_not : ¬ ((2 : ℕ) : ℕ∞) ≤ addVal 𝒪[K] (f.coeff 0) := by
    rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
    exact he.notMem
  have hcoeff_n : f.coeff n = 1 := by rw [← hdeg]; exact hmonic.leadingCoeff
  have ht_top : t ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ =
      n • addVal 𝒪[K] (n : 𝒪[K]) + (n : ℕ∞) := by
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp only [t, hn1, hcoeff_n, one_mul]
  have hle_all : ∀ i : Fin n, ((n + j : ℕ) : ℕ∞) ≤ t i := fun i ↦ hiInf ▸ iInf_le t i
  have hdepth (i : Fin n) :
      (oreCoefficientDepth K n j i.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i.1) := by
    rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
    · rw [hi0, oreCoefficientDepth_zero, Nat.cast_one]
      exact hmem_one ⟨0, hn⟩
    · have hle := hle_all ⟨i.1 - 1, by omega⟩
      have hi1 : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel hipos
      dsimp only [t] at hle
      rw [hi1, addVal_mul] at hle
      exact (oreCoefficientDepth_le_addVal_iff_of_one_le (hmem_one i)).2
        ((natCast_add_le_nsmul_add_iff hipos i.isLt _).1 hle)
  -- The finite infimum is attained at some index `i₀`, which determines Ore admissibility
  -- and exactness of the valuation at `j % n`.
  obtain ⟨i₀, hi₀⟩ := ENat.exists_eq_iInf t
  rw [hiInf] at hi₀
  have htop_le := hle_all ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
  rw [ht_top] at htop_le
  have hadm_and_not : IsOreAdmissible K n j ∧
      ∀ i : Fin n, i.1 = 0 ∨ i.1 = j % n →
        ¬ ((oreCoefficientDepth K n j i.1 + 1 : ℕ) : ℕ∞) ≤
            addVal 𝒪[K] (f.coeff i.1) := by
    rcases (Nat.succ_le_of_lt i₀.isLt).eq_or_lt with htop_eq | hmid_lt
    · have hi₀_eq : i₀ = ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hi₀_eq, ht_top] at hi₀
      cases hvn : addVal 𝒪[K] (n : 𝒪[K]) with
      | top =>
        rw [hvn, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 hn.ne'), top_add] at hi₀
        exact absurd hi₀ (ENat.top_ne_natCast _)
      | coe v =>
        rw [hvn, nsmul_eq_mul] at hi₀
        have hnat : n * v + n = n + j := by exact_mod_cast hi₀
        have hj : j = n * v := by omega
        refine ⟨isOreAdmissible_def.2
            ⟨hn, Or.inl ⟨by simp [hj], by rw [hj, Nat.mul_div_cancel_left v hn, hvn]⟩⟩,
          fun i hi ↦ ?_⟩
        have hmod0 : j % n = 0 := by simp [hj]
        have hi0 : i.1 = 0 := by omega
        simpa [hi0] using hcoeff0_not
    · set h : ℕ := i₀.1 + 1
      have hh0 : 0 < h := Nat.succ_pos _
      have hhn : h < n := hmid_lt
      dsimp only [t] at hi₀
      rw [addVal_mul] at hi₀
      set V : ℕ∞ := addVal 𝒪[K] (f.coeff h) + addVal 𝒪[K] (h : 𝒪[K])
      cases hV : V with
      | top =>
        rw [hV, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 hn.ne'), top_add] at hi₀
        exact absurd hi₀ (ENat.top_ne_natCast _)
      | coe m =>
        rw [hV, nsmul_eq_mul] at hi₀
        have hnat : n * m + h = n + j := by exact_mod_cast hi₀
        have hm1 : 1 ≤ m := by
          have h1 : (1 : ℕ∞) ≤ (m : ℕ∞) := hV ▸ le_add_right (hmem_one ⟨h, hhn⟩)
          exact_mod_cast h1
        have hmod : j % n = h := by
          have hmsub : n * (m - 1) + n = n * m := by rw [← mul_add_one, Nat.sub_add_cancel hm1]
          have : j = n * (m - 1) + h := by omega
          rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hhn]
        have hdiv : j / n + 1 = m := by
          have hnm : n * m = n * (j / n + 1) := by
            rw [mul_add_one]
            have := Nat.div_add_mod j n
            omega
          exact ((Nat.mul_right_inj hn.ne').1 hnm).symm
        have hvb : addVal 𝒪[K] (j % n : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) := by
          rw [hmod]
          cases hvh : addVal 𝒪[K] (h : 𝒪[K]) with
          | top => simp [V, hvh] at hV
          | coe vh =>
            cases hfc : addVal 𝒪[K] (f.coeff h) with
            | top => simp [V, hfc] at hV
            | coe fc =>
              have hfc1 : 1 ≤ fc := by
                have := hmem_one ⟨h, hhn⟩
                rw [hfc] at this
                exact_mod_cast this
              have hsum : fc + vh = m := by
                simp only [V, hfc, hvh] at hV
                exact_mod_cast hV
              exact_mod_cast (by omega : vh ≤ j / n)
        have hvn_ge : ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]) := by
          cases hvn : addVal 𝒪[K] (n : 𝒪[K]) with
          | top => exact le_top
          | coe vn =>
            rw [hvn, nsmul_eq_mul] at htop_le
            have hnat' : n + j ≤ n * vn + n := by exact_mod_cast htop_le
            have hdiv_mod := Nat.div_add_mod j n
            norm_cast
            by_contra hlt'
            have hmul : n * vn ≤ n * (j / n) := Nat.mul_le_mul_left n (by omega)
            omega
        have hadm : IsOreAdmissible K n j :=
          isOreAdmissible_def.2 ⟨hn, Or.inr ⟨hmod ▸ hh0, hvb, hvn_ge⟩⟩
        refine ⟨hadm, fun i hi ↦ ?_⟩
        rcases hi with hi0 | hib
        · simpa [hi0] using hcoeff0_not
        · have hih : i.1 = h := hib.trans hmod
          rw [hih]
          intro hge
          have hsum_eq := oreCoefficientDepth_mod_add_addVal_of_isOreAdmissible hadm (hmod ▸ hh0)
          rw [hmod] at hsum_eq
          have hle_m : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
            calc ((m + 1 : ℕ) : ℕ∞)
                = ((j / n + 1 : ℕ) : ℕ∞) + 1 := by rw [hdiv]; norm_cast
              _ = ((oreCoefficientDepth K n j h : ℕ∞) + 1) + addVal 𝒪[K] (h : 𝒪[K]) := by
                  rw [← hsum_eq]; ac_rfl
              _ ≤ addVal 𝒪[K] (f.coeff h) + addVal 𝒪[K] (h : 𝒪[K]) := by
                  gcongr; simpa only [Nat.cast_add, Nat.cast_one] using hge
              _ = (m : ℕ∞) := hV
          norm_cast at hle_m
          omega
  refine ⟨hadm_and_not.1, fun i ↦ ?_, fun i hi hbad ↦ ?_⟩
  · rw [← hcoeff i, coe_mem_image_maximalIdeal_pow_iff]
    exact hdepth i
  · rw [← hcoeff i, coe_mem_image_maximalIdeal_pow_iff] at hbad
    exact hadm_and_not.2 i hi hbad

/-- **Derivative-infimum characterization of the discriminant box.** For a polynomial `f` over
`𝒪[K]` that is Eisenstein at `𝓂[K]` and maps to `monicOfCoeff a` of positive degree `n`, the
coefficient vector `a` lies in `eisensteinBox K n j` if and only if the least valuation of the
derivative terms `n • v_K(f_{i+1} · (i + 1)) + i` equals `n - 1 + j`. -/
theorem iInf_addVal_derivative_eq_iff_mem_eisensteinBox {n j : ℕ} (hn : 0 < n) {a : Fin n → K}
    {f : 𝒪[K][X]} (he : f.IsEisensteinAt 𝓂[K])
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) :
    (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ)) =
        ((n - 1 + j : ℕ) : ℕ∞) ↔
      a ∈ eisensteinBox K n j := by
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hcoeff (i : Fin n) : (f.coeff i.1 : K) = a i := by
    have := congrArg (fun p : K[X] ↦ p.coeff i.1) hf
    simpa [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_monicOfCoeff] using this
  have hmem_one (i : Fin n) : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i.1) := by
    have h := he.mem (n := i.1) (by omega)
    rw [← pow_one 𝓂[K],
      TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at h
    simpa using h
  have hcoeff_n : f.coeff n = 1 := by rw [← hdeg]; exact hmonic.leadingCoeff
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let t (i : Fin n) : ℕ∞ :=
    n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + ((i.1 + 1 : ℕ) : ℕ∞)
  have hshift :
      ((⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ)) =
          ((n - 1 + j : ℕ) : ℕ∞)) ↔
        (⨅ i : Fin n, t i) = ((n + j : ℕ) : ℕ∞) := by
    have hadd : (⨅ i : Fin n,
        n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ)) + 1 =
        ⨅ i : Fin n, t i := by
      rw [ENat.iInf_add]
      exact iInf_congr fun i ↦ by simp only [t, add_assoc, Nat.cast_add, Nat.cast_one]
    have htarget : ((n - 1 + j : ℕ) : ℕ∞) + 1 = ((n + j : ℕ) : ℕ∞) := by
      norm_cast; omega
    refine ⟨fun h ↦ by rw [← hadd, h, htarget], fun h ↦ ?_⟩
    have h' := hadd.trans h
    rw [← htarget] at h'
    cases hval : ⨅ i : Fin n,
        n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ) with
    | top =>
      rw [hval, top_add] at h'
      exact absurd h' (by norm_cast)
    | coe d =>
      rw [hval] at h'
      norm_cast at h' ⊢
      omega
  rw [hshift]
  refine ⟨mem_eisensteinBox_of_iInf_addVal_derivative_succ_eq hn hmonic hdeg he hcoeff, ?_⟩
  rintro ⟨hadm, hmem, hnot⟩
  have hval (i : Fin n) :
      (oreCoefficientDepth K n j i.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i.1) := by
    have := hmem i
    rwa [← hcoeff i, coe_mem_image_maximalIdeal_pow_iff] at this
  have ht_top : t ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ =
      n • addVal 𝒪[K] (n : 𝒪[K]) + (n : ℕ∞) := by
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp only [t, hn1, hcoeff_n, one_mul]
  refine le_antisymm ?_ (le_iInf fun i ↦ ?_)
  · rcases (isOreAdmissible_def.1 hadm).2 with ⟨hmod, hdiv⟩ | ⟨hb, _, _⟩
    · refine iInf_le_of_le ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ ?_
      rw [ht_top, ← hdiv, nsmul_eq_mul]
      have := Nat.div_add_mod j n
      exact_mod_cast (by omega : n * (j / n) + n ≤ n + j)
    · have hblt : j % n < n := Nat.mod_lt j hn
      refine iInf_le_of_le ⟨j % n - 1, by omega⟩ ?_
      have hb1 : j % n - 1 + 1 = j % n := Nat.sub_add_cancel hb
      dsimp only [t]
      rw [hb1, addVal_mul]
      have hnot' : ¬ ((oreCoefficientDepth K n j (j % n) + 1 : ℕ) : ℕ∞) ≤
          addVal 𝒪[K] (f.coeff (j % n)) := by
        have := hnot ⟨j % n, hblt⟩ (Or.inr rfl)
        rwa [← hcoeff ⟨j % n, hblt⟩, coe_mem_image_maximalIdeal_pow_iff] at this
      have hval_b :
          addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞) := by
        have hge :
            (oreCoefficientDepth K n j (j % n) : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (j % n)) :=
          hval ⟨j % n, hblt⟩
        cases hfc : addVal 𝒪[K] (f.coeff (j % n)) with
        | top => exact absurd le_top (hfc ▸ hnot')
        | coe fc =>
          rw [hfc] at hge hnot'
          norm_cast at hge hnot' ⊢
          omega
      rw [hval_b, oreCoefficientDepth_mod_add_addVal_of_isOreAdmissible hadm hb, nsmul_eq_mul]
      have := Nat.div_add_mod j n
      exact_mod_cast (by rw [mul_add_one]; omega : n * (j / n + 1) + j % n ≤ n + j)
  · rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with htop | hmid
    · have hi_eq : i = ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ := Fin.ext (by dsimp; omega)
      rw [hi_eq, ht_top, Nat.cast_add, add_comm (n : ℕ∞)]
      exact add_le_add_left hadm.le_mul_addVal _
    · dsimp only [t]
      rw [addVal_mul]
      exact (natCast_add_le_nsmul_add_iff (Nat.succ_pos i.1) hmid _).2
        ((oreCoefficientDepth_le_addVal_iff_of_one_le (hmem_one ⟨i.1 + 1, hmid⟩)).1
          (hval ⟨i.1 + 1, hmid⟩))

/-- Distinct wild exponents give disjoint discriminant boxes. -/
theorem disjoint_eisensteinBox {n j₁ j₂ : ℕ} (h : j₁ ≠ j₂) :
    Disjoint (eisensteinBox K n j₁) (eisensteinBox K n j₂) := by
  refine Set.disjoint_left.2 fun a ha₁ ha₂ ↦ h ?_
  have hn : 0 < n := ha₁.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1
    (eisensteinBox_subset_eisensteinSet n j₁ ha₁)
  have h1 := (iInf_addVal_derivative_eq_iff_mem_eisensteinBox hn he hf).2 ha₁
  have h2 := (iInf_addVal_derivative_eq_iff_mem_eisensteinBox hn he hf).2 ha₂
  have heq : ((n - 1 + j₁ : ℕ) : ℕ∞) = ((n - 1 + j₂ : ℕ) : ℕ∞) := h1.symm.trans h2
  norm_cast at heq
  omega

/-- Every polynomial in a discriminant box is separable, including in equal characteristic. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have hn : 0 < n := ha.1.pos
  have haE : a ∈ eisensteinSet K n := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 haE
  rw [separable_iff_derivative_ne_zero (irreducible_monicOfCoeff_of_mem_eisensteinSet hn haE)]
  intro hderiv
  have hiInf := (iInf_addVal_derivative_eq_iff_mem_eisensteinBox hn he hf).2 ha
  have hzero : ∀ i : Fin n, f.coeff (i.1 + 1) * (i.1 + 1 : ℕ) = 0 := fun i ↦ by
    apply FaithfulSMul.algebraMap_injective 𝒪[K] K
    have hdi := congrArg (fun p : K[X] ↦ p.coeff i.1) hderiv
    rw [← hf, derivative_map, coeff_map, coeff_derivative, coeff_zero] at hdi
    simpa [map_mul, map_natCast] using hdi
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htop : (⨅ i : Fin n,
      n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ)) = ⊤ := by
    refine iInf_eq_top.2 fun i ↦ ?_
    rw [hzero i, addVal_zero, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 hn.ne'), top_add]
  rw [htop] at hiInf
  exact ENat.top_ne_natCast _ hiInf

/-- For `0 < n`, the discriminant boxes partition the separable Eisenstein coefficient vectors. -/
theorem iUnion_eisensteinBox_eq {n : ℕ} (hn : 0 < n) :
    (⋃ j : ℕ, eisensteinBox K n j) =
      {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, ha⟩
    exact ⟨eisensteinBox_subset_eisensteinSet n j ha,
      separable_monicOfCoeff_of_mem_eisensteinBox ha⟩
  · rintro ⟨haE, hsep⟩
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 haE
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
        natDegree_monicOfCoeff]
    have hderiv : derivative (monicOfCoeff a) ≠ 0 :=
      (separable_iff_derivative_ne_zero (irreducible_monicOfCoeff_of_mem_eisensteinSet hn haE)).1
        hsep
    -- Since the derivative is nonzero, some term of the infimum is finite.
    have hex : ∃ i : Fin n, f.coeff (i.1 + 1) * (i.1 + 1 : ℕ) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hderiv
      ext k
      rw [← hf, derivative_map, coeff_map, coeff_derivative, coeff_zero]
      by_cases hk : k < n
      · have := congrArg (algebraMap 𝒪[K] K) (hall ⟨k, hk⟩)
        simpa [map_mul, map_natCast] using this
      · have hgt : f.natDegree < k + 1 := by omega
        rw [coeff_eq_zero_of_natDegree_lt hgt, zero_mul, map_zero]
    obtain ⟨i₀, hi₀⟩ := hex
    set I : ℕ∞ :=
      ⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) + (i.1 : ℕ)
    have hI_lt_top : I ≠ ⊤ := by
      have hle :
          I ≤ n • addVal 𝒪[K] (f.coeff (i₀.1 + 1) * (i₀.1 + 1 : ℕ)) + (i₀.1 : ℕ) :=
        iInf_le _ i₀
      have hfin :
          n • addVal 𝒪[K] (f.coeff (i₀.1 + 1) * (i₀.1 + 1 : ℕ)) + (i₀.1 : ℕ) ≠ ⊤ := by
        cases hv : addVal 𝒪[K] (f.coeff (i₀.1 + 1) * (i₀.1 + 1 : ℕ)) with
        | top => exact absurd (addVal_eq_top_iff.1 hv) hi₀
        | coe v =>
          rw [nsmul_eq_mul]
          exact_mod_cast ENat.natCast_ne_top (n * v + i₀.1)
      exact ne_top_of_le_ne_top hfin hle
    -- Every term is at least `n - 1`.
    have hI_ge : ((n - 1 : ℕ) : ℕ∞) ≤ I := by
      refine le_iInf fun i ↦ ?_
      rcases (Nat.succ_le_of_lt i.isLt).eq_or_lt with htop | hmid
      · have : n - 1 = i.1 := by omega
        rw [this]
        exact le_add_self
      · have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i.1 + 1)) := by
          have h := he.mem (n := i.1 + 1) (by omega)
          rw [← pow_one 𝓂[K],
            TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at h
          simpa using h
        have h1' : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) := by
          rw [addVal_mul]
          exact h1.trans le_self_add
        calc ((n - 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast Nat.sub_le n 1
          _ = n • (1 : ℕ∞) := by simp [nsmul_eq_mul]
          _ ≤ n • addVal 𝒪[K] (f.coeff (i.1 + 1) * (i.1 + 1 : ℕ)) := by
              rw [nsmul_eq_mul, nsmul_eq_mul]; gcongr
          _ ≤ _ := le_self_add
    lift I to ℕ using hI_lt_top with d hd
    have hdge : n - 1 ≤ d := by exact_mod_cast hI_ge
    refine ⟨d - (n - 1), (iInf_addVal_derivative_eq_iff_mem_eisensteinBox hn he hf).1 ?_⟩
    exact hd.symm.trans (by exact_mod_cast (by omega : d = n - 1 + (d - (n - 1))))

/-- The discriminant box `eisensteinBox K n j` is nonempty exactly when `IsOreAdmissible K n j`. -/
theorem nonempty_eisensteinBox_iff {n j : ℕ} :
    (eisensteinBox K n j).Nonempty ↔ IsOreAdmissible K n j := by
  refine ⟨fun ⟨_, ha⟩ ↦ ha.1, fun hadm ↦ ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let a : Fin n → K := fun i ↦
    if i.1 = 0 then (ϖ : K)
    else if i.1 = j % n then ((ϖ ^ oreCoefficientDepth K n j i.1 : 𝒪[K]) : K)
    else 0
  refine ⟨a, hadm, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · simp only [a]
    split_ifs with h0 hb
    · rw [h0, oreCoefficientDepth_zero, coe_mem_image_maximalIdeal_pow_iff, addVal_uniformizer hϖ,
        Nat.cast_one]
    · rw [coe_mem_image_maximalIdeal_pow_iff, hϖ.addVal_pow]
    · exact ⟨0, Ideal.zero_mem _, rfl⟩
  · simp only [a]
    rcases hi with h0 | hb
    · rw [ite_eq_left h0, h0, oreCoefficientDepth_zero, coe_mem_image_maximalIdeal_pow_iff,
        addVal_uniformizer hϖ]
      norm_cast
    · by_cases h0 : i.1 = 0
      · rw [ite_eq_left h0, h0, oreCoefficientDepth_zero, coe_mem_image_maximalIdeal_pow_iff,
          addVal_uniformizer hϖ]
        norm_cast
      · rw [ite_eq_right h0, ite_eq_left hb, coe_mem_image_maximalIdeal_pow_iff, hϖ.addVal_pow]
        norm_cast
        omega

/-- Membership in a box of ideal powers with one coordinate deepened by `1` removed. -/
private theorem mem_univ_pi_sdiff_update_iff {n : ℕ} {e : Fin n → ℕ} {k : Fin n}
    {a : Fin n → K} :
    a ∈ (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        (Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e k (e k + 1) i)) ↔
      (∀ i, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) ∧
        a k ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (e k + 1)) := by
  simp only [Set.mem_sdiff, Set.mem_univ_pi]
  refine and_congr_right fun hmem ↦
    ⟨fun hnot hk ↦ hnot fun i ↦ ?_, fun hnot hall ↦ hnot ?_⟩
  · rcases eq_or_ne i k with rfl | hne
    · simpa [Function.update_self] using hk
    · simpa [Function.update_of_ne hne] using hmem i
  · simpa [Function.update_self] using hall k

/-- Representation of an admissible discriminant box with `j % n = 0` as a difference of two
ideal-power boxes. -/
theorem eisensteinBox_eq_sdiff_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : j % n = 0) :
    let ν : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    eisensteinBox K n j =
      (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ ν i)) \
        Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update ν i₀ (ν i₀ + 1) i) := by
  intro ν i₀
  ext a
  rw [mem_eisensteinBox_iff, mem_univ_pi_sdiff_update_iff]
  simp only [hadm, true_and]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ h i₀ (Or.inl rfl), fun h i hi ↦ ?_⟩
  have hi0 : i = i₀ := Fin.ext (by dsimp [i₀]; omega)
  exact hi0 ▸ h

/-- Representation of an admissible discriminant box with `j % n ≠ 0` as a difference of two
one-coordinate shell boxes. -/
theorem eisensteinBox_eq_sdiff_of_mod_ne_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hmod : j % n ≠ 0) :
    let ν : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    let ib : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    let νb : Fin n → ℕ := Function.update ν ib (ν ib + 1)
    eisensteinBox K n j =
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ ν i)) \
        Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update ν i₀ (ν i₀ + 1) i)) \
      ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ νb i)) \
        Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update νb i₀ (νb i₀ + 1) i)) := by
  intro ν i₀ ib νb
  have hne : i₀ ≠ ib := fun h ↦ hmod (congrArg Fin.val h).symm
  have hνb0 : νb i₀ = ν i₀ := Function.update_of_ne hne _ _
  ext a
  rw [mem_eisensteinBox_iff, Set.mem_sdiff, mem_univ_pi_sdiff_update_iff,
    mem_univ_pi_sdiff_update_iff, hνb0, and_assoc]
  simp only [hadm, true_and]
  refine and_congr_right fun hmem ↦ ⟨fun h ↦ ⟨h i₀ (Or.inl rfl), fun ⟨hb, _⟩ ↦
      h ib (Or.inr rfl) (by simpa [νb, Function.update_self] using hb ib)⟩,
    fun ⟨h0, hnb⟩ i hi h2 ↦ ?_⟩
  rcases hi with hi0 | hib
  · have hi_eq : i = i₀ := Fin.ext hi0
    exact h0 (hi_eq ▸ h2)
  · have hi_eq : i = ib := Fin.ext hib
    subst hi_eq
    refine hnb ⟨fun k ↦ ?_, h0⟩
    rcases eq_or_ne k ib with rfl | hk
    · simp only [νb, Function.update_self]
      exact h2
    · simp only [νb, Function.update_of_ne hk]
      exact hmem k

end DiscreteValuationRing

section LocalField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Roots of an Eisenstein polynomial in the discriminant box.** For `a ∈ eisensteinSet K n`
(`0 < n`) and any root `x` of `monicOfCoeff a` in `SeparableClosure K`, the generated extension
`K⟮x⟯` has wild exponent `j` if and only if `a ∈ eisensteinBox K n j`. -/
theorem mem_eisensteinBox_iff_wildExponent_eq {n j : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hxf : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf.symm ▸ hx
  have hmem : K⟮x⟯ ∈ totallyRamifiedOfDegree K n :=
    adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hxf
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hxf
  rw [hdeg] at hd
  have hwc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  rw [← iInf_addVal_derivative_eq_iff_mem_eisensteinBox hn he hf]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hd]
  constructor
  · intro heq
    have hnat : (K⟮x⟯).discriminantExponent = n - 1 + j := by exact_mod_cast heq
    omega
  · rintro rfl
    exact_mod_cast (by omega : (K⟮x⟯).discriminantExponent = n - 1 + (K⟮x⟯).wildExponent)

/-- **Ore's realizability theorem**: a wild exponent `j` occurs as the wild exponent of a totally
ramified separable extension of degree `n` of `K` if and only if `IsOreAdmissible K n j`. This
holds in both mixed and equal characteristic, and for `n = 0` both sides are false. -/
theorem ore_realizability (n j : ℕ) :
    (∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j) ↔ IsOreAdmissible K n j := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hE
    obtain ⟨f, x, hmonic, he, hdeg, hxf, rfl⟩ :=
      exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hE
    let a : Fin n → K := fun i ↦ (f.coeff i.1 : K)
    have hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a := by
      ext k
      rw [coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
      by_cases hk : k < n
      · simpa [a] using (coeff_monicOfCoeff a ⟨k, hk⟩).symm
      · rcases eq_or_lt_of_le (not_lt.1 hk) with rfl | hgt
        · rw [coeff_monicOfCoeff_self, ← hdeg, ← leadingCoeff, hmonic.leadingCoeff,
            Subring.coe_one]
        · rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hgt), coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_monicOfCoeff]; exact hgt), Subring.coe_zero]
    have haE : a ∈ eisensteinSet K n :=
      mem_eisensteinSet_iff_exists_isEisensteinAt.2 ⟨f, hf, he⟩
    exact ((mem_eisensteinBox_iff_wildExponent_eq hn haE (hf ▸ hxf)).2 rfl).1
  · intro hadm
    have hn : 0 < n := hadm.pos
    obtain ⟨a, ha⟩ := nonempty_eisensteinBox_iff.2 hadm
    have haE := eisensteinBox_subset_eisensteinSet n j ha
    have hsep := separable_monicOfCoeff_of_mem_eisensteinBox ha
    have hcard : ((monicOfCoeff a).aroots (SeparableClosure K)).card = n := by
      rw [aroots_def, ← (IsSepClosed.splits_codomain _ hsep).natDegree_eq_card_roots,
        natDegree_map, natDegree_monicOfCoeff]
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hn)
    have hax : aeval x (monicOfCoeff a) = 0 := (mem_aroots.1 hx).2
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.1 haE
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
        natDegree_monicOfCoeff]
    exact ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg (hf.symm ▸ hax),
      (mem_eisensteinBox_iff_wildExponent_eq hn haE hax).1 ha⟩

/-! ### Measurability and Haar volume of the discriminant box -/

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hadm : IsOreAdmissible K n j
  · by_cases hmod : j % n = 0
    · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hmod]
      exact (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    · rw [eisensteinBox_eq_sdiff_of_mod_ne_zero hadm hmod]
      exact ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)).diff
        ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow _))
  · rw [eisensteinBox_eq_empty_of_not_isOreAdmissible hadm]
    exact MeasurableSet.empty

/-- Helper: volume of a box of ideal powers with one coordinate deepened by `1`. -/
private theorem measure_sdiff_univ_pi_update_succ {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) (e : Fin n → ℕ) (k : Fin n) :
    μ ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e k (e k + 1) i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := e)
    (e := Function.update e k (e k + 1)) (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, Function.update e k (e k + 1) i = (∑ i, e i) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ k), ← Finset.erase_eq, add_comm (e k) 1,
      add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ k), add_comm]
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ (Function.update e k (e k + 1))
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [measure_sdiff hsub (measurableSet_univ_pi_image_maximalIdeal_pow _).nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.2 (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- **The volume of an admissible discriminant box**: for a left-invariant measure on `Fin n → K`
normalized on the integer box, the box for an Ore-admissible `(n, j)` has volume
`q ^ (-(1 + ∑_{1 ≤ h < n} ν_h)) * (1 - q⁻¹) * (1 - q⁻¹) ^ [j % n ≠ 0]`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_eisensteinBox {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
          (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set ν : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i.1
  set i₀ : Fin n := ⟨0, hadm.pos⟩
  have hsum_ν :
      ∑ i : Fin n, ν i = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
    rw [Fin.sum_univ_eq_sum_range (fun h ↦ oreCoefficientDepth K n j h) n,
      ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hadm.pos, oreCoefficientDepth_zero]
  by_cases hmod : j % n = 0
  · rw [ite_eq_left hmod, mul_one, eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hmod]
    simpa only [hsum_ν] using measure_sdiff_univ_pi_update_succ μ hμ ν i₀
  · rw [ite_eq_right hmod, eisensteinBox_eq_sdiff_of_mod_ne_zero hadm hmod]
    set ib : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    set νb : Fin n → ℕ := Function.update ν ib (ν ib + 1)
    have hne : i₀ ≠ ib := fun h ↦ hmod (congrArg Fin.val h).symm
    let box (e : Fin n → ℕ) : Set (Fin n → K) :=
      (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        Set.univ.pi fun i ↦
          ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e i₀ (e i₀ + 1) i)
    have hsub_sdiff : box νb ⊆ box ν := by
      intro a ha
      have hνb0 : νb i₀ = ν i₀ := Function.update_of_ne hne _ _
      rw [mem_univ_pi_sdiff_update_iff, hνb0] at ha
      rw [mem_univ_pi_sdiff_update_iff]
      refine ⟨fun i ↦ ?_, ha.2⟩
      exact univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := ν) (e := νb)
        (le_update_iff.2 ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩) (fun k _ ↦ ha.1 k) i (Set.mem_univ _)
    have hmeas_b : MeasurableSet (box νb) :=
      (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    have hsumb : ∑ i, νb i = (∑ i, ν i) + 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ ib), ← Finset.erase_eq, add_comm (ν ib) 1,
        add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ ib), add_comm]
    have h1 : μ (box ν) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, ν i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) :=
      measure_sdiff_univ_pi_update_succ μ hμ ν i₀
    have h2 : μ (box νb) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ((∑ i, ν i) + 1) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
      simpa only [hsumb] using measure_sdiff_univ_pi_update_succ μ hμ νb i₀
    have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
    have hfin2 : μ (box νb) ≠ ∞ := by
      rw [h2]
      exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq))
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    change μ (box ν \ box νb) = _
    rw [measure_sdiff hsub_sdiff hmeas_b.nullMeasurableSet hfin2, h1, h2, hsum_ν]
    set S : ℕ := 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    set c : ℝ≥0∞ := 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)
    have hpow_ne_top : (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S) ≠ ∞ :=
      ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)
    have hc_ne_top : c ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hfact : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (S + 1) * c =
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S * c) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
      simp only [one_div]
      rw [pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
        (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
      ring
    rw [hfact]
    conv_lhs => lhs; rw [← mul_one (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S * c)]
    rw [← ENNReal.mul_sub fun _ _ ↦ ENNReal.mul_ne_top hpow_ne_top hc_ne_top]

end LocalField

end TauCeti
