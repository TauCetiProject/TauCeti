/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Separable
public import TauCeti.NumberTheory.LocalField.Padic
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Ore's realizability theorem and Krasner's discriminant box

Let `K` be a nonarchimedean local field whose residue field `𝓀[K]` has `q` elements, and let
`σ_K(n) = TauCeti.totallyRamifiedOfDegree K n` be the set of totally ramified degree-`n`
subextensions of `SeparableClosure K`. For `L ∈ σ_K(n)` with discriminant exponent `d(L)`, Serre's
wild exponent is `c(L) = d(L) - n + 1` (`IntermediateField.wildExponent`). This file characterizes
which wild exponents `j` occur in `σ_K(n)` (Ore's conditions and realizability theorem, in
arbitrary characteristic) and stratifies the separable locus of `TauCeti.eisensteinSet K n` into
explicit measurable boxes `TauCeti.eisensteinBox K n j` of computed Haar volume.

## Ore's conditions and realizability

For `0 < n`, write `j = a n + b` with `a = j / n` and `b = j % n < n`, and write
`v_K(h) = TauCeti.natValuation K h ∈ ℕ∞` (`⊤` when `(h : K) = 0`). By the Eisenstein formula for
the different (`TauCeti.natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein`), an Eisenstein
generator of degree `n` with coefficients `c_0, …, c_{n-1} ∈ 𝓂[K]` has wild exponent

`c(L) = min (n v_K(n), min_{1 ≤ h < n} (n (v_K(c_h) - 1 + v_K(h)) + h))`.

The inner quantities `n (v_K(c_h) - 1 + v_K(h)) + h` have distinct nonzero residues `h` modulo `n`,
whereas `n v_K(n)` is `0` modulo `n`. Thus `j = a n + b` can be attained if and only if either
`b = 0` and `a = v_K(n)`, or `0 < b`, `v_K(b) ≤ a`, and `a + 1 ≤ v_K(n)`
(`TauCeti.IsOreAdmissible`). Conversely, `X ^ n + ϖ` (when `b = 0`) and
`X ^ n + ϖ ^ (a + 1 - v_K(b)) X ^ b + ϖ` (when `0 < b`) realize every admissible `j`
(`TauCeti.ore_realizability`). Equivalently, `IsOreAdmissible K n j` is the double inequality
`n * min (v_K(j % n)) (v_K(n)) ≤ j ≤ n * v_K(n)` (`TauCeti.isOreAdmissible_iff_le`).

## Krasner's discriminant box

The same derivative formula identifies the Eisenstein polynomials whose roots have wild exponent `j`
with a measurable box `TauCeti.eisensteinBox K n j ⊆ TauCeti.eisensteinSet K n` defined by lower
valuation bounds `ν_h = TauCeti.oreCoefficientDepth K n j h` on each coordinate, together with unit
conditions at coordinate `0` and (when `b > 0`) coordinate `b`. Every polynomial in
`eisensteinBox K n j` is separable, the boxes for distinct `j` are pairwise disjoint, their union
is `{a ∈ eisensteinSet K n | (monicOfCoeff a).Separable}` (almost all of `eisensteinSet K n` for
Haar measure), and `TauCeti.measure_eisensteinBox` evaluates the normalized Haar volume of each
admissible box.

## Main definitions

* `TauCeti.IsOreAdmissible`: Ore's admissibility conditions on `(n, j)`.
* `TauCeti.oreCoefficientDepth`: the lower valuation depth `ν_h` at coordinate `h`.
* `TauCeti.eisensteinBox`: Krasner's discriminant box in `Fin n → K` for wild exponent `j`.

## Main results

* `TauCeti.isOreAdmissible_iff_le` and `TauCeti.isOreAdmissible_padic_iff`: Ore's conditions as a
  double inequality in `ℕ∞` and over `ℚ_[p]`.
* `TauCeti.ore_realizability`: `∃ E ∈ σ_K(n), c(E) = j ↔ IsOreAdmissible K n j` for `0 < n`.
* `TauCeti.mem_eisensteinBox_iff_wildExponent_adjoin_eq`: root-wild-exponent characterization of
  `eisensteinBox K n j`.
* `TauCeti.separable_monicOfCoeff_of_mem_eisensteinBox`, `TauCeti.pairwiseDisjoint_eisensteinBox`,
  `TauCeti.iUnion_eisensteinBox_eq`, `TauCeti.biUnion_eisensteinBox_ae_eq_eisensteinSet`:
  separability and partition of the Eisenstein region.
* `TauCeti.measurableSet_eisensteinBox` and `TauCeti.measure_eisensteinBox`: measurability and
  normalized Haar volume of `eisensteinBox K n j`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8;
  *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928), 84–117.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Éditions du CNRS, Paris (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
-/

public section
noncomputable section

open MeasureTheory Polynomial ValuativeRel IsDiscreteValuationRing
open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff coeff_monicOfCoeff
  coeff_monicOfCoeff_self)
open scoped ENNReal IntermediateField

namespace TauCeti

/-! ### Auxiliary arithmetic and valuation lemmas -/

/-- Comparing two Euclidean expansions `n * a + b` and `n * m + h` with remainders `b, h < n`. -/
private theorem mul_add_le_mul_add_iff {n a b m h : ℕ} (hb : b < n) (hh : h < n) :
    n * a + b ≤ n * m + h ↔ a + (if h < b then 1 else 0) ≤ m := by
  split_ifs with hlt
  · constructor <;> intro H
    · by_contra! hm
      have : m ≤ a := Nat.lt_succ_iff.mp hm
      nlinarith
    · nlinarith
  · constructor <;> intro H
    · by_contra! hm
      have : m + 1 ≤ a := hm
      nlinarith
    · nlinarith

/-- Membership of a field element in the image of `𝓂[K] ^ k` read via `addVal 𝒪[K]`. -/
private theorem mem_image_maximalIdeal_pow_iff {K : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing 𝒪[K]] {x : K} {k : ℕ} :
    x ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) ↔
      ∃ y : 𝒪[K], (y : K) = x ∧ (k : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal 𝒪[K] y := by
  simp only [Set.mem_image, SetLike.mem_coe,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, and_comm]

/-- For `y : 𝒪[K]`, its coercion lies in the image of `𝓂[K] ^ k` iff `k ≤ addVal 𝒪[K] y`. -/
private theorem coe_mem_image_maximalIdeal_pow_iff {K : Type*} [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing 𝒪[K]] {y : 𝒪[K]} {k : ℕ} :
    (y : K) ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ k) ↔
      (k : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal 𝒪[K] y := by
  rw [mem_image_maximalIdeal_pow_iff]
  exact ⟨fun ⟨z, hz, hv⟩ ↦ Subtype.ext hz ▸ hv, fun hv ↦ ⟨y, rfl, hv⟩⟩

/-- Every separable monic polynomial `monicOfCoeff a` of positive degree has a root in
`SeparableClosure K`. -/
private theorem exists_root_separableClosure_monicOfCoeff {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) {a : Fin n → K} (hsep : (monicOfCoeff a).Separable) :
    ∃ x : SeparableClosure K, aeval x (monicOfCoeff a) = 0 := by
  have hdeg : ((monicOfCoeff a).map (algebraMap K (SeparableClosure K))).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (algebraMap K (SeparableClosure K)).injective,
      degree_eq_natDegree (monic_monicOfCoeff a).ne_zero, natDegree_monicOfCoeff]
    exact_mod_cast hn.ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg
    (hsep.map (f := algebraMap K (SeparableClosure K)))
  exact ⟨x, by rwa [aeval_def, ← eval_map]⟩

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The wild-exponent term contributed by derivative index `i : Fin n` of a monic Eisenstein
polynomial `f` of degree `n`: `n • v_K(n)` at the leading term `i + 1 = n`, and
`n • (v_K(f_{i+1}) - 1 + v_K(i + 1)) + (i + 1)` for `i + 1 < n`. -/
private def eisensteinWildTerm (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} (f : 𝒪[K][X]) (i : Fin n) : ℕ∞ :=
  if (i : ℕ) + 1 = n then n • natValuation K n
  else n • (_root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1)) - 1 +
    natValuation K (i + 1)) + ((i : ℕ) + 1 : ℕ)

/-- Shifting `eisensteinWildTerm` by `n - 1` recovers the `i`-th term of the Eisenstein different
formula. -/
private theorem eisensteinWildTerm_add_sub_one {n : ℕ} {f : 𝒪[K][X]}
    (hm : f.Monic) (he : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (i : Fin n) :
    eisensteinWildTerm K f i + ((n - 1 : ℕ) : ℕ∞) =
      n • _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  rw [AddValuation.map_mul, ← Nat.cast_add_one,
    IsDiscreteValuationRing.addVal_natCast_eq_natValuation]
  unfold eisensteinWildTerm
  split_ifs with hi
  · have hfn : f.coeff n = 1 := hdeg ▸ hm.coeff_natDegree
    rw [hi, hfn, AddValuation.map_one, zero_add]
    congr 1
    exact_mod_cast (by omega : n - 1 = (i : ℕ))
  · have hlt : (i : ℕ) + 1 < n := by omega
    have hv1 : (1 : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1)) := by
      simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
        (n := 1)).mp (by simpa using he.mem (hdeg ▸ hlt))
    rcases eq_or_ne (_root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1))) ⊤ with htop | hne
    · simp [htop, hn.ne']
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hk] at hv1 ⊢
      have hk1 : 1 ≤ k := Nat.cast_le.mp hv1
      rcases eq_or_ne (natValuation K ((i : ℕ) + 1)) ⊤ with hntop | hnne
      · simp [hntop, hn.ne']
      · obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.mp hnne
        rw [← hw, ← Nat.cast_one, ← ENat.natCast_sub k 1]
        simp only [nsmul_eq_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_inj]
        rw [show k + w = (k - 1 + w) + 1 by omega, mul_add_one]
        omega

/-- **Wild-exponent derivative formula**: for a monic Eisenstein polynomial `f` of degree `n > 0`
and a root `x` in `SeparableClosure K`, the wild exponent of `K⟮x⟯` is the minimum of
`eisensteinWildTerm K f i` over `i : Fin n`. -/
private theorem natCast_wildExponent_adjoin_eq_iInf_of_eisenstein {n : ℕ} (hn : 0 < n)
    {f : 𝒪[K][X]} (hm : f.Monic) (he : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n)
    {x : SeparableClosure K} (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    ((K⟮x⟯).wildExponent : ℕ∞) = ⨅ i : Fin n, eisensteinWildTerm K f i := by
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hx
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hx
  have hrel := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hd' : (K⟮x⟯).discriminantExponent = (K⟮x⟯).wildExponent + (n - 1) := by omega
  -- Cast `d(K⟮x⟯) = c(K⟮x⟯) + (n - 1)` to `ℕ∞` and cancel the finite constant `n - 1` across `⨅`.
  let e : Fin f.natDegree ≃ Fin n := finCongr hdeg
  have hiInf : (((K⟮x⟯).wildExponent : ℕ∞) + ((n - 1 : ℕ) : ℕ∞)) =
      ⨅ i : Fin n, (eisensteinWildTerm K f i + ((n - 1 : ℕ) : ℕ∞)) := by
    rw [← Nat.cast_add, ← hd', hd, ← e.iInf_comp]
    refine iInf_congr fun i ↦ ?_
    simpa [e, hdeg] using (eisensteinWildTerm_add_sub_one hm he hdeg (e i)).symm
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₁, hi₁⟩ := ENat.exists_eq_iInf fun i : Fin n ↦
    eisensteinWildTerm K f i + ((n - 1 : ℕ) : ℕ∞)
  refine le_antisymm
    (le_iInf fun i ↦ (ENat.add_le_add_iff_right (ENat.natCast_ne_top (n - 1))).mp
      (hiInf.le.trans (iInf_le _ i)))
    (iInf_le_of_le i₁ ((ENat.add_le_add_iff_right (ENat.natCast_ne_top (n - 1))).mp
      (hi₁ ▸ hiInf.ge)))

/-! ### Ore's admissibility conditions and realizability -/

variable (K) in
/-- **Ore's conditions** on a wild exponent `j = a n + b` (`a = j / n`, `b = j % n`) in degree
`n`: either `b = 0` and `a = v_K(n)`, or `0 < b`, `v_K(b) ≤ a`, and `a + 1 ≤ v_K(n)`. -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  (j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = natValuation K n) ∨
    (0 < j % n ∧ natValuation K (j % n) ≤ ((j / n : ℕ) : ℕ∞) ∧
      ((j / n : ℕ) : ℕ∞) + 1 ≤ natValuation K n)

/-- Unfolded characterization of `IsOreAdmissible`. -/
theorem isOreAdmissible_iff {n j : ℕ} :
    IsOreAdmissible K n j ↔
      (j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = natValuation K n) ∨
        (0 < j % n ∧ natValuation K (j % n) ≤ ((j / n : ℕ) : ℕ∞) ∧
          ((j / n : ℕ) : ℕ∞) + 1 ≤ natValuation K n) := by
  rw [IsOreAdmissible]

/-- In degree `1`, only wild exponent `0` is Ore-admissible. -/
@[simp]
theorem isOreAdmissible_one_iff {j : ℕ} : IsOreAdmissible K 1 j ↔ j = 0 := by
  simp [isOreAdmissible_iff, Nat.mod_one]

/-- Wild exponent `0` is Ore-admissible in degree `n` if and only if the residue characteristic
does not divide `n` (the tame case). -/
theorem isOreAdmissible_zero_right_iff {n : ℕ} :
    IsOreAdmissible K n 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  rw [isOreAdmissible_iff]
  simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, lt_self_iff_false, false_and, or_false,
    true_and]
  rw [eq_comm, natValuation_eq_zero_iff_not_dvd]

/-- **Ore's double inequality**: for `0 < n`, `IsOreAdmissible K n j` holds if and only if
`n * min (v_K(j % n)) (v_K(n)) ≤ j ≤ n * v_K(n)` in `ℕ∞`. -/
theorem isOreAdmissible_iff_le {n j : ℕ} (hn : 0 < n) :
    IsOreAdmissible K n j ↔
      (n : ℕ∞) * min (natValuation K (j % n)) (natValuation K n) ≤ j ∧
        (j : ℕ∞) ≤ (n : ℕ∞) * natValuation K n := by
  rw [isOreAdmissible_iff]
  set a := j / n
  set b := j % n
  have hb : b < n := Nat.mod_lt j hn
  have hj : n * a + b = j := Nat.div_add_mod j n
  have hn0 : (n : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · simp only [hb0, lt_self_iff_false, false_and, or_false, true_and, natValuation_zero,
      min_eq_right le_top]
    have hj' : j = n * a := by omega
    rcases eq_or_ne (natValuation K n) ⊤ with htop | hne
    · rw [htop, ENat.mul_top hn0]
      exact ⟨fun h ↦ absurd h (ENat.natCast_ne_top a),
        fun ⟨h, _⟩ ↦ absurd (top_unique h) (ENat.natCast_ne_top j)⟩
    · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hne
      rw [hj', ← le_antisymm_iff, ← hv]
      simp only [← Nat.cast_mul, Nat.cast_inj]
      exact ⟨fun h ↦ by rw [h], fun h ↦ Nat.eq_of_mul_eq_mul_left hn h.symm⟩
  · simp only [hbpos.ne', false_and, false_or, hbpos, true_and]
    constructor
    · rintro ⟨hba, han⟩
      have h1 : (n : ℕ∞) * min (natValuation K b) (natValuation K n) ≤ j :=
        (mul_le_mul_right (min_le_of_left_le hba) _).trans
          (hj ▸ (by exact_mod_cast Nat.le_add_right (n * a) b :
            (n : ℕ∞) * a ≤ ((n * a + b : ℕ) : ℕ∞)))
      have h2 : (j : ℕ∞) ≤ (n : ℕ∞) * natValuation K n :=
        (hj ▸ (by exact_mod_cast (by rw [mul_add_one]; omega : n * a + b ≤ n * (a + 1)) :
          ((n * a + b : ℕ) : ℕ∞) ≤ (n : ℕ∞) * ((a : ℕ∞) + 1))).trans (mul_le_mul_right han _)
      exact ⟨h1, h2⟩
    · rintro ⟨hlow, hhigh⟩
      have han : (a : ℕ∞) + 1 ≤ natValuation K n := by
        rcases eq_or_ne (natValuation K n) ⊤ with htop | hne
        · simp [htop]
        · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hne
          rw [← hv, ← hj] at hhigh
          rw [← hv]
          have hhigh' : n * a + b ≤ n * v := by exact_mod_cast hhigh
          exact_mod_cast (by nlinarith : a + 1 ≤ v)
      refine ⟨?_, han⟩
      by_contra! hab
      have hmin : (a : ℕ∞) + 1 ≤ min (natValuation K b) (natValuation K n) :=
        le_min (Order.add_one_le_of_lt hab) han
      have h1 : n * (a + 1) ≤ n * a + b := by
        exact_mod_cast (mul_le_mul_right hmin _).trans (hj ▸ hlow)
      rw [mul_add_one] at h1
      omega

/-- Every Ore-admissible wild exponent satisfies `j ≤ n * v_K(n)` in `ℕ∞`. -/
theorem le_mul_natValuation_of_isOreAdmissible {n j : ℕ} (hn : 0 < n)
    (h : IsOreAdmissible K n j) : (j : ℕ∞) ≤ (n : ℕ∞) * natValuation K n :=
  ((isOreAdmissible_iff_le hn).mp h).2

/-- Over `ℚ_[p]`, Ore's admissibility condition is Pauli and Roblot's double inequality
`min(v_p(j % n) n, v_p(n) n) ≤ j ≤ v_p(n) n` (with `v_p(0)` treated as `∞`, so the lower bound is
`v_p(n) n` when `n ∣ j`). -/
theorem isOreAdmissible_padic_iff (p : ℕ) [Fact p.Prime] {n j : ℕ} (hn : 0 < n) :
    IsOreAdmissible ℚ_[p] n j ↔
      (if j % n = 0 then n * padicValNat p n
        else n * min (padicValNat p (j % n)) (padicValNat p n)) ≤ j ∧
        j ≤ n * padicValNat p n := by
  rw [isOreAdmissible_iff_le hn, _root_.Padic.natValuation_of_ne_zero p hn.ne']
  rcases eq_or_ne (j % n) 0 with hb0 | hb
  · simp only [hb0, ↓reduceIte, natValuation_zero, min_eq_right le_top, ← Nat.cast_mul, Nat.cast_le]
  · rw [_root_.Padic.natValuation_of_ne_zero p hb]
    rcases le_total (padicValNat p (j % n)) (padicValNat p n) with hle | hle
    · rw [min_eq_left hle, min_eq_left (Nat.cast_le.mpr hle)]
      simp only [hb, ↓reduceIte, ← Nat.cast_mul, Nat.cast_le]
    · rw [min_eq_right hle, min_eq_right (Nat.cast_le.mpr hle)]
      simp only [hb, ↓reduceIte, ← Nat.cast_mul, Nat.cast_le]

/-! ### Krasner's discriminant box -/

variable (K) in
/-- The coefficient valuation lower bound `ν_h = max(1, ⌊j / n⌋ + 1 + [h < j % n] - v_K(h))` of
Krasner's discriminant box at index `h`, taking value `1` when `(h : K) = 0`. -/
def oreCoefficientDepth (n j h : ℕ) : ℕ := by
  classical
  exact if hh : (h : K) = 0 then 1 else
    max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh)

variable (K) in
/-- When `(h : K) = 0`, `oreCoefficientDepth K n j h` is `1`. -/
theorem oreCoefficientDepth_of_cast_eq_zero (n j : ℕ) {h : ℕ} (hh : (h : K) = 0) :
    oreCoefficientDepth K n j h = 1 := by
  classical
  rw [oreCoefficientDepth, dite_eq_left hh]

variable (K) in
/-- When `(h : K) ≠ 0`, `oreCoefficientDepth K n j h` is
`max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh)`. -/
theorem oreCoefficientDepth_of_cast_ne_zero (n j : ℕ) {h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth K n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  classical
  rw [oreCoefficientDepth, dite_eq_right hh]

variable (K) in
/-- At `h = 0`, `oreCoefficientDepth` is `1`. -/
@[simp]
theorem oreCoefficientDepth_zero (n j : ℕ) : oreCoefficientDepth K n j 0 = 1 :=
  oreCoefficientDepth_of_cast_eq_zero K n j Nat.cast_zero

variable (K) in
/-- Every `oreCoefficientDepth` is at least `1`. -/
theorem one_le_oreCoefficientDepth (n j h : ℕ) : 1 ≤ oreCoefficientDepth K n j h := by
  by_cases hh : (h : K) = 0
  · simp [oreCoefficientDepth_of_cast_eq_zero K n j hh]
  · simp [oreCoefficientDepth_of_cast_ne_zero K n j hh]

/-- At the active remainder coordinate `b = j % n > 0` of an Ore-admissible `j`, `(b : K) ≠ 0` and
`oreCoefficientDepth K n j b = j / n + 1 - v_K(b)`. -/
theorem oreCoefficientDepth_mod_of_isOreAdmissible {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    ∃ hh : ((j % n : ℕ) : K) ≠ 0,
      oreCoefficientDepth K n j (j % n) = j / n + 1 - natCastValuation K (j % n) hh := by
  rcases (isOreAdmissible_iff.mp hadm) with ⟨h0, -⟩ | ⟨-, hval, -⟩
  · omega
  have hh : ((j % n : ℕ) : K) ≠ 0 := by
    intro h0
    rw [natValuation_of_cast_eq_zero K h0] at hval
    exact ENat.natCast_ne_top (j / n) (top_unique hval)
  rw [natValuation_of_cast_ne_zero K hh, Nat.cast_le] at hval
  refine ⟨hh, ?_⟩
  rw [oreCoefficientDepth_of_cast_ne_zero K n j hh]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  omega

/-- Comparing `j` against the `i`-th derivative term `eisensteinWildTerm` (for `i + 1 < n`) is
equivalent to comparing `oreCoefficientDepth K n j (i + 1)` against `addVal (f.coeff (i + 1))`. -/
private theorem le_eisensteinWildTerm_iff_oreCoefficientDepth_le {n j : ℕ} {f : 𝒪[K][X]}
    (he : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    (j : ℕ∞) ≤ eisensteinWildTerm K f i ↔
      (oreCoefficientDepth K n j ((i : ℕ) + 1) : ℕ∞) ≤
        _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1)) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hv1 : (1 : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) := by
    simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
      (n := 1)).mp (by simpa using he.mem (hdeg ▸ hi))
  unfold eisensteinWildTerm
  rw [ite_eq_right hi.ne]
  by_cases hhK : (((i : ℕ) + 1 : ℕ) : K) = 0
  · rw [natValuation_of_cast_eq_zero K hhK, oreCoefficientDepth_of_cast_eq_zero K n j hhK]
    simp [hn.ne', hv1]
  · rw [natValuation_of_cast_ne_zero K hhK, oreCoefficientDepth_of_cast_ne_zero K n j hhK]
    rcases eq_or_ne (_root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff ((i : ℕ) + 1))) ⊤ with
      htop | hne
    · simp [htop, hn.ne']
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hk] at hv1 ⊢
      have hk1 : 1 ≤ k := Nat.cast_le.mp hv1
      rw [← Nat.cast_one, ← ENat.natCast_sub k 1]
      simp only [nsmul_eq_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_le]
      rw [← Nat.div_add_mod j n, mul_add_le_mul_add_iff (Nat.mod_lt j hn) hi,
        Nat.div_add_mod]
      omega

/-- At the remainder coordinate `h = j % n > 0` of an Ore-admissible `j`, the derivative term
equals `j` if and only if `addVal (f.coeff h) = oreCoefficientDepth K n j h`. -/
private theorem eisensteinWildTerm_eq_iff_addVal_eq {n j : ℕ} (hadm : IsOreAdmissible K n j)
    {f : 𝒪[K][X]} (he : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) {i : Fin n}
    (hi : (i : ℕ) + 1 = j % n) :
    eisensteinWildTerm K f i = (j : ℕ∞) ↔
      _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i + 1)) =
        oreCoefficientDepth K n j ((i : ℕ) + 1) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hb : 0 < j % n := by omega
  have hlt : (i : ℕ) + 1 < n := hi ▸ Nat.mod_lt j hn
  obtain ⟨hhK, hdepth⟩ := oreCoefficientDepth_mod_of_isOreAdmissible hadm hb
  have hv1 : (1 : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) := by
    simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
      (n := 1)).mp (by simpa using he.mem (hdeg ▸ hlt))
  have hhK' : (((i : ℕ) + 1 : ℕ) : K) ≠ 0 := hi ▸ hhK
  unfold eisensteinWildTerm
  rw [ite_eq_right hlt.ne, natValuation_of_cast_ne_zero K hhK']
  rcases eq_or_ne (_root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff ((i : ℕ) + 1))) ⊤ with
    htop | hne
  · simp [htop, hn.ne']
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hk] at hv1 ⊢
    have hk1 : 1 ≤ k := Nat.cast_le.mp hv1
    rw [← Nat.cast_one, ← ENat.natCast_sub k 1]
    simp only [nsmul_eq_mul, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_inj]
    have hval_le : natCastValuation K ((i : ℕ) + 1) hhK' ≤ j / n := by
      rcases (isOreAdmissible_iff.mp hadm) with ⟨h0, -⟩ | ⟨-, hv, -⟩
      · omega
      · rwa [← hi, natValuation_of_cast_ne_zero K hhK', Nat.cast_le] at hv
    have hdepth' : oreCoefficientDepth K n j ((i : ℕ) + 1) =
        j / n + 1 - natCastValuation K ((i : ℕ) + 1) hhK' := by
      simpa [hi] using hdepth
    rw [hdepth']
    constructor
    · intro H
      have H' : n * (k - 1 + natCastValuation K ((i : ℕ) + 1) hhK') + j % n =
          n * (j / n) + j % n := by
        calc n * (k - 1 + natCastValuation K ((i : ℕ) + 1) hhK') + j % n
            = n * (k - 1 + natCastValuation K ((i : ℕ) + 1) hhK') + ((i : ℕ) + 1) :=
              congrArg (_ + ·) hi.symm
          _ = j := H
          _ = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
      have H'' : k - 1 + natCastValuation K ((i : ℕ) + 1) hhK' = j / n :=
        Nat.eq_of_mul_eq_mul_left hn (Nat.add_right_cancel H')
      omega
    · intro H
      have H'' : k - 1 + natCastValuation K ((i : ℕ) + 1) hhK' = j / n := by omega
      rw [H'', hi, Nat.div_add_mod]

variable (K) in
/-- **Krasner's discriminant box** in `Fin n → K` for degree `n` and wild exponent `j`: empty
unless `0 < n` and `IsOreAdmissible K n j`, and otherwise the set of coefficient vectors `a` with
`a i ∈ 𝓂[K] ^ oreCoefficientDepth K n j i` for every `i : Fin n`, `a 0 ∉ 𝓂[K] ^ 2`, and (when
`j % n > 0`) `a (j % n) ∉ 𝓂[K] ^ (oreCoefficientDepth K n j (j % n) + 1)`. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | 0 < n ∧ IsOreAdmissible K n j ∧
    (∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
    ∀ i : Fin n, ((i : ℕ) = 0 ∨ (i : ℕ) = j % n) →
      a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i + 1))}

/-- Membership characterization for `eisensteinBox`. -/
theorem mem_eisensteinBox {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔ 0 < n ∧ IsOreAdmissible K n j ∧
      (∀ i : Fin n, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i)) ∧
      ∀ i : Fin n, ((i : ℕ) = 0 ∨ (i : ℕ) = j % n) →
        a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i + 1)) := by
  rw [eisensteinBox]
  rfl

/-- In degree `0`, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero_left (j : ℕ) : eisensteinBox K 0 j = ∅ := by
  ext a
  simp [mem_eisensteinBox]

/-- Outside Ore's admissible wild exponents, the discriminant box is empty. -/
theorem eisensteinBox_eq_empty_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ := by
  ext a
  simp [mem_eisensteinBox, h]

/-- Every discriminant box lies inside the Eisenstein region `eisensteinSet K n`. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n := by
  rintro a ha
  rw [mem_eisensteinBox] at ha
  obtain ⟨hn, -, hlow, hhigh⟩ := ha
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := fun _ ↦ 1)
    (e := fun i : Fin n ↦ oreCoefficientDepth K n j i)
    (fun i ↦ one_le_oreCoefficientDepth K n j i)
  simp only [pow_one] at hsub
  rw [eisensteinSet_eq_sdiff hn]
  refine ⟨hsub fun i _ ↦ hlow i, fun h2 ↦ hhigh ⟨0, hn⟩ (Or.inl rfl) ?_⟩
  simpa [Function.update_self] using h2 ⟨0, hn⟩ (Set.mem_univ _)

/-- Every polynomial with coefficient vector in `eisensteinBox K n j` is separable over `K`,
including in positive characteristic. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  have heis := eisensteinBox_subset_eisensteinSet n j ha
  rw [mem_eisensteinBox] at ha
  obtain ⟨hn, hadm, -, hhigh⟩ := ha
  rw [separable_iff_derivative_ne_zero (irreducible_monicOfCoeff_of_mem_eisensteinSet hn heis)]
  intro hderiv
  rcases (isOreAdmissible_iff.mp hadm) with ⟨-, hvn⟩ | ⟨hbpos, hvb, -⟩
  · -- When `j % n = 0`, `(n : K) ≠ 0` so the leading derivative coefficient `(n : K)` is nonzero.
    have hnK : (n : K) ≠ 0 :=
      (natValuation_ne_top_iff K).mp (hvn ▸ ENat.natCast_ne_top (j / n))
    have hc := congrArg (fun p : K[X] ↦ p.coeff (n - 1)) hderiv
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [coeff_derivative, hsub, coeff_monicOfCoeff_self, one_mul, coeff_zero,
      ← Nat.cast_add_one, hsub] at hc
    exact hnK hc
  · -- When `b = j % n > 0`, `(b : K) ≠ 0` and `a b ≠ 0`, so `(derivative).coeff (b - 1) ≠ 0`.
    set b := j % n
    have hb_lt : b < n := Nat.mod_lt j hn
    have hbK : (b : K) ≠ 0 :=
      (natValuation_ne_top_iff K).mp (ne_top_of_le_ne_top (ENat.natCast_ne_top (j / n)) hvb)
    have hab0 : a ⟨b, hb_lt⟩ ≠ 0 := by
      intro h0
      exact hhigh ⟨b, hb_lt⟩ (Or.inr rfl) ⟨0, zero_mem _, by simp [h0]⟩
    have hc := congrArg (fun p : K[X] ↦ p.coeff (b - 1)) hderiv
    have hsub : b - 1 + 1 = b := Nat.sub_add_cancel hbpos
    have hcoeff : (monicOfCoeff a).coeff (b - 1 + 1) = a ⟨b, hb_lt⟩ := by
      rw [hsub]; exact coeff_monicOfCoeff a ⟨b, hb_lt⟩
    rw [coeff_derivative, hcoeff, coeff_zero, ← Nat.cast_add_one, hsub] at hc
    exact mul_ne_zero hab0 hbK hc

/-- Every Ore-admissible discriminant box in positive degree is nonempty: `X ^ n + ϖ` lies in the
box when `j % n = 0`, and `X ^ n + ϖ ^ ν_b X ^ b + ϖ` lies in the box when `b = j % n > 0`. -/
theorem nonempty_eisensteinBox_of_isOreAdmissible {n j : ℕ} (hn : 0 < n)
    (hadm : IsOreAdmissible K n j) : (eisensteinBox K n j).Nonempty := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  have hϖ1 : _root_.IsDiscreteValuationRing.addVal 𝒪[K] ϖ = 1 :=
    _root_.IsDiscreteValuationRing.addVal_uniformizer hϖ
  set i₀ : Fin n := ⟨0, hn⟩
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · refine ⟨Function.update 0 i₀ (ϖ : K), ?_⟩
    rw [mem_eisensteinBox]
    refine ⟨hn, hadm, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rcases eq_or_ne i i₀ with rfl | hne
      · rw [Function.update_self, coe_mem_image_maximalIdeal_pow_iff, hϖ1]
        simp [i₀]
      · exact ⟨0, zero_mem _, by simp [Function.update_of_ne hne]⟩
    · have hi0 : i = i₀ := Fin.ext (hi.elim id (hb0 ▸ id))
      subst hi0
      rw [Function.update_self, coe_mem_image_maximalIdeal_pow_iff, hϖ1]
      simp [i₀]
  · set b := j % n
    have hb_lt : b < n := Nat.mod_lt j hn
    set ib : Fin n := ⟨b, hb_lt⟩
    have hib0 : ib ≠ i₀ := fun h ↦ hbpos.ne' (congrArg Fin.val h)
    set d := oreCoefficientDepth K n j b
    refine ⟨Function.update (Function.update 0 i₀ (ϖ : K)) ib ((ϖ ^ d : 𝒪[K]) : K), ?_⟩
    rw [mem_eisensteinBox]
    refine ⟨hn, hadm, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · by_cases h1 : i = ib
      · subst h1
        rw [Function.update_self, coe_mem_image_maximalIdeal_pow_iff, hϖ.addVal_pow]
      · rw [Function.update_of_ne h1]
        by_cases h2 : i = i₀
        · subst h2
          rw [Function.update_self, coe_mem_image_maximalIdeal_pow_iff, hϖ1]
          simp [i₀]
        · exact ⟨0, zero_mem _, by simp [Function.update_of_ne h2]⟩
    · rcases hi with hi0 | hib
      · have h_eq : i = i₀ := Fin.ext hi0
        subst h_eq
        rw [Function.update_of_ne hib0.symm, Function.update_self,
          coe_mem_image_maximalIdeal_pow_iff, hϖ1]
        simp [i₀]
      · have h_eq : i = ib := Fin.ext hib
        subst h_eq
        rw [Function.update_self, coe_mem_image_maximalIdeal_pow_iff, hϖ.addVal_pow, not_le,
          Nat.cast_lt]
        exact Nat.lt_succ_self _

/-- Forward direction of the discriminant-box characterization: if `a ∈ eisensteinBox K n j`, then
any root `x` of `monicOfCoeff a` generates `K⟮x⟯` of wild exponent `j`. -/
private theorem wildExponent_adjoin_eq_of_mem_eisensteinBox {n j : ℕ} (hn : 0 < n)
    {a : Fin n → K} (habox : a ∈ eisensteinBox K n j) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) : (K⟮x⟯).wildExponent = j := by
  have ha := eisensteinBox_subset_eisensteinSet n j habox
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hm : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hcoeff (i : Fin n) : a i = (f.coeff i : K) := by
    rw [← coeff_monicOfCoeff a i, ← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
  have hwild := natCast_wildExponent_adjoin_eq_iInf_of_eisenstein hn hm he hdeg (hf.symm ▸ hx)
  obtain ⟨-, hadm, hlow, hhigh⟩ := mem_eisensteinBox.mp habox
  have hle_all (i : Fin n) : (j : ℕ∞) ≤ eisensteinWildTerm K f i := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with hi_top | hi_lt
    · unfold eisensteinWildTerm
      rw [ite_eq_left hi_top, nsmul_eq_mul]
      exact le_mul_natValuation_of_isOreAdmissible hn hadm
    · rw [le_eisensteinWildTerm_iff_oreCoefficientDepth_le he hdeg hi_lt]
      have := hlow ⟨(i : ℕ) + 1, hi_lt⟩
      rwa [hcoeff ⟨(i : ℕ) + 1, hi_lt⟩, coe_mem_image_maximalIdeal_pow_iff] at this
  have hatt : ∃ i₀ : Fin n, eisensteinWildTerm K f i₀ ≤ (j : ℕ∞) := by
    rcases (isOreAdmissible_iff.mp hadm) with ⟨-, hvn⟩ | ⟨hbpos, -, -⟩
    · refine ⟨⟨n - 1, Nat.sub_lt hn zero_lt_one⟩, ?_⟩
      have htop : (⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ : Fin n).val + 1 = n :=
        Nat.sub_add_cancel hn
      unfold eisensteinWildTerm
      rw [ite_eq_left htop, ← hvn, nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]
      exact Nat.mul_div_le j n
    · have hb_lt : j % n < n := Nat.mod_lt j hn
      refine ⟨⟨j % n - 1, by omega⟩, le_of_eq ?_⟩
      have hmod : (⟨j % n - 1, by omega⟩ : Fin n).val + 1 = j % n := Nat.sub_add_cancel hbpos
      rw [eisensteinWildTerm_eq_iff_addVal_eq hadm he hdeg hmod]
      have hlow_b := hlow ⟨j % n, hb_lt⟩
      have hhigh_b := hhigh ⟨j % n, hb_lt⟩ (Or.inr rfl)
      rw [hcoeff ⟨j % n, hb_lt⟩, coe_mem_image_maximalIdeal_pow_iff] at hlow_b hhigh_b
      simp only [hmod] at hlow_b hhigh_b ⊢
      rcases eq_or_ne (_root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (j % n))) ⊤ with
        htop | hne
      · simp [htop] at hhigh_b
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
        rw [← hk, Nat.cast_le] at hlow_b hhigh_b
        rw [← hk, Nat.cast_inj]
        omega
  obtain ⟨i₀, hi₀⟩ := hatt
  exact Nat.cast_inj.mp (hwild.trans (le_antisymm (iInf_le_of_le i₀ hi₀) (le_iInf hle_all)))

/-- Deducing Ore admissibility and the attaining remainder index from an index `i₀` with
`eisensteinWildTerm K f i₀ = j` and the leading bound `j ≤ n * v_K(n)`. -/
private theorem isOreAdmissible_and_index_of_eisensteinWildTerm_eq {n j : ℕ} (hn : 0 < n)
    {f : 𝒪[K][X]} {i₀ : Fin n} (hlead : (j : ℕ∞) ≤ (n : ℕ∞) * natValuation K n)
    (hi₀_eq : eisensteinWildTerm K f i₀ = (j : ℕ∞)) :
    IsOreAdmissible K n j ∧ (0 < j % n → (i₀ : ℕ) + 1 = j % n) := by
  have hn0 : (n : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt i₀.isLt) with hi_top | hi_lt
  · unfold eisensteinWildTerm at hi₀_eq
    rw [ite_eq_left hi_top, nsmul_eq_mul] at hi₀_eq
    rcases eq_or_ne (natValuation K n) ⊤ with htop | hne
    · rw [htop, ENat.mul_top hn0] at hi₀_eq
      exact absurd hi₀_eq.symm (ENat.natCast_ne_top j)
    · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hv, ← Nat.cast_mul, Nat.cast_inj] at hi₀_eq
      have hmod : j % n = 0 := by rw [← hi₀_eq, Nat.mul_mod_right]
      have hdiv : j / n = v := by rw [← hi₀_eq, Nat.mul_div_right _ hn]
      exact ⟨isOreAdmissible_iff.mpr (Or.inl ⟨hmod, by rw [hdiv, hv]⟩), fun hb ↦ by omega⟩
  · unfold eisensteinWildTerm at hi₀_eq
    rw [ite_eq_right hi_lt.ne] at hi₀_eq
    set t := _root_.IsDiscreteValuationRing.addVal 𝒪[K] (f.coeff (i₀ + 1)) - 1 +
      natValuation K (i₀ + 1)
    rcases eq_or_ne t ⊤ with htop | hne
    · simp [t, htop, hn.ne'] at hi₀_eq
    · obtain ⟨m, hm_eq⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hm_eq, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj] at hi₀_eq
      have hmod : j % n = (i₀ : ℕ) + 1 := by
        rw [← hi₀_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hi_lt]
      have hdiv : j / n = m := by
        rw [← hi₀_eq, Nat.mul_add_div hn, Nat.div_eq_zero_iff.mpr (Or.inr hi_lt), add_zero]
      have hvm : natValuation K (j % n) ≤ (m : ℕ∞) := by
        rw [hmod, hm_eq]; exact le_add_self
      have han : ((m : ℕ∞) + 1) ≤ natValuation K n := by
        rcases eq_or_ne (natValuation K n) ⊤ with hvtop | hvne
        · simp [hvtop]
        · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hvne
          rw [← hv, ← hi₀_eq] at hlead
          have hlead' : n * m + ((i₀ : ℕ) + 1) ≤ n * v := by exact_mod_cast hlead
          rw [← hv]
          exact_mod_cast (by nlinarith : m + 1 ≤ v)
      exact ⟨isOreAdmissible_iff.mpr (Or.inr ⟨by omega, hdiv ▸ hvm, hdiv ▸ han⟩),
        fun _ ↦ hmod.symm⟩

/-- Reverse direction of the discriminant-box characterization: if `a ∈ eisensteinSet K n` and `x`
is a root of `monicOfCoeff a`, then `a ∈ eisensteinBox K n (K⟮x⟯).wildExponent`. -/
private theorem mem_eisensteinBox_wildExponent_adjoin {n : ℕ} (hn : 0 < n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n (K⟮x⟯).wildExponent := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hm : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  have hcoeff (i : Fin n) : a i = (f.coeff i : K) := by
    rw [← coeff_monicOfCoeff a i, ← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
  set j := (K⟮x⟯).wildExponent
  have hwild := natCast_wildExponent_adjoin_eq_iInf_of_eisenstein hn hm he hdeg (hf.symm ▸ hx)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hle_all (i : Fin n) : (j : ℕ∞) ≤ eisensteinWildTerm K f i := hwild ▸ iInf_le _ i
  obtain ⟨i₀, hi₀⟩ := ENat.exists_eq_iInf fun i : Fin n ↦ eisensteinWildTerm K f i
  have hlead : (j : ℕ∞) ≤ (n : ℕ∞) * natValuation K n := by
    have h := hle_all ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
    have htop : (⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ : Fin n).val + 1 = n := Nat.sub_add_cancel hn
    unfold eisensteinWildTerm at h; rwa [ite_eq_left htop, nsmul_eq_mul] at h
  obtain ⟨hadm, hidx⟩ := isOreAdmissible_and_index_of_eisensteinWildTerm_eq hn hlead
    (hi₀.trans hwild.symm)
  have ha0_mem : a ⟨0, hn⟩ ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j 0) := by
    rw [hcoeff ⟨0, hn⟩, oreCoefficientDepth_zero, pow_one]
    exact ⟨f.coeff 0, he.mem (hdeg ▸ hn), rfl⟩
  have ha0_notMem : a ⟨0, hn⟩ ∉
      ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j 0 + 1)) := by
    rw [hcoeff ⟨0, hn⟩, oreCoefficientDepth_zero, coe_mem_image_maximalIdeal_pow_iff,
      ← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
    exact he.notMem
  rw [mem_eisensteinBox]
  refine ⟨hn, hadm, fun i ↦ ?_, fun i hi_or ↦ ?_⟩
  · rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have h_eq : i = ⟨0, hn⟩ := Fin.ext hi0; exact h_eq ▸ ha0_mem
    · have hpred : (⟨(i : ℕ) - 1, by omega⟩ : Fin n).val + 1 = i := Nat.sub_add_cancel hipos
      have hlt_i : (⟨(i : ℕ) - 1, by omega⟩ : Fin n).val + 1 < n := by rw [hpred]; exact i.isLt
      have h := (le_eisensteinWildTerm_iff_oreCoefficientDepth_le he hdeg hlt_i).mp
        (hle_all ⟨(i : ℕ) - 1, by omega⟩)
      rw [hcoeff i, coe_mem_image_maximalIdeal_pow_iff]; rwa [hpred] at h
  · rcases hi_or with hi0 | hib
    · have h_eq : i = ⟨0, hn⟩ := Fin.ext hi0; exact h_eq ▸ ha0_notMem
    · rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
      · have h_eq : i = ⟨0, hn⟩ := Fin.ext (hib.trans hb0); exact h_eq ▸ ha0_notMem
      · have hval_eq := (eisensteinWildTerm_eq_iff_addVal_eq hadm he hdeg (hidx hbpos)).mp
          (hi₀.trans hwild.symm)
        rw [hcoeff i, coe_mem_image_maximalIdeal_pow_iff, hib]
        rw [hidx hbpos] at hval_eq
        rw [hval_eq, not_le, Nat.cast_lt]; exact Nat.lt_succ_self _

/-- **Box characterization of the wild exponent**: for `0 < n`, `a ∈ eisensteinSet K n`, and any
root `x : SeparableClosure K` of `monicOfCoeff a`, the generated extension `K⟮x⟯` has wild exponent
`j` if and only if `a ∈ eisensteinBox K n j`. -/
theorem mem_eisensteinBox_iff_wildExponent_adjoin_eq {n j : ℕ} (hn : 0 < n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    a ∈ eisensteinBox K n j ↔ (K⟮x⟯).wildExponent = j :=
  ⟨fun habox ↦ wildExponent_adjoin_eq_of_mem_eisensteinBox hn habox hx,
    fun h ↦ h ▸ mem_eisensteinBox_wildExponent_adjoin hn ha hx⟩

/-- Every root in `SeparableClosure K` of a polynomial in `eisensteinBox K n j` generates a member
of `σ_K(n)` of wild exponent `j`. -/
theorem adjoin_mem_and_wildExponent_eq_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) {x : SeparableClosure K} (hx : aeval x (monicOfCoeff a) = 0) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n ∧ (K⟮x⟯).wildExponent = j := by
  have heis := eisensteinBox_subset_eisensteinSet n j ha
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp heis
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) f, hf,
      natDegree_monicOfCoeff]
  exact ⟨adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg (hf.symm ▸ hx),
    wildExponent_adjoin_eq_of_mem_eisensteinBox (mem_eisensteinBox.mp ha).1 ha hx⟩

/-- **Ore's realizability theorem**: for `0 < n` and any local field `K` (of either
characteristic), some member of `totallyRamifiedOfDegree K n` has wild exponent `j` if and only if
`IsOreAdmissible K n j`. -/
theorem ore_realizability (n j : ℕ) (hn : 0 < n) :
    (∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j) ↔ IsOreAdmissible K n j := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨f, x, hm, he, hdeg, hx, rfl⟩ :=
      exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hE
    let a : Fin n → K := fun i ↦ (f.coeff i : K)
    have hmap : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a := by
      ext k
      rcases lt_trichotomy k n with hlt | rfl | hgt
      · simp [a, coeff_map, Algebra.algebraMap_ofSubsemiring_apply,
          coeff_monicOfCoeff a ⟨k, hlt⟩]
      · have hfn : f.coeff k = 1 := hdeg ▸ hm.coeff_natDegree
        rw [coeff_map, hfn, map_one, coeff_monicOfCoeff_self]
      · rw [coeff_map, coeff_eq_zero_of_natDegree_lt (hdeg ▸ hgt), map_zero,
          coeff_eq_zero_of_natDegree_lt ((natDegree_monicOfCoeff a).symm ▸ hgt)]
    have ha : a ∈ eisensteinSet K n :=
      mem_eisensteinSet_iff_exists_isEisensteinAt.mpr ⟨f, hmap, he⟩
    have habox := mem_eisensteinBox_wildExponent_adjoin hn ha (hmap ▸ hx)
    exact (mem_eisensteinBox.mp habox).2.1
  · intro hadm
    obtain ⟨a, ha⟩ := nonempty_eisensteinBox_of_isOreAdmissible hn hadm
    obtain ⟨x, hxa⟩ := exists_root_separableClosure_monicOfCoeff hn
      (separable_monicOfCoeff_of_mem_eisensteinBox ha)
    obtain ⟨hmem, hwild⟩ := adjoin_mem_and_wildExponent_eq_of_mem_eisensteinBox ha hxa
    exact ⟨K⟮x⟯, hmem, hwild⟩

/-- The discriminant boxes `eisensteinBox K n j` for distinct wild exponents `j` are pairwise
disjoint. -/
theorem pairwiseDisjoint_eisensteinBox (n : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (eisensteinBox K n) := by
  intro j _ j' _ hne
  refine Set.disjoint_left.mpr fun a hj hj' ↦ hne ?_
  have hn : 0 < n := (mem_eisensteinBox.mp hj).1
  obtain ⟨x, hxa⟩ := exists_root_separableClosure_monicOfCoeff hn
    (separable_monicOfCoeff_of_mem_eisensteinBox hj)
  exact (wildExponent_adjoin_eq_of_mem_eisensteinBox hn hj hxa).symm.trans
    (wildExponent_adjoin_eq_of_mem_eisensteinBox hn hj' hxa)

/-- For `0 < n`, the union of `eisensteinBox K n j` over all `j` (equivalently over all
Ore-admissible `j`) is the set of separable Eisenstein polynomials of degree `n`. -/
theorem iUnion_eisensteinBox_eq {n : ℕ} (hn : 0 < n) :
    (⋃ j : ℕ, eisensteinBox K n j) = {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨fun ⟨j, hj⟩ ↦ ⟨eisensteinBox_subset_eisensteinSet n j hj,
    separable_monicOfCoeff_of_mem_eisensteinBox hj⟩, fun ⟨heis, hsep⟩ ↦ ?_⟩
  obtain ⟨x, hxa⟩ := exists_root_separableClosure_monicOfCoeff hn hsep
  exact ⟨(K⟮x⟯).wildExponent, mem_eisensteinBox_wildExponent_adjoin hn heis hxa⟩

/-- For `0 < n` and any additive Haar measure `μ` on `Fin n → K`, the union of the admissible
discriminant boxes agrees `μ`-almost everywhere with `eisensteinSet K n`. -/
theorem biUnion_eisensteinBox_ae_eq_eisensteinSet {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    (⋃ (j : ℕ) (_ : IsOreAdmissible K n j), eisensteinBox K n j) =ᵐ[μ] eisensteinSet K n := by
  have hunion : (⋃ (j : ℕ) (_ : IsOreAdmissible K n j), eisensteinBox K n j) =
      ⋃ j : ℕ, eisensteinBox K n j := by
    ext a
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨j, _, hj⟩ ↦ ⟨j, hj⟩, fun ⟨j, hj⟩ ↦ ⟨j, (mem_eisensteinBox.mp hj).2.1, hj⟩⟩
  rw [hunion, iUnion_eisensteinBox_eq hn]
  have hae := ae_separable_monicOfCoeff_restrict_eisensteinSet hn μ
  rw [ae_restrict_iff' measurableSet_eisensteinSet] at hae
  filter_upwards [hae] with a ha
  exact ⟨And.left, fun heis ↦ ⟨heis, ha heis⟩⟩

/-! ### Measurability and Haar volume of Krasner's discriminant box -/

/-- Expressing an admissible discriminant box as a set difference of boxes of maximal-ideal
powers. -/
private theorem eisensteinBox_eq_sdiff {n j : ℕ} (hn : 0 < n) (hadm : IsOreAdmissible K n j) :
    let d : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i
    let i₀ : Fin n := ⟨0, hn⟩
    let d₀ : Fin n → ℕ := Function.update d i₀ (d i₀ + 1)
    let B : (Fin n → ℕ) → Set (Fin n → K) :=
      fun e ↦ Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)
    eisensteinBox K n j =
      if _ : j % n = 0 then B d \ B d₀
      else
        let ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
        (B d \ B d₀) \ (B (Function.update d ib (d ib + 1)) \
          B (Function.update d₀ ib (d ib + 1))) := by
  intro d i₀ d₀ B
  split_ifs with hb0
  · ext a
    simp only [mem_eisensteinBox, hn, hadm, hb0, or_self, true_and, Set.mem_sdiff, B,
      Set.mem_univ_pi]
    refine and_congr_right fun hlow ↦ ⟨fun hhigh hB0 ↦ ?_, fun hnot i hi0 ↦ ?_⟩
    · apply hhigh i₀ rfl
      simpa [d₀, i₀, d] using hB0 i₀
    · have hi : i = i₀ := Fin.ext hi0
      subst hi
      intro ha0
      apply hnot
      intro k
      rcases eq_or_ne k i₀ with rfl | hne
      · simpa [d₀, i₀, d] using ha0
      · simpa [d₀, Function.update_of_ne hne] using hlow k
  · set ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
    have hib0 : ib ≠ i₀ := fun h ↦ hb0 (congrArg Fin.val h)
    ext a
    simp only [mem_eisensteinBox, hn, hadm, true_and, Set.mem_sdiff, B, Set.mem_univ_pi]
    constructor
    · rintro ⟨hlow, hhigh⟩
      refine ⟨⟨hlow, fun hB0 ↦ hhigh i₀ (Or.inl rfl) (by simpa [d₀, i₀, d] using hB0 i₀)⟩,
        fun ⟨hBb, _⟩ ↦ hhigh ib (Or.inr rfl) (by simpa [ib, d] using hBb ib)⟩
    · rintro ⟨⟨hlow, hnot0⟩, hnotb⟩
      refine ⟨hlow, fun i hi ↦ ?_⟩
      rcases hi with hi0 | hib
      · have h_eq : i = i₀ := Fin.ext hi0
        subst h_eq
        intro ha0
        refine hnot0 fun k ↦ ?_
        rcases eq_or_ne k i₀ with rfl | hne
        · simpa [d₀, i₀, d] using ha0
        · simpa [d₀, Function.update_of_ne hne] using hlow k
      · have h_eq : i = ib := Fin.ext hib
        subst h_eq
        intro hab
        refine hnotb ⟨fun k ↦ ?_, fun hB0b ↦ hnot0 fun k ↦ ?_⟩
        · rcases eq_or_ne k ib with rfl | hne
          · simpa [ib, d] using hab
          · simpa [Function.update_of_ne hne] using hlow k
        · rcases eq_or_ne k i₀ with rfl | hne
          · simpa [Function.update_of_ne hib0.symm] using hB0b i₀
          · simpa [d₀, Function.update_of_ne hne] using hlow k

/-- Every discriminant box `eisensteinBox K n j` is measurable. -/
theorem measurableSet_eisensteinBox (n j : ℕ) [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  by_cases hadm : IsOreAdmissible K n j
  · rw [eisensteinBox_eq_sdiff hn hadm]
    split_ifs
    · exact (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    · exact ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)).diff
        ((measurableSet_univ_pi_image_maximalIdeal_pow _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow _))
  · simp [eisensteinBox_eq_empty_of_not_isOreAdmissible hadm]

/-- Sum of `oreCoefficientDepth K n j i` over `Fin n` for `0 < n`. -/
private theorem sum_fin_oreCoefficientDepth {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (∑ i : Fin n, oreCoefficientDepth K n j i) =
      1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
  rw [Fin.sum_univ_eq_sum_range (fun h ↦ oreCoefficientDepth K n j h),
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn, oreCoefficientDepth_zero]

/-- Incrementing one coordinate of `e : Fin n → ℕ` by `1` increases `∑ i, e i` by `1`. -/
private theorem sum_update_add_one {n : ℕ} (e : Fin n → ℕ) (i₀ : Fin n) :
    (∑ i, Function.update e i₀ (e i₀ + 1) i) = (∑ i, e i) + 1 := by
  classical
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i₀) e (e i₀ + 1)
  have h2 := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i₀)
  rw [Finset.sdiff_singleton_eq_erase] at h1
  omega

/-- Volume of a single one-coordinate shell `B e \ B (update e i (e i + 1))`. -/
private theorem measure_univ_pi_sdiff_update {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) (e : Fin n → ℕ) (i₀ : Fin n) :
    μ ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) \
        Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update e i₀ (e i₀ + 1) i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, e i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set e' := Function.update e i₀ (e i₀ + 1)
  have hsub := univ_pi_image_maximalIdeal_pow_subset (K := K) (e' := e) (e := e')
    (le_update_iff.mpr ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, e' i = (∑ i, e i) + 1 := sum_update_add_one e i₀
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ e'
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [measure_sdiff hsub (measurableSet_univ_pi_image_maximalIdeal_pow e').nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂]
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.mpr (pow_ne_zero _ hq), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hq))
      (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]

/-- Inclusion of the excluded coordinate-`ib` sub-shell inside the coordinate-`i₀` shell. -/
private theorem sdiff_update_subset_sdiff {n : ℕ} (d : Fin n → ℕ) (i₀ ib : Fin n) :
    ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d ib (d ib + 1) i)) \
      Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) ''
        ↑(𝓂[K] ^ Function.update (Function.update d i₀ (d i₀ + 1)) ib (d ib + 1) i)) ⊆
    (Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) \
      Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d i₀ (d i₀ + 1) i) := by
  rintro a ⟨hdb, hnot⟩
  refine ⟨univ_pi_image_maximalIdeal_pow_subset
    (le_update_iff.mpr ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩) hdb, fun hd0 ↦ hnot fun k _ ↦ ?_⟩
  rcases eq_or_ne k ib with rfl | hkb
  · simpa using hdb k (Set.mem_univ _)
  · simpa [Function.update_of_ne hkb] using hd0 k (Set.mem_univ _)

/-- Outside Ore's admissible wild exponents, `eisensteinBox K n j` has measure zero. -/
theorem measure_eisensteinBox_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] (μ : Measure (Fin n → K)) :
    μ (eisensteinBox K n j) = 0 := by
  rw [eisensteinBox_eq_empty_of_not_isOreAdmissible h, measure_empty]

/-- **Haar volume of Krasner's discriminant box**: for `0 < n`, `IsOreAdmissible K n j`, and a
left-invariant measure `μ` normalized on `integerBox K (Fin n)`, the volume of `eisensteinBox K n j`
is `q ^ (-(1 + ∑_{1 ≤ h < n} ν_h)) * (1 - q⁻¹) * (if j % n = 0 then 1 else 1 - q⁻¹)`. -/
theorem measure_eisensteinBox {n j : ℕ} (hn : 0 < n) (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set d : Fin n → ℕ := fun i ↦ oreCoefficientDepth K n j i
  set i₀ : Fin n := ⟨0, hn⟩
  set d₀ : Fin n → ℕ := Function.update d i₀ (d i₀ + 1)
  have hsum_d : (∑ i, d i) = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h :=
    sum_fin_oreCoefficientDepth hn j
  rw [eisensteinBox_eq_sdiff hn hadm]
  split_ifs with hb0
  · rw [measure_univ_pi_sdiff_update μ hμ d i₀, hsum_d, mul_one]
  · set ib : Fin n := ⟨j % n, Nat.mod_lt j hn⟩
    have hib0 : ib ≠ i₀ := fun h ↦ hb0 (congrArg Fin.val h)
    set db : Fin n → ℕ := Function.update d ib (d ib + 1)
    have hcomm : Function.update d₀ ib (d ib + 1) = Function.update db i₀ (db i₀ + 1) := by
      ext k
      rcases eq_or_ne k i₀ with rfl | hk0
      · simp [d₀, db, Function.update_of_ne hib0.symm]
      · rcases eq_or_ne k ib with rfl | hkb
        · simp [db, Function.update_of_ne hib0]
        · simp [d₀, db, Function.update_of_ne hk0, Function.update_of_ne hkb]
    have hm1 := measure_univ_pi_sdiff_update μ hμ d i₀
    have hm2 := measure_univ_pi_sdiff_update μ hμ db i₀
    rw [← hcomm] at hm2
    have hmeas_shell : MeasurableSet
        ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ db i)) \
          Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d₀ ib (d ib + 1) i)) :=
      (measurableSet_univ_pi_image_maximalIdeal_pow _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow _)
    have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
    have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hu_top : 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hfin2 : μ ((Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ db i)) \
        Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ Function.update d₀ ib (d ib + 1) i)) ≠ ⊤ :=
      hm2 ▸ ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)) hu_top
    rw [measure_sdiff (sdiff_update_subset_sdiff d i₀ ib) hmeas_shell.nullMeasurableSet hfin2,
      hm1, hm2, sum_update_add_one d ib, hsum_d]
    set S := 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    have hinv_top : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)) hu_top
    have hstep : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (S + 1) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
      simp only [one_div, pow_succ,
        ENNReal.mul_inv (.inl (pow_ne_zero _ hq)) (.inl (ENNReal.pow_ne_top hqt))]
      ring
    rw [hstep]
    conv_lhs => enter [1]; rw [← mul_one (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ S * _)]
    rw [← ENNReal.mul_sub fun _ _ ↦ hinv_top]

end TauCeti
