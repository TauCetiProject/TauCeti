/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import TauCeti.RingTheory.Valuation.Integers
public import TauCeti.RingTheory.Valuation.Continuous.Adic
public import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# Gauss valuations on Witt vectors

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`; for instance the ring of integers `𝒪_F` of a perfect nonarchimedean field `F`
of characteristic `p`, so that `𝕎 O = A_inf`. Write a Witt vector as its Teichmüller expansion
`x = ∑ₙ [xₙ] pⁿ` (`WittVector.teichmullerCoeff`). For `ρ < 1` the *Gauss valuation*

```text
λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ
```

is a valuation on `𝕎 O`. It takes the value `v(a) ρ ^ m` on `[a] p ^ m`, so `λ_ρ(p) = ρ` and
`λ_ρ([a]) = v(a)`, and for `0 < ρ` it vanishes only at `0`. These are the rank-one valuations from
which the Gauss points of `Spa(A_inf, A_inf)` and the norms of the interval rings of the
Fargues–Fontaine curve are built.

The ultrametric inequality rests on a description of the ideals `([c], p ^ (n + 1))` of `𝕎 O`:
they consist exactly of the Witt vectors whose first `n + 1` Teichmüller coordinates have valuation
at most `v(c)` (`Valuation.Integers.mem_span_teichmuller_pow_iff`), which uses that `O` is a
valuation ring. Multiplicativity follows by comparing the leading Teichmüller terms of a product
modulo a suitable power of `p`.

## Main definitions

* `TauCeti.WittVector.gaussValuation` : the Gauss valuation `λ_ρ` on `𝕎 O`.
* `TauCeti.WittVector.gaussDegree` : Kedlaya's degree for `λ_ρ`, the largest index `d` with
  `v(x_d) ρ ^ d = λ_ρ(x)`.

## Main results

* `Valuation.Integers.mem_span_teichmuller_pow_iff` : the ideal `([c], p ^ (n + 1))` in terms of
  Teichmüller coordinates.
* `TauCeti.WittVector.gaussValuation_apply` : `λ_ρ(x) = supₙ v(xₙ) ρⁿ`.
* `TauCeti.WittVector.gaussValuation_teichmuller_mul_pow` : `λ_ρ([a] p ^ m) = v(a) ρ ^ m`.
* `TauCeti.WittVector.gaussValuation_eq_zero_iff` : for `0 < ρ`, `λ_ρ` vanishes only at `0`.
* `TauCeti.WittVector.gaussValuation_pos` : for `0 < ρ`, `λ_ρ` is positive away from `0`.
* `TauCeti.WittVector.gaussValuation_teichmuller_add_teichmuller_sub_le` : Teichmüller
  representatives are additive up to multiples of `p`, with
  `λ_ρ([a] + [b] - [a + b]) ≤ ρ max (v(a), v(b))`.
* `TauCeti.WittVector.isContinuous_gaussValuation` : if `v(ϖ) < 1`, then `λ_ρ` is continuous for
  the `(p, [ϖ])`-adic topology.
* `TauCeti.WittVector.eventually_gaussValuation_eq_mul_pow_gaussDegree` : for `ρ'` slightly larger
  than `ρ`, `λ_ρ'(x) = v(x_d) ρ' ^ d` for the degree `d` of `x` for `λ_ρ`.
* `TauCeti.WittVector.gaussDegree_eq_of_gaussValuation_sub_lt` : the degree only depends on the
  leading part (Kedlaya, Remark 2.7).
* `TauCeti.WittVector.gaussDegree_mul` : the degree is additive on products (Kedlaya, Lemma 2.6).

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1, for the Gauss norms on `A_inf`.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors*, Nagoya Math. J. 209 (2013).
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Definition 2.5, Lemma 2.6 and Remark 2.7, for the degree.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

open scoped NNReal

namespace Valuation.Integers

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
  {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}
  [Algebra R K]

local notation "𝕎" => WittVector p

/-- Let `R` be the ring of integers of a valuation `v`. Then the ideal `([c], p ^ (n + 1))` of
`𝕎 R` consists exactly of the Witt vectors whose first `n + 1` Teichmüller coordinates have
valuation at most `v(c)`. -/
theorem mem_span_teichmuller_pow_iff (hv : v.Integers R) {c : R} {x : 𝕎 R} {n : ℕ} :
    x ∈ Ideal.span {teichmuller p c, (p : 𝕎 R) ^ (n + 1)} ↔
      ∀ i ≤ n, v (algebraMap R K (x.teichmullerCoeff i)) ≤ v (algebraMap R K c) := by
  refine ⟨fun hx i hi ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    rw [teichmullerCoeff_eq_of_dvd_sub (y := teichmuller p c * a) ⟨b, by ring⟩ hi,
      teichmullerCoeff_teichmuller_mul, map_mul, map_mul]
    exact mul_le_of_le_one_right' (hv.map_le_one _)
  · choose u hu using fun i : Finset.Iic n ↦
      hv.dvd_of_le (hx i (Finset.mem_Iic.mp i.2))
    obtain ⟨d, hd⟩ := pow_dvd_sub_sum_teichmullerCoeff x n
    refine Ideal.mem_span_pair.mpr ⟨∑ i : Finset.Iic n, teichmuller p (u i) * (p : 𝕎 R) ^ i.1,
      d, ?_⟩
    rw [sub_eq_iff_eq_add] at hd
    rw [hd, ← Finset.sum_coe_sort (Finset.Iic n), Finset.sum_mul, add_comm]
    simp only [hu, map_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun _ _ ↦ by ring

end Valuation.Integers

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K] [CharP O p]
  [PerfectRing O p] {v : Valuation K ℝ≥0} {ρ : ℝ≥0}

local notation "𝕎" => _root_.WittVector p

/-- The weighted valuation `v(xᵢ) ρⁱ` of the `i`-th Teichmüller coordinate. -/
private noncomputable def gaussTerm (v : Valuation K ℝ≥0) (ρ : ℝ≥0) (x : 𝕎 O) (i : ℕ) : ℝ≥0 :=
  v (algebraMap O K (x.teichmullerCoeff i)) * ρ ^ i

/-- The truncated Gauss norm `max_{i ≤ n} v(xᵢ) ρⁱ`, which only depends on `x` modulo
`p ^ (n + 1)`. -/
private noncomputable def gaussTrunc (v : Valuation K ℝ≥0) (ρ : ℝ≥0) (n : ℕ) (x : 𝕎 O) : ℝ≥0 :=
  (Finset.Iic n).sup (gaussTerm p v ρ x)

variable {p}

private theorem gaussTerm_le_gaussTrunc (x : 𝕎 O) {i n : ℕ} (hi : i ≤ n) :
    gaussTerm p v ρ x i ≤ gaussTrunc p v ρ n x :=
  Finset.le_sup (f := gaussTerm p v ρ x) (Finset.mem_Iic.mpr hi)

private theorem gaussTrunc_mono (x : 𝕎 O) {m n : ℕ} (h : m ≤ n) :
    gaussTrunc p v ρ m x ≤ gaussTrunc p v ρ n x :=
  Finset.sup_mono (Finset.Iic_subset_Iic.mpr h)

private theorem gaussTrunc_congr {x y : 𝕎 O} {n : ℕ} (h : (p : 𝕎 O) ^ (n + 1) ∣ x - y) :
    gaussTrunc p v ρ n x = gaussTrunc p v ρ n y :=
  Finset.sup_congr rfl fun i hi ↦ by
    rw [gaussTerm, gaussTerm, teichmullerCoeff_eq_of_dvd_sub h (Finset.mem_Iic.mp hi)]

private theorem gaussTerm_teichmuller_mul_pow (a : O) (m i : ℕ) :
    gaussTerm p v ρ (teichmuller p a * (p : 𝕎 O) ^ m) i =
      if i = m then v (algebraMap O K a) * ρ ^ m else 0 := by
  rw [gaussTerm, teichmullerCoeff_teichmuller_mul_pow]
  split_ifs with h <;> simp [h]

private theorem gaussTrunc_teichmuller_mul_pow (a : O) (m n : ℕ) :
    gaussTrunc p v ρ n (teichmuller p a * (p : 𝕎 O) ^ m) =
      if m ≤ n then v (algebraMap O K a) * ρ ^ m else 0 := by
  refine le_antisymm (Finset.sup_le fun i hi ↦ ?_) ?_
  · rw [gaussTerm_teichmuller_mul_pow]
    split_ifs with h₁ h₂ <;> simp_all
  · split_ifs with h
    · simpa [gaussTerm_teichmuller_mul_pow] using
        gaussTerm_le_gaussTrunc (v := v) (ρ := ρ) (teichmuller p a * (p : 𝕎 O) ^ m) h
    · exact zero_le

private theorem gaussTrunc_zero (n : ℕ) : gaussTrunc p v ρ n (0 : 𝕎 O) = 0 := by
  simpa using gaussTrunc_teichmuller_mul_pow (p := p) (v := v) (ρ := ρ) (0 : O) 0 n

/-- An index `i ≤ k` at which the Teichmüller coordinates `x₀, …, x_k` have maximal valuation. -/
private theorem exists_le_forall_le (x : 𝕎 O) (k : ℕ) :
    ∃ i ≤ k, ∀ j ≤ k, v (algebraMap O K (x.teichmullerCoeff j)) ≤
      v (algebraMap O K (x.teichmullerCoeff i)) := by
  obtain ⟨i, hi, h⟩ := (Finset.Iic k).exists_max_image
    (fun j ↦ v (algebraMap O K (x.teichmullerCoeff j))) ⟨0, Finset.mem_Iic.mpr k.zero_le⟩
  exact ⟨i, Finset.mem_Iic.mp hi, fun j hj ↦ h j (Finset.mem_Iic.mpr hj)⟩

/-- **The ultrametric inequality for truncated Gauss norms**, for every element of the ideal
generated by `x` and `y`. -/
private theorem gaussTrunc_le_of_mem_span (hv : v.Integers O) (hρ : ρ ≤ 1) {x y z : 𝕎 O}
    (hz : z ∈ Ideal.span {x, y}) (n : ℕ) :
    gaussTrunc p v ρ n z ≤ max (gaussTrunc p v ρ n x) (gaussTrunc p v ρ n y) := by
  refine Finset.sup_le fun k hk ↦ ?_
  replace hk := Finset.mem_Iic.mp hk
  refine le_trans ?_ (max_le_max (gaussTrunc_mono x hk) (gaussTrunc_mono y hk))
  clear hk
  obtain ⟨i, hi, hix⟩ := exists_le_forall_le (v := v) x k
  obtain ⟨j, hj, hjy⟩ := exists_le_forall_le (v := v) y k
  wlog h : v (algebraMap O K (x.teichmullerCoeff i)) ≤ v (algebraMap O K (y.teichmullerCoeff j))
    generalizing x y i j
  · rw [max_comm]
    exact this (by rwa [Set.pair_comm]) j hj hjy i hi hix (le_of_not_ge h)
  -- Both `x` and `y`, hence `z`, lie in the ideal `([y_j], p ^ (k + 1))`.
  have hle : Ideal.span {x, y} ≤
      Ideal.span {teichmuller p (y.teichmullerCoeff j), (p : 𝕎 O) ^ (k + 1)} := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hv.mem_span_teichmuller_pow_iff.mpr fun l hl ↦ (hix l hl).trans h,
      hv.mem_span_teichmuller_pow_iff.mpr hjy⟩
  calc gaussTerm p v ρ z k
      ≤ v (algebraMap O K (y.teichmullerCoeff j)) * ρ ^ j :=
        mul_le_mul' (hv.mem_span_teichmuller_pow_iff.mp (hle hz) k le_rfl)
          (pow_le_pow_of_le_one zero_le hρ hj)
    _ ≤ gaussTrunc p v ρ k y := gaussTerm_le_gaussTrunc y hj
    _ ≤ _ := le_max_right _ _

private theorem gaussTrunc_add_le (hv : v.Integers O) (hρ : ρ ≤ 1) (x y : 𝕎 O) (n : ℕ) :
    gaussTrunc p v ρ n (x + y) ≤ max (gaussTrunc p v ρ n x) (gaussTrunc p v ρ n y) :=
  gaussTrunc_le_of_mem_span hv hρ (Ideal.add_mem _ (Ideal.subset_span (by simp))
    (Ideal.subset_span (by simp))) n

private theorem gaussTrunc_neg_le (hv : v.Integers O) (hρ : ρ ≤ 1) (x : 𝕎 O) (n : ℕ) :
    gaussTrunc p v ρ n (-x) ≤ gaussTrunc p v ρ n x := by
  simpa using gaussTrunc_le_of_mem_span (y := x) hv hρ
    (neg_mem (Ideal.subset_span (Set.mem_insert x _))) n

private theorem gaussTrunc_sum_le (hv : v.Integers O) (hρ : ρ ≤ 1) {ι : Type*} (s : Finset ι)
    (f : ι → 𝕎 O) (n : ℕ) :
    gaussTrunc p v ρ n (∑ i ∈ s, f i) ≤ s.sup fun i ↦ gaussTrunc p v ρ n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussTrunc_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact (gaussTrunc_add_le hv hρ _ _ n).trans (max_le_max le_rfl ih)

/-- Modulo `p ^ (n + 1)`, the product `x y` is `∑_{i, j ≤ n} [xᵢ yⱼ] p ^ (i + j)`. -/
private theorem pow_dvd_mul_sub_sum (x y : 𝕎 O) (n : ℕ) :
    (p : 𝕎 O) ^ (n + 1) ∣ x * y - ∑ ij ∈ Finset.Iic n ×ˢ Finset.Iic n,
      teichmuller p (x.teichmullerCoeff ij.1 * y.teichmullerCoeff ij.2) *
        (p : 𝕎 O) ^ (ij.1 + ij.2) := by
  have hx := pow_dvd_sub_sum_teichmullerCoeff x n
  have hy := pow_dvd_sub_sum_teichmullerCoeff y n
  set X := ∑ i ≤ n, teichmuller p (x.teichmullerCoeff i) * (p : 𝕎 O) ^ i
  set Y := ∑ j ≤ n, teichmuller p (y.teichmullerCoeff j) * (p : 𝕎 O) ^ j
  have hXY : ∑ ij ∈ Finset.Iic n ×ˢ Finset.Iic n,
      teichmuller p (x.teichmullerCoeff ij.1 * y.teichmullerCoeff ij.2) *
        (p : 𝕎 O) ^ (ij.1 + ij.2) = X * Y := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [map_mul, pow_add]
      ring
  -- Split the difference of products into differences of factors.
  have hsplit : x * y - X * Y = x * (y - Y) + (x - X) * Y := by ring
  rw [hXY, hsplit]
  exact dvd_add (hy.mul_left x) (hx.mul_right Y)

/-- The weighted valuation of the product term `[xᵢ yⱼ] p ^ (i + j)`. -/
private theorem gaussTerm_mul_gaussTerm (x y : 𝕎 O) (i j : ℕ) :
    v (algebraMap O K (x.teichmullerCoeff i * y.teichmullerCoeff j)) * ρ ^ (i + j) =
      gaussTerm p v ρ x i * gaussTerm p v ρ y j := by
  rw [gaussTerm, gaussTerm, map_mul, map_mul, pow_add]
  ring

private theorem gaussTrunc_mul_le (hv : v.Integers O) (hρ : ρ ≤ 1) (x y : 𝕎 O) (n : ℕ) :
    gaussTrunc p v ρ n (x * y) ≤ gaussTrunc p v ρ n x * gaussTrunc p v ρ n y := by
  rw [gaussTrunc_congr (pow_dvd_mul_sub_sum x y n)]
  refine (gaussTrunc_sum_le hv hρ _ _ n).trans (Finset.sup_le fun ij hij ↦ ?_)
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  rw [gaussTrunc_teichmuller_mul_pow]
  split_ifs
  · rw [gaussTerm_mul_gaussTerm]
    exact mul_le_mul' (gaussTerm_le_gaussTrunc x (Finset.mem_Iic.mp hi))
      (gaussTerm_le_gaussTrunc y (Finset.mem_Iic.mp hj))
  · exact zero_le

private theorem gaussTerm_le_one (hv : v.Integers O) (hρ : ρ ≤ 1) (x : 𝕎 O) (i : ℕ) :
    gaussTerm p v ρ x i ≤ 1 :=
  mul_le_one' (hv.map_le_one _) (pow_le_one₀ zero_le hρ)

private theorem bddAbove_range_gaussTerm (hv : v.Integers O) (hρ : ρ ≤ 1) (x : 𝕎 O) :
    BddAbove (Set.range (gaussTerm p v ρ x)) :=
  ⟨1, Set.forall_mem_range.mpr (gaussTerm_le_one hv hρ x)⟩

/-- For `ρ < 1` the weighted valuations `v(xᵢ) ρⁱ` attain their supremum; we take the first
index `i₀` where they do. -/
private theorem exists_isGreatest_gaussTerm (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) :
    ∃ i₀, (∀ i, gaussTerm p v ρ x i ≤ gaussTerm p v ρ x i₀) ∧
      ∀ i < i₀, gaussTerm p v ρ x i < gaussTerm p v ρ x i₀ := by
  classical
  have hex : ∃ i₀, ∀ i, gaussTerm p v ρ x i ≤ gaussTerm p v ρ x i₀ := by
    by_cases h : ∀ i, gaussTerm p v ρ x i = 0
    · exact ⟨0, fun i ↦ by simp [h]⟩
    push Not at h
    obtain ⟨k, hk⟩ := h
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr hk) hρ
    -- Every term of index at least `N` is at most `ρ ^ N`, hence smaller than the `k`-th one.
    have hlt : ∀ i, N ≤ i → gaussTerm p v ρ x i < gaussTerm p v ρ x k := fun i hi ↦
      ((mul_le_of_le_one_left' (hv.map_le_one _)).trans
        (pow_le_pow_of_le_one zero_le hρ.le hi)).trans_lt hN
    have hkN : k < N := not_le.mp fun h ↦ (hlt k h).false
    obtain ⟨i₀, -, h⟩ := (Finset.range N).exists_max_image (gaussTerm p v ρ x)
      ⟨k, Finset.mem_range.mpr hkN⟩
    refine ⟨i₀, fun i ↦ ?_⟩
    rcases lt_or_ge i N with hi | hi
    · exact h i (Finset.mem_range.mpr hi)
    · exact (hlt i hi).le.trans (h k (Finset.mem_range.mpr hkN))
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi ↦ (Nat.find_spec hex i).lt_of_ne
    fun h ↦ Nat.find_min hex hi fun j ↦ (Nat.find_spec hex j).trans h.ge⟩

variable (p) in
/-- The Gauss norm `supᵢ v(xᵢ) ρⁱ`. -/
private noncomputable def gaussSup (v : Valuation K ℝ≥0) (ρ : ℝ≥0) (x : 𝕎 O) : ℝ≥0 :=
  ⨆ i, gaussTerm p v ρ x i

private theorem gaussTrunc_le_gaussSup (hv : v.Integers O) (hρ : ρ ≤ 1) (x : 𝕎 O) (n : ℕ) :
    gaussTrunc p v ρ n x ≤ gaussSup p v ρ x :=
  Finset.sup_le fun i _ ↦ le_ciSup (bddAbove_range_gaussTerm hv hρ x) i

private theorem gaussSup_eq_gaussTerm (hv : v.Integers O) (hρ : ρ ≤ 1) {x : 𝕎 O} {i₀ : ℕ}
    (h : ∀ i, gaussTerm p v ρ x i ≤ gaussTerm p v ρ x i₀) :
    gaussSup p v ρ x = gaussTerm p v ρ x i₀ :=
  le_antisymm (ciSup_le h) (le_ciSup (bddAbove_range_gaussTerm hv hρ x) i₀)

private theorem gaussSup_teichmuller_mul_pow (hv : v.Integers O) (hρ : ρ ≤ 1) (a : O) (m : ℕ) :
    gaussSup p v ρ (teichmuller p a * (p : 𝕎 O) ^ m) = v (algebraMap O K a) * ρ ^ m := by
  rw [gaussSup_eq_gaussTerm hv hρ (i₀ := m) fun i ↦ ?_, gaussTerm_teichmuller_mul_pow,
    ite_eq_left rfl]
  rw [gaussTerm_teichmuller_mul_pow, gaussTerm_teichmuller_mul_pow, ite_eq_left rfl]
  split_ifs <;> simp_all

private theorem gaussSup_add_le (hv : v.Integers O) (hρ : ρ ≤ 1) (x y : 𝕎 O) :
    gaussSup p v ρ (x + y) ≤ max (gaussSup p v ρ x) (gaussSup p v ρ y) :=
  ciSup_le fun i ↦ (gaussTerm_le_gaussTrunc _ le_rfl).trans <|
    (gaussTrunc_add_le hv hρ x y i).trans <|
      max_le_max (gaussTrunc_le_gaussSup hv hρ x i) (gaussTrunc_le_gaussSup hv hρ y i)

private theorem gaussSup_mul_le (hv : v.Integers O) (hρ : ρ ≤ 1) (x y : 𝕎 O) :
    gaussSup p v ρ (x * y) ≤ gaussSup p v ρ x * gaussSup p v ρ y :=
  ciSup_le fun i ↦ (gaussTerm_le_gaussTrunc _ le_rfl).trans <|
    (gaussTrunc_mul_le hv hρ x y i).trans <|
      mul_le_mul' (gaussTrunc_le_gaussSup hv hρ x i) (gaussTrunc_le_gaussSup hv hρ y i)

/-- The reverse inequality: modulo `p ^ (i₀ + j₀ + 1)`, where `i₀` and `j₀` are the first indices
at which the Gauss norms of `x` and `y` are attained, `x y` is the leading term
`[x_{i₀} y_{j₀}] p ^ (i₀ + j₀)` plus terms of strictly smaller truncated Gauss norm. -/
private theorem gaussSup_mul_le_gaussSup_mul (hv : v.Integers O) (hρ : ρ < 1) (x y : 𝕎 O) :
    gaussSup p v ρ x * gaussSup p v ρ y ≤ gaussSup p v ρ (x * y) := by
  obtain ⟨i₀, hi₀, hi₀'⟩ := exists_isGreatest_gaussTerm hv hρ x
  obtain ⟨j₀, hj₀, hj₀'⟩ := exists_isGreatest_gaussTerm hv hρ y
  rw [gaussSup_eq_gaussTerm hv hρ.le hi₀, gaussSup_eq_gaussTerm hv hρ.le hj₀]
  rcases eq_zero_or_pos (gaussTerm p v ρ x i₀ * gaussTerm p v ρ y j₀) with hM | hM
  · rw [hM]
    exact zero_le
  have hx₀ : 0 < gaussTerm p v ρ x i₀ := pos_of_mul_pos_left hM zero_le
  have hy₀ : 0 < gaussTerm p v ρ y j₀ := pos_of_mul_pos_right hM zero_le
  set n := i₀ + j₀
  let f : ℕ × ℕ → 𝕎 O := fun ij ↦
    teichmuller p (x.teichmullerCoeff ij.1 * y.teichmullerCoeff ij.2) * (p : 𝕎 O) ^ (ij.1 + ij.2)
  have hmem : (i₀, j₀) ∈ Finset.Iic n ×ˢ Finset.Iic n := by
    simp [n]
  set S := ∑ ij ∈ (Finset.Iic n ×ˢ Finset.Iic n).erase (i₀, j₀), f ij
  -- Every term other than the leading one has truncated Gauss norm below the product.
  have hS : gaussTrunc p v ρ n S < gaussTerm p v ρ x i₀ * gaussTerm p v ρ y j₀ := by
    refine (gaussTrunc_sum_le hv hρ.le _ _ n).trans_lt ((Finset.sup_lt_iff hM).mpr fun ij hij ↦ ?_)
    obtain ⟨hne, -⟩ := Finset.mem_erase.mp hij
    rw [gaussTrunc_teichmuller_mul_pow]
    split_ifs with hle
    · rw [gaussTerm_mul_gaussTerm]
      -- A non-leading index pair within `Iic n ×ˢ Iic n`, where `n = i₀ + j₀`, has a coordinate
      -- before the corresponding first maximiser.
      have hidx : ij.1 < i₀ ∨ ij.2 < j₀ := by
        by_contra! h
        exact hne (Prod.ext (by omega) (by omega))
      rcases hidx with h | h
      · exact (mul_le_mul' le_rfl (hj₀ _)).trans_lt (mul_lt_mul_of_pos_right (hi₀' _ h) hy₀)
      · exact (mul_le_mul' (hi₀ _) le_rfl).trans_lt (mul_lt_mul_of_pos_left (hj₀' _ h) hx₀)
    · exact hM
  have hT : gaussTerm p v ρ x i₀ * gaussTerm p v ρ y j₀ ≤ gaussTrunc p v ρ n (f (i₀, j₀)) := by
    rw [gaussTrunc_teichmuller_mul_pow, ite_eq_left le_rfl, gaussTerm_mul_gaussTerm]
  have hxy : gaussTrunc p v ρ n (x * y) = gaussTrunc p v ρ n (f (i₀, j₀) + S) := by
    rw [gaussTrunc_congr (pow_dvd_mul_sub_sum x y n), Finset.add_sum_erase _ _ hmem]
  -- The leading term is the sum of `f (i₀, j₀) + S` and `-S`, the latter being small.
  have key := hT.trans <| (add_neg_cancel_right (f (i₀, j₀)) S) ▸
    gaussTrunc_add_le hv hρ.le (f (i₀, j₀) + S) (-S) n
  rcases le_max_iff.mp key with h | h
  · exact h.trans (hxy ▸ gaussTrunc_le_gaussSup hv hρ.le (x * y) n)
  · exact absurd ((gaussTrunc_neg_le hv hρ.le S n).trans_lt hS) h.not_gt

variable (p) in
/-- **The Gauss valuation** `λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ` on the Witt vectors of the ring of
integers `O` of a valuation `v : Valuation K ℝ≥0`, for `O` perfect of characteristic `p` and
`ρ < 1`. -/
noncomputable def gaussValuation (hv : v.Integers O) (ρ : ℝ≥0) (hρ : ρ < 1) :
    Valuation (𝕎 O) ℝ≥0 where
  toFun := gaussSup p v ρ
  map_zero' := by simpa using gaussSup_teichmuller_mul_pow (p := p) hv hρ.le 0 0
  map_one' := by simpa using gaussSup_teichmuller_mul_pow (p := p) hv hρ.le 1 0
  map_mul' x y :=
    le_antisymm (gaussSup_mul_le hv hρ.le x y) (gaussSup_mul_le_gaussSup_mul hv hρ x y)
  map_add_le_max' := gaussSup_add_le hv hρ.le

/-- The Gauss valuation is the supremum of the weighted valuations of the Teichmüller
coordinates. -/
theorem gaussValuation_apply (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) :
    gaussValuation p hv ρ hρ x = ⨆ n, v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n :=
  (rfl)

/-- Each weighted valuation `v(xₙ) ρⁿ` of a Teichmüller coordinate is bounded by the Gauss
valuation. -/
theorem le_gaussValuation (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) (n : ℕ) :
    v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n ≤ gaussValuation p hv ρ hρ x :=
  le_ciSup (bddAbove_range_gaussTerm hv hρ.le x) n

/-- Increasing the radius increases the Gauss valuation of a Witt vector. -/
theorem gaussValuation_mono (hv : v.Integers O) {ρ₁ ρ₂ : ℝ≥0}
    (hρ₁ : ρ₁ < 1) (hρ₂ : ρ₂ < 1) (hρ : ρ₁ ≤ ρ₂) (x : 𝕎 O) :
    gaussValuation p hv ρ₁ hρ₁ x ≤ gaussValuation p hv ρ₂ hρ₂ x := by
  rw [gaussValuation_apply]
  exact ciSup_le fun n ↦ (mul_le_mul' le_rfl (pow_le_pow_left' hρ n)).trans
    (le_gaussValuation hv hρ₂ x n)

/-- **The Hadamard three circles inequality for Gauss valuations.** For radii
`0 < ρ₁ ≤ ρ ≤ ρ₂` and `m : ℕ`, the value `λ_ρ(x) / ρ ^ m`, which is the Gauss valuation at `ρ` of
`x / p ^ m` once `p` is inverted, is at most the larger of its values at `ρ₁` and `ρ₂`: each term
`v(xₙ) ρ ^ (n - m)` is monotone in `ρ`, increasing if `m ≤ n` and decreasing otherwise. -/
theorem gaussValuation_mul_inv_pow_le_max (hv : v.Integers O) {ρ₁ ρ₂ : ℝ≥0} (hρ : ρ < 1)
    (hρ₁ : ρ₁ < 1) (hρ₂ : ρ₂ < 1) (h₀ : 0 < ρ₁) (h₁ : ρ₁ ≤ ρ) (h₂ : ρ ≤ ρ₂) (x : 𝕎 O) (m : ℕ) :
    gaussValuation p hv ρ hρ x * (ρ ^ m)⁻¹ ≤
      max (gaussValuation p hv ρ₁ hρ₁ x * (ρ₁ ^ m)⁻¹)
        (gaussValuation p hv ρ₂ hρ₂ x * (ρ₂ ^ m)⁻¹) := by
  rw [gaussValuation_apply, NNReal.iSup_mul]
  refine ciSup_le fun n ↦ ?_
  rw [mul_assoc]
  rcases le_or_gt m n with hmn | hnm
  · -- `ρ ^ n / ρ ^ m = ρ ^ (n - m)` is at most `ρ₂ ^ (n - m)`
    refine le_max_of_le_right ?_
    rw [← pow_sub₀ _ (h₀.trans_le h₁).ne' hmn]
    calc v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ (n - m)
        ≤ v (algebraMap O K (x.teichmullerCoeff n)) * ρ₂ ^ (n - m) := by gcongr
      _ = v (algebraMap O K (x.teichmullerCoeff n)) * ρ₂ ^ n * (ρ₂ ^ m)⁻¹ := by
        rw [pow_sub₀ _ (h₀.trans_le (h₁.trans h₂)).ne' hmn, mul_assoc]
      _ ≤ _ := by gcongr; exact le_gaussValuation hv hρ₂ x n
  · -- `ρ ^ n / ρ ^ m = (ρ ^ (m - n))⁻¹` is at most `(ρ₁ ^ (m - n))⁻¹`
    refine le_max_of_le_left ?_
    have hρ₀ : 0 < ρ := h₀.trans_le h₁
    have key (r : ℝ≥0) (hr : 0 < r) : r ^ n * (r ^ m)⁻¹ = (r ^ (m - n))⁻¹ := by
      rw [pow_sub₀ _ hr.ne' hnm.le, mul_inv, inv_inv, mul_comm]
    calc v (algebraMap O K (x.teichmullerCoeff n)) * (ρ ^ n * (ρ ^ m)⁻¹)
        ≤ v (algebraMap O K (x.teichmullerCoeff n)) * (ρ₁ ^ n * (ρ₁ ^ m)⁻¹) := by
          rw [key ρ hρ₀, key ρ₁ h₀]
          gcongr
      _ = v (algebraMap O K (x.teichmullerCoeff n)) * ρ₁ ^ n * (ρ₁ ^ m)⁻¹ := (mul_assoc ..).symm
      _ ≤ _ := by gcongr; exact le_gaussValuation hv hρ₁ x n

/-- The Gauss valuation is at most one. -/
theorem gaussValuation_le_one (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) :
    gaussValuation p hv ρ hρ x ≤ 1 :=
  ciSup_le (gaussTerm_le_one hv hρ.le x)

/-- The Gauss valuation of `[a] p ^ m` is `v(a) ρ ^ m`. -/
@[simp]
theorem gaussValuation_teichmuller_mul_pow (hv : v.Integers O) (hρ : ρ < 1) (a : O) (m : ℕ) :
    gaussValuation p hv ρ hρ (teichmuller p a * (p : 𝕎 O) ^ m) = v (algebraMap O K a) * ρ ^ m :=
  gaussSup_teichmuller_mul_pow hv hρ.le a m

/-- The Gauss valuation of a Teichmüller representative `[a]` is `v(a)`. -/
@[simp]
theorem gaussValuation_teichmuller (hv : v.Integers O) (hρ : ρ < 1) (a : O) :
    gaussValuation p hv ρ hρ (teichmuller p a) = v (algebraMap O K a) := by
  simpa using gaussValuation_teichmuller_mul_pow (p := p) hv hρ a 0

/-- The Gauss valuation of `p` is `ρ`. -/
@[simp]
theorem gaussValuation_p (hv : v.Integers O) (hρ : ρ < 1) :
    gaussValuation p hv ρ hρ (p : 𝕎 O) = ρ := by
  simpa using gaussValuation_teichmuller_mul_pow (p := p) hv hρ 1 1

/-- In the splitting `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ b` of the Teichmüller expansion
(`WittVector.exists_eq_sum_teichmullerCoeff_add_pow_mul`), the tail satisfies
`λ_ρ(b) ρᵐ ≤ λ_ρ(y)`. -/
theorem gaussValuation_mul_pow_le_of_eq_sum_add_pow_mul (hv : v.Integers O) (hρ : ρ < 1)
    {y b : 𝕎 O} {m : ℕ}
    (hb : y = ∑ i ∈ Finset.range m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i +
      (p : 𝕎 O) ^ m * b) :
    gaussValuation p hv ρ hρ b * ρ ^ m ≤ gaussValuation p hv ρ hρ y := by
  have hsum : gaussValuation p hv ρ hρ
      (∑ i ∈ Finset.range m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i) ≤
        gaussValuation p hv ρ hρ y :=
    Valuation.map_sum_le _ fun i _ ↦ by
      rw [gaussValuation_teichmuller_mul_pow]
      exact le_gaussValuation hv hρ y i
  have h : (p : 𝕎 O) ^ m * b =
      y - ∑ i ∈ Finset.range m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i :=
    eq_sub_iff_add_eq'.mpr hb.symm
  calc gaussValuation p hv ρ hρ b * ρ ^ m = gaussValuation p hv ρ hρ ((p : 𝕎 O) ^ m * b) := by
        rw [map_mul, map_pow, gaussValuation_p, mul_comm]
    _ ≤ _ := h ▸ (Valuation.map_sub _ _ _).trans (max_le le_rfl hsum)

/-- A Witt vector whose `0`-th coordinate vanishes, that is, a multiple of `p`, has Gauss
valuation at most `ρ`. -/
theorem gaussValuation_le_of_coeff_zero_eq_zero (hv : v.Integers O) (hρ : ρ < 1) {x : 𝕎 O}
    (hx : x.coeff 0 = 0) : gaussValuation p hv ρ hρ x ≤ ρ := by
  rw [gaussValuation_apply]
  refine ciSup_le fun n ↦ ?_
  rcases n with _ | n
  · simp [hx]
  · exact (mul_le_of_le_one_left' (hv.map_le_one _)).trans
      (pow_le_of_le_one zero_le hρ.le n.succ_ne_zero)

/-- **Teichmüller representatives are additive up to `p`**, quantitatively:
`λ_ρ([a] + [b] - [a + b]) ≤ ρ max (v(a), v(b))`. -/
theorem gaussValuation_teichmuller_add_teichmuller_sub_le (hv : v.Integers O) (hρ : ρ < 1)
    (a b : O) :
    gaussValuation p hv ρ hρ (teichmuller p a + teichmuller p b - teichmuller p (a + b)) ≤
      ρ * max (v (algebraMap O K a)) (v (algebraMap O K b)) := by
  wlog h : v (algebraMap O K b) ≤ v (algebraMap O K a) generalizing a b
  · rw [max_comm, add_comm (teichmuller p a), add_comm a]
    exact this b a (le_of_not_ge h)
  obtain ⟨t, rfl⟩ := hv.dvd_of_le h
  -- `[a] + [a t] - [a + a t] = [a] (1 + [t] - [1 + t])`, and the second factor is a multiple of
  -- `p`.
  have he : (1 + teichmuller p t - teichmuller p (1 + t)).coeff 0 = 0 := by
    rw [← constantCoeff_apply, map_sub, map_add, map_one, constantCoeff_apply,
      constantCoeff_apply, teichmuller_coeff_zero, teichmuller_coeff_zero, sub_self]
  have hfac : teichmuller p a + teichmuller p (a * t) - teichmuller p (a + a * t) =
      teichmuller p a * (1 + teichmuller p t - teichmuller p (1 + t)) := by
    rw [← mul_one_add a t, map_mul, map_mul]
    ring
  rw [hfac, map_mul, gaussValuation_teichmuller, max_eq_left h, mul_comm ρ]
  exact mul_le_mul' le_rfl (gaussValuation_le_of_coeff_zero_eq_zero hv hρ he)

/-- For `0 < ρ`, the Gauss valuation vanishes only at zero. -/
@[simp]
theorem gaussValuation_eq_zero_iff (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {x : 𝕎 O} :
    gaussValuation p hv ρ hρ x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  ext n
  have hn := (le_gaussValuation hv hρ x n).trans h.le
  rw [nonpos_iff_eq_zero, mul_eq_zero, map_eq_zero, map_eq_zero_iff _ hv.hom_inj] at hn
  rw [← teichmullerCoeff_pow, zero_coeff,
    hn.resolve_right (pow_ne_zero n hρ₀.ne'), zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)]

/-- For `0 < ρ`, the Gauss valuation of a nonzero Witt vector is positive. -/
theorem gaussValuation_pos (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {x : 𝕎 O}
    (hx : x ≠ 0) : 0 < gaussValuation p hv ρ hρ x :=
  pos_iff_ne_zero.mpr ((gaussValuation_eq_zero_iff hv hρ₀ hρ).not.mpr hx)

/-- **The Gauss valuations are continuous** for the `(p, [ϖ])`-adic topology on `𝕎 O`, when
`v(ϖ) < 1`: `λ_ρ` is at most `1` everywhere, and at most `max ρ v(ϖ) < 1` at `p` and `[ϖ]`. -/
theorem isContinuous_gaussValuation [TopologicalSpace (𝕎 O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (hv : v.Integers O)
    (hρ : ρ < 1) (hϖ : v (algebraMap O K ϖ) < 1) : (gaussValuation p hv ρ hρ).IsContinuous := by
  refine Valuation.isContinuous_of_isAdic hI (fun a _ ↦ gaussValuation_le_one hv hρ a)
    (max_lt hρ hϖ) fun t ht ↦ ?_
  rcases ht with rfl | rfl <;> simp

/-! ### The degree

For `0 < ρ < 1` and `x ≠ 0`, the weighted valuations `v(xₙ) ρⁿ` attain their supremum `λ_ρ(x)` at
finitely many indices. Kedlaya calls the largest of them the *degree* of `x`. Viewing `x` as a
power series in `p` with Teichmüller coefficients, it is the degree of the leading part of `x` for
`λ_ρ`, and it behaves like the degree of a polynomial: it is additive on products and only depends
on `x` up to terms of smaller Gauss valuation.

Both facts come from the radii slightly larger than `ρ`. There `λ_ρ'(x) = v(x_d) ρ' ^ d` for the
degree `d`, because enlarging the radius favours the larger indices among those attaining
`λ_ρ(x)`. Since every `λ_ρ'` is a valuation, the degree is the exponent of this power law, and it
is computed from the valuations `λ_ρ'` alone, with no reference to Witt vector arithmetic. -/

section Degree

open Filter Topology

variable (p) in
/-- **The degree of a Witt vector for the Gauss valuation `λ_ρ`**: the largest index `d` with
`v(x_d) ρ ^ d = λ_ρ(x)`, for `x ≠ 0` and `0 < ρ < 1`. -/
noncomputable def gaussDegree (hv : v.Integers O) (ρ : ℝ≥0) (hρ : ρ < 1) (x : 𝕎 O) : ℕ :=
  sSup {n | v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n = gaussValuation p hv ρ hρ x}

/-- The degree of `0` is `0`: every index attains its Gauss valuation `0`. -/
@[simp]
theorem gaussDegree_zero (hv : v.Integers O) (hρ : ρ < 1) : gaussDegree p hv ρ hρ 0 = 0 := by
  simp [gaussDegree]

/-- The indices attaining a nonzero Gauss valuation are bounded. -/
private theorem bddAbove_setOf_eq_gaussValuation (hv : v.Integers O) (hρ : ρ < 1)
    {x : 𝕎 O} (hx : gaussValuation p hv ρ hρ x ≠ 0) :
    BddAbove {n | v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n =
      gaussValuation p hv ρ hρ x} := by
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr hx) hρ
  refine ⟨N, fun n hn ↦ le_of_not_ge fun hNn ↦ ?_⟩
  have h : v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n < gaussValuation p hv ρ hρ x :=
    ((mul_le_of_le_one_left' (hv.map_le_one (x.teichmullerCoeff n))).trans
      (pow_le_pow_of_le_one zero_le hρ.le hNn)).trans_lt hN
  exact h.ne hn

/-- Every Witt vector attains its Gauss valuation at some index. -/
private theorem nonempty_setOf_eq_gaussValuation (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) :
    {n | v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n =
      gaussValuation p hv ρ hρ x}.Nonempty := by
  obtain ⟨i₀, hi₀, -⟩ := exists_isGreatest_gaussTerm hv hρ x
  exact ⟨i₀, (gaussSup_eq_gaussTerm hv hρ.le hi₀).symm⟩

/-- Every Witt vector attains its Gauss valuation at its degree, including at radius zero:
`λ_ρ(x) = v(x_d) ρ ^ d` for `d = gaussDegree p hv ρ hρ x`. -/
theorem gaussValuation_eq_mul_pow_gaussDegree (hv : v.Integers O) (hρ : ρ < 1) (x : 𝕎 O) :
    gaussValuation p hv ρ hρ x = v (algebraMap O K (x.teichmullerCoeff (gaussDegree p hv ρ hρ x))) *
      ρ ^ gaussDegree p hv ρ hρ x := by
  by_cases hx : gaussValuation p hv ρ hρ x = 0
  · exact le_antisymm (hx ▸ zero_le) (le_gaussValuation hv hρ x _)
  · exact (Nat.sSup_mem (nonempty_setOf_eq_gaussValuation hv hρ x)
      (bddAbove_setOf_eq_gaussValuation hv hρ hx)).symm

/-- Every index at which a nonzero Witt vector attains its Gauss valuation is at most its
degree. -/
theorem le_gaussDegree (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {x : 𝕎 O} (hx : x ≠ 0)
    {n : ℕ} (hn : v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n = gaussValuation p hv ρ hρ x) :
    n ≤ gaussDegree p hv ρ hρ x :=
  le_csSup (bddAbove_setOf_eq_gaussValuation hv hρ (gaussValuation_pos hv hρ₀ hρ hx).ne') hn

/-- Beyond its degree, the weighted valuations of a nonzero Witt vector are smaller than its
Gauss valuation. -/
theorem mul_pow_lt_gaussValuation_of_gaussDegree_lt (hv : v.Integers O) (hρ₀ : 0 < ρ)
    (hρ : ρ < 1) {x : 𝕎 O} (hx : x ≠ 0) {n : ℕ} (hn : gaussDegree p hv ρ hρ x < n) :
    v (algebraMap O K (x.teichmullerCoeff n)) * ρ ^ n < gaussValuation p hv ρ hρ x :=
  (le_gaussValuation hv hρ x n).lt_of_ne fun h ↦ (le_gaussDegree hv hρ₀ hρ hx h).not_gt hn

/-- **The Gauss valuations near `ρ` follow a power law of the degree.** For `ρ'` slightly larger
than `ρ`, the Gauss valuation `λ_ρ'(x)` of a Witt vector is attained at its degree `d` for
`λ_ρ`: `λ_ρ'(x) = v(x_d) ρ' ^ d`. -/
theorem eventually_gaussValuation_eq_mul_pow_gaussDegree (hv : v.Integers O) (hρ₀ : 0 < ρ)
    (hρ : ρ < 1) (x : 𝕎 O) :
    ∀ᶠ ρ' in 𝓝[≥] ρ, ∀ hρ' : ρ' < 1, gaussValuation p hv ρ' hρ' x =
      v (algebraMap O K (x.teichmullerCoeff (gaussDegree p hv ρ hρ x))) *
        ρ' ^ gaussDegree p hv ρ hρ x := by
  by_cases hx : x = 0
  · simp [hx]
  set d := gaussDegree p hv ρ hρ x
  set a : ℕ → ℝ≥0 := fun n ↦ v (algebraMap O K (x.teichmullerCoeff n))
  have hM := gaussValuation_eq_mul_pow_gaussDegree hv hρ x
  have hM₀ : 0 < a d * ρ ^ d := hM ▸ gaussValuation_pos hv hρ₀ hρ hx
  obtain ⟨ρ₁, hρρ₁, hρ₁⟩ := exists_between hρ
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one hM₀ hρ₁
  -- Each of the finitely many indices below `N` is dominated by the degree near `ρ`: the indices
  -- below `d` for every `ρ' ≥ ρ`, and those above `d` by continuity, as they are strictly
  -- dominated at `ρ`.
  have hfin : ∀ᶠ ρ' in 𝓝[≥] ρ, ∀ n ∈ Finset.range N, a n * ρ' ^ n ≤ a d * ρ' ^ d := by
    refine (Filter.eventually_all_finset _).mpr fun n _ ↦ ?_
    rcases le_or_gt n d with hnd | hdn
    · filter_upwards [self_mem_nhdsWithin] with ρ' (hρ' : ρ ≤ ρ')
      -- Cancel `ρ ^ n` from `a n ρ ^ n ≤ a d ρ ^ d`, then enlarge `ρ ^ (d - n)` to `ρ' ^ (d - n)`.
      have key (b c : ℝ≥0) (k : ℕ) (hbc : b * ρ ^ n ≤ c * ρ ^ (n + k)) :
          b * ρ' ^ n ≤ c * ρ' ^ (n + k) := by
        rw [pow_add, mul_comm (ρ ^ n), ← mul_assoc] at hbc
        rw [pow_add, mul_comm (ρ' ^ n), ← mul_assoc]
        exact mul_le_mul' ((le_of_mul_le_mul_right hbc (pow_pos hρ₀ n)).trans
          (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hρ' k))) le_rfl
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnd
      have h : a n * ρ ^ n ≤ a d * ρ ^ d := hM ▸ le_gaussValuation hv hρ x n
      rw [hk] at h ⊢
      exact key _ _ k h
    · have hlt : a n * ρ ^ n < a d * ρ ^ d :=
        hM ▸ mul_pow_lt_gaussValuation_of_gaussDegree_lt hv hρ₀ hρ hx hdn
      exact (((continuous_const.mul (continuous_pow n)).continuousAt.eventually_lt
        (continuous_const.mul (continuous_pow d)).continuousAt hlt).filter_mono
          nhdsWithin_le_nhds).mono fun _ h ↦ h.le
  filter_upwards [hfin, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hρρ₁)] with
    ρ' hfin (hρ' : ρ ≤ ρ') (hρ'₁ : ρ' < ρ₁) hρ'1
  -- The indices from `N` on are dominated uniformly for `ρ ≤ ρ' < ρ₁`.
  have hle (n : ℕ) : a n * ρ' ^ n ≤ a d * ρ' ^ d := by
    rcases lt_or_ge n N with hn | hn
    · exact hfin n (Finset.mem_range.mpr hn)
    calc a n * ρ' ^ n ≤ ρ₁ ^ N :=
          (mul_le_of_le_one_left' (hv.map_le_one _)).trans
            ((pow_le_pow_left₀ zero_le hρ'₁.le n).trans (pow_le_pow_of_le_one zero_le hρ₁.le hn))
      _ ≤ a d * ρ ^ d := hN.le
      _ ≤ a d * ρ' ^ d := mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hρ' d)
  rw [gaussValuation_apply]
  exact le_antisymm (ciSup_le hle) (le_ciSup ⟨_, Set.forall_mem_range.mpr hle⟩ d)

/-- **The degree is the exponent of the power law.** If, for all `ρ'` slightly larger than `ρ`,
the Gauss valuation `λ_ρ'(x)` of a nonzero Witt vector is `c ρ' ^ n`, then `n` is the degree of
`x` for `λ_ρ`. -/
theorem gaussDegree_eq_of_eventually_eq_mul_pow (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    {x : 𝕎 O} (hx : x ≠ 0) {c : ℝ≥0} {n : ℕ}
    (h : ∀ᶠ ρ' in 𝓝[≥] ρ, ∀ hρ' : ρ' < 1, gaussValuation p hv ρ' hρ' x = c * ρ' ^ n) :
    gaussDegree p hv ρ hρ x = n := by
  set d := gaussDegree p hv ρ hρ x
  set a := v (algebraMap O K (x.teichmullerCoeff d))
  have hM₀ : a * ρ ^ d ≠ 0 :=
    (gaussValuation_eq_mul_pow_gaussDegree hv hρ x ▸ gaussValuation_pos hv hρ₀ hρ hx).ne'
  have heq : ∀ᶠ ρ' in 𝓝[≥] ρ, a * ρ' ^ d = c * ρ' ^ n := by
    filter_upwards [h, eventually_gaussValuation_eq_mul_pow_gaussDegree hv hρ₀ hρ x,
      nhdsWithin_le_nhds (Iio_mem_nhds hρ)] with ρ' h h' hρ'
    exact (h' hρ').symm.trans (h hρ')
  -- Comparing the power laws at `ρ` and at some `ρ' > ρ` identifies the exponents.
  obtain ⟨ρ', hρ', hρρ'⟩ :=
    ((heq.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)).and self_mem_nhdsWithin).exists
  set r := ρ' / ρ
  have hr : ρ' = ρ * r := (mul_div_cancel₀ ρ' hρ₀.ne').symm
  have hρeq : a * ρ ^ d = c * ρ ^ n := heq.self_of_nhdsWithin le_rfl
  rw [hr, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc, hρeq] at hρ'
  have hr₁ : 1 < r := (one_lt_div hρ₀).mpr hρρ'
  exact pow_right_injective₀ (zero_lt_one.trans hr₁) hr₁.ne'
    (mul_left_cancel₀ (hρeq ▸ hM₀) hρ')

/-- **The degree only depends on the leading part** (Kedlaya, Remark 2.7): if
`λ_ρ(x - y) < λ_ρ(x)`, then `x` and `y` have the same degree. -/
theorem gaussDegree_eq_of_gaussValuation_sub_lt (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    {x y : 𝕎 O} (h : gaussValuation p hv ρ hρ (x - y) < gaussValuation p hv ρ hρ x) :
    gaussDegree p hv ρ hρ y = gaussDegree p hv ρ hρ x := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  set d := gaussDegree p hv ρ hρ x
  set a := v (algebraMap O K (x.teichmullerCoeff d))
  set e := gaussDegree p hv ρ hρ (x - y)
  set b := v (algebraMap O K ((x - y).teichmullerCoeff e))
  have hlt : b * ρ ^ e < a * ρ ^ d := by
    rwa [gaussValuation_eq_mul_pow_gaussDegree hv hρ x,
      gaussValuation_eq_mul_pow_gaussDegree hv hρ (x - y)] at h
  have hlt' : ∀ᶠ ρ' in 𝓝[≥] ρ, b * ρ' ^ e < a * ρ' ^ d :=
    ((continuous_const.mul (continuous_pow e)).continuousAt.eventually_lt
      (continuous_const.mul (continuous_pow d)).continuousAt hlt).filter_mono nhdsWithin_le_nhds
  refine gaussDegree_eq_of_eventually_eq_mul_pow (c := a) hv hρ₀ hρ hy ?_
  filter_upwards [hlt', eventually_gaussValuation_eq_mul_pow_gaussDegree hv hρ₀ hρ x,
    eventually_gaussValuation_eq_mul_pow_gaussDegree hv hρ₀ hρ (x - y)] with ρ' hlt' hx' hxy' hρ'
  rw [← hx' hρ', ← hxy' hρ'] at hlt'
  rw [← hx' hρ', ← Valuation.map_sub_eq_of_lt_left _ hlt', sub_sub_cancel]

/-- **The degree is additive on products** (Kedlaya, Lemma 2.6). -/
theorem gaussDegree_mul (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {x y : 𝕎 O} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    gaussDegree p hv ρ hρ (x * y) = gaussDegree p hv ρ hρ x + gaussDegree p hv ρ hρ y := by
  have := hv.isDomain
  refine gaussDegree_eq_of_eventually_eq_mul_pow
    (c := v (algebraMap O K (x.teichmullerCoeff (gaussDegree p hv ρ hρ x))) *
      v (algebraMap O K (y.teichmullerCoeff (gaussDegree p hv ρ hρ y)))) hv hρ₀ hρ
    (mul_ne_zero hx hy) ?_
  filter_upwards [eventually_gaussValuation_eq_mul_pow_gaussDegree hv hρ₀ hρ x,
    eventually_gaussValuation_eq_mul_pow_gaussDegree hv hρ₀ hρ y] with ρ' hx' hy' hρ'
  rw [map_mul, hx' hρ', hy' hρ', pow_add]
  ring

/-- The degree of `[a] p ^ m` is `m`, for `a ≠ 0`. -/
theorem gaussDegree_teichmuller_mul_pow (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {a : O}
    (ha : a ≠ 0) (m : ℕ) : gaussDegree p hv ρ hρ (teichmuller p a * (p : 𝕎 O) ^ m) = m := by
  have := hv.isDomain
  have hp : (p : 𝕎 O) ≠ 0 := fun h ↦ hρ₀.ne (by simpa [h] using gaussValuation_p (p := p) hv hρ)
  exact gaussDegree_eq_of_eventually_eq_mul_pow hv hρ₀ hρ
    (mul_ne_zero (teichmuller_ne_zero p ha) (pow_ne_zero m hp))
    (Filter.Eventually.of_forall fun ρ' hρ' ↦ gaussValuation_teichmuller_mul_pow hv hρ' a m)

/-- Multiplying by a Teichmüller representative `[c]` with `c ≠ 0` does not change the degree. -/
@[simp]
theorem gaussDegree_teichmuller_mul (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {c : O}
    (hc : c ≠ 0) (x : 𝕎 O) :
    gaussDegree p hv ρ hρ (teichmuller p c * x) = gaussDegree p hv ρ hρ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mul_zero]
  have h₀ := gaussDegree_teichmuller_mul_pow (p := p) hv hρ₀ hρ hc 0
  rw [pow_zero, mul_one] at h₀
  rw [gaussDegree_mul hv hρ₀ hρ (teichmuller_ne_zero p hc) hx, h₀, zero_add]

/-- A nonzero finite Teichmüller sum `∑_{j < n} [aⱼ] pʲ` has degree less than `n`. -/
theorem gaussDegree_sum_range_teichmuller_mul_pow_lt (hv : v.Integers O) (hρ₀ : 0 < ρ)
    (hρ : ρ < 1) {a : ℕ → O} {n : ℕ}
    (h : ∑ j ∈ Finset.range n, teichmuller p (a j) * (p : 𝕎 O) ^ j ≠ 0) :
    gaussDegree p hv ρ hρ (∑ j ∈ Finset.range n, teichmuller p (a j) * (p : 𝕎 O) ^ j) < n := by
  by_contra! hn
  have := gaussValuation_eq_mul_pow_gaussDegree hv hρ
    (∑ j ∈ Finset.range n, teichmuller p (a j) * (p : 𝕎 O) ^ j)
  simp only [teichmullerCoeff_sum_range_teichmuller_mul_pow, hn.not_gt, ↓reduceIte, map_zero,
    zero_mul, gaussValuation_eq_zero_iff hv hρ₀ hρ] at this
  exact h this

end Degree

end TauCeti.WittVector
