/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integers
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

## Main results

* `Valuation.Integers.mem_span_teichmuller_pow_iff` : the ideal `([c], p ^ (n + 1))` in terms of
  Teichmüller coordinates.
* `TauCeti.WittVector.gaussValuation_apply` : `λ_ρ(x) = supₙ v(xₙ) ρⁿ`.
* `TauCeti.WittVector.gaussValuation_teichmuller_mul_pow` : `λ_ρ([a] p ^ m) = v(a) ρ ^ m`.
* `TauCeti.WittVector.gaussValuation_eq_zero_iff` : for `0 < ρ`, `λ_ρ` vanishes only at `0`.
* `TauCeti.WittVector.isContinuous_gaussValuation` : if `v(ϖ) < 1`, then `λ_ρ` is continuous for
  the `(p, [ϖ])`-adic topology.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1, for the Gauss norms on `A_inf`.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors*, Nagoya Math. J. 209 (2013).
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
  rw [hXY, show x * y - X * Y = x * (y - Y) + (x - X) * Y by ring]
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
      rcases (show ij.1 < i₀ ∨ ij.2 < j₀ by
        by_contra! h
        exact hne (Prod.ext (by omega) (by omega))) with h | h
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

/-- For `0 < ρ`, the Gauss valuation vanishes only at zero. -/
theorem gaussValuation_eq_zero_iff (hv : v.Integers O) (hρ₀ : 0 < ρ) (hρ : ρ < 1) {x : 𝕎 O} :
    gaussValuation p hv ρ hρ x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  ext n
  have hn := (le_gaussValuation hv hρ x n).trans h.le
  rw [nonpos_iff_eq_zero, mul_eq_zero, map_eq_zero, map_eq_zero_iff _ hv.hom_inj] at hn
  rw [← teichmullerCoeff_pow, zero_coeff,
    hn.resolve_right (pow_ne_zero n hρ₀.ne'), zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)]

/-- **The Gauss valuations are continuous** for the `(p, [ϖ])`-adic topology on `𝕎 O`, when
`v(ϖ) < 1`: `λ_ρ` is at most `1` everywhere, and at most `max ρ v(ϖ) < 1` at `p` and `[ϖ]`. -/
theorem isContinuous_gaussValuation [TopologicalSpace (𝕎 O)] {ϖ : O}
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (hv : v.Integers O)
    (hρ : ρ < 1) (hϖ : v (algebraMap O K ϖ) < 1) : (gaussValuation p hv ρ hρ).IsContinuous := by
  refine Valuation.isContinuous_of_isAdic hI (fun a _ ↦ gaussValuation_le_one hv hρ a)
    (max_lt hρ hϖ) fun t ht ↦ ?_
  rcases ht with rfl | rfl <;> simp

end TauCeti.WittVector
