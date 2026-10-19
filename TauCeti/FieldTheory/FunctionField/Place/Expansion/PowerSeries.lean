/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Power-series expansions at rational places

At a rational place with chosen uniformizer `t`, the compatible finite expansions define a
`k`-algebra embedding of the valuation ring into `k[[T]]`. Its coefficients characterize
congruence modulo every order-filtration step, so the embedding preserves orders and sends
`t` to `T`. These statements do not require completeness. When the field is complete for the
order filtration, every power series is an expansion
(`TauCeti.Place.powerSeriesExpansion_surjective`); this applies to the completion at a rational
place, and to the completion at any place with separable residue field viewed as a rational place
over its coefficient field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

public section

open scoped BigOperators

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

/-- The uniformizer expansion of an integral function at a rational place, assembled from
its compatible finite coefficient vectors. -/
noncomputable def powerSeriesExpansion : P.integers →ₐ[k] PowerSeries k where
  toFun x := PowerSeries.mk fun n ↦ P.truncatedExpansion hP ht (n + 1) x ⟨n, by omega⟩
  map_zero' := by ext n; simp
  map_one' := by ext n; simp [PowerSeries.coeff_one]
  map_add' x y := by ext n; simp
  map_mul' x y := by
    ext n
    simp only [PowerSeries.coeff_mk, P.truncatedExpansion_mul, PowerSeries.coeff_mul]
    apply sum_fin_product_eq_sum_antidiagonal (Nat.lt_succ_self n)
    intro l hl
    congr 1
    · exact P.truncatedExpansion_castLE hP ht
        (n := (l.1 : ℕ) + 1) (m := n + 1) (by omega) x ⟨l.1, by omega⟩
    · exact P.truncatedExpansion_castLE hP ht
        (n := (l.2 : ℕ) + 1) (m := n + 1) (by omega) y ⟨l.2, by omega⟩
  commutes' c := by
    ext n
    simp [Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_C]

/-- Every coefficient of the infinite expansion agrees with the corresponding coefficient
of any sufficiently long finite expansion. -/
@[simp]
theorem coeff_powerSeriesExpansion (n : ℕ) (x : P.integers) (i : Fin n) :
    PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) =
      P.truncatedExpansion hP ht n x i := by
  simp only [powerSeriesExpansion, AlgHom.coe_mks, PowerSeries.coeff_mk]
  exact (P.truncatedExpansion_castLE hP ht
    (n := (i : ℕ) + 1) (m := n) (by omega) x ⟨i, by omega⟩).symm

/-- Removing the first `n` coefficients of the power-series expansion leaves a function
vanishing to order at least `n`. -/
theorem sub_sum_coeff_powerSeriesExpansion_mem_filtration (n : ℕ) (x : P.integers) :
    (x : F) - ∑ i : Fin n, algebraMap k F
      (PowerSeries.coeff i (P.powerSeriesExpansion hP ht x)) * t ^ (i : ℕ) ∈
      P.filtration n := by
  simp only [P.coeff_powerSeriesExpansion hP ht]
  exact P.sub_sum_truncatedExpansion_mem_filtration hP ht n x

/-- Vanishing of the first `n` expansion coefficients is exactly membership in the `n`-th
order filtration, including the zero function. -/
theorem mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔
      ∀ i < n, PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) = 0 := by
  have heq := P.truncatedExpansion_eq_iff_sub_mem_filtration hP ht n x 0
  simp only [P.truncatedExpansion_zero hP ht, ZeroMemClass.coe_zero, sub_zero] at heq
  rw [← heq]
  constructor
  · intro h i hi
    rw [P.coeff_powerSeriesExpansion hP ht n x ⟨i, hi⟩, h]
    rfl
  · intro h
    ext i
    exact (P.coeff_powerSeriesExpansion hP ht n x i).symm.trans (h i i.isLt)

/-- The power-series embedding identifies the local order filtration with the usual
power-series order filtration. -/
theorem mem_filtration_iff_le_order_powerSeriesExpansion (n : ℕ) (x : P.integers) :
    (x : F) ∈ P.filtration n ↔
      (n : ℕ∞) ≤ (P.powerSeriesExpansion hP ht x).order := by
  rw [P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht,
    PowerSeries.nat_le_order_iff]

/-- Uniformizer expansion is injective even before completion: an integral function is
determined by all its coefficients. -/
theorem powerSeriesExpansion_injective : Function.Injective (P.powerSeriesExpansion hP ht) := by
  apply (injective_iff_map_eq_zero (P.powerSeriesExpansion hP ht)).mpr
  intro x hx
  by_contra hx0
  have hxF : (x : F) ≠ 0 := by simpa using hx0
  let n := (P.ord (x : F)).toNat + 1
  have hn : P.ord (x : F) < (n : ℤ) := by dsimp [n]; omega
  have hm := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht n x).mpr
    (by simp [hx])
  exact (not_le.mpr hn) ((P.mem_filtration_iff_le_ord hxF).mp hm)

/-- Two integral functions agree to order `n` precisely when their first `n` expansion
coefficients agree. -/
theorem sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq (n : ℕ) (x y : P.integers) :
    (x : F) - (y : F) ∈ P.filtration n ↔
      ∀ i < n, PowerSeries.coeff i (P.powerSeriesExpansion hP ht x) =
        PowerSeries.coeff i (P.powerSeriesExpansion hP ht y) := by
  simpa only [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero] using
    P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht n (x - y)

/-- The chosen uniformizer expands as the power-series variable. -/
@[simp]
theorem powerSeriesExpansion_uniformizer :
    P.powerSeriesExpansion hP ht ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      PowerSeries.X := by
  ext n
  rw [P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩,
    P.truncatedExpansion_uniformizer hP ht]
  simp [PowerSeries.coeff_X]

/-- **Every power series is an expansion** when the field is complete for the order filtration of
the rational place: if every sequence whose terms agree to increasing order, `g n ≡ g m` to order
`m` whenever `m ≤ n`, is approximated to order `n` by a single function, then every power series
is the uniformizer expansion of an integral function. -/
theorem powerSeriesExpansion_surjective
    (hcomplete : ∀ g : ℕ → F, (∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.filtration m) →
      ∃ x : F, ∀ n : ℕ, x - g n ∈ P.filtration n) :
    Function.Surjective (P.powerSeriesExpansion hP ht) := by
  intro f
  -- The partial sums of `∑ cᵢ tⁱ` agree to increasing order, as `tⁱ` has order `i`.
  let g : ℕ → F := fun n ↦
    ∑ i ∈ Finset.range n, algebraMap k F (PowerSeries.coeff i f) * t ^ i
  have hg : ∀ ⦃m n : ℕ⦄, m ≤ n → g n - g m ∈ P.filtration m := by
    intro m n hmn
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hmi : (m : ℤ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    refine P.filtration_antitone hmi ?_
    have hpow := P.mem_filtration_ord (t ^ i)
    rw [ord_pow, ht, mul_one] at hpow
    simpa only [zero_add] using P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers _)) hpow
  obtain ⟨x, hx⟩ := hcomplete g hg
  have hxint : x ∈ P.integers := by
    simpa [g, mem_filtration_zero_iff] using hx 0
  refine ⟨⟨x, hxint⟩, ?_⟩
  ext n
  have heq := (P.truncatedExpansion_eq_iff hP ht (n + 1) ⟨x, hxint⟩
    (fun i ↦ PowerSeries.coeff i f)).mpr (by
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ algebraMap k F (PowerSeries.coeff i f) * t ^ i)]
      exact hx (n + 1))
  rw [P.coeff_powerSeriesExpansion hP ht (n + 1) _ ⟨n, by omega⟩, heq]

/-- The order of a nonzero integral function is the first nonzero degree of its
power-series expansion. -/
theorem order_powerSeriesExpansion (x : P.integers) (hx : x ≠ 0) :
    (P.powerSeriesExpansion hP ht x).order = ((P.ord (x : F)).toNat : ℕ∞) := by
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have ho : 0 ≤ P.ord (x : F) := P.mem_integers_iff_ord_nonneg.mp x.2
  have hlow := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht
    (P.ord (x : F)).toNat x).mp
    ((P.mem_filtration_iff_le_ord hxF).mpr (by omega))
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨?_, hlow⟩
  intro hc
  have hm := (P.mem_filtration_iff_coeff_powerSeriesExpansion_eq_zero hP ht
    ((P.ord (x : F)).toNat + 1) x).mpr (fun i hi ↦ by
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact hlow i hi
      · exact hc)
  have := (P.mem_filtration_iff_le_ord hxF).mp hm
  omega

end TauCeti.Place
