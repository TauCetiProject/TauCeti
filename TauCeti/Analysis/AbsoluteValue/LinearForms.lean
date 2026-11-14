/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

import Mathlib.Data.Fintype.Order
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Local bounds for linear forms and dot products

For an absolute value `v` on a ring or field, this file records local estimates relating
coordinate bounds, dot-product pairings `y ⬝ᵥ x`, and evaluations of linear forms `l i x`.

* At a nonarchimedean absolute value, entrywise bounds on two finite tuples multiply to bound their
  dot product (`AbsoluteValue.apply_dotProduct_le_mul_of_isNonarchimedean`); in particular, the unit
  ball of `ι → R` is closed under dot products
  (`AbsoluteValue.apply_dotProduct_le_one_of_isNonarchimedean`).
* When a vector `z` lies in the span of the coefficient vectors `j ↦ l i (Pi.single j 1)` of a
  subfamily `s` of linear forms, a constant `B ≥ 1` independent of `x` and `M` bounds `v (z ⬝ᵥ x)`
  by `B * M` whenever `v (l i x) ≤ M` on `s`
  (`AbsoluteValue.exists_one_le_forall_dotProduct_le_mul`), and in particular by `B * Q ^ e₀` on
  power-bounded domains `{i | e i ≤ e₀}` for `Q ≥ 1`
  (`AbsoluteValue.exists_one_le_forall_dotProduct_le_mul_rpow`).
* Over a field, `#ι` linearly independent linear forms on `ι → K` span the dual space, so a
  constant `C ≥ 1` bounds every coordinate `v (x j)` by `C * ⨆ i, v (l i x)`
  (`AbsoluteValue.exists_one_le_forall_apply_le_mul_iSup`).

In Diophantine approximation over a number field, these single-place estimates convert bounds on
linear forms at archimedean and finite places into bounds on pairings with threshold vectors and on
coordinates of domain points.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.
* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. **101**
  (1996), Lemma 27.
-/

public section

namespace AbsoluteValue

/-- For a nonarchimedean absolute value `v`, entrywise bounds `v (y j) ≤ a` and `v (x j) ≤ b`
(`0 ≤ a`, `0 ≤ b`) pass to the dot product: `v (y ⬝ᵥ x) ≤ a * b`. -/
theorem apply_dotProduct_le_mul_of_isNonarchimedean {R S ι : Type*} [Semiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [Fintype ι] (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) {a b : S} (ha : 0 ≤ a) (hb : 0 ≤ b) {y x : ι → R}
    (hy : ∀ j, v (y j) ≤ a) (hx : ∀ j, v (x j) ≤ b) :
    v (y ⬝ᵥ x) ≤ a * b := by
  classical
  rw [dotProduct]
  refine Finset.induction_on Finset.univ (by simpa using mul_nonneg ha hb) fun j s hj hs ↦ ?_
  rw [Finset.sum_insert hj]
  refine (hv _ _).trans (max_le ?_ hs)
  rw [map_mul]
  exact mul_le_mul (hy j) (hx j) (v.nonneg _) ha

/-- For a nonarchimedean absolute value `v`, the dot product of two tuples in the unit ball lies in
the unit ball. -/
theorem apply_dotProduct_le_one_of_isNonarchimedean {R S ι : Type*} [Semiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [Fintype ι] (v : AbsoluteValue R S)
    (hv : IsNonarchimedean v) {y x : ι → R} (hy : ∀ j, v (y j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) :
    v (y ⬝ᵥ x) ≤ 1 :=
  (v.apply_dotProduct_le_mul_of_isNonarchimedean hv zero_le_one zero_le_one hy hx).trans_eq
    (one_mul 1)

/-- If `z` lies in the span of the coefficient vectors `j ↦ l i (Pi.single j 1)` of the forms
`l i` with `i ∈ s`, then some constant `B ≥ 1` (depending only on `v`, `l`, `s`, and `z`) bounds
`v (z ⬝ᵥ x)` by `B * M` whenever `0 ≤ M` and `v (l i x) ≤ M` for all `i ∈ s`. -/
theorem exists_one_le_forall_dotProduct_le_mul {R S ι κ : Type*} [CommSemiring R] [Semiring S]
    [LinearOrder S] [IsOrderedRing S] [DecidableEq ι] [Fintype ι] (v : AbsoluteValue R S)
    (l : κ → Module.Dual R (ι → R)) (s : Set κ) {z : ι → R}
    (hz : z ∈ Submodule.span R ((fun i j ↦ l i (Pi.single j 1)) '' s)) :
    ∃ B : S, 1 ≤ B ∧ ∀ ⦃M : S⦄, 0 ≤ M → ∀ ⦃x : ι → R⦄,
      (∀ i ∈ s, v (l i x) ≤ M) → v (z ⬝ᵥ x) ≤ B * M := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨i, hi, rfl⟩
    refine ⟨1, le_rfl, fun M _ x hx ↦ ?_⟩
    have hdot : (fun j ↦ l i (Pi.single j 1)) ⬝ᵥ x = l i x := by
      conv_rhs => rw [← (Pi.basisFun R ι).sum_repr x, map_sum]
      simp [dotProduct, mul_comm]
    rw [hdot, one_mul]
    exact hx i hi
  · exact ⟨1, le_rfl, fun M hM _ _ ↦ by
      simpa only [zero_dotProduct, AbsoluteValue.map_zero, one_mul] using hM⟩
  · rintro z₁ z₂ - - ⟨B₁, hB₁, h₁⟩ ⟨B₂, hB₂, h₂⟩
    refine ⟨B₁ + B₂, hB₁.trans (le_add_of_nonneg_right (zero_le_one.trans hB₂)),
      fun M hM x hx ↦ ?_⟩
    rw [add_dotProduct, add_mul]
    exact (v.add_le _ _).trans (add_le_add (h₁ hM hx) (h₂ hM hx))
  · rintro r z - ⟨B, _, h⟩
    refine ⟨max (v r * B) 1, le_max_right _ _, fun M hM x hx ↦ ?_⟩
    rw [smul_dotProduct, smul_eq_mul, map_mul]
    calc v r * v (z ⬝ᵥ x)
        ≤ v r * (B * M) := mul_le_mul_of_nonneg_left (h hM hx) (v.nonneg _)
      _ = v r * B * M := (mul_assoc _ _ _).symm
      _ ≤ max (v r * B) 1 * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM

/-- If `z` lies in the span of the coefficient vectors of those forms `l i` with `e i ≤ e₀`, then
some constant `B ≥ 1` bounds `v (z ⬝ᵥ x)` by `B * Q ^ e₀` whenever `1 ≤ Q` and
`v (l i x) ≤ Q ^ e i` for all `i`. -/
theorem exists_one_le_forall_dotProduct_le_mul_rpow {R ι κ : Type*} [CommSemiring R]
    [DecidableEq ι] [Fintype ι] (v : AbsoluteValue R ℝ) (l : κ → Module.Dual R (ι → R))
    (e : κ → ℝ) (e₀ : ℝ) {z : ι → R}
    (hz : z ∈ Submodule.span R ((fun i j ↦ l i (Pi.single j 1)) '' {i | e i ≤ e₀})) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ⦃Q : ℝ⦄, 1 ≤ Q → ∀ ⦃x : ι → R⦄,
      (∀ i, v (l i x) ≤ Q ^ e i) → v (z ⬝ᵥ x) ≤ B * Q ^ e₀ := by
  obtain ⟨B, hB1, hB⟩ := v.exists_one_le_forall_dotProduct_le_mul l {i | e i ≤ e₀} hz
  exact ⟨B, hB1, fun Q hQ x hx ↦ hB (Real.rpow_nonneg (zero_le_one.trans hQ) e₀)
    fun i hi ↦ (hx i).trans (Real.rpow_le_rpow_of_exponent_le hQ hi)⟩

/-- At any real-valued absolute value where `#ι` linear forms `l` on `ι → K` are linearly
independent, some `C ≥ 1` bounds every coordinate `v (x j)` by `C * ⨆ i, v (l i x)`. -/
theorem exists_one_le_forall_apply_le_mul_iSup {K ι : Type*} [Field K] [Finite ι]
    (v : AbsoluteValue K ℝ) {l : ι → Module.Dual K (ι → K)} (hl : LinearIndependent K l) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : ι → K) (j : ι), v (x j) ≤ C * ⨆ i, v (l i x) := by
  cases nonempty_fintype ι
  obtain ⟨a, ha⟩ := hl.exists_sum_smul_eq_proj
  refine ⟨1 + ∑ j, ∑ i, v (a j i),
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ v.nonneg _),
    fun x j ↦ ?_⟩
  have hxj : x j = ∑ i, a j i * l i x := by simpa using (LinearMap.congr_fun (ha j) x).symm
  rw [hxj]
  calc v (∑ i, a j i * l i x)
      ≤ ∑ i, v (a j i) * v (l i x) :=
        (v.sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by rw [map_mul])
    _ ≤ ∑ i, v (a j i) * ⨆ k, v (l k x) :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (Finite.le_ciSup_of_le i le_rfl) (v.nonneg _)
    _ = (∑ i, v (a j i)) * ⨆ k, v (l k x) := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + ∑ j', ∑ i, v (a j' i)) * ⨆ k, v (l k x) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun k ↦ v.nonneg _)
        have := Finset.single_le_sum (f := fun j' ↦ ∑ i, v (a j' i))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ v.nonneg _) (Finset.mem_univ j)
        linarith

end AbsoluteValue
