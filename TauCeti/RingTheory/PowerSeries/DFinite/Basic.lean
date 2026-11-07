/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.PowerSeries.Exp
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.RingTheory.Derivation.Basic
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# D-finite power series

Let `k` be a field and `K` a commutative `k`-algebra. A formal power series `f : K⟦X⟧` is
*D-finite* (or *holonomic*) over `k` if it satisfies a nonzero linear differential equation

  `p₀ f + p₁ f' + ⋯ + pₙ f⁽ⁿ⁾ = 0`

whose coefficients `pᵢ` are polynomials in `k[X]`, with `pₙ ≠ 0`. Here `k[X]` acts on `K⟦X⟧`
through Mathlib's algebra structure `PowerSeries.algebraPolynomial`, so that `p • f` is the
product of `f` with the image of `p`. Typical examples are the exponential series, polynomials,
and, by the closure properties below, all sums and products of these. D-finite series are the
setting of Siegel's E- and G-functions.

Since `pₙ` need not be a unit, the derivatives of `f` do not in general lie in the `k[X]`-span of
the first `n` of them. They do so up to nonzero polynomial factors: every derivative `f⁽ᵐ⁾` has a
nonzero multiple `r • f⁽ᵐ⁾` in the `k[X]`-span of finitely many fixed series
(`PowerSeries.isDFinite_iff_exists_smul_iterate_mem_span`). This is the polynomial form of the
statement that the derivatives of `f` span a finite-dimensional space over the rational
functions `k(X)`, and it is what makes D-finiteness stable under sums, products and
differentiation: the derivatives of `f + g` and of `f * g` are, up to nonzero factors, in the span
of the sums and products of finitely many derivatives of `f` and of `g`. Equivalently, `f` is
D-finite exactly when its derivatives are linearly dependent over `k[X]`
(`PowerSeries.isDFinite_iff_not_linearIndependent`).

## Main definitions

* `PowerSeries.IsDFinite k f`: the series `f` satisfies a nonzero linear differential equation
  with coefficients in `k[X]`.

## Main results

* `PowerSeries.isDFinite_iff_not_linearIndependent`: `f` is D-finite iff its derivatives are
  linearly dependent over `k[X]`.
* `PowerSeries.isDFinite_iff_exists_smul_iterate_mem_span`: `f` is D-finite iff nonzero
  multiples of all its derivatives lie in a finitely generated `k[X]`-submodule.
* `PowerSeries.IsDFinite.add`, `PowerSeries.IsDFinite.mul`, `PowerSeries.IsDFinite.derivative`:
  closure under sums, products and differentiation (with `neg`, `sub` and `iterate_derivative`).
* `PowerSeries.IsDFinite.tower_top`: D-finiteness over `k` implies D-finiteness over every field
  `k'` between `k` and `K`.
* `PowerSeries.isDFinite_polynomial`, `PowerSeries.isDFinite_algebraMap`,
  `PowerSeries.isDFinite_exp`: polynomials over `K` or over `k`, and the exponential series, are
  D-finite.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Southwestern Center for Arithmetic
  Geometry, 2008, §3.1, Proposition 3.2.1.
* R. P. Stanley, *Differentiably finite power series*, European J. Combin. **1** (1980),
  175–188, §2.
-/

public section

open Polynomial

namespace PowerSeries

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]

/-- The polynomial algebra map into power series over a nontrivial field algebra is injective. -/
theorem algebraMap_polynomial_injective [Nontrivial K] :
    Function.Injective (algebraMap k[X] K⟦X⟧) := by
  intro p q hpq
  apply Polynomial.coe_injective (R := k)
  apply map_injective (algebraMap k K) (algebraMap k K).injective
  simpa only [algebraMap_apply'] using hpq

/-! ### The definition -/

variable (k) in
/-- A power series `f : K⟦X⟧` is *D-finite* (holonomic) over the field `k` if it satisfies a
linear differential equation `∑ i ≤ n, pᵢ • f⁽ⁱ⁾ = 0` with polynomial coefficients `pᵢ ∈ k[X]`
and nonzero leading coefficient `pₙ`. -/
def IsDFinite (f : K⟦X⟧) : Prop :=
  ∃ (n : ℕ) (p : Fin (n + 1) → k[X]), p (Fin.last n) ≠ 0 ∧
    ∑ i, p i • (d⁄dX)^[i] f = 0

/-- Unfolding `IsDFinite`: a series is D-finite exactly when it satisfies a linear differential
equation with coefficients in `k[X]` and nonzero leading coefficient. -/
theorem isDFinite_def {f : K⟦X⟧} :
    IsDFinite k f ↔ ∃ (n : ℕ) (p : Fin (n + 1) → k[X]), p (Fin.last n) ≠ 0 ∧
      ∑ i, p i • (d⁄dX)^[i] f = 0 :=
  Iff.rfl

/-- Any nontrivial `k[X]`-linear relation among the first derivatives of `f` yields a
differential equation with nonzero leading coefficient. -/
private theorem isDFinite_of_sum_eq_zero {f : K⟦X⟧} {N : ℕ} {c : Fin (N + 1) → k[X]}
    (hc : c ≠ 0) (h : ∑ i, c i • (d⁄dX)^[i] f = 0) : IsDFinite k f := by
  induction N with
  | zero =>
    refine ⟨0, c, fun h0 ↦ hc (funext fun i ↦ ?_), h⟩
    rwa [Fin.fin_one_eq_zero i]
  | succ N ih =>
    by_cases hlast : c (Fin.last (N + 1)) = 0
    · refine ih (c := fun i ↦ c i.castSucc) (fun h0 ↦ hc (funext fun i ↦ ?_)) ?_
      · induction i using Fin.lastCases with
        | last => exact hlast
        | cast j => exact congrFun h0 j
      · simpa [Fin.sum_univ_castSucc, hlast] using h
    · exact ⟨N + 1, c, hlast, h⟩

/-- A power series is D-finite over `k` exactly when its derivatives are linearly dependent over
`k[X]`. -/
theorem isDFinite_iff_not_linearIndependent {f : K⟦X⟧} :
    IsDFinite k f ↔ ¬LinearIndependent k[X] (fun i : ℕ ↦ (d⁄dX)^[i] f) := by
  constructor
  · rintro ⟨n, p, hp, h⟩ hli
    have := (Fintype.linearIndependent_iff.mp (hli.comp _ Fin.val_injective)) p h (Fin.last n)
    exact hp this
  · intro hli
    obtain ⟨s, g, hg, i, his, hi⟩ := not_linearIndependent_iff.mp hli
    obtain ⟨N, hN⟩ : ∃ N, ∀ j ∈ s, j < N + 1 :=
      ⟨s.sup id, fun j hj ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩
    refine isDFinite_of_sum_eq_zero (N := N) (c := fun j ↦ if (j : ℕ) ∈ s then g j else 0)
      (fun h0 ↦ hi ?_) ?_
    · simpa [his] using congrFun h0 ⟨i, hN i his⟩
    · rw [← hg, Fin.sum_univ_eq_sum_range (fun j ↦ (if j ∈ s then g j else 0) • (d⁄dX)^[j] f),
        ← Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hN j hj))]
      · exact Finset.sum_congr rfl fun j hj ↦ by simp [hj]
      · intro j _ hj
        simp [hj]

/-! ### Finite rank of the module of derivatives -/

/-- **Finite rank characterization of D-finiteness.** A power series `f` is D-finite over `k`
exactly when there is a finite set `s` of series such that every derivative of `f` has a nonzero
`k[X]`-multiple in the `k[X]`-span of `s`. -/
theorem isDFinite_iff_exists_smul_iterate_mem_span {f : K⟦X⟧} :
    IsDFinite k f ↔ ∃ s : Finset K⟦X⟧, ∀ m, ∃ r : k[X], r ≠ 0 ∧
      r • (d⁄dX)^[m] f ∈ Submodule.span k[X] (s : Set K⟦X⟧) := by
  classical
  constructor
  · rintro ⟨n, p, hp, h⟩
    set v : ℕ → K⟦X⟧ := fun i ↦ (d⁄dX)^[i] f
    set S := Submodule.span k[X] ((Finset.range n).image v : Set K⟦X⟧)
    have hmem : ∀ i < n, v i ∈ S := fun i hi ↦
      Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem v
        (Finset.mem_range.mpr hi)))
    -- The leading coefficient brings the `n`-th derivative into `S`.
    have hlast : p (Fin.last n) • v n ∈ S := by
      have h' : p (Fin.last n) • v n = -∑ i : Fin n, p i.castSucc • v i := by
        rw [Fin.sum_univ_castSucc] at h
        exact eq_neg_of_add_eq_zero_right (by simpa [v] using h)
      rw [h']
      exact S.neg_mem (S.sum_mem fun i _ ↦ S.smul_mem _ (hmem i i.isLt))
    have hle : ∀ i ≤ n, p (Fin.last n) • v i ∈ S := fun i hi ↦ by
      rcases hi.lt_or_eq with hi | rfl
      · exact S.smul_mem _ (hmem i hi)
      · exact hlast
    -- `S` is stable under `p (Fin.last n) • d⁄dX`.
    have hS : ∀ y ∈ S, p (Fin.last n) • d⁄dX y ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        have : d⁄dX (v i) = v (i + 1) := (Function.iterate_succ_apply' _ _ _).symm
        rw [this]
        exact hle _ (Finset.mem_range.mp hi)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, smul_add]; exact S.add_mem hy hz
      | smul q y hy' hy =>
        rw [derivative_polynomial_smul, smul_add, smul_smul, smul_comm]
        exact S.add_mem (S.smul_mem _ hy') (S.smul_mem _ hy)
    refine ⟨(Finset.range n).image v, fun m ↦ ?_⟩
    induction m with
    | zero => exact ⟨_, hp, hle 0 (Nat.zero_le n)⟩
    | succ m ih =>
      obtain ⟨r, hr0, hr⟩ := ih
      refine ⟨p (Fin.last n) * r ^ 2, mul_ne_zero hp (pow_ne_zero 2 hr0), ?_⟩
      rw [Function.iterate_succ_apply']
      exact smul_derivative_mem hS hr
  · rintro ⟨s, hs⟩
    obtain ⟨r, hr0, hr⟩ := Submodule.exists_smul_mem_of_forall_exists_smul_mem _
      (Finset.range (s.card + 1)) fun m _ ↦ hs m
    refine isDFinite_iff_not_linearIndependent.mpr fun hli ↦ ?_
    -- The `s.card + 1` series `r • f⁽ⁱ⁾` are independent and lie in the span of `s`.
    have hli' : LinearIndependent k[X] fun i : Fin (s.card + 1) ↦ r • (d⁄dX)^[i] f :=
      (hli.comp _ Fin.val_injective).smul_of_isRightRegular
        (w := fun _ ↦ r) fun _ ↦ (isRegular_iff_ne_zero.mpr hr0).right
    have := linearIndependent_le_span' _ hli' (s : Set K⟦X⟧) (by
      rintro _ ⟨i, rfl⟩
      exact hr i (Finset.mem_range.mpr i.isLt))
    -- This reads `s.card + 1 ≤ s.card`.
    simp at this

/-! ### Closure properties -/

namespace IsDFinite

variable {f g : K⟦X⟧}

/-- The derivative of a D-finite series is D-finite. -/
protected theorem derivative (hf : IsDFinite k f) : IsDFinite k (d⁄dX f) := by
  obtain ⟨s, hs⟩ := isDFinite_iff_exists_smul_iterate_mem_span.mp hf
  refine isDFinite_iff_exists_smul_iterate_mem_span.mpr ⟨s, fun m ↦ ?_⟩
  simpa only [Function.iterate_succ_apply] using hs (m + 1)

/-- Iterated derivatives of a D-finite series are D-finite. -/
protected theorem iterate_derivative (hf : IsDFinite k f) (m : ℕ) :
    IsDFinite k ((d⁄dX)^[m] f) := by
  induction m with
  | zero => exact hf
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.derivative

/-- The sum of two D-finite series is D-finite. -/
protected theorem add (hf : IsDFinite k f) (hg : IsDFinite k g) : IsDFinite k (f + g) := by
  classical
  obtain ⟨s, hs⟩ := isDFinite_iff_exists_smul_iterate_mem_span.mp hf
  obtain ⟨t, ht⟩ := isDFinite_iff_exists_smul_iterate_mem_span.mp hg
  refine isDFinite_iff_exists_smul_iterate_mem_span.mpr ⟨s ∪ t, fun m ↦ ?_⟩
  obtain ⟨r, hr0, hr⟩ := hs m
  obtain ⟨q, hq0, hq⟩ := ht m
  refine ⟨r * q, mul_ne_zero hr0 hq0, ?_⟩
  have hs' := Submodule.span_mono (R := k[X]) (Finset.coe_subset.mpr (s.subset_union_left
    (s₂ := t)))
  have ht' := Submodule.span_mono (R := k[X]) (Finset.coe_subset.mpr (t.subset_union_right
    (s₁ := s)))
  rw [iterate_map_add, smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hs' hr)) (Submodule.smul_mem _ _ (ht' hq))

/-- The negation of a D-finite series is D-finite. -/
protected theorem neg (hf : IsDFinite k f) : IsDFinite k (-f) := by
  obtain ⟨n, p, hp, h⟩ := hf
  exact ⟨n, p, hp, by simp [iterate_map_neg, h]⟩

/-- The difference of two D-finite series is D-finite. -/
protected theorem sub (hf : IsDFinite k f) (hg : IsDFinite k g) : IsDFinite k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The product of two D-finite series is D-finite. -/
protected theorem mul (hf : IsDFinite k f) (hg : IsDFinite k g) : IsDFinite k (f * g) := by
  classical
  obtain ⟨s, hs⟩ := isDFinite_iff_exists_smul_iterate_mem_span.mp hf
  obtain ⟨t, ht⟩ := isDFinite_iff_exists_smul_iterate_mem_span.mp hg
  refine isDFinite_iff_exists_smul_iterate_mem_span.mpr
    ⟨Finset.image₂ (· * ·) s t, fun m ↦ ?_⟩
  obtain ⟨r, hr0, hr⟩ := Submodule.exists_smul_mem_of_forall_exists_smul_mem _
    (Finset.range (m + 1)) fun i _ ↦ hs i
  obtain ⟨q, hq0, hq⟩ := Submodule.exists_smul_mem_of_forall_exists_smul_mem _
    (Finset.range (m + 1)) fun i _ ↦ ht i
  refine ⟨r * q, mul_ne_zero hr0 hq0, ?_⟩
  have hspan : Submodule.span k[X] (s : Set K⟦X⟧) * Submodule.span k[X] (t : Set K⟦X⟧) ≤
      Submodule.span k[X] (Finset.image₂ (· * ·) s t : Set K⟦X⟧) := by
    rw [Submodule.span_mul_span, Finset.coe_image₂]
    rfl
  -- The general Leibniz rule writes `(f * g)⁽ᵐ⁾` through products `f⁽ⁱ⁾ * g⁽ʲ⁾`, `i + j = m`.
  rw [Derivation.iterate_apply_mul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun ij hij ↦ ?_
  have hij' := Finset.mem_antidiagonal.mp hij
  have hi : ij.1 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have hj : ij.2 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  rw [smul_comm, ← smul_mul_smul_comm]
  exact Submodule.smul_of_tower_mem _ _ (hspan (Submodule.mul_mem_mul (hr _ hi) (hq _ hj)))

/-- D-finiteness over `k` implies D-finiteness over any field `k'` between `k` and `K`, that is,
with compatible algebra maps `k → k' → K`. -/
theorem tower_top {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' K]
    [IsScalarTower k k' K] (hf : IsDFinite k f) : IsDFinite k' f := by
  obtain ⟨n, p, hp, h⟩ := hf
  refine ⟨n, fun i ↦ (p i).map (algebraMap k k'), ?_, by
    simpa only [polynomial_map_algebraMap_smul (S := k')] using h⟩
  exact (Polynomial.map_ne_zero_iff (algebraMap k k').injective).mpr hp

end IsDFinite

/-! ### Examples -/

variable (k) in
/-- Every polynomial over `K` is D-finite over `k`: its derivative of order one more than its
degree vanishes. -/
@[simp]
theorem isDFinite_polynomial (p : K[X]) : IsDFinite k (p : K⟦X⟧) := by
  classical
  refine ⟨p.natDegree + 1, Pi.single (Fin.last _) 1, by simp, ?_⟩
  rw [Fintype.sum_eq_single (Fin.last _) fun i hi ↦ by simp [hi], Pi.single_eq_same, one_smul,
    Fin.val_last, iterate_derivative_coe,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _), Polynomial.coe_zero]

/-- The image of a polynomial over `k` is D-finite over `k`. -/
@[simp]
theorem isDFinite_algebraMap (p : k[X]) : IsDFinite k (algebraMap k[X] K⟦X⟧ p) := by
  rw [algebraMap_apply', ← Polynomial.polynomial_map_coe]
  exact isDFinite_polynomial k _

/-- The zero series is D-finite. -/
@[simp]
theorem isDFinite_zero : IsDFinite k (0 : K⟦X⟧) := by
  simpa using isDFinite_algebraMap (k := k) (K := K) 0

/-- The constant series `1` is D-finite. -/
@[simp]
theorem isDFinite_one : IsDFinite k (1 : K⟦X⟧) := by
  simpa using isDFinite_algebraMap (k := k) (K := K) 1

/-- The exponential series is D-finite over every field `k`: it satisfies `f' - f = 0`. -/
@[simp]
theorem isDFinite_exp [Algebra ℚ K] : IsDFinite k (exp K) :=
  ⟨1, ![-1, 1], by simp, by simp [Fin.sum_univ_two, derivative_exp]⟩

end PowerSeries
