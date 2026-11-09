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
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Pochhammer

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

On coefficients, D-finiteness is a polynomial recurrence: `f = ∑ aₙ Xⁿ` is D-finite over `k`
exactly when `∑ i ≤ r, qᵢ(n) aₙ₊ᵢ = 0` for all `n`, for some polynomials `qᵢ ∈ k[X]` with
`q_r ≠ 0` (`PowerSeries.isDFinite_iff_pRecursive`). Comparing coefficients of `Xⁿ⁺ᵈ` in a
differential equation whose coefficients have degree at most `d` gives the recurrence, since
`Xʲ f⁽ⁱ⁾` contributes `(n + d - j + i) (n + d - j + i - 1) ⋯ (n + d - j + 1) aₙ₊d₋ⱼ₊ᵢ`.
Conversely, writing each `qᵢ(m - i)` in the basis of falling factorials
`m (m - 1) ⋯ (m - l + 1)`, which are the multipliers of the coefficients of `Xˡ f⁽ˡ⁾`, turns the
recurrence into a `k[X]`-combination of derivatives of `f` that is a polynomial of degree less
than `r`; differentiating it `r` more times gives a differential equation.

## Main definitions

* `PowerSeries.IsDFinite k f`: the series `f` satisfies a nonzero linear differential equation
  with coefficients in `k[X]`.

## Main results

* `PowerSeries.isDFinite_iff_not_linearIndependent`: `f` is D-finite iff its derivatives are
  linearly dependent over `k[X]`.
* `PowerSeries.isDFinite_iff_exists_smul_iterate_mem_span`: `f` is D-finite iff nonzero
  multiples of all its derivatives lie in a finitely generated `k[X]`-submodule.
* `PowerSeries.isDFinite_iff_pRecursive`: `f` is D-finite iff its coefficient sequence is
  P-recursive, that is, satisfies a linear recurrence with coefficients in `k[X]`.
* `PowerSeries.IsDFinite.add`, `PowerSeries.IsDFinite.mul`, `PowerSeries.IsDFinite.derivative`:
  closure under sums, products and differentiation (with `neg`, `sub` and `iterate_derivative`).
* `PowerSeries.IsDFinite.tower_top`: D-finiteness over `k` implies D-finiteness over every field
  `k'` between `k` and `K`.
* `PowerSeries.isDFinite_polynomial`, `PowerSeries.isDFinite_algebraMap`,
  `PowerSeries.isDFinite_exp`, `PowerSeries.isDFinite_mk_pow`: polynomials over `K` or over `k`,
  the exponential series and the geometric series with ratio in `k` are D-finite.

## References

* F. Beukers, *E-functions and G-functions*, lecture notes, Southwestern Center for Arithmetic
  Geometry, 2008, §3.1, Proposition 3.2.1.
* R. P. Stanley, *Differentiably finite power series*, European J. Combin. **1** (1980),
  175–188, §2.
* R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press, 1999,
  Proposition 6.4.3.
-/

public section

open Polynomial

namespace PowerSeries

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]

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

/-- If a property of families `Fin (N + 1) → M` survives dropping a vanishing last entry, then a
nonzero family with the property can be shortened to one with nonzero last entry. -/
private theorem exists_last_ne_zero_of_ne_zero {M : Type*} [Zero M]
    {P : ∀ N : ℕ, (Fin (N + 1) → M) → Prop}
    (hP : ∀ N c, c (Fin.last (N + 1)) = 0 → P (N + 1) c → P N fun i ↦ c i.castSucc)
    {N : ℕ} {c : Fin (N + 1) → M} (hc : c ≠ 0) (h : P N c) :
    ∃ (N : ℕ) (c : Fin (N + 1) → M), c (Fin.last N) ≠ 0 ∧ P N c := by
  induction N with
  | zero =>
    refine ⟨0, c, fun h0 ↦ hc (funext fun i ↦ ?_), h⟩
    rwa [Fin.fin_one_eq_zero i]
  | succ N ih =>
    by_cases hlast : c (Fin.last (N + 1)) = 0
    · refine ih (c := fun i ↦ c i.castSucc) (fun h0 ↦ hc (funext fun i ↦ ?_)) (hP N c hlast h)
      induction i using Fin.lastCases with
      | last => exact hlast
      | cast j => exact congrFun h0 j
    · exact ⟨N + 1, c, hlast, h⟩

/-- Any nontrivial `k[X]`-linear relation among the first derivatives of `f` yields a
differential equation with nonzero leading coefficient. -/
private theorem isDFinite_of_sum_eq_zero {f : K⟦X⟧} {N : ℕ} {c : Fin (N + 1) → k[X]}
    (hc : c ≠ 0) (h : ∑ i, c i • (d⁄dX)^[i] f = 0) : IsDFinite k f :=
  exists_last_ne_zero_of_ne_zero (P := fun N (c : Fin (N + 1) → k[X]) ↦
    ∑ i, c i • (d⁄dX)^[i] f = 0)
    (fun _ _ hlast h ↦ by simpa [Fin.sum_univ_castSucc, hlast] using h) hc h

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

/-! ### Polynomial recurrences for the coefficients -/

section Recurrence

variable {f : K⟦X⟧}

variable (k) in
/-- The `k[X]`-span of the first `m` derivatives `f, f', …, f⁽ᵐ⁻¹⁾` of `f`. -/
private noncomputable abbrev derivSpan (f : K⟦X⟧) (m : ℕ) : Submodule k[X] K⟦X⟧ :=
  Submodule.span k[X] (Set.range fun l : Fin m ↦ (d⁄dX)^[l] f)

private theorem iterate_mem_derivSpan {l m : ℕ} (h : l < m) :
    (d⁄dX)^[l] f ∈ derivSpan k f m :=
  Submodule.subset_span ⟨⟨l, h⟩, rfl⟩

private theorem derivSpan_mono {m m' : ℕ} (h : m ≤ m') : derivSpan k f m ≤ derivSpan k f m' :=
  Submodule.span_mono <| Set.range_subset_iff.mpr fun l ↦ ⟨⟨l, l.isLt.trans_le h⟩, rfl⟩

private theorem derivative_mem_derivSpan {m : ℕ} {y : K⟦X⟧} (hy : y ∈ derivSpan k f m) :
    d⁄dX y ∈ derivSpan k f (m + 1) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    rw [← Function.iterate_succ_apply' (d⁄dX)]
    exact iterate_mem_derivSpan (by omega)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul q y hy' hy =>
    rw [derivative_polynomial_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (derivSpan_mono (Nat.le_succ m) hy'))
      (Submodule.smul_mem _ _ hy)

/-- If `y` agrees with `b • f⁽ᵐ⁾` modulo the lower derivatives, then `y⁽ʳ⁾` agrees with
`b • f⁽ᵐ⁺ʳ⁾` modulo the lower derivatives. -/
private theorem iterate_derivative_sub_smul_mem {b : k[X]} {m : ℕ} {y : K⟦X⟧}
    (hy : y - b • (d⁄dX)^[m] f ∈ derivSpan k f m) (r : ℕ) :
    (d⁄dX)^[r] y - b • (d⁄dX)^[m + r] f ∈ derivSpan k f (m + r) := by
  induction r with
  | zero => exact hy
  | succ r ih =>
    have key : (d⁄dX)^[r + 1] y - b • (d⁄dX)^[m + (r + 1)] f =
        d⁄dX ((d⁄dX)^[r] y - b • (d⁄dX)^[m + r] f) +
          Polynomial.derivative b • (d⁄dX)^[m + r] f := by
      rw [map_sub, derivative_polynomial_smul, Function.iterate_succ_apply',
        ← add_assoc m r 1, Function.iterate_succ_apply' _ (m + r)]
      abel
    rw [key, ← add_assoc]
    exact Submodule.add_mem _ (derivative_mem_derivSpan ih)
      (Submodule.smul_mem _ _ (iterate_mem_derivSpan (Nat.lt_succ_self _)))

/-- If a series `y` with vanishing `r`-th derivative is `b • f⁽ᵐ⁾` with `b ≠ 0` modulo the lower
derivatives of `f`, then `f` is D-finite. -/
private theorem isDFinite_of_sub_smul_mem {b : k[X]} (hb : b ≠ 0) {m r : ℕ} {y : K⟦X⟧}
    (hy : y - b • (d⁄dX)^[m] f ∈ derivSpan k f m) (hr : (d⁄dX)^[r] y = 0) :
    IsDFinite k f := by
  have h := iterate_derivative_sub_smul_mem hy r
  rw [hr, zero_sub, Submodule.neg_mem_iff] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  refine ⟨m + r, Fin.snoc (α := fun _ ↦ k[X]) (-c) b, by simpa using hb, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [hc]

/-- **Falling factorial expansion.** If `P` has degree at most `e`, the series `∑ₘ P(m) aₘ Xᵐ`,
where `f = ∑ₘ aₘ Xᵐ`, is a `k[X]`-combination of `f, f', …, f⁽ᵉ⁾` whose coefficient on `f⁽ᵉ⁾` is
`P.coeff e • Xᵉ`. -/
private theorem exists_coeff_eq_eval_smul (f : K⟦X⟧) {e : ℕ} {P : k[X]} (hP : P.natDegree ≤ e) :
    ∃ G : K⟦X⟧, (∀ M : ℕ, coeff M G = P.eval (M : k) • coeff M f) ∧
      G - (Polynomial.C (P.coeff e) * Polynomial.X ^ e) • (d⁄dX)^[e] f ∈ derivSpan k f e := by
  induction e generalizing P with
  | zero =>
    refine ⟨(Polynomial.C (P.coeff 0) * Polynomial.X ^ 0) • (d⁄dX)^[0] f, fun M ↦ ?_, by simp⟩
    rw [mul_smul, polynomial_C_smul, polynomial_X_pow_smul, coeff_smul,
      coeff_X_pow_mul_iterate_derivative, Polynomial.eq_C_of_natDegree_le_zero hP]
    simp
  | succ e ih =>
    set a := P.coeff (e + 1)
    set P' := P - Polynomial.C a * descPochhammer k (e + 1) with hP'_def
    have hd := descPochhammer_natDegree k (e + 1)
    have hP' : P'.natDegree ≤ e := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rcases (Nat.succ_le_of_lt hN).eq_or_lt with rfl | hN
      · have h1 := (monic_descPochhammer k (e + 1)).coeff_natDegree
        rw [hd] at h1
        rw [hP'_def, Polynomial.coeff_sub, Polynomial.coeff_C_mul, h1, mul_one, sub_self]
      · rw [hP'_def, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hN),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hN), mul_zero, sub_zero]
    obtain ⟨G, hG, hGmem⟩ := ih hP'
    refine ⟨G + (Polynomial.C a * Polynomial.X ^ (e + 1)) • (d⁄dX)^[e + 1] f, fun M ↦ ?_, ?_⟩
    · rw [map_add, hG, mul_smul, polynomial_C_smul, polynomial_X_pow_smul, coeff_smul,
        coeff_X_pow_mul_iterate_derivative, hP'_def,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        descPochhammer_eval_eq_descFactorial]
      simp only [Algebra.smul_def, map_sub, map_mul, map_natCast]
      ring
    · rw [add_sub_cancel_right]
      have hmem := Submodule.add_mem _ (derivSpan_mono (Nat.le_succ e) hGmem)
        (Submodule.smul_mem _ (Polynomial.C (P'.coeff e) * Polynomial.X ^ e)
          (iterate_mem_derivSpan (f := f) (Nat.lt_succ_self e)))
      rwa [sub_add_cancel] at hmem

/-- If the series `G t` have coefficients `q t (M - t) • aₘ`, where the `q t` give a recurrence for
the coefficients `aₘ` of `f`, then `∑ t, Xʳ⁻ᵗ • G t` has no coefficients of index `r` or more, so
its `r`-th derivative vanishes. -/
private theorem iterate_derivative_sum_X_pow_smul_eq_zero {r : ℕ} {q : Fin (r + 1) → k[X]}
    (h : ∀ n : ℕ, ∑ i, (q i).eval (n : k) • coeff (n + i) f = 0) {G : Fin (r + 1) → K⟦X⟧}
    (hG : ∀ t M, coeff M (G t) = (Polynomial.taylor (-(t : k)) (q t)).eval (M : k) • coeff M f) :
    (d⁄dX)^[r] (∑ t : Fin (r + 1), (Polynomial.X ^ (r - (t : ℕ)) : k[X]) • G t) = 0 := by
  ext M
  rw [coeff_iterate_derivative, map_zero]
  suffices hM : coeff (M + r)
      (∑ t : Fin (r + 1), (Polynomial.X ^ (r - (t : ℕ)) : k[X]) • G t) = 0 by
    rw [hM, mul_zero]
  rw [map_sum, ← h M]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have ht := t.isLt
  rw [polynomial_X_pow_smul, coeff_X_pow_mul']
  simp only [show r - (t : ℕ) ≤ M + r by omega, ↓reduceIte]
  rw [show M + r - (r - t) = M + t by omega, hG, Polynomial.taylor_eval]
  push_cast
  rw [add_neg_cancel_right]

/-- A series whose coefficients satisfy a polynomial recurrence with nonzero leading coefficient
is D-finite. -/
private theorem isDFinite_of_recurrence {r : ℕ} {q : Fin (r + 1) → k[X]}
    (hq : q (Fin.last r) ≠ 0) (h : ∀ n : ℕ, ∑ i, (q i).eval (n : k) • coeff (n + i) f = 0) :
    IsDFinite k f := by
  classical
  set e := Finset.univ.sup fun t ↦ (q t).natDegree
  have hle : ∀ t, (q t).natDegree ≤ e := fun t ↦
    Finset.le_sup (f := fun t ↦ (q t).natDegree) (Finset.mem_univ t)
  -- The series `G t` has coefficients `q t (M - t) • aₘ`.
  choose G hG hGmem using fun t : Fin (r + 1) ↦ exists_coeff_eq_eval_smul (k := k) f
    (P := Polynomial.taylor (-(t : k)) (q t)) ((Polynomial.natDegree_taylor _ _).trans_le (hle t))
  set c : Fin (r + 1) → k := fun t ↦ (Polynomial.taylor (-(t : k)) (q t)).coeff e
  refine isDFinite_of_sub_smul_mem
    (y := ∑ t : Fin (r + 1), (Polynomial.X ^ (r - (t : ℕ)) : k[X]) • G t)
    (b := ∑ t : Fin (r + 1), Polynomial.C (c t) * Polynomial.X ^ (r - (t : ℕ) + e))
    (m := e) (r := r) ?_ ?_ ?_
  · -- Some `q t` of maximal degree `e` is nonzero, and its leading coefficient survives.
    obtain ⟨t₀, -, ht₀⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      fun t ↦ (q t).natDegree
    obtain ⟨t₁, ht₁, hdeg⟩ : ∃ t, q t ≠ 0 ∧ (q t).natDegree = e := by
      by_cases h0 : q t₀ = 0
      · exact ⟨Fin.last r, hq, le_antisymm (hle _) (by simp [e, ht₀, h0])⟩
      · exact ⟨t₀, h0, ht₀.symm⟩
    have hc : c t₁ ≠ 0 := by
      simpa only [c, ← hdeg, Polynomial.coeff_taylor_natDegree] using
        Polynomial.leadingCoeff_ne_zero.mpr ht₁
    intro hb
    have hcoeff := congrArg (Polynomial.coeff · (r - t₁ + e)) hb
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single t₁ (fun t _ ht ↦ ite_eq_right_iff.mpr fun h ↦
      absurd (Fin.ext (by omega)) ht) (by simp)] at hcoeff
    exact hc (by simpa using hcoeff)
  · have hsum : ∑ t : Fin (r + 1), (Polynomial.X ^ (r - (t : ℕ)) : k[X]) • G t -
        (∑ t : Fin (r + 1), Polynomial.C (c t) * Polynomial.X ^ (r - (t : ℕ) + e)) •
          (d⁄dX)^[e] f =
        ∑ t : Fin (r + 1), (Polynomial.X ^ (r - (t : ℕ)) : k[X]) •
          (G t - (Polynomial.C (c t) * Polynomial.X ^ e) • (d⁄dX)^[e] f) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [smul_sub, smul_smul, pow_add, mul_left_comm]
    rw [hsum]
    exact Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (hGmem t)
  · exact iterate_derivative_sum_X_pow_smul_eq_zero h hG

/-- For `p` of degree at most `d`, the coefficient of `Xᴺ⁺ᵈ` in `p • f⁽ⁱ⁾` is a combination of the
coefficients `a_{N + d - j + i}`, `j ≤ d`, of `f`. -/
private theorem coeff_add_smul_iterate_derivative (f : K⟦X⟧) {p : k[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (i N : ℕ) :
    coeff (N + d) (p • (d⁄dX)^[i] f) = ∑ j : Fin (d + 1),
      (p.coeff j * ((N + (d - j + i)).descFactorial i : k)) • coeff (N + (d - j + i)) f := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp),
    ← Fin.sum_univ_eq_sum_range, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj := j.isLt
  rw [mul_smul (Polynomial.C _), polynomial_C_smul, polynomial_X_pow_smul, coeff_smul,
    coeff_X_pow_mul']
  simp only [show (j : ℕ) ≤ N + d by omega, ↓reduceIte]
  rw [coeff_iterate_derivative_eq_descFactorial, show N + d - j + i = N + (d - j + i) by omega,
    mul_smul, Algebra.smul_def (A := K) ((N + (d - j + i)).descFactorial i : k), map_natCast]

/-- In a differential equation `∑ i ≤ n, pᵢ • f⁽ⁱ⁾ = 0` whose coefficients have degree at most `d`,
the term `pᵢⱼ Xʲ f⁽ⁱ⁾` contributes to the coefficient recurrence at the shift `d - j + i`. -/
private def recurrenceShift (n d : ℕ) (x : Fin (n + 1) × Fin (d + 1)) : Fin (d + n + 1) :=
  ⟨d - x.2 + x.1, by omega⟩

/-- The polynomial coefficient at shift `t` of the coefficient recurrence attached to the
differential equation `∑ i ≤ n, pᵢ • f⁽ⁱ⁾ = 0`, when every `pᵢ` has degree at most `d`. -/
private noncomputable def recurrencePoly {n : ℕ} (p : Fin (n + 1) → k[X]) (d : ℕ)
    (t : Fin (d + n + 1)) : k[X] :=
  ∑ x with recurrenceShift n d x = t,
    Polynomial.C ((p x.1).coeff x.2) * Polynomial.taylor (t : k) (descPochhammer k x.1)

/-- The recurrence attached to a differential equation with nonzero leading coefficient is
nontrivial: the leading coefficient of `pₙ` is the coefficient of degree `n` of one of its
polynomials. -/
private theorem recurrencePoly_ne_zero {n d : ℕ} {p : Fin (n + 1) → k[X]}
    (hp : p (Fin.last n) ≠ 0) (hle : (p (Fin.last n)).natDegree ≤ d) :
    recurrencePoly p d ≠ 0 := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (d + 1), (j₀ : ℕ) = (p (Fin.last n)).natDegree :=
    ⟨⟨_, Nat.lt_succ_of_le hle⟩, rfl⟩
  intro hq
  have hcoeff := congrArg (Polynomial.coeff · n)
    (congrFun hq (recurrenceShift n d (Fin.last n, j₀)))
  simp only [recurrencePoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Pi.zero_apply,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single (Fin.last n, j₀)] at hcoeff
  · have h1 := Polynomial.coeff_taylor_natDegree
      (r := ((recurrenceShift n d (Fin.last n, j₀) : ℕ) : k)) (f := descPochhammer k n)
    rw [descPochhammer_natDegree, (monic_descPochhammer k n).leadingCoeff] at h1
    rw [Fin.val_last, h1, mul_one, hj₀] at hcoeff
    exact hp (Polynomial.leadingCoeff_eq_zero.mp hcoeff)
  · rintro x hx hne
    rw [Finset.mem_filter] at hx
    by_cases hx1 : x.1 = Fin.last n
    · refine absurd (Prod.ext hx1 (Fin.ext (show (x.2 : ℕ) = j₀ from ?_))) hne
      have h2 : d - (x.2 : ℕ) + x.1 = d - j₀ + n := congrArg Fin.val hx.2
      rw [hx1, Fin.val_last] at h2
      have := x.2.isLt
      have := j₀.isLt
      omega
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (p := Polynomial.taylor _ (descPochhammer k x.1)), mul_zero]
      rw [Polynomial.natDegree_taylor, descPochhammer_natDegree]
      exact lt_of_le_of_ne (Nat.lt_succ_iff.mp x.1.isLt) (fun h ↦ hx1 (Fin.ext h))
  · simp

/-- The left side of the recurrence attached to `∑ i ≤ n, pᵢ • f⁽ⁱ⁾` at `N` is the coefficient of
`Xᴺ⁺ᵈ` in that sum. -/
private theorem sum_eval_recurrencePoly_smul {n d : ℕ} {p : Fin (n + 1) → k[X]}
    (hle : ∀ i, (p i).natDegree ≤ d) (N : ℕ) :
    ∑ t, (recurrencePoly p d t).eval (N : k) • coeff (N + t) f =
      coeff (N + d) (∑ i, p i • (d⁄dX)^[i] f) := by
  classical
  rw [map_sum]
  calc ∑ t, (recurrencePoly p d t).eval (N : k) • coeff (N + t) f
      = ∑ t, ∑ x with recurrenceShift n d x = t, ((p x.1).coeff x.2 *
          ((N + recurrenceShift n d x : ℕ).descFactorial x.1 : k)) •
            coeff (N + recurrenceShift n d x) f := by
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [recurrencePoly, Polynomial.eval_finsetSum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rw [(Finset.mem_filter.mp hx).2, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.taylor_eval, ← descPochhammer_eval_eq_descFactorial, Nat.cast_add]
    _ = ∑ x : Fin (n + 1) × Fin (d + 1), ((p x.1).coeff x.2 *
          ((N + recurrenceShift n d x : ℕ).descFactorial x.1 : k)) •
            coeff (N + recurrenceShift n d x) f :=
        Finset.sum_fiberwise _ (recurrenceShift n d) fun x ↦ ((p x.1).coeff x.2 *
          ((N + recurrenceShift n d x : ℕ).descFactorial x.1 : k)) •
            coeff (N + recurrenceShift n d x) f
    _ = ∑ i, coeff (N + d) (p i • (d⁄dX)^[i] f) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ ↦
          (coeff_add_smul_iterate_derivative f (hle i) i N).symm

/-- The coefficients of a D-finite series satisfy a nontrivial polynomial recurrence. -/
private theorem exists_recurrence_of_isDFinite (hf : IsDFinite k f) :
    ∃ (r : ℕ) (q : Fin (r + 1) → k[X]), q ≠ 0 ∧
      ∀ n : ℕ, ∑ i, (q i).eval (n : k) • coeff (n + i) f = 0 := by
  obtain ⟨n, p, hp, h⟩ := hf
  have hle : ∀ i, (p i).natDegree ≤ Finset.univ.sup fun i ↦ (p i).natDegree := fun i ↦
    Finset.le_sup (f := fun i ↦ (p i).natDegree) (Finset.mem_univ i)
  refine ⟨_, recurrencePoly p _, recurrencePoly_ne_zero hp (hle _), fun N ↦ ?_⟩
  rw [sum_eval_recurrencePoly_smul hle, h, map_zero]

/-- **D-finite series are P-recursive.** A power series `f = ∑ aₙ Xⁿ` is D-finite over `k` exactly
when its coefficients satisfy a linear recurrence `∑ i ≤ r, qᵢ(n) aₙ₊ᵢ = 0` for every `n`, with
polynomial coefficients `qᵢ ∈ k[X]` and nonzero leading coefficient `q_r`. -/
theorem isDFinite_iff_pRecursive :
    IsDFinite k f ↔ ∃ (r : ℕ) (q : Fin (r + 1) → k[X]), q (Fin.last r) ≠ 0 ∧
      ∀ n : ℕ, ∑ i, (q i).eval (n : k) • coeff (n + i) f = 0 := by
  refine ⟨fun hf ↦ ?_, fun ⟨_, _, hq, h⟩ ↦ isDFinite_of_recurrence hq h⟩
  obtain ⟨r, q, hq, h⟩ := exists_recurrence_of_isDFinite hf
  -- A nontrivial recurrence can be shortened to one with nonzero leading coefficient.
  exact exists_last_ne_zero_of_ne_zero (P := fun r (q : Fin (r + 1) → k[X]) ↦
    ∀ n : ℕ, ∑ i, (q i).eval (n : k) • coeff (n + i) f = 0)
    (fun _ _ hlast h n ↦ by simpa [Fin.sum_univ_castSucc, hlast] using h n) hq h

end Recurrence

variable (k) in
/-- The geometric series `∑ aⁿ Xⁿ` with ratio `a ∈ k` is D-finite over `k`: its coefficients
satisfy the recurrence `aₙ₊₁ - a aₙ = 0`. -/
@[simp]
theorem isDFinite_mk_pow (a : k) : IsDFinite k (mk fun n ↦ algebraMap k K a ^ n) :=
  isDFinite_iff_pRecursive.mpr ⟨1, ![Polynomial.C (-a), 1], by simp, fun n ↦ by
    simp only [Nat.reduceAdd, map_neg, coeff_mk, Algebra.smul_def, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Polynomial.eval_neg, Polynomial.eval_C, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, add_zero, neg_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Polynomial.eval_one, map_one, Nat.mod_succ, pow_succ, one_mul]
    ring⟩

end PowerSeries
