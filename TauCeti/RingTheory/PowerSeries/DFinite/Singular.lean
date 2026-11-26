/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.DFinite.Order
public import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Singular points of the minimal equation of a D-finite series

Let `f` be a D-finite power series over a field `k`, of minimal differential order `n`. A point
`ξ` of a `k`-algebra `L` is a *singular point of the minimal equation* of `f` if the leading
coefficient `pₙ` of every minimal equation `∑ i ≤ n, pᵢ f⁽ⁱ⁾ = 0` vanishes at `ξ`.

Quantifying over every minimal equation is essential. Minimal equations are only determined up
to a common factor: multiplying `f' - f = 0` by `X - 1` gives the minimal equation
`(X - 1) f' - (X - 1) f = 0` for the exponential series, whose leading coefficient vanishes at
`1`, although `1` is not a singular point of the exponential. Since any two minimal equations
`p` and `q` satisfy `qₙ pᵢ = pₙ qᵢ` (`PowerSeries.minimal_equation_unique`), the singular points
in a domain are the poles of the coefficients `pᵢ / pₙ` of the normalized operator: for `ξ` in a
domain and a single minimal equation `p`, the point `ξ` is singular exactly when some nonzero
`pᵢ` vanishes at `ξ` to a lower order than `pₙ`
(`PowerSeries.isMinimalSingularPoint_iff_exists_rootMultiplicity_lt`). In particular the singular
points are among the roots of `pₙ`, so a domain contains only finitely many of them, and every
singular point is algebraic over `k`.

A singular point need not be a genuine singularity of the solutions. For `a ∈ k` and a
`k`-algebra `L`, the point `a` of `L` is the only singular point of the minimal equation
`(X - a) f' - (X - a + 1) f = 0` of the series `(X - a) exp(X)`
(`PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp_iff`). Over `ℂ` this singular point is
apparent, which is not formalized here: the equation has order one and its solution space is
spanned by the entire function `(X - a) exp(X)`. By a theorem of André, every singular point
other than `0` of the minimal equation of an E-function is apparent, and this is the input of
Beukers' refinement of the Siegel–Shidlovskii theorem.

## Main definitions

* `PowerSeries.IsMinimalSingularPoint k f ξ`: `f` is D-finite over `k` and the leading
  coefficient of every minimal equation of `f` vanishes at `ξ`.

## Main results

* `PowerSeries.IsDFinite.not_isMinimalSingularPoint_iff`: for a D-finite series, `ξ` is not
  singular exactly when some minimal equation has a leading coefficient that does not vanish at
  `ξ`.
* `PowerSeries.IsMinimalSingularPoint.map`, `PowerSeries.isMinimalSingularPoint_algHom_iff`:
  singular points are preserved by `k`-algebra homomorphisms, and reflected by injective ones.
* `PowerSeries.IsMinimalSingularPoint.isAlgebraic`, `PowerSeries.IsMinimalSingularPoint.isIntegral`:
  singular points are algebraic over `k`.
* `PowerSeries.isMinimalSingularPoint_iff_of_sum_mul_eq_one`: in any `k`-algebra, the singular
  points are exactly the roots of the leading coefficient of a minimal equation whose
  coefficients generate the unit ideal of `k[X]`. Such an equation exists by
  `PowerSeries.IsDFinite.exists_minimal_equation_sum_mul_eq_one`.
* `PowerSeries.isMinimalSingularPoint_of_rootMultiplicity_lt`,
  `PowerSeries.isMinimalSingularPoint_iff_exists_rootMultiplicity_lt`: for points of a domain, the
  criterion by orders of vanishing of the coefficients of one minimal equation.
* `PowerSeries.finite_setOf_isMinimalSingularPoint`: a power series has only finitely many
  singular points in a domain.
* `PowerSeries.not_isMinimalSingularPoint_zero`, `PowerSeries.not_isMinimalSingularPoint_exp`,
  `PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp_iff`: in a nontrivial `k`-algebra, the
  zero series and the exponential series have no singular point, while `a` is the only singular
  point of the minimal equation of `(X - a) exp(X)`.

## References

* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. 163 (2006),
  §1 and §2.
* F. Beukers, *E-functions and G-functions*, Arizona Winter School lecture notes (2008), §3.4.
-/

public section

open Polynomial

namespace PowerSeries

variable {k K L : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing L] [Algebra k L]

variable (k) in
/-- A point `ξ` of a `k`-algebra is a *singular point of the minimal equation* of `f` over `k` if
`f` is D-finite over `k` and the leading coefficient of every differential equation of minimal
order `∑ i ≤ dfiniteOrder k f, pᵢ f⁽ⁱ⁾ = 0` with `pᵢ ∈ k[X]` vanishes at `ξ`. -/
def IsMinimalSingularPoint (f : K⟦X⟧) (ξ : L) : Prop :=
  IsDFinite k f ∧ ∀ p : Fin (dfiniteOrder k f + 1) → k[X],
    ∑ i, p i • (d⁄dX)^[i] f = 0 → Polynomial.aeval ξ (p (Fin.last _)) = 0

/-- Unfolding `PowerSeries.IsMinimalSingularPoint`. -/
theorem isMinimalSingularPoint_def {f : K⟦X⟧} {ξ : L} :
    IsMinimalSingularPoint k f ξ ↔ IsDFinite k f ∧ ∀ p : Fin (dfiniteOrder k f + 1) → k[X],
      ∑ i, p i • (d⁄dX)^[i] f = 0 → Polynomial.aeval ξ (p (Fin.last _)) = 0 :=
  Iff.rfl

/-- A series with a singular point is D-finite. -/
theorem IsMinimalSingularPoint.isDFinite {f : K⟦X⟧} {ξ : L} (h : IsMinimalSingularPoint k f ξ) :
    IsDFinite k f :=
  h.1

/-- At a singular point, the leading coefficient of every equation of minimal order vanishes. -/
theorem IsMinimalSingularPoint.aeval_eq_zero {f : K⟦X⟧} {ξ : L}
    (h : IsMinimalSingularPoint k f ξ) {n : ℕ} (hn : dfiniteOrder k f = n)
    {p : Fin (n + 1) → k[X]} (hp : ∑ i, p i • (d⁄dX)^[i] f = 0) :
    Polynomial.aeval ξ (p (Fin.last n)) = 0 := by
  subst hn
  exact (isMinimalSingularPoint_def.mp h).2 p hp

/-- A point is not singular for the minimal equation of `f` if the leading coefficient of one
equation of minimal order does not vanish there. -/
theorem not_isMinimalSingularPoint_of_aeval_ne_zero {f : K⟦X⟧} {ξ : L} {n : ℕ}
    (hn : dfiniteOrder k f = n) {p : Fin (n + 1) → k[X]} (hp : ∑ i, p i • (d⁄dX)^[i] f = 0)
    (hξ : Polynomial.aeval ξ (p (Fin.last n)) ≠ 0) : ¬IsMinimalSingularPoint k f ξ :=
  fun h ↦ hξ (h.aeval_eq_zero hn hp)

/-- A point is not singular for the minimal equation of a D-finite series exactly when some
equation of minimal order has a leading coefficient that does not vanish there. -/
theorem IsDFinite.not_isMinimalSingularPoint_iff {f : K⟦X⟧} (hf : IsDFinite k f) {ξ : L} :
    ¬IsMinimalSingularPoint k f ξ ↔ ∃ p : Fin (dfiniteOrder k f + 1) → k[X],
      ∑ i, p i • (d⁄dX)^[i] f = 0 ∧ Polynomial.aeval ξ (p (Fin.last _)) ≠ 0 := by
  simp [isMinimalSingularPoint_def, hf]

/-- A `k`-algebra homomorphism maps singular points of the minimal equation of `f` to singular
points. -/
theorem IsMinimalSingularPoint.map {M : Type*} [CommRing M] [Algebra k M] {f : K⟦X⟧} {ξ : L}
    (h : IsMinimalSingularPoint k f ξ) (φ : L →ₐ[k] M) : IsMinimalSingularPoint k f (φ ξ) :=
  ⟨h.isDFinite, fun p hp ↦ by rw [aeval_algHom_apply, h.aeval_eq_zero rfl hp, map_zero]⟩

/-- An injective `k`-algebra homomorphism preserves and reflects singular points of the minimal
equation of `f`. -/
theorem isMinimalSingularPoint_algHom_iff {M : Type*} [CommRing M] [Algebra k M] {f : K⟦X⟧}
    {ξ : L} {φ : L →ₐ[k] M} (hφ : Function.Injective φ) :
    IsMinimalSingularPoint k f (φ ξ) ↔ IsMinimalSingularPoint k f ξ := by
  simp only [isMinimalSingularPoint_def, aeval_algHom_apply, map_eq_zero_iff φ hφ]

/-- A singular point of the minimal equation is algebraic over `k`: it is a root of the nonzero
leading coefficient of a minimal equation. -/
theorem IsMinimalSingularPoint.isAlgebraic {f : K⟦X⟧} {ξ : L} (h : IsMinimalSingularPoint k f ξ) :
    IsAlgebraic k ξ := by
  obtain ⟨p, hp0, hp⟩ := h.isDFinite.exists_minimal_equation
  exact ⟨_, hp0, h.aeval_eq_zero rfl hp⟩

/-- A singular point of the minimal equation is integral over `k`. -/
theorem IsMinimalSingularPoint.isIntegral {f : K⟦X⟧} {ξ : L} (h : IsMinimalSingularPoint k f ξ) :
    IsIntegral k ξ :=
  h.isAlgebraic.isIntegral

/-- A minimal equation of `f` whose coefficients generate the unit ideal of `k[X]` decides every
singular point: `ξ` is singular exactly when the leading coefficient vanishes at `ξ`. Indeed the
leading coefficient of every other minimal equation is a multiple of this one. -/
theorem isMinimalSingularPoint_iff_of_sum_mul_eq_one {f : K⟦X⟧} {ξ : L} {n : ℕ}
    (hn : dfiniteOrder k f = n) {p c : Fin (n + 1) → k[X]}
    (hp : ∑ i, p i • (d⁄dX)^[i] f = 0) (hc : ∑ i, c i * p i = 1) :
    IsMinimalSingularPoint k f ξ ↔ Polynomial.aeval ξ (p (Fin.last n)) = 0 := by
  refine ⟨fun h ↦ h.aeval_eq_zero hn hp, fun hξ ↦ ⟨?_, ?_⟩⟩
  · refine isDFinite_iff_not_linearIndependent.mpr fun hli ↦ one_ne_zero (α := k[X]) ?_
    simp [← hc, Fintype.linearIndependent_iff.mp (hli.comp _ Fin.val_injective) p hp]
  · subst hn
    intro q hq
    have hq : q (Fin.last _) = p (Fin.last _) * ∑ i, c i * q i := by
      calc q (Fin.last _) = ∑ i, c i * (q (Fin.last _) * p i) := by
            conv_lhs => rw [← mul_one (q _), ← hc, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = p (Fin.last _) * ∑ i, c i * q i := by
            simp_rw [minimal_equation_unique hp hq, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hq, map_mul, hξ, zero_mul]

/-- The zero series has no singular point: `1 • f = 0` is an equation of minimal order zero. -/
@[simp]
theorem not_isMinimalSingularPoint_zero [Nontrivial L] {ξ : L} :
    ¬IsMinimalSingularPoint k (0 : K⟦X⟧) ξ :=
  not_isMinimalSingularPoint_of_aeval_ne_zero (p := fun _ ↦ 1) dfiniteOrder_zero (by simp)
    (by simp)

/-- In characteristic zero the exponential series has no singular point: `f' - f = 0` is an
equation of minimal order whose leading coefficient is `1`. -/
@[simp]
theorem not_isMinimalSingularPoint_exp [Algebra ℚ K] [Nontrivial L] {ξ : L} :
    ¬IsMinimalSingularPoint k (exp K) ξ := by
  -- Over the zero ring the exponential series is the zero series.
  cases subsingleton_or_nontrivial K
  · rw [Subsingleton.elim (exp K) 0]
    exact not_isMinimalSingularPoint_zero
  exact not_isMinimalSingularPoint_of_aeval_ne_zero dfiniteOrder_exp
    sum_smul_iterate_derivative_exp (by simp)

section Domain

variable [IsDomain L]

/-- A power series has only finitely many singular points in a domain: they are roots of the
leading coefficient of any one minimal equation. -/
theorem finite_setOf_isMinimalSingularPoint (f : K⟦X⟧) :
    {ξ : L | IsMinimalSingularPoint k f ξ}.Finite := by
  by_cases hf : IsDFinite k f
  · obtain ⟨p, hp0, hp⟩ := hf.exists_minimal_equation
    exact ((p (Fin.last _)).rootSet_finite L).subset fun ξ h ↦
      (mem_rootSet_of_ne hp0).mpr (h.aeval_eq_zero rfl hp)
  · exact Set.finite_empty.subset fun ξ h ↦ hf h.isDFinite

/-- The image of a nonzero polynomial over `k` vanishes to positive order at a point `ξ` of a
domain exactly when it vanishes at `ξ`. -/
private theorem rootMultiplicity_map_pos_iff {p : k[X]} (hp : p ≠ 0) {ξ : L} :
    0 < (p.map (algebraMap k L)).rootMultiplicity ξ ↔ Polynomial.aeval ξ p = 0 := by
  rw [rootMultiplicity_pos (Polynomial.map_ne_zero hp), IsRoot.def, eval_map_algebraMap]

/-- **Singular points from orders of vanishing.** Let `p` be an equation of minimal order for `f`.
If some nonzero coefficient `pᵢ` vanishes at `ξ` to a lower order than the leading coefficient
`pₙ`, then `ξ` is a singular point of the minimal equation: `ξ` is a pole of `pᵢ / pₙ`. -/
theorem isMinimalSingularPoint_of_rootMultiplicity_lt {f : K⟦X⟧} {ξ : L} {n : ℕ}
    (hn : dfiniteOrder k f = n) {p : Fin (n + 1) → k[X]} (hp : ∑ i, p i • (d⁄dX)^[i] f = 0)
    {i : Fin (n + 1)} (hi : p i ≠ 0)
    (hlt : ((p i).map (algebraMap k L)).rootMultiplicity ξ <
      ((p (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ) :
    IsMinimalSingularPoint k f ξ := by
  subst hn
  have hlast : p (Fin.last _) ≠ 0 := by
    rintro h
    simp [h] at hlt
  refine ⟨isDFinite_def.mpr ⟨_, p, hlast, hp⟩, fun q hq ↦ ?_⟩
  -- Any other minimal equation `q` satisfies `qₙ pᵢ = pₙ qᵢ`. Comparing orders of vanishing at
  -- `ξ`, the leading coefficient `qₙ` vanishes at `ξ` to positive order.
  by_cases hq0 : q (Fin.last _) = 0
  · simp [hq0]
  have heq := congrArg (Polynomial.map (algebraMap k L)) (minimal_equation_unique hp hq i)
  rw [Polynomial.map_mul, Polynomial.map_mul] at heq
  have hne : (q (Fin.last _)).map (algebraMap k L) * (p i).map (algebraMap k L) ≠ 0 :=
    mul_ne_zero (Polynomial.map_ne_zero hq0) (Polynomial.map_ne_zero hi)
  have hmul := congrArg (rootMultiplicity ξ) heq
  rw [rootMultiplicity_mul hne, rootMultiplicity_mul (heq ▸ hne)] at hmul
  exact (rootMultiplicity_map_pos_iff hq0).mp (by omega)

/-- **Criterion for singular points.** Let `p` be an equation of minimal order for `f`. Then `ξ` is
a singular point of the minimal equation of `f` exactly when some nonzero coefficient `pᵢ`
vanishes at `ξ` to a lower order than the leading coefficient `pₙ`, that is, when `ξ` is a pole
of some coefficient `pᵢ / pₙ` of the normalized operator. -/
theorem isMinimalSingularPoint_iff_exists_rootMultiplicity_lt {f : K⟦X⟧} {ξ : L} {n : ℕ}
    (hn : dfiniteOrder k f = n) {p : Fin (n + 1) → k[X]} (hp : ∑ i, p i • (d⁄dX)^[i] f = 0)
    (hlast : p (Fin.last n) ≠ 0) :
    IsMinimalSingularPoint k f ξ ↔ ∃ i, p i ≠ 0 ∧
      ((p i).map (algebraMap k L)).rootMultiplicity ξ <
        ((p (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi, hlt⟩ ↦
    isMinimalSingularPoint_of_rootMultiplicity_lt hn hp hi hlt⟩
  by_contra! hge
  -- Suppose every nonzero `pᵢ` vanishes at `ξ` to order at least `m`, the order of `pₙ`. Divide
  -- `p` by a generator `g` of the ideal spanned by its coefficients, giving an equation `q` of
  -- minimal order. Since `g` is a combination of the `pᵢ`, it also vanishes to order at least
  -- `m`, so the leading coefficient `qₙ = pₙ / g` does not vanish at `ξ`.
  obtain ⟨g, q, c, hq, hqlast, hqsum, hc⟩ :=
    exists_eq_mul_of_sum_smul_iterate_derivative_eq_zero hlast hp
  have hg : g ≠ 0 := fun h0 ↦ hlast (by rw [hq, h0, zero_mul])
  replace hc : ∑ i, c i * p i = g := by
    simp_rw [hq, mul_left_comm _ g, ← Finset.mul_sum, hc, mul_one]
  have hgm : ((p (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ ≤
      (g.map (algebraMap k L)).rootMultiplicity ξ := by
    rw [le_rootMultiplicity_iff (Polynomial.map_ne_zero hg), ← hc, Polynomial.map_sum]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [Polynomial.map_mul]
    by_cases hi : p i = 0
    · simp [hi]
    exact ((le_rootMultiplicity_iff (Polynomial.map_ne_zero hi)).mp (hge i hi)).mul_left _
  have hmul : ((p (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ =
      (g.map (algebraMap k L)).rootMultiplicity ξ +
        ((q (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ := by
    have hne : g.map (algebraMap k L) * (q (Fin.last n)).map (algebraMap k L) ≠ 0 := by
      rw [← Polynomial.map_mul, ← hq]
      exact Polynomial.map_ne_zero hlast
    rw [← rootMultiplicity_mul hne, ← Polynomial.map_mul, ← hq]
  have := (rootMultiplicity_map_pos_iff hqlast).mpr (h.aeval_eq_zero hn hqsum)
  omega

end Domain

/-- **The singular point of a minimal equation.** For `a ∈ k`, the series `(X - a) exp(X)`
satisfies the minimal equation `(X - a) f' - (X - a + 1) f = 0`, and `a` is its only singular
point, in every `k`-algebra. Over `ℂ` the singular point is moreover apparent, because the
equation has order one and its solutions are spanned by the entire function `(X - a) exp(X)`. -/
@[simp]
theorem isMinimalSingularPoint_X_sub_C_smul_exp_iff [Nontrivial K] [Algebra ℚ K] (a : k)
    (ξ : L) :
    IsMinimalSingularPoint k ((Polynomial.X - Polynomial.C a : k[X]) • exp K) ξ ↔
      ξ = algebraMap k L a := by
  rw [isMinimalSingularPoint_iff_of_sum_mul_eq_one
    (dfiniteOrder_polynomial_smul_exp (X_sub_C_ne_zero a))
    (sum_smul_iterate_derivative_polynomial_smul_exp _) (c := ![-1, -1])
    (by simp [Fin.sum_univ_two]; ring)]
  simp [sub_eq_zero]

end PowerSeries
