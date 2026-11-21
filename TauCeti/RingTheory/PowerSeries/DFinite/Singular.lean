/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.RingTheory.PowerSeries.DFinite.Order
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Integral
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
are the poles of the coefficients `pᵢ / pₙ` of the normalized operator. In terms of a single
minimal equation `p`, the point `ξ` is singular exactly when some nonzero `pᵢ` vanishes at `ξ` to
a lower order than `pₙ` (`PowerSeries.isMinimalSingularPoint_iff_exists_rootMultiplicity_lt`),
for every `ξ` in a domain. In particular the singular points are among the roots of `pₙ`, so
there are finitely many.

A singular point need not be a genuine singularity of the solutions. The series
`(X - a) exp(X)`, whose minimal equation is `(X - a) f' - (X - a + 1) f = 0`, is an entire
function over `ℂ`, but `a` is a singular point of its minimal equation
(`PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp`); such points are apparent singularities.
By a theorem of André, every singular point other than `0` of the minimal equation of an
E-function is apparent, and this is the input of Beukers' refinement of the Siegel–Shidlovskii
theorem.

## Main definitions

* `PowerSeries.IsMinimalSingularPoint k f ξ`: `f` is D-finite over `k` and the leading
  coefficient of every minimal equation of `f` vanishes at `ξ`.

## Main results

* `PowerSeries.IsDFinite.not_isMinimalSingularPoint_iff`: `ξ` is not singular exactly when some
  minimal equation has a leading coefficient that does not vanish at `ξ`.
* `PowerSeries.isMinimalSingularPoint_of_rootMultiplicity_lt`,
  `PowerSeries.isMinimalSingularPoint_iff_exists_rootMultiplicity_lt`: the criterion by orders of
  vanishing of the coefficients of one minimal equation.
* `PowerSeries.IsDFinite.finite_setOf_isMinimalSingularPoint`: a D-finite series has only
  finitely many singular points in a domain.
* `PowerSeries.not_isMinimalSingularPoint_exp`,
  `PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp`: the exponential series has no singular
  point, while `(X - a) exp(X)` has the apparent singular point `a`.

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
  exact not_isMinimalSingularPoint_of_aeval_ne_zero (p := ![-1, 1]) dfiniteOrder_exp
    (by simp [Fin.sum_univ_two, derivative_exp]) (by simp)

section Domain

variable [IsDomain L]

/-- A D-finite series has only finitely many singular points in a domain: they are roots of the
leading coefficient of any one minimal equation. -/
theorem IsDFinite.finite_setOf_isMinimalSingularPoint {f : K⟦X⟧} (hf : IsDFinite k f) :
    {ξ : L | IsMinimalSingularPoint k f ξ}.Finite := by
  obtain ⟨p, hp0, hp⟩ := hf.exists_minimal_equation
  exact ((p (Fin.last _)).rootSet_finite L).subset fun ξ h ↦
    (mem_rootSet_of_ne hp0).mpr (h.aeval_eq_zero rfl hp)

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
  have heq := congrArg (Polynomial.map (algebraMap k L)) (minimal_equation_unique hp hq i)
  rw [Polynomial.map_mul, Polynomial.map_mul] at heq
  by_cases hq0 : (q (Fin.last _)).map (algebraMap k L) = 0
  · rw [← eval_map_algebraMap, hq0, eval_zero]
  have hne : (q (Fin.last _)).map (algebraMap k L) * (p i).map (algebraMap k L) ≠ 0 :=
    mul_ne_zero hq0 (Polynomial.map_ne_zero hi)
  have hmul := congrArg (rootMultiplicity ξ) heq
  rw [rootMultiplicity_mul hne, rootMultiplicity_mul (heq ▸ hne)] at hmul
  have hpos : 0 < ((q (Fin.last _)).map (algebraMap k L)).rootMultiplicity ξ := by omega
  rw [← eval_map_algebraMap]
  exact (rootMultiplicity_pos hq0).mp hpos

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
  -- Suppose every nonzero `pᵢ` vanishes at `ξ` to order at least that of `pₙ`. Since `ξ` is
  -- singular, `pₙ` vanishes at `ξ`, hence so does every `pᵢ`, and all of them are divisible by
  -- the minimal polynomial `μ` of `ξ`. Dividing by `μ` gives an equation of minimal order with
  -- the same property and a leading coefficient of smaller degree; induct on that degree.
  induction hd : (p (Fin.last n)).natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
  have hroot := h.aeval_eq_zero hn hp
  have hint : IsIntegral k ξ := isAlgebraic_iff_isIntegral.mp ⟨_, hlast, hroot⟩
  have hmap {i} (hi : p i ≠ 0) : (p i).map (algebraMap k L) ≠ 0 := Polynomial.map_ne_zero hi
  have hdvd (i : Fin (n + 1)) : minpoly k ξ ∣ p i := by
    by_cases hi : p i = 0
    · simp [hi]
    refine minpoly.dvd k ξ ?_
    have hpos : 0 < ((p (Fin.last n)).map (algebraMap k L)).rootMultiplicity ξ := by
      rwa [rootMultiplicity_pos (hmap hlast), IsRoot.def, eval_map_algebraMap]
    have := (rootMultiplicity_pos (hmap hi)).mp (hpos.trans_le (hge i hi))
    rwa [IsRoot.def, eval_map_algebraMap] at this
  choose q hq using hdvd
  have hμ : minpoly k ξ ≠ 0 := minpoly.ne_zero hint
  have hqsum : ∑ i, q i • (d⁄dX)^[i] f = 0 := by
    refine (smul_eq_zero_iff_right hμ).mp ?_
    simp_rw [Finset.smul_sum, ← mul_smul, ← hq, hp]
  have hqne {i} (hi : p i ≠ 0) : q i ≠ 0 := by
    rintro h0
    exact hi (by rw [hq i, h0, mul_zero])
  -- Orders of vanishing of `pᵢ = μ qᵢ` at `ξ` split as those of `μ` and `qᵢ`.
  have hmult {i} (hi : p i ≠ 0) : ((p i).map (algebraMap k L)).rootMultiplicity ξ =
      ((minpoly k ξ).map (algebraMap k L)).rootMultiplicity ξ +
        ((q i).map (algebraMap k L)).rootMultiplicity ξ := by
    rw [← rootMultiplicity_mul (by rw [← Polynomial.map_mul, ← hq]; exact hmap hi),
      ← Polynomial.map_mul, ← hq]
  have hlt : (q (Fin.last n)).natDegree < d := by
    rw [← hd, hq (Fin.last n), natDegree_mul hμ (hqne hlast)]
    have := minpoly.natDegree_pos hint
    omega
  refine ih _ hlt hqsum (hqne hlast) (fun i hi ↦ ?_) rfl
  have hpi : p i ≠ 0 := by
    rw [hq i]
    exact mul_ne_zero hμ hi
  have := hge i hpi
  rw [hmult hpi, hmult hlast] at this
  omega

end Domain

/-- **An apparent singular point.** For `a ∈ k`, the series `(X - a) exp(X)` satisfies the
minimal equation `(X - a) f' - (X - a + 1) f = 0`, and `a` is a singular point of its minimal
equation, although over `ℂ` the series is an entire function. -/
theorem isMinimalSingularPoint_X_sub_C_smul_exp [Nontrivial K] [Algebra ℚ K] (a : k) :
    IsMinimalSingularPoint k ((Polynomial.X - Polynomial.C a) • exp K) (algebraMap k L a) := by
  set q : k[X] := Polynomial.X - Polynomial.C a with hq_def
  have hq : q ≠ 0 := X_sub_C_ne_zero a
  have hp : ∑ i, ![-(q + 1), q] i • (d⁄dX)^[i] (q • exp K) = 0 := by
    have hd : Polynomial.derivative q = 1 := by simp [hq_def]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
      Fin.val_one, Function.iterate_zero_apply, Function.iterate_one, derivative_polynomial_smul,
      derivative_exp, hd, smul_smul, ← add_smul]
    convert zero_smul k[X] (exp K) using 2
    ring
  have hn : dfiniteOrder k (q • exp K) = 1 :=
    le_antisymm (dfiniteOrder_le (by simpa using hq) hp) <|
      (isDFinite_def.mpr ⟨1, _, by simpa using hq, hp⟩).dfiniteOrder_pos
        (smul_ne_zero hq (isUnit_exp K).ne_zero)
  -- First `a` is singular as a point of `k`, by the criterion; then the leading coefficient of
  -- every minimal equation vanishes at `a`, hence at its image in `L`.
  have hk : IsMinimalSingularPoint k (q • exp K) a := by
    refine isMinimalSingularPoint_of_rootMultiplicity_lt hn hp (i := 0) ?_ ?_
    · -- The coefficient `-(X - a + 1)` takes the value `-1` at `a`.
      exact fun h ↦ by simpa [hq_def] using congrArg (Polynomial.eval a) h
    · simp [hq_def, rootMultiplicity_eq_zero, X_sub_C_ne_zero]
  refine isMinimalSingularPoint_def.mpr ⟨hk.isDFinite, fun p hp ↦ ?_⟩
  rw [aeval_algebraMap_apply_eq_algebraMap_eval, ← coe_aeval_eq_eval, hk.aeval_eq_zero rfl hp,
    map_zero]

end PowerSeries
