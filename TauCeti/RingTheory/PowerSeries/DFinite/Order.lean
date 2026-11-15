/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.DFinite.Basic
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Minimal differential equations of D-finite series

The order of a D-finite series is the least order of a polynomial-coefficient differential
equation with nonzero leading coefficient. The preceding derivatives are linearly independent
over the polynomial ring. Consequently any two minimal equations are proportional over the
rational function field: cross-multiplying their leading coefficients gives identical rows.
This uniqueness is the algebraic input for discussing the singularities of a minimal equation,
rather than the extra singularities introduced by multiplying an equation by a polynomial.

`PowerSeries.dfiniteOrder` takes the junk value zero on non-D-finite series. Existence of a
minimal equation requires `PowerSeries.IsDFinite`; order zero for a D-finite series means that
the series is zero. No characteristic-zero hypothesis is needed for this algebraic API.

## References

* F. Beukers, *E-functions and G-functions*, Arizona Winter School lecture notes (2008), §3.4.
* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. 163 (2006),
  §2, minimal differential equations.
-/

public noncomputable section

open Polynomial

namespace PowerSeries

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]

open Classical in
variable (k) in
/-- The least order of a nonzero polynomial-coefficient differential equation for `f`.
The value on a series that is not D-finite is zero. -/
def dfiniteOrder (f : K⟦X⟧) : ℕ :=
  if hf : IsDFinite k f then Nat.find (isDFinite_def.mp hf) else 0

/-- A non-D-finite series has the junk order zero. -/
theorem dfiniteOrder_of_not_isDFinite {f : K⟦X⟧} (hf : ¬IsDFinite k f) :
    dfiniteOrder k f = 0 := by
  simp [dfiniteOrder, hf]

/-- A D-finite series admits a differential equation of its minimal order. -/
theorem IsDFinite.exists_minimal_equation {f : K⟦X⟧} (hf : IsDFinite k f) :
    ∃ p : Fin (dfiniteOrder k f + 1) → k[X], p (Fin.last _) ≠ 0 ∧
      ∑ i, p i • (d⁄dX)^[i] f = 0 := by
  classical
  rw [dfiniteOrder, dite_eq_left hf]
  exact Nat.find_spec (isDFinite_def.mp hf)

/-- The minimal order is at most the order of every differential equation with nonzero
leading coefficient. -/
theorem dfiniteOrder_le {f : K⟦X⟧} {n : ℕ} {p : Fin (n + 1) → k[X]}
    (hp : p (Fin.last n) ≠ 0) (h : ∑ i, p i • (d⁄dX)^[i] f = 0) :
    dfiniteOrder k f ≤ n := by
  classical
  have hf : IsDFinite k f := isDFinite_def.mpr ⟨n, p, hp, h⟩
  simpa only [dfiniteOrder, dite_eq_left hf] using
    Nat.find_min' (isDFinite_def.mp hf) ⟨p, hp, h⟩

/-- Every prefix of derivatives of length at most the minimal order is linearly independent
over the polynomial ring. -/
theorem linearIndependent_iterate_derivative_of_le_dfiniteOrder {f : K⟦X⟧}
    {n : ℕ} (hn : n ≤ dfiniteOrder k f) :
    LinearIndependent k[X] (fun i : Fin n ↦ (d⁄dX)^[i] f) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    apply Fintype.linearIndependent_iff.mpr
    intro p hp
    have hlast : p (Fin.last n) = 0 := by
      by_contra hne
      have := dfiniteOrder_le hne hp
      omega
    have hinit : ∑ i : Fin n, p i.castSucc • (d⁄dX)^[i] f = 0 := by
      simpa only [Fin.sum_univ_castSucc, Fin.val_castSucc, hlast, zero_smul, add_zero] using hp
    have hcoeff := Fintype.linearIndependent_iff.mp (ih (by omega)) _ hinit
    intro i
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast i => exact hcoeff i

/-- The first `n` derivatives are independent exactly up to the minimal differential order. -/
theorem IsDFinite.linearIndependent_iterate_derivative_iff {f : K⟦X⟧}
    (hf : IsDFinite k f) (n : ℕ) :
    LinearIndependent k[X] (fun i : Fin n ↦ (d⁄dX)^[i] f) ↔ n ≤ dfiniteOrder k f := by
  refine ⟨fun hli ↦ ?_, linearIndependent_iterate_derivative_of_le_dfiniteOrder⟩
  by_contra hn
  obtain ⟨p, hp, h⟩ := hf.exists_minimal_equation
  have hli' := hli.comp (Fin.castLE (by omega : dfiniteOrder k f + 1 ≤ n))
    (Fin.castLE_injective _)
  exact hp (Fintype.linearIndependent_iff.mp hli' p h (Fin.last _))

/-- An equation is minimal if its preceding derivatives are linearly independent. -/
theorem dfiniteOrder_eq {f : K⟦X⟧} {n : ℕ} {p : Fin (n + 1) → k[X]}
    (hp : p (Fin.last n) ≠ 0) (h : ∑ i, p i • (d⁄dX)^[i] f = 0)
    (hli : LinearIndependent k[X] (fun i : Fin n ↦ (d⁄dX)^[i] f)) :
    dfiniteOrder k f = n := by
  have hf : IsDFinite k f := isDFinite_def.mpr ⟨n, p, hp, h⟩
  exact Nat.le_antisymm (dfiniteOrder_le hp h)
    ((hf.linearIndependent_iterate_derivative_iff n).mp hli)

/-- Two minimal equations have identical coefficients after cross-multiplication by their
leading coefficients. Thus their normalized rational differential operators are equal. -/
theorem minimal_equation_unique {f : K⟦X⟧}
    {p q : Fin (dfiniteOrder k f + 1) → k[X]}
    (hp : ∑ i, p i • (d⁄dX)^[i] f = 0) (hq : ∑ i, q i • (d⁄dX)^[i] f = 0)
    (i : Fin (dfiniteOrder k f + 1)) :
    q (Fin.last _) * p i = p (Fin.last _) * q i := by
  have hrel : ∑ i, (q (Fin.last _) * p i - p (Fin.last _) * q i) •
      (d⁄dX)^[i] f = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hp, hq,
      smul_zero, sub_self]
  have hlast : q (Fin.last _) * p (Fin.last _) - p (Fin.last _) * q (Fin.last _) = 0 :=
    sub_eq_zero.mpr (mul_comm _ _)
  have hinit : ∑ j : Fin (dfiniteOrder k f),
      (q (Fin.last _) * p j.castSucc - p (Fin.last _) * q j.castSucc) •
        (d⁄dX)^[j] f = 0 := by
    simpa only [Fin.sum_univ_castSucc, Fin.val_castSucc, hlast, zero_smul, add_zero] using hrel
  induction i using Fin.lastCases with
  | last => exact mul_comm _ _
  | cast i =>
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp
      (linearIndependent_iterate_derivative_of_le_dfiniteOrder (k := k) (f := f) le_rfl)
      _ hinit i)

/-- The zero series has minimal differential order zero. -/
@[simp]
theorem dfiniteOrder_zero : dfiniteOrder k (0 : K⟦X⟧) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dfiniteOrder_le (p := fun _ : Fin 1 ↦ 1) one_ne_zero (by simp)

/-- For a D-finite series, order zero is equivalent to vanishing. -/
@[simp]
theorem IsDFinite.dfiniteOrder_eq_zero_iff {f : K⟦X⟧} (hf : IsDFinite k f) :
    dfiniteOrder k f = 0 ↔ f = 0 := by
  constructor
  · intro horder
    have hex := hf.exists_minimal_equation
    rw [horder] at hex
    obtain ⟨p, hp, h⟩ := hex
    have heq : p (Fin.last 0) • f = 0 := by simpa using h
    exact (smul_eq_zero_iff_right hp).mp heq
  · rintro rfl
    exact dfiniteOrder_zero

/-- A nonzero D-finite series has positive differential order. -/
theorem IsDFinite.dfiniteOrder_pos {f : K⟦X⟧} (hf : IsDFinite k f) (hf0 : f ≠ 0) :
    0 < dfiniteOrder k f :=
  Nat.pos_of_ne_zero (hf.dfiniteOrder_eq_zero_iff.not.mpr hf0)

/-- A nonzero constant has differential order one. -/
@[simp]
theorem dfiniteOrder_C {a : K} (ha : a ≠ 0) : dfiniteOrder k (C a) = 1 := by
  have hf : IsDFinite k (C a) := by
    simpa using isDFinite_polynomial k (Polynomial.C a)
  apply Nat.le_antisymm _ (hf.dfiniteOrder_pos (fun h ↦ ha (by
    simpa using congrArg constantCoeff h)))
  exact dfiniteOrder_le (p := ![0, 1]) (by simp) (by simp [Fin.sum_univ_two])

/-- The constant series one has differential order one. -/
@[simp]
theorem dfiniteOrder_one [Nontrivial K] : dfiniteOrder k (1 : K⟦X⟧) = 1 := by
  simpa only [map_one] using dfiniteOrder_C (k := k) (K := K) one_ne_zero

/-- In characteristic zero the formal exponential has differential order one. -/
@[simp]
theorem dfiniteOrder_exp [Nontrivial K] [Algebra ℚ K] : dfiniteOrder k (exp K) = 1 := by
  apply Nat.le_antisymm _
    ((isDFinite_exp (k := k) (K := K)).dfiniteOrder_pos (isUnit_exp K).ne_zero)
  exact dfiniteOrder_le (p := ![-1, 1]) (by simp) (by
    simp [Fin.sum_univ_two, derivative_exp])

end PowerSeries
