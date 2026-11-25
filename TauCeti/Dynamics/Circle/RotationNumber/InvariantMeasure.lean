/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Rational rotation number and an invariant measure of full support

Let `f` be a continuous strictly increasing lift of a circle homeomorphism (a
`CircleDeg1Lift`) with translation number `p / q`, `q ≥ 1`. Then `f^q(x) = x + p` for some `x`
(Mathlib's `CircleDeg1Lift.translationNumber_eq_rat_iff`). If moreover `f` preserves a measure
of full support on the circle, then `f^q(x) = x + p` for every `x`: every orbit is periodic of
type `(p, q)` (`CircleDeg1Lift.iterate_eq_add_of_measurePreserving`). The measure is given on
the line as a locally finite measure with full support, invariant under `f` and under the
integer translations, as the lift of a measure on the circle is.

The proof: the map `h = f^q − p` is strictly increasing, preserves the measure, and has a fixed
point. If `h(x) ≠ x`, say `x < h(x)`, a fixed point `y > x` bounds the increasing orbit
`hⁿ(x) < y`, and the intervals `[hⁿ(x), hⁿ⁺¹(x))` are pairwise disjoint subsets of `[x, y]` of
equal positive measure, which contradicts the finiteness of the measure of `[x, y]`.

## References

* M. Bialy, A. E. Mironov, *The Birkhoff–Poritsky conjecture for centrally-symmetric billiard
  tables*, Ann. of Math. (2022), Section 1.3.
-/

public section

open MeasureTheory Set Function

namespace CircleDeg1Lift

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {h : ℝ → ℝ}

/-- A strictly increasing measure-preserving map of the line cannot move a point `a` up while
fixing a point above it: the intervals `[hⁿ(a), hⁿ⁺¹(a))` would be disjoint subsets of `[a, y]`
of equal positive measure. -/
private theorem false_of_lt_of_measurePreserving (hh : StrictMono h)
    (hμ : MeasurePreserving h μ μ) {a y : ℝ} (ha : a < h a) (hay : a < y) (hy : h y = y) :
    False := by
  set u : ℕ → ℝ := fun n => h^[n] a
  have hu (n : ℕ) : u (n + 1) = h (u n) := iterate_succ_apply' h n a
  have hsucc (n : ℕ) : u n < u (n + 1) := by
    induction n with
    | zero => exact ha
    | succ n ih => rw [hu (n + 1)]; nth_rewrite 1 [hu n]; exact hh ih
  have hmono : Monotone u := (strictMono_nat_of_lt_succ hsucc).monotone
  have hlt (n : ℕ) : u n < y := by
    induction n with
    | zero => exact hay
    | succ n ih => rw [hu n, ← hy]; exact hh ih
  have hpre (n : ℕ) : h ⁻¹' Ico (u (n + 1)) (u (n + 2)) = Ico (u n) (u (n + 1)) := by
    ext x
    simp only [mem_preimage, mem_Ico, hu (n + 1), hu n, hh.le_iff_le, hh.lt_iff_lt]
  have hmeas (n : ℕ) : μ (Ico (u n) (u (n + 1))) = μ (Ico a (h a)) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← hpre n, hμ.measure_preimage measurableSet_Ico.nullMeasurableSet]
  have hpos : μ (Ico a (h a)) ≠ 0 :=
    ((isOpen_Ioo.measure_pos μ (nonempty_Ioo.2 ha)).trans_le
      (measure_mono Ioo_subset_Ico_self)).ne'
  have hsub : (⋃ n, Ico (u n) (u (n + 1))) ⊆ Icc a y := iUnion_subset fun n x hx =>
    ⟨(hmono (Nat.zero_le n)).trans hx.1, (hx.2.trans (hlt (n + 1))).le⟩
  have hunion := measure_iUnion (μ := μ) hmono.pairwise_disjoint_on_Ico_succ
    fun _ => measurableSet_Ico
  simp only [Order.succ_eq_add_one, hmeas, ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hunion
  exact (isCompact_Icc.measure_lt_top (μ := μ)).ne (top_le_iff.1 (hunion ▸ measure_mono hsub))

/-- The mirror image of `false_of_lt_of_measurePreserving`: a strictly increasing
measure-preserving map of the line cannot move a point `a` down while fixing a point below it. -/
private theorem false_of_gt_of_measurePreserving (hh : StrictMono h)
    (hμ : MeasurePreserving h μ μ) {a y : ℝ} (ha : h a < a) (hay : y < a) (hy : h y = y) :
    False := by
  set u : ℕ → ℝ := fun n => h^[n] a
  have hu (n : ℕ) : u (n + 1) = h (u n) := iterate_succ_apply' h n a
  have hsucc (n : ℕ) : u (n + 1) < u n := by
    induction n with
    | zero => exact ha
    | succ n ih => rw [hu (n + 1)]; nth_rewrite 2 [hu n]; exact hh ih
  have hanti : Antitone u := (strictAnti_nat_of_succ_lt hsucc).antitone
  have hlt (n : ℕ) : y < u n := by
    induction n with
    | zero => exact hay
    | succ n ih => rw [hu n, ← hy]; exact hh ih
  have hpre (n : ℕ) : h ⁻¹' Ioc (u (n + 2)) (u (n + 1)) = Ioc (u (n + 1)) (u n) := by
    ext x
    simp only [mem_preimage, mem_Ioc, hu (n + 1), hu n, hh.le_iff_le, hh.lt_iff_lt]
  have hmeas (n : ℕ) : μ (Ioc (u (n + 1)) (u n)) = μ (Ioc (h a) a) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← hpre n, hμ.measure_preimage measurableSet_Ioc.nullMeasurableSet]
  have hpos : μ (Ioc (h a) a) ≠ 0 :=
    ((isOpen_Ioo.measure_pos μ (nonempty_Ioo.2 ha)).trans_le
      (measure_mono Ioo_subset_Ioc_self)).ne'
  have hsub : (⋃ n, Ioc (u (n + 1)) (u n)) ⊆ Icc y a := iUnion_subset fun n x hx =>
    ⟨((hlt (n + 1)).trans hx.1).le, hx.2.trans (hanti (Nat.zero_le n))⟩
  have hdisj : Pairwise (Disjoint on fun n => Ioc (u (n + 1)) (u n)) := by
    intro m n hmn
    rcases hmn.lt_or_gt with hmn | hmn
    · exact disjoint_left.2 fun x hxm hxn =>
        (hxn.2.trans (hanti (Nat.succ_le_of_lt hmn))).not_gt hxm.1
    · exact disjoint_left.2 fun x hxm hxn =>
        (hxm.2.trans (hanti (Nat.succ_le_of_lt hmn))).not_gt hxn.1
  have hunion := measure_iUnion (μ := μ) hdisj fun _ => measurableSet_Ioc
  simp only [hmeas, ENNReal.tsum_const_eq_top_of_ne_zero hpos] at hunion
  exact (isCompact_Icc.measure_lt_top (μ := μ)).ne (top_le_iff.1 (hunion ▸ measure_mono hsub))

/-- **Rational rotation number with an invariant measure of full support.** Let `f` be a
continuous strictly increasing `CircleDeg1Lift` with translation number `p / q`, `q ≥ 1`, and
let `μ` be a locally finite measure on `ℝ` of full support, invariant under `f` and under the
integer translations (the lift of an invariant measure of full support on the circle). Then
`f^q(x) = x + p` for every `x`: every orbit is periodic of type `(p, q)`. -/
theorem iterate_eq_add_of_measurePreserving {f : CircleDeg1Lift} (hf : StrictMono f)
    (hfc : Continuous f) {p : ℤ} {q : ℕ} (hq : 0 < q) (hτ : f.translationNumber = p / q)
    (hμ : MeasurePreserving f μ μ) (hμℤ : ∀ m : ℤ, MeasurePreserving (· + (m : ℝ)) μ μ)
    (x : ℝ) : f^[q] x = x + p := by
  obtain ⟨z, hz⟩ := (f.translationNumber_eq_rat_iff hfc hq).1 hτ
  rw [coe_pow] at hz
  set h : ℝ → ℝ := fun y => f^[q] y + (-p : ℤ)
  have hh : StrictMono h := fun a b hab => by simpa [h] using hf.iterate q hab
  have hhμ : MeasurePreserving h μ μ := (hμℤ (-p)).comp (hμ.iterate q)
  -- The integer translates of the fixed point `z` of `h` are fixed points of `h`.
  have hfix (m : ℤ) : h (z + m) = z + m := by
    have := (f ^ q).map_add_int z m
    rw [coe_pow, hz] at this
    simp only [h, this]
    push_cast
    ring
  by_contra hx
  rcases lt_or_gt_of_ne (show h x ≠ x from fun e => hx (by
    simp only [h] at e; push_cast at e; linarith)) with hlt | hlt
  · obtain ⟨m, hm⟩ := exists_int_lt (x - z)
    exact false_of_gt_of_measurePreserving hh hhμ hlt (by linarith) (hfix m)
  · obtain ⟨m, hm⟩ := exists_int_gt (x - z)
    exact false_of_lt_of_measurePreserving hh hhμ hlt (by linarith) (hfix m)

end CircleDeg1Lift
