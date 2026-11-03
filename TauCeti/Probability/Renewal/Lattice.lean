/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Lattice laws on the half-line and their maximal span

A measure `μ` on `ℝ≥0` is *lattice with span `a`* if `a > 0` and `μ` is concentrated on the
lattice `a ℕ = {0, a, 2a, …}`. No translation is allowed: the lattice always contains `0`. This is
the dichotomy of renewal theory. Blackwell's renewal theorem has a lattice form, stated along the
multiples of a span, and a nonlattice form, stated for intervals of every length, and the
excess-life limit splits the same way.

The lattice form is stated along the multiples of the *maximal* span. Dividing the increments by
a span gives an integer-valued law, and its positive support has gcd one exactly when the span is
maximal; this is the aperiodicity behind the lattice renewal theorem. This file shows that the
maximal span exists and identifies it arithmetically. Let `μ` be lattice with span `a`, and
suppose that `μ` is not concentrated at `0`. Let `d` be the gcd of the positive integers `n` with
`μ {n * a} > 0`. Then `d * a` is the greatest span of `μ`, and the spans of `μ` are exactly the
numbers `(d * a) / k` for positive integers `k`. In particular, a span `a` is maximal exactly when
the multiples of `a` carrying mass have gcd one. A greatest span is unique
(`IsGreatest.unique`). A measure concentrated at `0` has every positive number as a span, and
therefore no greatest one.

## Main definitions

* `MeasureTheory.Measure.IsLatticeSpan μ a`: `a > 0` and `μ` is concentrated on `a ℕ`.
* `MeasureTheory.Measure.IsLattice μ`: `μ` has some span.

## Main statements

* `MeasureTheory.Measure.IsLattice.isLatticeSpan_iff`: for a lattice measure, `b` is a span
  exactly when `b > 0` and every atom of `μ` is a multiple of `b`.
* `MeasureTheory.Measure.IsLatticeSpan.isGreatest_setGcd_mul`: if `a` is a span and
  `μ {0}ᶜ ≠ 0`, then `d * a` is the greatest span, where `d` is the gcd of the positive `n` with
  `μ {n * a} > 0`.
* `MeasureTheory.Measure.isGreatest_setOf_isLatticeSpan_iff`: a span is greatest exactly when
  this gcd is one.
* `MeasureTheory.Measure.IsLattice.exists_isGreatest`: a lattice measure not concentrated at `0`
  has a greatest span; `MeasureTheory.Measure.IsLattice.exists_isGreatest_of_measure_zero_lt_one`
  is the form for a probability measure `F` with `F {0} < 1`.
* `MeasureTheory.Measure.isLatticeSpan_iff_exists_nat_mul_eq`: the spans are the quotients of
  the greatest span by positive integers.
* `MeasureTheory.Measure.IsLatticeSpan.isGreatest_of_measure_singleton_pos`: a span carrying
  positive mass is the greatest span. For instance, `c` is the greatest span of `δ_c`.
* `MeasureTheory.Measure.not_isLattice`: a nonzero measure without atoms is nonlattice.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, §V.2 and Chapter XI.
-/

public section

open Set Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} {a b : ℝ≥0}

/-- A measure `μ` on `ℝ≥0` is lattice with span `a` if `a > 0` and `μ` is concentrated on the
multiples `{0, a, 2a, …}` of `a`. -/
structure IsLatticeSpan (μ : Measure ℝ≥0) (a : ℝ≥0) : Prop where
  /-- A span is positive. -/
  pos : 0 < a
  /-- Almost every point is a natural multiple of the span. -/
  ae_mem_range : ∀ᵐ x ∂μ, x ∈ range fun n : ℕ ↦ (n : ℝ≥0) * a

/-- A measure on `ℝ≥0` is lattice if it is concentrated on `a ℕ` for some `a > 0`. A measure that
is not lattice is called nonlattice. -/
def IsLattice (μ : Measure ℝ≥0) : Prop := ∃ a, μ.IsLatticeSpan a

/-- Unbundled form of `MeasureTheory.Measure.IsLatticeSpan`. -/
theorem isLatticeSpan_iff :
    μ.IsLatticeSpan a ↔ 0 < a ∧ ∀ᵐ x ∂μ, x ∈ range fun n : ℕ ↦ (n : ℝ≥0) * a :=
  ⟨fun h ↦ ⟨h.pos, h.ae_mem_range⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A measure is lattice exactly when it has a span. -/
theorem isLattice_iff : μ.IsLattice ↔ ∃ a, μ.IsLatticeSpan a := Iff.rfl

theorem IsLatticeSpan.isLattice (h : μ.IsLatticeSpan a) : μ.IsLattice := ⟨a, h⟩

/-- The span condition as a null set: `μ` gives no mass to the complement of `a ℕ`. -/
theorem IsLatticeSpan.measure_compl_range (h : μ.IsLatticeSpan a) :
    μ (range fun n : ℕ ↦ (n : ℝ≥0) * a)ᶜ = 0 :=
  mem_ae_iff.1 h.ae_mem_range

/-- Every atom of a measure with span `a` is a multiple of `a`. -/
theorem IsLatticeSpan.exists_nat_mul_eq_of_measure_singleton_ne_zero (h : μ.IsLatticeSpan a)
    {x : ℝ≥0} (hx : μ {x} ≠ 0) : ∃ n : ℕ, (n : ℝ≥0) * a = x := by
  by_contra hcon
  exact hx <| measure_mono_null (singleton_subset_iff.2 hcon) h.measure_compl_range

/-- For a lattice measure, `b` is a span exactly when `b > 0` and every atom is a multiple of
`b`. -/
theorem IsLattice.isLatticeSpan_iff (hμ : μ.IsLattice) :
    μ.IsLatticeSpan b ↔ 0 < b ∧ ∀ x, μ {x} ≠ 0 → ∃ n : ℕ, (n : ℝ≥0) * b = x := by
  refine ⟨fun h ↦ ⟨h.pos, fun x hx ↦ h.exists_nat_mul_eq_of_measure_singleton_ne_zero hx⟩, ?_⟩
  rintro ⟨hb, hatom⟩
  obtain ⟨a, ha⟩ := hμ
  -- Almost surely no point `n * a` outside `b ℕ` is hit: each such point is a null atom.
  have hnull : ∀ᵐ x ∂μ, ∀ n : ℕ, x = (n : ℝ≥0) * a → x ∈ range fun m : ℕ ↦ (m : ℝ≥0) * b := by
    refine ae_all_iff.2 fun n ↦ ?_
    by_cases hn : μ {(n : ℝ≥0) * a} = 0
    · exact ae_iff.2 <| measure_mono_null (fun x hx ↦ (not_imp.1 hx).1) hn
    · exact Eventually.of_forall fun x hx ↦ hx ▸ hatom _ hn
  refine ⟨hb, ?_⟩
  filter_upwards [ha.ae_mem_range, hnull] with x ⟨n, hn⟩ h
  exact h n hn.symm

/-- If `μ` has span `a` and is not concentrated at `0`, some positive multiple of `a` is an atom
of `μ`. -/
theorem IsLatticeSpan.exists_measure_singleton_pos (h : μ.IsLatticeSpan a) (h0 : μ {0}ᶜ ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ 0 < μ {(n : ℝ≥0) * a} := by
  by_contra! hcon
  refine h0 ?_
  have hnull : ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n → x ≠ (n : ℝ≥0) * a :=
    ae_all_iff.2 fun n ↦ ae_all_iff.2 fun hn ↦
      ae_iff.2 <| measure_mono_null (fun x hx ↦ not_not.1 hx) (nonpos_iff_eq_zero.1 (hcon n hn))
  filter_upwards [h.ae_mem_range, hnull] with x ⟨n, hn⟩ hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using hn.symm
  · exact (hx n hpos hn.symm).elim

/-- If `b` is a span of `μ`, then `d * a` is an integer multiple of `b` for every `a`, where `d`
is the gcd of the positive `n` with `μ {n * a} > 0`. The proof writes `d` as an integer
combination of such `n` (Bézout), each of which has `n * a ∈ b ℕ`. -/
private theorem IsLatticeSpan.setGcd_mul_mem_zmultiples (hb : μ.IsLatticeSpan b) (a : ℝ≥0) :
    ((Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} : ℝ≥0) * a : ℝ) ∈
      AddSubgroup.zmultiples (b : ℝ) := by
  set s := {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}}
  have hd : ((Nat.setGcd s : ℕ) : ℤ) ∈ Ideal.span (((↑) : ℕ → ℤ) '' s) := by
    rw [← Nat.span_singleton_setGcd]
    exact Ideal.mem_span_singleton_self _
  suffices ∀ z ∈ Ideal.span (((↑) : ℕ → ℤ) '' s),
      (z : ℝ) * a ∈ AddSubgroup.zmultiples (b : ℝ) by
    simpa using this _ hd
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, hn, rfl⟩ := hz
    obtain ⟨m, hm⟩ := hb.exists_nat_mul_eq_of_measure_singleton_ne_zero hn.2.ne'
    refine ⟨m, ?_⟩
    simpa using congrArg ((↑) : ℝ≥0 → ℝ) hm
  | zero => simp
  | add z w _ _ hz hw => simpa [add_mul] using add_mem hz hw
  | smul c z _ hz => simpa [mul_assoc] using AddSubgroup.zsmul_mem _ hz c

/-- If `μ` has span `a` and is not concentrated at `0`, the gcd of the positive `n` with
`μ {n * a} > 0` is positive. -/
private theorem IsLatticeSpan.setGcd_pos (ha : μ.IsLatticeSpan a) (h0 : μ {0}ᶜ ≠ 0) :
    0 < Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} := by
  obtain ⟨n, hn, hμn⟩ := ha.exists_measure_singleton_pos h0
  exact Nat.pos_of_dvd_of_pos (Nat.setGcd_dvd_of_mem ⟨hn, hμn⟩) hn

/-- If `a` and `b` are spans of a measure not concentrated at `0`, then `d * a = k * b` for a
positive integer `k`, where `d` is the gcd of the positive `n` with `μ {n * a} > 0`. -/
private theorem IsLatticeSpan.exists_nat_mul_eq_setGcd_mul (hb : μ.IsLatticeSpan b)
    (ha : μ.IsLatticeSpan a) (h0 : μ {0}ᶜ ≠ 0) :
    ∃ k : ℕ, 0 < k ∧
      (k : ℝ≥0) * b = Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} * a := by
  obtain ⟨k, hk⟩ := hb.setGcd_mul_mem_zmultiples a
  have hda : (0 : ℝ) < (Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} : ℝ≥0) * a := by
    exact_mod_cast mul_pos (Nat.cast_pos.2 (ha.setGcd_pos h0)) ha.pos
  have hk' : (k : ℝ) * b = (Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} : ℝ≥0) * a := by
    simpa using hk
  have hkpos : (0 : ℝ) < k :=
    pos_of_mul_pos_left (hk' ▸ hda) (NNReal.coe_nonneg b)
  lift k to ℕ using by exact_mod_cast hkpos.le
  refine ⟨k, by exact_mod_cast hkpos, ?_⟩
  rw [← NNReal.coe_inj]
  push_cast at hk' ⊢
  exact hk'

/-- **Maximal span.** If `a` is a span of `μ` and `μ` is not concentrated at `0`, then `d * a` is
the greatest span of `μ`, where `d` is the gcd of the positive integers `n` with
`μ {n * a} > 0`. -/
theorem IsLatticeSpan.isGreatest_setGcd_mul (ha : μ.IsLatticeSpan a) (h0 : μ {0}ᶜ ≠ 0) :
    IsGreatest {b | μ.IsLatticeSpan b}
      (Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} * a) := by
  set s := {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}}
  have hda : 0 < (Nat.setGcd s : ℝ≥0) * a :=
    mul_pos (Nat.cast_pos.2 (ha.setGcd_pos h0)) ha.pos
  refine ⟨(ha.isLattice.isLatticeSpan_iff).2 ⟨hda, fun x hx ↦ ?_⟩, fun b hb ↦ ?_⟩
  · -- Every atom `n * a` has `d ∣ n`, so it is a multiple of `d * a`.
    obtain ⟨n, rfl⟩ := ha.exists_nat_mul_eq_of_measure_singleton_ne_zero hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simp⟩
    · obtain ⟨k, rfl⟩ := Nat.setGcd_dvd_of_mem (s := s) ⟨hn, pos_iff_ne_zero.2 hx⟩
      exact ⟨k, by push_cast; ring⟩
  · -- Conversely `d * a = k * b` for a positive integer `k`.
    obtain ⟨k, hk, hkb⟩ := hb.exists_nat_mul_eq_setGcd_mul ha h0
    exact hkb ▸ le_mul_of_one_le_left (by simp) (Nat.one_le_cast.2 hk)

/-- A lattice measure that is not concentrated at `0` has a greatest span. It is unique by
`IsGreatest.unique`. -/
theorem IsLattice.exists_isGreatest (hμ : μ.IsLattice) (h0 : μ {0}ᶜ ≠ 0) :
    ∃ a, IsGreatest {b | μ.IsLatticeSpan b} a :=
  let ⟨_, ha⟩ := hμ
  ⟨_, ha.isGreatest_setGcd_mul h0⟩

/-- A lattice probability law `F` with `F {0} < 1` has a greatest span. -/
theorem IsLattice.exists_isGreatest_of_measure_zero_lt_one [IsProbabilityMeasure μ]
    (hμ : μ.IsLattice) (h0 : μ {0} < 1) : ∃ a, IsGreatest {b | μ.IsLatticeSpan b} a :=
  hμ.exists_isGreatest <| by
    rw [prob_compl_eq_one_sub (measurableSet_singleton 0)]
    exact (tsub_pos_of_lt h0).ne'

/-- A measure with a greatest span is not concentrated at `0`: if it were, `2 * g` would be a
span exceeding every span `g`. -/
private theorem measure_compl_singleton_zero_ne_zero {g : ℝ≥0}
    (hg : IsGreatest {b | μ.IsLatticeSpan b} g) : μ {0}ᶜ ≠ 0 := by
  intro h0
  have hspan : μ.IsLatticeSpan (2 * g) := by
    refine ⟨mul_pos two_pos hg.1.pos, ?_⟩
    filter_upwards [mem_ae_iff.2 h0] with x hx
    exact ⟨0, by simp [mem_singleton_iff.1 hx]⟩
  exact (hg.2 hspan).not_gt (lt_two_mul_self hg.1.pos)

/-- A span `a` is the greatest span exactly when the positive `n` with `μ {n * a} > 0` have gcd
one. -/
theorem isGreatest_setOf_isLatticeSpan_iff :
    IsGreatest {b | μ.IsLatticeSpan b} a ↔
      μ.IsLatticeSpan a ∧ Nat.setGcd {n : ℕ | 0 < n ∧ 0 < μ {(n : ℝ≥0) * a}} = 1 := by
  constructor
  · intro h
    have heq := (h.1.isGreatest_setGcd_mul (measure_compl_singleton_zero_ne_zero h)).unique h
    exact ⟨h.1, by exact_mod_cast (mul_eq_right₀ h.1.pos.ne').1 heq⟩
  · rintro ⟨ha, hd⟩
    -- A gcd of one forces an atom at a positive multiple of `a`.
    obtain ⟨n, ⟨hn, hμn⟩, -⟩ := Nat.exists_ne_zero_of_setGcd_ne_zero (hd ▸ one_ne_zero)
    have h0 : μ {0}ᶜ ≠ 0 := (hμn.trans_le <| measure_mono <| singleton_subset_iff.2 <|
      mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') ha.pos.ne').ne'
    simpa [hd] using ha.isGreatest_setGcd_mul h0

/-- A span at which `μ` has an atom is the greatest span. -/
theorem IsLatticeSpan.isGreatest_of_measure_singleton_pos (ha : μ.IsLatticeSpan a)
    (hμa : 0 < μ {a}) : IsGreatest {b | μ.IsLatticeSpan b} a :=
  isGreatest_setOf_isLatticeSpan_iff.2
    ⟨ha, Nat.dvd_one.1 <| Nat.setGcd_dvd_of_mem ⟨one_pos, by simpa using hμa⟩⟩

/-- If `g` is the greatest span of `μ`, the spans of `μ` are exactly the numbers `b` with
`g = k * b` for a positive integer `k`. -/
theorem isLatticeSpan_iff_exists_nat_mul_eq {g : ℝ≥0}
    (hg : IsGreatest {b | μ.IsLatticeSpan b} g) :
    μ.IsLatticeSpan b ↔ ∃ k : ℕ, 0 < k ∧ (k : ℝ≥0) * b = g := by
  have h0 := measure_compl_singleton_zero_ne_zero hg
  constructor
  · intro hb
    obtain ⟨k, hk, hkb⟩ := hb.exists_nat_mul_eq_setGcd_mul hg.1 h0
    exact ⟨k, hk, hkb.trans ((hg.1.isGreatest_setGcd_mul h0).unique hg)⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨pos_of_mul_pos_right hg.1.pos (by positivity), ?_⟩
    filter_upwards [hg.1.ae_mem_range] with x ⟨n, hn⟩
    exact ⟨n * k, by rw [← hn]; push_cast; ring⟩

/-- `δ_c` has span `c` for `c > 0`. -/
theorem isLatticeSpan_dirac {c : ℝ≥0} (hc : 0 < c) : (dirac c).IsLatticeSpan c :=
  ⟨hc, by simpa [ae_dirac_eq] using ⟨1, by simp⟩⟩

/-- The deterministic law `δ_c` with `c > 0` has greatest span `c`. -/
theorem isGreatest_setOf_isLatticeSpan_dirac {c : ℝ≥0} (hc : 0 < c) :
    IsGreatest {b | (dirac c).IsLatticeSpan b} c :=
  (isLatticeSpan_dirac hc).isGreatest_of_measure_singleton_pos (by simp)

/-- A nonzero measure without atoms is nonlattice: it gives no mass to any countable set. -/
theorem not_isLattice [NullSingletonClass μ] (hμ : μ ≠ 0) : ¬ μ.IsLattice := by
  rintro ⟨a, ha⟩
  refine hμ (measure_univ_eq_zero.1 ?_)
  rw [← union_compl_self (range fun n : ℕ ↦ (n : ℝ≥0) * a)]
  exact measure_union_null ((countable_range _).measure_zero μ) ha.measure_compl_range

end MeasureTheory.Measure
