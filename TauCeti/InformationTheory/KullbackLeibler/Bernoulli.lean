/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import TauCeti.Analysis.SpecialFunctions.Log.Basic
import TauCeti.InformationTheory.KullbackLeibler.Convex
import TauCeti.InformationTheory.KullbackLeibler.Finite
import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# The binary Kullback–Leibler divergence

The binary divergence `klBin a b = a log (a / b) + (1 - a) log ((1 - a) / (1 - b))` is the
relative entropy of the Bernoulli law with mass `a` at one point from the Bernoulli law with
mass `b` there, for `a ∈ [0, 1]` and `b ∈ (0, 1)`, when the two atoms are measurably separated:
on `Bool` with atoms `true` and `false`, or more generally when some measurable set contains
the first atom but not the second. At `b ∈ {0, 1}` with `a ≠ b` the divergence is infinite, and
`klBin a b` takes the junk value coming from `Real.log 0 = 0` (`TauCeti.klBin_zero_right`,
`TauCeti.klBin_one_right`). Parameters outside `[0, 1]` have no Bernoulli interpretation; there
`klBin` is just the formula, with `Real.log` of a negative number equal to the logarithm of its
absolute value.

It is jointly convex on `[0, 1] × (0, 1)` together with the diagonal endpoints `(0, 0)` and
`(1, 1)`: the Bernoulli law is affine in its parameter, and relative entropy is jointly convex
(`TauCeti.klDiv_smul_add_smul_smul_add_smul_le`). Data processing to the indicator of an event
gives `ENNReal.ofReal (klBin (P.real A) (Q.real A)) ≤ klDiv P Q`; its left side is `0` when
`Q.real A ∈ {0, 1}`, even where the divergence of the two Bernoulli laws is infinite. The binary
entropy bound `h(a) ≤ log 2` gives `-a log b - log 2 ≤ klBin a b` for `a, b ∈ [0, 1]`, used in
Fano's inequality.

## Main definitions and statements

* `TauCeti.klBin`: the binary Kullback–Leibler divergence, as a real number, with the
  simplification lemmas `TauCeti.klBin_self`, `TauCeti.klBin_zero_left`,
  `TauCeti.klBin_one_left`, `TauCeti.klBin_zero_right` and `TauCeti.klBin_one_right`.
* `TauCeti.klBin_nonneg`, `TauCeti.klBin_eq_zero_iff`: for `a ∈ [0, 1]` and `b ∈ (0, 1)`,
  `0 ≤ klBin a b`, with equality exactly when `a = b`.
* `TauCeti.klDiv_bernoulliMeasure`: `klBin a b` is the divergence of `Ber(x, y, a)` from
  `Ber(x, y, b)` when some measurable set contains `x` but not `y`, for `a ∈ [0, 1]` and
  `b ∈ (0, 1)`.
* `TauCeti.convexOn_klBin`: joint convexity on `([0, 1] × (0, 1)) ∪ {(0, 0), (1, 1)}`.
* `TauCeti.neg_mul_log_sub_log_two_le_klBin`: `-a log b - log 2 ≤ klBin a b` for
  `a, b ∈ [0, 1]`.
* `TauCeti.mul_log_sub_log_two_le_klBin`: `a log M - log 2 ≤ klBin a (1 / M)` for `a ∈ [0, 1]`
  and `M : ℕ`.
* `TauCeti.ofReal_klBin_le_klDiv`: data processing to an event,
  `ENNReal.ofReal (klBin (P.real A) (Q.real A)) ≤ klDiv P Q` for probability measures `P`, `Q`
  and any set `A`.

## References

* R. J. Samworth and R. D. Shah, *Modern Statistical Methods for Data Science* (lecture
  notes), proof of Theorem 8.11 and (8.10), p. 235.

The definition of `klBin`, the statement of `TauCeti.klBin_nonneg`, the formula for the
divergence of two Bernoulli laws and the event bound are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), files `CKSD/Inference/Divergence/Basic.lean`
(`bernoulliKullbackLeibler`, `bernoulliKullbackLeibler_nonneg`,
`klDiv_bernoulliMeasure_eq_bernoulliKullbackLeibler`,
`bernoulliKullbackLeibler_eq_neg_binEntropy_sub`) and
`CKSD/Nonparametric/LowerBounds/Testing.lean` (`measureReal_mul_neg_log_sub_log_two_le_klDiv`).
The proof of nonnegativity here is new, through Mathlib's `InformationTheory.klFun`. The proof of
the Bernoulli formula is also new: it specializes `TauCeti.klDiv_eq_ofReal_sum_log_singleton` to
`Bool` and transfers the result to `Ber(x, y, ·)` by Mathlib's `InformationTheory.klDiv_map_le`
in both directions.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Real unitInterval
open scoped ENNReal NNReal

namespace TauCeti

/-- The binary Kullback–Leibler divergence `a log (a / b) + (1 - a) log ((1 - a) / (1 - b))`.
For `a ∈ [0, 1]` and `b ∈ (0, 1)` it is the divergence of the Bernoulli law with mass `a` at
`true` from that with mass `b` at `true`, on `Bool` (or on any space whose two atoms some
measurable set separates, `TauCeti.klDiv_bernoulliMeasure`); at `b ∈ {0, 1}` it takes the junk
value given by `Real.log 0 = 0`. -/
noncomputable def klBin (a b : ℝ) : ℝ :=
  a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))

/-- The defining formula of the binary divergence. -/
theorem klBin_def (a b : ℝ) :
    klBin a b = a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b)) := by
  rw [klBin]

/-- The binary divergence of a parameter from itself vanishes, for every real `a`. -/
@[simp]
theorem klBin_self (a : ℝ) : klBin a a = 0 := by
  simp [klBin_def]

/-- From the deterministic source law `a = 0`, the binary divergence is `-log (1 - b)`, for every
real `b`. -/
@[simp]
theorem klBin_zero_left (b : ℝ) : klBin 0 b = -log (1 - b) := by
  simp [klBin_def]

/-- From the deterministic source law `a = 1`, the binary divergence is `-log b`, for every
real `b`. -/
@[simp]
theorem klBin_one_left (b : ℝ) : klBin 1 b = -log b := by
  simp [klBin_def]

/-- At the reference endpoint `b = 0` the binary divergence takes the junk value
`(1 - a) log (1 - a)`, from `Real.log 0 = 0`. -/
@[simp]
theorem klBin_zero_right (a : ℝ) : klBin a 0 = (1 - a) * log (1 - a) := by
  simp [klBin_def]

/-- At the reference endpoint `b = 1` the binary divergence takes the junk value `a log a`,
from `Real.log 0 = 0`. -/
@[simp]
theorem klBin_one_right (a : ℝ) : klBin a 1 = a * log a := by
  simp [klBin_def]

/-- The binary divergence as the `klFun` form of relative entropy, weighted by the reference
masses `b` and `1 - b`. -/
theorem klBin_eq_mul_klFun_add_mul_klFun {a b : ℝ} (hb₀ : b ≠ 0) (hb₁ : b ≠ 1) :
    klBin a b = b * klFun (a / b) + (1 - b) * klFun ((1 - a) / (1 - b)) := by
  have : 1 - b ≠ 0 := sub_ne_zero.mpr hb₁.symm
  simp only [klBin, klFun]
  field_simp
  ring

/-- The binary divergence is nonnegative for `a ∈ [0, 1]` and `b ∈ (0, 1)`. -/
theorem klBin_nonneg {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) : 0 ≤ klBin a b := by
  rw [klBin_eq_mul_klFun_add_mul_klFun hb.1.ne' hb.2.ne]
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  exact add_nonneg (mul_nonneg hb.1.le (klFun_nonneg (div_nonneg ha.1 hb.1.le)))
    (mul_nonneg hb'.le (klFun_nonneg (div_nonneg (sub_nonneg.mpr ha.2) hb'.le)))

/-- For `a ∈ [0, 1]` and `b ∈ (0, 1)`, the binary divergence vanishes exactly when `a = b`. The
interior reference is needed: `klBin 1 0 = 0` from `Real.log 0 = 0`. -/
theorem klBin_eq_zero_iff {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) :
    klBin a b = 0 ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, klBin_self]⟩
  rw [klBin_eq_mul_klFun_add_mul_klFun hb.1.ne' hb.2.ne] at h
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  have hab : 0 ≤ a / b := div_nonneg ha.1 hb.1.le
  have h₁ := mul_nonneg hb.1.le (klFun_nonneg hab)
  have h₂ := mul_nonneg hb'.le (klFun_nonneg (div_nonneg (sub_nonneg.mpr ha.2) hb'.le))
  have h₀ : klFun (a / b) = 0 := (mul_eq_zero.mp (by linarith)).resolve_left hb.1.ne'
  rwa [klFun_eq_zero_iff hab, div_eq_one_iff_eq hb.1.ne'] at h₀

/-- The binary divergence in terms of the binary entropy, for `b ∉ {0, 1}`. -/
theorem klBin_eq_neg_binEntropy_sub {a b : ℝ} (hb₀ : b ≠ 0) (hb₁ : b ≠ 1) :
    klBin a b = -binEntropy a - a * log b - (1 - a) * log (1 - b) := by
  rw [klBin, mul_log_div _ hb₀, mul_log_div _ (sub_ne_zero.mpr hb₁.symm),
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [negMulLog]
  ring

/-- The lower bound `-a log b - log 2 ≤ klBin a b` for `a, b ∈ [0, 1]`, from the binary
entropy bound `h(a) ≤ log 2`. -/
theorem neg_mul_log_sub_log_two_le_klBin {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    -(a * log b) - log 2 ≤ klBin a b := by
  have hh : -a * log a + -(1 - a) * log (1 - a) ≤ log 2 := by
    simpa [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog] using
      binEntropy_le_log_two (p := a)
  have h₀ : 0 ≤ -a * log a := negMulLog_nonneg ha.1 ha.2
  have h₁ : 0 ≤ -(1 - a) * log (1 - a) :=
    negMulLog_nonneg (sub_nonneg.mpr ha.2) (sub_le_self 1 ha.1)
  rcases hb.1.eq_or_lt with rfl | hb₀
  · simp only [klBin_zero_right, log_zero, mul_zero, neg_zero]
    linarith
  rcases hb.2.eq_or_lt with rfl | hb₁
  · simp only [klBin_one_right, log_one, mul_zero, neg_zero]
    linarith
  rw [klBin_eq_neg_binEntropy_sub hb₀.ne' hb₁.ne, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [negMulLog]
  have : (1 - a) * log (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha.2)
      (log_nonpos (sub_nonneg.mpr hb₁.le) (sub_le_self 1 hb₀.le))
  linarith

/-- **Fano's lower bound for `klBin`**: `a log M - log 2 ≤ klBin a (1 / M)` for `a ∈ [0, 1]`. -/
theorem mul_log_sub_log_two_le_klBin {a : ℝ} (ha : a ∈ Icc 0 1) (M : ℕ) :
    a * log M - log 2 ≤ klBin a (1 / M) := by
  have hM : (1 / M : ℝ) ∈ Icc 0 1 :=
    ⟨Nat.one_div_cast_nonneg M, by simpa only [one_div] using Nat.cast_inv_le_one (α := ℝ) M⟩
  simpa [one_div, log_inv] using neg_mul_log_sub_log_two_le_klBin ha hM

section Bernoulli

variable {X : Type*} [MeasurableSpace X]

/-- On `Bool`, the binary divergence is the divergence of the Bernoulli laws, for an interior
reference mass `b` or for `a = b`. -/
private theorem klDiv_bernoulliMeasure_bool {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hab : b ∈ Ioo 0 1 ∨ a = b) :
    klDiv (bernoulliMeasure true false ⟨a, ha⟩) (bernoulliMeasure true false ⟨b, hb⟩) =
      ENNReal.ofReal (klBin a b) := by
  obtain hb' | rfl := hab
  · have hν : ∀ c : Bool, bernoulliMeasure true false ⟨b, hb⟩ {c} ≠ 0 := by
      rintro (_ | _)
      · exact Probability.bernoulliMeasure_singleton_right_ne_zero (x := true) hb'.2
      · exact Probability.bernoulliMeasure_singleton_left_ne_zero (y := false) hb'.1
    rw [klDiv_eq_ofReal_sum_log_singleton hν, Fintype.sum_bool]
    simp [klBin, add_comm]
  · simp

/-- **Divergence of Bernoulli laws.** If a measurable set `s` contains `x` but not `y` (for
instance `s = {x}` when `x ≠ y` and singletons are measurable), then for `a ∈ [0, 1]` and
`b ∈ (0, 1)` the divergence of `Ber(x, y, a)` from `Ber(x, y, b)` (the laws with mass `a` and
`b` at `x`) is `klBin a b`. -/
theorem klDiv_bernoulliMeasure {x y : X} {s : Set X} (hs : MeasurableSet s) (hx : x ∈ s)
    (hy : y ∉ s) {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) :
    klDiv (bernoulliMeasure x y ⟨a, ha⟩) (bernoulliMeasure x y ⟨b, Ioo_subset_Icc_self hb⟩) =
      ENNReal.ofReal (klBin a b) := by
  classical
  rw [← klDiv_bernoulliMeasure_bool ha (Ioo_subset_Icc_self hb) (.inl hb)]
  set f : Bool → X := fun c ↦ cond c x y
  set g : X → Bool := fun z ↦ decide (z ∈ s)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_to_bool <| by simpa [g, Set.preimage] using hs
  have hfp (p : I) : (bernoulliMeasure true false p).map f = bernoulliMeasure x y p :=
    map_bernoulliMeasure' _ _ hf p
  have hgp (p : I) : (bernoulliMeasure x y p).map g = bernoulliMeasure true false p := by
    rw [map_bernoulliMeasure' _ _ hg p]
    simp [g, hx, hy]
  refine le_antisymm ?_ ?_
  · simpa only [hfp] using klDiv_map_le (μ := bernoulliMeasure true false ⟨a, ha⟩)
      (ν := bernoulliMeasure true false ⟨b, Ioo_subset_Icc_self hb⟩) hf
  · simpa only [hgp] using klDiv_map_le (μ := bernoulliMeasure x y ⟨a, ha⟩)
      (ν := bernoulliMeasure x y ⟨b, Ioo_subset_Icc_self hb⟩) hg

end Bernoulli

/-- The domain `([0, 1] × (0, 1)) ∪ {(0, 0), (1, 1)}` of the joint convexity of `klBin`: both
parameters lie in `[0, 1]`, and the reference mass is interior unless the two agree. -/
private theorem mem_klBin_domain_iff {p : ℝ × ℝ} :
    p ∈ (Icc 0 1 ×ˢ Ioo 0 1 ∪ {(0, 0), (1, 1)} : Set (ℝ × ℝ)) ↔
      p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ (p.2 ∈ Ioo 0 1 ∨ p.1 = p.2) := by
  obtain ⟨a, b⟩ := p
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨ha, Ioo_subset_Icc_self hb, .inl hb⟩
    · simp
    · simp
  · rintro ⟨ha, hb, hb' | rfl⟩
    · exact .inl ⟨ha, hb'⟩
    · rcases hb.1.eq_or_lt with rfl | h₀
      · simp
      rcases hb.2.eq_or_lt with rfl | h₁
      · simp
      exact .inl ⟨ha, h₀, h₁⟩

/-- The domain `([0, 1] × (0, 1)) ∪ {(0, 0), (1, 1)}` of the joint convexity of `klBin` is
convex. -/
private theorem convex_klBin_domain :
    Convex ℝ (Icc 0 1 ×ˢ Ioo 0 1 ∪ {(0, 0), (1, 1)} : Set (ℝ × ℝ)) := by
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ s t hs ht hst
  rw [mem_klBin_domain_iff] at h₁ h₂ ⊢
  obtain ⟨ha₁, hb₁, hab₁⟩ : a₁ ∈ Icc 0 1 ∧ b₁ ∈ Icc 0 1 ∧ (b₁ ∈ Ioo 0 1 ∨ a₁ = b₁) :=
    h₁
  obtain ⟨ha₂, hb₂, hab₂⟩ : a₂ ∈ Icc 0 1 ∧ b₂ ∈ Icc 0 1 ∧ (b₂ ∈ Ioo 0 1 ∨ a₂ = b₂) :=
    h₂
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine ⟨convex_Icc 0 1 ha₁ ha₂ hs ht hst, convex_Icc 0 1 hb₁ hb₂ hs ht hst, ?_⟩
  by_cases hb : s * b₁ + t * b₂ ∈ Ioo 0 1
  · exact .inl hb
  -- A positive weight on an interior reference mass would make the mixed reference interior,
  -- so every weighted point lies on the diagonal.
  have hw₁ : s * a₁ = s * b₁ := by
    obtain h | rfl := hab₁
    · obtain rfl | hs' := hs.eq_or_lt
      · simp
      refine absurd ⟨?_, ?_⟩ hb
      · nlinarith [mul_pos hs' h.1, mul_nonneg ht hb₂.1]
      · nlinarith [mul_lt_mul_of_pos_left h.2 hs', mul_le_of_le_one_right ht hb₂.2]
    · rfl
  have hw₂ : t * a₂ = t * b₂ := by
    obtain h | rfl := hab₂
    · obtain rfl | ht' := ht.eq_or_lt
      · simp
      refine absurd ⟨?_, ?_⟩ hb
      · nlinarith [mul_pos ht' h.1, mul_nonneg hs hb₁.1]
      · nlinarith [mul_lt_mul_of_pos_left h.2 ht', mul_le_of_le_one_right hs hb₁.2]
    · rfl
  exact .inr (by rw [hw₁, hw₂])

/-- **Joint convexity** of the binary divergence on `([0, 1] × (0, 1)) ∪ {(0, 0), (1, 1)}`, the
pairs of Bernoulli parameters whose divergence is finite and equal to `klBin`. The two diagonal
endpoints are the identical deterministic laws, of divergence `0`; they are included because an
average of divergences, as in Fano's inequality, may have terms with reference mass `0` or `1`.
Restrict with `ConvexOn.subset` to the rectangle `[0, 1] × (0, 1)`. -/
theorem convexOn_klBin :
    ConvexOn ℝ (Icc 0 1 ×ˢ Ioo 0 1 ∪ {(0, 0), (1, 1)}) fun p : ℝ × ℝ ↦ klBin p.1 p.2 := by
  have hconv := convex_klBin_domain
  refine ⟨hconv, ?_⟩
  rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ s t hs ht hst
  have hm := hconv h₁ h₂ hs ht hst
  rw [mem_klBin_domain_iff] at h₁ h₂ hm
  obtain ⟨ha₁, hb₁, hab₁⟩ : a₁ ∈ Icc 0 1 ∧ b₁ ∈ Icc 0 1 ∧ (b₁ ∈ Ioo 0 1 ∨ a₁ = b₁) :=
    h₁
  obtain ⟨ha₂, hb₂, hab₂⟩ : a₂ ∈ Icc 0 1 ∧ b₂ ∈ Icc 0 1 ∧ (b₂ ∈ Ioo 0 1 ∨ a₂ = b₂) :=
    h₂
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hm ⊢
  obtain ⟨ha, hb, hab⟩ := hm
  lift s to ℝ≥0 using hs
  lift t to ℝ≥0 using ht
  have hst' : s + t = 1 := by exact_mod_cast hst
  -- The Bernoulli laws of the mixed parameters are the mixtures of the Bernoulli laws.
  have hμ := Probability.bernoulliMeasure_eq_smul_add_smul true false (p := ⟨a₁, ha₁⟩)
    (q := ⟨a₂, ha₂⟩) (r := ⟨_, ha⟩) hst' rfl
  have hν := Probability.bernoulliMeasure_eq_smul_add_smul true false (p := ⟨b₁, hb₁⟩)
    (q := ⟨b₂, hb₂⟩) (r := ⟨_, hb⟩) hst' rfl
  have key := klDiv_smul_add_smul_smul_add_smul_le
    (μ₁ := bernoulliMeasure true false ⟨a₁, ha₁⟩) (μ₂ := bernoulliMeasure true false ⟨a₂, ha₂⟩)
    (ν₁ := bernoulliMeasure true false ⟨b₁, hb₁⟩) (ν₂ := bernoulliMeasure true false ⟨b₂, hb₂⟩)
    s t
  rw [← hμ, ← hν, klDiv_bernoulliMeasure_bool ha hb hab, klDiv_bernoulliMeasure_bool ha₁ hb₁ hab₁,
    klDiv_bernoulliMeasure_bool ha₂ hb₂ hab₂] at key
  -- `key` is now the convexity inequality in `ℝ≥0∞`; move it to `ℝ`.
  have hsmul (r : ℝ≥0) (u : ℝ) :
      (r : ℝ≥0∞) * ENNReal.ofReal u = ENNReal.ofReal (r * u) := by
    rw [ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hnn {a b : ℝ} (ha : a ∈ Icc 0 1) (hab : b ∈ Ioo 0 1 ∨ a = b) : 0 ≤ klBin a b := by
    obtain h | rfl := hab
    · exact klBin_nonneg ha h
    · simp
  have h₁ : 0 ≤ (s : ℝ) * klBin a₁ b₁ := mul_nonneg s.coe_nonneg (hnn ha₁ hab₁)
  have h₂ : 0 ≤ (t : ℝ) * klBin a₂ b₂ := mul_nonneg t.coe_nonneg (hnn ha₂ hab₂)
  rwa [hsmul s, hsmul t,
    ← ENNReal.ofReal_add h₁ h₂, ENNReal.ofReal_le_ofReal_iff (add_nonneg h₁ h₂)] at key

/-- **Data processing to an event.** For probability measures `P`, `Q` and any set `A`,
`ENNReal.ofReal (klBin (P.real A) (Q.real A)) ≤ klDiv P Q`: the binary divergence of the masses
of `A`, read in `ℝ≥0∞`, is at most the divergence of `P` from `Q`. The set need not be
measurable: its masses are those of a common measurable hull for `P + Q`. Where
`Q.real A ∈ {0, 1}`, `klBin` takes a junk value at most `0`, so the left side is `0`, even when
`P.real A` differs from `Q.real A` and the divergence of the two Bernoulli laws is infinite. -/
theorem ofReal_klBin_le_klDiv {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (A : Set X) :
    ENNReal.ofReal (klBin (P.real A) (Q.real A)) ≤ klDiv P Q := by
  set H := toMeasurable (P + Q) A
  have hH : MeasurableSet H := measurableSet_toMeasurable _ _
  have hfin : (P + Q) A ≠ ∞ := measure_ne_top _ _
  have hP : P.real A = P.real H := by
    simpa [Measure.real, H] using
      congrArg ENNReal.toReal
        (Measure.measure_toMeasurable_add_inter_left MeasurableSet.univ hfin).symm
  have hQ : Q.real A = Q.real H := by
    simpa [Measure.real, H] using
      congrArg ENNReal.toReal
        (Measure.measure_toMeasurable_add_inter_right MeasurableSet.univ hfin).symm
  rw [hP, hQ]
  set p := P.real H
  set q := Q.real H
  have hp : p ∈ Icc 0 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hq : q ∈ Icc 0 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  rcases hq.1.eq_or_lt with hq₀ | hq₀
  · refine le_of_eq_of_le (ENNReal.ofReal_of_nonpos ?_) zero_le
    have : 0 ≤ -(1 - p) * log (1 - p) := negMulLog_nonneg (sub_nonneg.mpr hp.2) (sub_le_self 1 hp.1)
    rw [← hq₀, klBin_zero_right]
    linarith
  rcases hq.2.eq_or_lt with hq₁ | hq₁
  · refine le_of_eq_of_le (ENNReal.ofReal_of_nonpos ?_) zero_le
    have : 0 ≤ -p * log p := negMulLog_nonneg hp.1 hp.2
    rw [hq₁, klBin_one_right]
    linarith
  have hlaw (R : Measure X) [IsProbabilityMeasure R] :=
    (hasLaw_indicator_one_bernoulliMeasure (M := ℝ) (P := R) hH.nullMeasurableSet).map_eq
  have hmeas : Measurable (H.indicator (1 : X → ℝ)) := measurable_one.indicator hH
  have hle := klDiv_map_le (μ := P) (ν := Q) hmeas
  rwa [hlaw P, hlaw Q, klDiv_bernoulliMeasure (measurableSet_singleton (1 : ℝ)) rfl
    (by norm_num) hp ⟨hq₀, hq₁⟩] at hle

end TauCeti
