/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.LocalLimit.MaximalSpanOne
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Lattice

/-!
# The characteristic function of an integer law of maximal span one

Let `μ` be a probability measure on `ℤ` and `φ = charFun (μ.map Int.cast)` the characteristic
function of its image on the line, which has period `2π`. Then `μ` has maximal span one exactly
when `|φ(t)| < 1` for every real `t` that is not an integer multiple of `2π`.

If `μ` is carried by a coset `b + hℤ` with `h ≥ 2`, then `φ(2π/h) = exp(2πi b/h)` has modulus one.
Conversely, `|φ(t)| = 1` forces the phases `t k` of the atoms `k` of `μ` into a single coset
`c + 2πℤ`, so that `t (k - l) ∈ 2πℤ` for any two atoms `k`, `l`; when these differences generate
`ℤ`, `t` itself lies in `2πℤ`.

By continuity and compactness, the characteristic function of a law of maximal span one is then
bounded away from modulus one on every compact set of frequencies avoiding `2πℤ`, in particular on
`δ ≤ |t| ≤ π` for `δ > 0`. This is the bound that controls the contribution of the frequencies
away from `0` in the Fourier-analytic proof of the local limit theorem for lattice laws.

## Main results

Throughout, `μ` is a probability measure on `ℤ`.

* `MeasureTheory.Measure.HasMaximalSpanOne.norm_charFun_lt_one`: a law of maximal span one has
  `|φ(t)| < 1` for `t ∉ 2πℤ`.
* `MeasureTheory.Measure.hasMaximalSpanOne_iff_norm_charFun_lt_one`: maximal span one is
  equivalent to `|φ(t)| < 1` for all `t ∉ 2πℤ`.
* `MeasureTheory.Measure.HasMaximalSpanOne.exists_lt_one_forall_norm_charFun_le`: on a compact
  set of frequencies avoiding `2πℤ`, `|φ|` is at most some `η < 1`;
  `MeasureTheory.Measure.HasMaximalSpanOne.exists_lt_one_forall_norm_charFun_le_of_le_abs`: in
  particular, for `δ > 0` there is `η < 1` with `|φ(t)| ≤ η` whenever `δ ≤ |t| ≤ π`.

## References

* R. Durrett, *Probability: Theory and Examples*, fifth edition, §3.5, Theorem 3.5.2 and the
  proof of Theorem 3.5.3.
-/

public section

open Complex Real

open scoped Pointwise

namespace MeasureTheory.Measure

variable {μ : Measure ℤ} [IsProbabilityMeasure μ]

/-- The characteristic function of a law of maximal span one on `ℤ` has modulus less than one at
every frequency that is not an integer multiple of `2π`. -/
theorem HasMaximalSpanOne.norm_charFun_lt_one (hμ : μ.HasMaximalSpanOne) {t : ℝ}
    (ht : ∀ j : ℤ, t ≠ j * (2 * π)) : ‖charFun (μ.map (Int.cast : ℤ → ℝ)) t‖ < 1 := by
  refine (norm_charFun_le_one t).lt_of_ne fun h1 ↦ ?_
  obtain ⟨c, hc⟩ := (norm_charFun_eq_one_iff t).1 h1
  have hatom : ∀ k : ℤ, μ {k} ≠ 0 → ∃ n : ℤ, k * t = c + n * (2 * π) := by
    refine ae_iff_of_countable.1 ((ae_of_ae_map (measurable_of_countable _).aemeasurable hc).mono
      fun k hk ↦ ?_)
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm t] using hk
  -- The integers `d` with `d t ∈ 2πℤ` form a subgroup containing the differences of atoms.
  let G : AddSubgroup ℤ := (AddSubgroup.zmultiples (2 * π)).comap
    ((AddMonoidHom.mulRight t).comp (Int.castAddHom ℝ))
  have hG : ∀ d : ℤ, d ∈ G ↔ ∃ j : ℤ, j * (2 * π) = d * t := by
    simp [G, AddSubgroup.mem_zmultiples_iff]
  have hle : AddSubgroup.closure ({k : ℤ | μ {k} ≠ 0} - {k : ℤ | μ {k} ≠ 0}) ≤ G := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨k, hk, l, hl, rfl⟩
    obtain ⟨n, hn⟩ := hatom k hk
    obtain ⟨m, hm⟩ := hatom l hl
    exact (hG _).2 ⟨n - m, by push_cast; linarith⟩
  rw [hasMaximalSpanOne_iff_closure_sub_eq_top.1 hμ, top_le_iff] at hle
  obtain ⟨j, hj⟩ := (hG 1).1 (hle ▸ AddSubgroup.mem_top 1)
  exact ht j (by simpa using hj.symm)

/-- A probability measure on `ℤ` has maximal span one if and only if the characteristic function
of its image on the line has modulus less than one at every frequency that is not an integer
multiple of `2π`. -/
theorem hasMaximalSpanOne_iff_norm_charFun_lt_one :
    μ.HasMaximalSpanOne ↔
      ∀ t : ℝ, (∀ j : ℤ, t ≠ j * (2 * π)) → ‖charFun (μ.map (Int.cast : ℤ → ℝ)) t‖ < 1 := by
  refine ⟨fun hμ _ ↦ hμ.norm_charFun_lt_one, fun h ↦ hasMaximalSpanOne_iff.2 fun b n hn hnull ↦ ?_⟩
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- A law carried by `b + nℤ` has phases `2π k/n` in the coset `2π b/n + 2πℤ`.
  have hae : ∀ᵐ k ∂μ, (n : ℤ) ∣ k - b := ae_iff.2 hnull
  have hone : ‖charFun (μ.map (Int.cast : ℤ → ℝ)) (2 * π / n)‖ = 1 := by
    refine (norm_charFun_eq_one_iff _).2 ⟨2 * π / n * b, ?_⟩
    rw [ae_map_iff (measurable_of_countable _).aemeasurable ?_]
    · refine hae.mono fun k ⟨m, hm⟩ ↦ ⟨m, ?_⟩
      have hk : (k : ℝ) = b + n * m := by exact_mod_cast (by omega : k = b + n * m)
      simp only [RCLike.inner_apply, conj_trivial, hk]
      field_simp
    · simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun _ ↦ measurableSet_eq_fun (by fun_prop) (by fun_prop)
  refine (h (2 * π / n) fun j hj ↦ ?_).ne hone
  -- `2π/n` is not a multiple of `2π`, since `0 < 1/n < 1`.
  rw [div_eq_iff hn₀] at hj
  have hjn : (j * n : ℝ) * (2 * π) = 1 * (2 * π) := by linear_combination -hj
  have hjn' : j * (n : ℤ) = 1 := by exact_mod_cast mul_right_cancel₀ two_pi_pos.ne' hjn
  rcases le_or_gt j 0 with hj₀ | hj₀ <;>
    nlinarith [show (2 : ℤ) ≤ n by exact_mod_cast hn]

/-- The characteristic function of a law of maximal span one on `ℤ` is bounded away from modulus
one on every compact set of frequencies containing no integer multiple of `2π`. -/
theorem HasMaximalSpanOne.exists_lt_one_forall_norm_charFun_le (hμ : μ.HasMaximalSpanOne)
    {K : Set ℝ} (hK : IsCompact K) (hK₀ : ∀ t ∈ K, ∀ j : ℤ, t ≠ j * (2 * π)) :
    ∃ η < 1, ∀ t ∈ K, ‖charFun (μ.map (Int.cast : ℤ → ℝ)) t‖ ≤ η := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, zero_lt_one, by simp⟩
  obtain ⟨t₀, ht₀, hmax⟩ := hK.exists_isMaxOn hne (by fun_prop : Continuous fun t ↦
    ‖charFun (μ.map (Int.cast : ℤ → ℝ)) t‖).continuousOn
  exact ⟨_, hμ.norm_charFun_lt_one (hK₀ t₀ ht₀), fun t ht ↦ hmax ht⟩

/-- The characteristic function of a law of maximal span one on `ℤ` is bounded away from modulus
one on `δ ≤ |t| ≤ π`, for every `δ > 0`. -/
theorem HasMaximalSpanOne.exists_lt_one_forall_norm_charFun_le_of_le_abs
    (hμ : μ.HasMaximalSpanOne) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η < 1, ∀ t : ℝ, δ ≤ |t| → |t| ≤ π → ‖charFun (μ.map (Int.cast : ℤ → ℝ)) t‖ ≤ η := by
  have hK : IsCompact {t : ℝ | δ ≤ |t| ∧ |t| ≤ π} :=
    (isCompact_Icc (a := -π) (b := π)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const))
      fun t ht ↦ abs_le.1 ht.2
  obtain ⟨η, hη, hle⟩ := hμ.exists_lt_one_forall_norm_charFun_le hK fun t ⟨hδt, htπ⟩ j hj ↦ by
    -- A nonzero multiple of `2π` has modulus at least `2π > π`.
    subst hj
    rcases eq_or_ne j 0 with rfl | hj
    · simp only [Int.cast_zero, zero_mul, abs_zero] at hδt
      linarith
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    rw [abs_mul, abs_of_pos two_pi_pos] at htπ
    nlinarith [pi_pos]
  exact ⟨η, hη, fun t h₁ h₂ ↦ hle t ⟨h₁, h₂⟩⟩

end MeasureTheory.Measure
