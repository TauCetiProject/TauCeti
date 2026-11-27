/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.RepresentationTheory.LinearCharacter.QuadraticCoset

/-!
# Averaging the main term of a Frobenius-restricted Riesz sum

When a prime sum is restricted to the complement of an index-two subgroup, the Fourier
expansion of its main term keeps only the trivial and quadratic characters. The cap at a
place changes the sampling scale to `a / w`; multiplying back by `w` leaves the dependence
on the caps only through the mean of `log w` over the places.

The arithmetic application and normalization are from Levent Alpöge's `Deduction.ch_balance`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open scoped BigOperators ComplexConjugate

namespace MonoidHom

/-- In the main-term correction for a Frobenius-restricted first Riesz sum, the constants `d χ`
for nontrivial characters cancel except for `d q`, which enters with a positive sign. The
principal constant is `b` (arithmetically `1 + γ`). Multiplication by `c` and `τ` matches the
caps off the kernel with those on the kernel. -/
theorem expect_filter_apply_ne_one_mul_log_div_sub_sum_conj_mul_eq {G : Type*} [Group G] [Fintype G]
    (q : G →* ℂˣ) [DecidablePred fun g ↦ q g ≠ 1] [DecidablePred fun h ↦ q h = 1]
    (hq : q * q = 1) {c τ : G} (hc : (q c : ℂ) = -1) (hτ : q τ = 1)
    (s : Finset (G →* ℂˣ)) [DecidableEq (G →* ℂˣ)] (hs : q ∈ s) (d : (G →* ℂˣ) → ℂ) (b : ℂ)
    (a : ℝ) (w : G → ℝ) (hw : ∀ h ∈ q.ker, w h ≠ 0) :
    (𝔼 g with q g ≠ 1, (w (c * g * τ) : ℂ) * ((a / w (c * g * τ) : ℝ) : ℂ) *
      ((Real.log (a / w (c * g * τ)) : ℂ) - b -
        ∑ χ ∈ s.erase 1, conj (χ g : ℂ) * d χ)) =
      (a : ℂ) * ((Real.log a : ℂ) - b + d q - 𝔼 h with q h = 1, (Real.log (w h) : ℂ)) := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  have hc₁ : q c ≠ 1 := (q.apply_ne_one_iff_of_mul_self_eq_one hq c).mpr hc
  have hq₁ : q ≠ 1 := fun h ↦ hc₁ (by simp [h])
  have hmem (g : G) : q g ≠ 1 ↔ q (c * g * τ) = 1 := by
    rcases q.apply_eq_one_or_eq_neg_one_of_mul_self_eq_one hq g with hg | hg
    · simp [hg, hτ, hc₁]
    · have hc' : q c = -1 := Units.val_eq_neg_one.mp hc
      exact ⟨fun _ ↦ by simp [hg, hc', hτ],
        fun _ ↦ (q.apply_ne_one_iff_of_mul_self_eq_one hq g).mpr (by simp [hg])⟩
  let t := Finset.univ.filter fun g ↦ q g ≠ 1
  have ht : t.Nonempty := ⟨c, by simp [t, hc₁]⟩
  have hlog : (𝔼 g ∈ t, (Real.log (w (c * g * τ)) : ℂ)) =
      𝔼 h with q h = 1, (Real.log (w h) : ℂ) :=
    Finset.expect_equiv ((Equiv.mulLeft c).trans (Equiv.mulRight τ))
      (fun g ↦ by simpa [t] using hmem g) (fun _ _ ↦ rfl)
  have hd : (𝔼 g ∈ t, ∑ χ ∈ s.erase 1, conj (χ g : ℂ) * d χ) = -d q := by
    rw [Finset.expect_sum_comm]
    have hconj (χ : G →* ℂˣ) : (𝔼 g ∈ t, conj (χ g : ℂ)) = conj (𝔼 g ∈ t, (χ g : ℂ)) := by
      simp only [Finset.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]
    simp_rw [← Finset.expect_mul, hconj]
    simp only [t, q.expect_filter_apply_ne_one_apply_of_mul_self_eq_one _ hq hq₁]
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_erase.mpr ⟨hq₁, hs⟩)]
    · simp [hq₁]
    · intro χ hχ hχq
      simp [(Finset.mem_erase.mp hχ).1, hχq]
  calc
    _ = 𝔼 g ∈ t, (a : ℂ) * ((Real.log a : ℂ) - b - (Real.log (w (c * g * τ)) : ℂ) -
          ∑ χ ∈ s.erase 1, conj (χ g : ℂ) * d χ) := by
      apply Finset.expect_congr rfl
      intro g hg
      have hwg := hw _ (MonoidHom.mem_ker.mpr ((hmem g).mp (Finset.mem_filter.mp hg).2))
      simp only [Real.log_div ha hwg, Complex.ofReal_div,
        mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hwg), Complex.ofReal_sub,
        sub_right_comm _ _ b]
    _ = _ := by
      simp only [← Finset.mul_expect, Finset.expect_sub_distrib, Finset.expect_const ht, hd, hlog]
      ring

end MonoidHom
