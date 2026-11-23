/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Trace.Word
import TauCeti.Combinatorics.TraceWord.Coding
import Mathlib.Tactic.FieldSimp

/-!
# Füredi–Komlós bound on growing Wigner traces

Let the entries of a Wigner matrix `Hₙ = Wₙ / √n` be independent and centred. Let them be bounded
by `K` almost surely and have second absolute moments at most `σ ^ 2`. If `K ≤ σ * γ ^ 2 * √n`
with `0 ≤ γ ≤ 1`, then `‖E trace Hₙ ^ L‖ ≤ n * (σ * (2 + L * γ)) ^ L` for every `L`.

The bound is uniform in the length `L`. With entries truncated at a power `n ^ a` with `a < 1/2`,
the choice `γ ^ 4 = K ^ 2 / (σ ^ 2 * n)` makes `L * γ` tend to zero along lengths `L` of
logarithmic order. So the expected trace grows at most like `n * (2 * σ) ^ L`, where `2 * σ` is
the right edge of the semicircle law of variance `σ ^ 2`. This is the input of the moment method
for the edge of the Wigner spectrum.

The proof expands the trace into closed walks that traverse each edge at least twice. Each edge
traversed `m` times contributes at most `b ^ (m - 2) * c`, where `b = K / √n` bounds the normalized
entries and `c = min (σ ^ 2 / n) (b ^ 2)` bounds their second moments. The walks are then counted
by the weighted Füredi–Komlós enumeration
`TauCeti.sum_pow_div_pow_card_image_le_of_no_singleton_edge`.

## Main result

* `TauCeti.norm_integral_trace_pow_wignerMatrix_le`: the trace bound.

## References

* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- Trading an edge for two extra traversals: `c ^ s * b ^ (L - 2 * s)` does not decrease when
`s` decreases, if `0 ≤ c ≤ b ^ 2`. -/
private theorem pow_mul_pow_sub_le {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hcb : c ≤ b ^ 2)
    {r s L : ℕ} (hrs : r ≤ s) (hs : 2 * s ≤ L) :
    c ^ s * b ^ (L - 2 * s) ≤ c ^ r * b ^ (L - 2 * r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  calc c ^ (r + d) * b ^ (L - 2 * (r + d)) = c ^ r * (c ^ d * b ^ (L - 2 * (r + d))) := by
        rw [pow_add, mul_assoc]
    _ ≤ c ^ r * ((b ^ 2) ^ d * b ^ (L - 2 * (r + d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc hcb d)
          (pow_nonneg hb _)) (pow_nonneg hc r)
    _ = c ^ r * b ^ (L - 2 * r) := by
        rw [← pow_mul, ← pow_add]
        congr 2
        omega

/-- The bound for a single trace word in the form counted by the Füredi–Komlós enumeration: a word
with `e` distinct edges and `t ≤ e + 1` vertices, `2 * e ≤ L`, contributes at most
`n * σ ^ L * γ ^ (2 * (L + 2 - 2 * t)) / n ^ t`. -/
private theorem pow_mul_pow_sub_le_mul_pow_div_pow {b c σ γ n : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcb : c ≤ b ^ 2) (hcσ : c ≤ σ ^ 2 / n) (hbσ : b ≤ σ * γ ^ 2) (hn : 0 < n)
    {e t L : ℕ} (ht : 1 ≤ t) (hte : t ≤ e + 1) (heL : 2 * e ≤ L) :
    c ^ e * b ^ (L - 2 * e) ≤ n * σ ^ L * (γ ^ (2 * (L + 2 - 2 * t)) / n ^ t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hσL : σ ^ L = (σ ^ 2) ^ t' * σ ^ (L - 2 * t') := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  calc _ ≤ c ^ t' * b ^ (L - 2 * t') := pow_mul_pow_sub_le hb hc hcb (by omega) heL
    _ ≤ (σ ^ 2 / n) ^ t' * (σ * γ ^ 2) ^ (L - 2 * t') :=
        mul_le_mul (pow_le_pow_left₀ hc hcσ _) (pow_le_pow_left₀ hb hbσ _) (pow_nonneg hb _)
          (pow_nonneg (hc.trans hcσ) _)
    _ = _ := by
        rw [show L + 2 - 2 * (t' + 1) = L - 2 * t' by omega, hσL, div_pow, mul_pow,
          ← pow_mul γ 2]
        field_simp [hn.ne']
        ring

/-- Bounded entries of second moment at most `σ ^ 2 / n` have absolute moments of order `m + 2`
at most `b ^ m * min (σ ^ 2 / n) (b ^ 2)`, for the bound `b = K / √n` on the normalized entries. -/
private theorem integral_norm_wignerMatrix_apply_pow_add_two_le [IsProbabilityMeasure P] {n : ℕ}
    {K σ : ℝ} (hn : 0 < n)
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEStronglyMeasurable (η i) P)
    (hξK : ∀ ij : StrictUpper, ij.val.2 < n → ∀ᵐ ω ∂P, ‖ξ ij ω‖ ≤ K)
    (hηK : ∀ i < n, ∀ᵐ ω ∂P, ‖η i ω‖ ≤ K)
    (hξσ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P ≤ σ ^ 2)
    (hησ : ∀ i < n, ∫ ω, ‖η i ω‖ ^ 2 ∂P ≤ σ ^ 2) (i j : Fin n) (m : ℕ) :
    ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ (m + 2) ∂P ≤
      (K / Real.sqrt n) ^ m * min (σ ^ 2 / n) ((K / Real.sqrt n) ^ 2) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hK₀ : 0 ≤ K := (hηK 0 hn).exists.elim fun _ h ↦ (norm_nonneg _).trans h
  have hξp (p : ℕ) : ∀ ij : StrictUpper, ij.val.2 < n → MemLp (ξ ij) p P :=
    fun ij hij ↦ .of_bound (hξm ij hij) K (hξK ij hij)
  have hηp (p : ℕ) : ∀ i < n, MemLp (η i) p P := fun i hi ↦ .of_bound (hηm i hi) K (hηK i hi)
  -- The normalized entries are bounded by `K / √n`.
  have hent : ∀ᵐ ω ∂P, ‖wignerMatrix ξ η n ω i j‖ ≤ K / Real.sqrt n := by
    by_cases hij : i = j
    · subst hij
      filter_upwards [hηK i.val i.isLt] with ω hω
      rw [wignerMatrix_apply_self, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hω hsqrt.le
    · filter_upwards [hξK ⟨(min i.val j.val, max i.val j.val),
        min_lt_max.mpr (Fin.val_ne_of_ne hij)⟩ (max_lt i.isLt j.isLt)] with ω hω
      rw [norm_wignerMatrix_apply_of_ne _ _ _ hij, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hω hsqrt.le
  have hint : Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω i j‖ ^ 2) P :=
    (memLp_wignerMatrix_apply (hξp 2) (hηp 2) i j).integrable_norm_pow two_ne_zero
  have hσn : ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P ≤ σ ^ 2 / n := by
    have := integral_norm_wignerMatrix_apply_pow_le (k := 2) hξσ hησ i j
    rwa [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), inv_mul_eq_div] at this
  have hbb : ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P ≤ (K / Real.sqrt n) ^ 2 := by
    calc _ ≤ ∫ _ : Ω, (K / Real.sqrt n) ^ 2 ∂P := integral_mono_ae hint (integrable_const _)
          (hent.mono fun ω hω ↦ pow_le_pow_left₀ (norm_nonneg _) hω 2)
      _ = (K / Real.sqrt n) ^ 2 := by simp
  calc _ ≤ ∫ ω, (K / Real.sqrt n) ^ m * ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P :=
        integral_mono_ae ((memLp_wignerMatrix_apply (hξp (m + 2)) (hηp (m + 2)) i j)
          |>.integrable_norm_pow (Nat.succ_ne_zero _)) (hint.const_mul _)
          (hent.mono fun ω hω ↦ by
            simp only [pow_add]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hω m)
              (sq_nonneg _))
    _ = (K / Real.sqrt n) ^ m * ∫ ω, ‖wignerMatrix ξ η n ω i j‖ ^ 2 ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_min hσn hbb)
        (pow_nonneg (div_nonneg hK₀ hsqrt.le) m)

/-- **Füredi–Komlós trace bound.** Let the entries in the `n × n` corner be independent and
centred, bounded by `K` in norm almost surely, and with second absolute moments at most `σ ^ 2`.
If `0 ≤ γ ≤ 1` and `K ≤ σ * γ ^ 2 * √n`, then for every `L` the expected trace of `Hₙ ^ L` has
norm at most `n * (σ * (2 + L * γ)) ^ L`. -/
theorem norm_integral_trace_pow_wignerMatrix_le {L n : ℕ} {K σ γ : ℝ}
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.val) (fun i ω ↦ (η i.val ω : ℂ)) r) P)
    (hξm : ∀ ij : StrictUpper, ij.val.2 < n → AEStronglyMeasurable (ξ ij) P)
    (hηm : ∀ i < n, AEStronglyMeasurable (η i) P)
    (hξ₀ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hη₀ : ∀ i < n, ∫ ω, η i ω ∂P = 0)
    (hξK : ∀ ij : StrictUpper, ij.val.2 < n → ∀ᵐ ω ∂P, ‖ξ ij ω‖ ≤ K)
    (hηK : ∀ i < n, ∀ᵐ ω ∂P, ‖η i ω‖ ≤ K)
    (hξσ : ∀ ij : StrictUpper, ij.val.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P ≤ σ ^ 2)
    (hησ : ∀ i < n, ∫ ω, ‖η i ω‖ ^ 2 ∂P ≤ σ ^ 2)
    (hσ : 0 ≤ σ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hK : K ≤ σ * γ ^ 2 * Real.sqrt n) :
    ‖∫ ω, (wignerMatrix ξ η n ω ^ L).trace ∂P‖ ≤ n * (σ * (2 + L * γ)) ^ L := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hK₀ : 0 ≤ K := (hηK 0 hn).exists.elim fun _ h ↦ (norm_nonneg _).trans h
  have hb₀ : 0 ≤ K / Real.sqrt n := div_nonneg hK₀ hsqrt.le
  rw [integral_trace_pow_wignerMatrix hL.ne' hindep hξ₀ hη₀
    (fun ij hij ↦ .of_bound (hξm ij hij) K (hξK ij hij))
    (fun i hi ↦ .of_bound (hηm i hi) K (hηK i hi))]
  have hcomb := sum_pow_div_pow_card_image_le_of_no_singleton_edge (α := Fin n) (L := L) hγ₀ hγ₁
  rw [Fintype.card_fin] at hcomb
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ w : Fin L → Fin n with
          ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
        n * σ ^ L * (γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / (n : ℝ) ^ #(univ.image w)) := by
        refine sum_le_sum fun w hw ↦ ?_
        have hw := (mem_filter.mp hw).2
        -- A walk with `t` vertices and `e` distinct edges has `t ≤ e + 1` and `2 * e ≤ L`.
        have hword := norm_integral_prod_wignerMatrix_apply_le_of_no_singleton_edge
          (fun ij hij ↦ (hξm ij hij).aemeasurable) (fun i hi ↦ (hηm i hi).aemeasurable) hindep
          (fun i j m _ ↦ integral_norm_wignerMatrix_apply_pow_add_two_le hn hξm hηm hξK hηK hξσ
            hησ i j m) w (fun s ↦ w (finRotate L s)) hw
        rw [Fintype.card_fin] at hword
        exact hword.trans (pow_mul_pow_sub_le_mul_pow_div_pow hb₀ (le_min (by positivity)
          (sq_nonneg _)) (min_le_right _ _) (min_le_left _ _) ((div_le_iff₀ hsqrt).mpr hK)
          (Nat.cast_pos.mpr hn) (card_pos.mpr (univ_nonempty.image _))
          ((card_image_le_card_nonloop_cyclic_edges_add_one w).trans
            (Nat.add_le_add_right (card_le_card (image_subset_image (filter_subset _ _))) 1))
          (two_mul_card_cyclic_edges_le_of_no_singleton_edge w hw))
    _ = n * σ ^ L * ∑ w : Fin L → Fin n with
          ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
        γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / (n : ℝ) ^ #(univ.image w) := by
        rw [mul_sum]
    _ ≤ n * σ ^ L * (2 + L * γ) ^ L :=
        mul_le_mul_of_nonneg_left hcomb (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hσ L))
    _ = n * (σ * (2 + L * γ)) ^ L := by rw [mul_pow, mul_assoc]

end TauCeti
