/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Trace.Word
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.Combinatorics.TraceWord.Coding
import TauCeti.Probability.Independence.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Füredi–Komlós bound on growing Wigner traces

Let the entries of a Wigner matrix `Hₙ = Wₙ / √n` be independent and centred. Let them be bounded
by `K` almost surely and have second absolute moments at most `σ ^ 2`, for some `σ ≥ 0`. If
`K ≤ σ * γ ^ 2 * √n` with `0 ≤ γ ≤ 1`, then `‖E trace Hₙ ^ L‖ ≤ n * (σ * (2 + L * γ)) ^ L` for
every `L`.

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

## Main results

* `ProbabilityTheory.iIndepFun.norm_integral_trace_pow_wignerMatrix_le`: the trace bound.
* `ProbabilityTheory.iIndepFun.norm_integral_trace_pow_wignerMatrix_centeredTruncation_le`: the
  trace bound for the zero-diagonal Wigner matrices of centered truncations at radius `R`, whose
  entries are bounded by `2 * R`.

## References

* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal NNReal

namespace TauCeti

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
  calc _ ≤ c ^ t' * b ^ (L - 2 * t') := pow_mul_pow_sub_two_mul_le hb hc hcb (by omega) heL
    _ ≤ (σ ^ 2 / n) ^ t' * (σ * γ ^ 2) ^ (L - 2 * t') :=
        mul_le_mul (pow_le_pow_left₀ hc hcσ _) (pow_le_pow_left₀ hb hbσ _) (pow_nonneg hb _)
          (pow_nonneg (hc.trans hcσ) _)
    _ = _ := by
        rw [show L + 2 - 2 * (t' + 1) = L - 2 * t' by omega, hσL, div_pow, mul_pow,
          ← pow_mul γ 2]
        field_simp [hn.ne']
        ring

end TauCeti

namespace ProbabilityTheory.iIndepFun

open TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- **Füredi–Komlós trace bound.** Let the entries in the `n × n` corner be independent and
centred, bounded by `K` in norm almost surely, and with second absolute moments at most `σ ^ 2`,
where `σ ≥ 0`. If `0 ≤ γ ≤ 1` and `K ≤ σ * γ ^ 2 * √n`, then for every `L` the expected trace of
`Hₙ ^ L` has norm at most `n * (σ * (2 + L * γ)) ^ L`. -/
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
          w (fun s ↦ w (finRotate L s)) hw fun s ↦ by
            -- The position of each step is read `m + 2` times for some `m`.
            obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le'
              (two_le_card_filter_eq_of_no_singleton_fiber hw _ (mem_image_of_mem _ (mem_univ s)))
            rw [hm, Nat.add_sub_cancel]
            exact integral_norm_wignerMatrix_apply_pow_add_two_le hξm hηm hξK hηK hξσ hησ _ _ m
        rw [Fintype.card_fin] at hword
        exact hword.trans (pow_mul_pow_sub_le_mul_pow_div_pow hb₀ (le_min (by positivity)
          (sq_nonneg _)) (min_le_right _ _) (min_le_left _ _) ((div_le_iff₀ hsqrt).mpr hK)
          (Nat.cast_pos.mpr hn) (card_pos.mpr (univ_nonempty.image _))
          (card_image_le_card_cyclic_edges_add_one w)
          (two_mul_card_cyclic_edges_le_of_no_singleton_edge w hw))
    _ = n * σ ^ L * ∑ w : Fin L → Fin n with
          ∀ t, ∃ s ≠ t, s(w s, w (finRotate L s)) = s(w t, w (finRotate L t)),
        γ ^ (2 * (L + 2 - 2 * #(univ.image w))) / (n : ℝ) ^ #(univ.image w) := by
        rw [mul_sum]
    _ ≤ n * σ ^ L * (2 + L * γ) ^ L :=
        mul_le_mul_of_nonneg_left hcomb (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hσ L))
    _ = n * (σ * (2 + L * γ)) ^ L := by rw [mul_pow, mul_assoc]

/-- Independent upper entries in the `n × n` corner and a zero diagonal give independent
coordinates on the corner. -/
private theorem sumElim_zero_subtype_lt {n : ℕ}
    (h : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n} ↦ ξ ij.val) P) :
    iIndepFun (fun r : {ij : StrictUpper // ij.val.2 < n} ⊕ {i : ℕ // i < n} ↦
      Sum.elim (fun ij ↦ ξ ij.val) (fun _ _ ↦ ((0 : ℝ) : ℂ)) r) P := by
  let e := Equiv.ofInjective
    (Sum.inl : {ij : StrictUpper // ij.val.2 < n} → _ ⊕ {i : ℕ // i < n}) Sum.inl_injective
  refine iIndepFun.of_subtype_of_ae_eq_const_outside (s := Set.range Sum.inl) ?_ ?_
  · refine (h.precomp e.symm.injective).congr fun i ↦ ?_
    obtain ⟨_, a, rfl⟩ := i
    exact .of_forall fun ω ↦ by simp [e]
  · rintro (a | b) hi
    · exact absurd ⟨a, rfl⟩ hi
    · exact ⟨0, .of_forall fun _ ↦ rfl⟩

/-- **Füredi–Komlós bound for centered truncations.** Let the upper entries in the `N × N` corner
be independent and square-integrable, with second absolute moments at most `σ ^ 2`, where
`σ ≥ 0`, and let `0 ≤ γ ≤ 1`. If the bound `2 * R` on their centered truncations at radius `R`
satisfies `2 * R ≤ σ * γ ^ 2 * √N`, then for every `L` the expected trace of the `L`th power of
the zero-diagonal Wigner matrix of size `N` built from these truncations has norm at most
`N * (σ * (2 + L * γ)) ^ L`. -/
theorem norm_integral_trace_pow_wignerMatrix_centeredTruncation_le {N : ℕ}
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < N} ↦ ξ ij.val) P)
    (hξ : ∀ ij : StrictUpper, ij.val.2 < N → MemLp (ξ ij) 2 P) {σ γ : ℝ}
    (hσ : ∀ ij : StrictUpper, ij.val.2 < N → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P ≤ σ ^ 2) (hσ₀ : 0 ≤ σ)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (R : ℝ≥0) (hR : 2 * (R : ℝ) ≤ σ * γ ^ 2 * Real.sqrt N)
    (L : ℕ) :
    ‖∫ ω, (wignerMatrix (fun ij ↦ TauCeti.Probability.centeredTruncation (ξ ij) P R)
      (fun _ _ ↦ 0) N ω ^ L).trace ∂P‖ ≤ N * (σ * (2 + L * γ)) ^ L := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  exact (sumElim_zero_subtype_lt (ξ := fun ij ↦ TauCeti.Probability.centeredTruncation (ξ ij) P R)
      (hind.centeredTruncation fun _ ↦ R)).norm_integral_trace_pow_wignerMatrix_le
    (fun ij hij ↦ (hξ ij hij).aestronglyMeasurable.centeredTruncation R)
    (fun _ _ ↦ aestronglyMeasurable_const)
    (fun ij hij ↦ (hξ ij hij).aestronglyMeasurable.integral_centeredTruncation R)
    (fun _ _ ↦ integral_zero _ _)
    (fun _ _ ↦ .of_forall fun ω ↦ TauCeti.Probability.norm_centeredTruncation_le R ω)
    (fun _ _ ↦ .of_forall fun _ ↦ by simp)
    (fun ij hij ↦ ((hξ ij hij).integral_norm_centeredTruncation_sq_le R).trans (hσ ij hij))
    (fun _ _ ↦ by simpa using sq_nonneg σ) hσ₀ hγ₀ hγ₁ hR

end ProbabilityTheory.iIndepFun
