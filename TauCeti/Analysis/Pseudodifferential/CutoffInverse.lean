/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# The cut-off inverse of a symbol

Let `a ∈ S^m_{1,0}` be a symbol of order `m` whose values `a(x, ξ) : V →L[ℂ] W` are invertible at
all large frequencies `|R| ≤ ‖ξ‖`, with the inverse bound `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there (the
constant `C` may depend on a compact set of positions). Such a symbol is elliptic in the sense of
the full-symbol calculus. For a frequency cutoff `χ`, the function

`b(x, ξ) = χ(ξ / R) a(x, ξ)⁻¹`

is then a symbol of order `-m` (`TauCeti.Symbol.cutoffInverse`): every mixed derivative satisfies
`‖∂_x^α ∂_ξ^β b(x, ξ)‖ ≤ C ⟨ξ⟩^(-m - |β|)`. For every `R`, it inverts `a` up to the error
`1 - χ(ξ / R)`:

`a(x, ξ) b(x, ξ) = χ(ξ / R) · id`, `b(x, ξ) a(x, ξ) = χ(ξ / R) · id`

(`TauCeti.Symbol.coefficient_comp_coefficient_cutoffInverse`,
`TauCeti.Symbol.coefficient_cutoffInverse_comp_coefficient`). For `R ≠ 0` this error has compact
frequency support, and `b` is the pointwise inverse once `‖ξ‖ ≥ 2|R|`
(`TauCeti.Symbol.coefficient_cutoffInverse_of_two_mul_abs_le`); for `R = 0` the cutoff
`χ(ξ / 0) = χ(0)` vanishes, so `b = 0`. If `a` satisfies uniform estimates and the inverse bound
holds with a constant independent of the position, `b` satisfies uniform estimates as well
(`TauCeti.Symbol.IsUniform.cutoffInverse`). This is the first step of the construction of a
parametrix of an elliptic operator: `b` is the leading term of its symbol.

## Implementation notes

The derivative estimates rest on the formula `∂(a⁻¹) = -a⁻¹ (∂a) a⁻¹`
(`DifferentiableAt.fderiv_clm_inverse`). Applied repeatedly, it writes every derivative of `a⁻¹`
as a sum of products of `a⁻¹` with derivatives of `a`. Each product has the order `-m - |β|` by
the Leibniz rule. The inverse is only smooth on the open set where `a` is invertible, so the proof
runs an induction on the number of derivatives, using the iterated directional derivatives
`TauCeti.iteratedFDerivAlong` in `ℝⁿ × ℝⁿ` along arbitrary words of position and frequency
directions (`TauCeti.mixedDirection`) and their calculus on open sets.
For smooth functions these are the mixed derivatives `TauCeti.mixedDeriv` of the symbol estimates
(`TauCeti.iteratedFDerivAlong_map_mixedDirection`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

section Bounds

/-! ### Symbol estimates along words, and the Leibniz rule

A word `w : List (Fin n ⊕ Fin n)` of position letters `Sum.inl j` and frequency letters
`Sum.inr j` names the iterated directional derivative `iteratedFDerivAlong ℝ (w.map mixedDirection)`
on `ℝⁿ × ℝⁿ`; each frequency letter lowers the order of a symbol estimate by one. -/

/-- The frequency letters of a word, in order. -/
private def freqLetters (w : List (Fin n ⊕ Fin n)) : List (Fin n) := w.filterMap Sum.getRight?

/-- The order lost by a derivative along a letter: `1` for a frequency direction, `0` for a
position direction. -/
private def letterOrder : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

private theorem length_freqLetters_append_singleton (w : List (Fin n ⊕ Fin n))
    (l : Fin n ⊕ Fin n) :
    ((freqLetters (w ++ [l])).length : ℝ) = letterOrder l + (freqLetters w).length := by
  cases l <;> simp [freqLetters, letterOrder, add_comm]

private theorem weight_mul (ξ : CoordinateSpace n) (s t : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (t / 2) = (1 + ‖ξ‖ ^ 2) ^ ((s + t) / 2) := by
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The symbol estimates of order `μ` on a set `S`, for all iterated directional derivatives
along words of length at most `k`. -/
private def WordBounds (S : Set (CoordinateSpace n × CoordinateSpace n)) (μ : ℝ) (k : ℕ)
    (f : CoordinateSpace n × CoordinateSpace n → A) : Prop :=
  ∀ w : List (Fin n ⊕ Fin n), w.length ≤ k → ∃ C, ∀ p ∈ S,
    ‖iteratedFDerivAlong ℝ (w.map mixedDirection) f p‖ ≤
      C * (1 + ‖p.2‖ ^ 2) ^ ((μ - (freqLetters w).length) / 2)

variable {S : Set (CoordinateSpace n × CoordinateSpace n)} {μ : ℝ} {k : ℕ}
  {f : CoordinateSpace n × CoordinateSpace n → A}

private theorem WordBounds.mono {k' : ℕ} (h : WordBounds S μ k f) (hk : k' ≤ k) :
    WordBounds S μ k' f :=
  fun w hw => h w (hw.trans hk)

/-- A directional derivative lowers the order by the order of its letter. -/
private theorem WordBounds.fderiv_apply (h : WordBounds S μ (k + 1) f) (l : Fin n ⊕ Fin n) :
    WordBounds S (μ - letterOrder l) k (iteratedFDerivAlong ℝ [mixedDirection l] f) := by
  intro w hw
  obtain ⟨C, hC⟩ := h (w ++ [l]) (by simpa using hw)
  refine ⟨C, fun p hp => ?_⟩
  have e : μ - letterOrder l - (freqLetters w).length = μ - (freqLetters (w ++ [l])).length := by
    rw [length_freqLetters_append_singleton]
    ring
  rw [e, ← iteratedFDerivAlong_append, ← List.map_singleton, ← List.map_append]
  exact hC p hp

/-- The symbol estimates of a smooth function, stated with mixed derivatives at the positions of
a set `T`, give its estimates along all words on every set of points with position in `T`. -/
private theorem wordBounds_of_mixedDeriv (hf : ContDiff ℝ ∞ f) {T : Set (CoordinateSpace n)}
    (hb : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2))
    (hS : ∀ p ∈ S, p.1 ∈ T) (k : ℕ) : WordBounds S μ k f := by
  intro w _
  obtain ⟨C, hC⟩ := hb (w.filterMap Sum.getLeft?) (freqLetters w)
  refine ⟨C, fun p hp => ?_⟩
  rw [iteratedFDerivAlong_map_mixedDirection w (hf.of_le (by exact_mod_cast le_top))]
  exact hC p.1 (hS p hp) p.2

variable {A₁ A₂ : Type*} [NormedAddCommGroup A₁] [NormedSpace ℝ A₁] [NormedAddCommGroup A₂]
  [NormedSpace ℝ A₂]

private theorem norm_bilinear_le (B : A₁ →L[ℝ] A₂ →L[ℝ] A) {x : A₁} {y : A₂} {C D s t : ℝ}
    {ξ : CoordinateSpace n} (hx : ‖x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2))
    (hy : ‖y‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ (t / 2)) :
    ‖B x y‖ ≤ ‖B‖ * C * D * (1 + ‖ξ‖ ^ 2) ^ ((s + t) / 2) := by
  calc ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := B.le_opNorm₂ x y
    _ ≤ ‖B‖ * (C * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) * (D * (1 + ‖ξ‖ ^ 2) ^ (t / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx B.opNorm_nonneg) hy (norm_nonneg _)
        (mul_nonneg B.opNorm_nonneg ((norm_nonneg _).trans hx))
    _ = ‖B‖ * C * D * (1 + ‖ξ‖ ^ 2) ^ ((s + t) / 2) := by
      rw [← weight_mul]
      ring

private theorem wordBounds_bilinear_nil (B : A₁ →L[ℝ] A₂ →L[ℝ] A)
    {f₁ : CoordinateSpace n × CoordinateSpace n → A₁}
    {f₂ : CoordinateSpace n × CoordinateSpace n → A₂} {ν : ℝ} (h₁ : WordBounds S μ k f₁)
    (h₂ : WordBounds S ν k f₂) : ∃ C, ∀ p ∈ S,
      ‖iteratedFDerivAlong ℝ (([] : List (Fin n ⊕ Fin n)).map mixedDirection)
          (fun p => B (f₁ p) (f₂ p)) p‖ ≤
        C * (1 + ‖p.2‖ ^ 2) ^ ((μ + ν - (freqLetters ([] : List (Fin n ⊕ Fin n))).length) / 2) := by
  obtain ⟨C, hC⟩ := h₁ [] (Nat.zero_le _)
  obtain ⟨D, hD⟩ := h₂ [] (Nat.zero_le _)
  refine ⟨‖B‖ * C * D, fun p hp => ?_⟩
  have h := norm_bilinear_le B (hC p hp) (hD p hp)
  simp only [freqLetters, List.filterMap_nil, List.length_nil, CharP.cast_eq_zero, sub_zero,
    List.map_nil, iteratedFDerivAlong_nil] at h ⊢
  exact h

/-- The Leibniz rule for symbol estimates: a bilinear expression in two functions smooth near
`S`, satisfying estimates of orders `μ` and `ν` on `S`, satisfies estimates of order `μ + ν`. -/
private theorem WordBounds.bilinear (B : A₁ →L[ℝ] A₂ →L[ℝ] A)
    {U : Set (CoordinateSpace n × CoordinateSpace n)} (hU : IsOpen U) (hSU : S ⊆ U)
    {f₁ : CoordinateSpace n × CoordinateSpace n → A₁}
    {f₂ : CoordinateSpace n × CoordinateSpace n → A₂} (hf₁ : ContDiffOn ℝ ∞ f₁ U)
    (hf₂ : ContDiffOn ℝ ∞ f₂ U) {ν : ℝ} (h₁ : WordBounds S μ k f₁) (h₂ : WordBounds S ν k f₂) :
    WordBounds S (μ + ν) k fun p => B (f₁ p) (f₂ p) := by
  induction k generalizing f₁ f₂ μ ν with
  | zero =>
    intro w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    exact wordBounds_bilinear_nil B h₁ h₂
  | succ k ih =>
    intro w hw
    rcases w.eq_nil_or_concat' with rfl | ⟨w, l, rfl⟩
    · exact wordBounds_bilinear_nil B h₁ h₂
    · have hw' : w.length ≤ k := by simpa using hw
      have hd₁ := hf₁.iteratedFDerivAlong (m := ∞) hU [mixedDirection l] (by simp)
      have hd₂ := hf₂.iteratedFDerivAlong (m := ∞) hU [mixedDirection l] (by simp)
      obtain ⟨C₁, hC₁⟩ := ih hd₁ hf₂ (h₁.fderiv_apply l) (h₂.mono k.le_succ) w hw'
      obtain ⟨C₂, hC₂⟩ := ih hf₁ hd₂ (h₁.mono k.le_succ) (h₂.fderiv_apply l) w hw'
      refine ⟨C₁ + C₂, fun p hp => ?_⟩
      have heq : iteratedFDerivAlong ℝ ((w ++ [l]).map mixedDirection)
            (fun p => B (f₁ p) (f₂ p)) p =
          iteratedFDerivAlong ℝ (w.map mixedDirection)
              (fun q => B (iteratedFDerivAlong ℝ [mixedDirection l] f₁ q) (f₂ q)) p +
            iteratedFDerivAlong ℝ (w.map mixedDirection)
              (fun q => B (f₁ q) (iteratedFDerivAlong ℝ [mixedDirection l] f₂ q)) p := by
        rw [List.map_append, iteratedFDerivAlong_append, List.map_singleton]
        refine ((Filter.EventuallyEq.iteratedFDerivAlong ?_ _).eq_of_nhds).trans
          (iteratedFDerivAlong_add_apply_of_isOpen
            ((contDiffOn_const.clm_apply hd₁).clm_apply hf₂)
            ((contDiffOn_const.clm_apply hf₁).clm_apply hd₂) hU _ (by exact_mod_cast le_top)
            (hSU hp))
        filter_upwards [hU.mem_nhds (hSU hp)] with q hq
        simp only [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil, Pi.add_apply]
        rw [B.fderiv_of_bilinear ((hf₁.differentiableOn (by simp)).differentiableAt
          (hU.mem_nhds hq)) ((hf₂.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq))]
        simp [add_comm]
      have e₁ : μ - letterOrder l + ν - (freqLetters w).length =
          μ + ν - (freqLetters (w ++ [l])).length := by
        rw [length_freqLetters_append_singleton]
        ring
      have e₂ : μ + (ν - letterOrder l) - (freqLetters w).length =
          μ + ν - (freqLetters (w ++ [l])).length := by
        rw [length_freqLetters_append_singleton]
        ring
      rw [heq]
      calc _ ≤ ‖iteratedFDerivAlong ℝ (w.map mixedDirection)
              (fun q => B (iteratedFDerivAlong ℝ [mixedDirection l] f₁ q) (f₂ q)) p‖ +
            ‖iteratedFDerivAlong ℝ (w.map mixedDirection)
              (fun q => B (f₁ q) (iteratedFDerivAlong ℝ [mixedDirection l] f₂ q)) p‖ :=
            norm_add_le _ _
        _ ≤ _ := add_le_add (hC₁ p hp) (hC₂ p hp)
        _ = _ := by rw [e₁, e₂, add_mul]

end Bounds

section Cutoff

/-! ### The rescaled frequency cutoff -/

/-- If `‖ξ / R‖ ≥ 1`, then `|R| ≤ ‖ξ‖`. -/
private theorem abs_le_norm_of_one_le_norm_inv_smul {R : ℝ} {ξ : CoordinateSpace n}
    (h : 1 ≤ ‖R⁻¹ • ξ‖) : |R| ≤ ‖ξ‖ := by
  rcases eq_or_ne R 0 with rfl | hR
  · norm_num at h
  · rw [norm_smul, norm_inv, Real.norm_eq_abs] at h
    simpa using (le_inv_mul_iff₀ (abs_pos.2 hR)).1 h

variable (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)

private theorem wordBounds_cutoff (S : Set (CoordinateSpace n × CoordinateSpace n)) (k : ℕ) :
    WordBounds S 0 k fun p => χ (R⁻¹ • p.2) :=
  wordBounds_of_mixedDeriv (χ.contDiff_comp_inv_smul_snd R) (T := univ)
    (fun α β => (χ.exists_bound_mixedDeriv_comp_inv_smul_snd R α β).imp fun _ h x _ ξ => h x ξ)
    (fun _ _ => mem_univ _) k

end Cutoff

section Inverse

/-! ### Derivatives of the pointwise inverse of a symbol -/

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- Composition of complex-linear maps, as a real bilinear map. -/
private abbrev compR (V₁ V₂ V₃ : Type*) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
    [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [NormedAddCommGroup V₃] [NormedSpace ℂ V₃] :
    (V₂ →L[ℂ] V₃) →L[ℝ] (V₁ →L[ℂ] V₂) →L[ℝ] (V₁ →L[ℂ] V₃) :=
  (ContinuousLinearMap.compL ℂ V₁ V₂ V₃).bilinearRestrictScalars ℝ

private theorem isOpen_setOf_isInvertible (a : Symbol n V W m) :
    IsOpen {p | (a.coefficient p).IsInvertible} :=
  ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage a.contDiff_coefficient.continuous

private theorem contDiffOn_inverse (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (fun p => (a.coefficient p).inverse) {p | (a.coefficient p).IsInvertible} :=
  a.contDiff_coefficient.contDiffOn.clm_inverse fun _ hp => hp

/-- The pointwise inverse of a symbol of order `m`, at the points of large frequency with position
in `T`, satisfies the estimates of order `-m` along all words, provided the inverse exists there
and satisfies the estimate of order `-m` itself. -/
private theorem wordBounds_inverse (a : Symbol n V W m) {T : Set (CoordinateSpace n)} {R : ℝ}
    (ha : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hinv : ∀ x ∈ T, ∀ ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hC : ∃ C, ∀ x ∈ T, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) (k : ℕ) :
    WordBounds {p | p.1 ∈ T ∧ |R| ≤ ‖p.2‖} (-m) k fun p => (a.coefficient p).inverse := by
  set S : Set (CoordinateSpace n × CoordinateSpace n) := {p | p.1 ∈ T ∧ |R| ≤ ‖p.2‖}
  have hU := isOpen_setOf_isInvertible a
  have hSU : S ⊆ {p | (a.coefficient p).IsInvertible} := fun p hp => hinv p.1 hp.1 p.2 hp.2
  have hinvU := contDiffOn_inverse a
  have hnil : ∃ C, ∀ p ∈ S, ‖iteratedFDerivAlong ℝ (([] : List (Fin n ⊕ Fin n)).map mixedDirection)
      (fun p => (a.coefficient p).inverse) p‖ ≤
      C * (1 + ‖p.2‖ ^ 2) ^ ((-m - (freqLetters ([] : List (Fin n ⊕ Fin n))).length) / 2) := by
    obtain ⟨C, hC⟩ := hC
    exact ⟨C, fun p hp => by simpa [freqLetters] using hC p.1 hp.1 p.2 hp.2⟩
  induction k with
  | zero =>
    intro w hw
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    exact hnil
  | succ k ih =>
    intro w hw
    rcases w.eq_nil_or_concat' with rfl | ⟨w, l, rfl⟩
    · exact hnil
    · -- `∂_l (a⁻¹) = -a⁻¹ (∂_l a) a⁻¹`, a product of factors with known estimates.
      have hda : ContDiffOn ℝ ∞ (iteratedFDerivAlong ℝ [mixedDirection l] a.coefficient) univ :=
        (a.contDiff_coefficient.iteratedFDerivAlong (m := ∞) _ (by simp)).contDiffOn
      have hdab : WordBounds S (m - letterOrder l) k
          (iteratedFDerivAlong ℝ [mixedDirection l] a.coefficient) :=
        (wordBounds_of_mixedDeriv (S := S) a.contDiff_coefficient ha (fun p hp => hp.1)
          (k + 1)).fderiv_apply l
      have h₁ := WordBounds.bilinear (compR W V W) hU hSU (hda.mono (subset_univ _)) hinvU hdab ih
      have hcomp : ContDiffOn ℝ ∞ (fun p => compR W V W
          (iteratedFDerivAlong ℝ [mixedDirection l] a.coefficient p) (a.coefficient p).inverse)
          {p | (a.coefficient p).IsInvertible} :=
        (contDiffOn_const.clm_apply (hda.mono (subset_univ _))).clm_apply hinvU
      have h₂ := WordBounds.bilinear (-compR W W V) hU hSU hinvU hcomp ih h₁
      obtain ⟨C, hC⟩ := h₂ w (by simpa using hw)
      refine ⟨C, fun p hp => ?_⟩
      have heq : iteratedFDerivAlong ℝ ((w ++ [l]).map mixedDirection)
            (fun p => (a.coefficient p).inverse) p =
          iteratedFDerivAlong ℝ (w.map mixedDirection) (fun q => (-compR W W V)
            (a.coefficient q).inverse (compR W V W
              (iteratedFDerivAlong ℝ [mixedDirection l] a.coefficient q)
              (a.coefficient q).inverse)) p := by
        rw [List.map_append, iteratedFDerivAlong_append, List.map_singleton]
        refine (Filter.EventuallyEq.iteratedFDerivAlong ?_ _).eq_of_nhds
        filter_upwards [hU.mem_nhds (hSU hp)] with q hq
        simp only [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil]
        rw [(a.contDiff_coefficient.differentiable (by simp) q).fderiv_clm_inverse hq]
        simp
      have e : -m + (m - letterOrder l + -m) - (freqLetters w).length =
          -m - (freqLetters (w ++ [l])).length := by
        rw [length_freqLetters_append_singleton]
        ring
      rw [heq, ← e]
      exact hC p hp

end Inverse

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- The cut-off inverse is smooth: it vanishes near the points with `‖ξ / R‖ < 1`, and elsewhere
the symbol is invertible. -/
private theorem contDiff_cutoffInverse (a : Symbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) :
    ContDiff ℝ ∞ fun p => χ (R⁻¹ • p.2) • (a.coefficient p).inverse := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : ‖R⁻¹ • p.2‖ < 1
  · exact contDiffAt_const.congr_of_eventuallyEq
      (χ.comp_inv_smul_snd_smul_eventuallyEq_zero R (fun p => (a.coefficient p).inverse) hp)
  · have hq : (a.coefficient p).IsInvertible :=
      hinv p.1 p.2 (abs_le_norm_of_one_le_norm_inv_smul (not_lt.1 hp))
    exact (χ.contDiff_comp_inv_smul_snd R).contDiffAt.smul
      (a.contDiff_coefficient.contDiffAt.clm_inverse hq)

/-- The estimates of the cut-off inverse at the positions of a set `T`, from those of the symbol
and of its inverse there. -/
private theorem exists_bound_cutoffInverse (a : Symbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) {T : Set (CoordinateSpace n)}
    (ha : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hC : ∃ C, ∀ x ∈ T, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (R⁻¹ • p.2) • (a.coefficient p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  have hSU : {p : CoordinateSpace n × CoordinateSpace n | p.1 ∈ T ∧ |R| ≤ ‖p.2‖} ⊆
      {p | (a.coefficient p).IsInvertible} := fun p hp => hinv p.1 p.2 hp.2
  have hb := WordBounds.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (isOpen_setOf_isInvertible a)
    hSU (χ.contDiff_comp_inv_smul_snd R).contDiffOn (contDiffOn_inverse a)
    (wordBounds_cutoff χ R _ (α.map Sum.inl ++ β.map Sum.inr).length)
    (wordBounds_inverse a ha (fun x _ ξ hξ => hinv x ξ hξ) hC _)
  obtain ⟨C, hC⟩ := hb _ le_rfl
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
  rw [mixedDeriv_eq_iteratedFDerivAlong α β
    ((contDiff_cutoffInverse a χ R hinv).of_le (by exact_mod_cast le_top))]
  by_cases hξ : ‖R⁻¹ • ξ‖ < 1
  · rw [iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero
      (χ.comp_inv_smul_snd_smul_eventuallyEq_zero R (fun p => (a.coefficient p).inverse)
        (p := (x, ξ)) hξ), norm_zero]
    positivity
  · have h := hC (x, ξ) ⟨hx, abs_le_norm_of_one_le_norm_inv_smul (not_lt.1 hξ)⟩
    simp only [ContinuousLinearMap.lsmul_apply, zero_add, List.map_append, List.map_map,
      Function.comp_def, mixedDirection_inl, mixedDirection_inr, ← mixedDirections_def] at h
    have hβ : freqLetters (α.map Sum.inl ++ β.map Sum.inr) = β := by
      simp [freqLetters, Function.comp_def]
    rw [hβ] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- The cut-off inverse `χ(ξ / R) a(x, ξ)⁻¹` of a symbol `a` of order `m` that is invertible at
all frequencies `|R| ≤ ‖ξ‖`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there for a constant `C` depending on
a compact set of positions. It is a symbol of order `-m`, inverse to `a` wherever `χ(ξ / R) = 1`.
-/
def cutoffInverse (a : Symbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    Symbol n W V (-m) where
  coefficient p := χ (R⁻¹ • p.2) • (a.coefficient p).inverse
  contDiff_coefficient := contDiff_cutoffInverse a χ R hinv
  exists_bound K hK := exists_bound_cutoffInverse a χ R hinv
    (fun α β => (a.exists_bound K hK α β).imp fun _ h => h.2) (hbound K hK)

variable (a : Symbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
  (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))

@[simp]
theorem coefficient_cutoffInverse (p : CoordinateSpace n × CoordinateSpace n) :
    (a.cutoffInverse χ R hinv hbound).coefficient p =
      χ (R⁻¹ • p.2) • (a.coefficient p).inverse := (rfl)

/-- The symbol composed with its cut-off inverse is the cutoff `χ(ξ / R)` times the identity. -/
theorem coefficient_comp_coefficient_cutoffInverse (x ξ : CoordinateSpace n) :
    (a.coefficient (x, ξ)).comp ((a.cutoffInverse χ R hinv hbound).coefficient (x, ξ)) =
      χ (R⁻¹ • ξ) • ContinuousLinearMap.id ℂ W := by
  rcases le_or_gt ‖R⁻¹ • ξ‖ 1 with hξ | hξ
  · simp [χ.apply_eq_zero_of_norm_le_one hξ]
  · simp [(hinv x ξ (abs_le_norm_of_one_le_norm_inv_smul hξ.le)).self_comp_inverse]

/-- The cut-off inverse composed with the symbol is the cutoff `χ(ξ / R)` times the identity. -/
theorem coefficient_cutoffInverse_comp_coefficient (x ξ : CoordinateSpace n) :
    ((a.cutoffInverse χ R hinv hbound).coefficient (x, ξ)).comp (a.coefficient (x, ξ)) =
      χ (R⁻¹ • ξ) • ContinuousLinearMap.id ℂ V := by
  rcases le_or_gt ‖R⁻¹ • ξ‖ 1 with hξ | hξ
  · simp [χ.apply_eq_zero_of_norm_le_one hξ]
  · simp [(hinv x ξ (abs_le_norm_of_one_le_norm_inv_smul hξ.le)).inverse_comp_self]

/-- For a nonzero radius `R`, at frequencies `‖ξ‖ ≥ 2 |R|` the cut-off inverse is the pointwise
inverse of the symbol. -/
theorem coefficient_cutoffInverse_of_two_mul_abs_le (hR : R ≠ 0) {ξ : CoordinateSpace n}
    (hξ : 2 * |R| ≤ ‖ξ‖) (x : CoordinateSpace n) :
    (a.cutoffInverse χ R hinv hbound).coefficient (x, ξ) = (a.coefficient (x, ξ)).inverse := by
  have h : 2 ≤ ‖R⁻¹ • ξ‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, le_inv_mul_iff₀ (abs_pos.2 hR)]
    linarith
  simp [χ.apply_eq_one_of_two_le_norm h]

/-- If the symbol satisfies uniform estimates and its inverse satisfies the order `-m` bound with
a constant independent of the position, the cut-off inverse satisfies uniform estimates. -/
theorem IsUniform.cutoffInverse {a : Symbol n V W m} (ha : a.IsUniform)
    (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hC : ∃ C, ∀ x ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    (a.cutoffInverse χ R hinv hbound).IsUniform := by
  rw [isUniform_iff]
  intro α β
  obtain ⟨C, hC0, hC'⟩ := exists_bound_cutoffInverse a χ R hinv (T := univ)
    (fun α β => (isUniform_iff.1 ha α β).imp fun _ h x _ ξ => h.2 x ξ)
    (hC.imp fun _ h x _ ξ hξ => h x ξ hξ) α β
  exact ⟨C, hC0, fun x ξ => hC' x (mem_univ x) ξ⟩

end Symbol

end TauCeti
