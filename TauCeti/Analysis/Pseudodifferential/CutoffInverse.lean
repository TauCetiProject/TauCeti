/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The cut-off inverse of a symbol

Let `a ∈ S^m_{1,0}` be a symbol of order `m` whose values `a(x, ξ) : V →L[ℂ] W` are invertible at
all large frequencies `R ≤ ‖ξ‖`, with the inverse bound `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there (the
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

The derivative estimates rest on the formula `∂(a⁻¹) = -a⁻¹ (∂a) a⁻¹`. Applied repeatedly, it
writes every derivative of `a⁻¹` as a sum of products of `a⁻¹` with derivatives of `a`. Each
product has the order `-m - |β|` by the Leibniz rule. The inverse is only smooth on the open set
where `a` is invertible, so the proof runs an induction on the number of derivatives, using the
iterated directional derivatives `TauCeti.iteratedFDerivAlong` in `ℝⁿ × ℝⁿ` along arbitrary words
of position and frequency directions (`TauCeti.mixedDirection`) and their calculus on open sets.
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
  rw [iteratedFDerivAlong_map_mixedDirection hf]
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

/-- If `‖ξ / R‖ ≥ 1`, then `R ≤ ‖ξ‖`. -/
private theorem le_norm_of_one_le_norm_inv_smul {R : ℝ} {ξ : CoordinateSpace n}
    (h : 1 ≤ ‖R⁻¹ • ξ‖) : R ≤ ‖ξ‖ := by
  rcases le_or_gt R 0 with hR | hR
  · exact hR.trans (norm_nonneg ξ)
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR] at h
    simpa using (le_inv_mul_iff₀ hR).1 h

variable (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)

/-- Multiplying by the rescaled cutoff `χ(ξ / R)` gives a function vanishing near every point
with `‖ξ / R‖ < 1`. -/
private theorem cutoff_smul_eventuallyEq_zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : CoordinateSpace n × CoordinateSpace n → A) {p : CoordinateSpace n × CoordinateSpace n}
    (hp : ‖R⁻¹ • p.2‖ < 1) : (fun q => χ (R⁻¹ • q.2) • f q) =ᶠ[𝓝 p] 0 := by
  have hc : Continuous fun q : CoordinateSpace n × CoordinateSpace n => R⁻¹ • q.2 :=
    continuous_snd.const_smul R⁻¹
  filter_upwards [(χ.eventuallyEq_zero_of_norm_lt_one hp).comp_tendsto hc.continuousAt]
    with q hq
  simp only [Function.comp_apply, Pi.zero_apply] at hq
  simp [hq]

private theorem contDiff_cutoff :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (R⁻¹ • p.2) :=
  χ.contDiff.comp (contDiff_snd.const_smul R⁻¹)

/-- If `k = 0` or `‖ξ / R‖ < 2`, then `|R⁻¹|^k ≤ |R⁻¹|^k ⟨2R⟩^k ⟨ξ⟩^(-k)`: below the radius
`2 |R|` the weight `⟨ξ⟩^(-k)` is bounded below by `⟨2R⟩^(-k)`, and for `R = 0` both sides vanish. -/
private theorem abs_inv_pow_le_mul_weight {R : ℝ} {k : ℕ} {ξ : CoordinateSpace n}
    (h : k = 0 ∨ ‖R⁻¹ • ξ‖ < 2) : |R⁻¹| ^ k ≤ |R⁻¹| ^ k *
      ((1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - k) / 2)) := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  rcases eq_or_ne R 0 with hR | hR
  · simp [hR, zero_pow hk]
  refine le_mul_of_one_le_right (by positivity) ?_
  have hlt := h.resolve_left hk
  rw [norm_smul, norm_inv, Real.norm_eq_abs] at hlt
  have hξ : ‖ξ‖ < 2 * |R| := by
    have := (inv_mul_lt_iff₀ (abs_pos.2 hR)).1 hlt
    linarith
  have h1 : 1 + ‖ξ‖ ^ 2 ≤ 1 + 4 * R ^ 2 := by
    nlinarith [norm_nonneg ξ, sq_abs R, abs_nonneg R]
  have hk0 : ((0 : ℝ) - k) / 2 ≤ 0 := by
    have := k.cast_nonneg (α := ℝ)
    linarith
  calc (1 : ℝ) = (1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) * (1 + 4 * R ^ 2) ^ (((0 : ℝ) - k) / 2) := by
        rw [← Real.rpow_add (by positivity), show (k : ℝ) / 2 + (0 - k) / 2 = 0 by ring,
          Real.rpow_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) h1 hk0)
        (by positivity)

/-- The rescaled cutoff `χ(ξ / R)` satisfies the symbol estimates of order `0`. -/
private theorem exists_bound_mixedDeriv_cutoff (α β : List (Fin n)) :
    ∃ C, ∀ x ξ : CoordinateSpace n,
      ‖mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n => χ (R⁻¹ • p.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - β.length) / 2) := by
  rcases eq_or_ne α [] with rfl | hα
  swap
  · refine ⟨0, fun x ξ => ?_⟩
    simp only [mixedDeriv_def]
    rw [coordinateDeriv_const _ hα]
    simp
  obtain ⟨B, hB⟩ := χ.exists_bound_iteratedFDeriv β.length
  have hval : ∀ x ξ, ‖mixedDeriv [] β (fun p : CoordinateSpace n × CoordinateSpace n =>
      χ (R⁻¹ • p.2)) x ξ‖ ≤ |R⁻¹| ^ β.length * ‖iteratedFDeriv ℝ β.length χ (R⁻¹ • ξ)‖ := by
    intro x ξ
    have hk : ContDiff ℝ β.length χ := χ.contDiff.of_le (by exact_mod_cast le_top)
    have hk' : ContDiff ℝ β.length fun z => χ (R⁻¹ • z) := hk.comp (contDiff_const_smul R⁻¹)
    simp only [mixedDeriv_def, coordinateDeriv_nil]
    refine (norm_coordinateDeriv_le β hk' ξ).trans ?_
    rw [iteratedFDeriv_comp_const_smul R⁻¹ hk, norm_smul, norm_pow, Real.norm_eq_abs]
  set k := β.length
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨|R⁻¹| ^ k * B * (1 + 4 * R ^ 2) ^ ((k : ℝ) / 2), fun x ξ => (hval x ξ).trans ?_⟩
  by_cases hz : k ≠ 0 ∧ 2 ≤ ‖R⁻¹ • ξ‖
  · rw [χ.iteratedFDeriv_eq_zero_of_two_le_norm hz.1 hz.2, norm_zero, mul_zero]
    positivity
  have key := abs_inv_pow_le_mul_weight ((not_and_or.1 hz).imp not_not.1 not_le.1)
  calc |R⁻¹| ^ k * ‖iteratedFDeriv ℝ k χ (R⁻¹ • ξ)‖ ≤ |R⁻¹| ^ k * B :=
        mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ ≤ |R⁻¹| ^ k * ((1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) *
          (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - k) / 2)) * B := mul_le_mul_of_nonneg_right key hB0
    _ = _ := by ring

private theorem wordBounds_cutoff (S : Set (CoordinateSpace n × CoordinateSpace n)) (k : ℕ) :
    WordBounds S 0 k fun p => χ (R⁻¹ • p.2) :=
  wordBounds_of_mixedDeriv (contDiff_cutoff χ R) (T := univ)
    (fun α β => (exists_bound_mixedDeriv_cutoff χ R α β).imp fun _ h x _ ξ => h x ξ)
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
  fun p hp => ((hp.contDiffAt_map_inverse (𝕜 := ℂ)).restrict_scalars ℝ |>.comp p
    a.contDiff_coefficient.contDiffAt).contDiffWithinAt

/-- The derivative of the pointwise inverse: `∂(a⁻¹) = -a⁻¹ (∂a) a⁻¹`. -/
private theorem fderiv_inverse_apply (a : Symbol n V W m)
    {q : CoordinateSpace n × CoordinateSpace n}
    (hq : (a.coefficient q).IsInvertible) (v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p => (a.coefficient p).inverse) q v =
      -((a.coefficient q).inverse.comp ((fderiv ℝ a.coefficient q v).comp
        (a.coefficient q).inverse)) := by
  have hU := (isOpen_setOf_isInvertible a).mem_nhds hq
  have hev : (fun p => compR W V W (a.coefficient p) (a.coefficient p).inverse) =ᶠ[𝓝 q]
      fun _ => ContinuousLinearMap.id ℂ W := by
    filter_upwards [hU] with p hp
    exact hp.self_comp_inverse
  have h0 := congrArg (fun L => L v) (hev.fderiv_eq (𝕜 := ℝ))
  rw [(compR W V W).fderiv_of_bilinear (a.contDiff_coefficient.differentiable (by simp) q)
    (((contDiffOn_inverse a).differentiableOn (by simp)).differentiableAt hU)] at h0
  have h1 : (a.coefficient q).comp (fderiv ℝ (fun p => (a.coefficient p).inverse) q v) =
      -((fderiv ℝ a.coefficient q v).comp (a.coefficient q).inverse) :=
    eq_neg_of_add_eq_zero_left (by simpa using h0)
  calc fderiv ℝ (fun p => (a.coefficient p).inverse) q v =
        ((a.coefficient q).inverse.comp (a.coefficient q)).comp
          (fderiv ℝ (fun p => (a.coefficient p).inverse) q v) := by
        rw [hq.inverse_comp_self, ContinuousLinearMap.id_comp]
    _ = _ := by
        rw [ContinuousLinearMap.comp_assoc, h1, ContinuousLinearMap.comp_neg]

/-- The pointwise inverse of a symbol of order `m`, at the points of large frequency with position
in `T`, satisfies the estimates of order `-m` along all words, provided the inverse exists there
and satisfies the estimate of order `-m` itself. -/
private theorem wordBounds_inverse (a : Symbol n V W m) {T : Set (CoordinateSpace n)} {R : ℝ}
    (ha : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hinv : ∀ x ∈ T, ∀ ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hC : ∃ C, ∀ x ∈ T, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) (k : ℕ) :
    WordBounds {p | p.1 ∈ T ∧ R ≤ ‖p.2‖} (-m) k fun p => (a.coefficient p).inverse := by
  set S : Set (CoordinateSpace n × CoordinateSpace n) := {p | p.1 ∈ T ∧ R ≤ ‖p.2‖}
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
        rw [fderiv_inverse_apply a hq]
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
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) :
    ContDiff ℝ ∞ fun p => χ (R⁻¹ • p.2) • (a.coefficient p).inverse := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : ‖R⁻¹ • p.2‖ < 1
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cutoff_smul_eventuallyEq_zero χ R (fun p => (a.coefficient p).inverse) hp)
  · have hq : (a.coefficient p).IsInvertible :=
      hinv p.1 p.2 (le_norm_of_one_le_norm_inv_smul (not_lt.1 hp))
    exact (contDiff_cutoff χ R).contDiffAt.smul
      ((contDiffOn_inverse a).contDiffAt ((isOpen_setOf_isInvertible a).mem_nhds hq))

/-- The estimates of the cut-off inverse at the positions of a set `T`, from those of the symbol
and of its inverse there. -/
private theorem exists_bound_cutoffInverse (a : Symbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) {T : Set (CoordinateSpace n)}
    (ha : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hC : ∃ C, ∀ x ∈ T, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (R⁻¹ • p.2) • (a.coefficient p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  have hSU : {p : CoordinateSpace n × CoordinateSpace n | p.1 ∈ T ∧ R ≤ ‖p.2‖} ⊆
      {p | (a.coefficient p).IsInvertible} := fun p hp => hinv p.1 p.2 hp.2
  have hb := WordBounds.bilinear (ContinuousLinearMap.lsmul ℝ ℝ) (isOpen_setOf_isInvertible a)
    hSU (contDiff_cutoff χ R).contDiffOn (contDiffOn_inverse a)
    (wordBounds_cutoff χ R _ (α.map Sum.inl ++ β.map Sum.inr).length)
    (wordBounds_inverse a ha (fun x _ ξ hξ => hinv x ξ hξ) hC _)
  obtain ⟨C, hC⟩ := hb _ le_rfl
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
  rw [mixedDeriv_eq_iteratedFDerivAlong (contDiff_cutoffInverse a χ R hinv)]
  by_cases hξ : ‖R⁻¹ • ξ‖ < 1
  · rw [iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero (cutoff_smul_eventuallyEq_zero χ R
      (fun p => (a.coefficient p).inverse) (p := (x, ξ)) hξ), norm_zero]
    positivity
  · have h := hC (x, ξ) ⟨hx, le_norm_of_one_le_norm_inv_smul (not_lt.1 hξ)⟩
    simp only [ContinuousLinearMap.lsmul_apply, zero_add] at h
    have hβ : freqLetters (α.map Sum.inl ++ β.map Sum.inr) = β := by
      simp [freqLetters, Function.comp_def]
    rw [hβ] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- The cut-off inverse `χ(ξ / R) a(x, ξ)⁻¹` of a symbol `a` of order `m` that is invertible at
all frequencies `R ≤ ‖ξ‖`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there for a constant `C` depending on
a compact set of positions. It is a symbol of order `-m`, inverse to `a` wherever `χ(ξ / R) = 1`.
-/
def cutoffInverse (a : Symbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    Symbol n W V (-m) where
  coefficient p := χ (R⁻¹ • p.2) • (a.coefficient p).inverse
  contDiff_coefficient := contDiff_cutoffInverse a χ R hinv
  exists_bound K hK := exists_bound_cutoffInverse a χ R hinv
    (fun α β => (a.exists_bound K hK α β).imp fun _ h => h.2) (hbound K hK)

variable (a : Symbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
  (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))

@[simp]
theorem coefficient_cutoffInverse (x ξ : CoordinateSpace n) :
    (a.cutoffInverse χ R hinv hbound).coefficient (x, ξ) =
      χ (R⁻¹ • ξ) • (a.coefficient (x, ξ)).inverse := (rfl)

/-- The symbol composed with its cut-off inverse is the cutoff `χ(ξ / R)` times the identity. -/
theorem coefficient_comp_coefficient_cutoffInverse (x ξ : CoordinateSpace n) :
    (a.coefficient (x, ξ)).comp ((a.cutoffInverse χ R hinv hbound).coefficient (x, ξ)) =
      χ (R⁻¹ • ξ) • ContinuousLinearMap.id ℂ W := by
  rcases le_or_gt ‖R⁻¹ • ξ‖ 1 with hξ | hξ
  · simp [χ.apply_eq_zero_of_norm_le_one hξ]
  · simp [(hinv x ξ (le_norm_of_one_le_norm_inv_smul hξ.le)).self_comp_inverse]

/-- The cut-off inverse composed with the symbol is the cutoff `χ(ξ / R)` times the identity. -/
theorem coefficient_cutoffInverse_comp_coefficient (x ξ : CoordinateSpace n) :
    ((a.cutoffInverse χ R hinv hbound).coefficient (x, ξ)).comp (a.coefficient (x, ξ)) =
      χ (R⁻¹ • ξ) • ContinuousLinearMap.id ℂ V := by
  rcases le_or_gt ‖R⁻¹ • ξ‖ 1 with hξ | hξ
  · simp [χ.apply_eq_zero_of_norm_le_one hξ]
  · simp [(hinv x ξ (le_norm_of_one_le_norm_inv_smul hξ.le)).inverse_comp_self]

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
    (hinv : ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hC : ∃ C, ∀ x ξ, R ≤ ‖ξ‖ →
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
