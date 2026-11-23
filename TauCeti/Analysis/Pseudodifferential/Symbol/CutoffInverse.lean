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
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

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

The same estimates invert a symbol on any set `S` of points `(x, ξ)` on which it is elliptic
(`TauCeti.Symbol.IsEllipticOn`: invertible, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for positions in
each compact set). Ellipticity on `S` passes to the closure of `S`
(`TauCeti.Symbol.IsEllipticOn.closure`), and for a symbol `r` of order `μ` vanishing outside `S`,
the products `r(x, ξ) a(x, ξ)⁻¹` and `a(x, ξ)⁻¹ r(x, ξ)` are symbols of order `μ - m`
(`TauCeti.Symbol.compInverse`, `TauCeti.Symbol.inverseComp`), with `(r a⁻¹) a = r` and
`a (a⁻¹ r) = r` at every point. These are the inverses used for microlocal parametrices, where `a`
is only elliptic on a conic set of frequencies.

If `a(x, ξ)` is invertible at every point, with the same inverse bound at large frequencies, no
cutoff is needed: the inverse bound extends to the remaining compact set of frequencies by
continuity, and the same estimates make the pointwise inverse `a(x, ξ)⁻¹` itself a symbol of order
`-m` (`TauCeti.Symbol.inverse`), such as `(1 + ⟨ξ⟩)⁻¹` of order `-1`.

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
      rw [one_add_norm_sq_rpow_add]
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

/-- The rescaled cutoff `χ(ξ / R)` vanishes at the frequencies `‖ξ‖ < |R|`. -/
private theorem cutoff_eq_zero_of_norm_lt_abs {ξ : CoordinateSpace n} (h : ‖ξ‖ < |R|) :
    χ (R⁻¹ • ξ) = 0 :=
  χ.apply_eq_zero_of_norm_le_one <| le_of_not_gt fun h' =>
    (h.trans_le (abs_le_norm_of_one_le_norm_inv_smul h'.le)).false

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

/-- The pointwise inverse of a symbol of order `m`, on a set `S` of points with position in `T`,
satisfies the estimates of order `-m` along all words, provided the inverse exists on `S` and
satisfies the estimate of order `-m` itself there. -/
private theorem wordBounds_inverse (a : Symbol n V W m) {T : Set (CoordinateSpace n)}
    {S : Set (CoordinateSpace n × CoordinateSpace n)} (hST : ∀ p ∈ S, p.1 ∈ T)
    (ha : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hinv : ∀ p ∈ S, (a.coefficient p).IsInvertible)
    (hC : ∃ C, ∀ p ∈ S, ‖(a.coefficient p).inverse‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (-m / 2)) (k : ℕ) :
    WordBounds S (-m) k fun p => (a.coefficient p).inverse := by
  have hU := isOpen_setOf_isInvertible a
  have hSU : S ⊆ {p | (a.coefficient p).IsInvertible} := hinv
  have hinvU := contDiffOn_inverse a
  have hnil : ∃ C, ∀ p ∈ S, ‖iteratedFDerivAlong ℝ (([] : List (Fin n ⊕ Fin n)).map mixedDirection)
      (fun p => (a.coefficient p).inverse) p‖ ≤
      C * (1 + ‖p.2‖ ^ 2) ^ ((-m - (freqLetters ([] : List (Fin n ⊕ Fin n))).length) / 2) := by
    obtain ⟨C, hC⟩ := hC
    exact ⟨C, fun p hp => by simpa [freqLetters] using hC p hp⟩
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
        (wordBounds_of_mixedDeriv (S := S) a.contDiff_coefficient ha hST (k + 1)).fderiv_apply l
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

section ClosedSet

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] (B : F →L[ℝ] (W →L[ℂ] V) →L[ℝ] G) (a : Symbol n V W m)
  {S : Set (CoordinateSpace n × CoordinateSpace n)} {f : CoordinateSpace n × CoordinateSpace n → F}

/-- A bilinear expression `B (f p) a(p)⁻¹` is smooth if `f` is smooth and vanishes outside a closed
set on which `a` is invertible. -/
private theorem contDiff_bilinear_inverse (hf : ContDiff ℝ ∞ f) (hS : IsClosed S)
    (hfS : ∀ p ∉ S, f p = 0) (hinv : ∀ p ∈ S, (a.coefficient p).IsInvertible) :
    ContDiff ℝ ∞ fun p => B (f p) (a.coefficient p).inverse := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  by_cases hp : p ∈ S
  · exact (contDiffAt_const.clm_apply hf.contDiffAt).clm_apply
      (a.contDiff_coefficient.contDiffAt.clm_inverse (hinv p hp))
  · refine (contDiffAt_const (c := (0 : G))).congr_of_eventuallyEq ?_
    filter_upwards [hS.isOpen_compl.mem_nhds hp] with q hq
    simp [hfS q hq]

/-- The estimates of `B (f p) a(p)⁻¹` at the positions of a set `T`, from the estimates of order
`μ` of `f` and of order `m` of `a` there, if `f` vanishes outside a closed set `S` on which `a` is
invertible, with `‖a(p)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` at the points of `S` with position in `T`. -/
private theorem exists_bound_bilinear_inverse {μ : ℝ} (hf : ContDiff ℝ ∞ f) (hS : IsClosed S)
    (hfS : ∀ p ∉ S, f p = 0) (hinv : ∀ p ∈ S, (a.coefficient p).IsInvertible)
    {T : Set (CoordinateSpace n)} (hfT : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((μ - β.length) / 2))
    (haT : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (hC : ∃ C, ∀ p ∈ S, p.1 ∈ T →
      ‖(a.coefficient p).inverse‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (-m / 2)) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ T, ∀ ξ,
      ‖mixedDeriv α β (fun p => B (f p) (a.coefficient p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((μ + -m - β.length) / 2) := by
  -- The estimates along words on the points of `S` with position in `T`, by the Leibniz rule.
  let ST : Set (CoordinateSpace n × CoordinateSpace n) := {p | p ∈ S ∧ p.1 ∈ T}
  have hinvST (p) (hp : p ∈ ST) : (a.coefficient p).IsInvertible := hinv p hp.1
  have hb := WordBounds.bilinear B (isOpen_setOf_isInvertible a) hinvST hf.contDiffOn
    (contDiffOn_inverse a) (wordBounds_of_mixedDeriv hf hfT (fun _ (hp : _ ∈ ST) => hp.2) _)
    (wordBounds_inverse a (fun _ (hp : _ ∈ ST) => hp.2) haT hinvST
      (hC.imp fun _ h p (hp : p ∈ ST) => h p hp.1 hp.2) (α.map Sum.inl ++ β.map Sum.inr).length)
  obtain ⟨C, hC⟩ := hb _ le_rfl
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
  rw [mixedDeriv_eq_iteratedFDerivAlong α β ((contDiff_bilinear_inverse B a hf hS hfS
    hinv).of_le (by exact_mod_cast le_top))]
  by_cases hp : (x, ξ) ∈ S
  · have h := hC (x, ξ) ⟨hp, hx⟩
    simp only [List.map_append, List.map_map, Function.comp_def, mixedDirection_inl,
      mixedDirection_inr, ← mixedDirections_def] at h
    have hβ : freqLetters (α.map Sum.inl ++ β.map Sum.inr) = β := by
      simp [freqLetters, Function.comp_def]
    rw [hβ] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · rw [iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero, norm_zero]
    · positivity
    filter_upwards [hS.isOpen_compl.mem_nhds hp] with q hq
    simp [hfS q hq]

end ClosedSet

/-- The cut-off inverse is smooth: it vanishes outside the closed set of frequencies
`|R| ≤ ‖ξ‖`, on which the symbol is invertible. -/
private theorem contDiff_cutoffInverse (a : Symbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)
    (hinv : ∀ x ξ, |R| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible) :
    ContDiff ℝ ∞ fun p => χ (R⁻¹ • p.2) • (a.coefficient p).inverse := by
  simpa only [ContinuousLinearMap.lsmul_apply] using
    contDiff_bilinear_inverse (ContinuousLinearMap.lsmul ℝ ℝ) a (S := {p | |R| ≤ ‖p.2‖})
      (χ.contDiff_comp_inv_smul_snd R) (isClosed_le continuous_const continuous_snd.norm)
      (fun p hp => cutoff_eq_zero_of_norm_lt_abs χ R (not_le.1 hp)) fun p hp => hinv p.1 p.2 hp

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
  simpa only [ContinuousLinearMap.lsmul_apply, zero_add] using
    exists_bound_bilinear_inverse (ContinuousLinearMap.lsmul ℝ ℝ) a (S := {p | |R| ≤ ‖p.2‖})
      (μ := 0) (χ.contDiff_comp_inv_smul_snd R) (isClosed_le continuous_const continuous_snd.norm)
      (fun p hp => cutoff_eq_zero_of_norm_lt_abs χ R (not_le.1 hp)) (fun p hp => hinv p.1 p.2 hp)
      (fun α β => (χ.exists_bound_mixedDeriv_comp_inv_smul_snd R α β).imp fun _ h x _ ξ => h x ξ)
      ha (hC.imp fun _ h p hp hpT => h p.1 hpT p.2 hp) α β

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

/-! ### The inverse of a symbol that is invertible everywhere -/

section Inverse

private theorem contDiff_inverse (a : Symbol n V W m) (hinv : ∀ p, (a.coefficient p).IsInvertible) :
    ContDiff ℝ ∞ fun p => (a.coefficient p).inverse :=
  contDiff_iff_contDiffAt.2 fun p => a.contDiff_coefficient.contDiffAt.clm_inverse (hinv p)

/-- The estimates of the pointwise inverse of a symbol that is invertible at every point, at the
positions of a compact set. On the compact set `K × closedBall 0 |R|` the continuous inverse is
bounded, so the inverse bound at frequencies `|R| ≤ ‖ξ‖` extends to all frequencies. -/
private theorem exists_bound_inverse (a : Symbol n V W m)
    (hinv : ∀ p, (a.coefficient p).IsInvertible) (R : ℝ) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K)
    (hC : ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => (a.coefficient p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  obtain ⟨C, hC⟩ := hC
  have hw : Continuous fun p : CoordinateSpace n × CoordinateSpace n =>
      (1 + ‖p.2‖ ^ 2) ^ (-m / 2) :=
    (continuous_const.add ((continuous_norm.comp continuous_snd).pow 2)).rpow_const
      fun p => Or.inl (by positivity : (0 : ℝ) < 1 + ‖p.2‖ ^ 2).ne'
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_closedBall 0 |R|)).exists_bound_of_continuousOn
    ((contDiff_inverse a hinv).continuous.norm.div hw fun p => (by positivity : 0 <
      (1 + ‖p.2‖ ^ 2) ^ (-m / 2)).ne').continuousOn
  have hC' : ∃ C, ∀ p ∈ (univ : Set (CoordinateSpace n × CoordinateSpace n)), p.1 ∈ K →
      ‖(a.coefficient p).inverse‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (-m / 2) := by
    refine ⟨max C M, fun ⟨x, ξ⟩ _ hx => ?_⟩
    have hw0 : 0 < (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by positivity
    rcases le_total |R| ‖ξ‖ with hξ | hξ
    · exact (hC x hx ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le)
    · have h := hM (x, ξ) ⟨hx, mem_closedBall_zero_iff.2 hξ⟩
      rw [Pi.div_apply, Real.norm_of_nonneg (by positivity), div_le_iff₀ hw0] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw0.le)
  let e : Symbol n W W 0 := const (.id ℂ W)
  simpa only [e, coefficient_const, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_id, zero_add] using
    exists_bound_bilinear_inverse (compR W W V).flip a e.contDiff_coefficient
      isClosed_univ (fun p hp => absurd (mem_univ p) hp) (fun p _ => hinv p)
      (fun α β => (e.exists_bound K hK α β).imp fun _ h => h.2)
      (fun α β => (a.exists_bound K hK α β).imp fun _ h => h.2) hC' α β

/-- The pointwise inverse `a(x, ξ)⁻¹` of a symbol `a` of order `m` that is invertible at every
point, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` at the frequencies `|R| ≤ ‖ξ‖` for a constant `C` depending
on a compact set of positions. It is a symbol of order `-m`, a two-sided inverse of `a` at every
point (`TauCeti.Symbol.coefficient_comp_coefficient_inverse`,
`TauCeti.Symbol.coefficient_inverse_comp_coefficient`). Its hypotheses are those of
`TauCeti.Symbol.cutoffInverse` together with invertibility at low frequencies, and it involves no
cutoff. -/
def inverse (a : Symbol n V W m) (hinv : ∀ p, (a.coefficient p).IsInvertible) (R : ℝ)
    (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    Symbol n W V (-m) where
  coefficient p := (a.coefficient p).inverse
  contDiff_coefficient := contDiff_inverse a hinv
  exists_bound _ hK := exists_bound_inverse a hinv R hK (hbound _ hK)

variable (a : Symbol n V W m) (hinv : ∀ p, (a.coefficient p).IsInvertible) (R : ℝ)
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |R| ≤ ‖ξ‖ →
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))

@[simp]
theorem coefficient_inverse (p : CoordinateSpace n × CoordinateSpace n) :
    (a.inverse hinv R hbound).coefficient p = (a.coefficient p).inverse := (rfl)

/-- The symbol composed with its inverse is the identity at every point. -/
theorem coefficient_comp_coefficient_inverse (p : CoordinateSpace n × CoordinateSpace n) :
    (a.coefficient p).comp ((a.inverse hinv R hbound).coefficient p) =
      ContinuousLinearMap.id ℂ W :=
  (hinv p).self_comp_inverse

/-- The inverse composed with the symbol is the identity at every point. -/
theorem coefficient_inverse_comp_coefficient (p : CoordinateSpace n × CoordinateSpace n) :
    ((a.inverse hinv R hbound).coefficient p).comp (a.coefficient p) =
      ContinuousLinearMap.id ℂ V :=
  (hinv p).inverse_comp_self

end Inverse

/-! ### Inverses on a set of points

A symbol `a` need not be invertible at all large frequencies to be inverted where it matters. If
`a` is elliptic on a set `S` of points `(x, ξ)`, invertible there with the inverse bound of order
`-m`, then it is elliptic on the closure of `S` (`TauCeti.Symbol.IsEllipticOn.closure`), and
composing a symbol `r` that vanishes outside `S` with the pointwise inverse of `a`, on either side,
gives a symbol (`TauCeti.Symbol.compInverse`, `TauCeti.Symbol.inverseComp`): `r a⁻¹` and `a⁻¹ r`
vanish near every point outside the closure of `S`, and are smooth near every point of the closure
since invertibility is an open condition. These are the inverses from which microlocal parametrices
are built, `S` being a conic set of large frequencies over a compact set of positions. -/

omit [CompleteSpace V] in
/-- A symbol `a` of order `m` is *elliptic on* a set `S` of points `(x, ξ)` if its value `a(x, ξ)`
is invertible at every point of `S`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` at the points of `S` whose
position lies in a compact set `K`, for a constant `C` depending on `K`. -/
def IsEllipticOn (a : Symbol n V W m) (S : Set (CoordinateSpace n × CoordinateSpace n)) : Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ p ∈ S, p.1 ∈ K →
    (a.coefficient p).IsInvertible ∧ ‖(a.coefficient p).inverse‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (-m / 2)

variable {S : Set (CoordinateSpace n × CoordinateSpace n)}

omit [CompleteSpace V] in
theorem isEllipticOn_iff {a : Symbol n V W m} :
    a.IsEllipticOn S ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ p ∈ S, p.1 ∈ K →
      (a.coefficient p).IsInvertible ∧
        ‖(a.coefficient p).inverse‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (-m / 2) :=
  Iff.rfl

omit [CompleteSpace V] in
/-- The value of a symbol elliptic on `S` is invertible at every point of `S`. -/
theorem IsEllipticOn.isInvertible {a : Symbol n V W m} (ha : a.IsEllipticOn S) {p}
    (hp : p ∈ S) : (a.coefficient p).IsInvertible := by
  obtain ⟨C, hC⟩ := ha {p.1} isCompact_singleton
  exact (hC p hp rfl).1

omit [CompleteSpace V] in
/-- A symbol elliptic on a set is elliptic on every subset. -/
theorem IsEllipticOn.mono {a : Symbol n V W m} (ha : a.IsEllipticOn S)
    {S' : Set (CoordinateSpace n × CoordinateSpace n)} (h : S' ⊆ S) : a.IsEllipticOn S' :=
  fun K hK => (ha K hK).imp fun _ hC p hp hpK => hC p (h hp) hpK

/-- **Ellipticity passes to the closure.** A symbol elliptic on a set `S` is elliptic on its
closure: near a limit point `p` of `S`, the values of `a` are invertible with inverses bounded by a
multiple of `⟨ξ⟩^(-m)`, so `a(p)` is a small perturbation of such a value. -/
theorem IsEllipticOn.closure {a : Symbol n V W m} (ha : a.IsEllipticOn S) :
    a.IsEllipticOn (closure S) := by
  intro K hK
  obtain ⟨C, hC⟩ := ha _ (hK.cthickening (r := 1))
  refine ⟨4 * C, fun p hp hpK => ?_⟩
  -- The weight `⟨ξ⟩^(-m)`, continuous and positive.
  set w : CoordinateSpace n × CoordinateSpace n → ℝ := fun q => (1 + ‖q.2‖ ^ 2) ^ (-m / 2)
  have hw : Continuous w :=
    (continuous_const.add (continuous_snd.norm.pow 2)).rpow_const fun q =>
      Or.inl (by positivity : (1 : ℝ) + ‖q.2‖ ^ 2 ≠ 0)
  have hwpos (q : CoordinateSpace n × CoordinateSpace n) : 0 < w q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hwp := hwpos p
  -- A point `q` of `S` near `p`, at which `‖a(q)⁻¹‖ ≤ C w(q) ≤ 2 C w(p)`.
  have h₁ : ∀ᶠ q in 𝓝 p, dist q.1 p.1 < 1 :=
    (continuous_fst.dist continuous_const).continuousAt.eventually_lt continuousAt_const
      (by simp)
  have h₂ : ∀ᶠ q in 𝓝 p, w q < 2 * w p :=
    hw.continuousAt.eventually_lt continuousAt_const (by linarith)
  have h₃ : ∀ᶠ q in 𝓝 p, |C| * (2 * w p) * ‖a.coefficient p - a.coefficient q‖ < 1 / 2 :=
    (continuous_const.mul (continuous_const.sub a.contDiff_coefficient.continuous).norm
      ).continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨q, ⟨hq₁, hq₂, hq₃⟩, hqS⟩ := mem_closure_iff_nhds.1 hp _ (h₁.and (h₂.and h₃))
  obtain ⟨hinv, hbound⟩ := hC q hqS (Metric.mem_cthickening_of_dist_le _ _ _ _ hpK hq₁.le)
  have hwq := hwpos q
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hbound) hwq
  rw [abs_of_nonneg hC0] at hq₃
  have hM : ‖(a.coefficient q).inverse‖ ≤ C * (2 * w p) :=
    hbound.trans (mul_le_mul_of_nonneg_left hq₂.le hC0)
  have h : C * (2 * w p) * ‖a.coefficient p - a.coefficient q‖ < 1 := by linarith
  refine ⟨hinv.of_mul_norm_sub_lt hM h, (hinv.norm_inverse_le_of_mul_norm_sub_lt hM h).trans ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hC0 hwp.le]

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {μ : ℝ}

/-- The symbol `r(x, ξ) a(x, ξ)⁻¹` of order `μ - m`, for a symbol `r` of order `μ` vanishing
outside a set `S` on which the symbol `a` of order `m` is elliptic. Outside `S` it is `0`. -/
def compInverse (r : Symbol n V U μ) (a : Symbol n V W m) (hr : ∀ p ∉ S, r.coefficient p = 0)
    (ha : a.IsEllipticOn S) : Symbol n W U (μ + -m) where
  coefficient p := (r.coefficient p).comp (a.coefficient p).inverse
  contDiff_coefficient := contDiff_bilinear_inverse (compR W V U) a r.contDiff_coefficient
    isClosed_closure (fun p hp => hr p fun h => hp (subset_closure h))
    fun _ hp => ha.closure.isInvertible hp
  exists_bound K hK := exists_bound_bilinear_inverse (compR W V U) a r.contDiff_coefficient
    isClosed_closure (fun p hp => hr p fun h => hp (subset_closure h))
    (fun _ hp => ha.closure.isInvertible hp)
    (fun α β => (r.exists_bound K hK α β).imp fun _ h => h.2)
    (fun α β => (a.exists_bound K hK α β).imp fun _ h => h.2)
    ((ha.closure K hK).imp fun _ h p hp hpK => (h p hp hpK).2)

/-- The symbol `a(x, ξ)⁻¹ r(x, ξ)` of order `μ - m`, for a symbol `r` of order `μ` vanishing
outside a set `S` on which the symbol `a` of order `m` is elliptic. Outside `S` it is `0`. -/
def inverseComp (a : Symbol n V W m) (r : Symbol n U W μ) (hr : ∀ p ∉ S, r.coefficient p = 0)
    (ha : a.IsEllipticOn S) : Symbol n U V (-m + μ) where
  coefficient p := (a.coefficient p).inverse.comp (r.coefficient p)
  contDiff_coefficient := contDiff_bilinear_inverse (compR U W V).flip a r.contDiff_coefficient
    isClosed_closure (fun p hp => hr p fun h => hp (subset_closure h))
    fun _ hp => ha.closure.isInvertible hp
  exists_bound K hK := by
    obtain h := exists_bound_bilinear_inverse (compR U W V).flip a r.contDiff_coefficient
      isClosed_closure (fun p hp => hr p fun h => hp (subset_closure h))
      (fun _ hp => ha.closure.isInvertible hp)
      (fun α β => (r.exists_bound K hK α β).imp fun _ h => h.2)
      (fun α β => (a.exists_bound K hK α β).imp fun _ h => h.2)
      ((ha.closure K hK).imp fun _ h p hp hpK => (h p hp hpK).2)
    exact fun α β => (h α β).imp fun _ ⟨hC0, hC⟩ => ⟨hC0, fun x hx ξ => by
      rw [add_comm (-m) μ]
      exact hC x hx ξ⟩

section CompInverse

variable (r : Symbol n V U μ) (a : Symbol n V W m) (hr : ∀ p ∉ S, r.coefficient p = 0)
  (ha : a.IsEllipticOn S)

@[simp]
theorem coefficient_compInverse (p : CoordinateSpace n × CoordinateSpace n) :
    (r.compInverse a hr ha).coefficient p = (r.coefficient p).comp (a.coefficient p).inverse :=
  (rfl)

/-- The composition `r a⁻¹` vanishes outside `S`. -/
theorem coefficient_compInverse_of_notMem {p : CoordinateSpace n × CoordinateSpace n}
    (hp : p ∉ S) : (r.compInverse a hr ha).coefficient p = 0 := by
  simp [hr p hp]

/-- **`r a⁻¹` inverts `a` on the left up to `r`**: `(r a⁻¹) a = r` at every point. -/
theorem coefficient_compInverse_comp_coefficient (p : CoordinateSpace n × CoordinateSpace n) :
    ((r.compInverse a hr ha).coefficient p).comp (a.coefficient p) = r.coefficient p := by
  by_cases hp : p ∈ S
  · simp [ContinuousLinearMap.comp_assoc, (ha.isInvertible hp).inverse_comp_self]
  · simp [hr p hp]

end CompInverse

section InverseComp

variable (a : Symbol n V W m) (r : Symbol n U W μ) (hr : ∀ p ∉ S, r.coefficient p = 0)
  (ha : a.IsEllipticOn S)

@[simp]
theorem coefficient_inverseComp (p : CoordinateSpace n × CoordinateSpace n) :
    (a.inverseComp r hr ha).coefficient p = (a.coefficient p).inverse.comp (r.coefficient p) :=
  (rfl)

/-- The composition `a⁻¹ r` vanishes outside `S`. -/
theorem coefficient_inverseComp_of_notMem {p : CoordinateSpace n × CoordinateSpace n}
    (hp : p ∉ S) : (a.inverseComp r hr ha).coefficient p = 0 := by
  simp [hr p hp]

/-- **`a⁻¹ r` inverts `a` on the right up to `r`**: `a (a⁻¹ r) = r` at every point. -/
theorem coefficient_comp_coefficient_inverseComp (p : CoordinateSpace n × CoordinateSpace n) :
    (a.coefficient p).comp ((a.inverseComp r hr ha).coefficient p) = r.coefficient p := by
  by_cases hp : p ∈ S
  · simp [← ContinuousLinearMap.comp_assoc, (ha.isInvertible hp).self_comp_inverse]
  · simp [hr p hp]

end InverseComp

end Symbol

end TauCeti
