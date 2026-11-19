/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Rapid decay in conic neighbourhoods

Let `Γ` be an open subset of a real normed space which is closed under multiplication by positive
reals, such as an open cone of frequencies in microlocal analysis. Every `ξ ∈ Γ` lies in a smaller
open cone `Γ'` which stays inside `Γ` after perturbations proportional to the size of the
frequency: for some `c > 0`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`.
Take `Γ'` to be the cone over a small ball about `ξ`.

This is the geometric input to the localization of rapid decay in cones. If `F` grows at most
polynomially and decays rapidly on `Γ`, and the coefficients `a i` decay rapidly in `‖v i‖`, then
the superposition `∑ i, a i • F (η - v i)` decays rapidly on `Γ'`: the shifts with
`‖v i‖ ≤ c ‖η‖` evaluate `F` at points of `Γ` of size comparable to `‖η‖`, and the remaining
shifts have `‖v i‖` comparable to `‖η‖`, where the decay of the coefficients wins. Applied to the
Fourier coefficients of a smooth function, this shows that rapid decay of a localized Fourier
transform in a cone survives multiplication of the cutoff by a smooth function.

Rapid decay on a smaller cone also follows from square integrability of every order on `Γ`, for a
function `F` that is Lipschitz with a polynomially growing constant:
`‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`. On the closed ball of radius
`δ = (1 + ‖η‖) ^ (-M)` about `η` the value `F η` is within `A (1 + ‖η‖) ^ (k - M)` of `F`, and
averaging `‖F‖ ^ 2` over that ball, which lies in `Γ` for `η ∈ Γ'`, bounds `‖F η‖ ^ 2` by
`δ ^ (-n) (1 + ‖η‖) ^ (-2 s)` times the weighted `L²` norm of order `s`, plus
`A² (1 + ‖η‖) ^ (2 (k - M))`. For `M` and then `s` large both terms are `O((1 + ‖η‖) ^ (-2 N))`.
Applied to a localized Fourier transform, this turns microlocal `H^s` regularity for every `s` into
microlocal smoothness.

Rapid decay in a cone also survives multiplication by a function of polynomial growth in other
variables: if `g` decays rapidly on a cone around `a ζ₀ ≠ 0`, then `g (a ζ) h (b ζ)` decays rapidly
on the cone of those `ζ` with `a ζ` in that cone and `‖b ζ‖ < c ‖a ζ‖`. This is how the localized
Fourier transform of a tensor product inherits the decay of one of its factors.

In a proper space, if every unit vector lies in an open cone, finitely many of these cones cover
the nonzero vectors, by compactness of the unit sphere. This is how conditions imposed direction by
direction combine into one condition on the whole frequency space.

## Main results

* `IsOpen.exists_cone_exists_smul_mem`: the open cone over an open set containing `ξ`.
* `IsOpen.exists_cone_closedBall_subset`: an open cone `Γ` containing `ξ` contains a smaller open
  cone `Γ'` containing `ξ` such that `closedBall η (c * ‖η‖) ⊆ Γ` for every `η ∈ Γ'`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`: decay of order `N` on `Γ'` of a
  superposition of translates of a function decaying at order `N` on `Γ`, with rapidly decreasing
  coefficients, bounded by a weighted `ℓ¹` norm of the coefficients.
* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp`: a function that is Lipschitz with
  polynomially growing constant and whose weighted squares are integrable on `Γ` for every weight
  decays rapidly on `Γ'`.
* `TauCeti.exists_cone_decay_mul`: if `g` decays rapidly on an open cone around `a ζ₀ ≠ 0` and `h`
  grows at most polynomially, then `ζ ↦ g (a ζ) * h (b ζ)` decays rapidly on an open cone around
  `ζ₀`, provided `‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖`.
* `TauCeti.exists_finset_compl_singleton_subset_biUnion`: if every unit vector lies in an open
  cone, finitely many of these cones cover the nonzero vectors.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Lemma 8.1.1.
-/

public section

open Metric Set

namespace IsOpen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone over an open set: if `V` is open and contains `ξ`, there is an open set `Γ`
containing `ξ` and closed under multiplication by positive reals, every element of which is
rescaled by some `t > 0` into `V`. -/
theorem exists_cone_exists_smul_mem {V : Set E} (hV : IsOpen V) {ξ : E} (hξ : ξ ∈ V) :
    ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ η ∈ Γ, ∃ t : ℝ, 0 < t ∧ t • η ∈ V := by
  set Γ : Set E := ⋃ t ∈ Ioi (0 : ℝ), (t • ·) ⁻¹' V
  have hmem {η : E} : η ∈ Γ ↔ ∃ t : ℝ, 0 < t ∧ t • η ∈ V := by simp [Γ]
  refine ⟨Γ, isOpen_biUnion fun t _ ↦ hV.preimage (continuous_const_smul t),
    hmem.2 ⟨1, one_pos, by simpa using hξ⟩, fun s hs η hη ↦ ?_, fun η ↦ hmem.1⟩
  obtain ⟨t, ht, htη⟩ := hmem.1 hη
  exact hmem.2 ⟨t / s, div_pos ht hs, by rwa [smul_smul, div_mul_cancel₀ _ hs.ne']⟩

/-- An open set `Γ` closed under multiplication by positive reals contains, around each of its
points `ξ`, a smaller open set `Γ'` closed under multiplication by positive reals such that, for
some `c > 0`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. -/
theorem exists_cone_closedBall_subset {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ Γ' : Set E, IsOpen Γ' ∧ ξ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧
      ∃ c > 0, ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ := by
  obtain ⟨r, hr, hball⟩ := isOpen_iff.1 hΓ ξ hξ
  -- `Γ'` is the cone over the ball of radius `r / 2` about `ξ`.
  obtain ⟨Γ', hΓ'o, hξ', hcone', hmem⟩ :=
    exists_cone_exists_smul_mem (isOpen_ball (x := ξ)) (mem_ball_self (half_pos hr))
  refine ⟨Γ', hΓ'o, hξ', hcone', r / (2 * ‖ξ‖ + r), by positivity, fun η hη ζ hζ ↦ ?_⟩
  obtain ⟨t, ht, htη⟩ := hmem η hη
  rw [mem_ball] at htη
  -- Rescaled by `t`, the point `ζ` is within `r` of `ξ`, since `t ‖η‖ < ‖ξ‖ + r / 2`.
  have hnorm : t * ‖η‖ < ‖ξ‖ + r / 2 := by
    have h := norm_le_norm_add_norm_sub' (t • η) ξ
    rw [norm_smul, Real.norm_of_nonneg ht.le, ← dist_eq_norm] at h
    linarith
  have hζη : t * dist ζ η ≤ r / (2 * ‖ξ‖ + r) * (t * ‖η‖) := by
    rw [mem_closedBall] at hζ
    nlinarith
  have hr' : r / (2 * ‖ξ‖ + r) * (‖ξ‖ + r / 2) = r / 2 := by
    field_simp
  have htζ : t • ζ ∈ Γ := by
    refine hball (mem_ball.2 ?_)
    calc dist (t • ζ) ξ ≤ dist (t • ζ) (t • η) + dist (t • η) ξ := dist_triangle _ _ _
      _ = t * dist ζ η + dist (t • η) ξ := by
        rw [dist_smul₀, Real.norm_of_nonneg ht.le]
      _ < r / 2 + r / 2 := by
        refine add_lt_add_of_le_of_lt ?_ htη
        calc t * dist ζ η ≤ r / (2 * ‖ξ‖ + r) * (t * ‖η‖) := hζη
          _ ≤ r / (2 * ‖ξ‖ + r) * (‖ξ‖ + r / 2) := by gcongr
          _ = r / 2 := hr'
      _ = r := add_halves r
  simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using hcone t⁻¹ (inv_pos.2 ht) _ htζ

end IsOpen

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- **Rapid decay of a discrete convolution on a smaller cone.** A superposition
`∑ i, a i • F (η - v i)` of translates of a function `F` of polynomial growth, with coefficients
`a i` rapidly decreasing in `‖v i‖`, decays on every set `Γ'` whose conic neighbourhoods
`closedBall η (c ‖η‖)`, `c > 0`, lie in a set `Γ`, at every order `N` at which `F` decays on `Γ`:
if `F` grows at most like `(1 + ‖ζ‖) ^ k` and `(1 + ‖η‖) ^ N ‖F η‖` is bounded on `Γ`, then
`(1 + ‖η‖) ^ N ‖∑ i, a i • F (η - v i)‖` is bounded on `Γ'` by
`D ∑ i, (1 + ‖v i‖) ^ (N + 2 k) ‖a i‖`, with a constant `D ≥ 0` independent of the coefficients. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_hasSum {ι 𝕜 G : Type*} [NormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (v : ι → E) {F : E → G} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {N : ℕ} (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖F η‖ ≤ C) :
    ∃ D, 0 ≤ D ∧ ∀ a : ι → 𝕜, Summable (fun i ↦ (1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖) →
      ∀ η ∈ Γ', ∀ s, HasSum (fun i ↦ a i • F (η - v i)) s →
        (1 + ‖η‖) ^ N * ‖s‖ ≤ D * ∑' i, (1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C₁, hC₁⟩ := hdecay
  set D := max (2 ^ N * C₁) (C₀ * c'⁻¹ ^ (N + k))
  have hD : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨D, hD, fun a ha η hη s hs ↦ ?_⟩
  -- Each translate is bounded by `D (1 + ‖v i‖) ^ (N + 2 k) (1 + ‖η‖) ^ (-N)`.
  have hterm (i : ι) : (1 + ‖η‖) ^ N * ‖F (η - v i)‖ ≤ D * (1 + ‖v i‖) ^ (N + 2 * k) := by
    have h1 : 1 ≤ (1 + ‖v i‖) ^ (N + 2 * k) := one_le_pow₀ (by linarith [norm_nonneg (v i)])
    by_cases hv : ‖v i‖ ≤ c' * ‖η‖
    · -- Small shifts stay in `Γ`, where `F` decays rapidly, and `‖η - v i‖ ≥ ‖η‖ / 2`.
      have hmem : η - v i ∈ Γ := by
        refine hΓ' η hη (mem_closedBall.2 ?_)
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hv.trans (by gcongr; exact min_le_left _ _)
      have hle : 1 + ‖η‖ ≤ 2 * (1 + ‖η - v i‖) := by
        have := norm_sub_norm_le η (v i)
        nlinarith [norm_nonneg η]
      calc (1 + ‖η‖) ^ N * ‖F (η - v i)‖ ≤ (2 * (1 + ‖η - v i‖)) ^ N * ‖F (η - v i)‖ := by
            gcongr
        _ = 2 ^ N * ((1 + ‖η - v i‖) ^ N * ‖F (η - v i)‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ N * C₁ := by gcongr; exact hC₁ _ hmem
        _ ≤ D := le_max_left _ _
        _ ≤ D * (1 + ‖v i‖) ^ (N + 2 * k) := le_mul_of_one_le_right hD h1
    · -- Large shifts have `1 + ‖η‖ ≤ c'⁻¹ (1 + ‖v i‖)`; use the polynomial growth of `F`.
      push Not at hv
      have hle : 1 + ‖η‖ ≤ c'⁻¹ * (1 + ‖v i‖) := by
        rw [le_inv_mul_iff₀ hc']
        nlinarith [norm_nonneg η]
      have hFle : ‖F (η - v i)‖ ≤ C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v i‖) ^ k) := by
        refine (hF _).trans ?_
        rw [← mul_pow]
        gcongr
        nlinarith [norm_sub_le η (v i), norm_nonneg η, norm_nonneg (v i)]
      calc (1 + ‖η‖) ^ N * ‖F (η - v i)‖
          ≤ (1 + ‖η‖) ^ N * (C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v i‖) ^ k)) := by gcongr
        _ = C₀ * ((1 + ‖η‖) ^ (N + k) * (1 + ‖v i‖) ^ k) := by ring
        _ ≤ C₀ * ((c'⁻¹ * (1 + ‖v i‖)) ^ (N + k) * (1 + ‖v i‖) ^ k) := by gcongr
        _ = C₀ * c'⁻¹ ^ (N + k) * (1 + ‖v i‖) ^ (N + 2 * k) := by rw [mul_pow]; ring
        _ ≤ D * (1 + ‖v i‖) ^ (N + 2 * k) := by gcongr; exact le_max_right _ _
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  have hbound := hs.norm_le_of_bounded ((ha.hasSum.mul_left D).div_const _) fun i ↦ by
    rw [norm_smul, le_div_iff₀ hp]
    nlinarith [hterm i, norm_nonneg (a i)]
  rw [le_div_iff₀ hp] at hbound
  linarith

section MemLp

open MeasureTheory Module

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ G] in
/-- The pointwise step: within distance `δ ≤ 1` of a frequency `η` with `‖η‖ ≥ 1`, the value
`F η` is within `b = |A| (1 + ‖η‖) ^ k δ` of `F ζ`, and the weight `(1 + ‖ζ‖ ^ 2) ^ σ` is at least
`((1 + ‖η‖) ^ 2 / 8) ^ σ`. -/
private theorem sq_norm_le_of_norm_sub_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {η ζ : E}
    (hη : 1 ≤ ‖η‖) {δ : ℝ} (hδ : δ ≤ 1) (hd : ‖η - ζ‖ ≤ δ) (σ : ℕ) :
    ‖F η‖ ^ 2 ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) +
      2 * (|A| * (1 + ‖η‖) ^ k * δ) ^ 2 := by
  set b := |A| * (1 + ‖η‖) ^ k * δ
  have hFη : ‖F η‖ ≤ ‖F ζ‖ + b :=
    calc ‖F η‖ = ‖F ζ + (F η - F ζ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖F ζ‖ + ‖F η - F ζ‖ := norm_add_le _ _
      _ ≤ ‖F ζ‖ + A * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by gcongr; exact hLip η ζ (hd.trans hδ)
      _ ≤ ‖F ζ‖ + b := add_le_add le_rfl (by
        calc A * (1 + ‖η‖) ^ k * ‖η - ζ‖ ≤ |A| * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by
              gcongr; exact le_abs_self A
          _ ≤ |A| * (1 + ‖η‖) ^ k * δ := by gcongr)
  -- `‖ζ‖ ≥ ‖η‖ - 1 ≥ 0`, so `1 + ‖ζ‖ ^ 2 ≥ (1 + ‖η‖) ^ 2 / 8`.
  have hw : (1 + ‖η‖) ^ 2 / 8 ≤ 1 + ‖ζ‖ ^ 2 := by
    have hζη : ‖η‖ - 1 ≤ ‖ζ‖ := by linarith [norm_sub_norm_le η ζ]
    nlinarith [mul_self_le_mul_self (sub_nonneg.2 hη) hζη, sq_nonneg (‖η‖ - 9 / 7)]
  have hw₀ : 0 < ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by positivity
  have hW : ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) ≤ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 := by
    rw [← pow_mul, mul_comm σ 2]
    exact pow_le_pow_left₀ (by positivity) hw _
  have hFζ : ‖F ζ‖ ^ 2 ≤
      ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by
    rw [le_div_iff₀ hw₀, mul_comm]
    exact mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  calc ‖F η‖ ^ 2 ≤ 2 * ‖F ζ‖ ^ 2 + 2 * b ^ 2 := by
        nlinarith [norm_nonneg (F η), norm_nonneg (F ζ), sq_nonneg (‖F ζ‖ - b)]
    _ ≤ 2 * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ)) +
        2 * b ^ 2 := by gcongr
    _ = _ := by ring

omit [NormedSpace ℝ G] in
/-- The averaging step: a pointwise bound `a ≤ e g ζ + c` on a set `B ⊆ Γ` of finite measure,
with `g ≥ 0` integrable on `Γ` and `e ≥ 0`, gives `vol(B) a ≤ e ∫_Γ g + vol(B) c`. -/
private theorem measureReal_mul_le_mul_setIntegral_add {g : E → ℝ} {Γ B : Set E}
    (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) (hBΓ : B ⊆ Γ)
    (hg : Integrable g (volume.restrict Γ)) (hg0 : ∀ ζ, 0 ≤ g ζ) {a c e : ℝ} (he : 0 ≤ e)
    (h : ∀ ζ ∈ B, a ≤ e * g ζ + c) :
    volume.real B * a ≤ e * (∫ ζ in Γ, g ζ) + volume.real B * c := by
  have hgB : Integrable g (volume.restrict B) :=
    hg.mono_measure (Measure.restrict_mono_set volume hBΓ)
  have hle := setIntegral_ge_of_const_le hB hBfin h
    ((hgB.const_mul e).add (integrableOn_const hBfin))
  rw [integral_add (hgB.const_mul e) (integrableOn_const hBfin), integral_const_mul,
    setIntegral_const, smul_eq_mul, smul_eq_mul] at hle
  exact hle.trans (add_le_add (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hg (.of_forall hg0) (ae_of_all _ hBΓ)) he) le_rfl)

omit [NormedSpace ℝ G] in
/-- The estimate at a frequency `η` far from the origin: averaging the pointwise step over the
ball of radius `(1 + ‖η‖) ^ (-(N + k))` about `η`, which lies in `Γ`, bounds
`((1 + ‖η‖) ^ N ‖F η‖) ^ 2` by the weighted `L²` norm of order `4 σ` of `F` on `Γ`, where
`σ = d (N + k) + N` and `d` is the dimension. -/
private theorem sq_one_add_norm_pow_mul_norm_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {Γ : Set E}
    (N : ℕ) (hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 *
      ‖F ζ‖ ^ 2) (volume.restrict Γ)) {η : E} (hη : 1 ≤ ‖η‖) (hΓ : closedBall η 1 ⊆ Γ) :
    ((1 + ‖η‖) ^ N * ‖F η‖) ^ 2 ≤
      2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 * ‖F ζ‖ ^ 2) *
        8 ^ (2 * (finrank ℝ E * (N + k) + N)) / volume.real (ball (0 : E) 1) + 2 * A ^ 2 := by
  set d := finrank ℝ E
  set σ := d * (N + k) + N
  have ht1 : 1 ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
  have hδ0 : 0 < ((1 + ‖η‖) ^ (N + k))⁻¹ := by positivity
  have hδ1 : ((1 + ‖η‖) ^ (N + k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht1)
  have hle := measureReal_mul_le_mul_setIntegral_add measurableSet_closedBall
    measure_closedBall_lt_top.ne ((closedBall_subset_closedBall hδ1).trans hΓ) hint
    (fun ζ ↦ by positivity) (by positivity : (0 : ℝ) ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ))
    fun ζ hζ ↦
      sq_norm_le_of_norm_sub_le hLip hη hδ1 (by rw [← dist_eq_norm, dist_comm]; exact hζ) σ
  rw [Measure.addHaar_real_closedBall volume η hδ0.le] at hle
  -- Name the quantities of the estimate; `set` also abbreviates them in `hle`.
  set I := ∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2
  set v := volume.real (ball (0 : E) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set t := 1 + ‖η‖
  set δ := (t ^ (N + k))⁻¹
  set w₀ : ℝ := (t ^ 2 / 8) ^ (2 * σ)
  set b := |A| * t ^ k * δ
  have hmain : ‖F η‖ ^ 2 ≤ 2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2 := by
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    calc ‖F η‖ ^ 2 * (δ ^ d * v) = δ ^ d * v * ‖F η‖ ^ 2 := by ring
      _ ≤ 2 / w₀ * I + δ ^ d * v * (2 * b ^ 2) := hle
      _ = 2 / w₀ * I + 2 * b ^ 2 * (δ ^ d * v) := by ring
  -- The powers of `t` cancel, since `2 N + (N + k) d ≤ 4 σ` and `M = N + k`.
  have key₁ : t ^ (2 * N) ≤ 8 ^ (2 * σ) * (w₀ * δ ^ d) := by
    have h : 8 ^ (2 * σ) * (w₀ * δ ^ d) = t ^ (4 * σ) / t ^ ((N + k) * d) := by
      simp only [w₀, δ, div_pow, inv_pow, ← pow_mul]
      field_simp
      ring
    rw [h, le_div_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_right₀ ht1 (by
      simp only [σ]; nlinarith [Nat.zero_le (d * N), Nat.zero_le (d * k)])
  have key₂ : b ^ 2 * t ^ (2 * N) = A ^ 2 := by
    simp only [b, δ, mul_pow, sq_abs, inv_pow]
    field_simp
    ring
  calc (t ^ N * ‖F η‖) ^ 2 = t ^ (2 * N) * ‖F η‖ ^ 2 := by ring
    _ ≤ t ^ (2 * N) * (2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2) := by gcongr
    _ = 2 * I / v * (t ^ (2 * N) / (w₀ * δ ^ d)) + 2 * (b ^ 2 * t ^ (2 * N)) := by
      field_simp
    _ ≤ 2 * I / v * 8 ^ (2 * σ) + 2 * A ^ 2 := by
      rw [key₂]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      exact key₁
    _ = 2 * I * 8 ^ (2 * σ) / v + 2 * A ^ 2 := by ring

/-- **Rapid decay from square integrability of every order.** Let `F` be Lipschitz with a
polynomially growing constant, `‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`, and let
`⟨η⟩ ^ s F η` be square integrable on a set `Γ` for every real `s`, where
`⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)`. If for some `c > 0` the closed ball of radius `c ‖η‖` about
every point `η` of `Γ'` lies in `Γ`, then `F` decays rapidly on `Γ'`. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_forall_memLp {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hL : ∀ s : ℝ, MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 (volume.restrict Γ))
    (N : ℕ) : ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖F η‖ ≤ C := by
  set σ : ℕ := finrank ℝ E * (N + k) + N
  -- The weighted squares of order `4 σ` are integrable on `Γ`.
  have hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) (volume.restrict Γ) := by
    refine ((hL (2 * σ)).integrable_norm_pow two_ne_zero).congr (.of_forall fun ζ ↦ ?_)
    have h2 : (2 * (σ : ℝ)) / 2 = σ := by ring
    simp only [h2, Real.rpow_natCast, norm_smul, mul_pow,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖ ^ 2) ^ σ)]
  -- Near the origin `F` is bounded; far from it, `closedBall η 1 ⊆ Γ` for `η ∈ Γ'`.
  set R₀ := max 1 c⁻¹
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun η ↦
    continuousAt_of_locally_lipschitz one_pos (|A| * (1 + ‖η‖) ^ k) fun ζ hζ ↦ by
      rw [dist_comm (F ζ), dist_comm ζ, dist_eq_norm, dist_eq_norm]
      refine (hLip η ζ (by rw [← dist_eq_norm, dist_comm]; exact hζ.le)).trans ?_
      gcongr
      exact le_abs_self A
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : E) R₀).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨max (Real.sqrt (2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) * 8 ^ (2 * σ) /
    volume.real (ball (0 : E) 1) + 2 * A ^ 2)) ((1 + R₀) ^ N * C₁), fun η hη ↦ ?_⟩
  rcases lt_or_ge ‖η‖ R₀ with hsmall | hlarge
  · exact le_max_of_le_right (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N)
      (hC₁ η (by simpa using hsmall.le)) (norm_nonneg _) (by positivity))
  have hct : 1 ≤ c * ‖η‖ :=
    calc 1 = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * ‖η‖ := by gcongr; exact (le_max_right _ _).trans hlarge
  exact le_max_of_le_left ((le_abs_self _).trans (Real.abs_le_sqrt
    (sq_one_add_norm_pow_mul_norm_le hLip N hint ((le_max_left _ _).trans hlarge)
      ((closedBall_subset_closedBall hct).trans (hΓ' η hη)))))

end MemLp

/-- **Rapid decay of a product on a cone.** If `g` decays rapidly on an open cone `Γ` containing
`a ζ₀ ≠ 0` and `h` grows at most polynomially, then `ζ ↦ g (a ζ) * h (b ζ)` decays rapidly on an
open cone containing `ζ₀`, provided `‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖`. The cone is that of the `ζ` with
`a ζ ∈ Γ` and `‖b ζ‖ < c ‖a ζ‖`, on which `‖ζ‖` and `‖b ζ‖` are at most `(1 + c) ‖a ζ‖`. -/
theorem exists_cone_decay_mul {X A B 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B]
    (a : X →L[ℝ] A) (b : X →L[ℝ] B) (hab : ∀ ζ, ‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖) {Γ : Set A}
    (hΓ : IsOpen Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ, t • ξ ∈ Γ) {ζ₀ : X} (hζ₀ : a ζ₀ ∈ Γ)
    (ha₀ : a ζ₀ ≠ 0) {g : A → 𝕜} {h : B → 𝕜}
    (hg : ∀ N : ℕ, ∃ C, ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ N * ‖g ξ‖ ≤ C)
    (hh : ∃ (C : ℝ) (k : ℕ), ∀ η, ‖h η‖ ≤ C * (1 + ‖η‖) ^ k) :
    ∃ Γ' : Set X, IsOpen Γ' ∧ ζ₀ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ', t • ζ ∈ Γ') ∧
      ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ', (1 + ‖ζ‖) ^ N * ‖g (a ζ) * h (b ζ)‖ ≤ C := by
  obtain ⟨C₀, k, hC₀⟩ := hh
  have hC₀' : 0 ≤ C₀ := by simpa using (norm_nonneg _).trans (hC₀ 0)
  have ha₀' : 0 < ‖a ζ₀‖ := norm_pos_iff.2 ha₀
  set c := ‖b ζ₀‖ / ‖a ζ₀‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  refine ⟨a ⁻¹' Γ ∩ {ζ | ‖b ζ‖ < c * ‖a ζ‖},
    (hΓ.preimage a.continuous).inter (isOpen_lt (by fun_prop) (by fun_prop)), ⟨hζ₀, ?_⟩, ?_,
    fun N ↦ ?_⟩
  · have : c * ‖a ζ₀‖ = ‖b ζ₀‖ + ‖a ζ₀‖ := by
      rw [hc_def, add_mul, div_mul_cancel₀ _ ha₀'.ne', one_mul]
    simp only [mem_ofPred_eq, this]
    linarith
  · rintro t ht ζ ⟨h₁, h₂⟩
    refine ⟨by simpa using hcone t ht _ h₁, ?_⟩
    simp only [mem_ofPred_eq, map_smul, norm_smul, Real.norm_of_nonneg ht.le]
    rw [mul_left_comm]
    exact mul_lt_mul_of_pos_left h₂ ht
  · obtain ⟨C, hC⟩ := hg (N + k)
    refine ⟨(1 + c) ^ (N + k) * C₀ * C, fun ζ ⟨h₁, h₂⟩ ↦ ?_⟩
    have h₂' : ‖b ζ‖ ≤ c * ‖a ζ‖ := h₂.le
    have hr : 0 ≤ ‖a ζ‖ := norm_nonneg _
    have hζ : 1 + ‖ζ‖ ≤ (1 + c) * (1 + ‖a ζ‖) := by nlinarith [hab ζ]
    have hb : 1 + ‖b ζ‖ ≤ (1 + c) * (1 + ‖a ζ‖) := by nlinarith
    have hh' : ‖h (b ζ)‖ ≤ C₀ * ((1 + c) * (1 + ‖a ζ‖)) ^ k :=
      (hC₀ _).trans (by gcongr)
    calc (1 + ‖ζ‖) ^ N * ‖g (a ζ) * h (b ζ)‖
        = (1 + ‖ζ‖) ^ N * ‖h (b ζ)‖ * ‖g (a ζ)‖ := by rw [norm_mul]; ring
      _ ≤ ((1 + c) * (1 + ‖a ζ‖)) ^ N * (C₀ * ((1 + c) * (1 + ‖a ζ‖)) ^ k) * ‖g (a ζ)‖ := by
          gcongr
      _ = (1 + c) ^ (N + k) * C₀ * ((1 + ‖a ζ‖) ^ (N + k) * ‖g (a ζ)‖) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]
          ring
      _ ≤ (1 + c) ^ (N + k) * C₀ * C := by gcongr; exact hC _ h₁


/-- **Finitely many open cones cover the nonzero vectors.** If every unit vector `ξ` of a proper
real normed space lies in an open set `Γ ξ` closed under multiplication by positive reals, then
finitely many of these cones cover every nonzero vector: the unit sphere is compact. -/
theorem exists_finset_compl_singleton_subset_biUnion [NormedSpace ℝ E] [ProperSpace E]
    {Γ : sphere (0 : E) 1 → Set E} (hΓ : ∀ ξ, IsOpen (Γ ξ)) (hξΓ : ∀ ξ, (ξ : E) ∈ Γ ξ)
    (hcone : ∀ ξ, ∀ t : ℝ, 0 < t → ∀ η ∈ Γ ξ, t • η ∈ Γ ξ) :
    ∃ t : Finset (sphere (0 : E) 1), {0}ᶜ ⊆ ⋃ ξ ∈ t, Γ ξ := by
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover Γ hΓ
    fun ζ hζ ↦ mem_iUnion.2 ⟨⟨ζ, hζ⟩, hξΓ _⟩
  refine ⟨t, fun η hη ↦ ?_⟩
  -- The direction of `η` lies in one of the finitely many cones, hence so does `η`.
  have hη' : 0 < ‖η‖ := norm_pos_iff.2 hη
  obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (ht (show ‖η‖⁻¹ • η ∈ sphere (0 : E) 1 by
    simp [norm_smul, inv_mul_cancel₀ hη'.ne']))
  exact mem_iUnion₂.2 ⟨ξ, hξt, by
    simpa [smul_smul, mul_inv_cancel₀ hη'.ne'] using hcone ξ ‖η‖ hη' _ hηξ⟩

end TauCeti
