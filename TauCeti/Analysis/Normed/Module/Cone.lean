/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic

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

Rapid decay in a cone also survives multiplication by a function of polynomial growth in other
variables: if `g` decays rapidly on a cone around `a ζ₀ ≠ 0`, then `g (a ζ) h (b ζ)` decays rapidly
on the cone of those `ζ` with `a ζ` in that cone and `‖b ζ‖ < c ‖a ζ‖`. This is how the localized
Fourier transform of a tensor product inherits the decay of one of its factors.

In a proper space, if every unit vector lies in an open cone, finitely many of these cones cover
the nonzero vectors, by compactness of the unit sphere. This is how conditions imposed direction by
direction combine into one condition on the whole frequency space.

## Main results

* `IsOpen.exists_cone_closedBall_subset`: an open cone `Γ` containing `ξ` contains a smaller open
  cone `Γ'` containing `ξ` such that `closedBall η (c * ‖η‖) ⊆ Γ` for every `η ∈ Γ'`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`: decay of order `N` on `Γ'` of a
  superposition of translates of a function decaying at order `N` on `Γ`, with rapidly decreasing
  coefficients.
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

/-- An open set `Γ` closed under multiplication by positive reals contains, around each of its
points `ξ`, a smaller open set `Γ'` closed under multiplication by positive reals such that, for
some `c > 0`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. -/
theorem exists_cone_closedBall_subset {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ Γ' : Set E, IsOpen Γ' ∧ ξ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧
      ∃ c > 0, ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ := by
  obtain ⟨r, hr, hball⟩ := isOpen_iff.1 hΓ ξ hξ
  -- `Γ'` is the cone over the ball of radius `r / 2` about `ξ`.
  set Γ' : Set E := ⋃ t ∈ Ioi (0 : ℝ), (t • ·) ⁻¹' ball ξ (r / 2)
  have hmem {η : E} : η ∈ Γ' ↔ ∃ t : ℝ, 0 < t ∧ dist (t • η) ξ < r / 2 := by
    simp [Γ']
  refine ⟨Γ', isOpen_biUnion fun t _ ↦ isOpen_ball.preimage (continuous_const_smul t),
    hmem.2 ⟨1, one_pos, by simpa using half_pos hr⟩, fun s hs η hη ↦ ?_,
    r / (2 * ‖ξ‖ + r), by positivity, fun η hη ζ hζ ↦ ?_⟩
  · obtain ⟨t, ht, htη⟩ := hmem.1 hη
    exact hmem.2 ⟨t / s, div_pos ht hs, by rwa [smul_smul, div_mul_cancel₀ _ hs.ne']⟩
  · obtain ⟨t, ht, htη⟩ := hmem.1 hη
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
if `(1 + ‖η‖) ^ N ‖F η‖` is bounded on `Γ`, then `(1 + ‖η‖) ^ N ‖∑ i, a i • F (η - v i)‖` is
bounded on `Γ'`. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_hasSum {ι 𝕜 G : Type*} [NormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {v : ι → E} {a : ι → 𝕜}
    (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) {F : E → G} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {N : ℕ} (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖F η‖ ≤ C) :
    ∃ C, ∀ η ∈ Γ', ∀ s, HasSum (fun i ↦ a i • F (η - v i)) s → (1 + ‖η‖) ^ N * ‖s‖ ≤ C := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C₁, hC₁⟩ := hdecay
  set D := max (2 ^ N * C₁) (C₀ * c'⁻¹ ^ (N + k))
  have hD : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨D * ∑' i, (1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖, fun η hη s hs ↦ ?_⟩
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
  have hbound := hs.norm_le_of_bounded (((ha (N + 2 * k)).hasSum.mul_left D).div_const _)
    fun i ↦ by
      rw [norm_smul, le_div_iff₀ hp]
      calc ‖a i‖ * ‖F (η - v i)‖ * (1 + ‖η‖) ^ N
          = ‖a i‖ * ((1 + ‖η‖) ^ N * ‖F (η - v i)‖) := by ring
        _ ≤ ‖a i‖ * (D * (1 + ‖v i‖) ^ (N + 2 * k)) := by gcongr ‖a i‖ * ?_; exact hterm i
        _ = D * ((1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖) := by ring
  rw [le_div_iff₀ hp] at hbound
  linarith

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
