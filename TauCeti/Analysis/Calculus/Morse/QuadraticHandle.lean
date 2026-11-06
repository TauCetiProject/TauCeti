/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Milnor's handle in the quadratic model is a product of discs

Near a nondegenerate critical point of index `λ` with critical value `c`, a Morse function has the
form `f = c - ‖u‖² + ‖v‖²`, where `u ∈ Eᵤ` runs over the `λ` negative directions and `v ∈ Eₛ`
over the positive ones. Milnor lowers `f` near the critical point to
`F = f - μ(‖u‖² + 2‖v‖²)`, where `μ` is a nonincreasing cutoff equal to `2ε` near `0` and vanishing
on `[2ε, ∞)`. The modified function has the same upper sublevel `{F ≤ c + ε} = {f ≤ c + ε}` and no
critical points in the band `F⁻¹[c - ε, c + ε]`, so `{f ≤ c + ε}` is diffeomorphic to the sublevel
`{F ≤ c - ε}`. That sublevel is the lower sublevel `{f ≤ c - ε}` together with the *handle*

`H = {-ε ≤ -‖u‖² + ‖v‖², -‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²) ≤ -ε, ‖u‖² + 2‖v‖² ≤ 2ε}`

(`TauCeti.quadraticHandle ε μ`): every point of `{F ≤ c - ε}` above the level `f = c - ε` lies
in it (`TauCeti.mem_quadraticHandle_or_eq_of_le`). It meets the lower sublevel in its *attaching
region* `H ∩ {-‖u‖² + ‖v‖² = -ε}`.

This file identifies the handle with the product `D^λ × D^(m-λ)` of closed unit discs, carrying the
attaching region onto `∂D^λ × D^(m-λ)`. The identification is explicit: `TauCeti.quadraticHandleMap`
rescales the two components,

`(u, v) ↦ ((‖v‖² + ε)^(-1/2) • u, (‖u‖² + μ(‖u‖² + 2‖v‖²) - ε)^(-1/2) • v)`.

So the squared norms of the two components of the image are `s / (t + ε)` and
`t / (s + μ(s + 2t) - ε)`, where `s = ‖u‖²` and `t = ‖v‖²`. On each line `s = σ (t + ε)` of
constant first coordinate `σ ∈ [0, 1]`, the second coordinate increases strictly with `t` from `0`
on the core `v = 0` to `1` on the top `F = c - ε` of the handle, because `μ` is nonincreasing. So
the map is a bijection from the handle onto the product of the closed unit balls
(`TauCeti.bijOn_quadraticHandleMap`), and since the handle is compact in finite dimensions it is
a homeomorphism (`TauCeti.quadraticHandleHomeomorph`). The first component has norm `1` exactly on
the attaching region (`TauCeti.norm_fst_quadraticHandleMap_eq_one_iff`) and the second exactly on
the top of the handle (`TauCeti.norm_snd_quadraticHandleMap_eq_one_iff`); the second vanishes
exactly on the core `v = 0` (`TauCeti.quadraticHandleMap_snd_eq_zero_iff`).

The cutoff is assumed continuous, nonincreasing, larger than `ε` at `ε`, and positive exactly on
`(-∞, 2ε)`; the last condition makes the handle end where the cutoff does.

## Main declarations

* `TauCeti.quadraticHandle`: Milnor's handle in the quadratic model.
* `TauCeti.quadraticHandleMap`: the rescaling which straightens it.
* `TauCeti.bijOn_quadraticHandleMap`: the rescaling maps the handle bijectively onto the product
  of the closed unit balls.
* `TauCeti.quadraticHandleHomeomorph`: the homeomorphism of the handle with `D^λ × D^(m-λ)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2 and Remark 3.3.
-/

public section

open Set Metric

noncomputable section

namespace TauCeti

variable {Eᵤ Eₛ : Type*} [NormedAddCommGroup Eᵤ] [NormedAddCommGroup Eₛ] {ε : ℝ} {μ : ℝ → ℝ}
  {z : Eᵤ × Eₛ}

/-- **Milnor's handle** in the quadratic model `-‖u‖² + ‖v‖²` of a Morse function at a critical
point: the points of the ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε` lying on or above the level `-ε` of the
model and on or below the level `-ε` of the lowered model `-‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`. -/
def quadraticHandle (ε : ℝ) (μ : ℝ → ℝ) : Set (Eᵤ × Eₛ) :=
  {z | -ε ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ∧
    -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) ≤ -ε ∧
    ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 ≤ 2 * ε}

@[simp]
theorem mem_quadraticHandle :
    z ∈ quadraticHandle ε μ ↔ -ε ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ∧
      -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) ≤ -ε ∧
      ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 ≤ 2 * ε :=
  Iff.rfl

/-- Where the cutoff vanishes on `[2ε, ∞)`, a point on or above the level `-ε` of the model and on
or below the level `-ε` of the lowered model lies in the handle or on the level `-ε` of the
model. So the handle is what the lowering adds to the lower sublevel of the model. -/
theorem mem_quadraticHandle_or_eq_of_le (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    (h₁ : -ε ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
    (h₂ : -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) ≤ -ε) :
    z ∈ quadraticHandle ε μ ∨ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -ε := by
  by_cases h₃ : ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 ≤ 2 * ε
  · exact .inl ⟨h₁, h₂, h₃⟩
  · rw [hμ₀ _ (not_le.1 h₃).le, sub_zero] at h₂
    exact .inr (le_antisymm h₂ h₁)

variable [NormedSpace ℝ Eᵤ] [NormedSpace ℝ Eₛ]

/-- The rescaling `(u, v) ↦ ((‖v‖² + ε)^(-1/2) • u, (‖u‖² + μ(‖u‖² + 2‖v‖²) - ε)^(-1/2) • v)`
which identifies Milnor's handle `TauCeti.quadraticHandle ε μ` with the product of the closed unit
balls (`TauCeti.bijOn_quadraticHandleMap`). -/
def quadraticHandleMap (ε : ℝ) (μ : ℝ → ℝ) (z : Eᵤ × Eₛ) : Eᵤ × Eₛ :=
  ((√(‖z.2‖ ^ 2 + ε))⁻¹ • z.1, (√(‖z.1‖ ^ 2 + μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) - ε))⁻¹ • z.2)

theorem quadraticHandleMap_apply (z : Eᵤ × Eₛ) :
    quadraticHandleMap ε μ z = ((√(‖z.2‖ ^ 2 + ε))⁻¹ • z.1,
      (√(‖z.1‖ ^ 2 + μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) - ε))⁻¹ • z.2) :=
  (rfl)

/-- The squared norm of a vector scaled by the square root of `a ≥ 0` is multiplied by `a`. -/
private theorem norm_sqrt_smul_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a : ℝ}
    (ha : 0 ≤ a) (x : F) : ‖√a • x‖ ^ 2 = a * ‖x‖ ^ 2 := by
  simp [norm_smul, mul_pow, Real.sq_sqrt ha]

/-- The squared norm of a vector scaled by the inverse square root of `a ≥ 0` is divided by `a`. -/
private theorem norm_inv_sqrt_smul_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 ≤ a) (x : F) : ‖(√a)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / a := by
  simp [norm_smul, mul_pow, Real.sq_sqrt ha, div_eq_inv_mul]

/-! ### The handle in the coordinates `s = ‖u‖²`, `t = ‖v‖²`

The handle and the rescaling only depend on `s = ‖u‖²` and `t = ‖v‖²`. In these coordinates the
handle is the region `-ε ≤ -s + t`, `-s + t - μ(s + 2t) ≤ -ε`, `s + 2t ≤ 2ε`, and the squared norms
of the components of the rescaling are `s / (t + ε)` and `t / (s + μ(s + 2t) - ε)`. -/

section Coordinates

variable (hμa : Antitone μ) (hμε : ε < μ ε)
include hμa hμε

/-- The denominator `s + μ(s + 2t) - ε` of the second coordinate is positive on the handle: it is
at least `t` there, and for `t = 0` it is `s + μ(s) - ε ≥ μ(ε) - ε > 0`. -/
private theorem sub_pos_of_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h₁ : -ε ≤ -s + t)
    (h₂ : -s + t - μ (s + 2 * t) ≤ -ε) : 0 < s + μ (s + 2 * t) - ε := by
  rcases ht.eq_or_lt with rfl | ht
  · have := hμa (by linarith : s + 2 * 0 ≤ ε)
    linarith
  · linarith

/-- Along a line `s = σ (t + ε)` of constant first coordinate, the second coordinate
`t / (s + μ(s + 2t) - ε)` of points of the handle increases strictly with `t`. Writing
`κ = μ(s + 2t) - (1 - σ) ε`, the claim is `t κ' < t' κ` for `t < t'`; here `κ' ≤ κ` because `μ` is
nonincreasing, and `κ > 0` by the defining inequalities of the handle. -/
private theorem mul_lt_mul_of_lt (hε : 0 < ε) (hμ_pos : ∀ r < 2 * ε, 0 < μ r) {s t s' t' : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (h₁ : -ε ≤ -s + t) (h₂ : -s + t - μ (s + 2 * t) ≤ -ε)
    (h₃' : s' + 2 * t' ≤ 2 * ε) (hσ : s * (t' + ε) = s' * (t + ε)) (htt : t < t') :
    t * (s' + μ (s' + 2 * t') - ε) < t' * (s + μ (s + 2 * t) - ε) := by
  have htε : 0 < t + ε := by linarith
  set σ := s / (t + ε) with hσdef
  have hs_eq : s = σ * (t + ε) := by rw [hσdef, div_mul_cancel₀ _ htε.ne']
  have hs'_eq : s' = σ * (t' + ε) := by
    rw [hσdef]
    field_simp
    linarith
  have hσ0 : 0 ≤ σ := div_nonneg hs htε.le
  have hσ1 : σ ≤ 1 := (div_le_one htε).2 (by linarith)
  have hss' : s ≤ s' := by rw [hs_eq, hs'_eq]; nlinarith
  have hμμ := hμa (by linarith : s + 2 * t ≤ s' + 2 * t')
  -- The key positivity `κ = μ(s + 2t) - (1 - σ) ε > 0`.
  have hκ : 0 < μ (s + 2 * t) - (1 - σ) * ε := by
    rcases hσ1.lt_or_eq with hσ1 | hσ1
    · rcases ht.eq_or_lt with rfl | ht
      · have := hμa (by linarith : s + 2 * 0 ≤ ε)
        nlinarith
      · nlinarith
    · rw [hσ1, sub_self, zero_mul, sub_zero]
      exact hμ_pos (s + 2 * t) (by linarith)
  set μ₁ := μ (s + 2 * t)
  set μ₂ := μ (s' + 2 * t')
  have key : t * (s' + μ₂ - ε) - t' * (s + μ₁ - ε) =
      t * (μ₂ - (1 - σ) * ε) - t' * (μ₁ - (1 - σ) * ε) := by
    rw [hs_eq, hs'_eq]
    ring
  have h₁ : t * (μ₂ - (1 - σ) * ε) ≤ t * (μ₁ - (1 - σ) * ε) :=
    mul_le_mul_of_nonneg_left (by linarith) ht
  have h₂ : t * (μ₁ - (1 - σ) * ε) < t' * (μ₁ - (1 - σ) * ε) := mul_lt_mul_of_pos_right htt hκ
  linarith

/-- Points of the handle with the same coordinates `s / (t + ε)` and `t / (s + μ(s + 2t) - ε)`
have the same `s` and `t`. -/
private theorem eq_of_div_eq (hε : 0 < ε) (hμ_pos : ∀ r < 2 * ε, 0 < μ r) {s t s' t' : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (h₁ : -ε ≤ -s + t) (h₂ : -s + t - μ (s + 2 * t) ≤ -ε)
    (h₃ : s + 2 * t ≤ 2 * ε) (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h₁' : -ε ≤ -s' + t')
    (h₂' : -s' + t' - μ (s' + 2 * t') ≤ -ε) (h₃' : s' + 2 * t' ≤ 2 * ε)
    (hσ : s / (t + ε) = s' / (t' + ε))
    (hρ : t / (s + μ (s + 2 * t) - ε) = t' / (s' + μ (s' + 2 * t') - ε)) :
    s = s' ∧ t = t' := by
  have hD := sub_pos_of_le hμa hμε hs ht h₁ h₂
  have hD' := sub_pos_of_le hμa hμε hs' ht' h₁' h₂'
  rw [div_eq_div_iff (by linarith) (by linarith)] at hσ
  have htt : t = t' := by
    rcases lt_trichotomy t t' with htt | htt | htt
    · have := mul_lt_mul_of_lt hμa hμε hε hμ_pos hs ht h₁ h₂ h₃' hσ htt
      rw [div_eq_div_iff hD.ne' hD'.ne'] at hρ
      linarith
    · exact htt
    · have := mul_lt_mul_of_lt hμa hμε hε hμ_pos hs' ht' h₁' h₂' h₃ hσ.symm htt
      rw [div_eq_div_iff hD.ne' hD'.ne'] at hρ
      linarith
  subst htt
  exact ⟨mul_right_cancel₀ (by linarith : t + ε ≠ 0) hσ, rfl⟩

/-- Every pair of coordinates `(σ, ρ) ∈ [0, 1]²` is attained on the handle: on the line
`s = σ (t + ε)`, the handle is the segment from `t = 0`, where `ρ = 0`, to the point on its top
`-s + t - μ(s + 2t) = -ε`, where `ρ = 1`. -/
private theorem exists_div_eq (hε : 0 < ε) (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    {σ ρ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ t, 0 ≤ t ∧ -ε ≤ -(σ * (t + ε)) + t ∧
      -(σ * (t + ε)) + t - μ (σ * (t + ε) + 2 * t) ≤ -ε ∧ σ * (t + ε) + 2 * t ≤ 2 * ε ∧
      t / (σ * (t + ε) + μ (σ * (t + ε) + 2 * t) - ε) = ρ := by
  -- `h t ≥ 0` is the condition to lie below the top of the handle; `h` is nonincreasing.
  set h : ℝ → ℝ := fun t ↦ σ * (t + ε) + μ (σ * (t + ε) + 2 * t) - t - ε with hh
  have hcont : Continuous h := by fun_prop
  have hanti : Antitone h := fun t t' htt ↦ by
    have := hμa (by nlinarith : σ * (t + ε) + 2 * t ≤ σ * (t' + ε) + 2 * t')
    simp only [hh]
    nlinarith
  have h0 : 0 < h 0 := by
    have := hμa (by nlinarith : σ * (0 + ε) + 2 * 0 ≤ ε)
    simp only [hh]
    nlinarith
  -- At `T`, the end of the line inside the ellipsoid, the cutoff vanishes and `h T ≤ 0`.
  set T := (2 - σ) * ε / (σ + 2) with hT
  have hT0 : 0 ≤ T := div_nonneg (mul_nonneg (by linarith) hε.le) (by linarith)
  have hTell : σ * (T + ε) + 2 * T = 2 * ε := by
    rw [hT]
    field_simp
    ring
  have hT : h T ≤ 0 := by
    simp only [hh]
    rw [hTell, hμ₀ _ le_rfl]
    nlinarith
  obtain ⟨t₀, ⟨ht₀0, ht₀T⟩, ht₀⟩ :=
    intermediate_value_Icc' hT0 hcont.continuousOn ⟨hT, h0.le⟩
  have ht₀pos : 0 < t₀ := ht₀0.lt_of_ne (by rintro rfl; linarith)
  -- Along `[0, t₀]` the second coordinate runs continuously from `0` to `1`.
  have hden (t : ℝ) (ht : t ∈ Icc 0 t₀) : 0 < σ * (t + ε) + μ (σ * (t + ε) + 2 * t) - ε := by
    have hle : h t₀ ≤ h t := hanti ht.2
    rcases ht.1.eq_or_lt with rfl | htpos
    · simpa [hh] using h0
    · simp only [hh] at hle ht₀
      linarith
  have hρcont : ContinuousOn (fun t ↦ t / (σ * (t + ε) + μ (σ * (t + ε) + 2 * t) - ε))
      (Icc 0 t₀) :=
    continuousOn_id.div (by fun_prop) fun t ht ↦ (hden t ht).ne'
  have hρt₀ : t₀ / (σ * (t₀ + ε) + μ (σ * (t₀ + ε) + 2 * t₀) - ε) = 1 := by
    rw [div_eq_one_iff_eq (hden t₀ ⟨ht₀0, le_rfl⟩).ne']
    simp only [hh] at ht₀
    linarith
  obtain ⟨t, ⟨ht0, htt₀⟩, rfl⟩ :=
    intermediate_value_Icc ht₀0 hρcont ⟨by simpa using hρ0, by rwa [hρt₀]⟩
  have hle : h t₀ ≤ h t := hanti htt₀
  simp only [hh] at hle ht₀
  exact ⟨t, ht0, by nlinarith, by linarith, by nlinarith, rfl⟩

end Coordinates

/-! ### The rescaling as a homeomorphism -/

variable (hε : 0 < ε) (hμa : Antitone μ) (hμε : ε < μ ε)
include hε hμa hμε

omit [NormedSpace ℝ Eᵤ] [NormedSpace ℝ Eₛ] hε in
/-- On the handle, the denominator `‖u‖² + μ(‖u‖² + 2‖v‖²) - ε` of the second component of the
rescaling is positive. -/
private theorem sub_pos_of_mem_quadraticHandle (hz : z ∈ quadraticHandle ε μ) :
    0 < ‖z.1‖ ^ 2 + μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) - ε :=
  sub_pos_of_le hμa hμε (sq_nonneg _) (sq_nonneg _) hz.1 hz.2.1

omit hμa hμε in
/-- The squared norm of the first component of the rescaling is `‖u‖² / (‖v‖² + ε)`. -/
theorem norm_fst_quadraticHandleMap_sq (z : Eᵤ × Eₛ) :
    ‖(quadraticHandleMap ε μ z).1‖ ^ 2 = ‖z.1‖ ^ 2 / (‖z.2‖ ^ 2 + ε) := by
  rw [quadraticHandleMap_apply, norm_inv_sqrt_smul_sq (by positivity)]

omit hε in
/-- The squared norm of the second component of the rescaling is
`‖v‖² / (‖u‖² + μ(‖u‖² + 2‖v‖²) - ε)`. -/
theorem norm_snd_quadraticHandleMap_sq (hz : z ∈ quadraticHandle ε μ) :
    ‖(quadraticHandleMap ε μ z).2‖ ^ 2 =
      ‖z.2‖ ^ 2 / (‖z.1‖ ^ 2 + μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) - ε) := by
  rw [quadraticHandleMap_apply,
    norm_inv_sqrt_smul_sq (sub_pos_of_mem_quadraticHandle hμa hμε hz).le]

/-- The rescaling maps the handle into the product of the closed unit balls. -/
theorem mapsTo_quadraticHandleMap :
    MapsTo (quadraticHandleMap ε μ) (quadraticHandle ε μ)
      (closedBall (0 : Eᵤ) 1 ×ˢ closedBall (0 : Eₛ) 1) := fun z hz ↦ by
  have hD := sub_pos_of_mem_quadraticHandle hμa hμε hz
  simp only [mem_prod, mem_closedBall_zero_iff]
  refine ⟨(sq_le_one_iff₀ (norm_nonneg _)).1 ?_, (sq_le_one_iff₀ (norm_nonneg _)).1 ?_⟩
  · rw [norm_fst_quadraticHandleMap_sq hε, div_le_one (by positivity)]
    linarith [hz.1]
  · rw [norm_snd_quadraticHandleMap_sq hμa hμε hz, div_le_one hD]
    linarith [hz.2.1]

/-- The rescaling is injective on the handle. -/
theorem injOn_quadraticHandleMap (hμ_pos : ∀ r < 2 * ε, 0 < μ r) :
    InjOn (quadraticHandleMap ε μ : Eᵤ × Eₛ → Eᵤ × Eₛ) (quadraticHandle ε μ) :=
    fun z hz z' hz' hzz ↦ by
  have hσ := norm_fst_quadraticHandleMap_sq hε (μ := μ) z
  have hρ := norm_snd_quadraticHandleMap_sq hμa hμε hz
  rw [hzz, norm_fst_quadraticHandleMap_sq hε] at hσ
  rw [hzz, norm_snd_quadraticHandleMap_sq hμa hμε hz'] at hρ
  obtain ⟨hs, ht⟩ := eq_of_div_eq hμa hμε hε hμ_pos (sq_nonneg _) (sq_nonneg _) hz.1 hz.2.1
    hz.2.2 (sq_nonneg _) (sq_nonneg _) hz'.1 hz'.2.1 hz'.2.2 hσ.symm hρ.symm
  -- The rescaling factors agree and are nonzero, so the components agree.
  simp only [quadraticHandleMap_apply, Prod.mk.injEq, hs, ht] at hzz
  refine Prod.ext (smul_right_injective _ ?_ hzz.1) (smul_right_injective _ ?_ hzz.2)
  · exact inv_ne_zero (Real.sqrt_pos.2 (by positivity)).ne'
  · exact inv_ne_zero (Real.sqrt_pos.2 (ht ▸ hs ▸ sub_pos_of_mem_quadraticHandle hμa hμε hz)).ne'

/-- The rescaling maps the handle onto the product of the closed unit balls. Given `(a, b)`, the
coordinates `s` and `t` of a preimage are found on the line `s = ‖a‖² (t + ε)`, and the preimage is
`(√(t + ε) • a, √(s + μ(s + 2t) - ε) • b)`. -/
theorem surjOn_quadraticHandleMap (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) :
    SurjOn (quadraticHandleMap ε μ) (quadraticHandle ε μ)
      (closedBall (0 : Eᵤ) 1 ×ˢ closedBall (0 : Eₛ) 1) := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  rw [mem_closedBall_zero_iff] at ha hb
  obtain ⟨t, ht0, h₁, h₂, h₃, hρ⟩ := exists_div_eq hμa hμε hε hμ hμ₀ (sq_nonneg ‖a‖)
    (pow_le_one₀ (norm_nonneg _) ha) (sq_nonneg ‖b‖) (pow_le_one₀ (norm_nonneg _) hb)
  set s := ‖a‖ ^ 2 * (t + ε)
  have htε : 0 < t + ε := by linarith
  have hD : 0 < s + μ (s + 2 * t) - ε := sub_pos_of_le hμa hμε (by positivity) ht0 h₁ h₂
  have hu : ‖√(t + ε) • a‖ ^ 2 = s := by
    rw [norm_sqrt_smul_sq htε.le, mul_comm]
  have hv : ‖√(s + μ (s + 2 * t) - ε) • b‖ ^ 2 = t := by
    rw [norm_sqrt_smul_sq hD.le, ← hρ, mul_div_cancel₀ _ hD.ne']
  refine ⟨(√(t + ε) • a, √(s + μ (s + 2 * t) - ε) • b), ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [hu, hv] using h₁
  · simpa only [hu, hv] using h₂
  · simpa only [hu, hv] using h₃
  · simp only [quadraticHandleMap_apply, hu, hv, smul_smul, inv_mul_cancel₀
      (Real.sqrt_pos.2 htε).ne', inv_mul_cancel₀ (Real.sqrt_pos.2 hD).ne', one_smul]

/-- **Milnor's handle is a product of discs.** The rescaling `TauCeti.quadraticHandleMap` maps the
handle bijectively onto the product of the closed unit balls of `Eᵤ` and `Eₛ`. -/
theorem bijOn_quadraticHandleMap (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
    (hμ_pos : ∀ r < 2 * ε, 0 < μ r) :
    BijOn (quadraticHandleMap ε μ) (quadraticHandle ε μ)
      (closedBall (0 : Eᵤ) 1 ×ˢ closedBall (0 : Eₛ) 1) :=
  ⟨mapsTo_quadraticHandleMap hε hμa hμε, injOn_quadraticHandleMap hε hμa hμε hμ_pos,
    surjOn_quadraticHandleMap hε hμa hμε hμ hμ₀⟩

/-- The rescaling is continuous on the handle. -/
theorem continuousOn_quadraticHandleMap (hμ : Continuous μ) :
    ContinuousOn (quadraticHandleMap ε μ : Eᵤ × Eₛ → Eᵤ × Eₛ) (quadraticHandle ε μ) := by
  refine ContinuousOn.prodMk ?_ ?_
  · exact ((Continuous.continuousOn (by fun_prop)).inv₀ fun z _ ↦
      (Real.sqrt_pos.2 (by positivity)).ne').smul continuous_fst.continuousOn
  · exact ((Continuous.continuousOn (by fun_prop)).inv₀ fun z hz ↦
      (Real.sqrt_pos.2 (sub_pos_of_mem_quadraticHandle hμa hμε hz)).ne').smul
        continuous_snd.continuousOn

omit [NormedSpace ℝ Eᵤ] [NormedSpace ℝ Eₛ] hε hμa hμε in
/-- The handle is closed. -/
theorem isClosed_quadraticHandle (hμ : Continuous μ) :
    IsClosed (quadraticHandle ε μ : Set (Eᵤ × Eₛ)) := by
  rw [quadraticHandle, ofPred_and, ofPred_and]
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    ((isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop)))

omit hε hμa hμε in
/-- In finite dimensions the handle is compact: it is closed and lies in the ellipsoid
`‖u‖² + 2‖v‖² ≤ 2ε`. -/
theorem isCompact_quadraticHandle [FiniteDimensional ℝ Eᵤ] [FiniteDimensional ℝ Eₛ]
    (hμ : Continuous μ) : IsCompact (quadraticHandle ε μ : Set (Eᵤ × Eₛ)) := by
  refine isCompact_of_isClosed_isBounded (isClosed_quadraticHandle hμ)
    ((isBounded_closedBall (x := (0 : Eᵤ)) (r := √(2 * ε))).prod
      (isBounded_closedBall (x := (0 : Eₛ)) (r := √(2 * ε))) |>.subset fun z hz ↦ ?_)
  simp only [mem_prod, mem_closedBall_zero_iff]
  have h := hz.2.2
  exact ⟨Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.2‖]),
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.1‖])⟩

/-- **Milnor's handle is a product of discs**: the homeomorphism
`TauCeti.quadraticHandleMap` from the handle onto the product of the closed unit balls of `Eᵤ` and
`Eₛ`, that is onto `D^λ × D^(m-λ)`. The first component has norm `1` exactly on the attaching
region (`TauCeti.norm_fst_quadraticHandleMap_eq_one_iff`). -/
def quadraticHandleHomeomorph [FiniteDimensional ℝ Eᵤ] [FiniteDimensional ℝ Eₛ]
    (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) (hμ_pos : ∀ r < 2 * ε, 0 < μ r) :
    (quadraticHandle ε μ : Set (Eᵤ × Eₛ)) ≃ₜ closedBall (0 : Eᵤ) 1 × closedBall (0 : Eₛ) 1 :=
  have : CompactSpace (quadraticHandle ε μ : Set (Eᵤ × Eₛ)) :=
    isCompact_iff_compactSpace.1 (isCompact_quadraticHandle hμ)
  (Continuous.homeoOfEquivCompactToT2 (f := (bijOn_quadraticHandleMap hε hμa hμε hμ hμ₀
    hμ_pos).equiv _) ((continuousOn_quadraticHandleMap hε hμa hμε hμ).mapsToRestrict
      (mapsTo_quadraticHandleMap hε hμa hμε))).trans (Homeomorph.Set.prod _ _)

@[simp]
theorem coe_fst_quadraticHandleHomeomorph [FiniteDimensional ℝ Eᵤ] [FiniteDimensional ℝ Eₛ]
    (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) (hμ_pos : ∀ r < 2 * ε, 0 < μ r)
    (z : (quadraticHandle ε μ : Set (Eᵤ × Eₛ))) :
    ((quadraticHandleHomeomorph hε hμa hμε hμ hμ₀ hμ_pos z).1 : Eᵤ) =
      (quadraticHandleMap ε μ (z : Eᵤ × Eₛ)).1 :=
  (rfl)

@[simp]
theorem coe_snd_quadraticHandleHomeomorph [FiniteDimensional ℝ Eᵤ] [FiniteDimensional ℝ Eₛ]
    (hμ : Continuous μ) (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) (hμ_pos : ∀ r < 2 * ε, 0 < μ r)
    (z : (quadraticHandle ε μ : Set (Eᵤ × Eₛ))) :
    ((quadraticHandleHomeomorph hε hμa hμε hμ hμ₀ hμ_pos z).2 : Eₛ) =
      (quadraticHandleMap ε μ (z : Eᵤ × Eₛ)).2 :=
  (rfl)

omit hμa hμε in
/-- **The attaching region.** On the handle, the first component of the rescaling has norm `1`
exactly on the level `-‖u‖² + ‖v‖² = -ε`, where the handle meets the lower sublevel. -/
theorem norm_fst_quadraticHandleMap_eq_one_iff (z : Eᵤ × Eₛ) :
    ‖(quadraticHandleMap ε μ z).1‖ = 1 ↔ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = -ε := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_fst_quadraticHandleMap_sq hε,
    div_eq_one_iff_eq (by positivity : ‖z.2‖ ^ 2 + ε ≠ 0)]
  constructor <;> intro h <;> linarith

omit hε in
/-- **The top of the handle.** On the handle, the second component of the rescaling has norm `1`
exactly on the level `-‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²) = -ε` of the lowered model. -/
theorem norm_snd_quadraticHandleMap_eq_one_iff (hz : z ∈ quadraticHandle ε μ) :
    ‖(quadraticHandleMap ε μ z).2‖ = 1 ↔
      -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 - μ (‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2) = -ε := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    norm_snd_quadraticHandleMap_sq hμa hμε hz,
    div_eq_one_iff_eq (sub_pos_of_mem_quadraticHandle hμa hμε hz).ne']
  constructor <;> intro h <;> linarith

omit hε in
/-- **The core of the handle.** On the handle, the second component of the rescaling vanishes
exactly on the core `v = 0`, which contains the cell `{‖u‖² ≤ ε, v = 0}`. -/
theorem quadraticHandleMap_snd_eq_zero_iff (hz : z ∈ quadraticHandle ε μ) :
    (quadraticHandleMap ε μ z).2 = 0 ↔ z.2 = 0 := by
  rw [quadraticHandleMap_apply, smul_eq_zero, or_iff_right (inv_ne_zero
    (Real.sqrt_pos.2 (sub_pos_of_mem_quadraticHandle hμa hμε hz)).ne')]

end TauCeti
