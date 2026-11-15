/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Fourier.NonstationaryPhase.Basic
import TauCeti.Analysis.Normed.Module.Cone
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Microlocal decay against a nonlinear phase

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, and let `Φ : E → E'` be smooth on `Ω`. The localized Fourier transform `T (ψ e_ξ)` pairs
`T` with a cutoff `ψ` modulated by the linear phase `x ↦ ⟪x, ξ⟫`. Pushforwards and pullbacks along
`Φ` lead instead to pairings `T (ψ 𝐞 (-⟪Φ ·, η⟫))` with the nonlinear phase `x ↦ ⟪Φ x, η⟫`, whose
gradient is `Φ'(x)ᵀ η`. This file proves that these pairings decay rapidly in `η` wherever the
gradient points into a direction in which `T` is microlocally smooth
(`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_decay_phase`): if `T` is microlocally
smooth at `(x₀, Φ'(x₀)ᵀ η₀)` and `Φ'(x₀)ᵀ η₀ ≠ 0`, then `T (ψ 𝐞 (-⟪Φ ·, η⟫))` decays rapidly
for `η` in an open cone around `η₀`, for every cutoff `ψ` supported near `x₀`.

## The argument

Take a cutoff `χ` equal to one near `x₀` and a lattice `L` none of whose nonzero translates of the
support of `χ` meet it. Expanding `ψ 𝐞 (-⟪Φ ·, η⟫)` in its Fourier series along `L`
(`Distribution.hasSum_fourier_mul_localFourier`) gives

`T (ψ 𝐞 (-⟪Φ ·, η⟫)) = ∑ m : L^∨, (covolume L)⁻¹ c(η, m) T (χ e_(-m))`,

where `c(η, m) = ∫ 𝐞 (-(⟪Φ x, η⟫ + ⟪x, m⟫)) ψ x dx`. The phase `⟪Φ x, η⟫ + ⟪x, m⟫` has gradient
`Φ'(x)ᵀ η + m`. For `η` near the ray of `η₀` and `x` near `x₀`, `Φ'(x)ᵀ η` lies in a small cone
around `Φ'(x₀)ᵀ η₀`, so either `-m` lies in a slightly larger cone `Γ₀` with `‖m‖` comparable to
`‖η‖`, where `T (χ e_(-m))` decays rapidly, or the gradient is at least a fixed multiple of
`‖η‖ + ‖m‖`, and `c(η, m)` decays rapidly in `(η, m)` by non-stationary phase
(`TauCeti.exists_one_add_norm_pow_mul_norm_integral_le`). In both cases the terms are bounded by
`(1 + ‖η‖) ^ (-N) (1 + ‖m‖) ^ (-r)` with `r` larger than the rank of `L`, and the series sums to a
bound `(1 + ‖η‖) ^ (-N)`.

## Main results

* `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_decay_phase`: rapid decay of
  `T (ψ 𝐞 (-⟪Φ ·, η⟫))` in a cone around `η₀`, for cutoffs `ψ` supported near `x₀`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proofs of Theorems 8.2.4 and 8.2.13.
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology RealInnerProductSpace InnerProduct ContDiff FourierTransform

namespace Distribution

variable {E E' : Type*}

/-- The non-stationarity estimate: if `‖ζ‖ ≥ a s` and either `ζ + m` is not within `c₁ ‖ζ‖` of
`0`, or `m` is small compared with `s`, then `‖ζ + m‖` controls `s + ‖m‖`. -/
private theorem mul_add_le_of_cone [NormedAddCommGroup E] {ζ m : E} {s a c₁ : ℝ} (ha : 0 < a)
    (hc₁ : 0 < c₁) (hζ : a * s ≤ ‖ζ‖) (h : c₁ * ‖ζ‖ < ‖ζ + m‖ ∨ 4 * ‖m‖ < a * s) :
    a * c₁ * (s + ‖m‖) ≤ 2 * (1 + a) * (1 + c₁) * ‖ζ + m‖ := by
  have t1 : ‖m‖ ≤ ‖ζ + m‖ + ‖ζ‖ := by simpa using norm_sub_le (ζ + m) ζ
  have t2 : ‖ζ‖ ≤ ‖ζ + m‖ + ‖m‖ := by simpa using norm_sub_le (ζ + m) m
  have hw := norm_nonneg (ζ + m)
  have hm := norm_nonneg m
  rcases h with h | h
  · have h1 : a * c₁ * s ≤ ‖ζ + m‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hζ hc₁.le]
    have h2 : a * c₁ * ‖m‖ ≤ a * c₁ * ‖ζ + m‖ + a * ‖ζ + m‖ := by
      nlinarith [mul_le_mul_of_nonneg_left t1 (mul_nonneg ha.le hc₁.le),
        mul_le_mul_of_nonneg_left h.le ha.le]
    nlinarith [mul_nonneg hc₁.le hw, mul_nonneg (mul_nonneg ha.le hc₁.le) hw,
      mul_nonneg ha.le hw]
  · have h1 : 3 * (a * s) ≤ 4 * ‖ζ + m‖ := by linarith
    have h2 : 3 * ‖m‖ ≤ ‖ζ + m‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hc₁.le, mul_le_mul_of_nonneg_left h2
      (mul_nonneg ha.le hc₁.le), mul_nonneg hc₁.le hw, mul_nonneg (mul_nonneg ha.le hc₁.le) hw,
      mul_nonneg ha.le hw]

/-- The bound on one term of the lattice series for `T (ψ 𝐞 (-⟪Φ ·, η⟫))`, as an inequality between
real numbers: `s = ‖η‖`, `M = ‖m‖`, `f` is the size of the Fourier coefficient and `φ` that of the
localized Fourier transform of `T` at `-m`. Either the coefficient decays (`P = ‖(η, m)‖`), or
`‖η‖ ≤ b ‖m‖` and the localized Fourier transform decays. -/
private theorem one_add_pow_mul_mul_mul_le {s M P f φ A₀ b C₀ C₁ C₂ : ℝ} {N k r : ℕ}
    (hM : 0 ≤ M) (hf : 0 ≤ f) (hφ0 : 0 ≤ φ) (hA₀ : 0 ≤ A₀) (hb : 0 ≤ b)
    (hφ : φ ≤ |C₀| * (1 + M) ^ k)
    (h : (0 ≤ s ∧ s ≤ P ∧ M ≤ P ∧ (1 + P) ^ (N + k + r) * f ≤ |C₁|) ∨
      (0 ≤ s ∧ f ≤ A₀ ∧ s ≤ b * M ∧ (1 + M) ^ (N + r) * φ ≤ |C₂|)) :
    (1 + s) ^ N * f * φ * (1 + M) ^ r ≤ |C₀| * |C₁| + A₀ * (1 + b) ^ N * |C₂| := by
  rcases h with ⟨hs, hsP, hMP, h1⟩ | ⟨hs, hfA, hsM, h2⟩
  · have hle : (1 + s) ^ N * (1 + M) ^ (k + r) ≤ (1 + P) ^ (N + k + r) := by
      rw [add_assoc, pow_add (1 + P) N]
      exact mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) _)
        (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity)
        (pow_nonneg (by linarith) _)
    calc (1 + s) ^ N * f * φ * (1 + M) ^ r
        ≤ (1 + s) ^ N * f * (|C₀| * (1 + M) ^ k) * (1 + M) ^ r := by gcongr
      _ = |C₀| * (((1 + s) ^ N * (1 + M) ^ (k + r)) * f) := by ring
      _ ≤ |C₀| * ((1 + P) ^ (N + k + r) * f) := by gcongr
      _ ≤ |C₀| * |C₁| := by gcongr
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hs' : 1 + s ≤ (1 + b) * (1 + M) := by nlinarith
    calc (1 + s) ^ N * f * φ * (1 + M) ^ r
        ≤ ((1 + b) * (1 + M)) ^ N * A₀ * φ * (1 + M) ^ r := by gcongr
      _ = A₀ * (1 + b) ^ N * ((1 + M) ^ (N + r) * φ) := by rw [mul_pow, pow_add]; ring
      _ ≤ A₀ * (1 + b) ^ N * |C₂| := by gcongr
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E']
  [InnerProductSpace ℝ E']

/-- The phase `⟪Φ x, η⟫ + ⟪x, m⟫` of the Fourier coefficients of a cutoff modulated along `Φ`, as a
linear form in `(η, m)`. -/
private def phase (Φ : E → E') (x : E) : E' × E →L[ℝ] ℝ :=
  (innerSL ℝ (Φ x)).comp (ContinuousLinearMap.fst ℝ E' E) +
    (innerSL ℝ x).comp (ContinuousLinearMap.snd ℝ E' E)

private theorem phase_apply (Φ : E → E') (x : E) (p : E' × E) :
    phase Φ x p = ⟪Φ x, p.1⟫ + ⟪x, p.2⟫ := by
  simp [phase]

private theorem contDiff_phase [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {Φ : E → E'}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (phase Φ) := by
  rw [contDiff_clm_apply_iff]
  intro p
  simp only [phase_apply]
  exact (hΦ.inner ℝ contDiff_const).add (contDiff_id.inner ℝ contDiff_const)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- The gradient of the phase `x ↦ ⟪Φ x, η⟫ + ⟪x, m⟫` is `Φ'(x)ᵀ η + m`. -/
private theorem norm_fderiv_phase {Φ : E → E'} {x : E} (hΦ : DifferentiableAt ℝ Φ x)
    (p : E' × E) :
    ‖fderiv ℝ (fun y ↦ phase Φ y p) x‖ = ‖((fderiv ℝ Φ x)†) p.1 + p.2‖ := by
  have h : HasFDerivAt (fun y ↦ phase Φ y p) (innerSL ℝ (((fderiv ℝ Φ x)†) p.1 + p.2)) x := by
    have h1 := ((innerSL ℝ p.1).hasFDerivAt.comp x hΦ.hasFDerivAt).add
      (innerSL ℝ p.2).hasFDerivAt
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)).congr_fderiv ?_
    · simp [phase_apply, real_inner_comm]
    · ext v
      simp [ContinuousLinearMap.adjoint_inner_left]
  rw [h.fderiv, innerSL_apply_norm]

/-- The phase `⟪Φ y, η⟫ + ⟪y, m⟫` is non-stationary at `x`, uniformly in `(η, m)`, when
`Φ'(x)ᵀ η` is at least `a ‖η‖` and lies in `Γ₀` with a ball of radius `c₁ ‖Φ'(x)ᵀ η‖`, and either
`-m ∉ Γ₀` or `m` is small compared with `η`. -/
private theorem mul_norm_le_norm_fderiv_phase {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) {Γ₀ : Set E}
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) {x : E} {η : E'} {m : E}
    (hgeom : Metric.closedBall (((fderiv ℝ Φ x)†) η) (c₁ * ‖((fderiv ℝ Φ x)†) η‖) ⊆ Γ₀ ∧
      a * ‖η‖ ≤ ‖((fderiv ℝ Φ x)†) η‖) (hm : -m ∉ Γ₀ ∨ 4 * ‖m‖ < a * ‖η‖) :
    a * c₁ / (2 * (1 + a) * (1 + c₁)) * ‖((η, m) : E' × E)‖ ≤
      ‖fderiv ℝ (fun y ↦ phase Φ y (η, m)) x‖ := by
  rw [norm_fderiv_phase ((hΦ.differentiable (by simp)) x)]
  have key := mul_add_le_of_cone (m := m) ha hc₁ hgeom.2 (hm.imp_left fun hm ↦ ?_)
  · have hp' : ‖((η, m) : E' × E)‖ ≤ ‖η‖ + ‖m‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hp' (mul_nonneg ha.le hc₁.le)]
  · by_contra hle
    rw [not_lt] at hle
    refine hm (hgeom.1 ?_)
    rwa [Metric.mem_closedBall, dist_eq_norm, neg_sub_left, norm_neg]

variable {Ω : Opens E}

omit [FiniteDimensional ℝ E'] in
/-- The Fourier coefficients of a cutoff modulated along `Φ` are oscillatory integrals with phase
`⟪Φ x, η⟫ + ⟪x, m⟫`. -/
private theorem fourier_eq_integral_phase [MeasurableSpace E] [BorelSpace E] {Φ : E → E'}
    {ψ : E → ℂ} {g : E' → E → ℂ} (hg : ∀ η x, g η x = ψ x * 𝐞 (-⟪Φ x, η⟫)) (η : E') (m : E) :
    𝓕 (g η) m = ∫ x, 𝐞 (-phase Φ x (η, m)) • ψ x := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [hg, phase_apply, Circle.smul_def, neg_add, AddChar.map_add_eq_mul,
    Circle.coe_mul, smul_eq_mul]
  ring

/-- **The core estimate.** Let `χ = 1` on the support of `ψ`, let `L` be a lattice adapted to the
support of `χ`, and let `T` have localized Fourier transform with cutoff `χ` rapidly decreasing on
`Γ₀`. Suppose that for `x` in the support of `ψ` and `η ∈ Γ`, the covector `Φ'(x)ᵀ η` is at least
`a ‖η‖` and lies in `Γ₀` with a ball of radius `c₁ ‖Φ'(x)ᵀ η‖`. Then `T (ψ 𝐞 (-⟪Φ ·, η⟫))` decays
rapidly for `η ∈ Γ`. Expand `ψ 𝐞 (-⟪Φ ·, η⟫)` in its Fourier series along `L`: the coefficient of
the mode `m` is an oscillatory integral with phase `⟪Φ x, η⟫ + ⟪x, m⟫`, which decays rapidly
in `(η, m)` unless `-m` is near `Φ'(x)ᵀ η`; there the localized Fourier transform of `T` at `-m`
decays instead. -/
private theorem exists_decay_complexPairing_of_cone [MeasurableSpace E] [BorelSpace E]
    {T : 𝓓'(Ω, ℂ)} {χ : 𝓓(Ω, ℂ)}
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ x ∈ tsupport χ, ∀ ℓ ∈ L, x + ℓ ∈ tsupport χ → ℓ = 0)
    {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) {ψ : 𝓓(Ω, ℂ)} (hχψ : EqOn (χ : E → ℂ) 1 (support ψ))
    {g : E' → 𝓓(Ω, ℂ)} (hg : ∀ η x, g η x = ψ x * 𝐞 (-⟪Φ x, η⟫)) {Γ₀ : Set E}
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ₀, (1 + ‖ζ‖) ^ N * ‖T.localFourier χ ζ‖ ≤ C)
    {Γ : Set E'} {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁)
    (hgeom : ∀ x ∈ tsupport ψ, ∀ η ∈ Γ,
      Metric.closedBall (((fderiv ℝ Φ x)†) η) (c₁ * ‖((fderiv ℝ Φ x)†) η‖) ⊆ Γ₀ ∧
        a * ‖η‖ ≤ ‖((fderiv ℝ Φ x)†) η‖) (N : ℕ) :
    ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.complexPairing (g η)‖ ≤ C := by
  set r := Module.finrank ℤ (ZLattice.dual L) + 1
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T χ
  obtain ⟨C₂, hC₂⟩ := hdecay (N + r)
  -- The Fourier coefficients of `g η` are oscillatory integrals with phase `phase Φ`.
  have hcoef (η : E') (m : E) : 𝓕 (g η : E → ℂ) m = ∫ x, 𝐞 (-phase Φ x (η, m)) • ψ x :=
    fourier_eq_integral_phase (g := fun η ↦ g η) hg η m
  have hEq (η : E') : EqOn (χ : E → ℂ) 1 (support (g η)) := fun x hx ↦
    hχψ fun h0 ↦ hx (by simp [hg, h0])
  -- Away from the stationary set `-m ≈ Φ'(x)ᵀ η`, the coefficients decay rapidly in `(η, m)`.
  set S : Set (E' × E) := {p | p.1 ∈ Γ ∧ (-p.2 ∉ Γ₀ ∨ 4 * ‖p.2‖ < a * ‖p.1‖)}
  have hc : 0 < a * c₁ / (2 * (1 + a) * (1 + c₁)) := by positivity
  have hS (p : E' × E) (hp : p ∈ S) (x : E) (hx : x ∈ tsupport ψ) :
      a * c₁ / (2 * (1 + a) * (1 + c₁)) * ‖p‖ ≤ ‖fderiv ℝ (fun y ↦ phase Φ y p) x‖ :=
    mul_norm_le_norm_fderiv_phase hΦ ha hc₁ (hgeom x hx p.1 hp.1) hp.2
  obtain ⟨C₁, hC₁⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_integral_le (contDiff_phase hΦ)
    ψ.contDiff ψ.hasCompactSupport volume hc hS (N + k + r)
  -- Sum the bounds `(1 + ‖η‖) ^ (-N) D (1 + ‖m‖) ^ (-r)` on the terms of the lattice series.
  refine ZLattice.exists_one_add_norm_pow_mul_norm_le_of_forall_hasSum (ZLattice.dual L) (r := r)
    (fun η _ ↦ hasSum_fourier_mul_localFourier T χ L hL (hEq η)) (Nat.lt_succ_self _)
    (D := ‖((ZLattice.covolume L : ℂ))⁻¹‖ *
      (|C₀| * |C₁| + (∫ x, ‖ψ x‖) * (1 + 4 / a) ^ N * |C₂|)) fun η hη m ↦ ?_
  rw [hcoef, norm_mul, norm_mul, le_mul_inv_iff₀ (by positivity)]
  have hcase : ((0 ≤ ‖η‖ ∧ ‖η‖ ≤ ‖((η, (m : E)) : E' × E)‖ ∧ ‖(m : E)‖ ≤ ‖((η, (m : E)) : E' × E)‖ ∧
      (1 + ‖((η, (m : E)) : E' × E)‖) ^ (N + k + r) *
        ‖∫ x, 𝐞 (-phase Φ x (η, (m : E))) • ψ x‖ ≤ |C₁|) ∨
      (0 ≤ ‖η‖ ∧ ‖∫ x, 𝐞 (-phase Φ x (η, (m : E))) • ψ x‖ ≤ ∫ x, ‖ψ x‖ ∧
        ‖η‖ ≤ 4 / a * ‖(m : E)‖ ∧
        (1 + ‖(m : E)‖) ^ (N + r) * ‖T.localFourier χ (-(m : E))‖ ≤ |C₂|)) := by
    by_cases hp : ((η, (m : E)) : E' × E) ∈ S
    · exact Or.inl ⟨norm_nonneg _, norm_fst_le ((η, (m : E)) : E' × E),
        norm_snd_le ((η, (m : E)) : E' × E), (hC₁ _ hp).trans (le_abs_self _)⟩
    · -- Near the stationary set, `-m ∈ Γ₀` and `‖η‖ ≤ (4 / a) ‖m‖`.
      simp only [S, mem_ofPred_eq, not_and, not_or, not_not, not_lt] at hp
      obtain ⟨hmΓ, hma⟩ := hp hη
      refine Or.inr ⟨norm_nonneg _, (norm_integral_le_integral_norm _).trans_eq (by simp), ?_,
        by simpa using (hC₂ _ hmΓ).trans (le_abs_self _)⟩
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith
  have hFm : ‖T.localFourier χ (-(m : E))‖ ≤ |C₀| * (1 + ‖(m : E)‖) ^ k :=
    (hF _).trans (by rw [norm_neg]; gcongr; exact le_abs_self _)
  have hf0 := norm_nonneg (∫ x, 𝐞 (-phase Φ x (η, (m : E))) • ψ x)
  have hφ0 := norm_nonneg (T.localFourier χ (-(m : E)))
  have hA₀ : 0 ≤ ∫ x, ‖ψ x‖ := integral_nonneg fun _ ↦ norm_nonneg _
  generalize ‖∫ x, 𝐞 (-phase Φ x (η, (m : E))) • ψ x‖ = f at hcase hf0 ⊢
  generalize ‖T.localFourier χ (-(m : E))‖ = φ at hcase hFm hφ0 ⊢
  have key := one_add_pow_mul_mul_mul_le (norm_nonneg (m : E)) hf0 hφ0 hA₀
    (div_pos four_pos ha).le hFm hcase
  have hc0 := norm_nonneg ((ZLattice.covolume L : ℂ))⁻¹
  generalize ‖((ZLattice.covolume L : ℂ))⁻¹‖ = c at hc0 ⊢
  calc (1 + ‖η‖) ^ N * (c * f * φ) * (1 + ‖(m : E)‖) ^ r
      = c * ((1 + ‖η‖) ^ N * f * φ * (1 + ‖(m : E)‖) ^ r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hc0

/-- **Decay against a nonlinear phase.** Let `Φ` be smooth on `Ω` and let `T` be microlocally
smooth at `(x₀, Φ'(x₀)ᵀ η₀)`, where `Φ'(x₀)ᵀ η₀ ≠ 0`. Then there are a neighbourhood `U` of `x₀`
and an open cone `Γ` containing `η₀` such that for every cutoff `ψ` supported in `U`, the pairing
of `T` with the modulated cutoff `ψ 𝐞 (-⟪Φ ·, η⟫)` decays rapidly for `η ∈ Γ`. For linear `Φ`
these pairings are localized Fourier transforms of `T`; in general they are the localized Fourier
transforms of pushforwards and pullbacks along `Φ`. -/
theorem IsMicrolocallySmoothAt.exists_nhds_cone_decay_phase {T : 𝓓'(Ω, ℂ)} {Φ : E → E'}
    (hΦ : ContDiffOn ℝ ∞ Φ Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) {η₀ : E'}
    (hη₀ : ((fderiv ℝ Φ x₀)†) η₀ ≠ 0)
    (h : T.IsMicrolocallySmoothAt x₀ (((fderiv ℝ Φ x₀)†) η₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set E', IsOpen Γ ∧ η₀ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ (ψ : 𝓓(Ω, ℂ)) (g : E' → 𝓓(Ω, ℂ)), tsupport ψ ⊆ U →
        (∀ η x, g η x = ψ x * 𝐞 (-⟪Φ x, η⟫)) →
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.complexPairing (g η)‖ ≤ C := by
  borelize E
  -- Cones around `Φ'(x₀)ᵀ η₀` on which `T` decays, with room to spare, transported back to a cone
  -- `Γ` around `η₀` by `Φ'(x)ᵀ` for `x` near `x₀`.
  obtain ⟨U₀, hU₀, Γ₀, hΓ₀, hξΓ₀, hcone₀, hdecay₀⟩ := h.exists_nhds_cone
  obtain ⟨Γ₁, hΓ₁, hξΓ₁, hcone₁, c₁, hc₁, hΓ₁₀⟩ := hΓ₀.exists_cone_closedBall_subset hcone₀ hξΓ₀
  obtain ⟨a, ha, U₁, hU₁, Γ, hΓo, hηΓ, hcone, hgeom⟩ :=
    TauCeti.exists_cone_forall_mem_of_continuousAt
      (ContinuousLinearMap.adjoint.continuous.continuousAt.comp
        ((hΦ.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).continuousAt
          (Ω.isOpen.mem_nhds hx₀))) hη₀ hΓ₁ hcone₁ hξΓ₁
  -- A cutoff `χ₀` equal to one on a closed ball `K` around `x₀`, supported in `U₀ ∩ U₁ ∩ Ω`.
  obtain ⟨V, hVsub, hVo, hx₀V⟩ :=
    mem_nhds_iff.1 (inter_mem (inter_mem hU₀ hU₁) (Ω.isOpen.mem_nhds hx₀))
  obtain ⟨K, hKc, hKn, hKV⟩ : ∃ K, IsCompact K ∧ K ∈ 𝓝 x₀ ∧ K ⊆ V := by
    obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hVo x₀ hx₀V
    exact ⟨Metric.closedBall x₀ (ρ / 2), isCompact_closedBall _ _,
      Metric.closedBall_mem_nhds _ (by linarith),
      (Metric.closedBall_subset_ball (by linarith)).trans hρV⟩
  obtain ⟨χ₀, -, hχ₀1, hχ₀V⟩ :=
    exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤) hKc hVo hKV fun y hy ↦ (hVsub hy).2
  set χc : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ₀
  have hχc (y : E) : χc y = χ₀ y := by simp [χc]
  have hχcV : tsupport χc ⊆ V := by
    rw [show (χc : E → ℂ) = Complex.ofReal ∘ χ₀ from funext hχc]
    exact (tsupport_comp_subset Complex.ofReal_zero _).trans hχ₀V
  -- A smooth map `Φ'` on all of `E` equal to `Φ` near `K`.
  set Φ' : E → E' := fun x ↦ χ₀ x • Φ x
  have hΦ' : ContDiff ℝ ∞ Φ' :=
    hΦ.contDiff_smul_of_tsupport_subset Ω.isOpen χ₀.contDiff.contDiffOn χ₀.tsupport_subset
  have hΦ'K (x : E) (hx : x ∈ K) : Φ' =ᶠ[𝓝 x] Φ :=
    (hχ₀1.filter_mono (nhds_le_nhdsSet hx)).mono fun y hy ↦ by simp [Φ', hy]
  -- A lattice adapted to the support of `χc`.
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χc.hasCompactSupport.isCompact.isBounded
  refine ⟨K, hKn, Γ, hΓo, hηΓ, hcone, fun ψ g hψ hg N ↦ ?_⟩
  -- On the support of `ψ`, `Φ'` agrees with `Φ` to first order.
  have hg' (η : E') (x : E) : g η x = ψ x * 𝐞 (-⟪Φ' x, η⟫) := by
    by_cases hx : ψ x = 0
    · simp [hg, hx]
    rw [hg, (hΦ'K x (hψ (subset_tsupport _ hx))).self_of_nhds]
  refine exists_decay_complexPairing_of_cone hL hΦ' (fun x hx ↦ ?_) hg'
    (hdecay₀ χc (hχcV.trans fun y hy ↦ (hVsub hy).1.1)) ha hc₁ (fun x hx η hη ↦ ?_) N
  · simp [hχc, hχ₀1.self_of_nhdsSet x (hψ (subset_tsupport _ hx))]
  · have hxK := hψ hx
    rw [(hΦ'K x hxK).fderiv_eq]
    exact ⟨hΓ₁₀ _ (hgeom x (hVsub (hKV hxK)).1.2 η hη).1, (hgeom x (hVsub (hKV hxK)).1.2 η hη).2⟩

end Distribution
