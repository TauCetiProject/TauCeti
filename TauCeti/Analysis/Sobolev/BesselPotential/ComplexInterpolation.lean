/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Interpolation of operators on the Hilbert scale of Bessel-potential spaces

Let `E₁` and `E₂` be finite-dimensional real inner product spaces and `H^s = H^{s,2}` Mathlib's
Bessel-potential spaces of functions on `E₁` or `E₂` with values in a complex Hilbert space. This
file proves that the scale `(H^s)_{s ∈ ℝ}` interpolates operators: if a linear map `T` from
Schwartz functions on `E₁` to Schwartz functions on `E₂` is bounded `H^{s₀} → H^{t₀}` with norm
at most `M₀` and `H^{s₁} → H^{t₁}` with norm at most `M₁`, then for `0 ≤ θ ≤ 1` it is bounded
`H^{s_θ} → H^{t_θ}` with norm at most `M₀ ^ (1 - θ) M₁ ^ θ`, where `s_θ = (1 - θ) s₀ + θ s₁`
and `t_θ = (1 - θ) t₀ + θ t₁`.

The proof is Stein's argument with an analytic family of weights. The tool is the Bessel potential
of complex order (`SchwartzMap.besselPotentialCLM`), the Fourier multiplier `J^z` with symbol the
complex power `⟨ξ⟩ ^ z` of the Japanese bracket. The `H^r` norm of `J^z u` is the `H^{r + re z}`
norm of `u` (`SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`), so imaginary orders
act isometrically on every `H^r`, and its dependence on `z` is holomorphic in every `H^r`
(`SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`).

Given Schwartz functions `u` and `v`, the function

`G z = ∫ ⟪J^{d(conj z)} v, T (J^{c(z)} u)⟫`, `c(z) = s_θ - s_z`, `d(z) = t_z - t_θ`,

is entire, bounded on the strip `0 ≤ re z ≤ 1`, and on the two boundary lines the duality of
`H^{-t_j}` and `H^{t_j}` under the `L²` pairing
(`SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm`) bounds it by
`M_j ‖u‖_{H^{s_θ}} ‖v‖_{H^{-t_θ}}`. Hadamard's three-lines theorem then bounds `G θ = ∫ ⟪v, T u⟫`,
and the choice `v = J^{2 t_θ} (T u)` turns this into the norm bound
(`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`). Since Schwartz functions
are dense, `T` then extends to a bounded operator `H^{s_θ} → H^{t_θ}`
(`SchwartzMap.exists_apply_toBesselPotentialSpaceCLM_eq_and_norm_le_rpow_mul_rpow`).

## Main declarations

* `SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`: the interpolation
  inequality.
* `SchwartzMap.exists_apply_toBesselPotentialSpaceCLM_eq_and_norm_le_rpow_mul_rpow`: the
  interpolated operator `H^{s_θ} → H^{t_θ}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §§4.1, 6.4.
* E. M. Stein, *Interpolation of linear operators*, Trans. Amer. Math. Soc. 83 (1956), 482–492.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Complex Complex.HadamardThreeLines
open scoped ENNReal SchwartzMap BesselPotentialSpace InnerProductSpace ComplexConjugate

namespace SchwartzMap

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂]

section Interpolation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- A linear map `T` of Schwartz spaces that is bounded `H^s → H^t` sends a family whose image in
`H^s` is complex differentiable to a family whose image in `H^t` is complex differentiable. -/
private theorem hasDerivAt_toBesselPotentialSpaceCLM_apply {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {s t M : ℝ}
    (hT : ∀ u, ‖toBesselPotentialSpaceCLM t 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖)
    {f : ℂ → 𝓢(E₁, V)} {f' : 𝓢(E₁, V)} {z : ℂ}
    (hf : HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM s 2 (f w))
      (toBesselPotentialSpaceCLM s 2 f') z) :
    HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM t 2 (T (f w)))
      (toBesselPotentialSpaceCLM t 2 (T f')) z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  refine (Asymptotics.IsBigO.of_bound M (.of_forall fun h ↦ ?_)).trans_isLittleO hf
  simpa only [map_sub, map_smul] using hT (f (z + h) - f z - h • f')

/-- For a linear map `T` of Schwartz spaces that is bounded `H^s → H^t`, the pairing
`z ↦ ∫ ⟪J^{a' + b' conj z} v, T (J^{a + b z} u)⟫` along affine families of orders is entire. -/
private theorem differentiable_integral_inner_besselPotentialCLM {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {s t M : ℝ}
    (hT : ∀ u, ‖toBesselPotentialSpaceCLM t 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(E₁, V)) (v : 𝓢(E₂, W)) (a b a' b' : ℂ) :
    Differentiable ℂ fun z ↦ ∫ x,
      ⟪besselPotentialCLM (a' + conj z * b') v x, T (besselPotentialCLM (a + z * b) u) x⟫_ℂ := by
  intro z
  have h1 := (hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM s u (a + z * b)).scomp z
    (((hasDerivAt_id z).mul_const b).const_add a)
  rw [← map_smul] at h1
  have h2 := (hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM (-t) v
    (a' + conj z * b')).scomp (conj z) (((hasDerivAt_id (conj z)).mul_const b').const_add a')
  set eΦ := (BesselPotentialSpace.toLpₗᵢ E₂ W t 2).toContinuousLinearEquiv
  set eΨ := (BesselPotentialSpace.toLpₗᵢ E₂ W (-t) 2).toContinuousLinearEquiv
  obtain ⟨Φ', hΦ⟩ : ∃ Φ', HasDerivAt
      (fun w ↦ (toBesselPotentialSpaceCLM t 2 (T (besselPotentialCLM (a + w * b) u))).toLp) Φ' z :=
    ⟨_, (eΦ.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_toBesselPotentialSpaceCLM_apply hT h1))
      |>.congr_of_eventuallyEq (.of_forall fun w ↦ by simp [eΦ])⟩
  obtain ⟨Ψ', hΨ⟩ : ∃ Ψ', HasDerivAt
      (fun w ↦ (toBesselPotentialSpaceCLM (-t) 2 (besselPotentialCLM (a' + w * b') v)).toLp) Ψ'
        (conj z) :=
    ⟨_, (eΨ.hasFDerivAt.comp_hasDerivAt (conj z) h2).congr_of_eventuallyEq
      (.of_forall fun w ↦ by simp [eΨ])⟩
  refine (hΨ.inner_comp_conj hΦ).differentiableAt.congr_of_eventuallyEq (.of_forall fun w ↦ ?_)
  exact (inner_toLp_toBesselPotentialSpaceCLM_neg t _ _).symm

/-- For a linear map `T` of Schwartz spaces with `‖T u‖_{H^r} ≤ M ‖u‖_{H^s}`, the duality of
`H^{-r}` and `H^r` bounds the pairing `∫ ⟪J^{a' + b' conj z} v, T (J^{a + b z} u)⟫` by
`‖v‖_{H^{-r + a' + b' re z}} M ‖u‖_{H^{s + a + b re z}}`. -/
private theorem norm_integral_inner_besselPotentialCLM_le {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {r s M : ℝ}
    (hT : ∀ u, ‖toBesselPotentialSpaceCLM r 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(E₁, V)) (v : 𝓢(E₂, W)) (a b a' b' : ℝ) (z : ℂ) :
    ‖∫ x, ⟪besselPotentialCLM ((a' : ℂ) + conj z * b') v x,
        T (besselPotentialCLM ((a : ℂ) + z * b) u) x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (-r + (a' + z.re * b')) 2 v‖ *
        (M * ‖toBesselPotentialSpaceCLM (s + (a + z.re * b)) 2 u‖) := by
  have hre : ((a : ℂ) + z * b).re = a + z.re * b := by simp
  have hre' : ((a' : ℂ) + conj z * b').re = a' + z.re * b' := by simp
  refine (norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm r _ _).trans ?_
  rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, hre', ← hre,
    ← norm_toBesselPotentialSpaceCLM_besselPotentialCLM s _ u]
  gcongr
  exact hT _

/-- Under the hypotheses of `norm_integral_inner_besselPotentialCLM_le` with `0 ≤ M`, the pairing
`∫ ⟪J^{a' + b' conj z} v, T (J^{a + b z} u)⟫` is bounded on the strip `0 ≤ re z ≤ 1`. -/
private theorem bddAbove_norm_integral_inner_besselPotentialCLM {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {r s M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ u, ‖toBesselPotentialSpaceCLM r 2 (T u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(E₁, V)) (v : 𝓢(E₂, W)) (a b a' b' : ℝ) :
    BddAbove ((norm ∘ fun z ↦ ∫ x, ⟪besselPotentialCLM ((a' : ℂ) + conj z * b') v x,
      T (besselPotentialCLM ((a : ℂ) + z * b) u) x⟫_ℂ) '' verticalClosedStrip 0 1) := by
  refine ⟨‖toBesselPotentialSpaceCLM (-r + (a' + |b'|)) 2 v‖ *
    (M * ‖toBesselPotentialSpaceCLM (s + (a + |b|)) 2 u‖), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hz0, hz1⟩ : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  refine (norm_integral_inner_besselPotentialCLM_le hT u v a b a' b' z).trans ?_
  have hle_v : -r + (a' + z.re * b') ≤ -r + (a' + |b'|) := by
    nlinarith [le_abs_self b', neg_abs_le b']
  have hle_u : s + (a + z.re * b) ≤ s + (a + |b|) := by
    nlinarith [le_abs_self b, neg_abs_le b]
  rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hle_v,
    ← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM hle_u]
  gcongr
  · exact BesselPotentialSpace.norm_inclusion_apply_le _ _
  · exact BesselPotentialSpace.norm_inclusion_apply_le _ _

/-- **Interpolation on the Hilbert scale of Bessel-potential spaces.** Let `T` be a linear map of
Schwartz spaces with `‖T u‖_{H^{t₀}} ≤ M₀ ‖u‖_{H^{s₀}}` and `‖T u‖_{H^{t₁}} ≤ M₁ ‖u‖_{H^{s₁}}`.
Then for `0 ≤ θ ≤ 1`,
`‖T u‖_{H^{t_θ}} ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖u‖_{H^{s_θ}}`, where `s_θ = (1 - θ) s₀ + θ s₁` and
`t_θ = (1 - θ) t₀ + θ t₁`. -/
theorem norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {s₀ s₁ t₀ t₁ M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ u, ‖toBesselPotentialSpaceCLM t₀ 2 (T u)‖ ≤ M₀ * ‖toBesselPotentialSpaceCLM s₀ 2 u‖)
    (h₁ : ∀ u, ‖toBesselPotentialSpaceCLM t₁ 2 (T u)‖ ≤ M₁ * ‖toBesselPotentialSpaceCLM s₁ 2 u‖)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (u : 𝓢(E₁, V)) :
    ‖toBesselPotentialSpaceCLM ((1 - θ) * t₀ + θ * t₁) 2 (T u)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 u‖ := by
  set sθ := (1 - θ) * s₀ + θ * s₁ with hsθ
  set tθ := (1 - θ) * t₀ + θ * t₁ with htθ
  -- The test function `v = J^{2 tθ} (T u)` realizes the `H^{tθ}` norm of `T u` in the pairing.
  set v : 𝓢(E₂, W) := besselPotentialCLM ((2 * tθ : ℝ) : ℂ) (T u) with hv
  -- The pairing along the analytic families of orders `sθ - s_z` for `u` and `t_z - tθ` for `v`.
  set G : ℂ → ℂ := fun z ↦ ∫ x, ⟪besselPotentialCLM (((t₀ - tθ : ℝ) : ℂ) + conj z * (t₁ - t₀ : ℝ))
    v x, T (besselPotentialCLM (((sθ - s₀ : ℝ) : ℂ) + z * (s₀ - s₁ : ℝ)) u) x⟫_ℂ with hG
  -- At `θ` both orders vanish and `G θ = ‖T u‖²_{H^{tθ}}`.
  have hcθ : ((sθ - s₀ : ℝ) : ℂ) + (θ : ℂ) * (s₀ - s₁ : ℝ) = 0 := by
    simp only [hsθ]
    push_cast
    ring
  have hdθ : ((t₀ - tθ : ℝ) : ℂ) + conj (θ : ℂ) * (t₁ - t₀ : ℝ) = 0 := by
    simp only [Complex.conj_ofReal, htθ]
    push_cast
    ring
  have hvL : (toBesselPotentialSpaceCLM (-tθ) 2 v).toLp =
      (toBesselPotentialSpaceCLM tθ 2 (T u)).toLp := by
    rw [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
      toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, hv,
      besselPotentialCLM_besselPotentialCLM_apply]
    congr 3
    push_cast
    ring
  set N := ‖toBesselPotentialSpaceCLM tθ 2 (T u)‖ with hN
  have hGθ : G θ = ((N ^ 2 : ℝ) : ℂ) := by
    simp only [hG, hcθ, hdθ, besselPotentialCLM_zero, ContinuousLinearMap.id_apply]
    rw [← inner_toLp_toBesselPotentialSpaceCLM_neg tθ, hvL, inner_self_eq_norm_sq_to_K,
      BesselPotentialSpace.norm_toLp_eq, hN]
    norm_cast
  have hvN : ‖toBesselPotentialSpaceCLM (-tθ) 2 v‖ = N := by
    rw [hv, norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
      show -tθ + 2 * tθ = tθ by ring]
  -- Boundary bounds on the two lines.
  set X := ‖toBesselPotentialSpaceCLM sθ 2 u‖
  have ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖G z‖ ≤ N * (M₀ * X) := fun z hz ↦ by
    have hz' : z.re = 0 := hz
    have h := norm_integral_inner_besselPotentialCLM_le h₀ u v (sθ - s₀) (s₀ - s₁) (t₀ - tθ)
      (t₁ - t₀) z
    rw [show -t₀ + (t₀ - tθ + z.re * (t₁ - t₀)) = -tθ by rw [hz']; ring,
      show s₀ + (sθ - s₀ + z.re * (s₀ - s₁)) = sθ by rw [hz']; ring, hvN] at h
    exact h
  have hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖G z‖ ≤ N * (M₁ * X) := fun z hz ↦ by
    have hz' : z.re = 1 := hz
    have h := norm_integral_inner_besselPotentialCLM_le h₁ u v (sθ - s₀) (s₀ - s₁) (t₀ - tθ)
      (t₁ - t₀) z
    rw [show -t₁ + (t₀ - tθ + z.re * (t₁ - t₀)) = -tθ by rw [hz']; ring,
      show s₁ + (sθ - s₀ + z.re * (s₀ - s₁)) = sθ by rw [hz']; ring, hvN] at h
    exact h
  -- Hadamard's three-lines theorem at `θ` gives `N ^ 2 ≤ N (M₀ X) ^ (1 - θ) (M₁ X) ^ θ`.
  have hX0 : 0 ≤ X := norm_nonneg _
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' G (z := θ)
    (by simpa [verticalClosedStrip] using hθ)
    (differentiable_integral_inner_besselPotentialCLM h₀ u v _ _ _ _).diffContOnCl
    (bddAbove_norm_integral_inner_besselPotentialCLM hM₀ h₀ u v _ _ _ _) ha hb
  -- The common factors `N` and `X` come out of the geometric mean of the boundary bounds.
  have hmean : (N * (M₀ * X)) ^ (1 - θ) * (N * (M₁ * X)) ^ θ =
      N * (M₀ ^ (1 - θ) * M₁ ^ θ * X) := by
    rw [Real.mul_rpow_one_sub_mul_mul_rpow (norm_nonneg _), mul_comm M₀, mul_comm M₁,
      Real.mul_rpow_one_sub_mul_mul_rpow hX0, mul_comm X]
  simp only [hGθ, Complex.ofReal_re, Complex.norm_real, hmean, sq, Real.norm_eq_abs,
    abs_mul_self] at h3
  -- Divide by `N`.
  rcases (norm_nonneg _ : 0 ≤ N).eq_or_lt with hN0 | hN0
  · rw [show N = 0 from hN0.symm]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hX0
  · exact le_of_mul_le_mul_left h3 hN0

/-- **Interpolated operators on the Hilbert scale.** Under the hypotheses of
`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`, the linear map `T` of
Schwartz spaces extends to a bounded operator `H^{s_θ} → H^{t_θ}` of norm at most
`M₀ ^ (1 - θ) M₁ ^ θ`. -/
theorem exists_apply_toBesselPotentialSpaceCLM_eq_and_norm_le_rpow_mul_rpow
    {T : 𝓢(E₁, V) →ₗ[ℂ] 𝓢(E₂, W)}
    {s₀ s₁ t₀ t₁ M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ u, ‖toBesselPotentialSpaceCLM t₀ 2 (T u)‖ ≤ M₀ * ‖toBesselPotentialSpaceCLM s₀ 2 u‖)
    (h₁ : ∀ u, ‖toBesselPotentialSpaceCLM t₁ 2 (T u)‖ ≤ M₁ * ‖toBesselPotentialSpaceCLM s₁ 2 u‖)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ S : H^{(1 - θ) * s₀ + θ * s₁}(E₁, V) →L[ℂ] H^{(1 - θ) * t₀ + θ * t₁}(E₂, W),
      (∀ u, S (toBesselPotentialSpaceCLM _ 2 u) = toBesselPotentialSpaceCLM _ 2 (T u)) ∧
        ‖S‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hbd := norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm hM₀ hM₁ h₀ h₁ hθ
  have hdense := denseRange_toBesselPotentialSpaceCLM (E := E₁) (F := V)
    ((1 - θ) * s₀ + θ * s₁) (p := 2) ENNReal.ofNat_ne_top
  refine ⟨((toBesselPotentialSpaceCLM ((1 - θ) * t₀ + θ * t₁) 2).toLinearMap ∘ₗ T).extendOfNorm
    (toBesselPotentialSpaceCLM _ 2).toLinearMap, fun u ↦ ?_, ?_⟩
  · exact LinearMap.extendOfNorm_eq hdense ⟨_, hbd⟩ u
  · exact LinearMap.opNorm_extendOfNorm_le hdense
      (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hbd

end Interpolation

end SchwartzMap
