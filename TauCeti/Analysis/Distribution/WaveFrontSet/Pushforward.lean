/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Fourier.NonstationaryPhase.Parametric
import TauCeti.Analysis.Normed.Module.Cone

/-!
# The wave front set of a pushforward along a smooth map

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, and let `χ` be a test function on `Ω`. For a map `Φ : E → E'` smooth on `Ω`, the
pushforward `Φ_* (χ T)` is the distribution `f ↦ T (χ (f ∘ Φ))` on an open set `Ω'` of `E'`
(`Distribution.cutoffPushforwardCLM`); when `χ` is equal to one near the support of `T`, which is
then compact, it is the pushforward `Φ_* T`, and for a projection it is integration over the
fibres. This file proves Hörmander's bound for its wave front set:

`WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, (DΦ x)ᵀ η = 0 or (x, (DΦ x)ᵀ η) ∈ WF(T)}`.

The localized Fourier transform of `Φ_* (χ T)` with cutoff `f` at `η` pairs `T` with
`ψ (e_η ∘ Φ)`, where `ψ = χ (f ∘ Φ)` and `e_η` is the Fourier atom of `E'`. For a linear map `A`
the atom `e_η ∘ A` is the atom of `E` at `Aᵀ η` (`Distribution.localFourier_cutoffPushforwardCLM`).
For a nonlinear map it is not an atom, and near a point `x₀` the argument runs as follows. Let
`φ` be a cutoff equal to one near `x₀` such that `η' ↦ T (φ e_η')` decays rapidly in an open cone
`Γ` around `(DΦ x₀)ᵀ η`. Expanding `ψ (e_η ∘ Φ)` in a Fourier series on the support of `φ`
gives (`Distribution.hasSum_fourier_mul_localFourier`)

`T (ψ (e_η ∘ Φ)) = ∑ m, c 𝓕(ψ (e_η ∘ Φ))(m) T (φ e_(-m))`

over a lattice. The coefficient `𝓕(ψ (e_η ∘ Φ))(m)` is an oscillatory integral of `ψ` with phase
`x ↦ -(⟪m, x⟫ + ⟪η, Φ x⟫)`, whose gradient `-(m + (DΦ x)ᵀ η)` vanishes only when `-m` is close to
`(DΦ x)ᵀ η`. For `η` in a small cone around the original direction and `x` near `x₀`, either `-m`
lies in `Γ` and is comparable with `η`, where `T (φ e_(-m))` decays rapidly, or the phase has no
critical point, and non-stationary phase for the compact family of normalized phases
(`TauCeti.exists_abs_pow_mul_norm_integral_fourierChar_smul_le`) makes the coefficient decay
rapidly in `‖m‖ + ‖η‖`, against the polynomial growth of `T (φ e_(-m))`. Over a point `y`, the
local decay statements are patched along the compact set `supp χ ∩ supp T ∩ Φ⁻¹ {y}`
(`Distribution.exists_isOpen_cone_forall_decay_of_forall_mem_nhds`), and a cutoff `f` around `y`
pulls back to a cutoff supported near that set.

The covectors with `(DΦ x)ᵀ η = 0` cannot be omitted, even for smooth `T`: along a constant map
with value `c` the pushforward of `T` is the multiple `T χ` of the point mass at `c`, and when
`T χ ≠ 0` its wave front set is `{c} × (E' \ {0})`
(`Distribution.waveFrontSet_cutoffPushforwardCLM_const`). When the differentials of `Φ` are
surjective, their transposes are injective and these covectors do not occur.

## Main results

* `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: if `(DΦ x)ᵀ η ≠ 0` and `T` is
  microlocally smooth at `(x, (DΦ x)ᵀ η)` for every `x ∈ supp χ ∩ supp T` with `Φ x = y`, then
  `Φ_* (χ T)` is microlocally smooth at `(y, η)`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front bound above.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: when the differentials
  of `Φ` are surjective on `supp χ ∩ supp T`,
  `WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, (x, (DΦ x)ᵀ η) ∈ WF(T)}`.
* `Distribution.localFourier_cutoffPushforwardCLM`: for a linear map `A`, localized Fourier
  transforms of `A_* T` are localized Fourier transforms of `T` at the transposed frequency.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: the pushforward along a constant map
  with value `c` has wave front set `{c} × (E' \ {0})` whenever `T χ ≠ 0`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward) and Theorem 7.7.1
  (non-stationary phase).
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct ContDiff FourierTransform

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω' : Opens E'}

section Smooth

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- The test function `ψ (e_η ∘ Φ)`: a test function times the Fourier atom `e_η` of `E'` pulled
back along a smooth map `Φ`. -/
private def pullbackAtom {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (ψ : 𝓓(Ω, ℂ)) (η : E') : 𝓓(Ω, ℂ) :=
  bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) ((TauCeti.contDiff_fourierAtom η).comp hΦ) ψ

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
private theorem pullbackAtom_apply {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (ψ : 𝓓(Ω, ℂ)) (η : E')
    (x : E) : pullbackAtom hΦ ψ η x = ψ x * TauCeti.fourierAtom η (Φ x) := by
  simp only [pullbackAtom, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', Function.comp_apply]

/-- The pairing `T (ψ (e_η ∘ Φ))` of `T` with a test function times the Fourier atom `e_η` of `E'`
pulled back along a smooth map `Φ`. For `Φ` the identity it is the localized Fourier transform. -/
private def pullbackFourier (T : 𝓓'(Ω, ℂ)) {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (ψ : 𝓓(Ω, ℂ))
    (η : E') : ℂ :=
  T.complexPairing (pullbackAtom hΦ ψ η)

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
private theorem pullbackFourier_add (T : 𝓓'(Ω, ℂ)) {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ)
    (ψ ψ' : 𝓓(Ω, ℂ)) (η : E') :
    pullbackFourier T hΦ (ψ + ψ') η = pullbackFourier T hΦ ψ η + pullbackFourier T hΦ ψ' η := by
  simp only [pullbackFourier, pullbackAtom, map_add]

omit [FiniteDimensional ℝ E'] in
private theorem pullbackFourier_eq_zero_of_disjoint {T : 𝓓'(Ω, ℂ)} {Φ : E → E'}
    (hΦ : ContDiff ℝ ∞ Φ) {ψ : 𝓓(Ω, ℂ)} (h : Disjoint (tsupport ψ) (dsupport T)) (η : E') :
    pullbackFourier T hΦ ψ η = 0 :=
  complexPairing_eq_zero_of_disjoint_dsupport T
    (h.mono_left (tsupport_bilinLeftCLM_subset _ _ ψ))

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- The localized Fourier transform of the pushforward `Φ_* (χ T)` along a smooth map pairs `T`
with the cutoff `χ (f ∘ Φ)` times the Fourier atom pulled back along `Φ`. -/
private theorem localFourier_cutoffPushforwardCLM_eq_pullbackFourier {Φ : E → E'}
    (hΦ : ContDiff ℝ ∞ Φ) (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω', ℂ)) (η : E') :
    (cutoffPushforwardCLM χ Φ hΦ.contDiffOn T : 𝓓'(Ω', ℂ)).localFourier f η =
      pullbackFourier T hΦ (cutoffCompCLM χ Φ hΦ.contDiffOn f) η := by
  rw [localFourier_def, complexPairing_cutoffPushforwardCLM, pullbackFourier]
  congr 1
  ext x
  simp [pullbackAtom_apply, mul_assoc]

/-- Near a point `x₀` at which `(DΦ x₀)ᵀ η` is a nonzero point of an open cone `Γ`, the
transposed differentials map a whole open cone `Γ'` around `η` into `Γ`, with
`‖η'‖ ≤ a ‖(DΦ x)ᵀ η'‖`, for all `x` in a closed ball around `x₀` inside a given neighbourhood. -/
private theorem exists_closedBall_cone_adjoint_fderiv_mem {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ)
    {x₀ : E} {η : E'} {Γ : Set E} (hΓ : IsOpen Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ)
    (hη : ((fderiv ℝ Φ x₀)†) η ∈ Γ) (hη0 : ((fderiv ℝ Φ x₀)†) η ≠ 0) {U : Set E} (hU : U ∈ 𝓝 x₀) :
    ∃ ρ > 0, closedBall x₀ ρ ⊆ U ∧ ∃ Γ' : Set E', IsOpen Γ' ∧ η ∈ Γ' ∧
      (∀ t : ℝ, 0 < t → ∀ v ∈ Γ', t • v ∈ Γ') ∧ ∃ a > 0, ∀ x ∈ closedBall x₀ ρ, ∀ v ∈ Γ',
        ((fderiv ℝ Φ x)†) v ∈ Γ ∧ ‖v‖ ≤ a * ‖((fderiv ℝ Φ x)†) v‖ := by
  set F : E × E' → E := fun p => ((fderiv ℝ Φ p.1)†) p.2
  have hF : Continuous F := (ContinuousLinearMap.adjoint.continuous.comp
    ((hΦ.continuous_fderiv (by simp)).comp continuous_fst)).clm_apply continuous_snd
  set ξ₀ := F (x₀, η)
  have hξ₀ : 0 < ‖ξ₀‖ := norm_pos_iff.2 hη0
  have hηpos : 0 < ‖η‖ := norm_pos_iff.2 fun h => hη0 (by simp [h])
  -- An open neighbourhood of `(x₀, η)` on which `F` lands in `Γ` with a norm bound.
  set O : Set (E × E') := {p | F p ∈ Γ ∧ ‖p.2‖ * ‖ξ₀‖ < 2 * ‖η‖ * ‖F p‖}
  have hO : IsOpen O := (hΓ.preimage hF).inter (isOpen_lt
    (continuous_snd.norm.mul continuous_const) (continuous_const.mul hF.norm))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds (show (x₀, η) ∈ O from
    ⟨hη, by nlinarith⟩))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.1 (inter_mem hU hu)
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1 hv
  -- `Γ'` is the cone over the ball of radius `δ` about `η`.
  set Γ' : Set E' := ⋃ t ∈ Ioi (0 : ℝ), (t • ·) ⁻¹' ball η δ
  have hmem {w : E'} : w ∈ Γ' ↔ ∃ t : ℝ, 0 < t ∧ t • w ∈ ball η δ := by simp [Γ']
  have hball : closedBall x₀ (ρ / 2) ⊆ ball x₀ ρ := closedBall_subset_ball (by linarith)
  refine ⟨ρ / 2, by positivity, hball.trans (hρs.trans inter_subset_left), Γ',
    isOpen_biUnion fun t _ => isOpen_ball.preimage (continuous_const_smul t),
    hmem.2 ⟨1, one_pos, by simpa using hδ⟩, fun s hs w hw => ?_, 2 * ‖η‖ / ‖ξ₀‖,
    by positivity, fun x hx w hw => ?_⟩
  · obtain ⟨t, ht, htw⟩ := hmem.1 hw
    exact hmem.2 ⟨t / s, div_pos ht hs, by rwa [smul_smul, div_mul_cancel₀ _ hs.ne']⟩
  · obtain ⟨t, ht, htw⟩ := hmem.1 hw
    obtain ⟨h1, h2⟩ : (x, t • w) ∈ O := huv ⟨(hρs (hball hx)).2, hδv htw⟩
    simp only [F, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1 h2
    refine ⟨by simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using hcone t⁻¹ (inv_pos.2 ht) _ h1, ?_⟩
    rw [div_mul_eq_mul_div, le_div_iff₀ hξ₀]
    nlinarith

omit [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] in
/-- If the conic neighbourhood `closedBall ζ (c ‖ζ‖)` of `ζ` lies in `Γ` and `‖v‖ ≤ a ‖ζ‖`, then
`‖m + ζ‖` is at least a fixed multiple of `‖m‖ + ‖v‖` as soon as `-m ∉ Γ`, or `m` is small
compared with `v`. -/
private theorem mul_add_le_norm_add {Γ : Set E} {c a : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) {ζ m : E} {v : E'} (hball : closedBall ζ (c * ‖ζ‖) ⊆ Γ) (hv : ‖v‖ ≤ a * ‖ζ‖)
    (h : -m ∉ Γ ∨ ‖m‖ * (2 * a) < ‖v‖) :
    c / (4 * (1 + a)) * (‖m‖ + ‖v‖) ≤ ‖m + ζ‖ := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h1 : ‖ζ‖ ≤ ‖m + ζ‖ + ‖m‖ := by simpa [add_comm] using norm_le_add_norm_add ζ m
  have h2 : ‖m‖ ≤ ‖m + ζ‖ + ‖ζ‖ := norm_le_add_norm_add m ζ
  have hm := norm_nonneg m
  have hv0 := norm_nonneg v
  rcases h with h | h
  · have h3 : c * ‖ζ‖ < ‖m + ζ‖ := by
      by_contra! h3
      refine h (hball ?_)
      simpa [mem_closedBall, dist_comm, dist_eq_norm, add_comm] using h3
    nlinarith [mul_le_mul_of_nonneg_left hv hc.le]
  · have h4 : a * ‖m‖ ≤ a * ‖m + ζ‖ := by nlinarith
    have h5 : ‖m‖ ≤ ‖m + ζ‖ := le_of_mul_le_mul_left h4 ha
    nlinarith [mul_le_mul_of_nonneg_right hc1 (add_nonneg hm hv0)]

/-- The Fourier coefficient `𝓕(ψ (e_η ∘ Φ))(m)` of a test function times the Fourier atom `e_η`
of `E'` pulled back along `Φ`. -/
private def pullbackCoeff [MeasurableSpace E] [BorelSpace E] {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ)
    (ψ : 𝓓(Ω, ℂ)) (η : E') (m : E) : ℂ :=
  𝓕 (pullbackAtom hΦ ψ η : E → ℂ) m

omit [FiniteDimensional ℝ E'] in
/-- The Fourier coefficients of `ψ (e_η ∘ Φ)` are oscillatory integrals of `ψ` with the phase
`x ↦ -(⟪m, x⟫ + ⟪η, Φ x⟫)`, written for every `s ≠ 0` as `s` times the phase with `(m, η)`
replaced by `s⁻¹ (m, η)`. -/
private theorem pullbackCoeff_eq_integral [MeasurableSpace E] [BorelSpace E]
    {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (ψ : 𝓓(Ω, ℂ)) (η : E') (m : E) {s : ℝ} (hs : s ≠ 0) :
    pullbackCoeff hΦ ψ η m =
      ∫ x, 𝐞 (s * -(⟪(s⁻¹ • (m, η)).1, x⟫ + ⟪(s⁻¹ • (m, η)).2, Φ x⟫)) • ψ x := by
  rw [pullbackCoeff, Real.fourier_eq]
  congr 1
  ext x
  have he : s * -(⟪(s⁻¹ • (m, η)).1, x⟫ + ⟪(s⁻¹ • (m, η)).2, Φ x⟫) =
      -⟪x, m⟫ + -⟪Φ x, η⟫ := by
    simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, real_inner_comm m,
      real_inner_comm η]
    field_simp
    ring
  rw [he, AddChar.map_add_eq_mul]
  simp only [Circle.smul_def, pullbackAtom_apply, TauCeti.fourierAtom_eq_fourierChar,
    smul_eq_mul, Circle.coe_mul]
  ring

/-- The phase `x ↦ -(⟪θ₁, x⟫ + ⟪θ₂, Φ x⟫)` has nonzero derivative at `x` as soon as its gradient
`θ₁ + (DΦ x)ᵀ θ₂` is nonzero. -/
private theorem fderiv_phase_ne_zero {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (θ : E × E') {x : E}
    (h : θ.1 + ((fderiv ℝ Φ x)†) θ.2 ≠ 0) :
    fderiv ℝ (fun x => -(⟪θ.1, x⟫ + ⟪θ.2, Φ x⟫)) x ≠ 0 := by
  have hd : HasFDerivAt (fun x => -(⟪θ.1, x⟫ + ⟪θ.2, Φ x⟫))
      (-(innerSL ℝ θ.1 + (innerSL ℝ θ.2).comp (fderiv ℝ Φ x))) x :=
    ((innerSL ℝ θ.1).hasFDerivAt.add ((innerSL ℝ θ.2).hasFDerivAt.comp x
      ((hΦ.differentiable (by simp)) x).hasFDerivAt)).neg
  rw [hd.fderiv]
  intro h0
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L (θ.1 + ((fderiv ℝ Φ x)†) θ.2)) h0
  simp only [neg_apply, add_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
    zero_apply] at h1
  rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_add_left, neg_eq_zero,
    real_inner_self_eq_norm_sq] at h1
  exact h (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

omit [FiniteDimensional ℝ E'] in
/-- The Fourier coefficients of `ψ (e_η ∘ Φ)` are bounded by `∫ ‖ψ‖`. -/
private theorem norm_pullbackCoeff_le [MeasurableSpace E] [BorelSpace E]
    {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) (ψ : 𝓓(Ω, ℂ)) (η : E') (m : E) :
    ‖pullbackCoeff hΦ ψ η m‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [pullbackCoeff_eq_integral hΦ ψ η m one_ne_zero]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun x => ?_)))
  simp [Circle.smul_def]

/-- The normalized frequencies `θ = (m, v) / (‖m‖ + ‖v‖)` whose phase gradients
`θ₁ + (DΦ x)ᵀ θ₂` stay away from zero over `K` form a compact set. -/
private theorem isCompact_inter_iInter_le_norm_add (Φ : E → E') (K : Set E) (κ : ℝ) :
    IsCompact ({θ : E × E' | ‖θ.1‖ + ‖θ.2‖ ≤ 1} ∩
      ⋂ x ∈ K, {θ | κ ≤ ‖θ.1 + ((fderiv ℝ Φ x)†) θ.2‖}) := by
  refine (isCompact_closedBall (0 : E × E') 1).of_isClosed_subset ((isClosed_le
    (by fun_prop : Continuous fun θ : E × E' => ‖θ.1‖ + ‖θ.2‖) continuous_const).inter
    (isClosed_biInter fun x _ => isClosed_le continuous_const
      (continuous_fst.add (((fderiv ℝ Φ x)†).continuous.comp continuous_snd)).norm))
    fun θ hθ => ?_
  have h1 : ‖θ.1‖ + ‖θ.2‖ ≤ 1 := hθ.1
  simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  exact ⟨by linarith [norm_nonneg θ.2], by linarith [norm_nonneg θ.1]⟩

omit [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A bound `F ≤ B` together with `s ^ M F ≤ C` gives `(1 + s) ^ M F ≤ 2 ^ M (B + C)`. -/
private theorem one_add_pow_mul_le {s F B C : ℝ} {M : ℕ} (hs : 0 ≤ s) (hF : 0 ≤ F) (hFB : F ≤ B)
    (hFC : s ^ M * F ≤ C) : (1 + s) ^ M * F ≤ 2 ^ M * (B + C) :=
  calc (1 + s) ^ M * F ≤ 2 ^ M * (1 + s ^ M) * F := by
        gcongr
        calc (1 + s) ^ M ≤ 2 ^ (M - 1) * (1 ^ M + s ^ M) := add_pow_le zero_le_one hs M
          _ ≤ 2 ^ M * (1 + s ^ M) := by
            rw [one_pow]
            gcongr
            · norm_num
            · omega
    _ ≤ 2 ^ M * (B + C) := by
        rw [mul_assoc, add_mul, one_mul]
        gcongr

/-- **Non-stationary phase for the Fourier coefficients.** Let `ψ` be supported in a set
`K` over which the transposed differentials `(DΦ x)ᵀ` map an open cone `Γ'` into a cone `Γ₂`, with
`‖v‖ ≤ a ‖(DΦ x)ᵀ v‖`, where the conic neighbourhood `closedBall ζ (c ‖ζ‖)` of every `ζ ∈ Γ₂` lies
in a cone `Γ`. Then the Fourier coefficients `𝓕 (ψ (e_v ∘ Φ)) m` decay faster than every power of
`‖m‖ + ‖v‖` over the pairs with `v ∈ Γ'` and either `-m ∉ Γ` or `‖m‖ (2 a) < ‖v‖`: for these pairs
the phase `x ↦ -(⟪m, x⟫ + ⟪v, Φ x⟫)` has no critical point on `K`. -/
private theorem exists_one_add_pow_mul_norm_fourier_le [MeasurableSpace E] [BorelSpace E]
    {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ) {ψ : 𝓓(Ω, ℂ)} {K : Set E} (hψK : tsupport ψ ⊆ K)
    {Γ Γ₂ : Set E} {Γ' : Set E'} {c a : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hΓ₂ : ∀ ζ ∈ Γ₂, closedBall ζ (c * ‖ζ‖) ⊆ Γ)
    (hKΓ' : ∀ x ∈ K, ∀ v ∈ Γ', ((fderiv ℝ Φ x)†) v ∈ Γ₂ ∧ ‖v‖ ≤ a * ‖((fderiv ℝ Φ x)†) v‖)
    (M : ℕ) :
    ∃ C, ∀ v ∈ Γ', ∀ m : E, (-m ∉ Γ ∨ ‖m‖ * (2 * a) < ‖v‖) →
      (1 + (‖m‖ + ‖v‖)) ^ M * ‖pullbackCoeff hΦ ψ v m‖ ≤ C := by
  set κ := c / (4 * (1 + a))
  have hκ : 0 < κ := by positivity
  -- The normalized frequencies `(m, v) / (‖m‖ + ‖v‖)` lie in a compact set of non-critical
  -- parameters.
  set P : Set (E × E') := {θ | ‖θ.1‖ + ‖θ.2‖ ≤ 1} ∩
    ⋂ x ∈ K, {θ | κ ≤ ‖θ.1 + ((fderiv ℝ Φ x)†) θ.2‖}
  have hP : IsCompact P := isCompact_inter_iInter_le_norm_add Φ K κ
  set G : (E × E') × E → ℝ := fun p => -(⟪p.1.1, p.2⟫ + ⟪p.1.2, Φ p.2⟫)
  have hG : ContDiff ℝ ∞ G := ((contDiff_fst.fst.inner ℝ contDiff_snd).add
    (contDiff_fst.snd.inner ℝ (hΦ.comp contDiff_snd))).neg
  obtain ⟨C, hC⟩ := TauCeti.exists_abs_pow_mul_norm_integral_fourierChar_smul_le
    (μ := volume) hG ψ.contDiff ψ.hasCompactSupport hP
    (fun θ hθ x hx => fderiv_phase_ne_zero hΦ θ
      (norm_pos_iff.1 (hκ.trans_le (mem_iInter₂.1 hθ.2 x (hψK hx))))) M
  set B := ∫ x, ‖ψ x‖
  have hB : 0 ≤ B := integral_nonneg fun x => norm_nonneg _
  refine ⟨2 ^ M * (B + (max C 0 + B)), fun v hv m hm => ?_⟩
  set s := ‖m‖ + ‖v‖
  have hs0 : 0 ≤ s := by positivity
  have hL1 := norm_pullbackCoeff_le hΦ ψ v m
  -- Non-stationary phase gives `s ^ M ‖𝓕 (ψ (e_v ∘ Φ)) m‖ ≤ C` for `s > 0`.
  have hdecay : s ^ M * ‖pullbackCoeff hΦ ψ v m‖ ≤ max C 0 + B := by
    rcases hs0.eq_or_lt with hs | hs
    · rcases M.eq_zero_or_pos with hM | hM
      · rw [hM, pow_zero, one_mul]
        linarith [le_max_right C 0]
      · rw [← hs, zero_pow hM.ne', zero_mul]
        positivity
    have hθ : s⁻¹ • (m, v) ∈ P := by
      refine ⟨?_, mem_iInter₂.2 fun x hx => ?_⟩
      · simp only [mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hs, ← mul_add]
        rw [inv_mul_cancel₀ hs.ne']
      obtain ⟨hζ, hvζ⟩ := hKΓ' x hx v hv
      have h := mul_add_le_norm_add hc hc1 ha (hΓ₂ _ hζ) hvζ hm
      simp only [mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, map_smul, ← smul_add, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hs]
      rw [le_inv_mul_iff₀ hs]
      linarith
    have h := hC _ hθ s
    rw [abs_of_pos hs, ← pullbackCoeff_eq_integral hΦ ψ v m hs.ne'] at h
    linarith [le_max_left C 0]
  exact one_add_pow_mul_le hs0 (norm_nonneg _) hL1 hdecay

omit [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The bound on one term of the expansion of `T (ψ (e_v ∘ Φ))`, in the two regimes: either the
frequency `-m` is a direction of decay of the localized Fourier transform `L` of `T`, comparable
in size with `v`, or the Fourier coefficient `F` of `ψ (e_v ∘ Φ)` decays rapidly in `‖m‖ + ‖v‖`
while `L` grows at most polynomially. -/
private theorem one_add_pow_mul_mul_le {nv nm F L a B C₁ C₂ C₃ : ℝ} {N k r : ℕ} (hnv : 0 ≤ nv)
    (hnm : 0 ≤ nm) (hF : 0 ≤ F) (hL : 0 ≤ L) (ha : 0 < a)
    (h : (nv ≤ nm * (2 * a) ∧ F ≤ B ∧ (1 + nm) ^ (N + r) * L ≤ C₁) ∨
      (L ≤ C₂ * (1 + nm) ^ k ∧ (1 + (nm + nv)) ^ (N + k + r) * F ≤ C₃)) :
    (1 + nv) ^ N * (F * L) * (1 + nm) ^ r ≤ max (B * C₁ * (1 + 2 * a) ^ N) (C₂ * C₃) := by
  rcases h with ⟨hv, hFB, hLC⟩ | ⟨hLC, hFC⟩
  · refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 + nv) ^ N ≤ (1 + 2 * a) ^ N * (1 + nm) ^ N := by
      rw [← mul_pow]
      gcongr
      nlinarith
    calc (1 + nv) ^ N * (F * L) * (1 + nm) ^ r
        ≤ (1 + 2 * a) ^ N * (1 + nm) ^ N * (B * L) * (1 + nm) ^ r := by gcongr
      _ = B * ((1 + nm) ^ (N + r) * L) * (1 + 2 * a) ^ N := by ring
      _ ≤ B * C₁ * (1 + 2 * a) ^ N := by
          gcongr
          exact hF.trans hFB
  · refine le_trans ?_ (le_max_right _ _)
    have hC₂ : 0 ≤ C₂ := nonneg_of_mul_nonneg_left (hL.trans hLC) (by positivity)
    have h1 : (1 + nv) ^ N * (1 + nm) ^ k * (1 + nm) ^ r ≤ (1 + (nm + nv)) ^ (N + k + r) := by
      rw [pow_add, pow_add]
      gcongr <;> linarith
    calc (1 + nv) ^ N * (F * L) * (1 + nm) ^ r
        ≤ (1 + nv) ^ N * (F * (C₂ * (1 + nm) ^ k)) * (1 + nm) ^ r := by gcongr
      _ = C₂ * (((1 + nv) ^ N * (1 + nm) ^ k * (1 + nm) ^ r) * F) := by ring
      _ ≤ C₂ * ((1 + (nm + nv)) ^ (N + k + r) * F) := by gcongr
      _ ≤ C₂ * C₃ := by gcongr

omit [FiniteDimensional ℝ E'] in
/-- The bound on one term `c₀ 𝓕(ψ (e_v ∘ Φ))(m) T (φ e_(-m))` of the expansion of
`T (ψ (e_v ∘ Φ))`, weighted by `(1 + ‖v‖) ^ N`, in the two regimes of `one_add_pow_mul_mul_le`:
either `-m` lies in the cone `Γ` in which `T (φ e_·)` decays and is comparable in size with `v`,
or the Fourier coefficient of `ψ (e_v ∘ Φ)` decays rapidly in `‖m‖ + ‖v‖`. -/
private theorem norm_one_add_pow_smul_mul_le [MeasurableSpace E] [BorelSpace E] {Φ : E → E'}
    (hΦ : ContDiff ℝ ∞ Φ) (T : 𝓓'(Ω, ℂ)) (φ ψ : 𝓓(Ω, ℂ)) (c₀ : ℂ) {Γ : Set E}
    {a CA CB C₁ : ℝ} {N k r : ℕ} (ha : 0 < a)
    (hCA : ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ (N + r) * ‖T.localFourier φ ξ‖ ≤ CA)
    (hpoly : ∀ ξ, ‖T.localFourier φ ξ‖ ≤ C₁ * (1 + ‖ξ‖) ^ k) (v : E') (m : E)
    (hCB : (-m ∉ Γ ∨ ‖m‖ * (2 * a) < ‖v‖) →
      (1 + (‖m‖ + ‖v‖)) ^ (N + k + r) * ‖pullbackCoeff hΦ ψ v m‖ ≤ CB) :
    ‖(1 + ‖v‖) ^ N • (c₀ * pullbackCoeff hΦ ψ v m * T.localFourier φ (-m))‖ ≤
      ‖c₀‖ * max ((∫ x, ‖ψ x‖) * CA * (1 + 2 * a) ^ N) (C₁ * CB) * ((1 + ‖m‖) ^ r)⁻¹ := by
  have hshape (x y z w u : ℝ) : x * (u * y * z) * w = u * (x * (y * z) * w) := by ring
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), norm_smul, norm_mul, norm_mul,
    Real.norm_of_nonneg (by positivity), hshape]
  gcongr
  refine one_add_pow_mul_mul_le (k := k) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) ha ?_
  by_cases hA : -m ∈ Γ ∧ ‖v‖ ≤ ‖m‖ * (2 * a)
  · exact Or.inl ⟨hA.2, norm_pullbackCoeff_le hΦ ψ v m,
      by simpa using hCA _ hA.1⟩
  · refine Or.inr ⟨by simpa using hpoly (-m), hCB ?_⟩
    by_contra! h
    exact hA h

/-- **Decay of the Fourier atoms pulled back along `Φ`, near a point.** If `T` is microlocally
smooth at `(x₀, (DΦ x₀)ᵀ η)` and `(DΦ x₀)ᵀ η ≠ 0`, then there are a neighbourhood `V` of `x₀` and
an open cone `Γ'` around `η` such that `v ↦ T (ψ (e_v ∘ Φ))` decays rapidly on `Γ'` for every test
function `ψ` supported in `V`. -/
private theorem exists_nhds_cone_pullbackFourier {Φ : E → E'} (hΦ : ContDiff ℝ ∞ Φ)
    {T : 𝓓'(Ω, ℂ)} {x₀ : E} {η : E'} (hξ : ((fderiv ℝ Φ x₀)†) η ≠ 0)
    (hT : T.IsMicrolocallySmoothAt x₀ (((fderiv ℝ Φ x₀)†) η)) :
    ∃ V ∈ 𝓝 x₀, ∃ Γ' : Set E', IsOpen Γ' ∧ η ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ v ∈ Γ', t • v ∈ Γ') ∧
      ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ V →
        ∀ N : ℕ, ∃ C, ∀ v ∈ Γ', (1 + ‖v‖) ^ N * ‖pullbackFourier T hΦ ψ v‖ ≤ C := by
  borelize E
  -- `T` decays in an open cone `Γ` for cutoffs supported in `U`; `Γ₂` is a conic core of `Γ`.
  obtain ⟨U, hU, Γ, hΓo, hξΓ, hΓcone, hdecay⟩ := hT.exists_nhds_cone
  obtain ⟨Γ₂, hΓ₂o, hξΓ₂, hΓ₂cone, c', hc', hΓ₂Γ⟩ :=
    IsOpen.exists_cone_closedBall_subset hΓo hΓcone hξΓ
  have hΓ₂c : ∀ ζ ∈ Γ₂, closedBall ζ (min c' 1 * ‖ζ‖) ⊆ Γ := fun ζ hζ =>
    (closedBall_subset_closedBall (by gcongr; exact min_le_left _ _)).trans (hΓ₂Γ ζ hζ)
  have hx₀ : x₀ ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨ρ, hρ, hρU, Γ', hΓ'o, hηΓ', hΓ'cone, a, ha, hgeom⟩ :=
    exists_closedBall_cone_adjoint_fderiv_mem hΦ hΓ₂o hΓ₂cone hξΓ₂ hξ
      (inter_mem hU (Ω.isOpen.mem_nhds hx₀))
  -- A cutoff `φ` equal to one on `closedBall x₀ (ρ / 2)` and supported in `U`.
  obtain ⟨φ, hφ1, hφs⟩ := exists_eventually_eq_tsupport_subset (n := ⊤)
    (isCompact_closedBall x₀ (ρ / 2)) isOpen_ball (closedBall_subset_ball (by linarith))
    (ball_subset_closedBall.trans (hρU.trans inter_subset_right)) (1 : ℂ)
  have hφU : tsupport φ ⊆ U :=
    hφs.trans (ball_subset_closedBall.trans (hρU.trans inter_subset_left))
  -- `T ψ` expands in the localized Fourier transforms of `T` with cutoff `φ`.
  obtain ⟨L₀, _, _, hL₀⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded φ.hasCompactSupport.isCompact.isBounded
  obtain ⟨L, hL, c₀, hexp⟩ : ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L) (c₀ : ℂ),
      ∀ ψ : 𝓓(Ω, ℂ), EqOn (φ : E → ℂ) 1 (support ψ) →
        HasSum (fun m : L ↦ c₀ * 𝓕 (ψ : E → ℂ) m * T.localFourier φ (-m))
          (T.complexPairing ψ) :=
    ⟨_, inferInstance, _, fun _ hψ => hasSum_fourier_mul_localFourier T φ L₀ hL₀ hψ⟩
  obtain ⟨C₁, k, hpoly⟩ := exists_norm_localFourier_le T φ
  have hw := ZLattice.summable_one_add_norm_pow_inv L (r := Module.finrank ℤ L + 1) (by omega)
  refine ⟨ball x₀ (ρ / 2), ball_mem_nhds x₀ (by positivity), Γ', hΓ'o, hηΓ', hΓ'cone,
    fun ψ hψ N => ?_⟩
  set r := Module.finrank ℤ L + 1
  have hψK : tsupport ψ ⊆ closedBall x₀ (ρ / 2) := hψ.trans ball_subset_closedBall
  obtain ⟨CA, hCA⟩ := hdecay φ hφU (N + r)
  obtain ⟨CB, hCB⟩ := exists_one_add_pow_mul_norm_fourier_le hΦ hψK (lt_min hc' one_pos)
    (min_le_right _ _) ha hΓ₂c (fun x hx v hv =>
      hgeom x (closedBall_subset_closedBall (by linarith) hx) v hv) (N + k + r)
  refine ⟨‖c₀‖ * max ((∫ x, ‖ψ x‖) * CA * (1 + 2 * a) ^ N) (C₁ * CB) *
    ∑' m : L, ((1 + ‖(m : E)‖) ^ r)⁻¹, fun v hv => ?_⟩
  have hsum := (hexp (pullbackAtom hΦ ψ v) fun x hx => hφ1.self_of_nhdsSet x
    (hψK (tsupport_bilinLeftCLM_subset _ _ ψ (subset_tsupport _ hx)))).const_smul ((1 + ‖v‖) ^ N)
  have h := hsum.norm_le_of_bounded (hw.hasSum.mul_left (‖c₀‖ *
    max ((∫ x, ‖ψ x‖) * CA * (1 + 2 * a) ^ N) (C₁ * CB))) fun m =>
      norm_one_add_pow_smul_mul_le hΦ T φ ψ c₀ ha hCA hpoly v m (hCB v hv m)
  rwa [norm_smul, Real.norm_of_nonneg (by positivity)] at h

/-- `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM` for a map `Φ` smooth on all
of `E`. -/
private theorem isMicrolocallySmoothAt_cutoffPushforwardCLM_of_contDiff {Φ : E → E'}
    (hΦ : ContDiff ℝ ∞ Φ) {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, Φ x = y →
      ((fderiv ℝ Φ x)†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    (cutoffPushforwardCLM χ Φ hΦ.contDiffOn T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  set D := tsupport χ ∩ dsupport T
  have hD : IsCompact D := χ.hasCompactSupport.inter_right isClosed_dsupport
  -- The pulled-back Fourier atoms decay in one cone `Γ` around `η` for cutoffs supported near
  -- `D ∩ Φ⁻¹ {y}`.
  obtain ⟨W, hW, hKW, Γ, hΓ, hηΓ, hcone, hdecay⟩ :=
    exists_isOpen_cone_forall_decay_of_forall_mem_nhds
      (AddMonoidHom.mk' (pullbackFourier T hΦ) fun ψ ψ' => funext (pullbackFourier_add T hΦ ψ ψ'))
      isClosed_dsupport (fun _ hψ => funext (pullbackFourier_eq_zero_of_disjoint hΦ hψ))
      (hD.inter_right (isClosed_singleton.preimage hΦ.continuous)) fun x hx =>
        exists_nhds_cone_pullbackFourier hΦ (h x hx.1 hx.2).1 (h x hx.1 hx.2).2
  -- The compact set `Φ (D \ W)` misses `y`, so a cutoff `f` around `y` pulls back into
  -- `W ∪ (supp T)ᶜ`.
  have hC : IsCompact (Φ '' (D \ W)) := (hD.diff hW).image hΦ.continuous
  have hyC : y ∉ Φ '' (D \ W) := fun ⟨x, ⟨hxD, hxW⟩, hxy⟩ => hxW (hKW ⟨hxD, hxy⟩)
  obtain ⟨f, hf, hfy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hC.isClosed.isOpen_compl.mem_nhds hyC) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  have hψ : tsupport (cutoffCompCLM χ Φ hΦ.contDiffOn f) ⊆ W ∪ (dsupport T)ᶜ := fun z hz => by
    by_contra hzW
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzW
    obtain ⟨hzχ, hzf⟩ := tsupport_cutoffCompCLM_subset f hz
    exact (hf hzf).1 ⟨z, ⟨⟨hzχ, hzW.2⟩, hzW.1⟩, rfl⟩
  refine isMicrolocallySmoothAt_iff.2 ⟨f, by simp [hfy], Γ, hΓ, hηΓ, hcone, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hdecay _ hψ N
  exact ⟨C, fun η' hη' => by
    rw [localFourier_cutoffPushforwardCLM_eq_pullbackFourier hΦ]
    exact hC η' hη'⟩

/-- **Microlocal smoothness of a pushforward along a smooth map.** Let `y ∈ Ω'`. If for every
`x ∈ supp χ ∩ supp T` with `Φ x = y` the transposed differential `(DΦ x)ᵀ η` is nonzero and `T` is
microlocally smooth at `(x, (DΦ x)ᵀ η)`, then the pushforward `Φ_* (χ T)` is microlocally smooth
at `(y, η)`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, Φ x = y →
      ((fderiv ℝ Φ x)†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    (Distribution.cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  -- Replace `Φ` by a map smooth on all of `E` that agrees with it near `supp χ`.
  obtain ⟨Φ', hΦ', -, -, -, heq⟩ :=
    hΦ.exists_contDiff_eventuallyEq_on_isCompact χ.hasCompactSupport Ω.isOpen χ.tsupport_subset
  rw [cutoffPushforwardCLM_congr_map (hΦ' := hΦ'.contDiffOn) T
    fun x hx => (heq x hx).eq_of_nhds.symm]
  refine isMicrolocallySmoothAt_cutoffPushforwardCLM_of_contDiff hΦ' hy fun x hx hxy => ?_
  rw [(heq x hx.1).fderiv_eq]
  exact h x hx ((heq x hx.1).eq_of_nhds.symm.trans hxy)

/-- **The wave front set of a pushforward** (Hörmander I, Theorem 8.2.13). Every covector `(y, η)`
in the wave front set of the pushforward `Φ_* (χ T)` along a map `Φ` smooth on `Ω` lies over a
point `x` of `supp χ ∩ supp T` with `Φ x = y`, at which either `(DΦ x)ᵀ η = 0` or
`(x, (DΦ x)ᵀ η)` lies in the wave front set of `T`. When `χ` is equal to one near the support of
`T`, this is the bound for the pushforward `Φ_* T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset {Φ : E → E'} (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (((fderiv ℝ Φ x)†) p.2 = 0 ∨ (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, -, hS⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hne
  refine hS (IsMicrolocallySmoothAt.cutoffPushforwardCLM hy fun x hx hxy => ?_)
  have h0 : ((fderiv ℝ Φ x)†) η ≠ 0 := fun h0 => hne ⟨x, hx, hxy, Or.inl h0⟩
  refine ⟨h0, ?_⟩
  by_contra hT
  exact hne ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨χ.tsupport_subset hx.1, h0, hT⟩)⟩

/-- **Pushforward along a submersion.** If the differential of `Φ` is surjective at every point of
`supp χ ∩ supp T`, its transpose is injective there, and every covector `(y, η)` in the wave front
set of `Φ_* (χ T)` lies over a point `x` of `supp χ ∩ supp T` with `Φ x = y` and
`(x, (DΦ x)ᵀ η)` in the wave front set of `T`. This applies to every surjective linear map. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {Φ : E → E'}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) {T : 𝓓'(Ω, ℂ)}
    (hs : ∀ x ∈ tsupport χ ∩ dsupport T, Surjective (fderiv ℝ Φ x)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset hΦ T hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 => (mem_waveFrontSet_iff.1 hp).2.1 ?_⟩
  obtain ⟨z, hz⟩ := hs x hx η
  have h := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ Φ x) z η
  rw [h0, inner_zero_left, hz] at h
  exact inner_self_eq_zero.1 h.symm

end Smooth

section Linear

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **Localized Fourier transforms of a pushforward.** The localized Fourier transform of the
pushforward `A_* T` along a linear map `A`, with cutoff `f`, at the frequency `η`, is that of `T`
with the cutoff `χ (f ∘ A)` at the transposed frequency `Aᵀ η`. -/
theorem localFourier_cutoffPushforwardCLM (A : E →L[ℝ] E') (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω', ℂ))
    (η : E') :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).localFourier f η =
      T.localFourier (cutoffCompCLM χ A A.contDiff.contDiffOn f) ((A†) η) := by
  rw [localFourier_eq _ f (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) f) fun x => by
      simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply],
    complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq _ _ fun x => ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    ContinuousLinearMap.adjoint_inner_right, mul_assoc]

end Linear

section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **The zero covectors cannot be omitted.** Pushing `T` forward along the constant map with
value `c ∈ Ω'` gives the multiple `T χ` of the point mass at `c`; if `T χ ≠ 0`, its wave front set
is `{c} × (E' \ {0})`, whatever the wave front set of `T`. The differential of a constant map is
zero, so the transpose of the differential kills every covector: all these covectors come from the
term `(DΦ x)ᵀ η = 0` of `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`. -/
theorem waveFrontSet_cutoffPushforwardCLM_const (T : 𝓓'(Ω, ℂ)) (hT : T χ ≠ 0) {c : E'}
    (hc : c ∈ Ω') :
    (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)).waveFrontSet =
      {c} ×ˢ {0}ᶜ := by
  have h : (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)) =
      T χ • mapCLM ofRealCLM (delta c : 𝓓'(Ω', ℝ)) := by
    rw [cutoffPushforwardCLM_const]
    ext f
    simp [mul_comm]
  rw [h, waveFrontSet_smul hT, waveFrontSet_delta hc]

end Const

end Distribution
