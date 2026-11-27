/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.MicrolocalRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Cone
import TauCeti.Algebra.Module.ZLattice.Dual
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TestFunction.ChangeOfVariables
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Fourier.NonstationaryPhase.Directional
import TauCeti.Analysis.Normed.Module.Cone

/-!
# The wave front set under smooth changes of variables

Let `e` be a smooth change of variables of a finite-dimensional real inner product space `E`: a
smooth open partial homeomorphism with smooth inverse. A complex distribution `T` on an open set
`Ω` pulls back along `e` to the distribution `e^* T` on an open subset `U` of the source of `e`
mapped into `Ω` (`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that the wave
front set transforms as a subset of the cotangent bundle: covectors pull back by the transpose of
the derivative,

`(x, ξ) ∈ WF(e^* T) ↔ (e x, (De⁻¹(e x))ᵀ ξ) ∈ WF(T)` for `x ∈ U`

(`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`), that is,
`WF(e^* T) = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ WF(T)}` (`TauCeti.covectorPullback`). This is the
invariance of the wave front set under diffeomorphisms (Hörmander I, Theorem 8.2.4), which makes
it a well-defined closed conic subset of the cotangent bundle of a manifold. For linear `e` it is
`Distribution.waveFrontSet_compCLMOfContinuousLinearEquiv`.

## The argument

Let `T` be microlocally smooth at `(y₀, η₀)` with `y₀ = e x₀` and `η₀ = Bᵀ ξ₀`, where
`B = De⁻¹(y₀)`. For a cutoff `φ` supported near `x₀`, the localized Fourier transform of `e^* T`
at `ξ` pairs `T` with `ψ(y) 𝐞(-⟪e⁻¹ y, ξ⟫)`, where `ψ` is the pushforward of `φ`. Factoring out the
linear part of the phase, this is the localized Fourier transform of `T` at `η = Bᵀ ξ` with the
cutoff `G_ξ(y) = ψ(y) 𝐞(⟪y, Bᵀ ξ⟫ - ⟪e⁻¹ y, ξ⟫)`, which depends on `ξ`. Expanding `G_ξ` in a
Fourier series on a compact set meeting none of its nonzero lattice translates
(`Distribution.hasSum_localFourier_ofSupportedIn`) gives

`T (G_ξ e_η) = ∑ m, a_m(ξ) T (χ e_(η - m))`,  `a_m(ξ) = (covolume)⁻¹ 𝓕 G_ξ (m)`.

The terms with `‖m‖ ≤ c ‖η‖` evaluate `T (χ e_ζ)` in the cone around `η₀` where it decays
rapidly, and `|a_m(ξ)|` is bounded. For the others, the phase of `𝓕 G_ξ (m)` has derivative
`‖m‖ + ⟪(B - De⁻¹(y)) w, ξ⟫` in the direction `w = -m / ‖m‖`, which is at least `‖m‖ / 2` once
`De⁻¹` stays close to `B` on the support of `ψ`, so `𝓕 G_ξ (m)` decays faster than every power of
`‖m‖` by non-stationary phase (`TauCeti.exists_norm_integral_mul_fourierChar_le`).

## Main results

* `Distribution.hasSum_localFourier_compCLMOfOpenPartialHomeomorph`: the localized Fourier
  transform of `e^* T` as a lattice series of localized Fourier transforms of `T`, with the
  Fourier coefficients of `e_* (φ e_ξ)` as coefficients.
* `Distribution.IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph`: if `T` is microlocally
  smooth at `(e x, (De⁻¹(e x))ᵀ ξ)`, then `e^* T` is microlocally smooth at `(x, ξ)`.
* `Distribution.isInvariantMicrolocalRegularity_isMicrolocallySmoothAt`: microlocal smoothness is
  an invariant notion of microlocal regularity (`Distribution.IsInvariantMicrolocalRegularity`).
* `Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`: the converse, for
  `x ∈ U`, by pulling back along `e⁻¹` from `e '' U`.
* `Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`: the wave front set of `e^* T` is
  the pullback `e^* WF(T)`.
* `OpenPartialHomeomorph.mem_covectorPullback_iff`: for `U` in the source of `e`,
  `(x, ξ) ∈ e^* Γ ↔ x ∈ U ∧ (e x, (De⁻¹(e x))ᵀ ξ) ∈ Γ`.
* `Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph_subset`: the pullback
  `e^* Γ = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ Γ}` (`TauCeti.covectorPullback`) of a set `Γ` of
  covectors contains the wave front set of `e^* T` whenever `Γ` contains that of `T`.
* `OpenPartialHomeomorph.ne_zero_of_mem_covectorPullback`,
  `OpenPartialHomeomorph.isOpen_prod_compl_sdiff_covectorPullback`: like `Γ`, the cone `e^* Γ`
  contains no zero covectors, and it is closed in `U × (E \ {0})` when `Γ` is closed in
  `Ω × (E \ {0})`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and Theorem 7.7.1.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The wave front set of a pullback -/

variable {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **The localized Fourier transform of a pullback as a lattice series.** Let `χ` be supported in
a compact set `K ⊆ Ω` which meets none of its translates by nonzero vectors of a full lattice `L`,
and equal to one at `e x` for every `x` in the support of the cutoff `φ`. Then the localized Fourier
transform of `e^* T` with cutoff `φ` at `ξ` is a superposition of the localized Fourier transforms
of `T` with cutoff `χ` at the frequencies `-m`, `m ∈ L^∨`:

`(e^* T)(φ e_ξ) = ∑ m, ((covolume L)⁻¹ ∫ φ(x) 𝐞(⟪e x, -m⟫ - ⟪x, ξ⟫) dx) T (χ e_(-m))`.

The coefficients are the Fourier coefficients of the pushed forward test function `e_* (φ e_ξ)`,
computed by changing variables. -/
theorem hasSum_localFourier_compCLMOfOpenPartialHomeomorph [MeasurableSpace E] [BorelSpace E]
    (T : 𝓓'(Ω, ℂ)) {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hL : ∀ x ∈ K, ∀ ℓ : L, x + ℓ ∈ K → ℓ = 0)
    {χ : 𝓓_{K}(E, ℂ)} {φ : 𝓓(U, ℂ)} (hχ : ∀ x ∈ tsupport φ, χ (e x) = 1) (ξ : E) :
    HasSum (fun m : ZLattice.dual L ↦ ((ZLattice.covolume L : ℂ)⁻¹ *
        ∫ x, φ x * 𝐞 (⟪e x, -(m : E)⟫ - ⟪x, ξ⟫)) • T.localFourier (ofSupportedIn hKΩ χ) (-m))
      ((compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier φ ξ) := by
  -- The pushforward `g = e_* (φ e_ξ)` of the modulated cutoff.
  set ψ : 𝓓(U, ℂ) := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom ξ) φ
  set g := pushforwardCLM e he he' hU hUΩ ψ
  have hψ (x : E) : ψ x = φ x * 𝐞 (-⟪x, ξ⟫) := by
    simp [ψ, bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
  have hψs : tsupport ψ ⊆ tsupport φ :=
    closure_mono fun x hx ↦ left_ne_zero_of_mul (by rwa [← hψ])
  -- `g` is supported in `e (supp φ)`, where `χ = 1`.
  have hg1 : support g ⊆ {y | χ y = 1} := fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := (tsupport_pushforwardCLM_subset ψ).trans (image_mono hψs)
      (subset_tsupport _ hy)
    exact hχ x hx
  -- The pairing of `e^* T` with `φ e_ξ` is the pairing of `T` with `g`.
  have h0 : T.complexPairing g =
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier φ ξ := by
    rw [localFourier_def, complexPairing_compCLMOfOpenPartialHomeomorph]
  -- The Fourier coefficients of `g`, by changing variables `y = e x`.
  have hF (m : E) : 𝓕 (g : E → ℂ) m = ∫ x, φ x * 𝐞 (⟪e x, -m⟫ - ⟪x, ξ⟫) := by
    rw [Real.fourier_eq]
    calc ∫ v, 𝐞 (-⟪v, m⟫) • g v = ∫ v, g v • (𝐞 (-⟪v, m⟫) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
          simp [Circle.smul_def, mul_comm]
      _ = ∫ x, ψ x • (𝐞 (-⟪e x, m⟫) : ℂ) := integral_pushforwardCLM_smul volume ψ _
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [hψ, smul_eq_mul, inner_neg_right, sub_eq_add_neg, AddChar.map_add_eq_mul,
            Circle.coe_mul]
          ring
  have h := hasSum_fourier_mul_localFourier T (ofSupportedIn hKΩ χ) L
    (fun y hy ℓ hℓ h ↦ congrArg Subtype.val
      (hL y (χ.tsupport_subset hy) ⟨ℓ, hℓ⟩ (χ.tsupport_subset h)))
    (φ := g) fun y hy ↦ by simpa using hg1 hy
  rw [← h0]
  simpa only [hF, smul_eq_mul] using h

/-- The localized Fourier transform of the pullback `e^* T` with cutoff `φ` at `ζ` is that of `T`
at `Bᵀ ζ` with the cutoff `G = (e_* φ) 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)`, for any `σ` agreeing with `e⁻¹` on
the support of the pushforward `e_* φ`. -/
private theorem localFourier_compCLMOfOpenPartialHomeomorph_eq (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(U, ℂ))
    {σ : E → E} (hσ : ∀ y ∈ e.target, φ (e.symm y) ≠ 0 → σ y = e.symm y) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) (G : 𝓓_{K}(E, ℂ)) (B : E →L[ℝ] E) (ζ : E)
    (hG : ∀ y, G y = pushforwardCLM e he he' hU hUΩ φ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier φ ζ =
      T.localFourier (ofSupportedIn hKΩ G) ((B†) ζ) := by
  rw [localFourier_def, complexPairing_compCLMOfOpenPartialHomeomorph]
  refine (localFourier_eq _ _ fun y ↦ ?_).symm
  by_cases hy : y ∈ e.target
  · rw [pushforwardCLM_apply_of_mem _ hy]
    by_cases hφy : φ (e.symm y) = 0
    · simp [bilinLeftCLM_apply, hG, pushforwardCLM_apply_of_mem _ hy, hφy]
    · simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', coe_ofSupportedIn, hG,
        pushforwardCLM_apply_of_mem _ hy, hσ y hy hφy, TauCeti.fourierAtom_eq_fourierChar,
        real_smul, real_inner_comm ζ]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_assoc]
      congr 3
      ring
  · simp [pushforwardCLM_apply_of_notMem _ hy, hG]

omit [FiniteDimensional ℝ E] in
/-- **Decay of the localized Fourier transforms with phase-modulated cutoffs.** Let `T` have
localized Fourier transforms decaying rapidly on a cone `Γ` for all cutoffs supported in `W`, and
let `Γ'` have conic neighbourhoods of relative size `c ≤ 1 / 2` inside `Γ`. Let `ψ` be supported
in a set `K₁` on which a smooth function `χ` supported in a compact set `K ⊆ W ∩ Ω` equals one,
`K` meeting none of its nonzero translates by a lattice `L`. If `‖ζ‖ ≤ a ‖Bᵀ ζ‖` and `Dσ` stays
within `c / (2 a)` of `B` on the support of `ψ`, then `T` with the cutoffs
`G ζ = ψ 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)` has localized Fourier transform at `Bᵀ ζ` decaying rapidly in
`Bᵀ ζ ∈ Γ'`. The Fourier series of `G ζ` on `K` is split into the frequencies `m` small
compared with `Bᵀ ζ`, which stay in `Γ`, and the large ones, where `𝓕 (G ζ)` decays by
non-stationary phase. -/
private theorem exists_one_add_norm_pow_mul_norm_localFourier_le [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {T : 𝓓'(Ω, ℂ)} {W Γ Γ' : Set E}
    (hdecay : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ W →
      ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier ψ η‖ ≤ C)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (hKW : (K : Set E) ⊆ W) {K₁ : Set E}
    {χ : 𝓓_{K}(E, ℂ)} (hχ : ∀ y ∈ K₁, χ y = 1) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hL : ∀ y ∈ K, ∀ ℓ : L, y + ℓ ∈ K → ℓ = 0) {ψ : 𝓓(Ω, ℂ)}
    (hψK₁ : tsupport ψ ⊆ K₁) {σ : E → E} (hσ : ContDiff ℝ ∞ σ) (B : E →L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (hB : ∀ ζ, ‖ζ‖ ≤ a * ‖(B†) ζ‖)
    (hσB : ∀ y ∈ tsupport (ψ : E → ℂ), ‖fderiv ℝ σ y - B‖ ≤ c / (2 * a))
    (G : E → 𝓓_{K}(E, ℂ)) (hG : ∀ ζ y, G ζ y = ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) (N : ℕ) :
    ∃ C, ∀ ζ, (B†) ζ ∈ Γ' →
      (1 + ‖(B†) ζ‖) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖ ≤ C := by
  -- The Fourier series of `G ζ` in the modulations of `χ`, and the growth and decay of the
  -- localized Fourier transform `F` of `T` with cutoff `χ`.
  have hχG (ζ : E) : EqOn χ 1 (support (G ζ)) := fun y hy ↦ by
    refine hχ y (hψK₁ (subset_tsupport _ fun h0 ↦ hy ?_))
    rw [hG, h0, zero_mul]
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T (ofSupportedIn hKΩ χ)
  set q := Module.finrank ℝ E + 1
  have hq : Summable fun m : ZLattice.dual L ↦ ((1 + ‖(m : E)‖) ^ q)⁻¹ :=
    ZLattice.summable_one_add_norm_pow_inv _ (by rw [ZLattice.rank ℝ]; omega)
  obtain ⟨C₁, hC₁⟩ := hdecay (ofSupportedIn hKΩ χ)
    (fun y hy ↦ hKW (χ.tsupport_subset (by simpa using hy))) (N + q)
  -- The Fourier coefficients of `G ζ` are bounded, and decay at large frequencies.
  set κ := ‖((ZLattice.covolume L : ℂ))⁻¹‖
  set A₀ := κ * ∫ y, ‖ψ y‖
  have ha₀ (ζ m : E) : ‖(ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (G ζ : E → ℂ) m‖ ≤ A₀ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((Real.norm_fourier_le_integral_norm _ _).trans_eq
      (integral_congr_ae (ae_of_all _ fun y ↦ ?_))) (norm_nonneg _)
    simp [hG]
  obtain ⟨C₂, hC₂⟩ := TauCeti.exists_norm_pow_mul_norm_fourier_mul_fourierChar_le ψ.contDiff
    ψ.hasCompactSupport hσ B (by positivity) hσB (N + 2 * k + q)
  refine ⟨_, fun ζ hζ ↦ TauCeti.one_add_norm_pow_mul_norm_le_of_hasSum
    (fun m : ZLattice.dual L ↦ (m : E)) hq hF hC₁ hc hc1 (hΓ' _ hζ) (A₀ := A₀)
    (A₁ := κ * max C₂ 0) (by positivity) (by positivity) (fun m ↦ ha₀ ζ m) (fun m hm ↦ ?_)
    (hasSum_localFourier_ofSupportedIn T hKΩ L hL (hχG ζ) _)⟩
  -- Frequencies `m` with `‖m‖ > c ‖Bᵀ ζ‖ ≥ (c / a) ‖ζ‖` are non-stationary.
  have hm0 : (m : E) ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hm; exact (lt_irrefl _ (hm.trans_le' (by positivity)))
  have hεm : 2 * (c / (2 * a)) * ‖ζ‖ ≤ ‖(m : E)‖ := by
    have : 2 * (c / (2 * a)) * ‖ζ‖ ≤ c * ‖(B†) ζ‖ := by
      rw [show 2 * (c / (2 * a)) = c / a by field_simp, div_mul_eq_mul_div,
        div_le_iff₀ ha]
      nlinarith [hB ζ]
    linarith
  have hGf : (G ζ : E → ℂ) = fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) := funext (hG ζ)
  rw [norm_mul, mul_left_comm, hGf]
  exact mul_le_mul_of_nonneg_left ((hC₂ ζ m hm0 hεm).trans (le_max_left _ _)) (norm_nonneg _)

variable (e he he' hU hUΩ) in
/-- **The wave front set of a pullback along a change of variables.** If `T` is microlocally
smooth at `(e x, (De⁻¹(e x))ᵀ ξ)`, then its pullback `e^* T` is microlocally smooth at `(x, ξ)`
(Hörmander I, Theorem 8.2.4). -/
theorem IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ U) (h : T.IsMicrolocallySmoothAt (e x) (((fderiv ℝ e.symm (e x))†) ξ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x ξ := by
  borelize E
  set B : E →L[ℝ] E := fderiv ℝ e.symm (e x)
  set a := ‖fderiv ℝ e x‖ + 1
  have hxs : x ∈ e.source := hU hx
  have hy₀ : e x ∈ e.target := e.map_source hxs
  -- Frequencies are comparable through the transposes: `‖ζ‖ ≤ (‖De(x)‖ + 1) ‖Bᵀ ζ‖`.
  have hB (ζ : E) : ‖ζ‖ ≤ a * ‖(B†) ζ‖ :=
    calc ‖ζ‖ = ‖((fderiv ℝ e x)†) ((B†) ζ)‖ := by
          rw [e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn he he' (by simp) hxs]
      _ ≤ ‖(fderiv ℝ e x)†‖ * ‖(B†) ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ a * ‖(B†) ζ‖ := by rw [LinearIsometryEquiv.norm_map]; gcongr; linarith
  -- The decay of `T` near `(e x, Bᵀ ξ)`, uniform over the cutoffs supported in `W`, on the cone
  -- `Γ`; the smaller cone `Γ'` has conic neighbourhoods of relative size `c'` inside `Γ`.
  obtain ⟨W, hW, Γ, hΓo, hΓξ, hΓc, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨Γ', hΓ'o, hΓ'ξ, hΓ'c, c, hc, hΓ'⟩ := hΓo.exists_cone_closedBall_subset hΓc hΓξ
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hΓ'' : ∀ η ∈ Γ', closedBall η (c' * ‖η‖) ⊆ Γ := fun η hη ↦
    (closedBall_subset_closedBall (by gcongr; exact min_le_left _ _)).trans (hΓ' η hη)
  -- A compact set `K ⊆ W ∩ Ω` around `e x`, a lattice, and a cutoff `χ` equal to one on `K₁ ∋ e x`.
  obtain ⟨K, K₁, hKW, hK₁, hK₁K, ⟨χ, hχ⟩, L, _, _, hL⟩ :=
    ContDiffMapSupportedIn.exists_compacts_cutoff_lattice
      (inter_mem hW (Ω.isOpen.mem_nhds (hUΩ hx)))
  have hKΩ : (K : Set E) ⊆ Ω := hKW.trans inter_subset_right
  -- A smooth `σ` equal to `e⁻¹` near `e x`; near `e x`, `Dσ` stays within `c' / (2 a)` of `B`.
  obtain ⟨σ, hσ, -, hσe⟩ :=
    he'.exists_contDiff_eventuallyEq_of_finiteDimensional (e.open_target.mem_nhds hy₀)
  have hε : 0 < c' / (2 * a) := by positivity
  set S : Set E := K₁ ∩ {y | σ y = e.symm y} ∩ {y | ‖fderiv ℝ σ y - B‖ < c' / (2 * a)}
  have hS : S ∈ 𝓝 (e x) := by
    have hσc := ((hσ.continuous_fderiv (by simp)).continuousAt (x := e x)).eventually
      (Metric.ball_mem_nhds _ hε)
    rw [hσe.fderiv_eq] at hσc
    exact inter_mem (inter_mem hK₁ hσe) (hσc.mono fun y hy ↦ by simpa [dist_eq_norm] using hy)
  -- A cutoff `φ` at `x` whose pushforward `ψ` is supported in `S`.
  obtain ⟨φ, hφs, hφx⟩ := exists_tsupport_subset_apply_eq (Ω := U)
    (inter_mem (U.isOpen.mem_nhds hx) ((e.continuousAt hxs).preimage_mem_nhds hS))
    inter_subset_left (1 : ℂ)
  set ψ : 𝓓(Ω, ℂ) := pushforwardCLM e he he' hU hUΩ φ
  have hψS : tsupport ψ ⊆ S :=
    (tsupport_pushforwardCLM_subset φ).trans (image_subset_iff.2 (hφs.trans inter_subset_right))
  -- The cutoffs `G ζ = ψ 𝐞(⟪·, Bᵀ ζ⟫ - ⟪σ ·, ζ⟫)`, supported in `K`.
  have hGc (ζ : E) : ContDiff ℝ ∞ fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) :=
    ψ.contDiff.mul
      ((contDiff_id.inner ℝ contDiff_const).sub (hσ.inner ℝ contDiff_const)).fourierChar
  have hGs (ζ : E) : support (fun y ↦ ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫)) ⊆ K := fun y hy ↦
    hK₁K (hψS (subset_tsupport _ (left_ne_zero_of_mul hy))).1.1
  let G (ζ : E) : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset (hGc ζ) (hGs ζ)
  have hG (ζ y : E) : G ζ y = ψ y * 𝐞 (⟪y, (B†) ζ⟫ - ⟪σ y, ζ⟫) :=
    ContDiffMapSupportedIn.coe_of_support_subset _ _ y
  -- On the support of `φ ∘ e⁻¹`, `σ = e⁻¹`.
  have hσφ : ∀ y ∈ e.target, φ (e.symm y) ≠ 0 → σ y = e.symm y := fun y hy hφy ↦ by
    simpa [e.right_inv hy] using ((hφs (subset_tsupport _ hφy)).2).1.2
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], (B†) ⁻¹' Γ',
    hΓ'o.preimage (B†).continuous, hΓ'ξ,
    fun t ht ζ hζ ↦ by simpa [map_smul] using hΓ'c t ht _ hζ, fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_localFourier_le hdecay hc'
    (min_le_right _ _) hΓ'' hKΩ (fun y hy ↦ (hKW hy).1) hχ L hL (fun y hy ↦ (hψS hy).1.1) hσ B
    (by positivity) hB (fun y hy ↦ (hψS hy).2.le) G hG N
  refine ⟨a ^ N * C, fun ζ hζ ↦ ?_⟩
  rw [localFourier_compCLMOfOpenPartialHomeomorph_eq T φ hσφ hKΩ (G ζ) B ζ (hG ζ)]
  calc (1 + ‖ζ‖) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖
      ≤ (a * (1 + ‖(B†) ζ‖)) ^ N * ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖ := by
        gcongr
        nlinarith [hB ζ, norm_nonneg ((B†) ζ), norm_nonneg (fderiv ℝ e x)]
    _ = a ^ N * ((1 + ‖(B†) ζ‖) ^ N *
          ‖T.localFourier (ofSupportedIn hKΩ (G ζ)) ((B†) ζ)‖) := by rw [mul_pow]; ring
    _ ≤ a ^ N * C := mul_le_mul_of_nonneg_left (hC ζ hζ) (by positivity)

/-- Microlocal smoothness is an invariant notion of microlocal regularity: it is open, linear,
conic, preserved by smooth multiples and pullback along smooth changes of variables, and unchanged
by restriction to smaller open sets. -/
theorem isInvariantMicrolocalRegularity_isMicrolocallySmoothAt :
    IsInvariantMicrolocalRegularity
      fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ξ ↦ T.IsMicrolocallySmoothAt x ξ where
  isOpen_setOf _ T := isOpen_setOf_isMicrolocallySmoothAt T
  zero hx ξ := isMicrolocallySmoothAt_zero hx ξ
  add hS hT := hS.add hT
  smul c hT := hT.smul c
  smul_covector hr hT := (isMicrolocallySmoothAt_smul_iff hr).2 hT
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  smulLeftCLM_iff hg hx := isMicrolocallySmoothAt_smulLeftCLM_iff hg hx
  restrictCLM_iff h _ _ hx _ := isMicrolocallySmoothAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph he he' hU hUΩ _ _ _ hx hT :=
    hT.compCLMOfOpenPartialHomeomorph _ he he' hU hUΩ hx

/-- **The wave front set under a change of variables, pointwise.** For `x ∈ U`, the pullback
`e^* T` is microlocally smooth at `(x, ξ)` exactly when `T` is microlocally smooth at
`(e x, (De⁻¹(e x))ᵀ ξ)`. -/
theorem isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x ξ ↔
      T.IsMicrolocallySmoothAt (e x) (((fderiv ℝ e.symm (e x))†) ξ) :=
  isInvariantMicrolocalRegularity_isMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph_iff hx

end Distribution

/-! ### The pullback of a cone -/

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Over a subset of the source of a change of variables `e`, the pullback `e^* Γ` consists of
the `(x, ξ)` with `x ∈ U` and `(e x, (De⁻¹(e x))ᵀ ξ) ∈ Γ`: the covector `η` with `De(x)ᵀ η = ξ` is
`(De⁻¹(e x))ᵀ ξ`. -/
theorem mem_covectorPullback_iff (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {U : Set E} (hU : U ⊆ e.source) {Γ : Set (E × E)} {p : E × E} :
    p ∈ TauCeti.covectorPullback e U Γ ↔
      p.1 ∈ U ∧ (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2) ∈ Γ := by
  rw [TauCeti.mem_covectorPullback]
  refine ⟨fun ⟨hx, η, hη, hηp⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hp⟩ ↦ ⟨hx, _, hp,
    e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn he he' (by simp) (hU hx) p.2⟩⟩
  rwa [← hηp,
    e.adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he he' (by simp) (hU hx) η]

/-- The pullback `e^* Γ` along a change of variables of a set `Γ` of nonzero covectors contains no
zero covectors, since the transposed derivative of `e` is injective. -/
theorem ne_zero_of_mem_covectorPullback (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {U : Set E} (hU : U ⊆ e.source) {Γ : Set (E × E)} (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0) {p : E × E}
    (hp : p ∈ TauCeti.covectorPullback e U Γ) : p.2 ≠ 0 := by
  obtain ⟨hx, η, hη, hηp⟩ := TauCeti.mem_covectorPullback.1 hp
  intro h0
  refine hΓ0 _ hη ?_
  rw [← e.adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he he' (by simp) (hU hx) η,
    hηp, h0, map_zero]

/-- **The pullback of a closed cone is closed.** If `Γ` is closed in `Ω × (E \ {0})`, then the
pullback `e^* Γ` along a change of variables is closed in `U × (E \ {0})`: over `U` it is the
preimage of `Γ` under the continuous map `(x, ξ) ↦ (e x, De⁻¹(e x)ᵀ ξ)`. -/
theorem isOpen_prod_compl_sdiff_covectorPullback (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {U Ω : Set E} (hUo : IsOpen U) (hU : U ⊆ e.source) (hUΩ : MapsTo e U Ω) {Γ : Set (E × E)}
    (hΓ : IsOpen ((Ω ×ˢ {0}ᶜ) \ Γ)) :
    IsOpen ((U ×ˢ {0}ᶜ) \ TauCeti.covectorPullback e U Γ) := by
  set Φ : E × E → E × E := fun p ↦ (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2)
  have hset : (U ×ˢ {0}ᶜ) \ TauCeti.covectorPullback e U Γ =
      (U ×ˢ {0}ᶜ) ∩ Φ ⁻¹' ((Ω ×ˢ {0}ᶜ) \ Γ) := by
    ext ⟨x, ξ⟩
    simp only [Set.mem_sdiff, mem_prod, mem_compl_iff, mem_singleton_iff, mem_inter_iff,
      mem_preimage, e.mem_covectorPullback_iff he he' hU, Φ]
    constructor
    · rintro ⟨⟨hx, hξ⟩, hn⟩
      refine ⟨⟨hx, hξ⟩, ⟨hUΩ hx, fun h0 ↦ hξ ?_⟩, fun hΓξ ↦ hn ⟨hx, hΓξ⟩⟩
      rw [← e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn he he' (by simp)
        (hU hx) ξ, h0, map_zero]
    · rintro ⟨⟨hx, hξ⟩, -, hn⟩
      exact ⟨⟨hx, hξ⟩, fun h ↦ hn h.2⟩
  rw [hset]
  have hcont : ContinuousOn Φ (U ×ˢ univ) := by
    have he1 : ContinuousOn (fun p : E × E ↦ e p.1) (U ×ˢ univ) :=
      (e.continuousOn.mono hU).comp continuousOn_fst fun p hp ↦ hp.1
    have hD : ContinuousOn (fun p : E × E ↦ (fderiv ℝ e.symm (e p.1))†) (U ×ˢ univ) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp_continuousOn
        ((he'.continuousOn_fderiv_of_isOpen e.open_target (by simp)).comp he1
          fun p hp ↦ e.map_source (hU hp.1))
    exact he1.prodMk (hD.clm_apply continuousOn_snd)
  exact (hcont.mono (prod_mono subset_rfl (subset_univ _))).isOpen_inter_preimage
    (hUo.prod isOpen_compl_singleton) hΓ

end OpenPartialHomeomorph

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **The wave front set under a change of variables** (Hörmander I, Theorem 8.2.4). The wave
front set of the pullback `e^* T` is the pullback `e^* WF(T)` (`TauCeti.covectorPullback`): it
consists of the `(x, ξ)` with `x ∈ U` and `(e x, (De⁻¹(e x))ᵀ ξ) ∈ WF(T)`
(`OpenPartialHomeomorph.mem_covectorPullback_iff`), so covectors pull back by the transpose of
the derivative. -/
theorem waveFrontSet_compCLMOfOpenPartialHomeomorph (T : 𝓓'(Ω, ℂ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).waveFrontSet =
      TauCeti.covectorPullback e U T.waveFrontSet := by
  ext ⟨x, ξ⟩
  rw [e.mem_covectorPullback_iff he he' hU]
  simpa only [mem_waveFrontSet_iff, mem_ofPred_eq, SetLike.mem_coe] using Set.ext_iff.1
    (isInvariantMicrolocalRegularity_isMicrolocallySmoothAt.setOf_compCLMOfOpenPartialHomeomorph
      (hUΩ := hUΩ) T) (x, ξ)

/-- If the wave front set of `T` lies in `Γ`, that of its pullback `e^* T` along a change of
variables lies in `e^* Γ = {(x, De(x)ᵀ η) | x ∈ U, (e x, η) ∈ Γ}` (`TauCeti.covectorPullback`). -/
theorem waveFrontSet_compCLMOfOpenPartialHomeomorph_subset {T : 𝓓'(Ω, ℂ)} {Γ : Set (E × E)}
    (hT : T.waveFrontSet ⊆ Γ) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).waveFrontSet ⊆
      TauCeti.covectorPullback e U Γ :=
  (waveFrontSet_compCLMOfOpenPartialHomeomorph T).trans_subset (TauCeti.covectorPullback_mono hT)

end Distribution
