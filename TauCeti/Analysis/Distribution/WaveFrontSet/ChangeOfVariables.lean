/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.NonstationaryPhase
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Normed.Module.Cone

/-!
# The wave front set under changes of variables

Let `e` be a smooth change of variables of a finite-dimensional real inner product space `E`: a
smooth open partial homeomorphism with smooth inverse, mapping an open set `U` of its source into
an open set `Ω`. A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that the wave front set is
invariant under such changes of variables, with covectors transforming by the transposed
derivative (Hörmander I, Theorem 8.2.4, for diffeomorphisms):

`(x, (De(x))† η) ∈ WF(e^* T) ↔ (e x, η) ∈ WF(T)` for `x ∈ U`.

This chart invariance is what allows the wave front set of a distribution on a manifold to be
defined as a subset of the cotangent bundle, with microlocal regularity read off in any chart.

## The argument

Cut `e^* T` off by a test function `φ` near `x`. Choose a cutoff `χ` near `e x` equal to one on
`e (supp φ)`, supported in a compact set `K` which meets none of its translates by the nonzero
vectors of a full lattice `L`. Expanding the pushed forward test function `e_* (φ e_ξ)` in its
Fourier series along `L` turns the localized Fourier transform of `e^* T` into the lattice series
(`Distribution.hasSum_localFourier_compCLMOfOpenPartialHomeomorph`)

`(e^* T)(φ e_ξ) = ∑ m, ((covolume L)⁻¹ ∫ φ(y) 𝐞(⟪e y, -m⟫ - ⟪y, ξ⟫) dy) T (χ e_(-m))`.

Suppose `T` is microlocally smooth at `(e x, η)`, so that `ζ ↦ T (χ e_ζ)` decays rapidly on an open
cone `Γ` around `η` and grows at most polynomially elsewhere. On an open cone `Γ'` around
`(De(x))† η` (`IsOpen.exists_cone_mul_add_le_norm_sub`), every term of the series is small:

* if `ζ = -m` lies in `Γ` and `‖ζ‖ ≥ c ‖ξ‖`, then `T (χ e_ζ)` is rapidly decreasing in `‖ζ‖`, hence
  in `‖ξ‖`;
* otherwise `(De(x))† ζ` is far from `ξ`, uniformly in the size of `ξ` and `ζ`, and since `De(y)`
  stays close to `De(x)` on the support of `φ`, the phase `⟪e y, ζ⟫ - ⟪y, ξ⟫` has gradient of size
  `‖ξ‖ + ‖ζ‖` there. Non-stationary phase
  (`TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le`) makes the coefficient rapidly
  decreasing in `‖ξ‖ + ‖ζ‖`, which beats the polynomial growth of `T (χ e_ζ)`.

Summing over the lattice shows that `(e^* T)(φ e_ξ)` decays rapidly for `ξ ∈ Γ'`. The converse
follows by pulling back along `e⁻¹`.

## Main results

* `Distribution.hasSum_localFourier_compCLMOfOpenPartialHomeomorph`: the lattice series for the
  localized Fourier transform of a pullback.
* `Distribution.IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph`: if `T` is microlocally
  smooth at `(e x, η)`, then `e^* T` is microlocally smooth at `(x, (De(x))† η)`.
* `Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`: the converse, for
  `x ∈ U`.
* `Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`: the wave front set of `e^* T` is the
  set of `(x, ξ)` with `x ∈ U` and `(e x, (De⁻¹(e x))† ξ) ∈ WF(T)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the wave front set of a pullback) and Theorem 7.7.1
  (non-stationary phase).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Lattice

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- A lattice series whose terms are bounded by `D (1 + ‖m‖)^(-d)`, with `d` above the rank, is
bounded by `D ∑ (1 + ‖m‖)^(-d)`, after multiplication by any `a > 0`. -/
private theorem mul_norm_le_of_hasSum {f : ZLattice.dual L → ℂ} {s : ℂ} (hs : HasSum f s)
    {a D : ℝ} (ha : 0 < a) {d : ℕ} (hd : Module.finrank ℤ (ZLattice.dual L) < d)
    (hf : ∀ m, a * ‖f m‖ ≤ D * ((1 + ‖(m : E)‖) ^ d)⁻¹) :
    a * ‖s‖ ≤ D * ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ d)⁻¹ := by
  have hsum := (ZLattice.summable_one_add_norm_pow_inv (ZLattice.dual L) hd).mul_left (D / a)
  have h := tsum_of_norm_bounded (f := f) hsum.hasSum fun m ↦ by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha, mul_comm]
    exact hf m
  rw [hs.tsum_eq, tsum_mul_left] at h
  rw [← le_div_iff₀' ha]
  calc ‖s‖ ≤ D / a * ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ d)⁻¹ := h
    _ = _ := by ring

/-- `(1 + a)ᴺ (1 + b)ᵏ (1 + b)ᵈ ≤ (1 + a + b)^(N + k + d)` for `a, b ≥ 0`. -/
private theorem one_add_pow_mul_one_add_pow_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N k d : ℕ) : (1 + a) ^ N * (1 + b) ^ k * (1 + b) ^ d ≤ (1 + a + b) ^ (N + k + d) := by
  have h1 : 1 + a ≤ 1 + a + b := by linarith
  have h2 : 1 + b ≤ 1 + a + b := by linarith
  rw [pow_add, pow_add]
  exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) h1 N)
    (pow_le_pow_left₀ (by positivity) h2 k) (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) h2 d) (by positivity) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A term of the lattice series of a pullback: either `ζ` lies in the cone `Γ` where `G` decays
rapidly and is not small compared with `ξ`, or the oscillatory coefficient `I` decays rapidly in
`‖ξ‖ + ‖ζ‖` while `G` grows at most polynomially. In both cases the term, weighted by
`(1 + ‖ξ‖) ^ N`, is `O((1 + ‖ζ‖) ^ (-d))`. -/
private theorem one_add_norm_pow_mul_norm_mul_le {Γ : Set E} {c M₀ Ca C₃ C₀ : ℝ} (hc : 0 < c)
    {N k₀ d : ℕ} {ξ ζ : E} {I G : ℂ} (hI : ‖I‖ ≤ M₀)
    (hGa : ζ ∈ Γ → (1 + ‖ζ‖) ^ (N + d) * ‖G‖ ≤ Ca) (hG : ‖G‖ ≤ C₀ * (1 + ‖ζ‖) ^ k₀)
    (hIb : (ζ ∉ Γ ∨ ‖ζ‖ < c * ‖ξ‖) → ‖I‖ ≤ C₃ / (1 + ‖ξ‖ + ‖ζ‖) ^ (N + k₀ + d))
    (hM₀ : 0 ≤ M₀) (hCa : 0 ≤ Ca) (hC₃ : 0 ≤ C₃) :
    (1 + ‖ξ‖) ^ N * (‖I‖ * ‖G‖) ≤
      (M₀ * Ca / min c 1 ^ N + C₃ * C₀) * ((1 + ‖ζ‖) ^ d)⁻¹ := by
  have hC₀ : 0 ≤ C₀ := by
    have := (norm_nonneg G).trans hG
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hc' : 0 < min c 1 := lt_min hc one_pos
  by_cases hcase : ζ ∉ Γ ∨ ‖ζ‖ < c * ‖ξ‖
  · -- Non-stationary case: the coefficient decays in `‖ξ‖ + ‖ζ‖`.
    have hI' := hIb hcase
    have hpow := one_add_pow_mul_one_add_pow_mul_le (norm_nonneg ξ) (norm_nonneg ζ) N k₀ d
    calc (1 + ‖ξ‖) ^ N * (‖I‖ * ‖G‖)
        ≤ (1 + ‖ξ‖) ^ N * (C₃ / (1 + ‖ξ‖ + ‖ζ‖) ^ (N + k₀ + d) * (C₀ * (1 + ‖ζ‖) ^ k₀)) := by
          gcongr
      _ = C₃ * C₀ * ((1 + ‖ξ‖) ^ N * (1 + ‖ζ‖) ^ k₀ * (1 + ‖ζ‖) ^ d) /
            (1 + ‖ξ‖ + ‖ζ‖) ^ (N + k₀ + d) * ((1 + ‖ζ‖) ^ d)⁻¹ := by
          field_simp
      _ ≤ C₃ * C₀ * 1 * ((1 + ‖ζ‖) ^ d)⁻¹ := by
          gcongr
          rw [mul_div_assoc]
          gcongr
          exact div_le_one_of_le₀ hpow (by positivity)
      _ ≤ _ := by
          rw [mul_one]
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  · -- Conic case: `G` decays rapidly at `ζ`, and `ξ` is at most comparable with `ζ`.
    rw [not_or, not_not, not_lt] at hcase
    have hGa' := hGa hcase.1
    have hξζ : min c 1 * (1 + ‖ξ‖) ≤ 1 + ‖ζ‖ := by
      have h1 : min c 1 ≤ 1 := min_le_right _ _
      have h2 : min c 1 * ‖ξ‖ ≤ c * ‖ξ‖ := by gcongr; exact min_le_left _ _
      nlinarith [hcase.2]
    calc (1 + ‖ξ‖) ^ N * (‖I‖ * ‖G‖)
        ≤ ((1 + ‖ζ‖) / min c 1) ^ N * (M₀ * ‖G‖) := by
          gcongr
          rwa [le_div_iff₀' hc']
      _ = M₀ / min c 1 ^ N * ((1 + ‖ζ‖) ^ (N + d) * ‖G‖) * ((1 + ‖ζ‖) ^ d)⁻¹ := by
          rw [div_pow, pow_add]
          field_simp
      _ ≤ M₀ / min c 1 ^ N * Ca * ((1 + ‖ζ‖) ^ d)⁻¹ := by gcongr
      _ ≤ _ := by
          gcongr
          rw [div_mul_eq_mul_div]
          exact le_add_of_nonneg_right (mul_nonneg hC₃ hC₀)

/-- **Decay of a lattice superposition of a pullback.** Let `G` grow at most polynomially and decay
rapidly on `Γ`, and let the coefficients `I ξ ζ` be bounded and decay rapidly in `‖ξ‖ + ‖ζ‖` where
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`. If, for `ξ ∈ Γ'`, this inequality holds whenever `ζ ∉ Γ` or `ζ` is
small compared with `ξ`, then `∑ m, a I ξ (-m) G (-m)` decays rapidly on `Γ'`. -/
private theorem exists_one_add_norm_pow_mul_norm_le_of_hasSum {Γ Γ' : Set E} {B : E →L[ℝ] E}
    {c : ℝ} (hc : 0 < c)
    (hsep : ∀ ξ ∈ Γ', ∀ ζ, (ζ ∉ Γ ∨ ‖ζ‖ < c * ‖ξ‖) → c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖)
    {G : E → ℂ} {C₀ : ℝ} {k₀ : ℕ} (hG : ∀ ζ, ‖G ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k₀)
    (hGdecay : ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ N * ‖G ζ‖ ≤ C) (hΓ : Γ.Nonempty)
    {I : E → E → ℂ} {M₀ : ℝ} (hI : ∀ ξ ζ, ‖I ξ ζ‖ ≤ M₀)
    (hIdecay : ∀ K : ℕ, ∃ C, ∀ ξ ζ, c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ →
      ‖I ξ ζ‖ ≤ C / (1 + ‖ξ‖ + ‖ζ‖) ^ K)
    {a : ℂ} {F : E → ℂ}
    (hF : ∀ ξ ∈ Γ', HasSum (fun m : ZLattice.dual L ↦ (a * I ξ (-m)) • G (-m)) (F ξ)) (N : ℕ) :
    ∃ C, ∀ ξ ∈ Γ', (1 + ‖ξ‖) ^ N * ‖F ξ‖ ≤ C := by
  set d := Module.finrank ℤ (ZLattice.dual L) + 1
  obtain ⟨Ca, hCa⟩ := hGdecay (N + d)
  obtain ⟨C₃, hC₃⟩ := hIdecay (N + k₀ + d)
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans (hI 0 0)
  have hCa0 : 0 ≤ Ca := by
    obtain ⟨ζ, hζ⟩ := hΓ
    exact (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖) ^ (N + d) * ‖G ζ‖).trans (hCa ζ hζ)
  have hC₃0 : 0 ≤ C₃ := by simpa using (norm_nonneg _).trans (hC₃ 0 0 (by simp))
  refine ⟨‖a‖ * (M₀ * Ca / min c 1 ^ N + C₃ * C₀) *
    ∑' m : ZLattice.dual L, ((1 + ‖(m : E)‖) ^ d)⁻¹, fun ξ hξ ↦ ?_⟩
  refine mul_norm_le_of_hasSum (hF ξ hξ) (by positivity) (Nat.lt_succ_self _) fun m ↦ ?_
  have h := one_add_norm_pow_mul_norm_mul_le hc (hI ξ (-m)) (hCa (-m)) (hG (-m))
    (fun h ↦ hC₃ ξ (-m) (hsep ξ hξ (-m) h)) hM₀ hCa0 hC₃0
  rw [norm_neg] at h
  rw [norm_smul, norm_mul]
  calc (1 + ‖ξ‖) ^ N * (‖a‖ * ‖I ξ (-m)‖ * ‖G (-m)‖)
      = ‖a‖ * ((1 + ‖ξ‖) ^ N * (‖I ξ (-m)‖ * ‖G (-m)‖)) := by ring
    _ ≤ ‖a‖ * ((M₀ * Ca / min c 1 ^ N + C₃ * C₀) * ((1 + ‖(m : E)‖) ^ d)⁻¹) := by gcongr
    _ = _ := by ring

end Lattice

section ChangeOfVariables

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
  have hgK : support g ⊆ K := fun y hy ↦
    χ.support_subset (by simp [show χ y = 1 from hg1 hy])
  set gK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset g.contDiff hgK
  have hgK' : ofSupportedIn hKΩ gK = g := by
    ext y
    simp [gK, ContDiffMapSupportedIn.coe_of_support_subset]
  have h := hasSum_localFourier_ofSupportedIn T hKΩ L hL (φ := gK) (χ := χ)
    (fun y hy ↦ hg1 (by simpa [gK, ContDiffMapSupportedIn.coe_of_support_subset] using hy)) 0
  -- The pairing of `e^* T` with `φ e_ξ` is the pairing of `T` with `g`.
  have h0 : T.localFourier (ofSupportedIn hKΩ gK) 0 =
      (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).localFourier φ ξ := by
    rw [hgK', localFourier_eq T g (ψ := g) fun y ↦ by simp, localFourier_def,
      complexPairing_compCLMOfOpenPartialHomeomorph]
  -- The Fourier coefficients of `g`, by changing variables `y = e x`.
  have hF (m : E) : 𝓕 (gK : E → ℂ) m = ∫ x, φ x * 𝐞 (⟪e x, -m⟫ - ⟪x, ξ⟫) := by
    rw [Real.fourier_eq]
    calc ∫ v, 𝐞 (-⟪v, m⟫) • gK v = ∫ v, g v • (𝐞 (-⟪v, m⟫) : ℂ) := by
          refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
          simp [gK, ContDiffMapSupportedIn.coe_of_support_subset, Circle.smul_def, mul_comm]
      _ = ∫ x, ψ x • (𝐞 (-⟪e x, m⟫) : ℂ) := integral_pushforwardCLM_smul volume ψ _
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [hψ, smul_eq_mul, inner_neg_right, sub_eq_add_neg, AddChar.map_add_eq_mul,
            Circle.coe_mul]
          ring
  rw [← h0]
  simpa only [hF, zero_sub] using h

/-- Near a point `x` of `U` there is a cutoff `φ` with `φ x = 1` such that `e` maps its support into
a given neighbourhood of `e x` and `(De(y))†` stays within `δ` of `(De(x))†` on its support. -/
private theorem exists_cutoff_adjoint_fderiv (hes : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hUs : (U : Set E) ⊆ e.source) {x : E} (hx : x ∈ U) {s : Set E} (hs : s ∈ 𝓝 (e x)) {δ : ℝ}
    (hδ : 0 < δ) : ∃ φ : 𝓓(U, ℂ), φ x = 1 ∧
      ∀ y ∈ tsupport φ, e y ∈ s ∧ ‖(fderiv ℝ e y)† - (fderiv ℝ e x)†‖ < δ := by
  have hxs : e.source ∈ 𝓝 x := e.open_source.mem_nhds (hUs hx)
  have hD : ContinuousAt (fun y ↦ (fderiv ℝ e y)†) x :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp
      ((hes.continuousOn_fderiv_of_isOpen e.open_source (by simp)).continuousAt hxs)
  have hev : ∀ᶠ y in 𝓝 x, ‖(fderiv ℝ e y)† - (fderiv ℝ e x)†‖ < δ :=
    (hD.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simpa using hδ))
  obtain ⟨φ, hφW, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) (Ω := U)
    (inter_mem (U.isOpen.mem_nhds hx)
      (inter_mem ((hes.continuousOn.continuousAt hxs).preimage_mem_nhds hs) hev))
    inter_subset_left (1 : ℂ)
  exact ⟨φ, hφx, fun y hy ↦ (hφW hy).2⟩

/-- **Microlocal smoothness under a change of variables** (Hörmander I, Theorem 8.2.4, for
diffeomorphisms). If `T` is microlocally smooth at `(e x, η)`, then its pullback `e^* T` along the
smooth change of variables `e` is microlocally smooth at `(x, (De(x))† η)`: covectors transform by
the transpose of the derivative. -/
theorem IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph {T : 𝓓'(Ω, ℂ)} {x η : E}
    (hx : x ∈ U) (h : T.IsMicrolocallySmoothAt (e x) η) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x
      (((fderiv ℝ e x)†) η) := by
  borelize E
  have hxs : x ∈ e.source := hU hx
  -- Rapid decay of `T` near `(e x, η)` for a cutoff `χ` adapted to a lattice.
  obtain ⟨U₀, hU₀, Γ, hΓ, hηΓ, hcone, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨K, K₁, hKU, hK₁x, -, ⟨χ, hχ1⟩, L, _, _, hL⟩ :=
    exists_compacts_cutoff_lattice (hUΩ hx) hU₀
  have hKΩ : (K : Set E) ⊆ Ω := hKU.trans inter_subset_right
  obtain ⟨C₀, k₀, hG⟩ := exists_norm_localFourier_le T (ofSupportedIn hKΩ χ)
  -- The cone `Γ'` around `(De x)† η` separated from the complement of `Γ`.
  obtain ⟨hd, hds⟩ :=
    e.differentiableAt_and_differentiableAt_symm_of_contDiffOn he he' (by simp) hxs
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hxs hd hds
  obtain ⟨Γ', hΓ', hξΓ', hcone', c, hc, hsep⟩ :=
    hΓ.exists_cone_mul_add_le_norm_sub hcone hηΓ A.adjointEquiv
  have hB : (A.adjointEquiv : E →L[ℝ] E) = (fderiv ℝ e x)† := by
    ext v
    simp [hA]
  -- A cutoff `φ` near `x`, and a globally smooth map agreeing with `e` near its support.
  obtain ⟨φ, hφx, hφ⟩ := exists_cutoff_adjoint_fderiv he hU hx hK₁x (half_pos hc)
  obtain ⟨f, hf, -, -, -, hfe⟩ := he.exists_contDiff_eventuallyEq_on_isCompact
    φ.hasCompactSupport e.open_source (φ.tsupport_subset.trans hU)
  have hI (ξ ζ : E) : ∫ y, φ y * 𝐞 (⟪e y, ζ⟫ - ⟪y, ξ⟫) =
      ∫ y, φ y * 𝐞 (⟪f y, ζ⟫ - ⟪y, ξ⟫) := by
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ tsupport φ
    · simp only [(hfe y hy).self_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  refine isMicrolocallySmoothAt_iff.2
    ⟨φ, by simp [hφx], Γ', hΓ', by rw [← hA]; simpa using hξΓ', hcone', fun N ↦ ?_⟩
  refine exists_one_add_norm_pow_mul_norm_le_of_hasSum (B := (A.adjointEquiv : E →L[ℝ] E)) hc hsep
    hG
    (hdecay (ofSupportedIn hKΩ χ) (χ.tsupport_subset.trans (hKU.trans inter_subset_left)))
    ⟨η, hηΓ⟩ (I := fun ξ ζ ↦ ∫ y, φ y * 𝐞 (⟪e y, ζ⟫ - ⟪y, ξ⟫)) (M₀ := ∫ y, ‖φ y‖)
    (fun ξ ζ ↦ (norm_integral_le_integral_norm _).trans_eq (by simp)) (fun K ↦ ?_)
    (fun ξ _ ↦ hasSum_localFourier_compCLMOfOpenPartialHomeomorph T hKΩ L hL
      (fun y hy ↦ hχ1 _ (hφ y hy).1) ξ) N
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_integral_mul_fourierChar_inner_sub_le hf φ.contDiff
    φ.hasCompactSupport hc (B := (A.adjointEquiv : E →L[ℝ] E)) (fun y hy ↦ by
      rw [(hfe y hy).fderiv_eq, hB]
      exact (hφ y hy).2.le) K
  exact ⟨C, fun ξ ζ hξζ ↦ by simpa only [hI] using hC ξ ζ hξζ⟩

/-- **Microlocal smoothness is invariant under changes of variables.** For `x ∈ U`, the pullback
`e^* T` is microlocally smooth at `(x, (De(x))† η)` exactly when `T` is microlocally smooth at
`(e x, η)`. -/
theorem isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff {T : 𝓓'(Ω, ℂ)} {x η : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySmoothAt x
        (((fderiv ℝ e x)†) η) ↔ T.IsMicrolocallySmoothAt (e x) η := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLMOfOpenPartialHomeomorph hx⟩
  -- Pull `e^* T` back along `e⁻¹` from the image `V = e '' U`, which gives back `T` on `V`.
  have hxs : x ∈ e.source := hU hx
  let V : Opens E := ⟨e '' U, e.isOpen_image_of_subset_source U.isOpen hU⟩
  have hVΩ : V ≤ Ω := image_subset_iff.2 hUΩ
  have hVt : (V : Set E) ⊆ e.symm.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hU hz)
  have hVU : MapsTo e.symm V U := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [e.left_inv (hU hz)]
  have hUV : MapsTo e U V := fun z hz ↦ ⟨z, hz, rfl⟩
  have hres : compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T =
      compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T) := by
    rw [← restrictCLM_compCLMOfOpenPartialHomeomorph le_rfl hVΩ, restrictCLM_self]
  rw [hres] at h
  have h₁ : (compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T)).IsMicrolocallySmoothAt
      (e.symm (e x)) (((fderiv ℝ e x)†) η) := by
    rwa [e.left_inv hxs]
  have h' := h₁.compCLMOfOpenPartialHomeomorph (e := e.symm) (he := he')
    (he' := by simpa using he) (hU := hVt) (hUΩ := hVU) ⟨x, hx, rfl⟩
  have hback := compCLMOfOpenPartialHomeomorph_symm_apply_apply (e := e) (he := he) (he' := he')
    (hU := hU) (hUV := hUV) (he₁ := he') (he₁' := by simpa using he) (hV := hVt) (hVU := hVU)
    (restrictCLM T : 𝓓'(V, ℂ))
  rw [hback] at h'
  obtain ⟨hd, hds⟩ :=
    e.differentiableAt_and_differentiableAt_symm_of_contDiffOn he he' (by simp) hxs
  rw [e.adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_mem_source hxs hd hds] at h'
  exact (isMicrolocallySmoothAt_restrictCLM_iff hVΩ ⟨x, hx, rfl⟩).1 h'

/-- **The wave front set under a change of variables.** The wave front set of the pullback `e^* T`
along a smooth change of variables `e` with smooth inverse consists of the `(x, ξ)` with `x ∈ U`
and `(e x, (De⁻¹(e x))† ξ)` in the wave front set of `T`: positions move by `e⁻¹` and covectors by
the transposed derivative, `ξ = (De(x))† η`. -/
theorem waveFrontSet_compCLMOfOpenPartialHomeomorph (T : 𝓓'(Ω, ℂ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).waveFrontSet =
      (U : Set E) ×ˢ univ ∩
        (fun p : E × E ↦ (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2)) ⁻¹' T.waveFrontSet := by
  have hinv {x : E} (hx : x ∈ U) (ξ : E) :
      ((fderiv ℝ e x)†) (((fderiv ℝ e.symm (e x))†) ξ) = ξ :=
    have hd :=
      e.differentiableAt_and_differentiableAt_symm_of_contDiffOn he he' (by simp) (hU hx)
    e.adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_mem_source (hU hx) hd.1 hd.2 ξ
  ext ⟨x, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage]
  refine ⟨fun ⟨hx, hξ, hT⟩ ↦ ⟨hx, hUΩ hx, fun h0 ↦ hξ ?_, fun h ↦ hT ?_⟩,
    fun ⟨hx, _, hη, hT⟩ ↦ ⟨hx, fun h0 ↦ hη (by simp [h0]), fun h ↦ hT ?_⟩⟩
  · rw [← hinv hx ξ, h0, map_zero]
  · rwa [← isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff hx, hinv hx] at h
  · rwa [← isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff hx, hinv hx]

end ChangeOfVariables

end Distribution
