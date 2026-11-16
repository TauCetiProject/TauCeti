/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.RealInterpolation
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Complex interpolation of the Hilbert scale of Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space, `H` a complex Hilbert space and
`H^s = H^{s,2}(E, H)` Mathlib's Bessel-potential spaces. For real orders `s₀`, `s₁` the spaces
`H^{s₀}` and `H^{s₁}` form a compatible couple inside the tempered distributions
(`TauCeti.CompatibleCouple.besselPotentialSpace`). This file proves that for `0 ≤ θ ≤ 1` its
complex interpolation space is again a Bessel-potential space, isometrically:

`[H^{s₀}, H^{s₁}]_θ = H^{s_θ}`, `s_θ = (1 - θ) s₀ + θ s₁`

(`TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodEquiv`). No condition `s₀ ≠ s₁` is
needed, and the norms agree exactly, not only up to equivalence. The tool on both sides is the
Bessel potential `J^w` of complex order (`SchwartzMap.besselPotentialCLM`): the `H^r` norm of
`J^w f` is the `H^{r + re w}` norm of `f`, and `w ↦ J^w f` is holomorphic with values in every
`H^r`.

* `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ`. For a Schwartz function `f` the admissible function
  `F z = exp (δ (z - θ)²) J^{(θ - z) (s₁ - s₀)} f`, `δ > 0`, equals `f` at `θ`, and on the line
  `re z = j` its value lies in `H^{s_j}` with norm `|exp (δ (j + i t - θ)²)| ‖f‖_{H^{s_θ}}`.
  Letting `δ → 0` bounds the interpolation norm of `f` by `‖f‖_{H^{s_θ}}`, and Schwartz functions
  are dense in `H^{s_θ}`.
* `[H^{s₀}, H^{s₁}]_θ ⊆ H^{s_θ}`. Let `m = min s₀ s₁`, so that `H^{s₀} + H^{s₁} ⊆ H^m`. For an
  admissible function `F` with boundary traces `g` and a Schwartz function `v`, the pairing
  `z ↦ ⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}` is holomorphic on the strip and bounded on its
  boundary lines by `‖g‖ ‖v‖_{H^{2m - s_θ}}`, so by Hadamard's three-lines theorem the same bound
  holds for `⟪v, F θ⟫_{H^m}`. An element of `H^m` whose `H^m` inner products with Schwartz
  functions are bounded in this way lies in `H^{s_θ}`, by the Riesz representation theorem in
  `H^{s_θ}`.

## Main declarations

* `TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodEquiv`: the isometric isomorphism
  `[H^{s₀}, H^{s₁}]_θ ≃ H^{s_θ}`, which keeps the underlying tempered distribution
  (`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceComplexMethodEquiv_apply`,
  `TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply`).
* `TauCeti.CompatibleCouple.exists_complexMethodSpace_toSum_eq_iff_memSobolev`: an element of
  `H^{s₀} + H^{s₁}` lies in `[H^{s₀}, H^{s₁}]_θ` exactly when its tempered distribution lies in
  `H^{s_θ}`.
* `TauCeti.CompatibleCouple.besselPotentialSpace_fstToSum_toBesselPotentialSpaceCLM`: a Schwartz
  function has the same class in `H^{s₀,p} + H^{s₁,p}` whichever endpoint it is read in.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.1,
  Theorem 5.4.1 and Theorem 6.4.5 (7).
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §1.18.5 and §2.4.2.
-/

public section

noncomputable section

open Complex Filter Set Topology SchwartzMap BesselPotentialSpace
open scoped ENNReal SchwartzMap BesselPotentialSpace ZeroAtInfty

namespace TauCeti

namespace CompatibleCouple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Schwartz

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ : ℝ}

/-- A Schwartz function has the same class in the sum space `H^{s₀,p} + H^{s₁,p}` whether it is
read in `H^{s₀,p}` or in `H^{s₁,p}`. -/
theorem besselPotentialSpace_fstToSum_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    (besselPotentialSpace E F p s₀ s₁).fstToSum (toBesselPotentialSpaceCLM s₀ p f) =
      (besselPotentialSpace E F p s₀ s₁).sndToSum (toBesselPotentialSpaceCLM s₁ p f) :=
  (besselPotentialSpace E F p s₀ s₁).sumSpace_ext <| by
    rw [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besselPotentialSpace_embed₀_apply,
      besselPotentialSpace_embed₁_apply, toDistr_toBesselPotentialSpaceCLM,
      toDistr_toBesselPotentialSpaceCLM]

end Schwartz

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s₀ s₁ θ δ : ℝ}

/-! ### The admissible function of a Schwartz function -/

/-- The Bessel potential `J^{(θ - z) (s₁ - s₀)} f` of a Schwartz function, read in `H^r`. -/
private def besselShift (s₀ s₁ θ r : ℝ) (f : 𝓢(E, H)) (z : ℂ) : H^{r}(E, H) :=
  toBesselPotentialSpaceCLM r 2 (besselPotentialCLM (((θ : ℂ) - z) * ((s₁ - s₀ : ℝ) : ℂ)) f)

private theorem differentiable_besselShift (s₀ s₁ θ r : ℝ) (f : 𝓢(E, H)) :
    Differentiable ℂ (besselShift s₀ s₁ θ r f) := fun z ↦
  ((hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM r f _).scomp z
    (((hasDerivAt_id' z).const_sub (θ : ℂ)).mul_const ((s₁ - s₀ : ℝ) : ℂ))).differentiableAt

private theorem norm_besselShift (s₀ s₁ θ r : ℝ) (f : 𝓢(E, H)) (z : ℂ) :
    ‖besselShift s₀ s₁ θ r f z‖ =
      ‖toBesselPotentialSpaceCLM (r + (θ - z.re) * (s₁ - s₀)) 2 f‖ := by
  have hre : (((θ : ℂ) - z) * ((s₁ - s₀ : ℝ) : ℂ)).re = (θ - z.re) * (s₁ - s₀) := by simp
  rw [besselShift, norm_toBesselPotentialSpaceCLM_besselPotentialCLM, hre]

private theorem norm_besselShift_mul_I (s₀ s₁ θ : ℝ) (f : 𝓢(E, H)) (t : ℝ) :
    ‖besselShift s₀ s₁ θ s₀ f (t * I)‖ =
      ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  rw [norm_besselShift,
    show s₀ + (θ - ((t : ℂ) * I).re) * (s₁ - s₀) = (1 - θ) * s₀ + θ * s₁ by simp; ring]

private theorem norm_besselShift_one_add_mul_I (s₀ s₁ θ : ℝ) (f : 𝓢(E, H)) (t : ℝ) :
    ‖besselShift s₀ s₁ θ s₁ f (1 + t * I)‖ =
      ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  rw [norm_besselShift,
    show s₁ + (θ - (1 + (t : ℂ) * I).re) * (s₁ - s₀) = (1 - θ) * s₀ + θ * s₁ by simp; ring]

private theorem norm_besselShift_le (s₀ s₁ θ r : ℝ) (f : 𝓢(E, H)) {z : ℂ}
    (hz : z.re ∈ Icc 0 1) :
    ‖besselShift s₀ s₁ θ r f z‖ ≤
      ‖toBesselPotentialSpaceCLM (r + (|θ| + 1) * |s₁ - s₀|) 2 f‖ := by
  have habs : |θ - z.re| ≤ |θ| + 1 :=
    abs_le.2 ⟨by linarith [neg_abs_le θ, hz.2], by linarith [le_abs_self θ, hz.1]⟩
  have hle : r + (θ - z.re) * (s₁ - s₀) ≤ r + (|θ| + 1) * |s₁ - s₀| := by
    have h := (le_abs_self ((θ - z.re) * (s₁ - s₀))).trans_eq (abs_mul _ _)
    nlinarith [abs_nonneg (s₁ - s₀)]
  rw [norm_besselShift, ← inclusion_toBesselPotentialSpaceCLM hle]
  exact norm_inclusion_apply_le _ _

private theorem continuous_besselTrace₀ (s₀ s₁ θ δ : ℝ) (f : 𝓢(E, H)) :
    Continuous fun t : ℝ ↦ stripGaussian δ θ (t * I) • besselShift s₀ s₁ θ s₀ f (t * I) :=
  ((differentiable_stripGaussian δ θ).continuous.comp (by fun_prop)).smul
    ((differentiable_besselShift s₀ s₁ θ s₀ f).continuous.comp (by fun_prop))

private theorem continuous_besselTrace₁ (s₀ s₁ θ δ : ℝ) (f : 𝓢(E, H)) :
    Continuous fun t : ℝ ↦
      stripGaussian δ θ (1 + t * I) • besselShift s₀ s₁ θ s₁ f (1 + t * I) :=
  ((differentiable_stripGaussian δ θ).continuous.comp (by fun_prop)).smul
    ((differentiable_besselShift s₀ s₁ θ s₁ f).continuous.comp (by fun_prop))

private theorem tendsto_besselTrace₀ (s₀ s₁ θ : ℝ) (hδ : 0 < δ) (f : 𝓢(E, H)) :
    Tendsto (fun t : ℝ ↦ stripGaussian δ θ (t * I) • besselShift s₀ s₁ θ s₀ f (t * I))
      (cocompact ℝ) (𝓝 0) := by
  set N := ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖
  have h (t : ℝ) : ‖stripGaussian δ θ (t * I) • besselShift s₀ s₁ θ s₀ f (t * I)‖ ≤
      ‖stripGaussian δ θ (t * I)‖ * N := by
    rw [norm_smul, norm_besselShift_mul_I]
  exact squeeze_zero_norm h (by simpa using (tendsto_norm_stripGaussian hδ θ 0).mul_const N)

private theorem tendsto_besselTrace₁ (s₀ s₁ θ : ℝ) (hδ : 0 < δ) (f : 𝓢(E, H)) :
    Tendsto (fun t : ℝ ↦ stripGaussian δ θ (1 + t * I) • besselShift s₀ s₁ θ s₁ f (1 + t * I))
      (cocompact ℝ) (𝓝 0) := by
  set N := ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖
  have h (t : ℝ) : ‖stripGaussian δ θ (1 + t * I) • besselShift s₀ s₁ θ s₁ f (1 + t * I)‖ ≤
      ‖stripGaussian δ θ (1 + t * I)‖ * N := by
    rw [norm_smul, norm_besselShift_one_add_mul_I]
  exact squeeze_zero_norm h (by simpa using (tendsto_norm_stripGaussian hδ θ 1).mul_const N)

/-- The boundary traces of the admissible function `exp (δ (z - θ)²) J^{(θ - z) (s₁ - s₀)} f`. -/
private def besselTrace (s₀ s₁ θ : ℝ) (hδ : 0 < δ) (f : 𝓢(E, H)) :
    C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H)) :=
  (⟨⟨_, continuous_besselTrace₀ s₀ s₁ θ δ f⟩, tendsto_besselTrace₀ s₀ s₁ θ hδ f⟩,
    ⟨⟨_, continuous_besselTrace₁ s₀ s₁ θ δ f⟩, tendsto_besselTrace₁ s₀ s₁ θ hδ f⟩)

private theorem isStripFunction_besselTrace (hδ : 0 < δ) (f : 𝓢(E, H)) :
    (besselPotentialSpace E H 2 s₀ s₁).IsStripFunction
      (fun z ↦ stripGaussian δ θ z •
        (besselPotentialSpace E H 2 s₀ s₁).fstToSum (besselShift s₀ s₁ θ s₀ f z))
      (besselTrace s₀ s₁ θ hδ f) where
  diffContOnCl := ((differentiable_stripGaussian δ θ).smul
    ((besselPotentialSpace E H 2 s₀ s₁).fstToSum.differentiable.comp
      (differentiable_besselShift s₀ s₁ θ s₀ f))).diffContOnCl
  isBounded := by
    refine isBounded_iff_forall_norm_le.2 ⟨Real.exp (δ * (|θ| + 1) ^ 2) *
      ‖toBesselPotentialSpaceCLM (s₀ + (|θ| + 1) * |s₁ - s₀|) 2 f‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_smul]
    exact mul_le_mul (norm_stripGaussian_le hδ.le θ hz)
      (((besselPotentialSpace E H 2 s₀ s₁).norm_fstToSum_le _).trans
        (norm_besselShift_le s₀ s₁ θ s₀ f hz)) (norm_nonneg _) (Real.exp_pos _).le
  apply_mul_I t := by simp [besselTrace]
  apply_one_add_mul_I t := by
    simp [besselTrace, besselShift, besselPotentialSpace_fstToSum_toBesselPotentialSpaceCLM]

private theorem besselTrace_mem (hδ : 0 < δ) (f : 𝓢(E, H)) :
    besselTrace s₀ s₁ θ hδ f ∈ (besselPotentialSpace E H 2 s₀ s₁).stripTraces :=
  mem_stripTraces_iff.2 ⟨_, isStripFunction_besselTrace hδ f⟩

private theorem stripEval_besselTrace (hδ : 0 < δ) (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    (besselPotentialSpace E H 2 s₀ s₁).stripEval θ
        ⟨besselTrace s₀ s₁ θ hδ f, besselTrace_mem hδ f⟩ =
      (besselPotentialSpace E H 2 s₀ s₁).fstToSum (toBesselPotentialSpaceCLM s₀ 2 f) := by
  rw [stripEval_apply, stripFunction_eq (isStripFunction_besselTrace hδ f) (by simpa using hθ)]
  simp [besselShift]

private theorem norm_besselTrace_le (hδ : 0 < δ) (f : 𝓢(E, H)) :
    ‖besselTrace s₀ s₁ θ hδ f‖ ≤
      Real.exp (δ * (|θ| + 1) ^ 2) * ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t ↦ ?_,
    (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t ↦ ?_⟩
  · -- Evaluating the bundled trace at `t` gives its defining formula.
    change ‖stripGaussian δ θ (t * I) • besselShift s₀ s₁ θ s₀ f (t * I)‖ ≤ _
    rw [norm_smul, norm_besselShift_mul_I]
    exact mul_le_mul_of_nonneg_right (norm_stripGaussian_le hδ.le θ (by simp)) (norm_nonneg _)
  · -- Evaluating the bundled trace at `t` gives its defining formula.
    change ‖stripGaussian δ θ (1 + t * I) • besselShift s₀ s₁ θ s₁ f (1 + t * I)‖ ≤ _
    rw [norm_smul, norm_besselShift_one_add_mul_I]
    exact mul_le_mul_of_nonneg_right (norm_stripGaussian_le hδ.le θ (by simp)) (norm_nonneg _)

/-! ### The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` -/

variable (E H s₀ s₁) in
/-- The inclusion of Schwartz functions into `[H^{s₀}, H^{s₁}]_θ`, through the admissible function
`exp ((z - θ)²) J^{(θ - z) (s₁ - s₀)} f`. -/
private def schwartzToComplexMethod (hθ : θ ∈ Icc 0 1) :
    𝓢(E, H) →ₗ[ℂ] (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ where
  toFun f := ComplexMethodSpace.mk θ ⟨besselTrace s₀ s₁ θ one_pos f, besselTrace_mem one_pos f⟩
  map_add' f g := ComplexMethodSpace.ext <| by
    simp only [map_add, ComplexMethodSpace.toSum_mk, stripEval_besselTrace one_pos hθ]
  map_smul' c f := ComplexMethodSpace.ext <| by
    simp only [map_smul, ComplexMethodSpace.toSum_mk, stripEval_besselTrace one_pos hθ,
      RingHom.id_apply]

private theorem toSum_schwartzToComplexMethod (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    ComplexMethodSpace.toSum (schwartzToComplexMethod E H s₀ s₁ hθ f) =
      (besselPotentialSpace E H 2 s₀ s₁).fstToSum (toBesselPotentialSpaceCLM s₀ 2 f) :=
  (ComplexMethodSpace.toSum_mk _).trans (stripEval_besselTrace one_pos hθ f)

private theorem norm_schwartzToComplexMethod_le (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    ‖schwartzToComplexMethod E H s₀ s₁ hθ f‖ ≤
      ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  set N := ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖
  have key (δ : ℝ) (hδ : 0 < δ) :
      ‖schwartzToComplexMethod E H s₀ s₁ hθ f‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * N := by
    have h : schwartzToComplexMethod E H s₀ s₁ hθ f =
        ComplexMethodSpace.mk θ ⟨besselTrace s₀ s₁ θ hδ f, besselTrace_mem hδ f⟩ :=
      ComplexMethodSpace.ext <| by
        rw [toSum_schwartzToComplexMethod, ComplexMethodSpace.toSum_mk,
          stripEval_besselTrace hδ hθ]
    rw [h]
    exact (ComplexMethodSpace.norm_mk_le _).trans (norm_besselTrace_le hδ f)
  have hlim : Tendsto (fun δ : ℝ ↦ Real.exp (δ * (|θ| + 1) ^ 2) * N) (𝓝[>] 0) (𝓝 N) := by
    have : Continuous fun δ : ℝ ↦ Real.exp (δ * (|θ| + 1) ^ 2) * N := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

variable (E H s₀ s₁) in
/-- The inclusion of `H^{s_θ}` into `[H^{s₀}, H^{s₁}]_θ`, the continuous extension of
`schwartzToComplexMethod`. -/
private def besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1) :
    H^{(1 - θ) * s₀ + θ * s₁}(E, H) →L[ℂ]
      (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ :=
  (schwartzToComplexMethod E H s₀ s₁ hθ).extendOfNorm
    (toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2).toLinearMap

private theorem denseRange_toBesselPotentialSpaceCLM_two (s : ℝ) :
    DenseRange (toBesselPotentialSpaceCLM (E := E) (F := H) s 2) :=
  denseRange_toBesselPotentialSpaceCLM s ENNReal.ofNat_ne_top

private theorem besselPotentialSpaceToComplexMethod_toBesselPotentialSpaceCLM
    (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ
        (toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f) =
      schwartzToComplexMethod E H s₀ s₁ hθ f :=
  LinearMap.extendOfNorm_eq (denseRange_toBesselPotentialSpaceCLM_two _)
    ⟨1, fun f ↦ by simpa using norm_schwartzToComplexMethod_le hθ f⟩ f

/-- The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` keeps the underlying tempered distribution. -/
private theorem sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1)
    (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u)) =
      u.toDistr := by
  refine (denseRange_toBesselPotentialSpaceCLM_two _).induction_on u
    (isClosed_eq ((besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed.comp
      (ComplexMethodSpace.toSum.comp (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ))).continuous
      continuous_toDistr) fun f ↦ ?_
  rw [besselPotentialSpaceToComplexMethod_toBesselPotentialSpaceCLM,
    toSum_schwartzToComplexMethod, sumSpaceEmbed_fstToSum, besselPotentialSpace_embed₀_apply,
    toDistr_toBesselPotentialSpaceCLM, toDistr_toBesselPotentialSpaceCLM]

/-- The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` does not increase norms:
`‖u‖_{[H^{s₀}, H^{s₁}]_θ} ≤ ‖u‖_{H^{s_θ}}`. -/
private theorem norm_besselPotentialSpaceToComplexMethod_le (hθ : θ ∈ Icc 0 1)
    (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    ‖besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u‖ ≤ ‖u‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le (denseRange_toBesselPotentialSpaceCLM_two _) 1
    (fun f ↦ by simpa using norm_schwartzToComplexMethod_le hθ f) u
  rw [one_mul] at h
  exact h

/-! ### The `H^m` pairing with Schwartz functions -/

section Pairing

open scoped InnerProductSpace ComplexConjugate

private theorem norm_toBesselPotentialSpaceCLM_congr {r r' : ℝ} (h : r = r') (φ : 𝓢(E, H)) :
    ‖toBesselPotentialSpaceCLM r 2 φ‖ = ‖toBesselPotentialSpaceCLM r' 2 φ‖ := by
  subst h
  rfl

private theorem besselPotentialCLM_ofReal_comp (a b : ℝ) (u : 𝓢(E, H)) :
    besselPotentialCLM (b : ℂ) (besselPotentialCLM (a : ℂ) u) =
      besselPotentialCLM ((a + b : ℝ) : ℂ) u := by
  rw [besselPotentialCLM_besselPotentialCLM_apply]
  push_cast
  rfl

/-- Bessel potentials of real order are symmetric for the `L²` inner product of Schwartz
functions. -/
private theorem inner_toLp_besselPotentialCLM_left (a : ℝ) (X Y : 𝓢(E, H)) :
    ⟪(besselPotentialCLM (a : ℂ) X).toLp 2, Y.toLp 2⟫_ℂ =
      ⟪X.toLp 2, (besselPotentialCLM (a : ℂ) Y).toLp 2⟫_ℂ := by
  have h0 := inner_toLp_toBesselPotentialSpaceCLM_neg 0 (besselPotentialCLM (a : ℂ) X) Y
  have ha := inner_toLp_toBesselPotentialSpaceCLM_neg a (besselPotentialCLM (a : ℂ) X) Y
  rw [neg_zero, toLp_toBesselPotentialSpaceCLM_zero, toLp_toBesselPotentialSpaceCLM_zero] at h0
  rw [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, besselPotentialCLM_ofReal_comp,
    add_neg_cancel, ofReal_zero, besselPotentialCLM_zero, ContinuousLinearMap.id_apply] at ha
  rw [h0, ← ha]

/-- For `Y ∈ H^r` and `m ≤ r`, the `H^m` inner product of `Y` with a Schwartz function `φ` is the
`H^r` inner product of `Y` with `J^{2 (m - r)} φ`. -/
private theorem inner_inclusion_toBesselPotentialSpaceCLM {m r : ℝ} (h : m ≤ r)
    (Y : H^{r}(E, H)) (φ : 𝓢(E, H)) :
    ⟪inclusion h Y, toBesselPotentialSpaceCLM m 2 φ⟫_ℂ =
      ⟪Y, toBesselPotentialSpaceCLM r 2 (besselPotentialCLM ((2 * (m - r) : ℝ) : ℂ) φ)⟫_ℂ := by
  refine (denseRange_toBesselPotentialSpaceCLM_two r).induction_on Y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun ψ ↦ ?_
  rw [inclusion_toBesselPotentialSpaceCLM, ← inner_toLp_toLp, ← inner_toLp_toLp,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM, besselPotentialCLM_ofReal_comp,
    show besselPotentialCLM (m : ℂ) ψ =
      besselPotentialCLM ((m - r : ℝ) : ℂ) (besselPotentialCLM (r : ℂ) ψ) by
        rw [besselPotentialCLM_ofReal_comp, add_sub_cancel],
    inner_toLp_besselPotentialCLM_left, besselPotentialCLM_ofReal_comp]
  congr 4
  push_cast
  ring

/-- For `x ∈ H^s` and `m ≤ s`, the `H^m` inner product of a Schwartz function `φ` with `x` is
bounded by `‖φ‖_{H^{2m - s}} ‖x‖_{H^s}`. -/
private theorem norm_inner_inclusion_le {m s : ℝ} (h : m ≤ s) (φ : 𝓢(E, H)) (x : H^{s}(E, H)) :
    ‖⟪toBesselPotentialSpaceCLM m 2 φ, inclusion h x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (2 * m - s) 2 φ‖ * ‖x‖ := by
  rw [norm_inner_symm, inner_inclusion_toBesselPotentialSpaceCLM]
  refine (norm_inner_le_norm _ _).trans_eq ?_
  rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM,
    norm_toBesselPotentialSpaceCLM_congr (r' := 2 * m - s) (by simp only [ofReal_re]; ring),
    mul_comm]

/-- **A duality criterion for `H^r`.** Let `m ≤ r` and `M ≥ 0`. If the `H^m` inner products of
`y ∈ H^m` with Schwartz functions `φ` are bounded by `M ‖φ‖_{H^{2m - r}}`, then `y` lies in `H^r`,
with norm at most `M`. -/
private theorem exists_inclusion_eq_and_norm_le {m r M : ℝ} (hmr : m ≤ r) (hM : 0 ≤ M)
    (y : H^{m}(E, H))
    (hy : ∀ φ : 𝓢(E, H), ‖⟪toBesselPotentialSpaceCLM m 2 φ, y⟫_ℂ‖ ≤
      M * ‖toBesselPotentialSpaceCLM (2 * m - r) 2 φ‖) :
    ∃ Y : H^{r}(E, H), inclusion hmr Y = y ∧ ‖Y‖ ≤ M := by
  -- The functional `χ ↦ ⟪y, J^{2 (r - m)} χ⟫_{H^m}` is bounded in the `H^r` norm.
  let L : 𝓢(E, H) →ₗ[ℂ] ℂ :=
    { toFun χ := ⟪y, toBesselPotentialSpaceCLM m 2
        (besselPotentialCLM ((2 * (r - m) : ℝ) : ℂ) χ)⟫_ℂ
      map_add' χ χ' := by simp [inner_add_right]
      map_smul' a χ := by simp [inner_smul_right] }
  have hL (χ : 𝓢(E, H)) : ‖L χ‖ ≤ M * ‖toBesselPotentialSpaceCLM r 2 χ‖ := by
    -- `L χ` is by definition the inner product `⟪y, J^{2 (r - m)} χ⟫_{H^m}`.
    change ‖⟪y, _⟫_ℂ‖ ≤ _
    rw [norm_inner_symm]
    refine (hy _).trans_eq ?_
    rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM,
      norm_toBesselPotentialSpaceCLM_congr (r' := r) (by simp only [ofReal_re]; ring)]
  have hdense := denseRange_toBesselPotentialSpaceCLM_two (E := E) (H := H) r
  set Λ := L.extendOfNorm (toBesselPotentialSpaceCLM r 2).toLinearMap
  have hΛ (χ : 𝓢(E, H)) : Λ (toBesselPotentialSpaceCLM r 2 χ) = L χ :=
    LinearMap.extendOfNorm_eq hdense ⟨M, hL⟩ χ
  -- By the Riesz representation theorem in `H^r`, `Λ` is the inner product with some `Y`.
  set Y := (InnerProductSpace.toDual ℂ H^{r}(E, H)).symm Λ
  refine ⟨Y, ?_, ?_⟩
  · have hd (w : H^{m}(E, H)) : ⟪inclusion hmr Y - y, w⟫_ℂ = 0 := by
      refine (denseRange_toBesselPotentialSpaceCLM_two m).induction_on w
        (isClosed_eq (by fun_prop) continuous_const) fun φ ↦ ?_
      rw [inner_sub_left, inner_inclusion_toBesselPotentialSpaceCLM,
        InnerProductSpace.toDual_symm_apply, hΛ]
      -- Unfold `L`; the two Bessel potentials then cancel.
      change ⟪y, toBesselPotentialSpaceCLM m 2 (besselPotentialCLM ((2 * (r - m) : ℝ) : ℂ)
        (besselPotentialCLM ((2 * (m - r) : ℝ) : ℂ) φ))⟫_ℂ - _ = 0
      rw [besselPotentialCLM_ofReal_comp, show 2 * (m - r) + 2 * (r - m) = 0 by ring, ofReal_zero,
        besselPotentialCLM_zero, ContinuousLinearMap.id_apply, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (hd _))
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.opNorm_extendOfNorm_le hdense hM hL

end Pairing


/-! ### The inclusion `[H^{s₀}, H^{s₁}]_θ ⊆ H^{s_θ}` -/

section Reverse

open _root_.Complex.HadamardThreeLines
open scoped InnerProductSpace ComplexConjugate

variable (E H s₀ s₁) in
/-- The sum space `H^{s₀} + H^{s₁}` lies in `H^{min s₀ s₁}`. -/
private def sumToMin :
    (besselPotentialSpace E H 2 s₀ s₁).SumSpace →L[ℂ] H^{min s₀ s₁}(E, H) :=
  (besselPotentialSpace E H 2 s₀ s₁).sumLift (inclusion (min_le_left s₀ s₁))
    (inclusion (min_le_right s₀ s₁)) fun x ↦ BesselPotentialSpace.ext <| by
      simpa [toDistr_inclusion] using (besselPotentialSpace E H 2 s₀ s₁).embed₀_interFst x

private theorem sumToMin_fstToSum (x : H^{s₀}(E, H)) :
    sumToMin E H s₀ s₁ ((besselPotentialSpace E H 2 s₀ s₁).fstToSum x) =
      inclusion (min_le_left s₀ s₁) x :=
  sumLift_fstToSum _ _ _ _ x

private theorem sumToMin_sndToSum (x : H^{s₁}(E, H)) :
    sumToMin E H s₀ s₁ ((besselPotentialSpace E H 2 s₀ s₁).sndToSum x) =
      inclusion (min_le_right s₀ s₁) x :=
  sumLift_sndToSum _ _ _ _ x

private theorem toDistr_sumToMin (w : (besselPotentialSpace E H 2 s₀ s₁).SumSpace) :
    (sumToMin E H s₀ s₁ w).toDistr = (besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed w := by
  obtain ⟨x₀, x₁, rfl⟩ := (besselPotentialSpace E H 2 s₀ s₁).exists_fstToSum_add_sndToSum_eq w
  simp [sumToMin_fstToSum, sumToMin_sndToSum, toDistr_inclusion]

private theorem min_le_interp (hθ : θ ∈ Icc 0 1) : min s₀ s₁ ≤ (1 - θ) * s₀ + θ * s₁ := by
  nlinarith [min_le_left s₀ s₁, min_le_right s₀ s₁, hθ.1, hθ.2]

/-- The pairing `z ↦ ⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}`, `m = min s₀ s₁`, of a Schwartz
function `v` with a function `F` on the strip with values in the sum space. -/
private def stripPairing (θ : ℝ) (v : 𝓢(E, H))
    (F : ℂ → (besselPotentialSpace E H 2 s₀ s₁).SumSpace) (z : ℂ) : ℂ :=
  ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z), sumToMin E H s₀ s₁ (F z)⟫_ℂ

private theorem diffContOnCl_stripPairing {F : ℂ → (besselPotentialSpace E H 2 s₀ s₁).SumSpace}
    (hF : DiffContOnCl ℂ F (verticalStrip 0 1)) (v : 𝓢(E, H)) :
    DiffContOnCl ℂ (stripPairing θ v F) (verticalStrip 0 1) := by
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hFz := (hF.differentiableAt (isOpen_Ioo.preimage continuous_re) hz).hasDerivAt
    exact (HasDerivAt.inner_comp_conj
      (differentiable_besselShift s₁ s₀ θ (min s₀ s₁) v (conj z)).hasDerivAt
      ((sumToMin E H s₀ s₁).hasFDerivAt.comp_hasDerivAt z hFz)).differentiableAt
      |>.differentiableWithinAt
  · exact ((differentiable_besselShift s₁ s₀ θ (min s₀ s₁) v).continuous.comp
      continuous_conj).continuousOn.inner
        ((sumToMin E H s₀ s₁).continuous.comp_continuousOn hF.continuousOn)

private theorem bddAbove_stripPairing {F : ℂ → (besselPotentialSpace E H 2 s₀ s₁).SumSpace}
    {g : C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H))}
    (hF : (besselPotentialSpace E H 2 s₀ s₁).IsStripFunction F g) (v : 𝓢(E, H)) :
    BddAbove ((norm ∘ stripPairing θ v F) '' verticalClosedStrip 0 1) := by
  obtain ⟨K, hK⟩ := hF.exists_norm_le
  refine ⟨‖toBesselPotentialSpaceCLM (min s₀ s₁ + (|θ| + 1) * |s₀ - s₁|) 2 v‖ *
    (‖sumToMin E H s₀ s₁‖ * K), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (conj z).re ∈ Icc 0 1 := by
    rw [conj_re]
    exact hz
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_besselShift_le s₁ s₀ θ _ v hz')
    (((sumToMin E H s₀ s₁).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _))

/-- On a boundary line, the test function `J^{(conj z - θ) (s₁ - s₀)} v` has `H^{2m - s_j}` norm
`‖v‖_{H^{2m - s_θ}}`, which bounds its pairing with an element of `H^{s_j}`. -/
private theorem norm_inner_besselShift_inclusion_le {s : ℝ} (hs : min s₀ s₁ ≤ s) (v : 𝓢(E, H))
    (z : ℂ) (x : H^{s}(E, H))
    (hzs : s - (θ - z.re) * (s₀ - s₁) = (1 - θ) * s₀ + θ * s₁) :
    ‖⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z), inclusion hs x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖ * ‖x‖ := by
  refine (norm_inner_inclusion_le hs _ x).trans_eq ?_
  rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, norm_toBesselPotentialSpaceCLM_congr]
  rw [← hzs]
  simp only [sub_re, ofReal_re, conj_re, mul_re, ofReal_im, mul_zero, sub_zero]
  ring

/-- **The three-lines step.** For an admissible function `F` with boundary traces `g`, the
`H^m` inner product, `m = min s₀ s₁`, of a Schwartz function `v` with `F θ` is bounded by
`‖g‖ ‖v‖_{H^{2m - s_θ}}`: the pairing `⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}` is holomorphic
on the strip, and on the line `re z = j` it has this bound. -/
private theorem norm_inner_sumToMin_le (hθ : θ ∈ Icc 0 1)
    {F : ℂ → (besselPotentialSpace E H 2 s₀ s₁).SumSpace}
    {g : C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H))}
    (hF : (besselPotentialSpace E H 2 s₀ s₁).IsStripFunction F g) (v : 𝓢(E, H)) :
    ‖⟪toBesselPotentialSpaceCLM (min s₀ s₁) 2 v, sumToMin E H s₀ s₁ (F θ)⟫_ℂ‖ ≤
      ‖g‖ * ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖ := by
  set N := ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖
  have ha : ∀ z ∈ re ⁻¹' {0}, ‖stripPairing θ v F z‖ ≤ ‖g‖ * N := fun z hz ↦ by
    have hz' : z.re = 0 := hz
    have hzI : z = (z.im : ℂ) * I := Complex.ext (by simp [hz']) (by simp)
    have hval : stripPairing θ v F z = ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z),
        inclusion (min_le_left s₀ s₁) (g.1 z.im)⟫_ℂ := by
      rw [stripPairing, hzI, hF.apply_mul_I, sumToMin_fstToSum, ← hzI]
    rw [hval, mul_comm]
    refine (norm_inner_besselShift_inclusion_le _ v z _ (by rw [hz']; ring)).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_fst_le g)
  have hb : ∀ z ∈ re ⁻¹' {1}, ‖stripPairing θ v F z‖ ≤ ‖g‖ * N := fun z hz ↦ by
    have hz' : z.re = 1 := hz
    have hzI : z = 1 + (z.im : ℂ) * I := Complex.ext (by simp [hz']) (by simp)
    have hval : stripPairing θ v F z = ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z),
        inclusion (min_le_right s₀ s₁) (g.2 z.im)⟫_ℂ := by
      rw [stripPairing, hzI, hF.apply_one_add_mul_I, sumToMin_sndToSum, ← hzI]
    rw [hval, mul_comm]
    refine (norm_inner_besselShift_inclusion_le _ v z _ (by rw [hz']; ring)).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_snd_le g)
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' (stripPairing θ v F) (z := θ)
    (by simpa [verticalClosedStrip] using hθ) (diffContOnCl_stripPairing hF.diffContOnCl v)
    (bddAbove_stripPairing hF v) ha hb
  have hGθ : stripPairing θ v F θ =
      ⟪toBesselPotentialSpaceCLM (min s₀ s₁) 2 v, sumToMin E H s₀ s₁ (F θ)⟫_ℂ := by
    simp [stripPairing, besselShift]
  rw [← hGθ]
  refine h3.trans_eq ?_
  rw [ofReal_re, ← Real.rpow_add' (by positivity) (by norm_num), sub_add_cancel, Real.rpow_one]

/-- An element of `[H^{s₀}, H^{s₁}]_θ` lies in `H^{s_θ}`, with `H^{s_θ}` norm at most its
interpolation norm. -/
private theorem exists_toDistr_eq_and_norm_le_of_complexMethod (hθ : θ ∈ Icc 0 1)
    (u : (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ) :
    ∃ Y : H^{(1 - θ) * s₀ + θ * s₁}(E, H),
      Y.toDistr = (besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) ∧
        ‖Y‖ ≤ ‖u‖ := by
  have hm := min_le_interp (s₀ := s₀) (s₁ := s₁) hθ
  -- Every trace `g` representing `u` gives an element of `H^{s_θ}` of norm at most `‖g‖`.
  have key (g) (hg : ComplexMethodSpace.mk θ g = u) : ∃ Y : H^{(1 - θ) * s₀ + θ * s₁}(E, H),
      inclusion hm Y = sumToMin E H s₀ s₁ (ComplexMethodSpace.toSum u) ∧ ‖Y‖ ≤ ‖g‖ := by
    have hF := (besselPotentialSpace E H 2 s₀ s₁).isStripFunction_stripFunction g
    have hFθ : (besselPotentialSpace E H 2 s₀ s₁).stripFunction g θ =
        ComplexMethodSpace.toSum u := by
      rw [← hg, ComplexMethodSpace.toSum_mk, stripEval_apply]
    refine exists_inclusion_eq_and_norm_le hm (norm_nonneg _) _ fun φ ↦ ?_
    simpa [hFθ] using norm_inner_sumToMin_le hθ hF φ
  obtain ⟨g₀, hg₀⟩ := ComplexMethodSpace.mk_surjective u
  obtain ⟨Y, hY, -⟩ := key g₀ hg₀
  refine ⟨Y, by rw [← toDistr_inclusion hm, hY, toDistr_sumToMin], ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨g, hg, hgε⟩ := ComplexMethodSpace.norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hε)
  obtain ⟨Y', hY', hle⟩ := key g hg
  rw [← inclusion_injective hm (hY'.trans hY.symm)]
  exact hle.trans_lt hgε

private theorem norm_besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1)
    (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    ‖besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u‖ = ‖u‖ := by
  refine le_antisymm (norm_besselPotentialSpaceToComplexMethod_le hθ u) ?_
  obtain ⟨Y, hY, hle⟩ := exists_toDistr_eq_and_norm_le_of_complexMethod hθ
    (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u)
  have hYu : Y = u := BesselPotentialSpace.ext <| by
    rw [hY, sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod]
  rwa [hYu] at hle

private theorem surjective_besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1) :
    Function.Surjective (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ) := fun u ↦ by
  obtain ⟨Y, hY, -⟩ := exists_toDistr_eq_and_norm_le_of_complexMethod hθ u
  exact ⟨Y, ComplexMethodSpace.ext <| (besselPotentialSpace E H 2 s₀ s₁).sumSpace_ext <| by
    rw [sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod, hY]⟩

end Reverse

/-! ### The identification `[H^{s₀}, H^{s₁}]_θ = H^{s_θ}` -/

variable (E H s₀ s₁) in
/-- **Complex interpolation of the Hilbert scale of Bessel-potential spaces.** For `0 ≤ θ ≤ 1`,
Calderón's complex interpolation space `[H^{s₀}, H^{s₁}]_θ` of the couple
`(H^{s₀}(E, H), H^{s₁}(E, H))` is the Bessel-potential space `H^{s_θ}(E, H)`,
`s_θ = (1 - θ) s₀ + θ s₁`, with equal norms. The isometry keeps the underlying tempered
distribution (`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceComplexMethodEquiv_apply`). -/
def besselPotentialSpaceComplexMethodEquiv (hθ : θ ∈ Icc 0 1) :
    (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      H^{(1 - θ) * s₀ + θ * s₁}(E, H) :=
  (LinearIsometryEquiv.ofSurjective
    { toLinearMap := (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ).toLinearMap
      norm_map' := norm_besselPotentialSpaceToComplexMethod hθ }
    (surjective_besselPotentialSpaceToComplexMethod hθ)).symm

@[simp]
theorem sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply
    (hθ : θ ∈ Icc 0 1) (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum ((besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm u)) =
      u.toDistr :=
  sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod hθ u

@[simp]
theorem toDistr_besselPotentialSpaceComplexMethodEquiv_apply (hθ : θ ∈ Icc 0 1)
    (u : (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ) :
    (besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ u).toDistr =
      (besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
  conv_rhs => rw [← (besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm_apply_apply u]
  rw [sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply]

/-- **Complex interpolation of the Hilbert scale of Bessel-potential spaces**, membership form: for
`0 ≤ θ ≤ 1`, an element `w` of `H^{s₀} + H^{s₁}` lies in `[H^{s₀}, H^{s₁}]_θ` exactly when its
tempered distribution lies in `H^{s_θ}`, where `s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem exists_complexMethodSpace_toSum_eq_iff_memSobolev (hθ : θ ∈ Icc 0 1)
    {w : (besselPotentialSpace E H 2 s₀ s₁).SumSpace} :
    (∃ v : (besselPotentialSpace E H 2 s₀ s₁).ComplexMethodSpace θ,
        ComplexMethodSpace.toSum v = w) ↔
      ((besselPotentialSpace E H 2 s₀ s₁).sumSpaceEmbed w).MemSobolev
        ((1 - θ) * s₀ + θ * s₁) 2 := by
  refine ⟨?_, fun hw ↦ ⟨(besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm
    hw.toBesselPotentialSpace, (besselPotentialSpace E H 2 s₀ s₁).sumSpace_ext ?_⟩⟩
  · rintro ⟨v, rfl⟩
    rw [← toDistr_besselPotentialSpaceComplexMethodEquiv_apply hθ v]
    exact memSobolev_toDistr _
  · rw [sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr]

end Hilbert

end CompatibleCouple

end TauCeti
