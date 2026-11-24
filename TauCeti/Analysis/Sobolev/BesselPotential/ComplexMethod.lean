/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.RealInterpolation
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.SpecialFunctions.Exp.Limits

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
  `F z = exp (δ (z - θ)²) J^{(θ - z) (s₁ - s₀)} f`, `δ > 0`
  (`TauCeti.CompatibleCouple.isStripFunction_stripGaussian_smul`), equals `f` at `θ`, and on the
  line `re z = j` its value lies in `H^{s_j}` with norm `|exp (δ (j + i t - θ)²)| ‖f‖_{H^{s_θ}}`.
  Letting `δ → 0` (`Real.le_of_forall_pos_le_exp_mul`) bounds the interpolation norm of `f` by
  `‖f‖_{H^{s_θ}}`, and Schwartz functions are dense in `H^{s_θ}`.
* `[H^{s₀}, H^{s₁}]_θ ⊆ H^{s_θ}`. Let `m = min s₀ s₁`, so that `H^{s₀} + H^{s₁} ⊆ H^m`
  (`TauCeti.CompatibleCouple.besselPotentialSpaceSumToMin`). For an admissible function `F` with
  boundary traces `g` and a Schwartz function `v`, the pairing
  `z ↦ ⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}` is holomorphic on the strip and bounded on its
  boundary lines by `‖g‖ ‖v‖_{H^{2m - s_θ}}`, so by Hadamard's three-lines theorem the same bound
  holds for `⟪v, F θ⟫_{H^m}`. An element of `H^m` whose `H^m` inner products with Schwartz
  functions are bounded in this way lies in `H^{s_θ}`, by the Riesz representation theorem in
  `H^{s_θ}` (`BesselPotentialSpace.exists_inclusion_eq_and_norm_le`).

## Main declarations

* `TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodEquiv`: the isometric isomorphism
  `[H^{s₀}, H^{s₁}]_θ ≃ H^{s_θ}`, which keeps the underlying tempered distribution
  (`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceComplexMethodEquiv_apply`,
  `TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply`).
* `TauCeti.CompatibleCouple.exists_complexMethodSpace_toSum_eq_iff_memSobolev`: an element of
  `H^{s₀} + H^{s₁}` lies in `[H^{s₀}, H^{s₁}]_θ` exactly when its tempered distribution lies in
  `H^{s_θ}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.1,
  Theorem 5.4.1 and Theorem 6.4.5 (7).
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §1.18.5 and §2.4.2.
-/

public section

noncomputable section

open Complex Filter Set Topology SchwartzMap BesselPotentialSpace
open Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction ENNReal SchwartzMap BesselPotentialSpace ZeroAtInfty

namespace TauCeti

namespace CompatibleCouple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

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

/-- The values `t ↦ J^{(θ - a - i t) (s₁ - s₀)} f` on the line `re z = a`, read in `H^r`, as a
bounded continuous function: they all have the norm of `f` in `H^{r + (θ - a) (s₁ - s₀)}`. -/
private def besselLine (s₀ s₁ θ r a : ℝ) (f : 𝓢(E, H)) : ℝ →ᵇ H^{r}(E, H) :=
  .ofNormedAddCommGroup (fun t ↦ besselShift s₀ s₁ θ r f (a + t * I))
    ((differentiable_besselShift s₀ s₁ θ r f).continuous.comp (by fun_prop))
    ‖toBesselPotentialSpaceCLM (r + (θ - a) * (s₁ - s₀)) 2 f‖ fun t ↦ by
      rw [norm_besselShift, show ((a : ℂ) + t * I).re = a by simp]

private theorem norm_besselLine_le (s₀ s₁ θ r a : ℝ) (f : 𝓢(E, H)) :
    ‖besselLine s₀ s₁ θ r a f‖ ≤ ‖toBesselPotentialSpaceCLM (r + (θ - a) * (s₁ - s₀)) 2 f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

/-- The boundary traces of the admissible function `exp (δ (z - θ)²) J^{(θ - z) (s₁ - s₀)} f`. -/
private def besselTrace (s₀ s₁ θ : ℝ) (hδ : 0 < δ) (f : 𝓢(E, H)) :
    C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H)) :=
  (stripGaussianSMul hδ θ 0 (besselLine s₀ s₁ θ s₀ 0 f),
    stripGaussianSMul hδ θ 1 (besselLine s₀ s₁ θ s₁ 1 f))

private theorem diffContOnCl_besselShift (f : 𝓢(E, H)) :
    DiffContOnCl ℂ (fun z ↦ (besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum
      (besselShift s₀ s₁ θ s₀ f z)) (verticalStrip 0 1) :=
  ((besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum.differentiable.comp
    (differentiable_besselShift s₀ s₁ θ s₀ f)).diffContOnCl

private theorem isBounded_image_besselShift (f : 𝓢(E, H)) :
    Bornology.IsBounded ((fun z ↦ (besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum
      (besselShift s₀ s₁ θ s₀ f z)) '' verticalClosedStrip 0 1) :=
  isBounded_iff_forall_norm_le.2
    ⟨‖toBesselPotentialSpaceCLM (s₀ + (|θ| + 1) * |s₁ - s₀|) 2 f‖, by
      rintro _ ⟨z, hz, rfl⟩
      exact ((besselPotentialSpace E H s₀ 2 s₁ 2).norm_fstToSum_le _).trans
        (norm_besselShift_le s₀ s₁ θ s₀ f hz)⟩

private theorem besselShift_one_add_mul_I (f : 𝓢(E, H)) (t : ℝ) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum (besselShift s₀ s₁ θ s₀ f (1 + t * I)) =
      (besselPotentialSpace E H s₀ 2 s₁ 2).sndToSum (besselLine s₀ s₁ θ s₁ 1 f t) := by
  simp [besselLine, besselShift, besselPotentialSpace_fstToSum_toBesselPotentialSpaceCLM]

private theorem besselTrace_mem (hδ : 0 < δ) (f : 𝓢(E, H)) :
    besselTrace s₀ s₁ θ hδ f ∈ (besselPotentialSpace E H s₀ 2 s₁ 2).stripTraces :=
  stripGaussianSMul_mem_stripTraces hδ θ (diffContOnCl_besselShift f)
    (isBounded_image_besselShift f) (fun t ↦ by simp [besselLine]) (besselShift_one_add_mul_I f)

private theorem stripEval_besselTrace (hδ : 0 < δ) (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).stripEval θ
        ⟨besselTrace s₀ s₁ θ hδ f, besselTrace_mem hδ f⟩ =
      (besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum (toBesselPotentialSpaceCLM s₀ 2 f) :=
  (stripEval_stripGaussianSMul hδ hθ (diffContOnCl_besselShift f)
    (isBounded_image_besselShift f) (fun t ↦ by simp [besselLine])
    (besselShift_one_add_mul_I f)).trans (by simp [besselShift])

private theorem norm_besselTrace_le (hδ : 0 < δ) (f : 𝓢(E, H)) :
    ‖besselTrace s₀ s₁ θ hδ f‖ ≤
      Real.exp (δ * (|θ| + 1) ^ 2) * ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  -- On both lines the order `r + (θ - a) (s₁ - s₀)` is `s_θ`.
  have h₀ := norm_besselLine_le s₀ s₁ θ s₀ 0 f
  have h₁ := norm_besselLine_le s₀ s₁ θ s₁ 1 f
  rw [show s₀ + (θ - 0) * (s₁ - s₀) = (1 - θ) * s₀ + θ * s₁ by ring] at h₀
  rw [show s₁ + (θ - 1) * (s₁ - s₀) = (1 - θ) * s₀ + θ * s₁ by ring] at h₁
  exact norm_prod_le_iff.2
    ⟨(norm_stripGaussianSMul_le hδ θ (by simp) _).trans
      (mul_le_mul_of_nonneg_left h₀ (Real.exp_pos _).le),
    (norm_stripGaussianSMul_le hδ θ (by simp) _).trans
      (mul_le_mul_of_nonneg_left h₁ (Real.exp_pos _).le)⟩

/-! ### The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` -/

variable (E H s₀ s₁) in
/-- The inclusion of Schwartz functions into `[H^{s₀}, H^{s₁}]_θ`, through the admissible function
`exp ((z - θ)²) J^{(θ - z) (s₁ - s₀)} f`. -/
private def schwartzToComplexMethod (hθ : θ ∈ Icc 0 1) :
    𝓢(E, H) →ₗ[ℂ] (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ where
  toFun f := ComplexMethodSpace.mk θ ⟨besselTrace s₀ s₁ θ one_pos f, besselTrace_mem one_pos f⟩
  map_add' f g := ComplexMethodSpace.ext <| by
    simp only [map_add, ComplexMethodSpace.toSum_mk, stripEval_besselTrace one_pos hθ]
  map_smul' c f := ComplexMethodSpace.ext <| by
    simp only [map_smul, ComplexMethodSpace.toSum_mk, stripEval_besselTrace one_pos hθ,
      RingHom.id_apply]

private theorem toSum_schwartzToComplexMethod (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    ComplexMethodSpace.toSum (schwartzToComplexMethod E H s₀ s₁ hθ f) =
      (besselPotentialSpace E H s₀ 2 s₁ 2).fstToSum (toBesselPotentialSpaceCLM s₀ 2 f) :=
  (ComplexMethodSpace.toSum_mk _).trans (stripEval_besselTrace one_pos hθ f)

private theorem norm_schwartzToComplexMethod_le (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    ‖schwartzToComplexMethod E H s₀ s₁ hθ f‖ ≤
      ‖toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f‖ := by
  refine Real.le_of_forall_pos_le_exp_mul (c := (|θ| + 1) ^ 2) fun δ hδ ↦ ?_
  have h : schwartzToComplexMethod E H s₀ s₁ hθ f =
      ComplexMethodSpace.mk θ ⟨besselTrace s₀ s₁ θ hδ f, besselTrace_mem hδ f⟩ :=
    ComplexMethodSpace.ext <| by
      rw [toSum_schwartzToComplexMethod, ComplexMethodSpace.toSum_mk, stripEval_besselTrace hδ hθ]
  rw [h]
  exact (ComplexMethodSpace.norm_mk_le _).trans (norm_besselTrace_le hδ f)

variable (E H s₀ s₁) in
/-- The inclusion of `H^{s_θ}` into `[H^{s₀}, H^{s₁}]_θ`, the continuous extension of
`schwartzToComplexMethod`. -/
private def besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1) :
    H^{(1 - θ) * s₀ + θ * s₁}(E, H) →L[ℂ]
      (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ :=
  (schwartzToComplexMethod E H s₀ s₁ hθ).extendOfNorm
    (toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2).toLinearMap

private theorem besselPotentialSpaceToComplexMethod_toBesselPotentialSpaceCLM
    (hθ : θ ∈ Icc 0 1) (f : 𝓢(E, H)) :
    besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ
        (toBesselPotentialSpaceCLM ((1 - θ) * s₀ + θ * s₁) 2 f) =
      schwartzToComplexMethod E H s₀ s₁ hθ f :=
  LinearMap.extendOfNorm_eq
    (denseRange_toBesselPotentialSpaceCLM (p := 2) _ ENNReal.ofNat_ne_top)
    ⟨1, fun f ↦ by simpa using norm_schwartzToComplexMethod_le hθ f⟩ f

/-- The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` keeps the underlying tempered distribution. -/
private theorem sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod (hθ : θ ∈ Icc 0 1)
    (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed
        (ComplexMethodSpace.toSum (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u)) =
      u.toDistr := by
  refine (denseRange_toBesselPotentialSpaceCLM (p := 2) _ ENNReal.ofNat_ne_top).induction_on
    u
    (isClosed_eq ((besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed.comp
      (ComplexMethodSpace.toSum.comp (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ))).continuous
      continuous_toDistr) fun f ↦ ?_
  rw [besselPotentialSpaceToComplexMethod_toBesselPotentialSpaceCLM,
    toSum_schwartzToComplexMethod]
  simp [sumSpaceEmbed_fstToSum, besselPotentialSpace_embed₀_apply,
    toDistr_toBesselPotentialSpaceCLM]

/-- The inclusion `H^{s_θ} ⊆ [H^{s₀}, H^{s₁}]_θ` does not increase norms:
`‖u‖_{[H^{s₀}, H^{s₁}]_θ} ≤ ‖u‖_{H^{s_θ}}`. -/
private theorem norm_besselPotentialSpaceToComplexMethod_le (hθ : θ ∈ Icc 0 1)
    (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    ‖besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ u‖ ≤ ‖u‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (denseRange_toBesselPotentialSpaceCLM (p := 2) _ ENNReal.ofNat_ne_top) 1
    (fun f ↦ by simpa using norm_schwartzToComplexMethod_le hθ f) u
  rw [one_mul] at h
  exact h

/-! ### The inclusion `[H^{s₀}, H^{s₁}]_θ ⊆ H^{s_θ}` -/

section Reverse

open scoped InnerProductSpace ComplexConjugate

private theorem min_le_interp (hθ : θ ∈ Icc 0 1) : min s₀ s₁ ≤ (1 - θ) * s₀ + θ * s₁ := by
  nlinarith [min_le_left s₀ s₁, min_le_right s₀ s₁, hθ.1, hθ.2]

/-- The pairing `z ↦ ⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}`, `m = min s₀ s₁`, of a Schwartz
function `v` with a function `F` on the strip with values in the sum space. -/
private def stripPairing (θ : ℝ) (v : 𝓢(E, H))
    (F : ℂ → (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace) (z : ℂ) : ℂ :=
  ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z), besselPotentialSpaceSumToMin E H 2 s₀ s₁ (F z)⟫_ℂ

private theorem diffContOnCl_stripPairing {F : ℂ → (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace}
    (hF : DiffContOnCl ℂ F (verticalStrip 0 1)) (v : 𝓢(E, H)) :
    DiffContOnCl ℂ (stripPairing θ v F) (verticalStrip 0 1) := by
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hFz := (hF.differentiableAt (isOpen_Ioo.preimage continuous_re) hz).hasDerivAt
    exact (HasDerivAt.inner_comp_conj
      (differentiable_besselShift s₁ s₀ θ (min s₀ s₁) v (conj z)).hasDerivAt
      ((besselPotentialSpaceSumToMin E H 2 s₀ s₁).hasFDerivAt.comp_hasDerivAt z
        hFz)).differentiableAt
      |>.differentiableWithinAt
  · exact ((differentiable_besselShift s₁ s₀ θ (min s₀ s₁) v).continuous.comp
      continuous_conj).continuousOn.inner
        ((besselPotentialSpaceSumToMin E H 2 s₀ s₁).continuous.comp_continuousOn hF.continuousOn)

private theorem bddAbove_stripPairing {F : ℂ → (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace}
    {g : C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H))}
    (hF : (besselPotentialSpace E H s₀ 2 s₁ 2).IsStripFunction F g) (v : 𝓢(E, H)) :
    BddAbove ((norm ∘ stripPairing θ v F) '' verticalClosedStrip 0 1) := by
  obtain ⟨K, hK⟩ := hF.exists_norm_le
  refine ⟨‖toBesselPotentialSpaceCLM (min s₀ s₁ + (|θ| + 1) * |s₀ - s₁|) 2 v‖ *
    (‖besselPotentialSpaceSumToMin E H 2 s₀ s₁‖ * K), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (conj z).re ∈ Icc 0 1 := by
    rw [conj_re]
    exact hz
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_besselShift_le s₁ s₀ θ _ v hz')
    (((besselPotentialSpaceSumToMin E H 2 s₀ s₁).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hK z hz) (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _))

/-- On a boundary line, the test function `J^{(conj z - θ) (s₁ - s₀)} v` has `H^{2m - s_j}` norm
`‖v‖_{H^{2m - s_θ}}`, which bounds its pairing with an element of `H^{s_j}`. -/
private theorem norm_inner_besselShift_inclusion_le {s : ℝ} (hs : min s₀ s₁ ≤ s) (v : 𝓢(E, H))
    (z : ℂ) (x : H^{s}(E, H))
    (hzs : s - (θ - z.re) * (s₀ - s₁) = (1 - θ) * s₀ + θ * s₁) :
    ‖⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z), inclusion hs x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖ * ‖x‖ := by
  refine (norm_inner_inclusion_le hs _ x).trans_eq ?_
  have hre : 2 * min s₀ s₁ - s + (((θ : ℂ) - conj z) * ((s₀ - s₁ : ℝ) : ℂ)).re =
      2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁) := by
    rw [← hzs]
    simp only [sub_re, ofReal_re, conj_re, mul_re, ofReal_im, mul_zero, sub_zero]
    ring
  rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, hre]

/-- **The three-lines step.** For an admissible function `F` with boundary traces `g`, the
`H^m` inner product, `m = min s₀ s₁`, of a Schwartz function `v` with `F θ` is bounded by
`‖g‖ ‖v‖_{H^{2m - s_θ}}`: the pairing `⟪J^{(conj z - θ) (s₁ - s₀)} v, F z⟫_{H^m}` is holomorphic
on the strip, and on the line `re z = j` it has this bound. -/
private theorem norm_inner_besselPotentialSpaceSumToMin_le (hθ : θ ∈ Icc 0 1)
    {F : ℂ → (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace}
    {g : C₀(ℝ, H^{s₀}(E, H)) × C₀(ℝ, H^{s₁}(E, H))}
    (hF : (besselPotentialSpace E H s₀ 2 s₁ 2).IsStripFunction F g) (v : 𝓢(E, H)) :
    ‖⟪toBesselPotentialSpaceCLM (min s₀ s₁) 2 v,
        besselPotentialSpaceSumToMin E H 2 s₀ s₁ (F θ)⟫_ℂ‖ ≤
      ‖g‖ * ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖ := by
  set N := ‖toBesselPotentialSpaceCLM (2 * min s₀ s₁ - ((1 - θ) * s₀ + θ * s₁)) 2 v‖
  have ha : ∀ z ∈ re ⁻¹' {0}, ‖stripPairing θ v F z‖ ≤ ‖g‖ * N := fun z hz ↦ by
    have hz' : z.re = 0 := hz
    have hzI : z = (z.im : ℂ) * I := Complex.ext (by simp [hz']) (by simp)
    have hval : stripPairing θ v F z = ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z),
        inclusion (min_le_left s₀ s₁) (g.1 z.im)⟫_ℂ := by
      rw [stripPairing, hzI, hF.apply_mul_I, besselPotentialSpaceSumToMin_fstToSum, ← hzI]
    rw [hval, mul_comm]
    refine (norm_inner_besselShift_inclusion_le _ v z _ (by rw [hz']; ring)).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_fst_le g)
  have hb : ∀ z ∈ re ⁻¹' {1}, ‖stripPairing θ v F z‖ ≤ ‖g‖ * N := fun z hz ↦ by
    have hz' : z.re = 1 := hz
    have hzI : z = 1 + (z.im : ℂ) * I := Complex.ext (by simp [hz']) (by simp)
    have hval : stripPairing θ v F z = ⟪besselShift s₁ s₀ θ (min s₀ s₁) v (conj z),
        inclusion (min_le_right s₀ s₁) (g.2 z.im)⟫_ℂ := by
      rw [stripPairing, hzI, hF.apply_one_add_mul_I, besselPotentialSpaceSumToMin_sndToSum, ← hzI]
    rw [hval, mul_comm]
    refine (norm_inner_besselShift_inclusion_le _ v z _ (by rw [hz']; ring)).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_snd_le g)
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' (stripPairing θ v F) (z := θ)
    (by simpa [verticalClosedStrip] using hθ) (diffContOnCl_stripPairing hF.diffContOnCl v)
    (bddAbove_stripPairing hF v) ha hb
  have hGθ : stripPairing θ v F θ =
      ⟪toBesselPotentialSpaceCLM (min s₀ s₁) 2 v,
        besselPotentialSpaceSumToMin E H 2 s₀ s₁ (F θ)⟫_ℂ := by
    simp [stripPairing, besselShift]
  rw [← hGθ]
  refine h3.trans_eq ?_
  rw [ofReal_re, ← Real.rpow_add' (by positivity) (by norm_num), sub_add_cancel, Real.rpow_one]

/-- An element of `[H^{s₀}, H^{s₁}]_θ` lies in `H^{s_θ}`, with `H^{s_θ}` norm at most its
interpolation norm. -/
private theorem exists_toDistr_eq_and_norm_le_of_complexMethod (hθ : θ ∈ Icc 0 1)
    (u : (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ) :
    ∃ Y : H^{(1 - θ) * s₀ + θ * s₁}(E, H),
      Y.toDistr = (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed (ComplexMethodSpace.toSum u) ∧
        ‖Y‖ ≤ ‖u‖ := by
  have hm := min_le_interp (s₀ := s₀) (s₁ := s₁) hθ
  -- Every trace `g` representing `u` gives an element of `H^{s_θ}` of norm at most `‖g‖`.
  have key (g) (hg : ComplexMethodSpace.mk θ g = u) : ∃ Y : H^{(1 - θ) * s₀ + θ * s₁}(E, H),
      inclusion hm Y = besselPotentialSpaceSumToMin E H 2 s₀ s₁ (ComplexMethodSpace.toSum u) ∧
        ‖Y‖ ≤ ‖g‖ := by
    have hF := (besselPotentialSpace E H s₀ 2 s₁ 2).isStripFunction_stripFunction g
    have hFθ : (besselPotentialSpace E H s₀ 2 s₁ 2).stripFunction g θ =
        ComplexMethodSpace.toSum u := by
      rw [← hg, ComplexMethodSpace.toSum_mk, stripEval_apply]
    refine exists_inclusion_eq_and_norm_le hm (norm_nonneg _) _ fun φ ↦ ?_
    simpa [hFθ] using norm_inner_besselPotentialSpaceSumToMin_le hθ hF φ
  obtain ⟨g₀, hg₀⟩ := ComplexMethodSpace.mk_surjective u
  obtain ⟨Y, hY, -⟩ := key g₀ hg₀
  refine ⟨Y, by rw [← toDistr_inclusion hm, hY, toDistr_besselPotentialSpaceSumToMin], ?_⟩
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
  exact ⟨Y, ComplexMethodSpace.ext <| (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpace_ext <| by
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
    (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ ≃ₗᵢ[ℂ]
      H^{(1 - θ) * s₀ + θ * s₁}(E, H) :=
  (LinearIsometryEquiv.ofSurjective
    { toLinearMap := (besselPotentialSpaceToComplexMethod E H s₀ s₁ hθ).toLinearMap
      norm_map' := norm_besselPotentialSpaceToComplexMethod hθ }
    (surjective_besselPotentialSpaceToComplexMethod hθ)).symm

@[simp]
theorem sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply
    (hθ : θ ∈ Icc 0 1) (u : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed
        (ComplexMethodSpace.toSum ((besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm u)) =
      u.toDistr :=
  sumSpaceEmbed_toSum_besselPotentialSpaceToComplexMethod hθ u

@[simp]
theorem toDistr_besselPotentialSpaceComplexMethodEquiv_apply (hθ : θ ∈ Icc 0 1)
    (u : (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ) :
    (besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ u).toDistr =
      (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
  conv_rhs => rw [← (besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm_apply_apply u]
  rw [sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply]

/-- **Complex interpolation of the Hilbert scale of Bessel-potential spaces**, membership form: for
`0 ≤ θ ≤ 1`, an element `w` of `H^{s₀} + H^{s₁}` lies in `[H^{s₀}, H^{s₁}]_θ` exactly when its
tempered distribution lies in `H^{s_θ}`, where `s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem exists_complexMethodSpace_toSum_eq_iff_memSobolev (hθ : θ ∈ Icc 0 1)
    {w : (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace} :
    (∃ v : (besselPotentialSpace E H s₀ 2 s₁ 2).ComplexMethodSpace θ,
        ComplexMethodSpace.toSum v = w) ↔
      ((besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed w).MemSobolev
        ((1 - θ) * s₀ + θ * s₁) 2 := by
  refine ⟨?_, fun hw ↦ ⟨(besselPotentialSpaceComplexMethodEquiv E H s₀ s₁ hθ).symm
    hw.toBesselPotentialSpace, (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpace_ext ?_⟩⟩
  · rintro ⟨v, rfl⟩
    rw [← toDistr_besselPotentialSpaceComplexMethodEquiv_apply hθ v]
    exact memSobolev_toDistr _
  · rw [sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodEquiv_symm_apply,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr]

end Hilbert

end CompatibleCouple

end TauCeti
