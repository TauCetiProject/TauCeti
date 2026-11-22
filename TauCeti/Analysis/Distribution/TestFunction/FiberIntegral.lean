/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TensorProduct
public import TauCeti.Analysis.Distribution.Gluing
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
import TauCeti.Analysis.Distribution.TestFunction.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Integration of test functions over the fibres of a submersion

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of finite-dimensional real normed spaces with additive
Haar measures `μ` and `ν`, and let `f : E → E'` be smooth on `Ω`, map `Ω` into `Ω'`, and have
surjective derivative at every point of `Ω`. A test function `φ` on `Ω`, read as a density, pushes
forward along `f` to a test function `f_♯ φ` on `Ω'`, its integral over the fibres of `f`:

`∫ y, (f_♯ φ) y • g y ∂ν = ∫ x, φ x • g (f x) ∂μ`

for every `g` continuous on `Ω'` (`TestFunction.integral_fiberIntegralCLM_smul`). In other words
`f_♯ φ` is the density with respect to `ν` of the image under `f` of the measure `φ μ`. This
property determines `f_♯ φ` (`TestFunction.eq_fiberIntegralCLM_iff`), and `f_♯` is a continuous
linear map `𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω', ℝ)` (`TestFunction.fiberIntegralCLM`), supported in
`f '' supp φ` (`TestFunction.tsupport_fiberIntegralCLM_subset`). Its transpose pulls distributions
back along `f`, see `TauCeti.Analysis.Distribution.Submersion`.

When `f` is a diffeomorphism and `ν = μ`, the fibres are points, and `f_♯` is the pushforward of
test densities `TestFunction.pushforwardCLM` of a change of variables. In general the fibres are
submanifolds, and the absence of critical points is what makes `f_♯ φ` smooth: at a critical value
the image measure of `φ μ` need not have a smooth density.

Since the defining identity determines `f_♯ φ`, fibre integration only depends on `f` on `Ω`
(`TestFunction.fiberIntegralCLM_congr`), it is compatible with shrinking `Ω`
(`TestFunction.fiberIntegralCLM_monoCLM`), and it is functorial: `(g ∘ f)_♯ = g_♯ ∘ f_♯`
(`TestFunction.fiberIntegralCLM_comp`).

## Construction

For a surjective linear map `A`, choose a linear equivalence `L : E ≃ E' × ker A` whose first
component is `A` (`TestFunction.linearCoord`, with linear section `TestFunction.linearSection` of
`A`). Then `A_♯ ψ` is, up to the constant `TestFunction.linearScale` comparing `μ` with the image
of the product measure (`TestFunction.map_linearCoord`), the partial integral
`y ↦ ∫ k, ψ (L⁻¹ (y, k)) dk` over the second factor; it is a test function by
`Distribution.partialPairing`, and the defining identity is Fubini's theorem. Near a point `a`
of `Ω`, the local normal form of a submersion
(`ContDiffOn.exists_openPartialHomeomorph_eqOn_fderiv_comp`) writes `f = Df(a) ∘ Θ` for a
diffeomorphism `Θ`, so `f_♯ = Df(a)_♯ ∘ Θ_*` on tests supported near `a`. These local maps satisfy
the same defining identity, which determines a continuous function by the fundamental lemma of the
calculus of variations, so they agree on overlaps and glue to `f_♯`
(`Distribution.existsUnique_gluing`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (Theorem 6.1.2).
-/

public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Distributions ContDiff

namespace TestFunction

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-! ### Fibre integration along a surjective linear map -/

section Linear

variable {A : E →L[ℝ] E'} (hA : Function.Surjective A)

/-- The linear equivalence `L : E ≃ E' × ker A` whose first component is `A`, that is,
`L x = (A x, P x)` for a projection `P` onto `ker A`. -/
def linearCoord : E ≃L[ℝ] E' × (A : E →ₗ[ℝ] E').ker :=
  A.implicitCoordEquiv (LinearMap.range_eq_top.2 hA) (.of_finiteDimensional _)

/-- The first component of `linearCoord` is `A`. -/
theorem linearCoord_apply_fst (x : E) : (linearCoord hA x).1 = A x := by
  simp [linearCoord]

/-- The linear section `y ↦ L⁻¹ (y, 0)` of `A`, where `L = linearCoord`. -/
def linearSection : E' →L[ℝ] E :=
  ((linearCoord hA).symm : E' × (A : E →ₗ[ℝ] E').ker →L[ℝ] E).comp
    (ContinuousLinearMap.inl ℝ E' (A : E →ₗ[ℝ] E').ker)

/-- `linearSection` is a right inverse of `A`. -/
theorem comp_linearSection : A.comp (linearSection hA) = ContinuousLinearMap.id ℝ E' := by
  ext y
  simpa [linearSection] using (linearCoord_apply_fst hA ((linearCoord hA).symm (y, 0))).symm

/-- Every `x` decomposes as `s (A x) + P x`, where `s = linearSection` and `P x ∈ ker A` is the
second component of `linearCoord`. -/
theorem linearSection_add_linearCoord_snd (x : E) :
    linearSection hA (A x) + ((linearCoord hA x).2 : E) = x := by
  symm
  conv_lhs => rw [← (linearCoord hA).symm_apply_apply x]
  rw [← linearCoord_apply_fst hA x, ← Prod.fst_add_snd (linearCoord hA x)]
  simp only [map_add, linearSection, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearMap.inl_apply, Prod.fst_add, Prod.snd_add, add_zero,
    zero_add]
  congr 1
  exact A.implicitCoordEquiv_symm_apply_zero_mk _ _ _

variable (W : Opens E)

/-- The open set `L(W)` of `E' × ker A`. -/
private def linearCoordImage : Opens (E' × (A : E →ₗ[ℝ] E').ker) :=
  ⟨(linearCoord hA).symm ⁻¹' W, W.isOpen.preimage (linearCoord hA).symm.continuous⟩

private theorem mapsTo_linearCoord : MapsTo (linearCoord hA) W (linearCoordImage hA W) :=
  fun x hx ↦ by simpa [linearCoordImage] using hx

variable {W} (hW : MapsTo A W Ω')
include hW in
private theorem linearCoordImage_subset :
    (linearCoordImage hA W : Set (E' × (A : E →ₗ[ℝ] E').ker)) ⊆
      (Ω' : Set E') ×ˢ ((⊤ : Opens (A : E →ₗ[ℝ] E').ker) : Set (A : E →ₗ[ℝ] E').ker) := by
  intro p hp
  refine ⟨?_, trivial⟩
  have h := hW (by simpa [linearCoordImage] using hp)
  rwa [← linearCoord_apply_fst hA, ContinuousLinearEquiv.apply_symm_apply] at h

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]

/-- The constant comparing `μ` with the product of `ν` and a Haar measure on `ker A`, through
`linearCoord`. -/
def linearScale : NNReal :=
  Measure.addHaarScalarFactor (μ.map (linearCoord hA)) (ν.prod Measure.addHaar)

/-- The constant `linearScale` is positive. -/
theorem linearScale_pos : 0 < linearScale hA μ ν :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- The image of `μ` under `linearCoord` is `linearScale` times the product of `ν` and a Haar
measure on `ker A`. -/
theorem map_linearCoord :
    μ.map (linearCoord hA) = linearScale hA μ ν • ν.prod Measure.addHaar :=
  Measure.isAddLeftInvariant_eq_smul _ _

/-- **Fubini in the linear coordinates.** Integrating a product `u (A x) v (P x)` against `μ`
gives `linearScale` times the product of the integrals. -/
theorem integral_mul_linearCoord {𝕜 : Type*} [RCLike 𝕜] (u : E' → 𝕜)
    (v : (A : E →ₗ[ℝ] E').ker → 𝕜) :
    ∫ x, u (linearCoord hA x).1 * v (linearCoord hA x).2 ∂μ =
      (linearScale hA μ ν : ℝ) • ((∫ y, u y ∂ν) * ∫ k, v k ∂Measure.addHaar) := by
  rw [← integral_prod_mul, ← NNReal.smul_def, ← integral_smul_nnreal_measure,
    ← map_linearCoord, ← (linearCoord hA).coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe,
    integral_map_equiv]

/-- Fibre integration along a surjective linear map `A`: `y ↦ c ∫ k, ψ (L⁻¹ (y, k)) dk`. -/
private def linearFiberIntegral : 𝓓(W, ℝ) →L[ℝ] 𝓓(Ω', ℝ) :=
  (linearScale hA μ ν : ℝ) •
    (Distribution.ofFun ⊤ (fun _ ↦ (1 : ℝ)) Measure.addHaar ⊤).partialPairing
      (linearCoordImage_subset hA hW) ∘L
    (linearCoord hA).transportTestFunction (mapsTo_linearCoord hA W)

private theorem linearFiberIntegral_apply (ψ : 𝓓(W, ℝ)) (y : E') :
    linearFiberIntegral hA hW μ ν ψ y =
      (linearScale hA μ ν : ℝ) * ∫ k, ψ ((linearCoord hA).symm (y, k)) ∂Measure.addHaar := by
  simp only [linearFiberIntegral, ContinuousLinearMap.comp_apply, smul_apply,
    Distribution.partialPairing_apply, smul_eq_mul]
  rw [Distribution.ofFun_apply (locallyIntegrableOn_const _)]
  simp

/-- The defining identity of fibre integration along a surjective linear map. -/
private theorem integral_linearFiberIntegral_smul (ψ : 𝓓(W, ℝ)) {g : E' → G}
    (hg : ContinuousOn g Ω') :
    ∫ y, linearFiberIntegral hA hW μ ν ψ y • g y ∂ν = ∫ x, ψ x • g (A x) ∂μ := by
  set L := linearCoord hA
  set ψ' := L.transportTestFunction (mapsTo_linearCoord hA W) ψ
  have hψ' (p : E' × (A : E →ₗ[ℝ] E').ker) : ψ' p = ψ (L.symm p) :=
    ContinuousLinearEquiv.transportTestFunction_apply ..
  -- The integrand on the product is continuous on `Ω' × ker A`, which contains the support of
  -- `ψ'`, so it is integrable.
  have hint : Integrable (fun p : E' × (A : E →ₗ[ℝ] E').ker ↦ ψ' p • g p.1)
      (ν.prod Measure.addHaar) := by
    have hK := ψ'.hasCompactSupport.isCompact
    have hc : ContinuousOn (fun p : E' × (A : E →ₗ[ℝ] E').ker ↦ ψ' p • g p.1) (tsupport ψ') :=
      ψ'.continuous.continuousOn.smul (hg.comp continuous_fst.continuousOn fun p hp ↦
        (linearCoordImage_subset hA hW (ψ'.tsupport_subset hp)).1)
    exact (integrableOn_iff_integrable_of_support_subset
      ((Function.support_smul_subset_left _ _).trans (subset_tsupport _))).1
      (hc.integrableOn_compact hK)
  calc ∫ y, linearFiberIntegral hA hW μ ν ψ y • g y ∂ν
      = (linearScale hA μ ν : ℝ) • ∫ y, (∫ k, ψ' (y, k) ∂Measure.addHaar) • g y ∂ν := by
        simp_rw [linearFiberIntegral_apply, mul_smul, integral_smul, hψ', L]
    _ = (linearScale hA μ ν : ℝ) • ∫ p, ψ' p • g p.1 ∂(ν.prod Measure.addHaar) := by
        rw [integral_prod _ hint]
        simp_rw [integral_smul_const]
    _ = ∫ p, ψ' p • g p.1 ∂(μ.map L) := by
        rw [map_linearCoord hA μ ν, integral_smul_nnreal_measure, NNReal.smul_def]
    _ = ∫ x, ψ x • g (A x) ∂μ := by
        rw [← L.coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
        simp [hψ', L, linearCoord_apply_fst]

end Linear

/-! ### Fibre integration along a submersion -/

section Chart

variable {f : E → E'} (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f x))

include hf hsurj in
/-- A submersion is, near each point `a` of `Ω`, its derivative at `a` after a change of
variables. -/
private theorem exists_chart (a : Ω) :
    ∃ Θ : OpenPartialHomeomorph E E, (a : E) ∈ Θ.source ∧ Θ.source ⊆ Ω ∧
      ContDiffOn ℝ ∞ Θ Θ.source ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target ∧
      EqOn f (fderiv ℝ f a ∘ Θ) Θ.source :=
  hf.exists_openPartialHomeomorph_eqOn_fderiv_comp Ω.isOpen a.property (by simp)
    (LinearMap.range_eq_top.2 (hsurj a a.property)) (.of_finiteDimensional _)

/-- The chart at `a` of `exists_chart`. -/
private def chart (a : Ω) : OpenPartialHomeomorph E E :=
  (exists_chart hf hsurj a).choose

private theorem mem_chart_source (a : Ω) : (a : E) ∈ (chart hf hsurj a).source :=
  (exists_chart hf hsurj a).choose_spec.1

private theorem chart_source_subset (a : Ω) : (chart hf hsurj a).source ⊆ Ω :=
  (exists_chart hf hsurj a).choose_spec.2.1

private theorem contDiffOn_chart (a : Ω) :
    ContDiffOn ℝ ∞ (chart hf hsurj a) (chart hf hsurj a).source :=
  (exists_chart hf hsurj a).choose_spec.2.2.1

private theorem contDiffOn_chart_symm (a : Ω) :
    ContDiffOn ℝ ∞ (chart hf hsurj a).symm (chart hf hsurj a).target :=
  (exists_chart hf hsurj a).choose_spec.2.2.2.1

private theorem eqOn_chart (a : Ω) :
    EqOn f (fderiv ℝ f a ∘ chart hf hsurj a) (chart hf hsurj a).source :=
  (exists_chart hf hsurj a).choose_spec.2.2.2.2

/-- The source of the chart at `a`, as an open set. -/
private def chartSource (a : Ω) : Opens E :=
  ⟨(chart hf hsurj a).source, (chart hf hsurj a).open_source⟩

/-- The open set `Df(a)⁻¹(Ω')`, into which the chart at `a` maps its source. -/
private def chartTarget (a : Ω) : Opens E :=
  ⟨fderiv ℝ f a ⁻¹' Ω', Ω'.isOpen.preimage (fderiv ℝ f a).continuous⟩

include hfΩ in
private theorem mapsTo_chart (a : Ω) :
    MapsTo (chart hf hsurj a) (chartSource hf hsurj a) (chartTarget (f := f) (Ω' := Ω') a) := by
  intro x hx
  have h := eqOn_chart hf hsurj a hx
  simp only [Function.comp_apply] at h
  rw [chartTarget, Opens.coe_mk, mem_preimage, ← h]
  exact hfΩ (chart_source_subset hf hsurj a hx)

private theorem iSup_chartSource : ⨆ a, chartSource hf hsurj a = Ω := by
  refine le_antisymm (iSup_le fun a _ hx ↦ chart_source_subset hf hsurj a hx) fun x hx ↦ ?_
  exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, mem_chart_source hf hsurj ⟨x, hx⟩⟩

end Chart

section Submersion

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]

/-- `TestFunction.ext_of_forall_integral_smul_eq` for real-valued tests, with the integrands in
the order `ψ y • g y` of the defining identity of fibre integration. -/
private theorem ext_of_forall_integral_smul_contDiff_eq {ψ₁ ψ₂ : 𝓓(Ω', ℝ)}
    (h : ∀ g : E' → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ω' →
      ∫ y, ψ₁ y • g y ∂ν = ∫ y, ψ₂ y • g y ∂ν) :
    ψ₁ = ψ₂ :=
  ext_of_forall_integral_smul_eq (μ := ν) fun g hg hgc hgΩ ↦ by
    simpa only [smul_eq_mul, mul_comm (g _)] using h g hg hgc hgΩ

/-- `IsOpen.eqOn_zero_of_integral_contDiff_smul_eq_zero` for real-valued functions, with the
integrands in the order `d y • g y` of the defining identity of fibre integration. -/
private theorem eqOn_zero_of_integral_smul_contDiff_eq_zero {U : Set E'} (hU : IsOpen U)
    {d : E' → ℝ} (hd : ContinuousOn d U)
    (h : ∀ g : E' → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ y, d y • g y ∂ν = 0) :
    EqOn d 0 U :=
  hU.eqOn_zero_of_integral_contDiff_smul_eq_zero (μ := ν) hd fun g hg hgc hgU ↦ by
    simpa only [smul_eq_mul, mul_comm (g _)] using h g hg hgc hgU

variable {f : E → E'} (hf : ContDiffOn ℝ ∞ f Ω) (hfΩ : MapsTo f Ω Ω')
  (hsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f x))

/-- Fibre integration of tests supported in the source of the chart at `a`: the pushforward along
the chart followed by fibre integration along `Df(a)`. -/
private def localFiberIntegral (a : Ω) : 𝓓(chartSource hf hsurj a, ℝ) →L[ℝ] 𝓓(Ω', ℝ) :=
  linearFiberIntegral (hsurj a a.property) (W := chartTarget (f := f) (Ω' := Ω') a) (fun _ hx ↦ hx)
      μ ν ∘L
    pushforwardCLM (chart hf hsurj a) (contDiffOn_chart hf hsurj a)
      (contDiffOn_chart_symm hf hsurj a) subset_rfl (mapsTo_chart hf hfΩ hsurj a)

/-- The defining identity of the local fibre integrals. -/
private theorem integral_localFiberIntegral_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (a : Ω) (φ : 𝓓(chartSource hf hsurj a, ℝ))
    {g : E' → G} (hg : ContinuousOn g Ω') :
    ∫ y, localFiberIntegral μ ν hf hfΩ hsurj a φ y • g y ∂ν = ∫ x, φ x • g (f x) ∂μ := by
  set Θ := chart hf hsurj a
  set A := fderiv ℝ f a
  calc ∫ y, localFiberIntegral μ ν hf hfΩ hsurj a φ y • g y ∂ν
      = ∫ z, pushforwardCLM Θ (contDiffOn_chart hf hsurj a) (contDiffOn_chart_symm hf hsurj a)
          subset_rfl (mapsTo_chart hf hfΩ hsurj a) φ z • g (A z) ∂μ :=
        integral_linearFiberIntegral_smul (hsurj a a.property) (fun _ hx ↦ hx) μ ν _ hg
    _ = ∫ x, φ x • g (A (Θ x)) ∂μ := integral_pushforwardCLM_smul μ φ (fun z ↦ g (A z))
    _ = ∫ x, φ x • g (f x) ∂μ := integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ (chart hf hsurj a).source
  · simp only [eqOn_chart hf hsurj a hx, Function.comp_apply, A, Θ]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)]

/-- The local fibre integrals agree on tests supported in the overlap of two chart sources. -/
private theorem localFiberIntegral_monoCLM (a b : Ω)
    (φ : 𝓓(chartSource hf hsurj a ⊓ chartSource hf hsurj b, ℝ)) :
    localFiberIntegral μ ν hf hfΩ hsurj a (monoCLM ℝ φ) =
      localFiberIntegral μ ν hf hfΩ hsurj b (monoCLM ℝ φ) :=
  ext_of_forall_integral_smul_contDiff_eq ν fun g hg _ _ ↦ by
    rw [integral_localFiberIntegral_smul μ ν hf hfΩ hsurj a _ hg.continuous.continuousOn,
      integral_localFiberIntegral_smul μ ν hf hfΩ hsurj b _ hg.continuous.continuousOn]
    simp

private theorem existsUnique_fiberIntegral :
    ∃! S : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω', ℝ),
      ∀ a, S ∘L monoCLM ℝ = localFiberIntegral μ ν hf hfΩ hsurj a :=
  Distribution.existsUnique_gluing (iSup_chartSource hf hsurj)
    (localFiberIntegral_monoCLM μ ν hf hfΩ hsurj)

variable (f) in
/-- **Fibre integration along a submersion.** For `f` smooth on `Ω`, mapping `Ω` into `Ω'`, with
surjective derivative at every point of `Ω`, the continuous linear map sending a test function `φ`
on `Ω` to the test function `f_♯ φ` on `Ω'` with
`∫ y, (f_♯ φ) y • g y ∂ν = ∫ x, φ x • g (f x) ∂μ` for every `g` continuous on `Ω'`
(`TestFunction.integral_fiberIntegralCLM_smul`, `TestFunction.eq_fiberIntegralCLM_iff`): the
density with respect to `ν` of the image under `f` of the measure `φ μ`. -/
def fiberIntegralCLM : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω', ℝ) :=
  (existsUnique_fiberIntegral μ ν hf hfΩ hsurj).exists.choose

private theorem fiberIntegralCLM_comp_monoCLM (a : Ω) :
    fiberIntegralCLM μ ν f hf hfΩ hsurj ∘L monoCLM ℝ = localFiberIntegral μ ν hf hfΩ hsurj a :=
  (existsUnique_fiberIntegral μ ν hf hfΩ hsurj).exists.choose_spec a

/-- **The defining identity of fibre integration**: integrating against `f_♯ φ` is integrating
against `φ` after composing with `f`. -/
theorem integral_fiberIntegralCLM_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (φ : 𝓓(Ω, ℝ)) {g : E' → G} (hg : ContinuousOn g Ω') :
    ∫ y, fiberIntegralCLM μ ν f hf hfΩ hsurj φ y • g y ∂ν = ∫ x, φ x • g (f x) ∂μ := by
  -- Both sides are continuous linear in `φ`, and they agree on tests supported in each chart.
  have hgf : ContinuousOn (fun x ↦ g (f x)) Ω := hg.comp hf.continuousOn hfΩ
  have h := Distribution.eq_of_forall_comp_monoCLM_eq (iSup_chartSource hf hsurj)
    (S := integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) ν g ∘L
      fiberIntegralCLM μ ν f hf hfΩ hsurj)
    (S' := integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ fun x ↦ g (f x))
    fun a ↦ by
      ext ψ
      rw [ContinuousLinearMap.comp_assoc, fiberIntegralCLM_comp_monoCLM]
      simp only [ContinuousLinearMap.comp_apply]
      rw [integralAgainstBilinCLM_eq_integral (hg.locallyIntegrableOn Ω'.isOpen.measurableSet),
        integralAgainstBilinCLM_eq_integral (hgf.locallyIntegrableOn Ω.isOpen.measurableSet)]
      have hle : chartSource hf hsurj a ≤ Ω := fun x hx ↦ chart_source_subset hf hsurj a hx
      simpa [hle] using integral_localFiberIntegral_smul μ ν hf hfΩ hsurj a ψ hg
  have := congrArg (fun S ↦ S φ) h
  simp only [ContinuousLinearMap.comp_apply] at this
  rwa [integralAgainstBilinCLM_eq_integral (hg.locallyIntegrableOn Ω'.isOpen.measurableSet),
    integralAgainstBilinCLM_eq_integral (hgf.locallyIntegrableOn Ω.isOpen.measurableSet)] at this

/-- **Characterization of fibre integration**: `f_♯ φ` is the only test function on `Ω'` whose
integrals against smooth functions compactly supported in `Ω'` are those of `φ` composed with
`f`. -/
theorem eq_fiberIntegralCLM_iff {φ : 𝓓(Ω, ℝ)} {ψ : 𝓓(Ω', ℝ)} :
    ψ = fiberIntegralCLM μ ν f hf hfΩ hsurj φ ↔
      ∀ g : E' → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ω' →
        ∫ y, ψ y • g y ∂ν = ∫ x, φ x • g (f x) ∂μ := by
  refine ⟨?_, fun h ↦ ext_of_forall_integral_smul_contDiff_eq ν fun g hg hgc hgΩ ↦ ?_⟩
  · rintro rfl g hg - -
    exact integral_fiberIntegralCLM_smul μ ν hf hfΩ hsurj φ hg.continuous.continuousOn
  · rw [h g hg hgc hgΩ, integral_fiberIntegralCLM_smul μ ν hf hfΩ hsurj φ
      hg.continuous.continuousOn]

/-- The fibre integral of `φ` is supported in the image under `f` of the support of `φ`. -/
theorem tsupport_fiberIntegralCLM_subset (φ : 𝓓(Ω, ℝ)) :
    tsupport (fiberIntegralCLM μ ν f hf hfΩ hsurj φ) ⊆ f '' tsupport φ := by
  have hK : IsCompact (f '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn (hf.continuousOn.mono φ.tsupport_subset)
  refine closure_minimal (fun y hy ↦ ?_) hK.isClosed
  by_contra hyK
  -- Off the compact set `f '' supp φ`, the fibre integral has zero integral against every test
  -- function, so it vanishes there.
  refine hy (eqOn_zero_of_integral_smul_contDiff_eq_zero ν hK.isClosed.isOpen_compl
    (fiberIntegralCLM μ ν f hf hfΩ hsurj φ).continuous.continuousOn (fun g hg _ hgK ↦ ?_) hyK)
  rw [integral_fiberIntegralCLM_smul μ ν hf hfΩ hsurj φ hg.continuous.continuousOn]
  have h0 : (fun x ↦ φ x • g (f x)) = 0 := funext fun x ↦ by
    by_cases hx : x ∈ tsupport φ
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hgK h ⟨x, hx, rfl⟩, smul_zero, Pi.zero_apply]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, Pi.zero_apply]
  rw [h0]
  exact integral_zero E ℝ

/-- Along a change of variables `e`, fibre integration with respect to one Haar measure is the
pushforward of test densities `TestFunction.pushforwardCLM`. -/
theorem fiberIntegralCLM_eq_pushforwardCLM {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {Ω₁ Ω₂ : Opens E} (hΩ₁ : (Ω₁ : Set E) ⊆ e.source) (hΩ₁₂ : MapsTo e Ω₁ Ω₂)
    {hsurj : ∀ x ∈ Ω₁, Function.Surjective (fderiv ℝ e x)} :
    fiberIntegralCLM μ μ e (he.mono hΩ₁) hΩ₁₂ hsurj = pushforwardCLM e he he' hΩ₁ hΩ₁₂ := by
  ext φ : 1
  refine ((eq_fiberIntegralCLM_iff μ μ _ _ _).2 fun g _ _ _ ↦ ?_).symm
  exact integral_pushforwardCLM_smul μ φ g

/-- Fibre integration only depends on the values of the submersion on `Ω`. -/
theorem fiberIntegralCLM_congr {f₂ : E → E'} (h : EqOn f f₂ Ω)
    {hf₂ : ContDiffOn ℝ ∞ f₂ Ω} {hf₂Ω : MapsTo f₂ Ω Ω'}
    {hsurj₂ : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ f₂ x)} :
    fiberIntegralCLM μ ν f₂ hf₂ hf₂Ω hsurj₂ = fiberIntegralCLM μ ν f hf hfΩ hsurj := by
  ext φ : 1
  refine (eq_fiberIntegralCLM_iff μ ν _ _ _).2 fun g hg _ _ ↦ ?_
  rw [integral_fiberIntegralCLM_smul μ ν hf₂ hf₂Ω hsurj₂ φ hg.continuous.continuousOn]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ Ω
  · simp only [h hx]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)]

/-- **Restriction of fibre integration**: on tests supported in an open set `U ≤ Ω`, fibre
integration along `f` on `U` is fibre integration along `f` on `Ω`. -/
@[simp]
theorem fiberIntegralCLM_monoCLM {U : Opens E} (hU : U ≤ Ω) (φ : 𝓓(U, ℝ)) :
    fiberIntegralCLM μ ν f hf hfΩ hsurj (monoCLM ℝ φ) =
      fiberIntegralCLM μ ν f (hf.mono hU) (hfΩ.mono_left hU) (fun x hx ↦ hsurj x (hU hx)) φ := by
  refine ((eq_fiberIntegralCLM_iff μ ν _ _ _).2 fun g hg _ _ ↦ ?_).symm
  rw [integral_fiberIntegralCLM_smul μ ν _ _ _ φ hg.continuous.continuousOn]
  simp [monoCLM_apply, hU]

/-- **Fibre integration is functorial**: integrating over the fibres of `f` and then over those of
`g` is integrating over the fibres of `g ∘ f`. -/
theorem fiberIntegralCLM_comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E''] (ρ : Measure E'')
    [ρ.IsAddHaarMeasure] {Ω'' : Opens E''} {g : E' → E''} (hg : ContDiffOn ℝ ∞ g Ω')
    (hgΩ : MapsTo g Ω' Ω'') (hgsurj : ∀ y ∈ Ω', Function.Surjective (fderiv ℝ g y))
    {hgf : ContDiffOn ℝ ∞ (g ∘ f) Ω} {hgfΩ : MapsTo (g ∘ f) Ω Ω''}
    {hgfsurj : ∀ x ∈ Ω, Function.Surjective (fderiv ℝ (g ∘ f) x)} :
    fiberIntegralCLM μ ρ (g ∘ f) hgf hgfΩ hgfsurj =
      (fiberIntegralCLM ν ρ g hg hgΩ hgsurj).comp (fiberIntegralCLM μ ν f hf hfΩ hsurj) := by
  ext φ : 1
  refine ((eq_fiberIntegralCLM_iff μ ρ _ _ _).2 fun u hu _ _ ↦ ?_).symm
  rw [ContinuousLinearMap.comp_apply,
    integral_fiberIntegralCLM_smul ν ρ hg hgΩ hgsurj _ hu.continuous.continuousOn]
  exact integral_fiberIntegralCLM_smul μ ν hf hfΩ hsurj φ
    (hu.continuous.comp_continuousOn hg.continuousOn)

end Submersion

end TestFunction
