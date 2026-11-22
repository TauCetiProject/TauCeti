/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import TauCeti.Analysis.Distribution.TestFunction.Homotopy
public import TauCeti.Analysis.Distribution.TestFunction.TranslateAverage
public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.MeasureTheory.Measure.Comap
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Mollification of test forms on the whole space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`ρ` be a smooth bump function centred at `0`, normalized to `ρ̂ = ρ.normed μ` of integral one and
supported in the closed ball of radius `r = ρ.rOut`. Mollification of test forms on `E`,

`(M ω) x = ∫ ρ̂ y ω (x + y) dμ(y) = (ρ̂ ⋆ ω) x`,

is a continuous linear map of the LF space of test forms (`TestFunction.mollifyCLM`), commuting
with the exterior derivative, not increasing sup norms, and converging to the identity as the bump
shrinks.

Averaging the straight-line homotopies `x ↦ x + t y` against `ρ̂ y` gives the operator

`(K ω) x = ∫ ρ̂ y ∫₀¹ ω (x + t y) (y, ·) dt dμ(y)`

(`TestFunction.mollifyHomotopyCLM`), with the homotopy formula `K d + d K = M - id` on forms of
positive degree and `K d = M - id` on functions, the sup bound `‖K ω‖ ≤ r ‖ω‖`, and support in
the closed `r`-neighbourhood of the support of `ω`. Precomposing currents with `M` and `K`
mollifies currents, see `TauCeti.Analysis.Distribution.Flat.Mollify`.

The homotopy formula is proved for currents first. A current passes under the averages
(`ContinuousLinearMap.apply_translateAverageCLM`), so it reduces to the homotopy formula for each
straight-line homotopy (`ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM`); applying
it to evaluations at points gives the identity of test forms.

## Main declarations

* `TestFunction.mollifyCLM`: mollification of test functions on `E`, with
  `TestFunction.mollifyCLM_apply_eq_integral` giving it as an average of translates and
  `TestFunction.mollifyCLM_apply` identifying it with the convolution `ρ̂ ⋆ ω`.
* `TestFunction.tsupport_mollifyCLM_subset`: the support of `M φ`.
* `TestFunction.apply_mollifyCLM`: a current passes under `M`, as the average of the translates
  `TauCeti.translateTestFunction`.
* `TestFunction.extDerivCLM_comp_mollifyCLM`: `d ∘ M = M ∘ d`.
* `TestFunction.mollifyHomotopyCLM`: the averaged straight-line homotopy operator `K`.
* `TestFunction.tsupport_mollifyHomotopyCLM_subset`: the support of `K ω`.
* `TestFunction.apply_mollifyHomotopyCLM`: a current passes under `K`, as the average of the
  contracted translates.
* `TestFunction.mollifyHomotopyCLM_comp_extDerivCLM`: `K ∘ d = M - id - d ∘ K`, and
  `TestFunction.mollifyHomotopyCLM_comp_extDerivCLM_finZero` in degree zero.

## References

* H. Federer, *Geometric Measure Theory*, §4.1 (regularization by convolution).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula for
  translations).
-/

public section

noncomputable section

open Set Function MeasureTheory Metric TopologicalSpace Filter ContinuousAlternatingMap
open scoped Distributions Topology Convolution Pointwise

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ}

section Parameters

private theorem continuous_homotopyShift (r : ℝ) :
    Continuous fun q : closedBall (0 : E) r × unitInterval ↦ (q.2 : ℝ) • (q.1 : E) :=
  (continuous_subtypeVal.comp continuous_snd).smul (continuous_subtypeVal.comp continuous_fst)

variable [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (ρ : ContDiffBump (0 : E))

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The weights of the mollification. -/
private theorem continuous_mollifyWeight :
    Continuous fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y • ContinuousLinearMap.id ℝ F :=
  (ρ.continuous_normed.comp continuous_subtypeVal).smul continuous_const

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The weights of the averaged homotopy operator. -/
private theorem continuous_homotopyWeight :
    Continuous fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦
      (curryLeftFlipL (ρ.normed μ q.1 • (q.1 : E)) : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) :=
  curryLeftFlipL.continuous.comp ((ρ.continuous_normed.comp
    (continuous_subtypeVal.comp continuous_fst)).smul (continuous_subtypeVal.comp continuous_fst))

end Parameters

section LineHomotopy

variable [FiniteDimensional ℝ F] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] {m : ℕ}

/-- The straight-line homotopy `(x, t) ↦ x + t y` from the identity to the translation by `y`. -/
private def lineHomotopy (y : E) (p : E × ℝ) : E :=
  p.1 + p.2 • y

private theorem contDiffAt_lineHomotopy (y : E) :
    ∀ p ∈ ((⊤ : Opens E) : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) (lineHomotopy y) p :=
  fun _ _ ↦ (contDiff_fst.add (contDiff_snd.smul contDiff_const)).contDiffAt

private theorem isCompact_lineHomotopy (y : E) : ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
    IsCompact ((((⊤ : Opens E) : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ lineHomotopy y ⁻¹' K) := by
  intro K hK _
  -- The preimage is closed and lies in the image of `K × [0, 1]` under `(z, t) ↦ (z - t y, t)`.
  refine ((hK.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).image
    (f := fun q : E × ℝ ↦ (q.1 - q.2 • y, q.2)) (by fun_prop)).of_isClosed_subset
    ((isClosed_univ.prod isClosed_Icc).inter
      (hK.isClosed.preimage (by unfold lineHomotopy; fun_prop))) ?_
  rintro ⟨x, t⟩ ⟨⟨-, ht⟩, hx⟩
  exact ⟨(x + t • y, t), ⟨hx, ht⟩, by simp⟩

private theorem contDiffOn_lineHomotopy_slice (y : E) (s : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy y (x, s)) (⊤ : Opens E) :=
  (contDiff_id.add contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun x : E ↦ x + s • y).contDiffOn

private theorem isCompact_lineHomotopy_slice (y : E) (s : ℝ) :
    ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
      IsCompact (((⊤ : Opens E) : Set E) ∩ (fun x ↦ lineHomotopy y (x, s)) ⁻¹' K) := by
  intro K hK _
  simpa [lineHomotopy] using (Homeomorph.addRight (s • y)).isCompact_preimage.2 hK

omit [FiniteDimensional ℝ F] in
/-- Pulling back along a slice of the straight-line homotopy translates. -/
private theorem pullbackCLM_lineHomotopy_apply (y : E) (s : ℝ)
    {h₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy y (x, s)) (⊤ : Opens E)}
    {h₂ : ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
      IsCompact (((⊤ : Opens E) : Set E) ∩ (fun x ↦ lineHomotopy y (x, s)) ⁻¹' K)}
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F)) (x : E) :
    pullbackCLM (fun x ↦ lineHomotopy y (x, s)) h₁ h₂ ω x = ω (x + s • y) := by
  have hD : fderiv ℝ (fun x ↦ lineHomotopy y (x, s)) x = ContinuousLinearMap.id ℝ E := by
    simp only [lineHomotopy]
    exact ((hasFDerivAt_id x).add_const (s • y)).fderiv
  rw [pullbackCLM_apply_of_mem _ (Opens.mem_top x), hD]
  ext v
  simp [lineHomotopy]

omit [FiniteDimensional ℝ F] in
/-- The slice at time `1` of the straight-line homotopy is the translation `ω ↦ ω (· + y)`. -/
private theorem pullbackCLM_lineHomotopy_one (y : E)
    {h₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy y (x, 1)) (⊤ : Opens E)}
    {h₂ : ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
      IsCompact (((⊤ : Opens E) : Set E) ∩ (fun x ↦ lineHomotopy y (x, 1)) ⁻¹' K)}
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F)) :
    pullbackCLM (fun x ↦ lineHomotopy y (x, 1)) h₁ h₂ ω =
      TauCeti.translateTestFunction (h := -y) (mapsTo_univ _ _) ω := by
  ext x : 1
  rw [pullbackCLM_lineHomotopy_apply, one_smul, TauCeti.translateTestFunction_apply,
    sub_neg_eq_add]

/-- The homotopy operator of the straight-line homotopy from the identity to the translation by
`y`: `x ↦ ∫₀¹ ω (x + t y) (y, ·) dt`. -/
private abbrev lineHomotopyCLM (y : E) :
    𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) :=
  homotopyPullbackCLM (contDiffAt_lineHomotopy y) (isCompact_lineHomotopy y)

private theorem lineHomotopyCLM_apply (y : E) (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F))
    (x : E) : lineHomotopyCLM y ω x = ∫ t in (0 : ℝ)..1, (ω (x + t • y)).curryLeft y := by
  rw [homotopyPullbackCLM_apply_of_mem ω (Opens.mem_top x), TauCeti.cylinderHomotopy_apply]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hD : fderiv ℝ (lineHomotopy y) (x, t) =
      ContinuousLinearMap.fst ℝ E ℝ + (ContinuousLinearMap.snd ℝ E ℝ).smulRight y :=
    (hasFDerivAt_fst.add (hasFDerivAt_snd.smul_const y)).fderiv
  ext v
  simp [hD, lineHomotopy, curryLeft_compContinuousLinearMap, Function.comp_def]

/-- The translates `x ↦ ω (x + t y) (y, ·)` integrated by the straight-line homotopy operator. -/
private abbrev lineHomotopyIntegrand (y : E) (t : ℝ)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) :=
  postcompCLM (curryLeftFlipL y)
    (pullbackCLM _ (contDiffOn_lineHomotopy_slice y t) (isCompact_lineHomotopy_slice y t) ω)

omit [FiniteDimensional ℝ F] in
private theorem lineHomotopyIntegrand_apply (y : E) (t : ℝ)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) (x : E) :
    lineHomotopyIntegrand y t ω x = curryLeftFlipL y (ω (x + t • y)) := by
  rw [postcompCLM_apply, Function.comp_apply, pullbackCLM_lineHomotopy_apply]

variable [FiniteDimensional ℝ E]

/-- A continuous linear map passes under the straight-line homotopy operator. -/
private theorem apply_lineHomotopyCLM (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
    (y : E) (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    S (lineHomotopyCLM y ω) = ∫ t : unitInterval, S (lineHomotopyIntegrand y t ω) := by
  refine S.apply_eq_integral_of_apply_eq_apply_add
    (L := fun _ : unitInterval ↦ curryLeftFlipL y) (v := fun t ↦ (t : ℝ) • y) continuous_const
    (continuous_subtypeVal.smul continuous_const) ω (fun t x ↦ lineHomotopyIntegrand_apply y t ω x)
    fun x ↦ ?_
  rw [lineHomotopyCLM_apply, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, unitInterval.volume_def,
    ← integral_subtype_comap measurableSet_Icc]
  simp only [lineHomotopyIntegrand_apply, curryLeftFlipL_apply_apply]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
/-- The slice at time `0` of the straight-line homotopy is the identity. -/
private theorem pullbackCLM_lineHomotopy_zero (y : E)
    {h₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy y (x, 0)) (⊤ : Opens E)}
    {h₂ : ∀ K : Set E, IsCompact K → K ⊆ (⊤ : Opens E) →
      IsCompact (((⊤ : Opens E) : Set E) ∩ (fun x ↦ lineHomotopy y (x, 0)) ⁻¹' K)}
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F)) :
    pullbackCLM (fun x ↦ lineHomotopy y (x, 0)) h₁ h₂ ω = ω := by
  ext x : 1
  rw [pullbackCLM_lineHomotopy_apply, zero_smul, add_zero]

end LineHomotopy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))

/-- **Mollification** of test functions on `E` by the normalized bump `ρ̂ = ρ.normed μ`:
`(M φ) x = ∫ ρ̂ y φ (x + y) dμ(y)`, which is the convolution `ρ̂ ⋆ φ`, see
`TestFunction.mollifyCLM_apply`. Precomposing a current with it mollifies the current. -/
def mollifyCLM : 𝓓((⊤ : Opens E), F) →L[ℝ] 𝓓((⊤ : Opens E), F) :=
  translateAverageCLM (μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E))
    (continuous_mollifyWeight μ ρ) continuous_subtypeVal

/-- Mollification at a point, as the average of translates over the closed ball of radius
`r = ρ.rOut`: `(M φ) x = ∫ ρ̂ y φ (x + y) dμ(y)`. -/
theorem mollifyCLM_apply_eq_integral (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    mollifyCLM μ ρ φ x =
      ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y • φ (x + y) ∂(μ.comap (↑)) := by
  rw [mollifyCLM, translateAverageCLM_apply]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]

/-- Mollification is convolution with the normalized bump. -/
theorem mollifyCLM_apply (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    mollifyCLM μ ρ φ x = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ) x := by
  rw [mollifyCLM_apply_eq_integral, ρ.integral_closedBall_normed_smul μ (fun y ↦ φ (x + y)),
    convolution_def, ← integral_neg_eq_self]
  simp [ρ.normed_neg, sub_eq_add_neg]

/-- On the whole space, mollification agrees with `TestFunction.mollify`. -/
theorem mollifyCLM_eq_mollify (φ : 𝓓((⊤ : Opens E), F)) :
    mollifyCLM μ ρ φ = mollify φ μ ρ (subset_univ _) := by
  ext x
  rw [mollifyCLM_apply, mollify_apply]

/-- A bound `C` on the values of `φ` bounds its mollification. -/
theorem norm_mollifyCLM_apply_le (φ : 𝓓((⊤ : Opens E), F)) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C)
    (x : E) : ‖mollifyCLM μ ρ φ x‖ ≤ C := by
  rw [mollifyCLM_apply]
  exact ρ.norm_normed_convolution_le hC x

/-- Mollification enlarges supports by at most `r = ρ.rOut`. -/
theorem tsupport_mollifyCLM_subset (φ : 𝓓((⊤ : Opens E), F)) :
    tsupport (mollifyCLM μ ρ φ) ⊆ tsupport φ + closedBall (0 : E) ρ.rOut := by
  rw [show ⇑(mollifyCLM μ ρ φ) = ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ⇑φ from
    funext (mollifyCLM_apply μ ρ φ), add_comm]
  exact ρ.tsupport_normed_convolution_subset

/-- As the bumps shrink, the mollifications of a test function converge to it in the LF
topology. -/
theorem tendsto_mollifyCLM {ι : Type*} {l : Filter ι} [CompleteSpace F]
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), F)) : Tendsto (fun i ↦ mollifyCLM μ (ρ i) φ) l (𝓝 φ) := by
  simp only [mollifyCLM_eq_mollify]
  exact tendsto_mollify φ μ hρ fun _ ↦ subset_univ _

/-- **Mollification commutes with the exterior derivative**: `d ∘ M = M ∘ d`. -/
theorem extDerivCLM_comp_mollifyCLM [CompleteSpace F] {m : ℕ} :
    (extDerivCLM ∘L mollifyCLM μ ρ : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      mollifyCLM μ ρ ∘L extDerivCLM := by
  ext ω x : 2
  ext v
  -- Differentiate `ρ̂ ⋆ ω` in each direction under the integral, and evaluate under it.
  have hint (w : E) := ρ.integrable_normed_smul μ
    ((ω.contDiff.continuous_fderiv_apply (by simp)).comp
      ((continuous_const (y := x)).sub continuous_id |>.prodMk (continuous_const (y := w))))
  have hM : ⇑(mollifyCLM μ ρ ω) = ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ⇑ω :=
    funext (mollifyCLM_apply μ ρ ω)
  have hD (w : E) (u : Fin m → E) :
      fderiv ℝ (mollifyCLM μ ρ ω) x w u = ∫ t, ρ.normed μ t • fderiv ℝ ω (x - t) w u ∂μ := by
    rw [hM, ω.hasCompactSupport.fderiv_convolution_right_apply _
      ρ.continuous_normed.locallyIntegrable (ω.contDiff.of_le (by simp)), convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [ContinuousAlternatingMap.integral_apply
      (φ := fun t ↦ ρ.normed μ t • fderiv ℝ ω (x - t) w) (hint w)]
    simp
  have hR := ρ.integrable_normed_smul μ
    ((extDerivCLM ω).continuous.comp ((continuous_const (y := x)).sub continuous_id))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, extDerivCLM_apply, extDeriv,
    alternatizeUncurryFin_apply, mollifyCLM_apply, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, hD]
  rw [ContinuousAlternatingMap.integral_apply
    (φ := fun t ↦ ρ.normed μ t • extDerivCLM ω (x - t)) hR]
  simp only [ContinuousAlternatingMap.smul_apply, extDerivCLM_apply, extDeriv,
    alternatizeUncurryFin_apply, Finset.smul_sum]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h | h <;> simp [h, integral_neg]
  · have hi := ρ.integrable_normed_smul μ ((continuous_eval_const (i.removeNth v)).comp
      ((ω.contDiff.continuous_fderiv_apply (by simp)).comp
        ((continuous_const (y := x)).sub continuous_id |>.prodMk (continuous_const (y := v i)))))
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h | h <;> simpa [h] using hi

/-- The **averaged homotopy operator** between mollification and the identity on test
`(k + 1)`-forms: `(K ω) x = ∫ ρ̂ y ∫₀¹ ω (x + t y) (y, ·) dt dμ(y)`. It satisfies
`K ∘ d = M - id - d ∘ K` (`TestFunction.mollifyHomotopyCLM_comp_extDerivCLM`). -/
def mollifyHomotopyCLM :
    𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) :=
  translateAverageCLM ((μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E)).prod volume)
    (continuous_homotopyWeight μ ρ) (continuous_homotopyShift _)

/-- The averaged homotopy operator at a point. -/
theorem mollifyHomotopyCLM_apply (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    mollifyHomotopyCLM μ ρ ω x =
      ∫ q : closedBall (0 : E) ρ.rOut × unitInterval,
        ρ.normed μ q.1 • (ω (x + (q.2 : ℝ) • (q.1 : E))).curryLeft (q.1 : E)
          ∂((μ.comap (↑)).prod volume) := by
  rw [mollifyHomotopyCLM, translateAverageCLM_apply]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, curryLeftFlipL_apply_apply]

/-- **Sup bound for the averaged homotopy operator**: `‖K ω‖ ≤ r ‖ω‖`, with `r = ρ.rOut`. -/
theorem norm_mollifyHomotopyCLM_apply_le (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F))
    {C : ℝ} (hC : ∀ y, ‖ω y‖ ≤ C) (x : E) : ‖mollifyHomotopyCLM μ ρ ω x‖ ≤ ρ.rOut * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine (norm_translateAverageCLM_apply_le ω hC x).trans (mul_le_mul_of_nonneg_right ?_ hC0)
  have hw : Continuous fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦ ρ.normed μ q.1 :=
    ρ.continuous_normed.comp (continuous_subtypeVal.comp continuous_fst)
  calc ∫ q : closedBall (0 : E) ρ.rOut × unitInterval,
        ‖(curryLeftFlipL (ρ.normed μ q.1 • (q.1 : E)) : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)‖ ∂_
      ≤ ∫ q : closedBall (0 : E) ρ.rOut × unitInterval, ρ.rOut * ρ.normed μ q.1
          ∂((μ.comap (↑)).prod volume) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
          ((hw.const_mul _).integrable_of_hasCompactSupport (.of_compactSpace _))
          (ae_of_all _ fun q ↦ ?_)
        dsimp only
        refine (norm_curryLeftFlipL_apply_le _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _), mul_comm]
        exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 q.1.property)
          (ρ.nonneg_normed _)
    _ = ρ.rOut := by
        rw [integral_const_mul, integral_prod _
          (hw.integrable_of_hasCompactSupport (.of_compactSpace _))]
        simp [ρ.integral_closedBall_normed]

/-- The averaged homotopy operator enlarges supports by at most `r = ρ.rOut`. -/
theorem tsupport_mollifyHomotopyCLM_subset (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (mollifyHomotopyCLM μ ρ ω) ⊆ tsupport ω + closedBall (0 : E) ρ.rOut := by
  refine (tsupport_translateAverageCLM_subset ω).trans ?_
  rintro _ ⟨⟨x, y, t⟩, ⟨hx, -⟩, rfl⟩
  refine ⟨x, hx, -((t : ℝ) • (y : E)), ?_, (sub_eq_add_neg _ _).symm⟩
  rw [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_of_nonneg t.property.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans
    (mem_closedBall_zero_iff.1 y.property)

section Currents

variable {G V : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **A current passes under mollification**, as the average of its translates:
`S (M ω) = ∫ ρ̂ y S (ω (· + y)) dμ(y)`. -/
theorem apply_mollifyCLM (S : 𝓓((⊤ : Opens E), G) →L[ℝ] V) (ω : 𝓓((⊤ : Opens E), G)) :
    S (mollifyCLM μ ρ ω) = ∫ y : closedBall (0 : E) ρ.rOut,
      ρ.normed μ y • S (TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω)
        ∂(μ.comap (↑)) := by
  rw [mollifyCLM, S.apply_translateAverageCLM ω
    (f := fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y •
      TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω)
    fun y x ↦ by simp [sub_neg_eq_add]]
  simp only [map_smul]

omit [FiniteDimensional ℝ G] [CompleteSpace V] in
/-- The translates averaged by mollification, tested against a current, are integrable. -/
private theorem integrable_apply_translateTestFunction (S : 𝓓((⊤ : Opens E), G) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), G)) :
    Integrable (fun y : closedBall (0 : E) ρ.rOut ↦
      ρ.normed μ y • S (TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω))
      (μ.comap (↑)) := by
  simpa only [Function.comp_def, map_smul] using (S.continuous.comp
    (continuous_of_apply_eq_apply_add (continuous_mollifyWeight μ ρ) continuous_subtypeVal ω
      (f := fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y •
        TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω)
      fun y x ↦ by simp [sub_neg_eq_add])).integrable_of_hasCompactSupport
    (μ := μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E)) (.of_compactSpace _)

/-- **A current passes under the averaged homotopy operator**, as the average of the translates
`ω (· + t y)` contracted with `y`: `S (K ω) = ∫ ρ̂ y S (ω (· + t y) (y, ·)) d(μ × dt)(y, t)`. -/
theorem apply_mollifyHomotopyCLM [FiniteDimensional ℝ F]
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    S (mollifyHomotopyCLM μ ρ ω) = ∫ q : closedBall (0 : E) ρ.rOut × unitInterval,
      ρ.normed μ q.1 • S (postcompCLM (curryLeftFlipL (q.1 : E))
        (TauCeti.translateTestFunction (h := -((q.2 : ℝ) • (q.1 : E))) (mapsTo_univ _ _) ω))
        ∂((μ.comap (↑)).prod volume) := by
  rw [mollifyHomotopyCLM, S.apply_translateAverageCLM ω
    (f := fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦
      ρ.normed μ q.1 • postcompCLM (curryLeftFlipL (q.1 : E))
      (TauCeti.translateTestFunction (h := -((q.2 : ℝ) • (q.1 : E))) (mapsTo_univ _ _) ω))
    fun q x ↦ by simp [sub_neg_eq_add, map_smul]]
  simp only [map_smul]

end Currents

section Identities

variable [FiniteDimensional ℝ F] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] {m : ℕ}

/-- The family integrated by the averaged homotopy operator. -/
private abbrev mollifyHomotopyIntegrand (q : closedBall (0 : E) ρ.rOut × unitInterval)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) :=
  ρ.normed μ q.1 • lineHomotopyIntegrand (q.1 : E) q.2 ω

omit [FiniteDimensional ℝ F] [BorelSpace E] [μ.IsAddHaarMeasure] [CompleteSpace V] in
private theorem continuous_mollifyHomotopyIntegrand
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    Continuous fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦
      S (mollifyHomotopyIntegrand μ ρ q ω) :=
  S.continuous.comp (continuous_of_apply_eq_apply_add (continuous_homotopyWeight μ ρ)
    (continuous_homotopyShift _) ω fun q x ↦ by
      simp [lineHomotopyIntegrand_apply, curryLeftFlipL_apply_apply, map_smul])

/-- **A current passes under the averaged homotopy operator**, as the average of the
straight-line homotopy currents: `S (K ω) = ∫ ρ̂ y S (h_y ω) dμ(y)`, and the integrand is
integrable. -/
private theorem apply_mollifyHomotopyCLM_lineHomotopyCLM
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    Integrable (fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y • S (lineHomotopyCLM (y : E) ω))
      (μ.comap (↑)) ∧
    S (mollifyHomotopyCLM μ ρ ω) = ∫ y : closedBall (0 : E) ρ.rOut,
      ρ.normed μ y • S (lineHomotopyCLM (y : E) ω) ∂(μ.comap (↑)) := by
  have hint := (continuous_mollifyHomotopyIntegrand μ ρ S ω).integrable_of_hasCompactSupport
    (μ := (μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E)).prod volume) (.of_compactSpace _)
  have hinner (y : closedBall (0 : E) ρ.rOut) :
      ∫ t : unitInterval, S (mollifyHomotopyIntegrand μ ρ (y, t) ω) =
        ρ.normed μ y • S (lineHomotopyCLM (y : E) ω) := by
    simp only [map_smul, integral_smul, apply_lineHomotopyCLM]
  refine ⟨(hint.integral_prod_left).congr (ae_of_all _ hinner), ?_⟩
  rw [mollifyHomotopyCLM, S.apply_translateAverageCLM ω
    (f := fun q ↦ mollifyHomotopyIntegrand μ ρ q ω) fun q x ↦ by
      simp [lineHomotopyIntegrand_apply, curryLeftFlipL_apply_apply, map_smul],
    integral_prod _ hint]
  exact integral_congr_ae (ae_of_all _ hinner)

/-- The homotopy formula for the averaged homotopy operator, tested against a current. -/
private theorem apply_mollifyHomotopyCLM_extDerivCLM
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    S (mollifyHomotopyCLM μ ρ (extDerivCLM ω)) =
      S (mollifyCLM μ ρ ω) - S ω - S (extDerivCLM (mollifyHomotopyCLM μ ρ ω)) := by
  have hy (y : closedBall (0 : E) ρ.rOut) :
      S (lineHomotopyCLM (y : E) (extDerivCLM ω)) =
        S (TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω) - S ω -
          (S ∘L extDerivCLM) (lineHomotopyCLM (y : E) ω) := by
    have h := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM
      (hH := contDiffAt_lineHomotopy (y : E)) (hHp := isCompact_lineHomotopy (y : E)) S) ω)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      pullbackCLM_lineHomotopy_zero, pullbackCLM_lineHomotopy_one] at h
    exact h
  have hM := integrable_apply_translateTestFunction μ ρ S ω
  obtain ⟨hK, hKe⟩ := apply_mollifyHomotopyCLM_lineHomotopyCLM μ ρ (S ∘L extDerivCLM) ω
  have hc := ρ.integrable_closedBall_normed_smul_const μ (S ω)
  rw [(apply_mollifyHomotopyCLM_lineHomotopyCLM μ ρ S _).2, apply_mollifyCLM μ ρ S ω,
    ← ContinuousLinearMap.comp_apply S extDerivCLM, hKe,
    ← ρ.integral_closedBall_normed_smul_const μ (S ω), ← integral_sub hM hc]
  rw [← integral_sub (f := fun y : closedBall (0 : E) ρ.rOut ↦
      ρ.normed μ y • S (TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω) -
        ρ.normed μ y • S ω) (hM.sub hc) hK]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [hy, smul_sub, smul_sub]

/-- The degree-zero homotopy formula for the averaged homotopy operator, tested against a
current. -/
private theorem apply_mollifyHomotopyCLM_extDerivCLM_finZero
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] F)) :
    S (mollifyHomotopyCLM μ ρ (extDerivCLM ω)) = S (mollifyCLM μ ρ ω) - S ω := by
  have hy (y : closedBall (0 : E) ρ.rOut) :
      S (lineHomotopyCLM (y : E) (extDerivCLM ω)) =
        S (TauCeti.translateTestFunction (h := -(y : E)) (mapsTo_univ _ _) ω) - S ω := by
    have h := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM_finZero
      (hH := contDiffAt_lineHomotopy (y : E)) (hHp := isCompact_lineHomotopy (y : E)) S) ω)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      pullbackCLM_lineHomotopy_zero, pullbackCLM_lineHomotopy_one] at h
    exact h
  have hM := integrable_apply_translateTestFunction μ ρ S ω
  have hc := ρ.integrable_closedBall_normed_smul_const μ (S ω)
  rw [(apply_mollifyHomotopyCLM_lineHomotopyCLM μ ρ S _).2, apply_mollifyCLM μ ρ S ω,
    ← ρ.integral_closedBall_normed_smul_const μ (S ω), ← integral_sub hM hc]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [hy, smul_sub]

end Identities

section FormIdentities

variable [FiniteDimensional ℝ F] {m : ℕ}

/-- **The homotopy formula for mollification** on test `(k + 1)`-forms:
`K ∘ d = M - id - d ∘ K`, where `M` is mollification and `K` the averaged straight-line homotopy
operator. -/
theorem mollifyHomotopyCLM_comp_extDerivCLM :
    (mollifyHomotopyCLM μ ρ ∘L extDerivCLM :
        𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      mollifyCLM μ ρ - ContinuousLinearMap.id ℝ _ - extDerivCLM ∘L mollifyHomotopyCLM μ ρ := by
  ext ω x : 2
  exact apply_mollifyHomotopyCLM_extDerivCLM μ ρ
    (BoundedContinuousFunction.evalCLM ℝ x ∘L toBoundedContinuousFunctionCLM ℝ) ω

/-- **The homotopy formula for mollification** on test functions: `K ∘ d = M - id`, where `M` is
mollification and `K` the averaged straight-line homotopy operator. -/
theorem mollifyHomotopyCLM_comp_extDerivCLM_finZero :
    (mollifyHomotopyCLM μ ρ ∘L extDerivCLM :
        𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      mollifyCLM μ ρ - ContinuousLinearMap.id ℝ _ := by
  ext ω x : 2
  exact apply_mollifyHomotopyCLM_extDerivCLM_finZero μ ρ
    (BoundedContinuousFunction.evalCLM ℝ x ∘L toBoundedContinuousFunctionCLM ℝ) ω

end FormIdentities

end TestFunction
