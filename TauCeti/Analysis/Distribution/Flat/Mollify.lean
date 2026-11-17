/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
public import TauCeti.Analysis.Distribution.TestFunction.Homotopy
public import TauCeti.Analysis.Distribution.TestFunction.TranslateAverage
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Mollification of currents in Euclidean space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`ρ` be a smooth bump function centred at `0`, normalized to `ρ̂ = ρ.normed μ` of integral one and
supported in the closed ball of radius `r = ρ.rOut`. Mollification of test forms on `E`,

`(M ω) x = ∫ ρ̂ y ω (x + y) dμ(y) = (ρ̂ ⋆ ω) x`,

is a continuous linear map of the LF space of test forms (`TestFunction.mollifyCLM`), commuting
with the exterior derivative. So the **mollification** of a current `T` on `E` is `T ∘ M`; its
boundary is the mollification of `∂T = T ∘ d`, its mass is at most `M(T)`, and it converges to `T`
on every test form as the bump shrinks.

Averaging the straight-line homotopies `x ↦ x + t y` against `ρ̂ y` gives the operator

`(K ω) x = ∫ ρ̂ y ∫₀¹ ω (x + t y) (y, ·) dt dμ(y)`

(`TestFunction.mollifyHomotopyCLM`), with the homotopy formula `K d + d K = M - id` on forms of
positive degree and `K d = M - id` on functions. Its sup bound `‖K ω‖ ≤ r ‖ω‖` gives the
decomposition `T - T ∘ M = R + ∂S` with `S = -(T ∘ K)` and `R = -(∂T ∘ K)`, of masses at most
`r M(T)` and `r M(∂T)`. Hence the **flat estimate**: for every real current `T` of positive
degree,

`F(T - T ∘ M) ≤ r (M(T) + M(∂T))`,

for the real normal flat mass `F = ContinuousLinearMap.normalFlatMass`, and `F(T - T ∘ M) ≤ r M(T)`
in degree zero; the bounds are infinite unless `T` is normal. Mollification thus approximates
normal currents in flat mass as `r → 0`, keeping both mass and boundary mass bounded. This is real
approximation: it does not preserve integer multiplicities.

The identities are proved for currents first. A current passes under the averages
(`ContinuousLinearMap.apply_translateAverageCLM`), so they reduce to the homotopy formula for each
straight-line homotopy (`ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM`); applying
them to evaluations at points gives the identities of test forms.

## Main declarations

* `TestFunction.mollifyCLM`: mollification of test functions on `E`, with
  `TestFunction.mollifyCLM_apply` identifying it with the convolution `ρ̂ ⋆ ω`.
* `TestFunction.extDerivCLM_comp_mollifyCLM`: `d ∘ M = M ∘ d`.
* `TestFunction.mollifyHomotopyCLM`: the averaged straight-line homotopy operator `K`.
* `TestFunction.mollifyHomotopyCLM_comp_extDerivCLM`: `K ∘ d = M - id - d ∘ K`, and
  `TestFunction.mollifyHomotopyCLM_comp_extDerivCLM_finZero` in degree zero.
* `ContinuousLinearMap.comp_mollifyCLM_comp_extDerivCLM`: `∂(T ∘ M) = (∂T) ∘ M`.
* `ContinuousLinearMap.tendsto_comp_mollifyCLM`: `T ∘ M → T` on every test form as `r → 0`.
* `Distribution.mass_comp_mollifyCLM_le`: `M(T ∘ M) ≤ M(T)`.
* `Distribution.mass_comp_mollifyHomotopyCLM_le`: `M(T ∘ K) ≤ r M(T)`.
* `Distribution.IsNormal.comp_mollifyCLM`: mollification preserves normal currents.
* `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le`: the flat estimate, and
  `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le_finZero` in degree zero.

## References

* H. Federer, *Geometric Measure Theory*, §4.1 (regularization of currents by convolution and
  its flat estimate).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula for
  translations).
-/

public section

noncomputable section

open Set Function MeasureTheory Metric TopologicalSpace Filter ContinuousAlternatingMap
open scoped Distributions Topology ENNReal NNReal Convolution BoundedContinuousFunction

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ}

section Parameters

/-- The contraction `α ↦ α (y, ·)` of `(k + 1)`-forms with a vector `y`, as a continuous linear
map depending linearly on `y`. -/
private def curryLeftCLM : E →L[ℝ] (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
  (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.flip

private theorem curryLeftCLM_apply (y : E) (α : E [⋀^Fin (k + 1)]→L[ℝ] F) :
    curryLeftCLM y α = α.curryLeft y :=
  rfl

private theorem norm_curryLeftCLM_le (y : E) :
    ‖(curryLeftCLM y : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)‖ ≤ ‖y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun α ↦ by
    rw [curryLeftCLM_apply, mul_comm]
    exact (α.curryLeft.le_opNorm y).trans_eq (by rw [norm_curryLeft])

private theorem continuous_homotopyShift (r : ℝ) :
    Continuous fun q : closedBall (0 : E) r × unitInterval ↦ (q.2 : ℝ) • (q.1 : E) :=
  (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)

variable [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (ρ : ContDiffBump (0 : E))

/-- The Haar measure on the closed ball carrying the bump is finite. -/
private theorem isFiniteMeasure_comap_closedBall (r : ℝ) :
    IsFiniteMeasure (μ.comap ((↑) : closedBall (0 : E) r → E)) :=
  ⟨by rw [comap_subtype_coe_apply measurableSet_closedBall, image_univ, Subtype.range_coe]
      exact measure_closedBall_lt_top⟩

attribute [local instance] isFiniteMeasure_comap_closedBall

/-- The normalized bump vanishes off the closed ball of radius `rOut`. -/
private theorem normed_eq_zero_of_notMem {y : E} (hy : y ∉ closedBall (0 : E) ρ.rOut) :
    ρ.normed μ y = 0 :=
  notMem_support.1 fun h ↦ hy (ball_subset_closedBall (ρ.support_normed_eq (μ := μ) ▸ h))

/-- Integrals against the normalized bump over its closed ball are integrals over `E`. -/
private theorem integral_closedBall_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : E → G) :
    ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y • g y ∂(μ.comap (↑)) =
      ∫ y, ρ.normed μ y • g y ∂μ := by
  rw [integral_subtype_comap measurableSet_closedBall (fun y ↦ ρ.normed μ y • g y)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
    rw [normed_eq_zero_of_notMem μ ρ hy, zero_smul]

/-- The normalized bump has integral one over its closed ball. -/
private theorem integral_closedBall_normed :
    ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y ∂(μ.comap (↑)) = 1 := by
  have h := integral_closedBall_eq μ ρ (fun _ ↦ (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [h, ρ.integral_normed]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The weights of the mollification. -/
private theorem continuous_mollifyWeight :
    Continuous fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y • ContinuousLinearMap.id ℝ F :=
  (ρ.continuous_normed.comp continuous_subtype_val).smul continuous_const

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The weights of the averaged homotopy operator. -/
private theorem continuous_homotopyWeight :
    Continuous fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦
      (curryLeftCLM (ρ.normed μ q.1 • (q.1 : E)) : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) :=
  curryLeftCLM.continuous.comp ((ρ.continuous_normed.comp
    (continuous_subtype_val.comp continuous_fst)).smul (continuous_subtype_val.comp continuous_fst))

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
  postcompCLM (curryLeftCLM y)
    (pullbackCLM _ (contDiffOn_lineHomotopy_slice y t) (isCompact_lineHomotopy_slice y t) ω)

omit [FiniteDimensional ℝ F] in
private theorem lineHomotopyIntegrand_apply (y : E) (t : ℝ)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) (x : E) :
    lineHomotopyIntegrand y t ω x = curryLeftCLM y (ω (x + t • y)) := by
  rw [postcompCLM_apply, Function.comp_apply, pullbackCLM_lineHomotopy_apply]

variable [FiniteDimensional ℝ E]

/-- A continuous linear map passes under the straight-line homotopy operator. -/
private theorem apply_lineHomotopyCLM (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
    (y : E) (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    S (lineHomotopyCLM y ω) = ∫ t : unitInterval, S (lineHomotopyIntegrand y t ω) := by
  refine S.apply_eq_integral_of_apply_eq_apply_add (L := fun _ : unitInterval ↦ curryLeftCLM y)
    (v := fun t ↦ (t : ℝ) • y) continuous_const
    (continuous_subtype_val.smul continuous_const) ω (fun t x ↦ lineHomotopyIntegrand_apply y t ω x)
    fun x ↦ ?_
  rw [lineHomotopyCLM_apply, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, unitInterval.volume_def,
    ← integral_subtype_comap measurableSet_Icc]
  simp only [lineHomotopyIntegrand_apply, curryLeftCLM_apply]

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

attribute [local instance] isFiniteMeasure_comap_closedBall

/-- **Mollification** of test functions on `E` by the normalized bump `ρ̂ = ρ.normed μ`:
`(M φ) x = ∫ ρ̂ y φ (x + y) dμ(y)`, which is the convolution `ρ̂ ⋆ φ`, see
`TestFunction.mollifyCLM_apply`. Precomposing a current with it mollifies the current. -/
def mollifyCLM : 𝓓((⊤ : Opens E), F) →L[ℝ] 𝓓((⊤ : Opens E), F) :=
  translateAverageCLM (μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E))
    (continuous_mollifyWeight μ ρ) continuous_subtype_val

/-- Mollification is convolution with the normalized bump. -/
theorem mollifyCLM_apply (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    mollifyCLM μ ρ φ x = (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ) x := by
  rw [mollifyCLM, translateAverageCLM_apply]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
  rw [integral_closedBall_eq μ ρ (fun y ↦ φ (x + y)), convolution_def,
    ← integral_neg_eq_self]
  simp [ρ.normed_neg, sub_eq_add_neg]

/-- On the whole space, mollification agrees with `TestFunction.mollify`. -/
theorem mollifyCLM_eq_mollify (φ : 𝓓((⊤ : Opens E), F)) :
    mollifyCLM μ ρ φ = mollify φ μ ρ (subset_univ _) := by
  ext x
  rw [mollifyCLM_apply, mollify_apply]

/-- A bound `C` on the values of `φ` bounds its mollification. -/
theorem norm_mollifyCLM_apply_le (φ : 𝓓((⊤ : Opens E), F)) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C)
    (x : E) : ‖mollifyCLM μ ρ φ x‖ ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine (norm_translateAverageCLM_apply_le φ hC x).trans ?_
  calc (∫ y : closedBall (0 : E) ρ.rOut, ‖ρ.normed μ y • ContinuousLinearMap.id ℝ F‖ ∂_) * C
      ≤ (∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y ∂(μ.comap (↑))) * C := by
        refine mul_le_mul_of_nonneg_right (integral_mono_of_nonneg
          (ae_of_all _ fun _ ↦ norm_nonneg _) ((ρ.continuous_normed.comp continuous_subtype_val)
            |>.integrable_of_hasCompactSupport (.of_compactSpace _)) (ae_of_all _ fun y ↦ ?_)) hC0
        dsimp only
        rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _)]
        exact mul_le_of_le_one_right (ρ.nonneg_normed _) ContinuousLinearMap.norm_id_le
    _ = C := by rw [integral_closedBall_normed, one_mul]

/-- As the bumps shrink, the mollifications of a test function converge to it in the LF
topology. -/
theorem tendsto_mollifyCLM {ι : Type*} {l : Filter ι} [CompleteSpace F]
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), F)) : Tendsto (fun i ↦ mollifyCLM μ (ρ i) φ) l (𝓝 φ) := by
  simp only [mollifyCLM_eq_mollify]
  exact tendsto_mollify φ μ hρ fun _ ↦ subset_univ _

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
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, curryLeftCLM_apply]

/-- **Sup bound for the averaged homotopy operator**: `‖K ω‖ ≤ r ‖ω‖`, with `r = ρ.rOut`. -/
theorem norm_mollifyHomotopyCLM_apply_le (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F))
    {C : ℝ} (hC : ∀ y, ‖ω y‖ ≤ C) (x : E) : ‖mollifyHomotopyCLM μ ρ ω x‖ ≤ ρ.rOut * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine (norm_translateAverageCLM_apply_le ω hC x).trans (mul_le_mul_of_nonneg_right ?_ hC0)
  have hw : Continuous fun q : closedBall (0 : E) ρ.rOut × unitInterval ↦ ρ.normed μ q.1 :=
    ρ.continuous_normed.comp (continuous_subtype_val.comp continuous_fst)
  calc ∫ q : closedBall (0 : E) ρ.rOut × unitInterval,
        ‖(curryLeftCLM (ρ.normed μ q.1 • (q.1 : E)) : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)‖ ∂_
      ≤ ∫ q : closedBall (0 : E) ρ.rOut × unitInterval, ρ.rOut * ρ.normed μ q.1
          ∂((μ.comap (↑)).prod volume) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
          ((hw.const_mul _).integrable_of_hasCompactSupport (.of_compactSpace _))
          (ae_of_all _ fun q ↦ ?_)
        dsimp only
        refine (norm_curryLeftCLM_le _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg_normed _), mul_comm]
        exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 q.1.2) (ρ.nonneg_normed _)
    _ = ρ.rOut := by
        rw [integral_const_mul, integral_prod _
          (hw.integrable_of_hasCompactSupport (.of_compactSpace _))]
        simp [integral_closedBall_normed]

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
      simp [lineHomotopyIntegrand_apply, curryLeftCLM_apply, map_smul])

/-- **A current passes under the averaged homotopy operator**, as the average of the
straight-line homotopy currents: `S (K ω) = ∫ ρ̂ y S (h_y ω) dμ(y)`, and the integrand is
integrable. -/
private theorem apply_mollifyHomotopyCLM (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
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
      simp [lineHomotopyIntegrand_apply, curryLeftCLM_apply, map_smul], integral_prod _ hint]
  exact integral_congr_ae (ae_of_all _ hinner)

/-- **A current passes under mollification**, as the average of its translates:
`S (M ω) = ∫ ρ̂ y S (ω (· + y)) dμ(y)`, and the integrand is integrable. -/
private theorem apply_mollifyCLM (S : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F)) :
    Integrable (fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y •
      S (pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
        (isCompact_lineHomotopy_slice (y : E) 1) ω)) (μ.comap (↑)) ∧
    S (mollifyCLM μ ρ ω) = ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y •
      S (pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
        (isCompact_lineHomotopy_slice (y : E) 1) ω) ∂(μ.comap (↑)) := by
  have hf (y : closedBall (0 : E) ρ.rOut) (x : E) :
      (ρ.normed μ y • pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
        (isCompact_lineHomotopy_slice (y : E) 1) ω) x =
        (ρ.normed μ y • ContinuousLinearMap.id ℝ _) (ω (x + y)) := by
    rw [FunLike.coe_smul, Pi.smul_apply, pullbackCLM_lineHomotopy_apply, one_smul]
    simp
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, map_smul] using (S.continuous.comp
      (continuous_of_apply_eq_apply_add (continuous_mollifyWeight μ ρ) continuous_subtype_val ω
        hf)).integrable_of_hasCompactSupport
      (μ := μ.comap ((↑) : closedBall (0 : E) ρ.rOut → E)) (.of_compactSpace _)
  · rw [mollifyCLM, S.apply_translateAverageCLM ω hf]
    simp only [map_smul]

/-- Mollification commutes with the boundary of currents with finite-dimensional coefficients. -/
private theorem apply_mollifyCLM_extDerivCLM
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F)) :
    S (mollifyCLM μ ρ (extDerivCLM ω)) = S (extDerivCLM (mollifyCLM μ ρ ω)) := by
  rw [(apply_mollifyCLM μ ρ S _).2, ← ContinuousLinearMap.comp_apply S extDerivCLM,
    (apply_mollifyCLM μ ρ (S ∘L extDerivCLM) ω).2]
  simp only [ContinuousLinearMap.comp_apply, extDerivCLM_pullbackCLM]

/-- The homotopy formula for the averaged homotopy operator, tested against a current. -/
private theorem apply_mollifyHomotopyCLM_extDerivCLM
    (S : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓((⊤ : Opens E), E [⋀^Fin (m + 1)]→L[ℝ] F)) :
    S (mollifyHomotopyCLM μ ρ (extDerivCLM ω)) =
      S (mollifyCLM μ ρ ω) - S ω - S (extDerivCLM (mollifyHomotopyCLM μ ρ ω)) := by
  have hy (y : closedBall (0 : E) ρ.rOut) :
      S (lineHomotopyCLM (y : E) (extDerivCLM ω)) =
        S (pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
          (isCompact_lineHomotopy_slice (y : E) 1) ω) - S ω -
          (S ∘L extDerivCLM) (lineHomotopyCLM (y : E) ω) := by
    have h := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM
      (hH := contDiffAt_lineHomotopy (y : E)) (hHp := isCompact_lineHomotopy (y : E)) S) ω)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      pullbackCLM_lineHomotopy_zero] at h
    exact h
  obtain ⟨hM, hMe⟩ := apply_mollifyCLM μ ρ S ω
  obtain ⟨hK, hKe⟩ := apply_mollifyHomotopyCLM μ ρ (S ∘L extDerivCLM) ω
  have hc : Integrable (fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y • S ω) (μ.comap (↑)) :=
    ((ρ.continuous_normed.comp continuous_subtype_val).smul continuous_const)
      |>.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hSω : S ω = ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y • S ω ∂(μ.comap (↑)) := by
    rw [integral_smul_const, integral_closedBall_normed, one_smul]
  rw [(apply_mollifyHomotopyCLM μ ρ S _).2, hMe, ← ContinuousLinearMap.comp_apply S extDerivCLM,
    hKe, hSω, ← integral_sub hM hc]
  rw [← integral_sub (f := fun y : closedBall (0 : E) ρ.rOut ↦
      ρ.normed μ y • S (pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
        (isCompact_lineHomotopy_slice (y : E) 1) ω) - ρ.normed μ y • S ω) (hM.sub hc) hK]
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
        S (pullbackCLM _ (contDiffOn_lineHomotopy_slice (y : E) 1)
          (isCompact_lineHomotopy_slice (y : E) 1) ω) - S ω := by
    have h := congr($(ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM_finZero
      (hH := contDiffAt_lineHomotopy (y : E)) (hHp := isCompact_lineHomotopy (y : E)) S) ω)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      pullbackCLM_lineHomotopy_zero] at h
    exact h
  obtain ⟨hM, hMe⟩ := apply_mollifyCLM μ ρ S ω
  have hc : Integrable (fun y : closedBall (0 : E) ρ.rOut ↦ ρ.normed μ y • S ω) (μ.comap (↑)) :=
    ((ρ.continuous_normed.comp continuous_subtype_val).smul continuous_const)
      |>.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hSω : S ω = ∫ y : closedBall (0 : E) ρ.rOut, ρ.normed μ y • S ω ∂(μ.comap (↑)) := by
    rw [integral_smul_const, integral_closedBall_normed, one_smul]
  rw [(apply_mollifyHomotopyCLM μ ρ S _).2, hMe, hSω, ← integral_sub hM hc]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [hy, smul_sub]

end Identities

section FormIdentities

variable [FiniteDimensional ℝ F] {m : ℕ}

/-- **Mollification commutes with the exterior derivative**: `d ∘ M = M ∘ d`. -/
theorem extDerivCLM_comp_mollifyCLM :
    (extDerivCLM ∘L mollifyCLM μ ρ : 𝓓((⊤ : Opens E), E [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      mollifyCLM μ ρ ∘L extDerivCLM := by
  ext ω x : 2
  exact (apply_mollifyCLM_extDerivCLM μ ρ
    (BoundedContinuousFunction.evalCLM ℝ x ∘L toBoundedContinuousFunctionCLM ℝ) ω).symm

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

namespace ContinuousLinearMap

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ}

/-- **Mollified currents converge on every test form**: as the bumps shrink,
`T (M φ) → T φ`. -/
theorem tendsto_comp_mollifyCLM [CompleteSpace F] (T : 𝓓((⊤ : Opens E), F) →L[ℝ] V)
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) (φ : 𝓓((⊤ : Opens E), F)) :
    Tendsto (fun i ↦ T (mollifyCLM μ (ρ i) φ)) l (𝓝 (T φ)) :=
  (T.continuous.tendsto φ).comp (tendsto_mollifyCLM μ hρ φ)

variable (ρ : ContDiffBump (0 : E)) [FiniteDimensional ℝ F]

/-- **The boundary of a mollified current** is the mollified boundary: `∂(T ∘ M) = (∂T) ∘ M`. -/
theorem comp_mollifyCLM_comp_extDerivCLM
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    (T ∘L mollifyCLM μ ρ) ∘L extDerivCLM = (T ∘L extDerivCLM) ∘L mollifyCLM μ ρ := by
  rw [ContinuousLinearMap.comp_assoc, ← extDerivCLM_comp_mollifyCLM,
    ContinuousLinearMap.comp_assoc]

end ContinuousLinearMap

namespace Distribution

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E)) {k : ℕ}

/-- **Mollification does not increase mass**: `M(T ∘ M) ≤ M(T)`. -/
theorem mass_comp_mollifyCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓((⊤ : Opens E), F) V]
    [LinearMapClass 𝓕 ℝ 𝓓((⊤ : Opens E), F) V] (T : 𝓕) :
    mass (T ∘ mollifyCLM μ ρ) ≤ mass T := by
  simpa using mass_comp_le_of_norm_apply_le T zero_le_one fun φ hφ x ↦
    norm_mollifyCLM_apply_le μ ρ φ hφ x

/-- **Mass of the averaged homotopy current**: `M(T ∘ K) ≤ r M(T)` for a `k`-current `T`, with
`r = ρ.rOut`. -/
theorem mass_comp_mollifyHomotopyCLM_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) :
    mass (T ∘ mollifyHomotopyCLM μ ρ) ≤ ENNReal.ofReal ρ.rOut * mass T :=
  mass_comp_le_of_norm_apply_le T ρ.rOut_pos.le fun φ hφ x ↦ by
    simpa using norm_mollifyHomotopyCLM_apply_le μ ρ φ hφ x

variable [FiniteDimensional ℝ F]

/-- **Mollification preserves normal currents.** -/
theorem IsNormal.comp_mollifyCLM {T : 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) : IsNormal (T ∘L mollifyCLM μ ρ) := by
  cases k with
  | zero =>
    rw [isNormal_finZero_iff] at hT ⊢
    exact ne_top_of_le_ne_top hT (mass_comp_mollifyCLM_le μ ρ T)
  | succ k =>
    rw [isNormal_succ_iff] at hT ⊢
    rw [ContinuousLinearMap.comp_mollifyCLM_comp_extDerivCLM]
    exact ⟨ne_top_of_le_ne_top hT.1 (mass_comp_mollifyCLM_le μ ρ T),
      ne_top_of_le_ne_top hT.2 (mass_comp_mollifyCLM_le μ ρ (T ∘L extDerivCLM))⟩

end Distribution

namespace ContinuousLinearMap

open TestFunction Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (ρ : ContDiffBump (0 : E)) {k : ℕ}

/-- **The flat estimate for mollification**: for a current `T` of positive degree,
`F(T - T ∘ M) ≤ r (M(T) + M(∂T))`, where `F` is the real normal flat mass and `r = ρ.rOut`. The
decomposition is `T - T ∘ M = -(∂T ∘ K) + ∂(-(T ∘ K))` for the averaged homotopy operator `K`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤
      ENNReal.ofReal ρ.rOut * (mass T + mass (T ∘L extDerivCLM)) := by
  have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
  by_cases hT : mass T = ⊤ ∨ mass (T ∘L extDerivCLM) = ⊤
  · rcases hT with h | h <;> simp [h, hr]
  push Not at hT
  set S := -(T ∘L mollifyHomotopyCLM μ ρ) with hS
  set R := -((T ∘L extDerivCLM) ∘L mollifyHomotopyCLM μ ρ) with hR
  have hSd : S ∘L extDerivCLM = T - T ∘L mollifyCLM μ ρ - R := by
    rw [hS, hR, neg_comp, comp_assoc, mollifyHomotopyCLM_comp_extDerivCLM, comp_sub, comp_sub,
      comp_id, comp_assoc]
    abel
  have hmS : mass S ≤ ENNReal.ofReal ρ.rOut * mass T := by
    rw [hS, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ T
  have hmR : mass R ≤ ENNReal.ofReal ρ.rOut * mass (T ∘L extDerivCLM) := by
    rw [hR, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ (T ∘L extDerivCLM)
  have hmS' : mass S ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.1) hmS
  have hmR' : mass R ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.2) hmR
  have hmM : mass (T ∘L mollifyCLM μ ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top hT.1 (mass_comp_mollifyCLM_le μ ρ T)
  have hnS : IsNormal S := by
    refine isNormal_succ_iff.2 ⟨hmS', ?_⟩
    rw [hSd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hT.1, hmM⟩, hmR'⟩)
      (mass_sub_le.trans (add_le_add mass_sub_le le_rfl))
  have hnR : IsNormal R := by
    refine isNormal_succ_iff.2 ⟨hmR', ?_⟩
    have hRd : R ∘L extDerivCLM =
        T ∘L extDerivCLM - (T ∘L extDerivCLM) ∘L mollifyCLM μ ρ := by
      have h := congr($hSd ∘L extDerivCLM)
      rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero, sub_comp, sub_comp,
        comp_mollifyCLM_comp_extDerivCLM] at h
      exact (sub_eq_zero.1 h.symm).symm
    rw [hRd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT.2, hT.2⟩)
      (mass_sub_le.trans (add_le_add le_rfl (mass_comp_mollifyCLM_le μ ρ (T ∘L extDerivCLM))))
  calc (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤ mass R + mass S :=
        normalFlatMass_le_of_eq_add_comp_extDerivCLM _ hnR hnS (by rw [hSd]; abel)
    _ ≤ ENNReal.ofReal ρ.rOut * mass (T ∘L extDerivCLM) + ENNReal.ofReal ρ.rOut * mass T :=
        add_le_add hmR hmS
    _ = ENNReal.ofReal ρ.rOut * (mass T + mass (T ∘L extDerivCLM)) := by ring

/-- **The flat estimate for mollification in degree zero**: `F(T - T ∘ M) ≤ r M(T)`, where `F` is
the real normal flat mass and `r = ρ.rOut`. The decomposition is `T - T ∘ M = ∂(-(T ∘ K))` for
the averaged homotopy operator `K`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le_finZero
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤ ENNReal.ofReal ρ.rOut * mass T := by
  have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
  by_cases hT : mass T = ⊤
  · simp [hT, hr]
  set S := -(T ∘L mollifyHomotopyCLM μ ρ) with hS
  have hSd : S ∘L extDerivCLM = T - T ∘L mollifyCLM μ ρ := by
    rw [hS, neg_comp, comp_assoc, mollifyHomotopyCLM_comp_extDerivCLM_finZero, comp_sub, comp_id]
    abel
  have hmS : mass S ≤ ENNReal.ofReal ρ.rOut * mass T := by
    rw [hS, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ T
  have hnS : IsNormal S := by
    refine isNormal_succ_iff.2
      ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hmS, ?_⟩
    rw [hSd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT, hT⟩)
      (mass_sub_le.trans (add_le_add le_rfl (mass_comp_mollifyCLM_le μ ρ T)))
  calc (T - T ∘L mollifyCLM μ ρ).normalFlatMass
      ≤ mass (0 : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) + mass S :=
        normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hnS (by rw [hSd, zero_add])
    _ ≤ ENNReal.ofReal ρ.rOut * mass T := by simpa using hmS

end ContinuousLinearMap
