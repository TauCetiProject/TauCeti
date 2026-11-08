/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Rescaling Floer solutions at a bubbling point

Bubbling analysis for the inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` blows a sequence of
solutions up at points where their derivatives concentrate. For a centre `c` and a scale `ε`, the
rescaled map `v(w) = u(c + ε w)` is the reparametrization of `u` along the affine change of
coordinates `w ↦ c + ε w`, whose derivative is `ε` times the identity and so is complex linear.
Hence (`TauCeti.Floer.perturbationPullback`) the rescaled map solves the Floer equation for the
rescaled perturbation `ε K(c + ε w)` and the almost complex structure `J(c + ε w, ·)`:

* the pullback of `K` along `w ↦ c + ε w` is the rescaled perturbation `ε K(c + ε w)`
  (`Floer.perturbationPullback_const_add_smul_stdComplexLineReal` and its `dt` analogue);
* the perturbed derivative of `v` is `ε` times that of `u` at `c + ε w`
  (`SymplecticForm.perturbedFDeriv_rescale`), so for `ε ≠ 0` the map `v` solves the rescaled
  equation exactly when `u` solves the original one
  (`SymplecticForm.isComplexLinearMap_perturbedFDeriv_rescale_iff`);
* the energy density and the curvature of the rescaled data are `ε²` times those of the original
  data (`SymplecticForm.floerEnergyDensity_rescale`, `SymplecticForm.hamiltonianCurvature_rescale`).

As the scale tends to zero the rescaled perturbation tends to zero and the rescaled structure
freezes at the limit `z₀` of the centres. So a limit of rescaled solutions is pseudoholomorphic for
the structure `J(z₀, ·)` frozen at the bubbling point, not for a structure at any other domain
point (`SymplecticForm.isComplexLinearMap_of_tendsto_rescale`). This needs only pointwise
convergence of the rescaled maps and their derivatives, together with continuity of `J` and of the
Hamiltonian vector fields of `K` at the limit point. Under the `C¹` convergence on compact sets
produced by compactness arguments, the limit is `J(z₀, ·)`-holomorphic on the whole open set of
convergence (`SymplecticForm.isJHolomorphicAt_of_tendstoLocallyUniformlyOn_rescale`).

The symplectic area of such a limit is bounded by the energy concentrating at `z₀`: for every
`δ > 0`, the integral over the whole plane of the area density `ω(∂_s v, ∂_t v)` is at most the
lower limit of the Floer energies of the original maps over the disc of radius `δ` about `z₀`
(`SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`). This is Fatou's lemma
after the change of variables `z = c + ε w`, and needs no equation; it is the energy accounting
that bounds the energy of a bubble by the energy lost at its bubbling point.

Choosing the centres and scales, for instance by Hofer's lemma (`hofer` in Mathlib), and the
removal of the singularity at infinity of the limit plane are not carried out here.

## Main results

* `SymplecticForm.perturbedFDeriv_rescale`: the perturbed derivative of a rescaled map.
* `SymplecticForm.isComplexLinearMap_perturbedFDeriv_rescale_iff`: rescaled solutions solve the
  rescaled Floer equation.
* `SymplecticForm.isComplexLinearMap_of_tendsto_rescale`: limits of rescaled solutions solve the
  Cauchy–Riemann equation for the frozen structure, pointwise.
* `SymplecticForm.isJHolomorphicAt_of_tendstoLocallyUniformlyOn_rescale`: the same on an open set,
  under locally uniform convergence of the derivatives.
* `SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`: the area of a limit of
  rescaled maps is at most the energy concentrating at the bubbling point.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.2
  (rescaling at a point where the derivatives blow up), Section 4.6 (bubbling) and Section 8.1
  (inhomogeneous equations and bubbles for the frozen structure).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

namespace Floer

variable {X : Type*} {c : ℝ × ℝ} {ε : ℝ}

/-- The `ds` component of the pullback of a perturbation along the rescaling `w ↦ c + ε w` is
`ε K_s(c + ε w)`. -/
@[simp]
theorem perturbationPullback_const_add_smul_stdComplexLineReal (Ks Kt : ℝ × ℝ → X → ℝ) :
    perturbationPullback (fun w ↦ c + ε • w) Ks Kt stdComplexLineReal =
      fun w x ↦ ε * Ks (c + ε • w) x := by
  funext w x
  simp [perturbationPullback_apply, fderiv_fun_const_smul differentiableAt_fun_id,
    stdComplexLineReal_eq]

/-- The `dt` component of the pullback of a perturbation along the rescaling `w ↦ c + ε w` is
`ε K_t(c + ε w)`. -/
@[simp]
theorem perturbationPullback_const_add_smul_stdComplexLineImag (Ks Kt : ℝ × ℝ → X → ℝ) :
    perturbationPullback (fun w ↦ c + ε • w) Ks Kt stdComplexLineImag =
      fun w x ↦ ε * Kt (c + ε • w) x := by
  funext w x
  simp [perturbationPullback_apply, fderiv_fun_const_smul differentiableAt_fun_id,
    stdComplexLineImag_eq]

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ}

section Pointwise

variable {u : ℝ × ℝ → V} {c w : ℝ × ℝ} {ε : ℝ}

/-- **The perturbed derivative of a rescaled map.** The perturbed derivative of
`v(w) = u(c + ε w)` for the rescaled perturbation `ε K(c + ε w)` is `ε` times the perturbed
derivative of `u` for `K` at `c + ε w`. -/
theorem perturbedFDeriv_rescale (ω : SymplecticForm V) :
    ω.perturbedFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w =
      ε • ω.perturbedFDeriv Ks Kt u (c + ε • w) := by
  -- Unlike `SymplecticForm.perturbedFDeriv_perturbationPullback`, this needs no differentiability:
  -- the chain rule for affine reparametrizations and the homogeneity `X_{ε H} = ε X_H` hold for
  -- arbitrary maps and Hamiltonians.
  have hd : fderiv ℝ (fun w ↦ u (c + ε • w)) w = ε • fderiv ℝ u (c + ε • w) := by
    rw [fderiv_comp_smul (f := fun y ↦ u (c + y)), fderiv_comp_add_left]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp [perturbedFDeriv_apply, hd, smul_sub, smul_comm ε]

/-- **Rescaled solutions.** For a nonzero scale `ε`, the rescaled map `w ↦ u(c + ε w)` solves the
Floer equation for the rescaled perturbation `ε K(c + ε w)` at `w`, with respect to a structure
`J`, exactly when `u` solves the Floer equation for `K` at `c + ε w` with respect to `J`. -/
theorem isComplexLinearMap_perturbedFDeriv_rescale_iff (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hε : ε ≠ 0) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
          (fun w ↦ u (c + ε • w)) w : ℝ × ℝ →ₗ[ℝ] V) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv Ks Kt u (c + ε • w) : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [ω.perturbedFDeriv_rescale, isComplexLinearMap_stdComplexLine_iff,
    isComplexLinearMap_stdComplexLine_iff]
  simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, map_smul]
  exact smul_right_injective V hε |>.eq_iff

/-- **The energy density of a rescaled map.** The Floer energy density of `w ↦ u(c + ε w)` for the
rescaled perturbation `ε K(c + ε w)` is `ε²` times the energy density of `u` at `c + ε w`. -/
theorem floerEnergyDensity_rescale (ω : SymplecticForm V) :
    ω.floerEnergyDensity (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w =
      ε ^ 2 * ω.floerEnergyDensity Ks Kt u (c + ε • w) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, ω.perturbedFDeriv_rescale]
  simp [sq, mul_assoc]

/-- **The curvature of rescaled data.** The curvature of the rescaled perturbation
`ε K(c + ε w)` is `ε²` times the curvature of `K` at `c + ε w`. -/
theorem hamiltonianCurvature_rescale (ω : SymplecticForm V) {x : V} :
    ω.hamiltonianCurvature (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x) w x =
      ε ^ 2 * ω.hamiltonianCurvature Ks Kt (c + ε • w) x := by
  -- As for `SymplecticForm.perturbedFDeriv_rescale`, this needs no differentiability: the chain
  -- rule for affine reparametrizations and the homogeneity of derivatives and Poisson brackets
  -- under constant multiples hold for arbitrary functions.
  have hd (K : ℝ × ℝ → V → ℝ) : fderiv ℝ (fun w ↦ ε * K (c + ε • w) x) w =
      ε • ε • fderiv ℝ (fun z ↦ K z x) (c + ε • w) := by
    -- The function `w ↦ ε * K (c + ε • w) x` is the scalar multiple `ε • (w ↦ K (c + ε • w) x)`.
    refine (congrFun (fderiv_const_smul_field (f := fun w ↦ K (c + ε • w) x) ε) w).trans ?_
    rw [Pi.smul_apply, fderiv_comp_smul (f := fun y ↦ K (c + y) x),
      fderiv_comp_add_left (f := fun z ↦ K z x)]
  simp only [hamiltonianCurvature_def, hd, poissonBracket_const_mul_left,
    poissonBracket_const_mul_right, smul_apply, smul_eq_mul]
  ring

end Pointwise

section Limit

variable {ι : Type*} {l : Filter ι} {u : ι → ℝ × ℝ → V} {c : ι → ℝ × ℝ} {ε : ι → ℝ}
  {z₀ : ℝ × ℝ}

/-- The perturbation terms `ε i • X_K(c i + ε i • w, x i)` of the rescaled equation tend to zero
along points `(c i + ε i • w, x i)` converging to a point where `X_K` is continuous. -/
private theorem tendsto_smul_hamiltonianVectorField (ω : SymplecticForm V) {K : ℝ × ℝ → V → ℝ}
    {x : ι → V} {x₀ : V} (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0)) {w : ℝ × ℝ}
    (hx : Tendsto x l (𝓝 x₀))
    (hX : ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (K z)) (z₀, x₀)) :
    Tendsto (fun i ↦ ε i • ω.hamiltonianVectorField (K (c i + ε i • w)) (x i)) l (𝓝 0) := by
  have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by simpa using hc.add (hε.smul_const w)
  simpa using hε.smul (hX.tendsto.comp (hz.prodMk_nhds hx))

/-- The rescaled perturbed derivatives `ε i • (du - X_K)` of maps `u i` at the points
`c i + ε i • w` converge to the limit `L` of the derivatives of the rescaled maps, when the
Hamiltonian vector fields of `K` are continuous at the limit point: the Hamiltonian terms carry a
factor `ε i → 0`. -/
private theorem tendsto_smul_perturbedFDeriv_rescale (ω : SymplecticForm V) {w : ℝ × ℝ} {x₀ : V}
    {L : ℝ × ℝ →L[ℝ] V} (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hx : Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 x₀))
    (hL : Tendsto (fun i ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) l (𝓝 L))
    (hXs : ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Ks z)) (z₀, x₀))
    (hXt : ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Kt z)) (z₀, x₀))
    (v : ℝ × ℝ) :
    Tendsto (fun i ↦ ε i • ω.perturbedFDeriv Ks Kt (u i) (c i + ε i • w) v) l (𝓝 (L v)) := by
  have h := ((hL.eval_const v).sub
    ((ω.tendsto_smul_hamiltonianVectorField hc hε (w := w) hx hXs).const_smul v.1)).sub
    ((ω.tendsto_smul_hamiltonianVectorField hc hε (w := w) hx hXt).const_smul v.2)
  rw [smul_zero, smul_zero, sub_zero, sub_zero] at h
  refine h.congr fun i ↦ ?_
  rw [← smul_apply, ← ω.perturbedFDeriv_rescale]
  simp [perturbedFDeriv_apply]

/-- **Bubbles are holomorphic for the frozen structure.** Let `u i` solve the Floer equation
`(du - X_K)^{0,1} = 0` for a domain-dependent structure `J(z, x)` at the points `c i + ε i • w`,
where the centres `c i` tend to `z₀` and the scales `ε i` tend to `0`. If the rescaled maps
`w' ↦ u i (c i + ε i • w')` converge at `w` to `x₀` and their derivatives at `w` converge to `L`,
and if `J` and the Hamiltonian vector fields of `K` are continuous at `(z₀, x₀)`, then `L` is
complex linear for the structure `J(z₀, x₀)` frozen at the bubbling point `z₀`. -/
theorem isComplexLinearMap_of_tendsto_rescale (ω : SymplecticForm V) [l.NeBot]
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {w : ℝ × ℝ} {x₀ : V} {L : ℝ × ℝ →L[ℝ] V}
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hx : Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 x₀))
    (hL : Tendsto (fun i ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) l (𝓝 L))
    (hJ : ContinuousAt (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (z₀, x₀))
    (hXs : ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Ks z)) (z₀, x₀))
    (hXt : ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Kt z)) (z₀, x₀))
    (hsol : ∀ᶠ i in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (c i + ε i • w) (u i (c i + ε i • w)))
      (ω.perturbedFDeriv Ks Kt (u i) (c i + ε i • w) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z₀ x₀) (L : ℝ × ℝ →ₗ[ℝ] V) := by
  -- The rescaled perturbed derivative `ε i • P i` converges to `L`.
  have hP := ω.tendsto_smul_perturbedFDeriv_rescale hc hε hx hL hXs hXt
  -- The structures along the sequence converge to the frozen structure `J(z₀, x₀)`.
  have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by simpa using hc.add (hε.smul_const w)
  have hJ' : Tendsto
      (fun i ↦ (J (c i + ε i • w) (u i (c i + ε i • w))).toLinearMap.toContinuousLinearMap) l
      (𝓝 (J z₀ x₀).toLinearMap.toContinuousLinearMap) :=
    hJ.tendsto.comp (hz.prodMk_nhds hx)
  -- Pass to the limit in `ε i • P i (0, 1) = J_i (ε i • P i (1, 0))`.
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe]
  refine tendsto_nhds_unique (hP stdComplexLineImag) ?_
  have h := (isBoundedBilinearMap_apply.continuous.tendsto _).comp
    (hJ'.prodMk_nhds (hP stdComplexLineReal))
  simp only [comp_def, LinearMap.coe_toContinuousLinearMap'] at h
  refine h.congr' (hsol.mono fun i hi ↦ ?_)
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe] at hi
  rw [map_smul, ← hi]

/-- **Bubbles are holomorphic for the frozen structure, on an open set.** Let `u i` solve the Floer
equation on the rescaled images `c i + ε i • Ω` of an open set `Ω`, with centres `c i → z₀` and
scales `ε i → 0`. If the rescaled maps converge pointwise on `Ω` to `v`, and their derivatives
converge locally uniformly on `Ω`, and if `J` and the Hamiltonian vector fields of `K` are
continuous at the points `(z₀, v w)`, then `v` is holomorphic on `Ω` for the structure `J(z₀, ·)`
frozen at the bubbling point. -/
theorem isJHolomorphicAt_of_tendstoLocallyUniformlyOn_rescale (ω : SymplecticForm V) [l.NeBot]
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ω : Set (ℝ × ℝ)} {v : ℝ × ℝ → V}
    {L : ℝ × ℝ → ℝ × ℝ →L[ℝ] V} (hΩ : IsOpen Ω)
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hv : ∀ w ∈ Ω, Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 (v w)))
    (hL : TendstoLocallyUniformlyOn (fun i w ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) L l Ω)
    (hJ : ∀ w ∈ Ω, ContinuousAt
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z₀, v w))
    (hXs : ∀ w ∈ Ω,
      ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Ks z)) (z₀, v w))
    (hXt : ∀ w ∈ Ω,
      ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (Kt z)) (z₀, v w))
    (hu : ∀ i, ∀ w ∈ Ω, DifferentiableAt ℝ (u i) (c i + ε i • w))
    (hsol : ∀ᶠ i in l, ∀ w ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (c i + ε i • w) (u i (c i + ε i • w)))
      (ω.perturbedFDeriv Ks Kt (u i) (c i + ε i • w) : ℝ × ℝ →ₗ[ℝ] V)) :
    ∀ w ∈ Ω, IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ) (J z₀) v w := by
  intro w hw
  have hvL : HasFDerivAt v (L w) w :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hL (fun i w' hw' ↦ ((hu i w' hw').comp w'
      (((hasFDerivAt_id w').const_smul (ε i)).const_add (c i)).differentiableAt).hasFDerivAt)
      hv hw
  exact isJHolomorphicAt_of_hasFDerivAt hvL <|
    ω.isComplexLinearMap_of_tendsto_rescale hc hε (hv w hw) (hL.tendsto_at hw) (hJ w hw)
      (hXs w hw) (hXt w hw) (hsol.mono fun i hi ↦ hi w hw)

/-- The energy estimate for a disc `B` inside the open set where the maps and the perturbation are
`C¹`; see `SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`. -/
private theorem lintegral_symplecticForm_le_liminf_of_tendsto_rescale_of_subset
    (ω : SymplecticForm V) [l.NeBot] [l.IsCountablyGenerated] {U : Set (ℝ × ℝ)} {v : ℝ × ℝ → V}
    (hU : IsOpen U) (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ)) (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ))
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hv : ∀ w, Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 (v w)))
    (hdv : ∀ w, Tendsto (fun i ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) l (𝓝 (fderiv ℝ v w)))
    {δ : ℝ} (hδ : 0 < δ) (hδU : ball z₀ δ ⊆ U) :
    ∫⁻ w, ENNReal.ofReal (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) ≤
      liminf (fun i ↦ ∫⁻ z in ball z₀ δ, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z))
        l := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set B := ball z₀ δ
  set φ : ι → ℝ × ℝ → ℝ × ℝ := fun i w ↦ c i + ε i • w
  have hφ (i : ι) : Continuous (φ i) := continuous_const.add (continuous_id.const_smul (ε i))
  have hpre (i : ι) : MeasurableSet (φ i ⁻¹' B) := (isOpen_ball.preimage (hφ i)).measurableSet
  -- The rescaled energy densities, cut off outside the preimage of the disc `B`.
  set g : ι → ℝ × ℝ → ENNReal := fun i ↦ (φ i ⁻¹' B).indicator
    fun w ↦ ENNReal.ofReal (ε i ^ 2 * ω.floerEnergyDensity Ks Kt (u i) (φ i w))
  -- Each cut-off density integrates to at most the energy of `u i` over `B`, by the change of
  -- variables `z = c i + ε i • w`, whose Jacobian is `ε i ^ 2`.
  have hint (i : ι) : ∫⁻ w, g i w ≤
      ∫⁻ z in B, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z) := by
    simp only [g, lintegral_indicator (hpre i)]
    rcases eq_or_ne (ε i) 0 with h0 | h0
    · simp [h0]
    have hinj : InjOn (φ i) (φ i ⁻¹' B) := fun a _ b _ hab ↦
      smul_right_injective _ h0 (add_left_cancel hab)
    refine le_trans (le_of_eq ?_) (lintegral_mono_set (image_preimage_subset (φ i) B))
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (f := φ i) (hpre i)
      (fun w _ ↦ (((hasFDerivAt_id w).const_smul (ε i)).const_add (c i)).hasFDerivWithinAt) hinj]
    refine setLIntegral_congr_fun (hpre i) fun w _ ↦ ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    simp only [φ]
    congr 2
    simp [ContinuousLinearMap.det, sq]
  -- Each cut-off density is measurable: the energy density of `u i` is continuous on `U`.
  have hmeas (i : ι) : AEMeasurable (g i) := by
    refine (aemeasurable_indicator_iff (hpre i)).mpr (ContinuousOn.aemeasurable ?_ (hpre i))
    refine ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul ?_)
    exact (ω.continuousOn_floerEnergyDensity hU (hu i) hKs hKt).comp (hφ i).continuousOn
      fun w hw ↦ hδU hw
  -- Pointwise, the cut-off densities converge to the area density of the limit `v`.
  have hlim (w : ℝ × ℝ) : Tendsto (fun i ↦ g i w) l (𝓝 (ENNReal.ofReal
      (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)))) := by
    have hz : Tendsto (φ · w) l (𝓝 z₀) := by simpa [φ] using hc.add (hε.smul_const w)
    have hB : ∀ᶠ i in l, φ i w ∈ B := hz (isOpen_ball.mem_nhds (mem_ball_self hδ))
    have hz₀ : (z₀, v w) ∈ U ×ˢ (univ : Set V) := ⟨hδU (mem_ball_self hδ), mem_univ _⟩
    have hUV := (hU.prod isOpen_univ).mem_nhds hz₀
    have hP := ω.tendsto_smul_perturbedFDeriv_rescale hc hε (hv w) (hdv w)
      ((ω.continuousOn_uncurry_hamiltonianVectorField hKs).continuousAt hUV)
      ((ω.continuousOn_uncurry_hamiltonianVectorField hKt).continuousAt hUV)
    have hω := ((ω.continuous_apply_comp continuous_fst continuous_snd).tendsto _).comp
      ((hP stdComplexLineReal).prodMk_nhds (hP stdComplexLineImag))
    refine (ENNReal.tendsto_ofReal hω).congr' (hB.mono fun i hi ↦ ?_)
    simp only [g, indicator_of_mem (mem_preimage.mpr hi), floerEnergyDensity_def,
      comp_apply, φ, map_smul, LinearMap.smul_apply, smul_eq_mul, sq, mul_assoc]
  -- Fatou's lemma.
  calc ∫⁻ w, ENNReal.ofReal
        (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag))
      = ∫⁻ w, liminf (fun i ↦ g i w) l := lintegral_congr fun w ↦ ((hlim w).liminf_eq).symm
    _ ≤ liminf (fun i ↦ ∫⁻ w, g i w) l := lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall hint)

/-- **The area of a bubble is at most the energy concentrating at its bubbling point.** Let `u i`
be `C¹` on an open set `U` containing `z₀`, and let the perturbation `K` be `C¹` on `U`. Rescale
`u i` at centres `c i → z₀` by scales `ε i → 0`, and suppose that the rescaled maps
`w ↦ u i (c i + ε i • w)` and their derivatives converge at every point of the plane, to a map `v`
and its derivative. Then for every `δ > 0` the symplectic area `∫ ω(∂_s v, ∂_t v)` of `v` over the
whole plane, with the area density truncated at zero, is at most the lower limit of the Floer
energies of `u i` over the disc of radius `δ` about `z₀`. -/
theorem lintegral_symplecticForm_le_liminf_of_tendsto_rescale (ω : SymplecticForm V) [l.NeBot]
    [l.IsCountablyGenerated] {U : Set (ℝ × ℝ)} {v : ℝ × ℝ → V} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ)) (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ))
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hv : ∀ w, Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 (v w)))
    (hdv : ∀ w, Tendsto (fun i ↦ fderiv ℝ (fun w' ↦ u i (c i + ε i • w')) w) l (𝓝 (fderiv ℝ v w)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ w, ENNReal.ofReal (ω (fderiv ℝ v w stdComplexLineReal) (fderiv ℝ v w stdComplexLineImag)) ≤
      liminf (fun i ↦ ∫⁻ z in ball z₀ δ, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z))
        l := by
  -- Shrink the disc into `U`; the energies over the smaller disc are smaller.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  refine (ω.lintegral_symplecticForm_le_liminf_of_tendsto_rescale_of_subset hU hu hKs hKt hc hε hv
    hdv (lt_min hδ hr) ((ball_subset_ball (min_le_right δ r)).trans hrU)).trans ?_
  exact liminf_le_liminf (Eventually.of_forall fun i ↦
    lintegral_mono_set (ball_subset_ball (min_le_left δ r)))

end Limit

end SymplecticForm

end TauCeti
