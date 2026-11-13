/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Analysis.Hofer
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Symplectic.Floer.Manifold.Limit
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Rescaling Floer solutions in a manifold at a bubbling point

Bubbling analysis for the inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` blows a sequence of
solutions up at points where their derivatives concentrate. This file carries out the rescaling
step of `TauCeti/Geometry/Symplectic/Floer/Rescaling/Basic.lean` for a map `u : ℝ × ℝ → M` into a
manifold `M` with a two-form `ω`, such as a closed symplectic manifold, where the perturbed
derivative `du - X_K` takes values in the actual tangent spaces of `M`.

For a centre `c` and a scale `ε`, the rescaled map is `v(w) = u(c + ε w)`. It solves the Floer
equation for the rescaled perturbation `ε K(c + ε w)` and the structure `J(c + ε w, ·)`:

* the perturbed derivative of `v` is `ε` times that of `u` at `c + ε w`
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_rescale`), so for `ε ≠ 0` the map `v` solves the
  rescaled equation exactly when `u` solves the original one
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_rescale_iff`);
* the energy density and the curvature of the rescaled data are `ε²` times those of the original
  data (`TauCeti.SmoothTwoForm.floerEnergyDensity_rescale`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_rescale`), hence the energy of `v` over a region `s`
  and the integral of `|R|` along `v` over `s` are those of `u` over the image `c + ε • s`
  (`TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_rescale`,
  `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_rescale`).

None of these needs differentiability: the chain rule for the affine reparametrization
`w ↦ c + ε w` holds for arbitrary maps (`TauCeti.mfderiv_comp_const_add_smul_apply`).

As the scale tends to zero the rescaled perturbation tends to zero and the rescaled structure
freezes at the limit `z₀` of the centres. So a limit of rescaled solutions is pseudoholomorphic for
the structure `J(z₀, ·)` frozen at the bubbling point
(`TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale`). The tangent spaces of `M` vary
with the base point, so convergence of the derivatives of the rescaled maps is convergence in the
tangent bundle, and continuity of the domain-dependent structure `J` is continuity of its
expression in the tangent coordinates at the limit point (`ContinuousLinearMap.inCoordinates`),
the form in which continuity of a bundle endomorphism is read off in Mathlib.

The symplectic area of such a limit is bounded by the energy concentrating at `z₀`. The energy
densities `ε² e(u)(c + ε w)` of the rescaled maps converge to the area density `ω(∂_s v, ∂_t v)` of
the limit `v` (`TauCeti.SmoothTwoForm.tendsto_floerEnergyDensity_rescale`), so by Fatou's lemma
after the change of variables `z = c + ε w`, for every `δ > 0` the area of `v` over the whole plane
is at most the lower limit of the Floer energies of the original maps over the disc of radius `δ`
about `z₀` (`TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale`). This is the
energy accounting that bounds the energy of a bubble by the energy lost at its bubbling point. The
values `ω(a, b)` along converging tangent vectors are read off in the trivialization at the limit
point (`TauCeti.IsSmoothForm.tendsto_apply`).

The centres and scales are chosen by Hofer's lemma applied to the square root of the Floer energy
density (`TauCeti.exists_tendsto_sq_mul_rescale_le`). On a manifold there is no norm of the
derivative without a choice of metric, but the energy density
`ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})` is intrinsic and scales by `ε²`, so it plays the role of the
squared norm of the derivative in the vector-space normalization. If the energy densities of
solutions blow up along points `z i → z₀`, there are centres `c i → z₀` and scales `ε i → 0` such
that the rescaled maps solve the rescaled Floer equation on closed discs of radii `R i → ∞`, have
energy density one at the origin and at most four on those discs, while the rescaled discs
`c i + ε i • closedBall 0 (R i)` shrink to `z₀`
(`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`).

The convergence of the rescaled maps and the removal of the singularity at infinity of the limit
plane are not carried out here.

## Main results

* `TauCeti.SmoothTwoForm.perturbedMFDeriv_rescale`: the perturbed derivative of a rescaled map.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_rescale_iff`: rescaled solutions
  solve the rescaled Floer equation.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_rescale`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_rescale`: the energy density and the curvature
  scale by `ε²`.
* `TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_rescale`,
  `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_rescale`: the energy and the
  curvature allowance are invariant under rescaling.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_of_tendsto_rescale`: limits of rescaled solutions
  solve the Cauchy–Riemann equation for the frozen structure.
* `TauCeti.SmoothTwoForm.tendsto_floerEnergyDensity_rescale`: the energy densities of the rescaled
  maps converge to the area density of the limit.
* `TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale`: the area of a limit of
  rescaled maps is at most the energy concentrating at the bubbling point.
* `TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale_of_contMDiffOn`: the same
  bound for maps that are `C¹` near the bubbling point, with no measurability hypothesis.
* `TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`: where the energy
  densities of Floer solutions blow up, rescaling gives solutions of the rescaled equation on
  growing discs with energy density one at the origin and at most four on the discs.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.2
  (rescaling at a point where the derivatives blow up), Section 4.6 (bubbling) and Section 8.1
  (inhomogeneous equations and bubbles for the frozen structure).
-/

public section

open Bundle Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {Ks Kt : ℝ × ℝ → M → ℝ}

section Pointwise

variable {u : ℝ × ℝ → M} {c w : ℝ × ℝ} {ε : ℝ}

/-- **The perturbed derivative of a rescaled map.** The perturbed derivative of
`v(w) = u(c + ε w)` for the rescaled perturbation `ε K(c + ε w)` is `ε` times the perturbed
derivative of `u` for `K` at `c + ε w`, in the tangent space `T_(u (c + ε w)) M`. -/
theorem perturbedMFDeriv_rescale (ω : SmoothTwoForm I M) :
    ω.perturbedMFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w =
      ε • ω.perturbedMFDeriv Ks Kt u (c + ε • w) := by
  -- As in `SmoothTwoForm.perturbedMFDeriv_perturbationPullback`, but with no differentiability:
  -- the chain rule for affine reparametrizations and `X_{ε H} = ε X_H` hold for arbitrary maps.
  have hX (K : ℝ × ℝ → M → ℝ) : ω.hamiltonianVectorField (fun x ↦ ε * K (c + ε • w) x) =
      ε • ω.hamiltonianVectorField (K (c + ε • w)) := by
    funext x
    exact ω.hamiltonianVectorField_const_smul (f := K (c + ε • w)) ε x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [perturbedMFDeriv_apply, hX, hX]
  refine (congrArg (fun a ↦ a - _ - _) (mfderiv_comp_const_add_smul_apply u c w ε v)).trans ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, perturbedMFDeriv_apply, smul_sub, smul_comm ε]

/-- **Rescaled solutions.** For a nonzero scale `ε`, the rescaled map `w ↦ u(c + ε w)` solves the
Floer equation for the rescaled perturbation `ε K(c + ε w)` at `w`, with respect to a structure
`J` on `T_(u (c + ε w)) M`, exactly when `u` solves the Floer equation for `K` at `c + ε w` with
respect to `J`. -/
theorem isComplexLinearMap_perturbedMFDeriv_rescale_iff (ω : SmoothTwoForm I M)
    {J : AlmostComplexStructure (TangentSpace I (u (c + ε • w)))} (hε : ε ≠ 0) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
          (fun w ↦ u (c + ε • w)) w).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u (c + ε • w)).toLinearMap := by
  rw [ω.perturbedMFDeriv_rescale, isComplexLinearMap_stdComplexLine_iff,
    isComplexLinearMap_stdComplexLine_iff]
  simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, map_smul]
  exact smul_right_injective _ hε |>.eq_iff

/-- **The energy density of a rescaled map.** The Floer energy density of `w ↦ u(c + ε w)` for the
rescaled perturbation `ε K(c + ε w)` is `ε²` times the energy density of `u` at `c + ε w`. -/
theorem floerEnergyDensity_rescale (ω : SmoothTwoForm I M) :
    ω.floerEnergyDensity (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x)
        (fun w ↦ u (c + ε • w)) w =
      ε ^ 2 * ω.floerEnergyDensity Ks Kt u (c + ε • w) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, ω.perturbedMFDeriv_rescale]
  simp only [FunLike.coe_smul, Pi.smul_apply, SmoothBundleForm.eval₂_smul_left,
    SmoothBundleForm.eval₂_smul_right, smul_eq_mul]
  ring

/-- **The curvature of rescaled data.** The curvature of the rescaled perturbation
`ε K(c + ε w)` is `ε²` times the curvature of `K` at `c + ε w`. -/
theorem hamiltonianCurvature_rescale (ω : SmoothTwoForm I M) {x : M} :
    ω.hamiltonianCurvature (fun w x ↦ ε * Ks (c + ε • w) x) (fun w x ↦ ε * Kt (c + ε • w) x) w x =
      ε ^ 2 * ω.hamiltonianCurvature Ks Kt (c + ε • w) x := by
  -- As for `SmoothTwoForm.perturbedMFDeriv_rescale`, this needs no differentiability: the chain
  -- rule for affine reparametrizations and the homogeneity of derivatives and Poisson brackets
  -- under constant multiples hold for arbitrary functions.
  have hd (K : ℝ × ℝ → M → ℝ) : fderiv ℝ (fun w ↦ ε * K (c + ε • w) x) w =
      ε • ε • fderiv ℝ (fun z ↦ K z x) (c + ε • w) := by
    refine (congrFun (fderiv_const_smul_field (f := fun w ↦ K (c + ε • w) x) ε) w).trans ?_
    rw [Pi.smul_apply, fderiv_comp_smul (f := fun y ↦ K (c + y) x),
      fderiv_comp_add_left (f := fun z ↦ K z x)]
  have hK (K : ℝ × ℝ → M → ℝ) : (fun x ↦ ε * K (c + ε • w) x) = ε • K (c + ε • w) := rfl
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def, hd, hd, hK, hK,
    poissonBracket_const_smul_left, poissonBracket_const_smul_right]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end Pointwise

section Integral

variable {u : ℝ × ℝ → M} {c : ℝ × ℝ} {ε : ℝ}

/-- **The energy of a rescaled map.** For a nonzero scale `ε`, the Floer energy of the rescaled map
`w ↦ u(c + ε w)` for the rescaled perturbation `ε K(c + ε w)` over a measurable set `s` is the
energy of `u` for `K` over the image `c + ε • s`: the Floer energy is invariant under rescaling.
No differentiability or integrability is needed. -/
theorem lintegral_floerEnergyDensity_rescale (ω : SmoothTwoForm I M) (hε : ε ≠ 0)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ w in s, ENNReal.ofReal (ω.floerEnergyDensity (fun w x ↦ ε * Ks (c + ε • w) x)
        (fun w x ↦ ε * Kt (c + ε • w) x) (fun w ↦ u (c + ε • w)) w) =
      ∫⁻ z in (fun w ↦ c + ε • w) '' s, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  refine (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul (φ := fun w ↦ c + ε • w) hs
    (fun _ _ _ _ hab ↦ smul_right_injective _ hε (add_left_cancel hab))
    (fun w _ ↦ (differentiableAt_id.const_smul ε).const_add c) fun w _ ↦ ?_).symm
  -- The Jacobian determinant of `w ↦ c + ε • w` is `ε²`.
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ c + ε • w) (ε • ContinuousLinearMap.id ℝ (ℝ × ℝ)) w :=
    ((hasFDerivAt_id w).const_smul ε).const_add c
  rw [h.fderiv, ω.floerEnergyDensity_rescale]
  simp [ContinuousLinearMap.det, sq]

/-- **The curvature allowance of rescaled data.** For a nonzero scale `ε`, the integral of `|R|`
for the rescaled perturbation `ε K(c + ε w)` along the rescaled map over a measurable set `s` is the
integral of `|R_K(u)|` over the image `c + ε • s`. -/
theorem lintegral_enorm_hamiltonianCurvature_rescale (ω : SmoothTwoForm I M) (hε : ε ≠ 0)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ w in s, ‖ω.hamiltonianCurvature (fun w x ↦ ε * Ks (c + ε • w) x)
        (fun w x ↦ ε * Kt (c + ε • w) x) w (u (c + ε • w))‖ₑ =
      ∫⁻ z in (fun w ↦ c + ε • w) '' s, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ := by
  refine (lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul (φ := fun w ↦ c + ε • w) hs
    (fun _ _ _ _ hab ↦ smul_right_injective _ hε (add_left_cancel hab))
    (fun w _ ↦ (differentiableAt_id.const_smul ε).const_add c) fun w _ ↦ ?_).symm
  -- The Jacobian determinant of `w ↦ c + ε • w` is `ε²`.
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ c + ε • w) (ε • ContinuousLinearMap.id ℝ (ℝ × ℝ)) w :=
    ((hasFDerivAt_id w).const_smul ε).const_add c
  rw [h.fderiv, ω.hamiltonianCurvature_rescale]
  simp [ContinuousLinearMap.det, sq]

end Integral

section Limit

variable {ι : Type*} {l : Filter ι} {u : ι → ℝ × ℝ → M} {c : ι → ℝ × ℝ} {ε : ι → ℝ}
  {z₀ : ℝ × ℝ} {x₀ : M}

/-- The rescaled Hamiltonian terms `ε i • X_K(c i + ε i • w, x i)`, in the fibre coordinates at
`x₀`, tend to zero when `X_K` is continuous at the limit point as a map into the tangent
bundle. -/
private theorem tendsto_smul_hamiltonianVectorField_coord (ω : SmoothTwoForm I M)
    {K : ℝ × ℝ → M → ℝ} {x : ι → M} (w : ℝ × ℝ)
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0)) (hx : Tendsto x l (𝓝 x₀))
    (hX : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (K p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀)) :
    Tendsto (fun i ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (x i)
      (ε i • ω.hamiltonianVectorField (K (c i + ε i • w)) (x i))) l (𝓝 0) := by
  have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by simpa using hc.add (hε.smul_const w)
  have h := (((trivializationAt E (TangentSpace I) x₀).tendsto_mk_nhds_mk_iff ℝ
    (FiberBundle.mem_baseSet_trivializationAt E _ x₀)).1
    (hX.tendsto.comp (hz.prodMk_nhds hx))).2
  simpa only [map_smul, zero_smul] using hε.smul h

/-- The rescaled perturbed derivatives `ε i • (du - X_K)` at the points `c i + ε i • w`, in the
fibre coordinates at `x₀`, converge to the coordinates of the limit `L v` of the derivatives of
the rescaled maps: the Hamiltonian terms carry a factor `ε i → 0`. -/
private theorem tendsto_coord_smul_perturbedMFDeriv_rescale (ω : SmoothTwoForm I M) {w : ℝ × ℝ}
    {L : ℝ × ℝ →L[ℝ] TangentSpace I x₀} (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hL : ∀ v, Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w' ↦ u i (c i + ε i • w')) w v⟩ : TangentBundle I M)) l
      (𝓝 ⟨x₀, L v⟩))
    (hXs : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (hXt : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (v : ℝ × ℝ) :
    Tendsto (fun i ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
      (u i (c i + ε i • w)) (ε i • ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w) v)) l
      (𝓝 ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ (L v))) := by
  obtain ⟨hx, hD⟩ := ((trivializationAt E (TangentSpace I) x₀).tendsto_mk_nhds_mk_iff ℝ
    (FiberBundle.mem_baseSet_trivializationAt E _ x₀)).1 (hL v)
  have h := (hD.sub ((ω.tendsto_smul_hamiltonianVectorField_coord w hc hε hx hXs).const_smul
    v.1)).sub ((ω.tendsto_smul_hamiltonianVectorField_coord w hc hε hx hXt).const_smul v.2)
  rw [smul_zero, smul_zero, sub_zero, sub_zero] at h
  refine h.congr fun i ↦ ?_
  rw [mfderiv_comp_const_add_smul_apply, perturbedMFDeriv_apply]
  simp only [map_sub, map_smul, smul_sub, smul_comm (ε i)]

/-- **Bubbles in a manifold are holomorphic for the frozen structure.** Let `u i` solve the Floer
equation `(du - X_K)^{0,1} = 0` in a manifold `M`, for a domain-dependent structure `J(z, x)` on
`T_x M`, at the points `c i + ε i • w`, where the centres `c i` tend to `z₀` and the scales `ε i`
tend to `0`. Suppose that the derivatives of the rescaled maps `w' ↦ u i (c i + ε i • w')` at `w`
converge in the tangent bundle to `L : ℝ × ℝ → T_(x₀) M`, that the Hamiltonian vector fields of
`K` are continuous at `(z₀, x₀)` as maps into the tangent bundle, and that `J` is continuous at
`(z₀, x₀)` in the tangent coordinates at `x₀`. Then `L` is complex linear for the structure
`J(z₀, x₀)` frozen at the bubbling point `z₀`. -/
theorem isComplexLinearMap_of_tendsto_rescale (ω : SmoothTwoForm I M) [FiniteDimensional ℝ E]
    [l.NeBot] {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {w : ℝ × ℝ}
    {L : ℝ × ℝ →L[ℝ] TangentSpace I x₀} (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hL : ∀ v, Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w' ↦ u i (c i + ε i • w')) w v⟩ : TangentBundle I M)) l
      (𝓝 ⟨x₀, L v⟩))
    (hJ : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ p.2 x₀ p.2
        (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z₀, x₀))
    (hXs : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (hXt : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (hsol : ∀ᶠ i in l, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (c i + ε i • w) (u i (c i + ε i • w)))
      (ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z₀ x₀) L.toLinearMap := by
  have hx : Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 x₀) :=
    (((trivializationAt E (TangentSpace I) x₀).tendsto_mk_nhds_mk_iff ℝ
      (FiberBundle.mem_baseSet_trivializationAt E _ x₀)).1 (hL 0)).1
  have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by simpa using hc.add (hε.smul_const w)
  -- The rescaled perturbed derivatives `ε i • (du - X_K)` converge to `L` in the tangent bundle,
  -- and are complex linear for the structures along the sequence.
  refine isComplexLinearMap_of_tendsto_tangentBundle
    (A := fun i ↦ ε i • ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w)) hz
    (fun v ↦ ((trivializationAt E (TangentSpace I) x₀).tendsto_mk_nhds_mk_iff ℝ
      (FiberBundle.mem_baseSet_trivializationAt E _ x₀)).2
      ⟨hx, ω.tendsto_coord_smul_perturbedMFDeriv_rescale hc hε hL hXs hXt v⟩) hJ
    (hsol.mono fun i hi ↦ hi.smul (ε i))

/-- **The energy densities of rescaled maps converge to the area density of the limit.** Rescale
maps `u i` into `M` at centres `c i → z₀` by scales `ε i → 0`. Suppose that the derivatives of the
rescaled maps `w' ↦ u i (c i + ε i • w')` at `w` converge in the tangent bundle to those of a map
`v`, and that the Hamiltonian vector fields of `K` are continuous at `(z₀, v w)` as maps into the
tangent bundle. Then the Floer energy densities `ε i ^ 2 * e(u i)(c i + ε i • w)` of the rescaled
maps converge to the area density `ω(∂_s v, ∂_t v)` of `v` at `w`: the rescaled perturbation
disappears in the limit. -/
theorem tendsto_floerEnergyDensity_rescale (ω : SmoothTwoForm I M) {v : ℝ × ℝ → M} {w : ℝ × ℝ}
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hdv : ∀ a, Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w' ↦ u i (c i + ε i • w')) w a⟩ : TangentBundle I M)) l
      (𝓝 ⟨v w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w a⟩))
    (hXs : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, v w))
    (hXt : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, v w)) :
    Tendsto (fun i ↦ ε i ^ 2 * ω.floerEnergyDensity Ks Kt (u i) (c i + ε i • w)) l
      (𝓝 (SmoothBundleForm.eval₂ ω (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag))) := by
  set T := trivializationAt E (TangentSpace I) (v w)
  have hx₀ : v w ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ (v w)
  have hx : Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 (v w)) :=
    ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hdv 0)).1
  -- The rescaled perturbed derivatives converge in the tangent bundle to the derivative of `v`.
  have hP (a : ℝ × ℝ) : Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      ε i • ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w) a⟩ : TangentBundle I M)) l
      (𝓝 ⟨v w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w a⟩) :=
    (T.tendsto_mk_nhds_mk_iff ℝ hx₀).2
      ⟨hx, ω.tendsto_coord_smul_perturbedMFDeriv_rescale hc hε hdv hXs hXt a⟩
  have h := (ω.isSmoothForm.of_le (by simp)).tendsto_apply hx
    (v := fun i ↦ ![ε i • ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w) stdComplexLineReal,
      ε i • ω.perturbedMFDeriv Ks Kt (u i) (c i + ε i • w) stdComplexLineImag])
    (v₀ := ![mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal,
      mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag])
    (fun j ↦ by fin_cases j <;> exact hP _)
  rw [SmoothBundleForm.eval₂_apply]
  refine h.congr fun i ↦ ?_
  rw [← ω.floerEnergyDensity_rescale, floerEnergyDensity_def, ω.perturbedMFDeriv_rescale,
    SmoothBundleForm.eval₂_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply]

/-- **The area of a bubble in a manifold is at most the energy concentrating at its bubbling
point.** Rescale maps `u i` into `M` at centres `c i → z₀` by scales `ε i → 0`, and suppose that at
every point `w` of the plane the derivatives of the rescaled maps `w' ↦ u i (c i + ε i • w')`
converge in the tangent bundle to those of a map `v`, and that the Hamiltonian vector fields of `K`
are continuous at the points `(z₀, v w)` as maps into the tangent bundle. Then for every `δ > 0`
the symplectic area `∫ ω(∂_s v, ∂_t v)` of `v` over the whole plane, with the area density
truncated at zero, is at most the lower limit of the Floer energies of `u i` over the disc of
radius `δ` about `z₀`, provided these energy densities are measurable on that disc. -/
theorem lintegral_eval₂_le_liminf_of_tendsto_rescale (ω : SmoothTwoForm I M) [l.NeBot]
    [l.IsCountablyGenerated] {v : ℝ × ℝ → M} {δ : ℝ} (hδ : 0 < δ)
    (hmeas : ∀ i, AEMeasurable (ω.floerEnergyDensity Ks Kt (u i))
      (volume.restrict (Metric.ball z₀ δ)))
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hdv : ∀ w a, Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w' ↦ u i (c i + ε i • w')) w a⟩ : TangentBundle I M)) l
      (𝓝 ⟨v w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w a⟩))
    (hXs : ∀ w, ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, v w))
    (hXt : ∀ w, ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, v w)) :
    ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)) ≤
      liminf (fun i ↦ ∫⁻ z in Metric.ball z₀ δ,
        ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z)) l := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set B := Metric.ball z₀ δ
  -- The rescaled energy densities, cut off outside the preimage of the disc `B`.
  set g : ι → ℝ × ℝ → ENNReal := fun i w ↦
    ENNReal.ofReal (ε i ^ 2 * B.indicator (ω.floerEnergyDensity Ks Kt (u i)) (c i + ε i • w))
  -- Each cut-off density integrates to at most the energy of `u i` over `B`, by the change of
  -- variables `z = c i + ε i • w`.
  have hint (i : ι) : ∫⁻ w, g i w ≤
      ∫⁻ z in B, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z) := by
    rcases eq_or_ne (ε i) 0 with h0 | h0
    · simp [g, h0]
    have hpre : MeasurableSet ((fun w ↦ c i + ε i • w) ⁻¹' B) :=
      (Metric.isOpen_ball.preimage
        (continuous_const.add (continuous_id.const_smul (ε i)))).measurableSet
    have hg : g i = ((fun w ↦ c i + ε i • w) ⁻¹' B).indicator fun w ↦
        ENNReal.ofReal (ω.floerEnergyDensity (fun w x ↦ ε i * Ks (c i + ε i • w) x)
          (fun w x ↦ ε i * Kt (c i + ε i • w) x) (fun w ↦ u i (c i + ε i • w)) w) := by
      funext w
      by_cases hw : c i + ε i • w ∈ B
      · simp [g, hw, ω.floerEnergyDensity_rescale]
      · simp [g, hw]
    rw [hg, lintegral_indicator hpre, ω.lintegral_floerEnergyDensity_rescale h0 hpre]
    exact lintegral_mono_set (image_preimage_subset _ B)
  -- Each cut-off density is measurable: the affine change of variables is quasi-measure
  -- preserving.
  have hmeas' (i : ι) : AEMeasurable (g i) := by
    rcases eq_or_ne (ε i) 0 with h0 | h0
    · have hg : g i = fun _ ↦ 0 := by
        funext w
        simp [g, h0]
      rw [hg]
      exact aemeasurable_const
    have he : AEMeasurable (B.indicator (ω.floerEnergyDensity Ks Kt (u i))) :=
      (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).2 (hmeas i)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_const.mul
      (he.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_add_smul volume (c i) h0)))
  -- Pointwise, the cut-off densities converge to the area density of the limit `v`.
  have hlim (w : ℝ × ℝ) : Tendsto (fun i ↦ g i w) l (𝓝 (ENNReal.ofReal
      (SmoothBundleForm.eval₂ ω (v w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)))) := by
    have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by
      simpa using hc.add (hε.smul_const w)
    have hB : ∀ᶠ i in l, c i + ε i • w ∈ B :=
      hz.eventually_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    refine (ENNReal.tendsto_ofReal (ω.tendsto_floerEnergyDensity_rescale hc hε (hdv w) (hXs w)
      (hXt w))).congr' (hB.mono fun i hi ↦ ?_)
    simp only [g, indicator_of_mem hi]
  -- Fatou's lemma.
  calc ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag))
      = ∫⁻ w, liminf (fun i ↦ g i w) l := lintegral_congr fun w ↦ ((hlim w).liminf_eq).symm
    _ ≤ liminf (fun i ↦ ∫⁻ w, g i w) l := lintegral_liminf_le' hmeas'
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall hint)

/-- **The area of a bubble of `C¹` maps in a manifold is at most the energy concentrating at its
bubbling point.** Let `u i` be `C¹` on an open set `U` containing `z₀`, and let the Hamiltonian
vector fields of the perturbation `K` be continuous on `U × M` as maps into the tangent bundle.
Rescale `u i` at centres `c i → z₀` by scales `ε i → 0`, and suppose that the derivatives of the
rescaled maps `w ↦ u i (c i + ε i • w)` converge in the tangent bundle at every point of the plane
to those of a map `v`. Then for every `δ > 0` the symplectic area `∫ ω(∂_s v, ∂_t v)` of `v` over
the whole plane, with the area density truncated at zero, is at most the lower limit of the Floer
energies of `u i` over the disc of radius `δ` about `z₀`. Unlike
`TauCeti.SmoothTwoForm.lintegral_eval₂_le_liminf_of_tendsto_rescale`, no measurability hypothesis
is needed: the energy densities are continuous on `U`. The vector-space case is
`SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`. -/
theorem lintegral_eval₂_le_liminf_of_tendsto_rescale_of_contMDiffOn (ω : SmoothTwoForm I M)
    [l.NeBot] [l.IsCountablyGenerated] {U : Set (ℝ × ℝ)} {v : ℝ × ℝ → M} (hU : IsOpen U)
    (hz₀ : z₀ ∈ U) (hu : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u i) U)
    (hXs : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (U ×ˢ univ))
    (hXt : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (U ×ˢ univ))
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0))
    (hdv : ∀ w e, Tendsto (fun i ↦ (⟨u i (c i + ε i • w),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w' ↦ u i (c i + ε i • w')) w e⟩ : TangentBundle I M)) l
      (𝓝 ⟨v w, mfderiv 𝓘(ℝ, ℝ × ℝ) I v w e⟩))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ w, ENNReal.ofReal (SmoothBundleForm.eval₂ ω (v w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I v w stdComplexLineImag)) ≤
      liminf (fun i ↦ ∫⁻ z in Metric.ball z₀ δ,
        ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u i) z)) l := by
  -- Shrink the disc to a disc `B ⊆ U`, on which the energy densities are continuous; the energies
  -- over `B` are smaller.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hBU : Metric.ball z₀ (min δ r) ⊆ U := (Metric.ball_subset_ball (min_le_right δ r)).trans hrU
  have hUM (w : ℝ × ℝ) : U ×ˢ univ ∈ 𝓝 (z₀, v w) :=
    (hU.prod isOpen_univ).mem_nhds (mk_mem_prod hz₀ (mem_univ (v w)))
  refine (ω.lintegral_eval₂_le_liminf_of_tendsto_rescale (lt_min hδ hr)
    (fun i ↦ ((ω.continuousOn_floerEnergyDensity hU (hu i) hXs hXt).mono hBU).aemeasurable
      Metric.isOpen_ball.measurableSet) hc hε hdv (fun w ↦ hXs.continuousAt (hUM w))
    (fun w ↦ hXt.continuousAt (hUM w))).trans ?_
  exact liminf_le_liminf (Eventually.of_forall fun i ↦
    lintegral_mono_set (Metric.ball_subset_ball (min_le_left δ r)))

end Limit

section Bubbling

variable {ι : Type*} {l : Filter ι} {u : ι → ℝ × ℝ → M} {z : ι → ℝ × ℝ} {z₀ : ℝ × ℝ}

/-- **Rescaling Floer solutions in a manifold where their energy density blows up.** Let `u i`
solve the Floer equation `(du - X_K)^{0,1} = 0` in a manifold `M` on an open set `U` of the
domain, for a domain-dependent structure `J(z, x)` on `T_x M`, with Floer energy densities
`e i = ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})` continuous on `U`. If `e i (z i) → ∞` along points
`z i → z₀ ∈ U`, there are centres `c i → z₀`, scales `ε i > 0` with `ε i → 0` and radii
`R i → ∞` with `ε i * R i → 0` such that eventually the rescaled maps `w ↦ u i (c i + ε i • w)`

* have energy density one at the origin for the rescaled perturbation `ε i K(c i + ε i • w)`;
* for `‖w‖ ≤ R i`, are defined at `w`, in the sense that `c i + ε i • w ∈ U`, have energy density
  at most four there, and solve the rescaled Floer equation there for the structure
  `J(c i + ε i • w, ·)`.

This is the choice of centres and scales of bubbling analysis. The energy density replaces the norm
of the derivative of the vector-space statement
`TauCeti.SymplecticForm.exists_rescale_isComplexLinearMap_perturbedFDeriv`: it is defined without a
metric on `M` and scales by `ε²` under rescaling
(`TauCeti.SmoothTwoForm.floerEnergyDensity_rescale`). -/
theorem exists_rescale_isComplexLinearMap_perturbedMFDeriv (ω : SmoothTwoForm I M)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (he : ∀ i, ContinuousOn (ω.floerEnergyDensity Ks Kt (u i)) U)
    (hsol : ∀ᶠ i in l, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J y (u i y)) (ω.perturbedMFDeriv Ks Kt (u i) y).toLinearMap)
    (hz : Tendsto z l (𝓝 z₀))
    (hblow : Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) (z i)) l atTop) :
    ∃ (c : ι → ℝ × ℝ) (ε R : ι → ℝ), (∀ i, 0 < ε i) ∧ Tendsto c l (𝓝 z₀) ∧
      Tendsto ε l (𝓝 0) ∧ Tendsto R l atTop ∧ Tendsto (fun i ↦ ε i * R i) l (𝓝 0) ∧
      ∀ᶠ i in l, ω.floerEnergyDensity (fun w x ↦ ε i * Ks (c i + ε i • w) x)
          (fun w x ↦ ε i * Kt (c i + ε i • w) x) (fun w ↦ u i (c i + ε i • w)) 0 = 1 ∧
        ∀ w, ‖w‖ ≤ R i → c i + ε i • w ∈ U ∧
          ω.floerEnergyDensity (fun w x ↦ ε i * Ks (c i + ε i • w) x)
            (fun w x ↦ ε i * Kt (c i + ε i • w) x) (fun w ↦ u i (c i + ε i • w)) w ≤ 4 ∧
          IsComplexLinearMap (AlmostComplexStructure.product ℝ)
            (J (c i + ε i • w) (u i (c i + ε i • w)))
            (ω.perturbedMFDeriv (fun w x ↦ ε i * Ks (c i + ε i • w) x)
              (fun w x ↦ ε i * Kt (c i + ε i • w) x) (fun w ↦ u i (c i + ε i • w)) w).toLinearMap
    := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz₀)
  obtain ⟨c, ε, R, hε, hc, hε0, hR, hεR, hev⟩ :=
    exists_tendsto_sq_mul_rescale_le hr (fun i ↦ (he i).mono hrU) hz hblow
  -- Eventually the rescaled discs `c i + ε i • closedBall 0 (R i)` lie in `closedBall z₀ r ⊆ U`.
  have hin : ∀ᶠ i in l, ε i * R i + dist (c i) z₀ < r := by
    have h := hεR.add (tendsto_iff_dist_tendsto_zero.1 hc)
    rw [add_zero] at h
    exact h.eventually (gt_mem_nhds hr)
  refine ⟨c, ε, R, hε, hc, hε0, hR, hεR, ?_⟩
  filter_upwards [hev, hin, hsol] with i hi hin hsol
  refine ⟨by rw [ω.floerEnergyDensity_rescale, smul_zero, add_zero]; exact hi.1, fun w hw ↦ ?_⟩
  have hmem : c i + ε i • w ∈ U := hrU <| Metric.mem_closedBall.2 <| by
    have hεw : ‖ε i • w‖ ≤ ε i * R i := by
      rw [norm_smul, Real.norm_of_nonneg (hε i).le]
      exact mul_le_mul_of_nonneg_left hw (hε i).le
    have := dist_triangle (c i + ε i • w) (c i) z₀
    rw [dist_self_add_left] at this
    linarith
  exact ⟨hmem, by rw [ω.floerEnergyDensity_rescale]; exact hi.2 w hw,
    (ω.isComplexLinearMap_perturbedMFDeriv_rescale_iff (hε i).ne').2 (hsol _ hmem)⟩

end Bubbling

end TauCeti.SmoothTwoForm
