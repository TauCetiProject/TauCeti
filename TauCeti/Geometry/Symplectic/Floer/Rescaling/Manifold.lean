/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.MeasureTheory.Function.Jacobian.Plane
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

Choosing the centres and scales, the convergence of the rescaled maps, the energy bound for the
bubble and the removal of the singularity at infinity of the limit plane are not carried out here.

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
  set T := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x₀
  have hx : Tendsto (fun i ↦ u i (c i + ε i • w)) l (𝓝 x₀) :=
    ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hL 0)).1
  have hz : Tendsto (fun i ↦ c i + ε i • w) l (𝓝 z₀) := by simpa using hc.add (hε.smul_const w)
  have hbase : ∀ᶠ i in l, u i (c i + ε i • w) ∈ T.baseSet := hx (T.open_baseSet.mem_nhds hx₀)
  -- In coordinates, the rescaled perturbed derivatives converge to `L`, and the structures along
  -- the sequence converge to the frozen structure.
  have hP := ω.tendsto_coord_smul_perturbedMFDeriv_rescale hc hε hL hXs hXt
  have h := (isBoundedBilinearMap_apply.continuous.tendsto _).comp
    ((hJ.tendsto.comp (hz.prodMk_nhds hx)).prodMk_nhds (hP stdComplexLineReal))
  -- Pass to the limit in `ε i • P i (0, 1) = J_i (ε i • P i (1, 0))`, read in coordinates, where
  -- the coordinate expression of `J_i` acts on coordinates of vectors as `J_i` on the vectors.
  have hlim : T.continuousLinearMapAt ℝ x₀ (L stdComplexLineImag) =
      ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x₀ x₀ x₀
        (J z₀ x₀).toLinearMap.toContinuousLinearMap
        (T.continuousLinearMapAt ℝ x₀ (L stdComplexLineReal)) :=
    tendsto_nhds_unique (hP stdComplexLineImag) (h.congr' ((hsol.and hbase).mono
      fun i ⟨hi, hb⟩ ↦ ?_))
  · rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, Trivialization.symmL_continuousLinearMapAt _ hx₀] at hlim
    rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe]
    rw [← T.coe_continuousLinearEquivAt_eq hx₀] at hlim
    exact (T.continuousLinearEquivAt ℝ x₀ hx₀).injective hlim
  · rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe] at hi
    simp only [comp_apply]
    rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, Trivialization.symmL_continuousLinearMapAt _ hb, map_smul, hi]
    rfl

end Limit

end TauCeti.SmoothTwoForm
