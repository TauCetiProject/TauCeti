/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Limits of gauges and the closed gauge orbit relation

A gauge `u : ℂ → Circle` is determined by its logarithmic derivative `Im (u⁻¹ du)`
(`TauCeti.Vortex.gaugeForm`) together with its value at one point, and depends continuously on
both. On a convex set, two differentiable gauges whose logarithmic derivatives differ by at most
`C` differ at `z` by at most their difference at `z₀` plus `C ‖z - z₀‖`
(`TauCeti.Vortex.norm_coe_sub_coe_le_of_norm_gaugeForm_sub_le`). Hence differentiable gauges whose
logarithmic derivatives converge locally uniformly to a continuous one-form `ω`, and whose values
converge at one point, converge locally uniformly to a differentiable gauge with logarithmic
derivative `ω`
(`TauCeti.Vortex.exists_tendstoLocallyUniformly_of_tendstoLocallyUniformly_gaugeForm`).

For plane vortex fields `x = (b₁, b₂, p, q)`, a gauge carries `x` to `y` exactly when its
logarithmic derivative is the connection difference `(b₁ - b₁') ds + (b₂ - b₂') dt` and it carries
the section of `x` to that of `y` (`TauCeti.Vortex.gaugeTransform_eq_iff`). Let continuous fields
`x` and `y` be locally uniform limits of fields `x i` and `y i = u i · x i`, with differentiable
gauges `u i`. Then the logarithmic derivatives of the `u i` converge locally uniformly, and:

* `x` and `y` are related by a differentiable gauge
  (`TauCeti.Vortex.exists_gaugeTransform_eq_of_tendstoLocallyUniformly`). No condition on the
  sections is needed: along an ultrafilter the values of the gauges at one point converge, since
  the circle is compact.
* If the section of `x` is nonzero at some point, then the gauges `u i` themselves converge
  locally uniformly to such a gauge
  (`TauCeti.Vortex.exists_gaugeTransform_eq_and_tendstoLocallyUniformly`).

For continuous fields of the affine space `A_m^k` (`TauCeti.Vortex.framedFieldSpace`) with
`k ≥ 3`, the section is nonzero near infinity and the connection difference is `C¹` by the Sobolev
embedding, so the limit gauge is `C²` (`TauCeti.Vortex.contDiff_coe_of_contDiff_gaugeForm`) and
lies in the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`). So the gauges converge locally
uniformly to an element of `G_(k+1)`
(`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly`). The
orbit relation of `G_(k+1)` on `A_m^k` is therefore closed under locally uniform convergence of
continuous fields (`TauCeti.Vortex.mem_orbit_sobolevGaugeGroup_of_tendstoLocallyUniformly`). This
is the input to the Hausdorff property of the quotient `A_m^k / G_(k+1)`, once convergence in
`H^k` is known to give locally uniform convergence of continuous representatives; that step is not
treated here. The fields `x i`, `y i` and the gauges `u i` need not lie in `A_m^k` or `G_(k+1)`.
Convergence of the gauges in the `H^(k+1)` norm and the slice theorem are not treated here either.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Set Topology

variable {ι : Type*} {l : Filter ι}

/-- **Two gauges with close logarithmic derivatives stay close.** On a convex set where the
logarithmic derivatives of two differentiable gauges differ by at most `C`, the gauges differ at
`z` by at most their difference at `z₀` plus `C ‖z - z₀‖`. -/
theorem norm_coe_sub_coe_le_of_norm_gaugeForm_sub_le {u v : ℂ → Circle} {s : Set ℂ}
    (hs : Convex ℝ s) (hu : ∀ w ∈ s, DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) w)
    (hv : ∀ w ∈ s, DifferentiableAt ℝ (fun w ↦ (v w : ℂ)) w) {C : ℝ}
    (hC : ∀ w ∈ s, ‖gaugeForm u w - gaugeForm v w‖ ≤ C) {z₀ z : ℂ} (hz₀ : z₀ ∈ s)
    (hz : z ∈ s) : ‖(u z : ℂ) - v z‖ ≤ ‖(u z₀ : ℂ) - v z₀‖ + C * ‖z - z₀‖ := by
  have hg (w : ℂ) (hw : w ∈ s) : DifferentiableAt ℝ (fun w ↦ ((u * v⁻¹) w : ℂ)) w := by
    simpa only [Pi.mul_apply, Circle.coe_mul] using
      (hu w hw).fun_mul (Circle.differentiableAt_coe_inv (hv w hw))
  have hbound (w : ℂ) (hw : w ∈ s) : ‖fderiv ℝ (fun w ↦ ((u * v⁻¹) w : ℂ)) w‖ ≤ C := by
    rw [norm_fderiv_coe_eq_norm_gaugeForm, gaugeForm_mul (hu w hw)
      (Circle.differentiableAt_coe_inv (hv w hw)), gaugeForm_inv (hv w hw), ← sub_eq_add_neg]
    exact hC w hw
  have hmv := hs.norm_image_sub_le_of_norm_fderiv_le hg hbound hz₀ hz
  -- `u - v = (u v⁻¹ - 1) v` and `|v| = 1`.
  have hdiff (w : ℂ) : ‖(u w : ℂ) - v w‖ = ‖((u * v⁻¹) w : ℂ) - 1‖ := by
    have hvw := Circle.coe_ne_zero (v w)
    rw [← mul_one ‖((u * v⁻¹) w : ℂ) - 1‖, ← Circle.norm_coe (v w), ← norm_mul]
    congr 1
    simp only [Pi.mul_apply, Pi.inv_apply, Circle.coe_mul, Circle.coe_inv]
    field_simp
  rw [hdiff, hdiff]
  calc ‖((u * v⁻¹) z : ℂ) - 1‖
      ≤ ‖((u * v⁻¹) z : ℂ) - (u * v⁻¹) z₀‖ + ‖((u * v⁻¹) z₀ : ℂ) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- Differentiable gauges whose logarithmic derivatives converge uniformly on a closed ball, and
whose values at its centre converge, are uniformly Cauchy on that ball. Mathlib's
`uniformCauchySeqOn_ball_of_fderiv` does not apply directly, because the derivatives
`du = i u Im (u⁻¹ du)` involve the gauges themselves; the quotients `u i (u j)⁻¹` are estimated by
`norm_coe_sub_coe_le_of_norm_gaugeForm_sub_le` instead. -/
private theorem uniformCauchySeqOn_closedBall_of_tendstoUniformlyOn_gaugeForm
    {u : ι → ℂ → Circle} (hu : ∀ i, Differentiable ℝ (fun z ↦ (u i z : ℂ)))
    {ω : ℂ → ℂ →L[ℝ] ℝ} {z₀ c : ℂ} {R : ℝ}
    (hω : TendstoUniformlyOn (fun i ↦ gaugeForm (u i)) ω l (closedBall z₀ R))
    (hc : Tendsto (fun i ↦ (u i z₀ : ℂ)) l (𝓝 c)) :
    UniformCauchySeqOn (fun i z ↦ (u i z : ℂ)) l (closedBall z₀ R) := by
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero,
    Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ := ε / (4 * (|R| + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδR : 2 * δ * (|R| + 1) = ε / 2 := by
    rw [hδ_def]
    field_simp
    ring
  have h₁ := Metric.tendstoUniformlyOn_iff.1 hω δ hδ
  have h₂ := Metric.tendsto_nhds.1 hc (ε / 4) (by positivity)
  filter_upwards [(h₁.and h₂).prod_mk (h₁.and h₂)] with p hp z hz
  obtain ⟨⟨hω₁, hc₁⟩, hω₂, hc₂⟩ := hp
  have hC (w : ℂ) (hw : w ∈ closedBall z₀ R) :
      ‖gaugeForm (u p.1) w - gaugeForm (u p.2) w‖ ≤ 2 * δ := by
    rw [← dist_eq_norm]
    linarith [hω₁ w hw, hω₂ w hw,
      dist_triangle_left (gaugeForm (u p.1) w) (gaugeForm (u p.2) w) (ω w)]
  have hmv := norm_coe_sub_coe_le_of_norm_gaugeForm_sub_le (convex_closedBall z₀ R)
    (fun w _ ↦ hu p.1 w) (fun w _ ↦ hu p.2 w) hC (mem_closedBall_self
      (dist_nonneg.trans (mem_closedBall.1 hz))) hz
  have hz₀ : ‖(u p.1 z₀ : ℂ) - u p.2 z₀‖ < ε / 2 := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (u p.1 z₀ : ℂ) (u p.2 z₀) c]
  have hzR : ‖z - z₀‖ ≤ |R| + 1 := by
    rw [← dist_eq_norm]
    exact (mem_closedBall.1 hz).trans
      ((le_abs_self R).trans (le_add_of_nonneg_right zero_le_one))
  have hδz : 2 * δ * ‖z - z₀‖ ≤ ε / 2 := hδR ▸ mul_le_mul_of_nonneg_left hzR (by positivity)
  rw [Pi.zero_apply, dist_zero_left, neg_add_eq_sub, norm_sub_rev]
  linarith

/-- The derivatives `du = (Im (u⁻¹ du)).smulRight (i u)` of gauges converge uniformly on a compact
set where the gauges and their logarithmic derivatives do, provided the limiting one-form is
continuous. -/
private theorem tendstoUniformlyOn_fderiv_of_tendstoUniformlyOn {u : ι → ℂ → Circle}
    {f : ℂ → ℂ} {ω : ℂ → ℂ →L[ℝ] ℝ} {K : Set ℂ} (hK : IsCompact K) (hωc : ContinuousOn ω K)
    (hf : TendstoUniformlyOn (fun i z ↦ (u i z : ℂ)) f l K)
    (hω : TendstoUniformlyOn (fun i ↦ gaugeForm (u i)) ω l K) :
    TendstoUniformlyOn (fun i z ↦ fderiv ℝ (fun w ↦ (u i w : ℂ)) z)
      (fun z ↦ (ω z).smulRight (f z * I)) l K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hωc
  rw [Metric.tendstoUniformlyOn_iff] at hf hω ⊢
  intro ε hε
  set δ := ε / (2 * (|M| + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδM : δ * (|M| + 1) = ε / 2 := by
    rw [hδ_def]
    field_simp
  filter_upwards [hf δ hδ, hω (ε / 2) (by positivity)] with i hfi hωi z hz
  rw [fderiv_coe_eq_smulRight_gaugeForm, dist_eq_norm]
  have hsplit : (ω z).smulRight (f z * I) - (gaugeForm (u i) z).smulRight ((u i z : ℂ) * I) =
      (ω z - gaugeForm (u i) z).smulRight ((u i z : ℂ) * I) +
        (ω z).smulRight ((f z - u i z) * I) := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [FunLike.coe_sub, FunLike.coe_add, Pi.sub_apply,
      Pi.add_apply, ContinuousLinearMap.smulRight_apply, Complex.real_smul]
    push_cast
    ring
  have h1 := hfi z hz
  have h2 := hωi z hz
  rw [dist_eq_norm] at h1 h2
  have hMz : ‖ω z‖ ≤ |M| := (hM z hz).trans (le_abs_self M)
  rw [hsplit]
  calc _ ≤ ‖(ω z - gaugeForm (u i) z).smulRight ((u i z : ℂ) * I)‖ +
        ‖(ω z).smulRight ((f z - u i z) * I)‖ := norm_add_le _ _
    _ = ‖ω z - gaugeForm (u i) z‖ + ‖ω z‖ * ‖f z - u i z‖ := by
        simp [ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖ω z - gaugeForm (u i) z‖ + |M| * δ := by
        gcongr
    _ < ε := by nlinarith [abs_nonneg M]

/-- **Limits of gauges with convergent logarithmic derivatives.** Let `u i` be differentiable
gauges whose logarithmic derivatives `Im (u i⁻¹ d(u i))` converge locally uniformly to a
continuous one-form `ω`, and whose values at one point `z₀` converge to `c`. Then the gauges
converge locally uniformly to a differentiable gauge `v` with logarithmic derivative `ω` and
`v z₀ = c`. -/
theorem exists_tendstoLocallyUniformly_of_tendstoLocallyUniformly_gaugeForm [l.NeBot]
    {u : ι → ℂ → Circle} (hu : ∀ i, Differentiable ℝ (fun z ↦ (u i z : ℂ)))
    {ω : ℂ → ℂ →L[ℝ] ℝ} (hω : TendstoLocallyUniformly (fun i ↦ gaugeForm (u i)) ω l)
    (hωc : Continuous ω) {z₀ c : ℂ} (hc : Tendsto (fun i ↦ (u i z₀ : ℂ)) l (𝓝 c)) :
    ∃ v : ℂ → Circle, Differentiable ℝ (fun z ↦ (v z : ℂ)) ∧ gaugeForm v = ω ∧ (v z₀ : ℂ) = c ∧
      TendstoLocallyUniformly (fun i z ↦ (u i z : ℂ)) (fun z ↦ (v z : ℂ)) l := by
  have hωK (R : ℝ) :=
    tendstoLocallyUniformly_iff_forall_isCompact.1 hω _ (isCompact_closedBall z₀ R)
  have hcauchy (R : ℝ) := uniformCauchySeqOn_closedBall_of_tendstoUniformlyOn_gaugeForm hu
    (hωK R) hc
  -- The pointwise limit `f`.
  choose f hf using fun z ↦ cauchy_map_iff_exists_tendsto.1
    ((hcauchy (dist z z₀)).cauchy_map (mem_closedBall.2 le_rfl))
  have hnorm (z : ℂ) : ‖f z‖ = 1 :=
    tendsto_nhds_unique (hf z).norm (tendsto_const_nhds.congr fun i ↦ (Circle.norm_coe _).symm)
  have hloc : TendstoLocallyUniformly (fun i z ↦ (u i z : ℂ)) f l := by
    refine tendstoLocallyUniformly_iff_forall_isCompact.2 fun K hK ↦ ?_
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall z₀
    exact ((hcauchy R).tendstoUniformlyOn_of_tendsto fun z _ ↦ hf z).mono hKR
  -- The derivatives converge locally uniformly to `(ω z).smulRight (f z * I)`.
  have hder (z : ℂ) : HasFDerivAt f ((ω z).smulRight (f z * I)) z := by
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (g' := fun z ↦ (ω z).smulRight (f z * I))
      isOpen_univ ?_
      (fun i z _ ↦ (hu i z).hasFDerivAt) (fun z _ ↦ hf z) (mem_univ z)
    refine tendstoLocallyUniformlyOn_univ.2
      (tendstoLocallyUniformly_iff_forall_isCompact.2 fun K hK ↦ ?_)
    exact tendstoUniformlyOn_fderiv_of_tendstoUniformlyOn hK hωc.continuousOn
      (tendstoLocallyUniformly_iff_forall_isCompact.1 hloc K hK)
      (tendstoLocallyUniformly_iff_forall_isCompact.1 hω K hK)
  let v : ℂ → Circle := fun z ↦ ⟨f z, mem_sphere_zero_iff_norm.2 (hnorm z)⟩
  -- `v` is `f` with its values in the circle, so its coercion is `f` by definition.
  have hvf : (fun z ↦ (v z : ℂ)) = f := rfl
  refine ⟨v, ?_, ?_, tendsto_nhds_unique (hf z₀) hc, by rwa [hvf]⟩
  · rw [hvf]
    exact fun z ↦ (hder z).differentiableAt
  funext z
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hconj : (starRingEnd ℂ) (f z) * f z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm z]
    norm_num
  have h : (starRingEnd ℂ) (f z) * ((ω z w : ℂ) * (f z * I)) = (ω z w : ℂ) * I := by
    linear_combination ((ω z w : ℂ) * I) * hconj
  have hvz : (v z : ℂ) = f z := rfl
  rw [gaugeForm_apply, hvf, (hder z).fderiv, hvz, ContinuousLinearMap.smulRight_apply,
    Complex.real_smul, h]
  simp

/-! ### Limits of gauge equivalent fields -/

/-- The connection difference `(b₁ - b₁') ds + (b₂ - b₂') dt` of a pair of field values, as a
continuous linear map. -/
private def connectionDifferenceCLM :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  ((EuclideanSpace.proj (0 : Fin 4)).comp (ContinuousLinearMap.fst ℝ _ _) -
      (EuclideanSpace.proj (0 : Fin 4)).comp (ContinuousLinearMap.snd ℝ _ _)).smulRight reCLM +
    ((EuclideanSpace.proj (1 : Fin 4)).comp (ContinuousLinearMap.fst ℝ _ _) -
      (EuclideanSpace.proj (1 : Fin 4)).comp (ContinuousLinearMap.snd ℝ _ _)).smulRight imCLM

private theorem connectionDifferenceCLM_apply
    (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    connectionDifferenceCLM p = (p.1 0 - p.2 0) • reCLM + (p.1 1 - p.2 1) • imCLM := (rfl)

/-- Sections converge pointwise along locally uniformly convergent fields. -/
private theorem tendsto_sectionValue_of_tendstoLocallyUniformly
    {F : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {G : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h : TendstoLocallyUniformly F G l) (z : ℂ) :
    Tendsto (fun i ↦ sectionValue (F i) z) l (𝓝 (sectionValue G z)) := by
  have hsec : Continuous fun p : EuclideanSpace ℝ (Fin 4) ↦ 2 * ((p 2 : ℂ) + (p 3 : ℂ) * I) := by
    fun_prop
  simp only [sectionValue_apply]
  exact (hsec.tendsto _).comp ((tendstoLocallyUniformlyOn_univ.2 h).tendsto_at (mem_univ z))

/-- The limit theorem for gauge equivalent fields, given the limit of the gauges at one point. -/
private theorem exists_gaugeTransform_eq_of_tendsto_apply [l.NeBot]
    {xs ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {us : ι → ℂ → Circle}
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hus : ∀ i, Differentiable ℝ (fun z ↦ (us i z : ℂ)))
    (hxy : ∀ i, gaugeTransform (us i) (xs i) = ys i) (hx : TendstoLocallyUniformly xs x l)
    (hy : TendstoLocallyUniformly ys y l) (hxc : Continuous x) (hyc : Continuous y) {z₀ c : ℂ}
    (hc : Tendsto (fun i ↦ (us i z₀ : ℂ)) l (𝓝 c)) :
    ∃ v : ℂ → Circle, Differentiable ℝ (fun z ↦ (v z : ℂ)) ∧ gaugeTransform v x = y ∧
      TendstoLocallyUniformly (fun i z ↦ (us i z : ℂ)) (fun z ↦ (v z : ℂ)) l := by
  set ω : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ connectionDifferenceCLM (x z, y z)
  have hωc : Continuous ω := connectionDifferenceCLM.continuous.comp (hxc.prodMk hyc)
  have hgauge (i : ι) : gaugeForm (us i) = fun z ↦ connectionDifferenceCLM (xs i z, ys i z) :=
    funext fun z ↦ by rw [connectionDifferenceCLM_apply, (gaugeTransform_eq_iff.1 (hxy i) z).1]
  have hω : TendstoLocallyUniformly (fun i ↦ gaugeForm (us i)) ω l := by
    simp only [hgauge]
    exact connectionDifferenceCLM.uniformContinuous.comp_tendstoLocallyUniformly (hx.prodMk hy)
  obtain ⟨v, hvd, hvω, -, hv⟩ :=
    exists_tendstoLocallyUniformly_of_tendstoLocallyUniformly_gaugeForm hus hω hωc hc
  refine ⟨v, hvd, gaugeTransform_eq_iff.2 fun z ↦
    ⟨by rw [hvω]; exact connectionDifferenceCLM_apply (x z, y z), ?_⟩, hv⟩
  -- Pass to the limit in `us i z * α(xs i) z = α(ys i) z`.
  have hvz := (tendstoLocallyUniformlyOn_univ.2 hv).tendsto_at (mem_univ z)
  refine tendsto_nhds_unique (hvz.mul (tendsto_sectionValue_of_tendstoLocallyUniformly hx z)) ?_
  exact (tendsto_sectionValue_of_tendstoLocallyUniformly hy z).congr fun i ↦
    ((gaugeTransform_eq_iff.1 (hxy i) z).2).symm

/-- **The gauge orbit relation is closed under locally uniform limits.** If continuous fields `x`
and `y` are locally uniform limits of fields `x i` and `y i = u i · x i` related by differentiable
gauges `u i`, then `x` and `y` are related by a differentiable gauge. -/
theorem exists_gaugeTransform_eq_of_tendstoLocallyUniformly [l.NeBot]
    {xs ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {us : ι → ℂ → Circle}
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hus : ∀ i, Differentiable ℝ (fun z ↦ (us i z : ℂ)))
    (hxy : ∀ i, gaugeTransform (us i) (xs i) = ys i) (hx : TendstoLocallyUniformly xs x l)
    (hy : TendstoLocallyUniformly ys y l) (hxc : Continuous x) (hyc : Continuous y) :
    ∃ v : ℂ → Circle, Differentiable ℝ (fun z ↦ (v z : ℂ)) ∧ gaugeTransform v x = y := by
  -- Along an ultrafilter finer than `l`, the values at `0` converge in the compact circle.
  set U := Ultrafilter.of l
  have hU : (U : Filter ι) ≤ l := Ultrafilter.of_le l
  have hmono {F : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {G : ℂ → EuclideanSpace ℝ (Fin 4)}
      (h : TendstoLocallyUniformly F G l) : TendstoLocallyUniformly F G U :=
    tendstoLocallyUniformly_iff_filter.2 fun z ↦
      (tendstoLocallyUniformly_iff_filter.1 h z).mono_left hU
  have hc : Tendsto (fun i ↦ (us i 0 : ℂ)) U (𝓝 ((U.map fun i ↦ us i 0).lim : ℂ)) :=
    (continuous_subtype_val.tendsto _).comp (U.map fun i ↦ us i 0).le_nhds_lim
  obtain ⟨v, hvd, hv, -⟩ := exists_gaugeTransform_eq_of_tendsto_apply hus hxy (hmono hx)
    (hmono hy) hxc hyc hc
  exact ⟨v, hvd, hv⟩

/-- **Convergence of the gauges between convergent fields.** If continuous fields `x` and `y` are
locally uniform limits of fields `x i` and `y i = u i · x i` related by differentiable gauges `u i`,
and the section of `x` is nonzero at some point, then the gauges converge locally uniformly to a
differentiable gauge `v` with `v · x = y`. -/
theorem exists_gaugeTransform_eq_and_tendstoLocallyUniformly [l.NeBot]
    {xs ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {us : ι → ℂ → Circle}
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hus : ∀ i, Differentiable ℝ (fun z ↦ (us i z : ℂ)))
    (hxy : ∀ i, gaugeTransform (us i) (xs i) = ys i) (hx : TendstoLocallyUniformly xs x l)
    (hy : TendstoLocallyUniformly ys y l) (hxc : Continuous x) (hyc : Continuous y) {z₀ : ℂ}
    (hz₀ : sectionValue x z₀ ≠ 0) :
    ∃ v : ℂ → Circle, Differentiable ℝ (fun z ↦ (v z : ℂ)) ∧ gaugeTransform v x = y ∧
      TendstoLocallyUniformly (fun i z ↦ (us i z : ℂ)) (fun z ↦ (v z : ℂ)) l := by
  have hat {F : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {G : ℂ → EuclideanSpace ℝ (Fin 4)}
      (h : TendstoLocallyUniformly F G l) :=
    tendsto_sectionValue_of_tendstoLocallyUniformly h z₀
  have hc : Tendsto (fun i ↦ (us i z₀ : ℂ)) l (𝓝 (sectionValue y z₀ / sectionValue x z₀)) := by
    refine ((hat hy).div (hat hx) hz₀).congr' ?_
    filter_upwards [(hat hx).eventually_ne hz₀] with i hi
    rw [Pi.div_apply, ← (gaugeTransform_eq_iff.1 (hxy i) z₀).2, mul_div_cancel_right₀ _ hi]
  exact exists_gaugeTransform_eq_of_tendsto_apply hus hxy hx hy hxc hyc hc

/-! ### The Sobolev gauge group -/

/-- **Limits of Sobolev gauge equivalences.** Let `k ≥ 3` and let `x`, `y` be continuous fields of
`A_m^k` which are locally uniform limits of fields `x i` and `y i = u i · x i`, related by
differentiable gauges `u i`. Then the gauges converge locally uniformly to an element `v` of the
Sobolev gauge group `G_(k+1)` with `v · x = y`. The fields `x i` and `y i` and the gauges `u i`
need not lie in `A_m^k` or `G_(k+1)`. -/
theorem exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly [l.NeBot]
    {k : ℕ} (hk : 2 < k) {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {xs ys : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {us : ι → ℂ → Circle}
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hus : ∀ i, Differentiable ℝ (fun z ↦ (us i z : ℂ)))
    (hxy : ∀ i, gaugeTransform (us i) (xs i) = ys i) (hx : TendstoLocallyUniformly xs x l)
    (hy : TendstoLocallyUniformly ys y l) (hxc : Continuous x) (hyc : Continuous y)
    (hxA : x ∈ framedFieldSpace f m k) (hyA : y ∈ framedFieldSpace f m k) :
    ∃ v ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega), gaugeTransform v x = y ∧
      TendstoLocallyUniformly (fun i z ↦ (us i z : ℂ)) (fun z ↦ (v z : ℂ)) l := by
  have hk2 : (2 : ℝ) < k := by exact_mod_cast hk
  have hk' : (1 : ℝ) < k := by linarith
  obtain ⟨z₀, hz₀⟩ := exists_sectionValue_ne_zero_of_mem_framedFieldSpace hk' hxA hxc
  obtain ⟨v, hvd, hv, hconv⟩ :=
    exists_gaugeTransform_eq_and_tendstoLocallyUniformly hus hxy hx hy hxc hyc hz₀
  refine ⟨v, ?_, hv, hconv⟩
  -- The connection difference of `x` and `y` lies in `H^k`, `k > 2`, so it is `C¹`; hence `v` is
  -- `C²`, and a `C²` gauge between fields of `A_m^k` lies in `G_(k+1)`.
  have hd : x - y ∈ sobolevFields k := by
    simpa only [sub_sub_sub_cancel_right] using
      sub_mem (mem_framedFieldSpace.1 hxA) (mem_framedFieldSpace.1 hyA)
  have hC1 (i : Fin 4) : ContDiff ℝ 1 (fun z ↦ x z i - y z i) := by
    have hdi := mem_sobolevFields.1 hd i
    simp only [Pi.sub_apply, PiLp.sub_apply] at hdi
    refine TemperedDistribution.contDiff_of_mem_realSobolevFunctions ?_ hdi ?_
    · rw [Complex.finrank_real_complex]
      push_cast
      linarith
    · exact ((EuclideanSpace.proj i).continuous.comp hxc).sub
        ((EuclideanSpace.proj i).continuous.comp hyc)
  have hω : ContDiff ℝ (1 : ℕ) (gaugeForm v) := by
    have heq : gaugeForm v = fun z ↦ (x z 0 - y z 0) • reCLM + (x z 1 - y z 1) • imCLM :=
      funext fun z ↦ (gaugeTransform_eq_iff.1 hv z).1
    rw [heq]
    exact ((hC1 0).smul contDiff_const).add ((hC1 1).smul contDiff_const)
  have hv2 : ContDiff ℝ 2 (fun z ↦ (v z : ℂ)) := by
    exact_mod_cast contDiff_coe_of_contDiff_gaugeForm hvd hω
  exact mem_sobolevGaugeGroup_of_mem_framedFieldSpace (by omega) hxA hv2 (hv ▸ hyA)

/-- **The orbit relation of `G_(k+1)` on `A_m^k` is closed under locally uniform convergence**,
`k ≥ 3`: if continuous fields `x`, `y` of `A_m^k` are locally uniform limits of fields `x i` and
`y i` of `A_m^k` lying in one `G_(k+1)`-orbit, then `x` and `y` lie in one `G_(k+1)`-orbit. The
instance `Fact (1 < k)` is the one under which `G_(k+1)` acts on `A_m^k`. -/
theorem mem_orbit_sobolevGaugeGroup_of_tendstoLocallyUniformly [l.NeBot] {k : ℕ} [Fact (1 < k)]
    (hk : 2 < k) {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {xs ys : ι → framedFieldSpace f m k} {x y : framedFieldSpace f m k}
    (hxy : ∀ i, ys i ∈ MulAction.orbit (sobolevGaugeGroup hs) (xs i))
    (hx : TendstoLocallyUniformly (fun i ↦ (xs i : ℂ → EuclideanSpace ℝ (Fin 4))) x l)
    (hy : TendstoLocallyUniformly (fun i ↦ (ys i : ℂ → EuclideanSpace ℝ (Fin 4))) y l)
    (hxc : Continuous (x : ℂ → EuclideanSpace ℝ (Fin 4)))
    (hyc : Continuous (y : ℂ → EuclideanSpace ℝ (Fin 4))) :
    y ∈ MulAction.orbit (sobolevGaugeGroup hs) x := by
  choose us hus using hxy
  have hk2 : (2 : ℝ) < k := by exact_mod_cast hk
  have h2 : 2 < (k : ℝ) + 1 := by linarith
  obtain ⟨v, hvG, hv, -⟩ :=
    exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly hk
      (fun i ↦ differentiable_of_mem_sobolevGaugeGroup h2 (us i).2)
      (fun i ↦ congrArg Subtype.val (hus i)) hx hy hxc hyc x.2 y.2
  exact ⟨⟨v, hvG⟩, Subtype.ext hv⟩

end TauCeti.Vortex
