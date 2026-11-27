/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Complex.RiemannSurface.Differential.RealForm
import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Integral
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.Integration
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff

/-!
# The residue theorem on a compact Riemann surface

Let `X` be a compact Riemann surface and `ω` a `1`-form meromorphic at every point of `X`. Then
the residues of `ω` add up to zero (`TauCeti.RiemannSurface.OneForm.sum_residue_eq_zero`):

`∑_{x ∈ supp (div ω)} Res_x ω = 0`.

Equivalently, the sum of the residues over any finite set containing the points of nonzero residue
vanishes (`TauCeti.RiemannSurface.OneForm.sum_residue_eq_zero_of_support_subset`), and so does the
`finsum` of the residues (`TauCeti.RiemannSurface.OneForm.finsum_residue_eq_zero`).

The proof is Forster's (Theorem 10.21), by Stokes' theorem. The points where `ω` is not holomorphic
form a finite set (`TauCeti.RiemannSurface.OneForm.finite_setOf_not_holomorphicAt`). Around each
such point `p` choose a closed coordinate disc, the discs pairwise disjoint, and a smooth cutoff
`χ_p`, equal to `1` near `p` and supported in the disc. With `ψ = 1 - Σ_p χ_p`, the real form of
`ψ ω` is smooth (`TauCeti.RiemannSurface.OneForm.isSmoothForm_smul_toRoughForm`), so the integral
over `X` of its exterior derivative vanishes, for the real and imaginary parts alike
(`TauCeti.integralTopForm_mextDeriv_eq_zero`). This exterior derivative is supported in the discs,
and in the disc about `p` it is `d((1 - χ_p) f dz)` with `ω = f dz`. Its integral there is a planar
integral (`TauCeti.integralTopForm_reindex_complexManifoldOrientation_eq_integral`), equal to
`2πi · Res_p ω`
(`TauCeti.RiemannSurface.OneForm.integral_extDeriv_one_sub_mul_coeff_smul_dzForm_eq_residue`).

The Hausdorff hypothesis cannot be dropped: on the Riemann sphere with the point `∞` doubled, which
is compact but not Hausdorff, the `1`-form `dz / z` has residue `1` at `0` and `-1` at each copy
of `∞`.

As a consequence, the residue pairing of the principal parts of a meromorphic function with a
global section of `Ω_{-D}` vanishes
(`TauCeti.RiemannSurface.PrincipalParts.residuePairing_principalParts_eq_zero`, in
`TauCeti/Analysis/Complex/RiemannSurface/Differential/Residue/Pairing.lean`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 10.21 (the residue theorem).
-/

noncomputable section

open Complex Filter Function IsManifold MeasureTheory Metric Set
open scoped Manifold Real Topology TauCeti.ComplexManifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω : OneForm X}

/-! ### The contribution of one pole -/

section Pole

variable {p : X} {R : ℝ}

/-- On a coordinate disc about `p` over which `ω` is holomorphic away from `p`, the coefficient of
`ω` is analytic away from the centre. -/
theorem analyticAt_coeff_chartAt
    (hsub : closedBall (chartAt ℂ p p) R ⊆ (chartAt ℂ p).target)
    (hhol : ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) R → y ≠ p →
      ω.HolomorphicAt y)
    {z : ℂ} (hz : z ∈ closedBall (chartAt ℂ p p) R) (hzc : z ≠ chartAt ℂ p p) :
    AnalyticAt ℂ (ω.coeff (chartAt ℂ p)) z := by
  have hzt := hsub hz
  refine (holomorphicAt_symm_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas p) hzt).1
    (hhol _ ((chartAt ℂ p).map_target hzt) (by rwa [(chartAt ℂ p).right_inv hzt])
      fun h ↦ hzc ?_)
  rw [← (chartAt ℂ p).right_inv hzt, h]

/-- Outside the support of the cutoff `χ`, the form `(1 - χ) f dz` is closed on the disc, where
`ω = f dz` is holomorphic away from `p`. -/
theorem extDeriv_one_sub_mul_coeff_eq_zero {χ : ContDiffBump (chartAt ℂ p p)}
    (hsub : closedBall (chartAt ℂ p p) R ⊆ (chartAt ℂ p).target)
    (hhol : ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) R → y ≠ p →
      ω.HolomorphicAt y)
    {z : ℂ} (hz : z ∈ closedBall (chartAt ℂ p p) R) (hzχ : χ.rOut < dist z (chartAt ℂ p p)) :
    extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff (chartAt ℂ p) y) • dzForm) z = 0 := by
  have hχ : (χ : ℂ → ℝ) =ᶠ[𝓝 z] 0 :=
    notMem_tsupport_iff_eventuallyEq.1 (by rwa [χ.tsupport_eq, mem_closedBall, not_le])
  have hev : (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff (chartAt ℂ p) y) • dzForm) =ᶠ[𝓝 z]
      fun y ↦ ω.coeff (chartAt ℂ p) y • dzForm := by
    filter_upwards [hχ] with y hy
    rw [hy, Pi.zero_apply, sub_zero, ofReal_one, one_mul]
  have hzc : z ≠ chartAt ℂ p p := by
    rintro rfl
    rw [dist_self] at hzχ
    exact (χ.rOut_pos.trans hzχ).false
  rw [hev.extDeriv_eq]
  exact (analyticAt_coeff_chartAt hsub hhol hz hzc).differentiableAt.extDeriv_smul_dzForm

/-- The coefficient of `d((1 - χ) f dz)` on the basis `1, i` is integrable on the disc. -/
theorem integrableOn_extDeriv_one_sub_mul_coeff {χ : ContDiffBump (chartAt ℂ p p)}
    (hsub : closedBall (chartAt ℂ p p) R ⊆ (chartAt ℂ p).target)
    (hhol : ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) R → y ≠ p →
      ω.HolomorphicAt y) :
    IntegrableOn (fun z ↦ extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff (chartAt ℂ p) y) •
      dzForm) z ![1, I]) (closedBall (chartAt ℂ p p) R) := by
  refine ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) fun z hz ↦
    (continuousAt_extDeriv_apply (Contour.contDiffAt_one_sub_mul_smul_dzForm χ.contDiffAt ?_) _)
      |>.continuousWithinAt
  by_cases hzc : z = chartAt ℂ p p
  · exact .inr (hzc ▸ χ.eventuallyEq_one)
  · exact .inl ((analyticAt_coeff_chartAt hsub hhol hz hzc).contDiffAt.restrict_scalars ℝ)

/-- In the chart at `p`, the coefficient of `θ · L(d(ψ ω))` is `L (d((1 - χ) f dz))` on the disc
and `0` outside it. -/
theorem indicator_inChartAt_smul_mapCoeff_mextDeriv (L : ℂ →L[ℝ] ℝ)
    {χ θ : ContDiffBump (chartAt ℂ p p)}
    (hsub : closedBall (chartAt ℂ p p) R ⊆ (chartAt ℂ p).target)
    (hhol : ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) R → y ≠ p →
      ω.HolomorphicAt y)
    (hχθ : χ.rOut ≤ θ.rIn) (hθR : θ.rOut ≤ R)
    {ψ : X → ℝ} (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 ψ) (hψω : ∀ x ∈ tsupport ψ, ω.HolomorphicAt x)
    (hψχ : ∀ z ∈ ball (chartAt ℂ p p) R, ψ ((chartAt ℂ p).symm z) = 1 - χ z)
    {θX : X → ℝ} (hθXθ : ∀ z ∈ (chartAt ℂ p).target, θX ((chartAt ℂ p).symm z) = θ z) (z : ℂ) :
    (chartAt ℂ p).target.indicator (fun z ↦ RoughForm.inChartAt
      (fun x ↦ θX x • RoughForm.mapCoeff L (mextDeriv fun x ↦ ψ x • ω.toRoughForm x) x)
        p z ![1, I]) z =
      (closedBall (chartAt ℂ p p) R).indicator (fun z ↦ L (extDeriv
        (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff (chartAt ℂ p) y) • dzForm) z ![1, I])) z := by
  by_cases hzt : z ∈ (chartAt ℂ p).target
  swap
  · rw [indicator_of_notMem hzt, indicator_of_notMem fun h ↦ hzt (hsub h)]
  rw [indicator_of_mem hzt, RoughForm.inChartAt_fun_smul, RoughForm.inChartAt_mapCoeff]
  beta_reduce
  rw [inChartAt_mextDeriv_smul_toRoughForm hψ hψω p hzt, extChartAt_model_symm_eq_chartAt_symm,
    hθXθ z hzt]
  simp only [ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, comp_apply, smul_eq_mul]
  have hθ : θ.rIn < θ.rOut := θ.rIn_lt_rOut
  by_cases hzb : z ∈ ball (chartAt ℂ p p) R
  · have hE : extDeriv (fun y ↦ ((ψ ((chartAt ℂ p).symm y) : ℂ) * ω.coeff (chartAt ℂ p) y) •
        dzForm) z =
        extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff (chartAt ℂ p) y) • dzForm) z := by
      refine Filter.EventuallyEq.extDeriv_eq ?_
      filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
      rw [hψχ y hy]
    rw [hE, indicator_of_mem (ball_subset_closedBall hzb)]
    by_cases hzθ : z ∈ closedBall (chartAt ℂ p p) θ.rIn
    · rw [θ.one_of_mem_closedBall hzθ, one_mul]
    · rw [extDeriv_one_sub_mul_coeff_eq_zero hsub hhol (ball_subset_closedBall hzb)
        (hχθ.trans_lt (not_le.1 (mt mem_closedBall.2 hzθ)))]
      simp
  · rw [θ.zero_of_le_dist (hθR.trans (not_lt.1 (mt mem_ball.2 hzb))), zero_mul]
    by_cases hzc : z ∈ closedBall (chartAt ℂ p p) R
    · rw [indicator_of_mem hzc, extDeriv_one_sub_mul_coeff_eq_zero hsub hhol hzc
        ((hχθ.trans_lt hθ).trans_le (hθR.trans (not_lt.1 (mt mem_ball.2 hzb))))]
      simp
    · rw [indicator_of_notMem hzc]

variable [CompactSpace X] [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) X]

/-- **The contribution of one pole.** Let `ψ` be a smooth cutoff, vanishing near the points where
`ω` is not holomorphic and equal to `1 - χ` on a coordinate disc of radius `R` about `p`, and let
`θ` be a smooth bump equal to `1` on the support of `χ` and supported in that disc. Then the
integral of `θ · L(d(ψ ω))` is `L (2πi · Res_p ω)`, for every real-linear functional `L`. -/
theorem integralTopForm_smul_mapCoeff_mextDeriv_eq (L : ℂ →L[ℝ] ℝ)
    {χ θ : ContDiffBump (chartAt ℂ p p)}
    (hsub : closedBall (chartAt ℂ p p) R ⊆ (chartAt ℂ p).target) (hω : ω.MeromorphicAt p)
    (hhol : ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) R → y ≠ p →
      ω.HolomorphicAt y)
    (hχθ : χ.rOut ≤ θ.rIn) (hθR : θ.rOut ≤ R)
    {ψ : X → ℝ} (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) ψ) (hψω : ∀ x ∈ tsupport ψ, ω.HolomorphicAt x)
    (hψχ : ∀ z ∈ ball (chartAt ℂ p p) R, ψ ((chartAt ℂ p).symm z) = 1 - χ z)
    {θX : X → ℝ} (hθX : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) θX)
    (hθXs : tsupport θX ⊆ (chartAt ℂ p).source)
    (hθXθ : ∀ z ∈ (chartAt ℂ p).target, θX ((chartAt ℂ p).symm z) = θ z) :
    integralTopForm ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (fun x ↦ θX x • RoughForm.mapCoeff L (mextDeriv fun x ↦ ψ x • ω.toRoughForm x) x) =
      L (2 * π * I * ω.residue p) := by
  have hR : 0 < R := θ.rOut_pos.trans_le hθR
  have hα : IsSmoothForm 𝓘(ℝ, ℂ) (⊤ : ℕ∞) fun x ↦ ψ x • ω.toRoughForm x :=
    isSmoothForm_smul_toRoughForm hψ hψω
  have hD : IsSmoothForm 𝓘(ℝ, ℂ) 0
      (fun x ↦ θX x • RoughForm.mapCoeff L (mextDeriv fun x ↦ ψ x • ω.toRoughForm x) x) :=
    ((isSmoothForm_mextDeriv hα (n := 0) (by simp)).mapCoeff L).fun_smul (hθX.of_le (by simp))
  rw [integralTopForm_reindex_complexManifoldOrientation_eq_integral hD
      (isClosed_tsupport _).isCompact p ((tsupport_smul_subset_left _ _).trans hθXs),
    integral_congr_ae (ae_of_all _ (indicator_inChartAt_smul_mapCoeff_mextDeriv L hsub hhol hχθ
      hθR (hψ.of_le (by simp)) hψω hψχ hθXθ)),
    integral_indicator measurableSet_closedBall,
    L.integral_comp_comm (integrableOn_extDeriv_one_sub_mul_coeff (χ := χ) hsub hhol),
    integral_extDeriv_one_sub_mul_coeff_smul_dzForm_eq_residue (chart_mem_maximalAtlas p)
      (mem_chart_source ℂ p) (mem_ball_self hR) hsub hω hhol (fun z _ ↦ χ.contDiffAt)
      χ.eventuallyEq_one fun z hz ↦ χ.zero_of_le_dist ?_]
  rw [mem_sphere.1 hz]
  exact hχθ.trans (θ.rIn_lt_rOut.le.trans hθR)

end Pole

/-! ### Cutoffs about the poles -/

section Cutoff

omit [IsManifold 𝓘(ℂ) 1 X]

/-- Coordinate discs about the points of a finite set `s`: closed discs of radius `R p` in the
preferred charts, lying over pairwise disjoint open neighbourhoods `U p`. -/
structure PoleDiscs (s : Finset X) where
  /-- The disjoint neighbourhoods. -/
  U : X → Set X
  /-- The radii of the discs. -/
  R : X → ℝ
  isOpen_U : ∀ p, IsOpen (U p)
  mem_U : ∀ p, p ∈ U p
  disjoint_U : (s : Set X).PairwiseDisjoint U
  R_pos : ∀ p, 0 < R p
  closedBall_subset : ∀ p, closedBall (chartAt ℂ p p) (R p) ⊆
    (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' U p

/-- On a Hausdorff Riemann surface, every finite set has coordinate discs about its points. -/
theorem PoleDiscs.nonempty [T2Space X] (s : Finset X) : Nonempty (PoleDiscs s) := by
  obtain ⟨U, hU, hUd⟩ := s.finite_toSet.t2_separation
  have hex : ∀ p : X, ∃ R > 0, closedBall (chartAt ℂ p p) R ⊆
      (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' U p := fun p ↦
    nhds_basis_closedBall.mem_iff.1 (((chartAt ℂ p).isOpen_inter_preimage_symm (hU p).2).mem_nhds
      ⟨mem_chart_target ℂ p, by
        simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using (hU p).1⟩)
  choose R hR hRU using hex
  exact ⟨⟨U, R, fun p ↦ (hU p).2, fun p ↦ (hU p).1, hUd, hR, hRU⟩⟩

namespace PoleDiscs

variable {s : Finset X} (d : PoleDiscs s)

theorem closedBall_subset_target (p : X) :
    closedBall (chartAt ℂ p p) (d.R p) ⊆ (chartAt ℂ p).target :=
  fun _ hz ↦ (d.closedBall_subset p hz).1

theorem closedBall_half_subset_target (p : X) :
    closedBall (chartAt ℂ p p) (d.R p / 2) ⊆ (chartAt ℂ p).target :=
  (closedBall_subset_closedBall (half_le_self (d.R_pos p).le)).trans
    (d.closedBall_subset_target p)

/-- The cutoff about `p`: `1` on the coordinate disc of radius `R p / 4`, supported in the disc of
radius `R p / 2`. -/
def χ (p : X) : SmoothBumpFunction 𝓘(ℝ, ℂ) p :=
  SmoothBumpFunction.ofClosedBallSubset p (r := d.R p / 4) (r' := d.R p / 2)
    (by linarith [d.R_pos p]) (by linarith [d.R_pos p]) (d.closedBall_half_subset_target p)

/-- The localizing bump about `p`: `1` on the coordinate disc of radius `R p / 2`, supported in
the disc of radius `R p`. -/
def θ (p : X) : SmoothBumpFunction 𝓘(ℝ, ℂ) p :=
  SmoothBumpFunction.ofClosedBallSubset p (r := d.R p / 2) (r' := d.R p)
    (by linarith [d.R_pos p]) (by linarith [d.R_pos p]) (d.closedBall_subset_target p)

theorem χ_rIn (p : X) : (d.χ p).rIn = d.R p / 4 :=
  SmoothBumpFunction.ofClosedBallSubset_rIn _ _ _ _

theorem χ_rOut (p : X) : (d.χ p).rOut = d.R p / 2 :=
  SmoothBumpFunction.ofClosedBallSubset_rOut _ _ _ _

theorem θ_rIn (p : X) : (d.θ p).rIn = d.R p / 2 :=
  SmoothBumpFunction.ofClosedBallSubset_rIn _ _ _ _

theorem θ_rOut (p : X) : (d.θ p).rOut = d.R p :=
  SmoothBumpFunction.ofClosedBallSubset_rOut _ _ _ _

/-- The global cutoff `1 - Σ_p χ_p`, vanishing near the points of `s`. -/
def ψ (x : X) : ℝ :=
  1 - ∑ q ∈ s, d.χ q x

/-- The image of the coordinate disc of radius `r ≤ R p` lies in `U p`. -/
theorem symm_image_subset (p : X) {r : ℝ} (hr : r ≤ d.R p) :
    (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) r ⊆ d.U p := by
  rintro _ ⟨z, hz, rfl⟩
  exact (d.closedBall_subset p (closedBall_subset_closedBall hr hz)).2

/-- A function supported in `U q` vanishes on `U p` for distinct points `p, q ∈ s`. -/
theorem eq_zero_of_tsupport_subset {p q : X} (hp : p ∈ s) (hq : q ∈ s) (hqp : q ≠ p)
    {f : X → ℝ} (hf : tsupport f ⊆ d.U q) {x : X} (hx : x ∈ d.U p) : f x = 0 :=
  notMem_support.1 fun h ↦
    (d.disjoint_U hq hp hqp).ne_of_mem (hf (subset_tsupport _ h)) hx rfl

theorem mem_tsupport_χ (p : X) : p ∈ tsupport (d.χ p) :=
  subset_tsupport _ (by rw [mem_support, (d.χ p).eq_one]; exact one_ne_zero)

theorem ψ_eventuallyEq_one {x : X} (hx : ∀ p ∈ s, x ∉ tsupport (d.χ p)) :
    d.ψ =ᶠ[𝓝 x] fun _ ↦ 1 := by
  filter_upwards [(Filter.eventually_all_finset s).2 fun p hp ↦
    notMem_tsupport_iff_eventuallyEq.1 (hx p hp)] with y hy
  rw [ψ, Finset.sum_eq_zero hy, sub_zero]

theorem contMDiff_ψ [T2Space X] [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) X] :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) d.ψ :=
  contMDiff_const.sub (contMDiff_finsetSum fun q _ ↦ (d.χ q).contMDiff)

variable [T2Space X]

theorem tsupport_χ_subset (p : X) : tsupport (d.χ p) ⊆ d.U p :=
  (d.χ p).tsupport_subset_chartAt_symm_image_closedBall.trans
    (d.symm_image_subset p ((d.χ_rOut p).trans_le (half_le_self (d.R_pos p).le)))

theorem tsupport_θ_subset (p : X) : tsupport (d.θ p) ⊆ d.U p :=
  (d.θ p).tsupport_subset_chartAt_symm_image_closedBall.trans
    (d.symm_image_subset p (d.θ_rOut p).le)

theorem ψ_eq {p : X} (hp : p ∈ s) {x : X} (hx : x ∈ d.U p) : d.ψ x = 1 - d.χ p x := by
  rw [ψ, Finset.sum_eq_single p (fun q hq hqp ↦
    d.eq_zero_of_tsupport_subset hp hq hqp (d.tsupport_χ_subset q) hx) fun h ↦ (h hp).elim]

theorem ψ_eventuallyEq_zero {p : X} (hp : p ∈ s) : d.ψ =ᶠ[𝓝 p] 0 := by
  filter_upwards [(d.isOpen_U p).mem_nhds (d.mem_U p), (d.χ p).eventuallyEq_one] with x hx h1
  rw [d.ψ_eq hp hx, h1, Pi.one_apply, sub_self, Pi.zero_apply]

theorem ψ_symm_eq {p : X} (hp : p ∈ s) {z : ℂ} (hz : z ∈ ball (chartAt ℂ p p) (d.R p)) :
    d.ψ ((chartAt ℂ p).symm z) = 1 - (d.χ p).toContDiffBump z := by
  have hzc := ball_subset_closedBall hz
  rw [d.ψ_eq hp (d.symm_image_subset p le_rfl ⟨z, hzc, rfl⟩),
    (d.χ p).apply_chartAt_symm (d.closedBall_subset_target p hzc)]

theorem θ_eq_one {p : X} {x : X} (hx : x ∈ tsupport (d.χ p)) : d.θ p x = 1 := by
  obtain ⟨z, hz, rfl⟩ := (d.χ p).tsupport_subset_chartAt_symm_image_closedBall hx
  rw [d.χ_rOut] at hz
  rw [(d.θ p).apply_chartAt_symm (d.closedBall_half_subset_target p hz)]
  exact (d.θ p).one_of_mem_closedBall (by
    rwa [d.θ_rIn, TauCeti.extChartAt_model_apply_eq_chartAt_apply])

variable {ω : OneForm X} (hs : ∀ x ∉ s, ω.HolomorphicAt x)
include hs

theorem holomorphicAt_of_mem_tsupport_ψ {x : X} (hx : x ∈ tsupport d.ψ) : ω.HolomorphicAt x := by
  by_contra h
  exact (notMem_tsupport_iff_eventuallyEq.2
    (d.ψ_eventuallyEq_zero (by_contra fun hxs ↦ h (hs x hxs)))) hx

omit [T2Space X] in
theorem holomorphicAt_of_mem_disc {p : X} (hp : p ∈ s) {y : X} (hy : y ∈ (chartAt ℂ p).source)
    (hyR : chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) (d.R p)) (hyp : y ≠ p) :
    ω.HolomorphicAt y := by
  refine hs y fun hys ↦ hyp ?_
  have hyU : y ∈ d.U p := d.symm_image_subset p le_rfl
    ⟨_, hyR, (chartAt ℂ p).left_inv hy⟩
  by_contra hne
  exact (d.disjoint_U hys hp hne).ne_of_mem (d.mem_U y) hyU rfl

/-- The exterior derivative of `ψ ω` is supported in the supports of the cutoffs `χ_p`, where the
localizing bumps are `1`: it is the sum of its products with the bumps `θ_p`. -/
theorem sum_θ_smul_mapCoeff_mextDeriv [IsManifold 𝓘(ℂ) 1 X] (L : ℂ →L[ℝ] ℝ) :
    (∑ p ∈ s, fun x ↦
        d.θ p x • RoughForm.mapCoeff L (mextDeriv fun x ↦ d.ψ x • ω.toRoughForm x) x) =
      RoughForm.mapCoeff L (mextDeriv fun x ↦ d.ψ x • ω.toRoughForm x) := by
  funext x
  rw [Finset.sum_apply]
  by_cases h : ∃ p ∈ s, x ∈ tsupport (d.χ p)
  · obtain ⟨p, hp, hx⟩ := h
    rw [Finset.sum_eq_single p (fun q hq hqp ↦ by
        rw [d.eq_zero_of_tsupport_subset hp hq hqp (d.tsupport_θ_subset q)
          (d.tsupport_χ_subset p hx), zero_smul]) fun h ↦ (h hp).elim,
      d.θ_eq_one hx, one_smul]
  · simp only [not_exists, not_and] at h
    have h0 : mextDeriv (fun x ↦ d.ψ x • ω.toRoughForm x) x = 0 :=
      mextDeriv_smul_toRoughForm_eq_zero (d.ψ_eventuallyEq_one h) fun _ ↦
        hs x fun hxs ↦ h x hxs (d.mem_tsupport_χ x)
    have hD : RoughForm.mapCoeff L (mextDeriv fun x ↦ d.ψ x • ω.toRoughForm x) x = 0 := by
      ext v
      simp [RoughForm.mapCoeff_apply, h0]
    simp [hD]

end PoleDiscs

end Cutoff

/-! ### The residue theorem -/

/-- **The residue theorem**, for a finite set `s` outside which `ω` is holomorphic. -/
theorem sum_residue_eq_zero_of_forall_notMem [CompactSpace X] [T2Space X]
    (hω : ∀ x, ω.MeromorphicAt x) (s : Finset X) (hs : ∀ x ∉ s, ω.HolomorphicAt x) :
    ∑ x ∈ s, ω.residue x = 0 := by
  have : IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) X := IsManifold.restrictScalars_of_ne_zero _ one_ne_zero ‹_›
  obtain ⟨d⟩ := PoleDiscs.nonempty (X := X) s
  have key (L : ℂ →L[ℝ] ℝ) : L (2 * π * I * ∑ p ∈ s, ω.residue p) = 0 := by
    have hα : IsSmoothForm 𝓘(ℝ, ℂ) (⊤ : ℕ∞) fun x ↦ d.ψ x • ω.toRoughForm x :=
      isSmoothForm_smul_toRoughForm d.contMDiff_ψ fun _ ↦ d.holomorphicAt_of_mem_tsupport_ψ hs
    have hD : IsSmoothForm 𝓘(ℝ, ℂ) 0
        (RoughForm.mapCoeff L (mextDeriv fun x ↦ d.ψ x • ω.toRoughForm x)) :=
      (isSmoothForm_mextDeriv hα (n := 0) (by simp)).mapCoeff L
    have hStokes := integralTopForm_mextDeriv_eq_zero
      ((complexManifoldOrientation ℂ X).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      ((hα.mapCoeff L).of_le (by simp))
      (isClosed_tsupport _).isCompact
    rw [mextDeriv_mapCoeff L (hα.of_le (by simp)), ← d.sum_θ_smul_mapCoeff_mextDeriv hs L,
      integralTopForm_sum _ _ _ fun p _ ↦ (hD.fun_smul ((d.θ p).contMDiff.of_le (by simp)))
        |>.integrableTopForm (isClosed_tsupport _).isCompact Complex.basisOneI] at hStokes
    rw [Finset.mul_sum, map_sum, ← hStokes]
    refine Finset.sum_congr rfl fun p hp ↦ (integralTopForm_smul_mapCoeff_mextDeriv_eq L
      (χ := (d.χ p).toContDiffBump) (θ := (d.θ p).toContDiffBump)
      (d.closedBall_subset_target p) (hω p) (fun y hy hyR hyp ↦
        d.holomorphicAt_of_mem_disc hs hp hy hyR hyp) ((d.χ_rOut p).trans (d.θ_rIn p).symm).le
      (d.θ_rOut p).le d.contMDiff_ψ
      (fun _ ↦ d.holomorphicAt_of_mem_tsupport_ψ hs) (fun z hz ↦ d.ψ_symm_eq hp hz)
      (d.θ p).contMDiff (d.θ p).tsupport_subset_chartAt_source
      fun z hz ↦ (d.θ p).apply_chartAt_symm hz).symm
  have h0 : 2 * π * I * ∑ p ∈ s, ω.residue p = 0 :=
    Complex.ext (by simpa using key reCLM) (by simpa using key imCLM)
  exact (mul_eq_zero.1 h0).resolve_left (by simp [Real.pi_ne_zero, I_ne_zero])

end TauCeti.RiemannSurface.OneForm

end

public noncomputable section

open Complex Filter Function Set
open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω : OneForm X}

variable [CompactSpace X] [T2Space X]

/-- **The residue theorem on a compact Riemann surface** (Forster, Theorem 10.21). The sum of the
residues of a `1`-form meromorphic everywhere over any finite set containing the points of nonzero
residue is `0`. -/
theorem sum_residue_eq_zero_of_support_subset (hω : ∀ x, ω.MeromorphicAt x) {s : Finset X}
    (hs : support ω.residue ⊆ s) : ∑ x ∈ s, ω.residue x = 0 := by
  classical
  set t := (finite_setOf_not_holomorphicAt hω).toFinset
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := t)) fun x _ hx ↦
      notMem_support.1 fun h ↦ hx (hs h),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) fun x _ hx ↦
      HolomorphicAt.residue_eq_zero (by simpa [t] using hx)]
  exact sum_residue_eq_zero_of_forall_notMem hω t fun x hx ↦ by simpa [t] using hx

/-- **The residue theorem on a compact Riemann surface** (Forster, Theorem 10.21). The residues of
a `1`-form meromorphic everywhere add up to zero. A `1`-form that is not meromorphic everywhere has
divisor the junk value `0`, so the sum is empty. -/
@[simp]
theorem sum_residue_eq_zero : ∑ x ∈ ω.divisor.support, ω.residue x = 0 := by
  by_cases hω : ∀ x, ω.MeromorphicAt x
  · exact sum_residue_eq_zero_of_support_subset hω fun _ hx ↦ by
      by_contra h
      exact hx (residue_eq_zero_of_notMem_support hω h)
  · rw [divisor_of_not_forall_meromorphicAt hω, Finsupp.support_zero, Finset.sum_empty]

/-- **The residue theorem on a compact Riemann surface**, as a `finsum`. -/
theorem finsum_residue_eq_zero (hω : ∀ x, ω.MeromorphicAt x) : ∑ᶠ x, ω.residue x = 0 := by
  rw [finsum_eq_sum _ (finite_support_residue hω)]
  exact sum_residue_eq_zero_of_support_subset hω (by simp)

/-- **Check.** The residue theorem on the Riemann sphere is a special case. -/
example {ω : OneForm (OnePoint ℂ)} : ∑ x ∈ ω.divisor.support, ω.residue x = 0 :=
  sum_residue_eq_zero

end TauCeti.RiemannSurface.OneForm
