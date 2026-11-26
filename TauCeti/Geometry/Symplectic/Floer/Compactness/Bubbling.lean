/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
public import TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Manifold
public import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Geometry.Manifold.ExtChartAt.ClosedBall
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Floer solutions in a manifold converge off finitely many bubbling points

Let `ω` be a nondegenerate two-form on a boundaryless manifold `M` with finite-dimensional model
space, such as a closed symplectic manifold, and let `u` solve the Floer equation
`(du - X_{K_s} ds - X_{K_t} dt)^{0,1} = 0` for a perturbation `K_s ds + K_t dt` and
domain-dependent almost complex structures `J(z, x)` tamed by `ω`, with values in a compact set
`K ⊆ M`. This file proves the interior part of Gromov–Floer compactness for such solutions without
assuming that their images stay in a single chart.

The derivatives of the solutions are measured through a map `e : M → F` into a normed space,
injective and differentiable on `K`, such as the Whitney embedding of a closed manifold, with the
structures uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)`, as in
`TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity`. The four results, in the namespace
`TauCeti.SmoothTwoForm`, are the following.

* **The mean-value inequality in a compact subset of the manifold**
  (`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mem_of_dist_lt`). There are
  constants `δ > 0`, `C ≥ 0` and `θ > 0`, uniform over `K`, such that
  `r² ρ(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} ρ(u))` for every solution on a disc `B_r(z₀)` of energy
  `r² + ∫_{B_r(z₀)} ρ(u) < δ` that maps the disc into `K` with images through `e` within `θ` of
  `e (u z₀)`. No chart is prescribed.
* **Energy concentrates at blow-up points**
  (`IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity`).
  There is a threshold `δ > 0`, depending only on the data and on a compact window `D` of the
  domain, with the following property. If the Floer energy densities of solutions `uᵢ` on an
  open set `Ω ⊆ D` blow up along points converging to `z₀ ∈ Ω`, then for every `r > 0` the disc
  `B_r(z₀)` eventually carries Floer energy at least `δ`.
* **Convergence off finitely many bubbling points**
  (`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_mapsTo`).
  A sequence of solutions on `Ω ⊆ D` with Floer energy at most `A` has a subsequence and a finite
  set `Z ⊆ Ω` of bubbling points, `#Z δ ≤ A`, at each of which energy at least `δ` concentrates,
  such that the energy densities are bounded on compact subsets of `Ω \ Z` and the solutions
  converge on `Ω \ Z`, locally uniformly through `e` and pointwise in `M`, to a continuous map
  with values in `K`.
* **Convergence in `C¹` to a Floer solution**, in
  `IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_of_mapsTo`
  for smooth solutions: the limit `v` is `C¹` on `Ω \ Z` and solves the Floer equation there, and
  in the chart at every point `α ∈ K` the derivatives of the coordinate expressions
  `extChartAt I α ∘ u_{φ n}` converge to that of `extChartAt I α ∘ v`, locally uniformly where
  `v` lies in the chart source.

The threshold comes from the mean-value inequality in a chart
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy`), made uniform
over `K` in the first result
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mem_of_dist_lt`).
The point is to bring the discs where it is applied into a chart. Cover `K` by finitely many
charts. Near a blow-up point, choose centres `cᵢ` and scales `εᵢ → 0` as in bubbling analysis
(`TauCeti.SmoothTwoForm.exists_rescale_isComplexLinearMap_perturbedMFDeriv`): the energy density is
`εᵢ⁻²` at `cᵢ` and at most `4 εᵢ⁻²` on a disc of radius much larger than `εᵢ` about `cᵢ`. By
`TauCeti.SmoothTwoForm.IsNondegenerate.norm_fderiv_comp_le` this bounds the derivative of
`e ∘ uᵢ` by a multiple of `εᵢ⁻¹`, so the disc of radius `η εᵢ` about `cᵢ` has image of size
`O(η)` through `e`. Since `e` is injective on the compact set `K`, nearby images come from nearby
points (`IsCompact.exists_mem_nhds_inter_preimage_subset`), and for small `η`, fixed by the cover,
the image of that disc lies in one chart of the cover. There the mean-value inequality on the disc
of radius `r = η εᵢ`, at whose centre `r² ρ(uᵢ) = η²`, forces energy at least a fixed amount into
the disc. The finitely many charts give a uniform threshold, and counting concentration points
(`TauCeti.exists_strictMono_finset_forall_le_of_concentration`) and the convergence where the
energy density is bounded
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_strictMono_tendstoLocallyUniformlyOn_comp`) give
the compactness theorem.

The `C¹` statement is local. Near a point `y ∈ Ω \ Z`, the injectivity of `e` on `K` and the
convergence through `e` keep the values of `v` and of the tail of the sequence on a small disc
about `y` in a compact coordinate ball of a chart
(`IsCompact.exists_closedBall_forall_mem_extChartAt_source`). There the bounds on the energy
densities bound the derivatives of the coordinate expressions
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_le`), and the
`C¹` convergence theorem for the coordinate Floer equation
(`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub`) applies.

The energy of the limit is accounted for at the bubbling points, as for a symplectic vector space in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Limit` and for solutions in a single symplectic chart
in `TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold`.

* **The energy densities converge** (`tendstoLocallyUniformlyOn_floerEnergyDensity_of_mapsTo`).
  Where maps into `K` converge through `e`, and in `C¹` in every chart at a point of `K`, their
  Floer energy densities converge locally uniformly. In the chart at `α` the energy density of `w`
  at `z` is `ω` read in the chart on the coordinates of `∂ₛw - X_{K_s}` and `∂ₜw - X_{K_t}`
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_eq_inChartAt_sub`), a continuous function of
  `(z, χ (w z), d (χ ∘ w) z)` for `χ = extChartAt I α`, and the coordinate expressions converge
  in `C¹` near each point (`IsCompact.exists_closedBall_tendstoUniformlyOn_extChartAt_comp`).
* **Energy accounting** (in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`,
  `exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset_of_mapsTo`).
  Along a further subsequence every bubbling point `z` carries a mass `m z ≥ δ`: for small
  `ε > 0` the energies of the discs `B_ε(z)` converge to `m z` plus the energy of `v` on the
  punctured disc. The energy of `v` over `Ω \ Z` is finite and `∫_{Ω \ Z} ρ(v) + ∑ m z ≤ A`. This is
  `TauCeti.exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le_of_concentration`
  applied to the energy densities, which are nonnegative because the structures are tamed.

The bubbles at the points of `Z` and breaking along cylindrical ends are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (inhomogeneous equations).
-/

public section

noncomputable section

open Filter Function Metric MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}
  {U D : Set (ℝ × ℝ)} {K : Set M}

omit [NormedSpace ℝ F] in
/-- **The mean-value inequality near a point of `K`, measured through `e`.** For `x ∈ K` there
are `δ > 0`, `C ≥ 0` and `θ > 0` such that the mean-value inequality
`r² ρ(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} ρ(u))` holds for every solution on a closed disc
`closedBall z₀ r ⊆ D` of energy `r² + ∫_{B_r(z₀)} ρ(u) < δ` whose values on the disc lie in `K`
and have images within `θ` of `e x`: such a disc is mapped into a compact coordinate ball of the
chart at `x`. -/
private theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt_chart
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    {x : M} (hx : x ∈ K)
    (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ContinuousOn e K) (he_inj : InjOn e K) :
    ∃ δ > 0, ∃ C ≥ 0, ∃ θ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄,
      IsOpen Ω → 0 ≤ r → closedBall z₀ r ⊆ Ω → closedBall z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedMFDeriv Ks Kt u y).toLinearMap) →
      (∀ y ∈ closedBall z₀ r, u y ∈ K ∧ dist (e (u y)) (e x) < θ) →
      IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        C * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y) := by
  set φ := extChartAt I x
  -- A compact coordinate ball about `φ x` inside the chart target.
  obtain ⟨κ, hκ, hκT⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) x) (φ x)
    (mem_extChartAt_target x)
  have hBT : closedBall (φ x) (κ / 2) ⊆ φ.target :=
    (closedBall_subset_ball (half_lt_self hκ)).trans hκT
  obtain ⟨δ, hδ, C, hC, hmv⟩ := hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy x
    (hU.prod (isOpen_extChartAt_target x)) hJ hXs hXt hD (isCompact_closedBall _ _) hBT
    (prod_mono hDU hBT) fun z hz y _ ↦ hJt z hz _
  -- Points of `K` with images near `e x` lie in the chart source, with coordinates in the ball.
  have hN : φ.source ∩ φ ⁻¹' ball (φ x) (κ / 2) ∈ 𝓝 x :=
    inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ (half_pos hκ)))
  obtain ⟨V, hV, hVN⟩ :=
    hK.exists_mem_nhds_inter_preimage_subset he he_inj hx (mem_nhdsWithin_of_mem_nhds hN)
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨δ, hδ, C, hC, ρ, hρ, fun Ω u z₀ r hΩ hr hBΩ hBD hu hfl hρu hint hE ↦ ?_⟩
  have huN {y : ℝ × ℝ} (hy : y ∈ closedBall z₀ r) :
      u y ∈ φ.source ∩ φ ⁻¹' ball (φ x) (κ / 2) :=
    hVN ⟨(hρu y hy).1, hρV (mem_ball.2 (hρu y hy).2)⟩
  -- The coordinate expression of `u` is `C³` near the closed disc.
  set O := Ω ∩ u ⁻¹' φ.source
  have hO : IsOpen O := hu.continuousOn.isOpen_inter_preimage hΩ (isOpen_extChartAt_source x)
  have hBO : closedBall z₀ r ⊆ O := fun y hy ↦ ⟨hBΩ hy, (huN hy).1⟩
  obtain ⟨hcd, -⟩ := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub hO
    (hu.mono inter_subset_left) (by norm_num) (fun y hy ↦ hy.2) fun y hy ↦ hfl y hy.1
  have hcont : ContinuousOn (fun y ↦ fderiv ℝ (φ ∘ u) y stdComplexLineReal) (closedBall z₀ r) :=
    ((hcd.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const).mono hBO
  exact hmv hr (ball_subset_closedBall.trans hBD) (hu.mono (ball_subset_closedBall.trans hBΩ))
    hcont (fun y hy ↦ hfl y (hBΩ (ball_subset_closedBall hy)))
    (fun y hy ↦ ⟨(huN (ball_subset_closedBall hy)).1,
      ball_subset_closedBall (huN (ball_subset_closedBall hy)).2⟩) hint hE

omit [NormedSpace ℝ F] in
/-- **The mean-value inequality for Floer solutions in a compact subset of a manifold.** Let `ω`
be a nondegenerate two-form on a boundaryless manifold `M` with finite-dimensional model space,
`K ⊆ M` compact and `D ⊆ U` a compact window of an open set `U` of the domain. Let the structures
`J(z, x)` be tamed by `ω` for `z ∈ D`, and let them and the Hamiltonian vector fields of `K_s` and
`K_t`, read in the chart at every point of `K`, be `C²` on `U` times the chart target. Let
`e : M → F` be continuous and injective on `K`.

Then there are `δ > 0`, `C ≥ 0` and `θ > 0` with the following property. Let `u` be a `C³`
solution of the Floer equation `(du - X_{K_s} ds - X_{K_t} dt)^{0,1} = 0` on an open set
containing a closed disc `closedBall z₀ r ⊆ D`, mapping the disc into `K` with images through `e`
within `θ` of `e (u z₀)`. If its Floer energy density `ρ(u)` is integrable on `B_r(z₀)` and
`r² + ∫_{B_r(z₀)} ρ(u) < δ`, then

`r² ρ(u)(z₀) ≤ C (r² + ∫_{B_r(z₀)} ρ(u))`.

Unlike `IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy`, the disc
is not required to map into a prescribed chart, and the constants do not depend on a chart. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mem_of_dist_lt
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ContinuousOn e K) (he_inj : InjOn e K) :
    ∃ δ > 0, ∃ C ≥ 0, ∃ θ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄,
      IsOpen Ω → 0 ≤ r → closedBall z₀ r ⊆ Ω → closedBall z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
        (ω.perturbedMFDeriv Ks Kt u y).toLinearMap) →
      (∀ y ∈ closedBall z₀ r, u y ∈ K ∧ dist (e (u y)) (e (u z₀)) < θ) →
      IntegrableOn (ω.floerEnergyDensity Ks Kt u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y < δ →
      r ^ 2 * ω.floerEnergyDensity Ks Kt u z₀ ≤
        C * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y) := by
  -- The mean-value inequality near each point of `K`.
  choose! δ hδ C hC θ hθ hmv using fun x (hx : x ∈ K) ↦
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt_chart hU hDU hD hK hx
      (hJ x hx) (hXs x hx) (hXt x hx) hJt he he_inj
  -- Finitely many of the sets `{y ∈ K | dist (e y) (e x) < θ x / 2}` cover `K`.
  obtain ⟨b, hbK, hb, hcov⟩ := (hK.image_of_continuousOn he).elim_finite_subcover_image
    (b := K) (c := fun x ↦ ball (e x) (θ x / 2)) (fun _ _ ↦ isOpen_ball)
    fun _ ⟨x, hx, hxy⟩ ↦ mem_iUnion₂.2 ⟨x, hx, hxy ▸ mem_ball_self (half_pos (hθ x hx))⟩
  -- Constants uniform over the cover.
  obtain ⟨m, hmb, hm⟩ := ((((eventually_all_finite hb).2 fun x hx ↦
      (eventually_le_nhds (hδ x (hbK hx))).and
        (eventually_le_nhds (half_pos (hθ x (hbK hx))))).filter_mono
      nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hCb : ∀ x ∈ hb.toFinset, 0 ≤ C x := fun x hx ↦ hC x (hbK (hb.mem_toFinset.1 hx))
  refine ⟨m, hm, ∑ x ∈ hb.toFinset, C x, Finset.sum_nonneg hCb, m, hm,
    fun Ω u z₀ r hΩ hr hBΩ hBD hu hfl hθu hint hE ↦ ?_⟩
  obtain ⟨x, hxb, hxc⟩ :=
    mem_iUnion₂.1 (hcov (mem_image_of_mem e (hθu z₀ (mem_closedBall_self hr)).1))
  have hI : 0 ≤ r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity Ks Kt u y :=
    add_nonneg (sq_nonneg r) (setIntegral_nonneg measurableSet_ball fun y hy ↦
      floerEnergyDensity_nonneg hω (hJt y (hBD (ball_subset_closedBall hy)) _)
        (hfl y (hBΩ (ball_subset_closedBall hy))))
  refine (hmv x (hbK hxb) hΩ hr hBΩ hBD hu hfl (fun y hy ↦ ⟨(hθu y hy).1, ?_⟩) hint
    (hE.trans_le (hmb x hxb).1)).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum hCb (hb.mem_toFinset.2 hxb)) hI)
  calc dist (e (u y)) (e x) ≤ dist (e (u y)) (e (u z₀)) + dist (e (u z₀)) (e x) :=
        dist_triangle _ _ _
    _ < θ x / 2 + θ x / 2 := add_lt_add ((hθu y hy).2.trans_le (hmb x hxb).2) (mem_ball.1 hxc)
    _ = θ x := add_halves _

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- On a closed disc of radius `η ε` about `c₀` on which the Floer energy density of a solution `u`
is at most `4 ε⁻²`, the derivative of `e ∘ u` is at most `2 (2 / (ε √c) + B)`, so the images of
the disc through `e` lie within `η (4 / √c + 2 B ε)` of `e (u c₀)`. -/
private theorem IsNondegenerate.dist_comp_le_of_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (huK : MapsTo u Ω K) (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) {c B : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B)
    (hJc : ∀ y ∈ Ω, ∀ v,
      c * ‖mvfderiv I e (u y) v‖ ^ 2 ≤ hω.symplecticFormAt (u y) v (J y (u y) v))
    (hBs : ∀ y ∈ Ω, ‖mvfderiv I e (u y) (ω.hamiltonianVectorField (Ks y) (u y))‖ ≤ B)
    (hBt : ∀ y ∈ Ω, ‖mvfderiv I e (u y) (ω.hamiltonianVectorField (Kt y) (u y))‖ ≤ B)
    {c₀ : ℝ × ℝ} {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η) (hBΩ : closedBall c₀ (η * ε) ⊆ Ω)
    (hdens : ∀ y ∈ closedBall c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y ≤ 4 / ε ^ 2)
    {y : ℝ × ℝ} (hy : y ∈ closedBall c₀ (η * ε)) :
    dist (e (u y)) (e (u c₀)) ≤ η * (4 / √c + 2 * (B * ε)) := by
  have hc' : 0 < √c := Real.sqrt_pos.2 hc
  have hsq : √(4 / ε ^ 2 / c) = 2 / (ε * √c) := by
    rw [show 4 / ε ^ 2 / c = (2 / (ε * √c)) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hc.le]; ring]
    exact Real.sqrt_sq (div_nonneg two_pos.le (mul_pos hε hc').le)
  have hdiff {y' : ℝ × ℝ} (hy' : y' ∈ Ω) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u y' :=
    (hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hy')
  have hL : ∀ y' ∈ closedBall c₀ (η * ε),
      ‖fderiv ℝ (e ∘ u) y'‖ ≤ 2 * (2 / (ε * √c) + B) := fun y' hy' ↦ by
    have hy'Ω := hBΩ hy'
    rw [← hsq]
    exact hω.norm_fderiv_comp_le_of_floerEnergyDensity_le hc (he _ (huK hy'Ω)) (hdiff hy'Ω)
      (hJc y' hy'Ω) (hBs y' hy'Ω) (hBt y' hy'Ω) (hfl y' hy'Ω) (hdens y' hy')
  have hdiffe : ∀ y' ∈ closedBall c₀ (η * ε), DifferentiableAt ℝ (e ∘ u) y' := fun y' hy' ↦
    mdifferentiableAt_iff_differentiableAt.1 ((he _ (huK (hBΩ hy'))).comp y' (hdiff (hBΩ hy')))
  have hlip := (convex_closedBall c₀ (η * ε)).norm_image_sub_le_of_norm_fderiv_le hdiffe hL
    (mem_closedBall_self (mul_nonneg hη hε.le)) hy
  have hyc : ‖y - c₀‖ ≤ η * ε := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
  rw [dist_eq_norm]
  calc ‖e (u y) - e (u c₀)‖ ≤ 2 * (2 / (ε * √c) + B) * (η * ε) :=
        hlip.trans (mul_le_mul_of_nonneg_left hyc (by positivity))
    _ = η * (4 / √c + 2 * (B * ε)) := by field_simp; ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **The mean-value inequality at the scale of a bubble.** Let `u` be a solution whose Floer
energy density is `ε⁻²` at `c₀` and at most `4 ε⁻²` on the closed disc of radius `r = η ε` about
`c₀`, where `η (4 / √c + 2) < θ` and `B ε ≤ 1`, so that the disc maps into `K` with images through
`e` within `θ` of `e (u c₀)`. If the mean-value inequality `hmv` with constants `δ`, `C` holds on
this disc for such solutions, then the disc carries `r² + ∫_{B_r(c₀)} ρ(u) ≥ min δ (η² / (C + 1))`.
-/
private theorem IsNondegenerate.min_le_sq_add_setIntegral_floerEnergyDensity
    (hω : ω.IsNondegenerate) {δ C θ : ℝ} (hC : 0 ≤ C) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩD : Ω ⊆ D) {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω)
    (hfl : ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap)
    (huK : MapsTo u Ω K) (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hJc : ∀ z ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    {c₀ : ℝ × ℝ} {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η) (hηθ : η * (4 / √c + 2) < θ)
    (hBε : B * ε ≤ 1) (hBΩ : closedBall c₀ (η * ε) ⊆ Ω)
    (hcen : ε ^ 2 * ω.floerEnergyDensity Ks Kt u c₀ = 1)
    (hdens : ∀ y ∈ closedBall c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y ≤ 4 / ε ^ 2)
    (hmv : (∀ y ∈ closedBall c₀ (η * ε), u y ∈ K ∧ dist (e (u y)) (e (u c₀)) < θ) →
      (η * ε) ^ 2 + ∫ y in ball c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y < δ →
      (η * ε) ^ 2 * ω.floerEnergyDensity Ks Kt u c₀ ≤
        C * ((η * ε) ^ 2 + ∫ y in ball c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y)) :
    min δ (η ^ 2 / (C + 1)) ≤
      (η * ε) ^ 2 + ∫ y in ball c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y := by
  -- The disc maps into `K` with images within `θ` of `e (u c₀)`.
  have hmove : ∀ y ∈ closedBall c₀ (η * ε), u y ∈ K ∧ dist (e (u y)) (e (u c₀)) < θ :=
    fun y hy ↦ ⟨huK (hBΩ hy), (hω.dist_comp_le_of_floerEnergyDensity_le hΩ hu hfl huK he hc hB
      (fun y hy ↦ hJc y (hΩD hy) _ (huK hy)) (fun y hy ↦ hBs y (hΩD hy) _ (huK hy))
      (fun y hy ↦ hBt y (hΩD hy) _ (huK hy)) hε hη hBΩ hdens hy).trans_lt
        (lt_of_le_of_lt (by gcongr; linarith) hηθ)⟩
  have hI : 0 ≤ ∫ y in ball c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y :=
    setIntegral_nonneg measurableSet_ball fun y hy ↦ floerEnergyDensity_nonneg hω
      (hJt y (hΩD (hBΩ (ball_subset_closedBall hy))) _) (hfl y (hBΩ (ball_subset_closedBall hy)))
  by_cases hsmall : (η * ε) ^ 2 + ∫ y in ball c₀ (η * ε), ω.floerEnergyDensity Ks Kt u y < δ
  · -- At the centre, `r² ρ(u) = η²`.
    have h := hmv hmove hsmall
    rw [mul_pow, mul_assoc, hcen, mul_one] at h
    refine (min_le_right _ _).trans ((div_le_iff₀ (by linarith)).2 ?_)
    nlinarith [sq_nonneg (η * ε)]
  · exact (min_le_left _ _).trans (not_lt.1 hsmall)

/-- Let `cᵢ → z₀ ∈ Ω`, with `Ω` open, and `εᵢ → 0`. For `r > 0`, `a > 0` and constants `η` and
`B`, eventually the closed disc of radius `η εᵢ` about `cᵢ` lies in `B_r(z₀) ∩ Ω`,
`η² εᵢ² < a` and `B εᵢ ≤ 1`. -/
private theorem eventually_closedBall_subset_ball_inter_of_tendsto {ι : Type*} {l : Filter ι}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) {c : ι → ℝ × ℝ} {ε : ι → ℝ}
    (hc : Tendsto c l (𝓝 z₀)) (hε : Tendsto ε l (𝓝 0)) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (η B : ℝ) :
    ∀ᶠ i in l, closedBall (c i) (η * ε i) ⊆ ball z₀ r ∩ Ω ∧ η ^ 2 * ε i ^ 2 < a ∧ B * ε i ≤ 1 := by
  obtain ⟨s, hs, hsB⟩ := Metric.mem_nhds_iff.1 (inter_mem (ball_mem_nhds z₀ hr) (hΩ.mem_nhds hz₀))
  have h1 : Tendsto (fun i ↦ η * ε i) l (𝓝 0) := by simpa using hε.const_mul η
  have h2 : Tendsto (fun i ↦ η ^ 2 * ε i ^ 2) l (𝓝 0) := by
    simpa using (hε.pow 2).const_mul (η ^ 2)
  have h3 : Tendsto (fun i ↦ B * ε i) l (𝓝 0) := by simpa using hε.const_mul B
  filter_upwards [h1.eventually (gt_mem_nhds (half_pos hs)),
    hc.eventually (ball_mem_nhds z₀ (half_pos hs)), h2.eventually (gt_mem_nhds ha),
    h3.eventually (ge_mem_nhds one_pos)] with i h1 hci h2 h3
  refine ⟨fun y hy ↦ hsB (mem_ball.2 ?_), h2, h3⟩
  linarith [dist_triangle y (c i) z₀, mem_closedBall.1 hy, mem_ball.1 hci]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- If the rescaled map `w ↦ u(c + ε w)` has Floer energy density at most `a` for the rescaled
perturbation on the disc `‖w‖ ≤ R`, then `u` has Floer energy density at most `a / ε²` on the
closed disc of radius `ε R` about `c`. -/
private theorem floerEnergyDensity_le_div_sq_of_rescale (ω : SmoothTwoForm I M) {u : ℝ × ℝ → M}
    {c : ℝ × ℝ} {ε R a : ℝ} (hε : 0 < ε)
    (h : ∀ w : ℝ × ℝ, ‖w‖ ≤ R → ω.floerEnergyDensity (fun w x ↦ ε * Ks (c + ε • w) x)
      (fun w x ↦ ε * Kt (c + ε • w) x) (fun w ↦ u (c + ε • w)) w ≤ a)
    {y : ℝ × ℝ} (hy : dist y c ≤ ε * R) :
    ω.floerEnergyDensity Ks Kt u y ≤ a / ε ^ 2 := by
  have hyw : c + ε • (ε⁻¹ • (y - c)) = y := by
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul, add_sub_cancel]
  have hw : ‖ε⁻¹ • (y - c)‖ ≤ R := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le, ← dist_eq_norm, inv_mul_le_iff₀ hε]
    exact hy
  have h' := h _ hw
  rw [ω.floerEnergyDensity_rescale, hyw] at h'
  rw [le_div_iff₀ (pow_pos hε 2)]
  linarith

/-- **Energy concentrates where the energy density of Floer solutions in a manifold blows up.**
Let `ω`, `J`, `K_s`, `K_t`, `K` and `D ⊆ U` be as in
`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mem_of_dist_lt`. Let
`e : M → F` be differentiable at the points of `K` and injective on `K`, with the structures
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and the pushforwards
`d e (X_{K_s})` and `d e (X_{K_t})` at most `B` on `D × K`.

Then there is a threshold `δ > 0` with the following property. Let `uᵢ` be `C³` solutions of the
Floer equation `(du - X_{K_s} ds - X_{K_t} dt)^{0,1} = 0` on an open set `Ω ⊆ D` with values in
`K`, with continuous and integrable Floer energy densities `ρ(uᵢ)`. If `ρ(uᵢ)(zᵢ) → ∞` along points
`zᵢ → z₀ ∈ Ω`, then for every `r > 0`, eventually `δ ≤ ∫_{B_r(z₀) ∩ Ω} ρ(uᵢ)`. -/
theorem IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃ι : Type*⦄ ⦃l : Filter ι⦄ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ι → ℝ × ℝ → M⦄
      ⦃z : ι → ℝ × ℝ⦄ ⦃z₀ : ℝ × ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u i) Ω) → (∀ i, MapsTo (u i) Ω K) →
      (∀ i, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u i y))
        (ω.perturbedMFDeriv Ks Kt (u i) y).toLinearMap) →
      (∀ i, ContinuousOn (ω.floerEnergyDensity Ks Kt (u i)) Ω) →
      (∀ i, IntegrableOn (ω.floerEnergyDensity Ks Kt (u i)) Ω) →
      z₀ ∈ Ω → Tendsto z l (𝓝 z₀) →
      Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) (z i)) l atTop →
      ∀ r > 0, ∀ᶠ i in l, δ ≤ ∫ y in ball z₀ r ∩ Ω, ω.floerEnergyDensity Ks Kt (u i) y := by
  obtain ⟨δ, hδ, C, hC, θ, hθ, hmv⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_mem_of_dist_lt hU hDU hD hK hJ hXs hXt
      hJt (fun x hx ↦ (he x hx).continuousAt.continuousWithinAt) he_inj
  -- On discs of radius `η ε` with energy density at most `4 ε⁻²`, images move by less than `θ`.
  set η := θ / (4 * (4 / √c + 2))
  have hη : 0 < η := div_pos hθ (by positivity)
  have hηθ : η * (4 / √c + 2) < θ := by simp only [η]; field_simp; linarith
  -- The threshold.
  set δ₁ := min δ (η ^ 2 / (C + 1))
  have hδ₁ : 0 < δ₁ := lt_min hδ (div_pos (pow_pos hη 2) (by linarith))
  refine ⟨δ₁ / 2, half_pos hδ₁, fun ι l Ω u z z₀ hΩ hΩD hu huK hfl hcont hint hz₀ hz hblow r hr ↦
    ?_⟩
  -- Centres `cc i → z₀` and scales `ε i → 0` of bubbling analysis.
  obtain ⟨cc, ε, R, hε, hcc, hε0, hR, -, hev⟩ :=
    ω.exists_rescale_isComplexLinearMap_perturbedMFDeriv hΩ hz₀ hcont (Eventually.of_forall hfl)
      hz hblow
  filter_upwards [hev, hR.eventually_ge_atTop η,
    eventually_closedBall_subset_ball_inter_of_tendsto hΩ hz₀ hcc hε0 hr (half_pos hδ₁) η B]
    with i ⟨hcen, h4⟩ hηR ⟨hball, hηδ, hBε⟩
  set ρr := η * ε i with hρr_def
  have hρr : 0 ≤ ρr := (mul_pos hη (hε i)).le
  have hciΩ : cc i ∈ Ω := (hball (mem_closedBall_self hρr)).2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBs _ (hΩD hciΩ) _ (huK i hciΩ))
  -- The energy density is `ε i⁻²` at the centre and at most `4 ε i⁻²` on the disc.
  rw [ω.floerEnergyDensity_rescale, smul_zero, add_zero] at hcen
  have hdens : ∀ y ∈ closedBall (cc i) ρr, ω.floerEnergyDensity Ks Kt (u i) y ≤ 4 / ε i ^ 2 :=
    fun y hy ↦ ω.floerEnergyDensity_le_div_sq_of_rescale (hε i) (fun w hw ↦ (h4 w hw).2.1)
      ((mem_closedBall.1 hy).trans (by rw [hρr_def, mul_comm]; gcongr; exact (hε i).le))
  -- The mean-value inequality on the disc forces energy at least `δ₁ - ρr²` into it.
  set I₀ := ∫ y in ball (cc i) ρr, ω.floerEnergyDensity Ks Kt (u i) y
  have hkey : δ₁ ≤ ρr ^ 2 + I₀ :=
    hω.min_le_sq_add_setIntegral_floerEnergyDensity hC hΩ hΩD (hu i) (hfl i) (huK i) hJt he hc
      hB0 hJc hBs hBt (hε i) hη.le hηθ hBε (fun y hy ↦ (hball hy).2) hcen hdens
      fun hmove hsmall ↦ hmv hΩ hρr (fun y hy ↦ (hball hy).2) (fun y hy ↦ hΩD (hball hy).2)
        (hu i) (hfl i) hmove ((hint i).mono_set fun y hy ↦ (hball (ball_subset_closedBall hy)).2)
        hsmall
  have hmono : I₀ ≤ ∫ y in ball z₀ r ∩ Ω, ω.floerEnergyDensity Ks Kt (u i) y :=
    setIntegral_mono_set ((hint i).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ.measurableSet) fun y hy ↦
        floerEnergyDensity_nonneg hω (hJt y (hΩD hy.2) _) (hfl i y hy.2))
      (Eventually.of_forall fun y hy ↦ hball (ball_subset_closedBall hy))
  linarith [show ρr ^ 2 = η ^ 2 * ε i ^ 2 by rw [hρr_def, mul_pow]]

/-- **Floer solutions in a manifold converge off finitely many bubbling points.** Under the
hypotheses of `IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity` on
`ω`, `J`, the perturbation `K_s ds + K_t dt`, the compact set `K ⊆ M`, the compact window `D ⊆ U`
and the map `e : M → F`, there is a threshold `δ > 0` with the following property. Let `uₖ` be
`C³` solutions of the Floer equation `(du - X_{K_s} ds - X_{K_t} dt)^{0,1} = 0` on an open set
`Ω ⊆ D` with values in `K`, with continuous and integrable Floer energy densities `ρ(uₖ)` and Floer
energy `∫_Ω ρ(uₖ) ≤ A`. Then there are a subsequence `u_{φ n}` and a finite set `Z ⊆ Ω` of bubbling
points with `#Z δ ≤ A` such that

* energy at least `δ` concentrates at every point of `Z`: for `z ∈ Z` and `r > 0`, eventually
  `δ ≤ ∫_{B_r(z) ∩ Ω} ρ(u_{φ n})`;
* the energy densities `ρ(u_{φ n})` are uniformly bounded on every compact subset of `Ω \ Z`;
* the solutions converge on `Ω \ Z`, locally uniformly after applying `e` and pointwise in `M`,
  to a map `v` continuous on `Ω \ Z` with values in `K`. -/
theorem IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_mapsTo
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) → (∀ k, MapsTo (u k) Ω K) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
        (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap) →
      (∀ k, ContinuousOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ y in Ω, ω.floerEnergyDensity Ks Kt (u k) y ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ r > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z r ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y)) := by
  obtain ⟨δ, hδ, hconc⟩ := hω.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity hU
    hDU hD hK hJ hXs hXt hJt he he_inj hc hJc hBs hBt
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu huK hfl hcont hint hA ↦ ?_⟩
  -- Counting the points where energy concentrates.
  obtain ⟨φ, hφ, Z, hZΩ, hcard, hZ, hbd⟩ := exists_strictMono_finset_forall_le_of_concentration
    (μ := volume) (g := fun k ↦ ω.floerEnergyDensity Ks Kt (u k))
    (e := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)) hΩ.measurableSet hδ hcont
    (fun k y hy ↦ floerEnergyDensity_nonneg hω (hJt y (hΩD hy) _) (hfl k y hy)) hint hA
    fun ψ _ _ _ _ hz₀ hz hblow ↦ hconc hΩ hΩD (fun k ↦ hu (ψ k)) (fun k ↦ huK (ψ k))
      (fun k ↦ hfl (ψ k)) (fun k ↦ hcont (ψ k)) (fun k ↦ hint (ψ k)) hz₀ hz hblow
  -- Off the bubbling points the energy densities are locally bounded, so the solutions converge.
  obtain ⟨ψ, hψ, v, hv, hvK, hconv, hpt⟩ := hω.exists_strictMono_tendstoLocallyUniformlyOn_comp hK
    he he_inj (hΩ.sdiff Z.finite_toSet.isClosed) (u := fun n ↦ u (φ n)) (Ks := fun _ ↦ Ks)
    (Kt := fun _ ↦ Kt) (fun n y ↦ J y (u (φ n) y)) hc
    (fun n y hy ↦ ((hu (φ n)).mdifferentiableOn (by norm_num)).mdifferentiableAt
      (hΩ.mem_nhds hy.1))
    (fun n y hy ↦ huK (φ n) hy.1) (fun n y hy ↦ hJc y (hΩD hy.1) _ (huK _ hy.1))
    (fun n y hy ↦ hBs y (hΩD hy.1) _ (huK _ hy.1)) (fun n y hy ↦ hBt y (hΩD hy.1) _ (huK _ hy.1))
    (fun n y hy ↦ hfl (φ n) y hy.1) hbd
  exact ⟨φ ∘ ψ, hφ.comp hψ, Z, hZΩ, hcard,
    fun z hz r hr ↦ hψ.tendsto_atTop.eventually (hZ z hz r hr),
    fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ h n ↦ h (ψ n), v, hv, hvK, hconv, hpt⟩

omit [NormedSpace ℝ F] in
/-- **The limit near a point, read in a chart.** Let `uₙ` be smooth solutions of the Floer
equation on an open set `S ⊆ D` with values in `K`, with energy densities bounded on compact
subsets of `S`, converging to `v` on `S` locally uniformly through `e` and pointwise in `M`. If
`v y` lies in the source of the chart at `α`, then on a disc about `y` the coordinate expression
`extChartAt I α ∘ v` is a `C¹` solution of the coordinate Floer equation, and the derivatives of
`extChartAt I α ∘ uₙ` converge to its derivative locally uniformly. -/
private theorem IsNondegenerate.exists_ball_tendstoLocallyUniformlyOn_fderiv_extChartAt
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    {α : M}
    (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J) (U ×ˢ (extChartAt I α).target))
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks) (U ×ˢ (extChartAt I α).target))
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt) (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ContinuousOn e K) (he_inj : InjOn e K) {S : Set (ℝ × ℝ)} (hS : IsOpen S) (hSD : S ⊆ D)
    {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) S) (huK : ∀ n, MapsTo (u n) S K)
    (hfl : ∀ n, ∀ z ∈ S, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u n z))
      (ω.perturbedMFDeriv Ks Kt (u n) z).toLinearMap)
    (hbd : ∀ C, IsCompact C → C ⊆ S →
      ∃ A, ∀ n, ∀ z ∈ C, ω.floerEnergyDensity Ks Kt (u n) z ≤ A)
    (hv : ContinuousOn v S) (hvK : MapsTo v S K)
    (hconv : TendstoLocallyUniformlyOn (fun n ↦ e ∘ u n) (e ∘ v) atTop S)
    (hpt : ∀ z ∈ S, Tendsto (fun n ↦ u n z) atTop (𝓝 (v z)))
    {y : ℝ × ℝ} (hy : y ∈ S) (hyα : v y ∈ (extChartAt I α).source) :
    ∃ r > 0, ball y r ⊆ S ∧ MapsTo v (ball y r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball y r) ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball y r) ∧
      ∀ z ∈ ball y r, fderiv ℝ (extChartAt I α ∘ v) z stdComplexLineImag -
          ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ v) z) stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z, (extChartAt I α ∘ v) z)
          (fderiv ℝ (extChartAt I α ∘ v) z stdComplexLineReal -
            ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ v) z)
              stdComplexLineReal) := by
  set φ := extChartAt I α
  obtain ⟨κ, -, hKcT, r, hr, hcl, N, hN⟩ := hK.exists_closedBall_forall_mem_extChartAt_source he
    he_inj hS huK hv hvK hconv hy hyα
  have hvN {z : ℝ × ℝ} (hz : z ∈ closedBall y r) := (hN z hz).1
  have huN (n : ℕ) {z : ℝ × ℝ} (hz : z ∈ closedBall y r) :=
    (hN z hz).2 (n + N) (Nat.le_add_left N n)
  have hBS : ball y r ⊆ S := ball_subset_closedBall.trans hcl
  -- On the open disc, the tail `u (n + N)` is read in the chart at `α`.
  have hsmooth (n : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (φ ∘ u (n + N)) (ball y r) :=
    contMDiffOn_iff_contDiffOn.1 <| contMDiffOn_extChartAt.comp ((hu (n + N)).mono hBS)
      fun z hz ↦ by
        rw [mem_preimage, ← extChartAt_source I]
        exact (huN n (ball_subset_closedBall hz)).1
  have hchart (n : ℕ) := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub
    isOpen_ball (((hu (n + N)).mono hBS).of_le (by norm_cast)) (by norm_num)
    (fun z hz ↦ (huN n (ball_subset_closedBall hz)).1) fun z hz ↦ hfl (n + N) z (hBS hz)
  -- Bounds on the energy densities give bounds on the derivatives in the chart.
  have hbd' (C : Set (ℝ × ℝ)) (hC : IsCompact C) (hCB : C ⊆ ball y r) :
      ∃ L, ∀ n, ∀ z ∈ C, ‖fderiv ℝ (φ ∘ u (n + N)) z‖ ≤ L := by
    obtain ⟨A, hA⟩ := hbd C hC (hCB.trans hBS)
    obtain ⟨L, hL⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_le (Kt := Kt) α hD
      (isCompact_closedBall _ _) hKcT (hJ.continuousOn.mono (prod_mono hDU hKcT))
      (hXs.continuousOn.mono (prod_mono hDU hKcT)) (hXt.continuousOn.mono (prod_mono hDU hKcT))
      (fun z hz _ _ ↦ hJt z hz _) A
    have hzS {z : ℝ × ℝ} (hz : z ∈ C) : z ∈ S := hBS (hCB hz)
    exact ⟨L, fun n z hz ↦ hL (hSD (hzS hz)) (huN n (ball_subset_closedBall (hCB hz))).1
      (huN n (ball_subset_closedBall (hCB hz))).2
      (((hu (n + N)).mdifferentiableOn (by simp)).mdifferentiableAt (hS.mem_nhds (hzS hz)))
      (hfl (n + N) z (hzS hz)) (hA (n + N) z hz)⟩
  obtain ⟨hv1, hdconv, heq⟩ := Floer.tendstoLocallyUniformlyOn_fderiv_of_stdComplexLineImag_sub
    (J := Floer.almostComplexInChartAt I α J) (X := ω.hamiltonianOneFormInChartAt α Ks Kt)
    (hU.prod (isOpen_extChartAt_target α)) (hJ.of_le (by norm_num))
    ((contDiffOn_hamiltonianOneFormInChartAt hXs hXt).of_le (by norm_num)) isOpen_ball
    (u := fun n ↦ φ ∘ u (n + N)) (v := φ ∘ v)
    (fun z hz ↦ ⟨hDU (hSD (hBS hz)), φ.map_source (hvN (ball_subset_closedBall hz)).1⟩) hsmooth
    (fun n z hz w ↦ Floer.almostComplexInChartAt_apply_apply
      (φ.map_source (huN n (ball_subset_closedBall hz)).1) z w)
    (fun n ↦ (hchart n).2) hbd'
    (fun z hz ↦ (continuousAt_extChartAt' (hvN (ball_subset_closedBall hz)).1).tendsto.comp
      ((hpt z (hBS hz)).comp (tendsto_add_atTop_nat N)))
  refine ⟨r, hr, hBS, fun z hz ↦ (hvN (ball_subset_closedBall hz)).1, hv1, ?_, heq⟩
  -- Convergence of the tail is convergence of the sequence.
  intro s hs z hz
  obtain ⟨t, ht, hevt⟩ := hdconv s hs z hz
  exact ⟨t, ht, by rwa [← map_add_atTop_eq_nat N, eventually_map]⟩

/-- **Floer solutions in a manifold converge in `C¹` off finitely many bubbling points.** Under the
hypotheses of
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_mapsTo` on
`ω`, `J`, the perturbation `K_s ds + K_t dt`, the compact set `K ⊆ M`, the compact window `D ⊆ U`
and the map `e : M → F`, there is a threshold `δ > 0` with the following property. Let `uₖ` be
smooth solutions of the Floer equation `(du - X_{K_s} ds - X_{K_t} dt)^{0,1} = 0` on an open set
`Ω ⊆ D` with values in `K`, with continuous and integrable Floer energy densities `ρ(uₖ)` and Floer
energy `∫_Ω ρ(uₖ) ≤ A`. Then there are a subsequence `u_{φ n}` and a finite set `Z ⊆ Ω` of
bubbling points with `#Z δ ≤ A` such that

* energy at least `δ` concentrates at every point of `Z`: for `z ∈ Z` and `r > 0`, eventually
  `δ ≤ ∫_{B_r(z) ∩ Ω} ρ(u_{φ n})`;
* the energy densities `ρ(u_{φ n})` are uniformly bounded on every compact subset of `Ω \ Z`;
* the solutions converge on `Ω \ Z`, locally uniformly through `e` and pointwise in `M`, to a map
  `v` which is `C¹` on `Ω \ Z` with values in `K`;
* the convergence holds in `C¹`: for every `α ∈ K`, the derivatives of the coordinate expressions
  `extChartAt I α ∘ u_{φ n}` converge to the derivative of `extChartAt I α ∘ v` locally uniformly
  on the open set of points of `Ω \ Z` at which `v` lies in the source of the chart at `α`;
* `v` solves the Floer equation on `Ω \ Z`.

Unlike `IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`, the
solutions are not required to stay in a single chart. -/
theorem
    IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_of_mapsTo
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) → (∀ k, MapsTo (u k) Ω K) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
        (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap) →
      (∀ k, ContinuousOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ y in Ω, ω.floerEnergyDensity Ks Kt (u k) y ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ r > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z r ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
          (∀ α ∈ K, TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u (φ n)))
            (fderiv ℝ (extChartAt I α ∘ v)) atTop
            ((Ω \ ↑Z) ∩ v ⁻¹' (extChartAt I α).source)) ∧
          ∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (v y))
            (ω.perturbedMFDeriv Ks Kt v y).toLinearMap := by
  obtain ⟨δ, hδ, h0⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_mapsTo hU hDU hD hK
      hJ hXs hXt hJt he he_inj hc hJc hBs hBt
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu huK hfl hcont hint hA ↦ ?_⟩
  obtain ⟨φ, hφ, Z, hZΩ, hcard, hconc, hbd, v, hv, hvK, hconv, hpt⟩ :=
    h0 hΩ hΩD (fun k ↦ (hu k).of_le (by norm_cast)) huK hfl hcont hint hA
  set S := Ω \ (Z : Set (ℝ × ℝ))
  have hS : IsOpen S := hΩ.sdiff Z.finite_toSet.isClosed
  -- Near every point of `S`, the limit is read in the chart at any point of `K` whose source
  -- contains its value.
  have hloc {α : M} (hα : α ∈ K) {y : ℝ × ℝ} (hy : y ∈ S) (hyα : v y ∈ (extChartAt I α).source) :=
    hω.exists_ball_tendstoLocallyUniformlyOn_fderiv_extChartAt (u := fun n ↦ u (φ n)) hU hDU hD
      hK (hJ α hα) (hXs α hα) (hXt α hα) hJt (fun x hx ↦ (he x hx).continuousAt.continuousWithinAt)
      he_inj hS (sdiff_subset.trans hΩD) (fun n ↦ (hu (φ n)).mono sdiff_subset)
      (fun n ↦ (huK (φ n)).mono_left sdiff_subset) (fun n z hz ↦ hfl (φ n) z hz.1) hbd hv hvK
      hconv hpt hy hyα
  -- So the limit is `C¹` on `S`, and the derivatives converge in each chart.
  obtain ⟨hvC1, hdconv⟩ :=
    contMDiffOn_and_tendstoLocallyUniformlyOn_fderiv_extChartAt_comp_of_forall_exists_ball hS hv
      hvK (Q := fun n ↦ u (φ n)) fun α hα y hy hyα ↦
        (hloc hα hy hyα).imp fun _ ⟨hr, _, h₁, h₂, h₃, _⟩ ↦ ⟨hr, h₁, h₂, h₃⟩
  refine ⟨φ, hφ, Z, hZΩ, hcard, hconc, hbd, v, hvC1, hvK, hconv, hpt, hdconv, fun y hy ↦ ?_⟩
  -- In the chart at `v y`, the limit solves the Floer equation at `y`.
  obtain ⟨r, hr, -, -, -, -, heq⟩ := hloc (hvK hy) hy (mem_extChartAt_source (v y))
  refine (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
    (((hvC1 y hy).contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt one_ne_zero)
    (mem_extChartAt_source (v y))).2 ?_
  simpa only [hamiltonianOneFormInChartAt_stdComplexLineReal,
    hamiltonianOneFormInChartAt_stdComplexLineImag, Function.comp_apply] using
    heq y (mem_ball_self hr)


omit [FiniteDimensional ℝ E] in
/-- **The energy density is a continuous function of the jet in a chart.** If the Hamiltonian
vector fields of `K_s` and `K_t` read in the chart at `α` are continuous on
`U × (extChartAt I α).target`, there is a function `G`, continuous at every `(z, y, L)` at which
`U × (extChartAt I α).target` is a neighbourhood of `(z, y)`, such that the Floer energy density
of every map `w` differentiable at `z`, with `w z` in the chart source, is
`G (z, χ (w z), d (χ ∘ w) z)` for `χ = extChartAt I α`. -/
private theorem exists_forall_continuousAt_and_floerEnergyDensity_eq {α : M}
    (hXs : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks) (U ×ˢ (extChartAt I α).target))
    (hXt : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Kt) (U ×ˢ (extChartAt I α).target)) :
    ∃ G : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) → ℝ,
      (∀ p, U ×ˢ (extChartAt I α).target ∈ 𝓝 (p.1, p.2.1) → ContinuousAt G p) ∧
      ∀ ⦃w : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I w z →
        w z ∈ (extChartAt I α).source → ω.floerEnergyDensity Ks Kt w z =
          G (z, extChartAt I α (w z), fderiv ℝ (extChartAt I α ∘ w) z) := by
  set Xs := ω.hamiltonianVectorFieldInChartAt α Ks
  set Xt := ω.hamiltonianVectorFieldInChartAt α Kt
  refine ⟨fun p ↦ ContinuousAlternatingMap.flatL ℝ E ℝ
      (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α p.2.1)
      (p.2.2 stdComplexLineReal - Xs (p.1, p.2.1)) (p.2.2 stdComplexLineImag - Xt (p.1, p.2.1)),
    fun p hpn ↦ ?_, fun w z hw hwz ↦ ?_⟩
  · have hq : Continuous fun p : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) ↦ (p.1, p.2.1) :=
      continuous_fst.prodMk continuous_snd.fst
    -- The two perturbed derivatives in the chart are continuous at `p`.
    have hX {X : (ℝ × ℝ) × E → E} (hX : ContinuousOn X (U ×ˢ (extChartAt I α).target))
        (v : ℝ × ℝ) :
        ContinuousAt (fun p : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) ↦ p.2.2 v - X (p.1, p.2.1)) p :=
      (continuous_snd.snd.clm_apply continuous_const).continuousAt.sub
        (ContinuousAt.comp (g := X) (f := fun p : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) ↦ (p.1, p.2.1))
          (hX.continuousAt hpn) hq.continuousAt)
    have hω : ContinuousAt (fun p : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) ↦
        ContinuousAlternatingMap.flatL ℝ E ℝ
          (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α p.2.1)) p :=
      (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.continuousAt.comp
        (ContinuousAt.comp (f := fun p : (ℝ × ℝ) × E × (ℝ × ℝ →L[ℝ] E) ↦ p.2.1)
          ((ω.isSmoothForm.continuousOn_inChartAt α).continuousAt
            ((isOpen_extChartAt_target α).mem_nhds (mem_of_mem_nhds hpn).2))
          continuous_snd.fst.continuousAt)
    exact (hω.clm_apply (hX hXs _)).clm_apply (hX hXt _)
  · rw [ω.floerEnergyDensity_eq_inChartAt_sub hw hwz]
    exact (ContinuousAlternatingMap.flatL_apply_apply _ _ _).symm

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- **The energy densities converge where maps converge in `C¹`.** Let the Hamiltonian vector
fields of `K_s` and `K_t`, read in the chart at every point of a compact set `K ⊆ M`, be continuous
on `U × (extChartAt I x).target`, and let `e : M → F` be continuous and injective on `K`. Let `uₙ`
be differentiable and `v` be `C¹` on an open set `S ⊆ U`, with values in `K`, such that `uₙ → v` on
`S` locally uniformly through `e`, and such that for every `α ∈ K` the derivatives of the
coordinate expressions `extChartAt I α ∘ uₙ` converge to that of `extChartAt I α ∘ v` locally
uniformly where `v` lies in the chart source. Then the Floer energy densities `ρ(uₙ)` converge to
`ρ(v)` locally uniformly on `S`. No Floer equation is assumed. -/
theorem tendstoLocallyUniformlyOn_floerEnergyDensity_of_mapsTo (hK : IsCompact K)
    (hXs : ∀ x ∈ K,
      ContinuousOn (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContinuousOn (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (he : ContinuousOn e K) (he_inj : InjOn e K) {S : Set (ℝ × ℝ)} (hS : IsOpen S) (hSU : S ⊆ U)
    {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hu : ∀ n, MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I (u n) S) (huK : ∀ n, MapsTo (u n) S K)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v S) (hvK : MapsTo v S K)
    (hconv : TendstoLocallyUniformlyOn (fun n ↦ e ∘ u n) (e ∘ v) atTop S)
    (hdconv : ∀ α ∈ K, TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
      (fderiv ℝ (extChartAt I α ∘ v)) atTop (S ∩ v ⁻¹' (extChartAt I α).source)) :
    TendstoLocallyUniformlyOn (fun n ↦ ω.floerEnergyDensity Ks Kt (u n))
      (ω.floerEnergyDensity Ks Kt v) atTop S := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun y hy ↦ ?_
  set χ := extChartAt I (v y)
  obtain ⟨r, hr, N, hBS, hsrc, hjet, hc, hd⟩ :=
    hK.exists_closedBall_tendstoUniformlyOn_extChartAt_comp he he_inj hS hu huK hv hvK hconv hy
      (hdconv (v y) (hvK hy))
  -- In the chart at `v y` the energy density is a continuous function `G` of the jet.
  obtain ⟨G, hGc, hG⟩ := exists_forall_continuousAt_and_floerEnergyDensity_eq (ω := ω) (U := U)
    (hXs (v y) (hvK hy)) (hXt (v y) (hvK hy))
  have hGu := ((isCompact_closedBall y r).image_of_continuousOn hjet).comp_tendstoUniformlyOn
    (g := G) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hGc _ (mem_of_superset ((hS.prod (isOpen_extChartAt_target (v y))).mem_nhds
        ⟨hBS hz, χ.map_source (hsrc z hz).1⟩) (prod_mono hSU subset_rfl)))
    ((hc.prodMk_same hd).graph)
  refine ⟨closedBall y r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds y hr), ?_⟩
  rw [← map_add_atTop_eq_nat N, TauCeti.tendstoUniformlyOn_map_iff]
  refine (hGu.congr (.of_forall fun n z hz ↦ ?_)).congr_right fun z hz ↦ ?_
  · exact (hG ((hu (n + N)).mdifferentiableAt (hS.mem_nhds (hBS hz))) ((hsrc z hz).2 n)).symm
  · exact (hG ((hv.mdifferentiableOn (by norm_num)).mdifferentiableAt (hS.mem_nhds (hBS hz)))
      (hsrc z hz).1).symm

namespace IsNondegenerate

/-- **The energy of the limit and of the bubbling points.** In the situation of
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_of_mapsTo`,
for Floer solutions in a manifold that need not stay in a single chart, a further subsequence `φ`
attaches to every bubbling point `z ∈ Z` a mass `m z ≥ δ`: for every small `ε > 0` the Floer energy
of `u_{φ n}` over the disc `B_ε(z)` converges to `m z` plus the energy of the limit `v` over the
punctured disc. The energy densities of the `u_{φ n}` converge to that of `v` locally uniformly on
`Ω \ Z`, the energy of `v` over `Ω \ Z` is finite, and together with the masses it is at most `A`,
so no energy is created in the limit. -/
theorem exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset_of_mapsTo
    (hω : ω.IsNondegenerate) (hU : IsOpen U) (hDU : D ⊆ U) (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ∀ x ∈ K,
      ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I x J) (U ×ˢ (extChartAt I x).target))
    (hXs : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Ks) (U ×ˢ (extChartAt I x).target))
    (hXt : ∀ x ∈ K,
      ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt x Kt) (U ×ˢ (extChartAt I x).target))
    (hJt : ∀ z ∈ D, ∀ y, (hω.symplecticFormAt y).Tames (J z y))
    (he : ∀ x ∈ K, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : InjOn e K) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x ∈ K, ∀ v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x ∈ K, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) → (∀ k, MapsTo (u k) Ω K) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
        (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap) →
      (∀ k, ContinuousOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ y in Ω, ω.floerEnergyDensity Ks Kt (u k) y ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M) (m : ℝ × ℝ → ℝ), StrictMono φ ∧
        ↑Z ⊆ Ω ∧
        (∀ z ∈ Z, ∀ r > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z r ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
        (∀ α ∈ K, TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u (φ n)))
          (fderiv ℝ (extChartAt I α ∘ v)) atTop ((Ω \ ↑Z) ∩ v ⁻¹' (extChartAt I α).source)) ∧
        (∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (v y))
          (ω.perturbedMFDeriv Ks Kt v y).toLinearMap) ∧
        TendstoLocallyUniformlyOn (fun n ↦ ω.floerEnergyDensity Ks Kt (u (φ n)))
          (ω.floerEnergyDensity Ks Kt v) atTop (Ω \ ↑Z) ∧
        IntegrableOn (ω.floerEnergyDensity Ks Kt v) (Ω \ ↑Z) ∧
        (∀ z ∈ Z, δ ≤ m z) ∧
        (∀ z ∈ Z, ∀ᶠ ε in 𝓝[>] 0,
          Tendsto (fun n ↦ ∫ y in ball z ε, ω.floerEnergyDensity Ks Kt (u (φ n)) y) atTop
            (𝓝 (m z + ∫ y in ball z ε \ {z}, ω.floerEnergyDensity Ks Kt v y))) ∧
        (∫ y in Ω \ ↑Z, ω.floerEnergyDensity Ks Kt v y) + ∑ z ∈ Z, m z ≤ A := by
  obtain ⟨δ, hδ, h1⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_of_mapsTo hU hDU hD hK
      hJ hXs hXt hJt he he_inj hc hJc hBs hBt
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu huK hfl hcont hint hA ↦ ?_⟩
  obtain ⟨φ, hφ, Z, hZΩ, -, hconc, -, v, hv, hvK, hconv, hpt, hdconv, hveq⟩ :=
    h1 hΩ hΩD hu huK hfl hcont hint hA
  have hS : IsOpen (Ω \ (Z : Set (ℝ × ℝ))) := hΩ.sdiff Z.finite_toSet.isClosed
  have hnn (n : ℕ) (y : ℝ × ℝ) (hy : y ∈ Ω) : 0 ≤ ω.floerEnergyDensity Ks Kt (u (φ n)) y :=
    floerEnergyDensity_nonneg hω (hJt y (hΩD hy) _) (hfl (φ n) y hy)
  -- The energy densities converge locally uniformly off the bubbling points.
  have hdens := tendstoLocallyUniformlyOn_floerEnergyDensity_of_mapsTo hK
    (fun x hx ↦ (hXs x hx).continuousOn) (fun x hx ↦ (hXt x hx).continuousOn)
    (fun x hx ↦ (he x hx).continuousAt.continuousWithinAt) he_inj hS
    (sdiff_subset.trans (hΩD.trans hDU))
    (fun n ↦ ((hu (φ n)).mono sdiff_subset).mdifferentiableOn (by simp))
    (fun n ↦ (huK (φ n)).mono_left sdiff_subset) hv hvK hconv hdconv
  -- The energy of `v` over `Ω \ Z` is finite, and the bubbling points carry masses at least `δ`.
  obtain ⟨ψ, m, hψ, hint_v, hconcψ, hδm, hm, hmE⟩ :=
    exists_strictMono_tendsto_setIntegral_ball_and_setIntegral_add_sum_le_of_concentration hΩ hZΩ
      hnn (fun n ↦ hint (φ n)) (fun n ↦ hA (φ n)) hdens hconc
  exact ⟨φ ∘ ψ, Z, v, m, hφ.comp hψ, hZΩ, hconcψ, hv, hvK,
    hconv.comp_tendsto hψ.tendsto_atTop, fun y hy ↦ (hpt y hy).comp hψ.tendsto_atTop,
    fun α hα ↦ (hdconv α hα).comp_tendsto hψ.tendsto_atTop, hveq,
    hdens.comp_tendsto hψ.tendsto_atTop, hint_v, hδm, hm, hmE⟩

end IsNondegenerate

end TauCeti.SmoothTwoForm
