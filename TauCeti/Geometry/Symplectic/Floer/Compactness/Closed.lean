/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue
public import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
import TauCeti.Analysis.Hofer
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Topology.MetricSpace.Lebesgue

/-!
# Compactness of Floer solutions in a closed manifold off finitely many points

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold, and let `u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` for a
perturbation `K = K_s ds + K_t dt` and domain-dependent almost complex structures `J(z, x)` tamed by
`ω`. The compactness theorems of `TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold` and the
mean-value inequality of `TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue` hold for
solutions whose images stay in one chart. This file removes that condition: a sequence of solutions
of bounded energy, with arbitrary images in `M`, converges off finitely many bubbling points.

Sizes in `M` are measured through an injective map `e : M → F` into a normed space, such as the
Whitney embedding of a closed manifold
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`), as in
`TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity`. The data are read in the charts
of `M`, where they are assumed `C²`; for the Hamiltonian vector fields this holds as soon as the
Hamiltonians are `C³` (`IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`). The results
are in the namespace `TauCeti.SmoothTwoForm`.

* **The mean-value inequality on a closed manifold.** Since `e` embeds the compact space `M`, a
  Lebesgue number `l` of a finite cover of `e(M)` by images of chart pieces places every set
  whose image under `e` has radius less than `l` in one chart piece. So a closed disc
  `closedBall z₀ r` whose image under `e ∘ u` lies within `l` of `e(u(z₀))` satisfies the
  mean-value inequality in a chart, with constants uniform over the finite cover:
  `r² ρ(z₀) ≤ C (r² + ∫_{B_r(z₀)} ρ)` once `r² + ∫_{B_r(z₀)} ρ` is small, for the Floer energy
  density `ρ = ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})`
  (`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt`).
* **Energy concentration at blow-up points.** If the densities `ρᵢ` of solutions `uᵢ` blow up at
  points `zᵢ → z₀`, every disc about `z₀` eventually carries energy at least a fixed `δ > 0`
  (`IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity_ball`).
  Hofer's lemma (`TauCeti.exists_tendsto_hofer`) applied to `√ρᵢ` gives centres `cᵢ → z₀` with
  `ρᵢ ≤ 4 Nᵢ²` on discs of radii `sᵢ`, where `Nᵢ² = ρᵢ(cᵢ) → ∞` and `sᵢ Nᵢ → ∞`. On the disc of
  radius `rᵢ = σ / Nᵢ` about `cᵢ` the derivative of `e ∘ uᵢ` is then of order `Nᵢ`
  (`IsNondegenerate.norm_fderiv_comp_le`), so for a small fixed `σ` its image under `e ∘ uᵢ` has
  radius less than `l`. The mean-value inequality on that disc reads
  `σ² = rᵢ² ρᵢ(cᵢ) ≤ C (rᵢ² + ∫_{B_{rᵢ}(cᵢ)} ρᵢ)`. Since `rᵢ → 0`, the energy of the disc, and
  hence of every disc about `z₀`, is eventually at least a threshold `δ` small compared with
  `σ² / C`.
* **Compactness off finitely many points.** A sequence of solutions on an open set `Ω` with Floer
  energy at most `E₀` has a subsequence converging off a finite set `Z ⊆ Ω` of bubbling points with
  `#Z * δ ≤ E₀`: energy at least `δ` concentrates at every point of `Z`, the energy densities are
  bounded on compact subsets of `Ω \ Z`, and the solutions converge there to a continuous map,
  locally uniformly after applying `e` and pointwise in `M`
  (`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`).
  The counting argument is `TauCeti.exists_strictMono_finset_forall_le_of_concentration`, and the
  convergence where the densities are bounded is
  `IsNondegenerate.exists_strictMono_tendstoLocallyUniformlyOn_comp`.

**Compact parameter windows.** All of this holds uniformly over a compact window `C` of
parameters `p` in a finite-dimensional normed space `P`, for data `J_p`, `K_{s,p}`, `K_{t,p}` that
are jointly `C²` in the parameter, the domain point and the chart coordinate: one threshold `δ`
serves every parameter of `C`, and the subsequence can be chosen so that its parameters converge
in `C`
(`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset`).
The constants of the mean-value inequality in each chart are uniform over the window
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric`), and
the convergence where the densities are bounded already allows the data to vary along the sequence.
This is the compactness statement for the one-parameter families of Floer data, such as
continuation homotopies and the comparison families of products, whose boundary counts give chain
homotopies. A single datum is the constant family over a one-point window
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`).

The bubbles at the points of `Z`, the regularity of the limit and breaking along cylindrical ends
are not treated.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality), Section 4.6 (bubbling off finitely many points) and Section 8.1
  (inhomogeneous equations).
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {ω : SmoothTwoForm I M} {Ks Kt : P → ℝ × ℝ → M → ℝ}
  {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- A finite atlas adapted to the mean-value inequality over a compact parameter window: there
are `l > 0` and constants `δ`, `C` such that for every `x` the points whose images under `e` are
within `l` of `e x` lie in the source of one chart, with coordinates in a compact set `K` on which
the mean-value inequality in the chart
(`IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric`) holds
with these constants for every parameter of the window. -/
private theorem IsNondegenerate.exists_pos_forall_exists_chart_mean_value
    (hω : ω.IsNondegenerate) {X : Type*} [MetricSpace X] {e : M → X} (he : Continuous e)
    (he_inj : Injective e) {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ l > 0, ∃ δ > 0, ∃ C' ≥ 0, ∀ x : M, ∃ α : M, ∃ K : Set E,
      (∀ y, dist (e y) (e x) < l → y ∈ (extChartAt I α).source ∩ extChartAt I α ⁻¹' K) ∧
      ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃z₀ : ℝ × ℝ⦄ ⦃r : ℝ⦄, p ∈ C → 0 ≤ r → ball z₀ r ⊆ D →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u (ball z₀ r) →
        ContinuousOn (fun y ↦ fderiv ℝ (extChartAt I α ∘ u) y stdComplexLineReal)
          (closedBall z₀ r) →
        (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p y (u y))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u y).toLinearMap) →
        MapsTo u (ball z₀ r) ((extChartAt I α).source ∩ extChartAt I α ⁻¹' K) →
        IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (ball z₀ r) →
        r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y < δ →
        r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u z₀ ≤
          C' * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, one_pos, 1, one_pos, 0, le_rfl, fun x ↦ (IsEmpty.false x).elim⟩
  -- About the chart point of every `α`, a closed ball of chart coordinates in the chart target,
  -- on which the mean-value inequality in the chart at `α` holds.
  have hrad (α : M) : ∃ ρ > 0, closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) α) _
      (mem_extChartAt_target (I := I) α)
    exact ⟨ρ / 2, half_pos hρ, (closedBall_subset_ball (half_lt_self hρ)).trans hsub⟩
  choose ρ hρ hρt using hrad
  have hmv (α : M) := hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_small_energy_parametric
    α (hW.prod (isOpen_extChartAt_target (I := I) α)) (hJ α) (hXs α) (hXt α) hC hD
    (isCompact_closedBall _ _) (hρt α) (prod_mono hCDW (hρt α))
    fun p hp z hz _ _ ↦ hJt p hp z hz _
  choose δ' hδ' C' hC' hmv using hmv
  -- Finitely many of the open pieces `O α` of the charts cover `M`, and a Lebesgue number for
  -- them through the embedding `e` localizes small images.
  set O : M → Set M := fun α ↦
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' ball (extChartAt I α α) (ρ α)
  have hO (α : M) : IsOpen (O α) := (continuousOn_extChartAt (I := I) α).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) α) isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO fun x _ ↦
    mem_iUnion.2 ⟨x, mem_extChartAt_source (I := I) x, mem_ball_self (hρ x)⟩
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := hM
    obtain ⟨α, hα, -⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact ⟨α, hα⟩
  obtain ⟨l, hl, hleb⟩ := exists_pos_forall_exists_forall_dist_lt_mem he he_inj
    (W := fun α : t ↦ O α) (fun α ↦ hO α) fun x _ ↦ by
      obtain ⟨α, hαt, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact mem_iUnion.2 ⟨⟨α, hαt⟩, hx⟩
  refine ⟨l, hl, t.inf' htne δ', (Finset.lt_inf'_iff htne).2 fun α _ ↦ hδ' α,
    ∑ α ∈ t, C' α, Finset.sum_nonneg fun α _ ↦ hC' α, fun x ↦ ?_⟩
  obtain ⟨⟨α, hαt⟩, hα⟩ := hleb x
  refine ⟨α, closedBall (extChartAt I α α) (ρ α), fun y hy ↦
    inter_subset_inter_right _ (preimage_mono ball_subset_closedBall) (hα y hy),
    fun p u z₀ r hp hr hrD hu hcont hfl hmaps hint hE ↦ ?_⟩
  have hI0 : 0 ≤ r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y :=
    add_nonneg (sq_nonneg r) (setIntegral_nonneg measurableSet_ball fun y hy ↦
      floerEnergyDensity_nonneg hω (hJt p hp y (hrD hy) _) (hfl y hy))
  calc r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u z₀
      ≤ C' α * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y) :=
        hmv α hp hr hrD hu hcont hfl hmaps hint (hE.trans_le (Finset.inf'_le _ hαt))
    _ ≤ (∑ α ∈ t, C' α) * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun α _ ↦ hC' α) hαt) hI0

/-- **The mean-value inequality for Floer solutions in a closed manifold, over a compact parameter
window.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`. Let the
structures `J_p(z, x)` and the Hamiltonian vector fields of `K_{s,p}` and `K_{t,p}` depend on a
parameter `p` of a finite-dimensional normed space `P`, and, read in the chart at every point `α`,
be jointly `C²` on `W × (extChartAt I α).target` for an open set `W ⊆ P × (ℝ × ℝ)` containing
`C × D`, for a compact window `C` of parameters and a compact window `D` of the domain, with
`J_p(z, x)` tamed by `ω` for `p ∈ C` and `z ∈ D`. Let `e : M → X` be a continuous injective map into
a metric space, such as an embedding into a Euclidean space. There are `l > 0`, a threshold `δ > 0`
and a constant `C'`, the same for every parameter `p ∈ C`, with the following property. Let `u` be
`C³` on an open set `Ω` containing the closed ball `closedBall z₀ r ⊆ D` of `ℝ × ℝ` and solve the
Floer equation `(du - X_{K_p})^{0,1} = 0` for `J_p(z, u)` on the open ball, and let `e(u(y))` lie
within `l` of `e(u(z₀))` for `y ∈ closedBall z₀ r`. If the Floer energy density
`ρ = ω(∂ₛu - X_{K_{s,p}}, ∂ₜu - X_{K_{t,p}})` of `u` is integrable on the open ball `B_r(z₀)` and
`r² + ∫_{B_r(z₀)} ρ < δ`, then

`r² ρ(z₀) ≤ C' (r² + ∫_{B_r(z₀)} ρ)`.

Balls of `ℝ × ℝ` are squares for its sup norm. For a single datum, take a one-point parameter
space. -/
theorem IsNondegenerate.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt
    (hω : ω.IsNondegenerate) {X : Type*} [MetricSpace X] {e : M → X} (he : Continuous e)
    (he_inj : Injective e) {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ l > 0, ∃ δ > 0, ∃ C' ≥ 0, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃z₀ : ℝ × ℝ⦄
      ⦃r : ℝ⦄, p ∈ C → IsOpen Ω → 0 ≤ r → closedBall z₀ r ⊆ Ω → closedBall z₀ r ⊆ D →
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ ball z₀ r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p y (u y))
        (ω.perturbedMFDeriv (Ks p) (Kt p) u y).toLinearMap) →
      (∀ y ∈ closedBall z₀ r, dist (e (u y)) (e (u z₀)) < l) →
      IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) (ball z₀ r) →
      r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y < δ →
      r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u z₀ ≤
        C' * (r ^ 2 + ∫ y in ball z₀ r, ω.floerEnergyDensity (Ks p) (Kt p) u y) := by
  obtain ⟨l, hl, δ, hδ, C', hC', hchart⟩ :=
    hω.exists_pos_forall_exists_chart_mean_value he he_inj hW hC hD hCDW hJ hXs hXt hJt
  refine ⟨l, hl, δ, hδ, C', hC', fun p u Ω z₀ r hp hΩ hr hrΩ hrD hu hfl hdist hint hE ↦ ?_⟩
  obtain ⟨α, K, hK, hmv⟩ := hchart (u z₀)
  have huK {y : ℝ × ℝ} (hy : y ∈ closedBall z₀ r) := hK _ (hdist y hy)
  -- The derivative of the coordinate expression is continuous on the open set of points of `Ω`
  -- mapped into the chart source, which contains the closed ball.
  set V := Ω ∩ u ⁻¹' (extChartAt I α).source
  have hV : IsOpen V :=
    hu.continuousOn.isOpen_inter_preimage hΩ (isOpen_extChartAt_source (I := I) α)
  have hcd : ContDiffOn ℝ 3 (extChartAt I α ∘ u) V :=
    contMDiffOn_iff_contDiffOn.1 <| (contMDiffOn_extChartAt (n := 3)).comp
      (hu.mono inter_subset_left) fun y hy ↦ by
        rw [mem_preimage, ← extChartAt_source I]
        exact hy.2
  have hcont : ContinuousOn (fun y ↦ fderiv ℝ (extChartAt I α ∘ u) y stdComplexLineReal)
      (closedBall z₀ r) :=
    ((hcd.continuousOn_fderiv_of_isOpen hV (by norm_num)).clm_apply continuousOn_const).mono
      fun y hy ↦ ⟨hrΩ hy, (huK hy).1⟩
  exact hmv hp hr (ball_subset_closedBall.trans hrD)
    (hu.mono (ball_subset_closedBall.trans hrΩ)) hcont hfl
    (fun y hy ↦ huK (ball_subset_closedBall hy)) hint hE

/-- The arithmetic of the radius `σ / N`, for `σ = l / (2 (2 √(4 / c) + 1))`: the Lipschitz
constant `2 (√(4 N² / c) + B)` of `e ∘ u` on a disc where the density is at most `4 N²`, times the
radius, is less than `l` once `2 B ≤ N`. -/
private theorem two_mul_sqrt_add_mul_div_lt {c N B l : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hBN : 2 * B ≤ N) (hl : 0 < l) :
    2 * (√(4 * N ^ 2 / c) + B) * (l / (2 * (2 * √(4 / c) + 1)) / N) < l := by
  set σ := l / (2 * (2 * √(4 / c) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have hsq : √(4 * N ^ 2 / c) = √(4 / c) * N := by
    rw [show 4 * N ^ 2 / c = 4 / c * N ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hN.le]
  have hBr : 2 * B * (σ / N) ≤ σ := by
    rw [← mul_div_assoc, div_le_iff₀ hN]
    nlinarith
  have hNr : √(4 / c) * N * (σ / N) = √(4 / c) * σ := by field_simp
  have hσK : (2 * √(4 / c) + 1) * σ = l / 2 := by
    rw [hσ]
    field_simp
  rw [hsq]
  nlinarith

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [FiniteDimensional ℝ P] in
/-- The Hamiltonian vector field of one member `K_p` of a family, read in a chart, is continuous
where the family read in the chart is `C²` jointly in the parameter. -/
private theorem continuousOn_hamiltonianVectorFieldInChartAt_apply {K : P → ℝ × ℝ → M → ℝ}
    {α : M} {W : Set (P × (ℝ × ℝ))} {Ω : Set (ℝ × ℝ)} {p : P}
    (hX : ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (K q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hΩ : ∀ y ∈ Ω, (p, y) ∈ W) :
    ContinuousOn (ω.hamiltonianVectorFieldInChartAt α (K p)) (Ω ×ˢ (extChartAt I α).target) :=
  hX.continuousOn.comp (by fun_prop : Continuous fun y : (ℝ × ℝ) × E ↦ ((p, y.1), y.2)).continuousOn
    fun y hy ↦ ⟨hΩ y.1 hy.1, hy.2⟩

/-- Energy on the discs of Hofer's lemma, over a compact parameter window. There are `σ > 0`,
`δ > 0` and `κ > 0` with the following property, for every parameter `p ∈ C`. Let `N = √ρ(z₀)` for
the Floer energy density `ρ` of a solution `u` for `K_p` and `J_p`, with `N > 0` and `2 B ≤ N`, and
let `√ρ ≤ 2 N` on the closed disc of radius `σ / N` about `z₀`. If the radius is small,
`(σ / N)² < κ`, then every set `T ⊆ Ω` containing the disc carries energy `∫_T ρ ≥ δ`. Indeed the
image of the disc under `e ∘ u` is small enough for the mean-value inequality on a closed manifold,
which would otherwise bound `σ² = (σ / N)² ρ(z₀)` by `C ((σ / N)² + ∫_T ρ) < σ²`. -/
private theorem IsNondegenerate.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le
    (hω : ω.IsNondegenerate) {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J p z x)) {c B : ℝ}
    (hc : 0 < c)
    (hJc : ∀ p ∈ C, ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J p z x v))
    (hBs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks p z) x)‖ ≤ B)
    (hBt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt p z) x)‖ ≤ B) :
    ∃ σ > 0, ∃ δ > 0, ∃ κ > 0, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃Ω T : Set (ℝ × ℝ)⦄ ⦃z₀ : ℝ × ℝ⦄
      ⦃N : ℝ⦄, p ∈ C → IsOpen Ω → Ω ⊆ D → ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω →
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p y (u y))
        (ω.perturbedMFDeriv (Ks p) (Kt p) u y).toLinearMap) →
      MeasurableSet T → T ⊆ Ω → IntegrableOn (ω.floerEnergyDensity (Ks p) (Kt p) u) T →
      √(ω.floerEnergyDensity (Ks p) (Kt p) u z₀) = N → 0 < N → 2 * B ≤ N →
      closedBall z₀ (σ / N) ⊆ T →
      (∀ y ∈ closedBall z₀ (σ / N), √(ω.floerEnergyDensity (Ks p) (Kt p) u y) ≤ 2 * N) →
      (σ / N) ^ 2 < κ → δ ≤ ∫ y in T, ω.floerEnergyDensity (Ks p) (Kt p) u y := by
  obtain ⟨l, hl, δ, hδ, C', hC', hmv⟩ :=
    hω.exists_pos_forall_sq_mul_floerEnergyDensity_le_of_dist_lt
      (continuous_iff_continuousAt.2 fun x ↦ (he x).continuousAt) he_inj hW hC hD hCDW hJ hXs hXt
      hJt
  set σ := l / (2 * (2 * √(4 / c) + 1))
  have hσ : 0 < σ := by positivity
  refine ⟨σ, hσ, min (δ / 2) (σ ^ 2 / (4 * (C' + 1))), by positivity,
    min (δ / 2) (σ ^ 2 / (2 * (C' + 1))), by positivity,
    fun p u Ω T z₀ N hp hΩ hΩD hu hfl hT hTΩ hint hN hN0 hBN hrT hρ hκ ↦ ?_⟩
  by_contra! hE
  have hr0 : 0 < σ / N := div_pos hσ hN0
  have hrΩ : closedBall z₀ (σ / N) ⊆ Ω := hrT.trans hTΩ
  have hρ0 {y : ℝ × ℝ} (hy : y ∈ Ω) : 0 ≤ ω.floerEnergyDensity (Ks p) (Kt p) u y :=
    floerEnergyDensity_nonneg hω (hJt p hp y (hΩD hy) _) (hfl y hy)
  -- Since `ρ ≤ 4 N²` on the disc, `e ∘ u` is Lipschitz there with constant `L` of order `N`, and
  -- `L σ / N < l`.
  have hLip := hω.lipschitzOnWith_comp_of_floerEnergyDensity_le (A := 4 * N ^ 2)
    (convex_closedBall z₀ (σ / N)) (fun y ↦ J p y (u y)) hc (fun y _ ↦ he _)
    (fun y hy ↦ ((hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds (hrΩ hy))))
    (fun y hy ↦ hJc p hp y (hΩD (hrΩ hy)) _) (fun y hy ↦ hBs p hp y (hΩD (hrΩ hy)) _)
    (fun y hy ↦ hBt p hp y (hΩD (hrΩ hy)) _) (fun y hy ↦ hfl y (hrΩ hy)) fun y hy ↦ by
      rw [← Real.sq_sqrt (hρ0 (hrΩ hy))]
      nlinarith [hρ y hy, Real.sqrt_nonneg (ω.floerEnergyDensity (Ks p) (Kt p) u y)]
  have hB0 : 0 ≤ B :=
    (norm_nonneg _).trans (hBs p hp z₀ (hΩD (hrΩ (mem_closedBall_self hr0.le))) (u z₀))
  have hdist (y : ℝ × ℝ) (hy : y ∈ closedBall z₀ (σ / N)) : dist (e (u y)) (e (u z₀)) < l := by
    refine (hLip.dist_le_mul y hy z₀ (mem_closedBall_self hr0.le)).trans_lt ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall.1 hy) (by positivity)).trans_lt
      (two_mul_sqrt_add_mul_div_lt hc hN0 hBN hl)
  -- The energy of the open disc is at most that of `T`, which is small.
  have hI : ∫ y in ball z₀ (σ / N), ω.floerEnergyDensity (Ks p) (Kt p) u y ≤
      ∫ y in T, ω.floerEnergyDensity (Ks p) (Kt p) u y :=
    setIntegral_mono_set hint (ae_restrict_of_forall_mem hT fun y hy ↦ hρ0 (hTΩ hy))
      (Eventually.of_forall fun y hy ↦ hrT (ball_subset_closedBall hy))
  have hδE := hE.trans_le (min_le_left _ _)
  have hκδ := hκ.trans_le (min_le_left _ _)
  have h := hmv hp hΩ hr0.le hrΩ (hrΩ.trans hΩD) hu
    (fun y hy ↦ hfl y (hrΩ (ball_subset_closedBall hy))) hdist
    (hint.mono_set (ball_subset_closedBall.trans hrT)) (by linarith)
  -- So `σ² = (σ / N)² ρ(z₀) ≤ C' ((σ / N)² + ∫_T ρ) ≤ σ² / 2 + σ² / 4`.
  have hcentre : (σ / N) ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u z₀ = σ ^ 2 := by
    rw [← Real.sq_sqrt (hρ0 (hrΩ (mem_closedBall_self hr0.le))), hN]
    field_simp
  have h₁ := (le_div_iff₀ (by positivity)).1 (hκ.le.trans (min_le_right _ _))
  have h₂ := (le_div_iff₀ (by positivity)).1 (hE.le.trans (min_le_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left hI hC', sq_nonneg (σ / N), pow_pos hσ 2,
    setIntegral_nonneg (μ := volume) hT fun y hy ↦ hρ0 (hTΩ hy)]

/-- **Energy concentrates where Floer solutions in a closed manifold blow up, uniformly over a
compact parameter window.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold
`M`. Let the structures `J_p(z, x)` and the Hamiltonian vector fields of `K_{s,p}` and `K_{t,p}`
depend on a parameter `p` of a finite-dimensional normed space `P`, and, read in the chart at every
point `α`, be jointly `C²` on `W × (extChartAt I α).target` for an open set `W ⊆ P × (ℝ × ℝ)`
containing `C × D`, for a compact window `C` of parameters and a compact window `D` of the domain,
with `J_p(z, x)` tamed by `ω` for `p ∈ C` and `z ∈ D`. Let `e : M → F` be an injective
differentiable map into a normed space, such as the Whitney embedding, with the structures
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J_p v)` with `c > 0`, and the
pushforwards `d e (X_{K_{s,p}})`, `d e (X_{K_{t,p}})` at most `B`. There is a threshold `δ > 0` with
the following property. Let `uᵢ` be `C³` solutions of the Floer equation
`(du - X_{K_{pᵢ}})^{0,1} = 0` for `J_{pᵢ}(z, u)` on an open set `Ω ⊆ D`, for parameters `pᵢ ∈ C`,
with integrable Floer energy densities `ρᵢ`, and let `ρᵢ(zᵢ) → ∞` along points `zᵢ → z₀ ∈ Ω`.
Then for every `ε > 0`, eventually `∫_{B_ε(z₀) ∩ Ω} ρᵢ ≥ δ`. For a single datum, take a one-point
parameter space.

This is the energy concentration hypothesis of the counting lemma
`TauCeti.exists_strictMono_finset_forall_le_of_concentration`. -/
theorem IsNondegenerate.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity_ball
    (hω : ω.IsNondegenerate) {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J p z x)) {c B : ℝ}
    (hc : 0 < c)
    (hJc : ∀ p ∈ C, ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J p z x v))
    (hBs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks p z) x)‖ ≤ B)
    (hBt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt p z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃ι : Type*⦄ ⦃l : Filter ι⦄ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ι → P⦄ ⦃u : ι → ℝ × ℝ → M⦄
      ⦃z : ι → ℝ × ℝ⦄ ⦃z₀ : ℝ × ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ i, p i ∈ C) →
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u i) Ω) →
      (∀ i, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p i) y (u i y))
        (ω.perturbedMFDeriv (Ks (p i)) (Kt (p i)) (u i) y).toLinearMap) →
      (∀ i, IntegrableOn (ω.floerEnergyDensity (Ks (p i)) (Kt (p i)) (u i)) Ω) → z₀ ∈ Ω →
      Tendsto z l (𝓝 z₀) →
      Tendsto (fun i ↦ ω.floerEnergyDensity (Ks (p i)) (Kt (p i)) (u i) (z i)) l atTop →
      ∀ ε > 0, ∀ᶠ i in l,
        δ ≤ ∫ y in ball z₀ ε ∩ Ω, ω.floerEnergyDensity (Ks (p i)) (Kt (p i)) (u i) y := by
  obtain ⟨σ, -, δ, hδ, κ, hκ, hdisc⟩ :=
    hω.exists_pos_forall_le_setIntegral_floerEnergyDensity_of_sqrt_le he he_inj hW hC hD hCDW hJ
      hXs hXt hJt hc hJc hBs hBt
  refine ⟨δ, hδ, fun ι l Ω p u z z₀ hΩ hΩD hpC hu hfl hint hz₀ hz hblow ε hε ↦ ?_⟩
  set ρ : ι → ℝ × ℝ → ℝ := fun i ↦ ω.floerEnergyDensity (Ks (p i)) (Kt (p i)) (u i)
  -- Suppose that frequently `B_ε(z₀) ∩ Ω` carries energy less than `δ`, and restrict the filter
  -- to these indices.
  by_contra! hcon
  set S := {i | ∫ y in ball z₀ ε ∩ Ω, ρ i y < δ}
  have : (l ⊓ 𝓟 S).NeBot := frequently_iff_neBot.1 hcon
  -- The energy densities are continuous on `Ω`.
  have hρc (i : ι) : ContinuousOn (ρ i) Ω :=
    ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt hΩ ((hu i).of_le (by norm_num))
      (fun α ↦ continuousOn_hamiltonianVectorFieldInChartAt_apply (hXs α)
        fun y hy ↦ hCDW ⟨hpC i, hΩD hy⟩)
      (fun α ↦ continuousOn_hamiltonianVectorFieldInChartAt_apply (hXt α)
        fun y hy ↦ hCDW ⟨hpC i, hΩD hy⟩)
  -- Hofer's lemma for `√ρᵢ` gives centres `cᵢ → z₀` and radii `sᵢ` on whose discs
  -- `√ρᵢ ≤ 2 Nᵢ`, where `Nᵢ = √(ρᵢ(cᵢ)) → ∞` and `sᵢ Nᵢ → ∞`.
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hz₀)
  obtain ⟨cen, s, -, hcen, -, hsN, hev⟩ := exists_tendsto_hofer (l := l ⊓ 𝓟 S) hr₀
    (ϕ := fun i y ↦ √(ρ i y)) (fun i ↦ Real.continuous_sqrt.comp_continuousOn ((hρc i).mono hr₀Ω))
    (fun _ _ _ ↦ Real.sqrt_nonneg _) (hz.mono_left inf_le_left)
    (Real.tendsto_sqrt_atTop.comp (hblow.mono_left inf_le_left))
  set N : ι → ℝ := fun i ↦ √(ρ i (cen i))
  have hN : Tendsto N (l ⊓ 𝓟 S) atTop := tendsto_atTop_mono' _ (hev.mono fun i h ↦ h.1)
    (Real.tendsto_sqrt_atTop.comp (hblow.mono_left inf_le_left))
  have hr : Tendsto (fun i ↦ σ / N i) (l ⊓ 𝓟 S) (𝓝 0) := tendsto_const_nhds.div_atTop hN
  -- Eventually the disc `closedBall cᵢ (σ / Nᵢ)` is small and lies in `B_ε(z₀) ∩ Ω`, which then
  -- carries energy at least `δ`.
  have hfalse : ∀ᶠ _ in l ⊓ 𝓟 S, False := by
    filter_upwards [hev, hN.eventually_ge_atTop (max 1 (2 * B)), hsN.eventually_ge_atTop σ,
      (by simpa using (tendsto_iff_dist_tendsto_zero.1 hcen).add hr :
        Tendsto (fun i ↦ dist (cen i) z₀ + σ / N i) _ (𝓝 0)).eventually
          (gt_mem_nhds (lt_min hr₀ hε)),
      (by simpa using hr.pow 2 : Tendsto (fun i ↦ (σ / N i) ^ 2) _ (𝓝 0)).eventually
        (gt_mem_nhds hκ), mem_inf_of_right (mem_principal_self S)]
      with i hevi hNi hsi hnear hr2 hSi
    have hN0 : 0 < N i := one_pos.trans_le ((le_max_left _ _).trans hNi)
    have hsub : closedBall (cen i) (σ / N i) ⊆ ball z₀ ε ∩ Ω := fun y hy ↦ by
      have hd : dist y z₀ < min r₀ ε := (dist_triangle y (cen i) z₀).trans_lt
        (by linarith [mem_closedBall.1 hy])
      exact ⟨mem_ball.2 (hd.trans_le (min_le_right _ _)),
        hr₀Ω (mem_closedBall.2 (hd.trans_le (min_le_left _ _)).le)⟩
    refine (hdisc (hpC i) hΩ hΩD (hu i) (hfl i) (measurableSet_ball.inter hΩ.measurableSet)
      inter_subset_right ((hint i).mono_set inter_subset_right) rfl hN0
      ((le_max_right _ _).trans hNi) hsub (fun y hy ↦ hevi.2 y ((mem_closedBall'.1 hy).trans
        ((div_le_iff₀ hN0).2 (by simpa [mul_comm] using hsi)))) hr2).not_gt hSi
  exact hfalse.exists.elim fun _ h ↦ h

/-- **Gromov–Floer compactness in a closed manifold off finitely many points, over a compact
parameter window.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`,
such as a closed symplectic manifold. Let the structures `J_p(z, x)` and the Hamiltonian vector
fields of `K_{s,p}` and `K_{t,p}` depend on a parameter `p` of a finite-dimensional normed space
`P`, and, read in the chart at every point `α`, be jointly `C²` on `W × (extChartAt I α).target` for
an open set `W ⊆ P × (ℝ × ℝ)` containing `C × D`, for a compact window `C` of parameters and a
compact window `D` of the domain, with `J_p(z, x)` tamed by `ω` for `p ∈ C` and `z ∈ D`. Let
`e : M → F` be an injective differentiable map into a normed space, such as the Whitney embedding,
with the structures uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J_p v)` with `c > 0`, and
the pushforwards `d e (X_{K_{s,p}})`, `d e (X_{K_{t,p}})` at most `B`. There is a threshold `δ > 0`
with the following property. Let `uₖ` be `C³` solutions of the Floer equation
`(du - X_{K_{pₖ}})^{0,1} = 0` for `J_{pₖ}(z, u)` on an open set `Ω ⊆ D`, for parameters `pₖ ∈ C`,
with integrable Floer energy densities `ρₖ` and Floer energy `∫_Ω ρₖ ≤ E₀`. Then there are a
subsequence `φ`, a limit `p₀ ∈ C` of the parameters `p_{φ n}`, and a finite set `Z ⊆ Ω` of bubbling
points with `#Z * δ ≤ E₀` such that, along `φ`,

* energy at least `δ` concentrates at every point of `Z`: every disc about it eventually carries
  energy at least `δ`;
* the energy densities are uniformly bounded on every compact subset of `Ω \ Z`;
* the solutions converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying `e`
  and pointwise in `M`.

The threshold `δ` does not depend on the parameters, and no condition is put on the images of the
solutions. -/
theorem IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (hω : ω.IsNondegenerate) {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {W : Set (P × (ℝ × ℝ))} {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (fun q : (P × (ℝ × ℝ)) × E ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1.1) (q.1.2, q.2)) (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J p z x)) {c B : ℝ}
    (hc : 0 < c)
    (hJc : ∀ p ∈ C, ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      hω.symplecticFormAt x v (J p z x v))
    (hBs : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks p z) x)‖ ≤ B)
    (hBt : ∀ p ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt p z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) → (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) y (u k y))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) y).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ y in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) y ≤ E₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ C, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ A, ∀ n, ∀ y ∈ L, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y ≤ A) ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  obtain ⟨δ, hδ, hconc⟩ :=
    hω.exists_pos_forall_eventually_le_setIntegral_floerEnergyDensity_ball he he_inj hW hC hD hCDW
      hJ hXs hXt hJt hc hJc hBs hBt
  refine ⟨δ, hδ, fun Ω p u E₀ hΩ hΩD hpC hu hfl hint hE ↦ ?_⟩
  -- First make the parameters converge.
  obtain ⟨p₀, hp₀, ψ₀, hψ₀, hlim₀⟩ := hC.tendsto_subseq hpC
  set ρ : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)
  have hρc (k : ℕ) : ContinuousOn (ρ k) Ω :=
    ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt hΩ ((hu k).of_le (by norm_num))
      (fun α ↦ continuousOn_hamiltonianVectorFieldInChartAt_apply (hXs α)
        fun y hy ↦ hCDW ⟨hpC k, hΩD hy⟩)
      (fun α ↦ continuousOn_hamiltonianVectorFieldInChartAt_apply (hXt α)
        fun y hy ↦ hCDW ⟨hpC k, hΩD hy⟩)
  -- Energy concentrates wherever the densities blow up, so they are bounded on compact sets off
  -- finitely many concentration points.
  obtain ⟨φ, hφ, Z, hZΩ, hcard, hZ, hbd⟩ := exists_strictMono_finset_forall_le_of_concentration
    hΩ.measurableSet hδ (fun k ↦ hρc (ψ₀ k))
    (fun k y hy ↦ floerEnergyDensity_nonneg hω (hJt _ (hpC _) y (hΩD hy) _) (hfl _ y hy))
    (fun k ↦ hint (ψ₀ k)) (fun k ↦ hE (ψ₀ k))
    fun φ _ _ _ _ hz₀ hz hblow ↦ hconc hΩ hΩD (fun n ↦ hpC _) (fun n ↦ hu _) (fun n ↦ hfl _)
      (fun n ↦ hint _) hz₀ hz hblow
  -- Off them, the solutions converge along a further subsequence.
  have hΩZ : Ω \ ↑Z ⊆ Ω := sdiff_subset
  obtain ⟨ψ, hψ, v, hv, -, hconv, hpt⟩ := hω.exists_strictMono_tendstoLocallyUniformlyOn_comp
    isCompact_univ (fun x _ ↦ he x) he_inj.injOn (hΩ.sdiff Z.finite_toSet.isClosed)
    (u := fun n ↦ u (ψ₀ (φ n))) (Ks := fun n ↦ Ks (p (ψ₀ (φ n))))
    (Kt := fun n ↦ Kt (p (ψ₀ (φ n)))) (fun n z ↦ J (p (ψ₀ (φ n))) z (u (ψ₀ (φ n)) z)) hc
    (fun n z hz ↦ ((hu _).mdifferentiableOn (by norm_num)).mdifferentiableAt
      (hΩ.mem_nhds (hΩZ hz)))
    (fun _ ↦ mapsTo_univ _ _) (fun n z hz ↦ hJc _ (hpC _) z (hΩD (hΩZ hz)) _)
    (fun n z hz ↦ hBs _ (hpC _) z (hΩD (hΩZ hz)) _)
    (fun n z hz ↦ hBt _ (hpC _) z (hΩD (hΩZ hz)) _)
    (fun n z hz ↦ hfl _ z (hΩZ hz)) fun L hL hLΩ ↦ (hbd L hL hLΩ).imp fun A hA n ↦ hA n
  refine ⟨ψ₀ ∘ φ ∘ ψ, hψ₀.comp (hφ.comp hψ), p₀, hp₀,
    hlim₀.comp (hφ.comp hψ).tendsto_atTop, Z, hZΩ, hcard,
    fun z hz ε hε ↦ hψ.tendsto_atTop.eventually (hZ z hz ε hε),
    fun L hL hLΩ ↦ (hbd L hL hLΩ).imp fun A hA n ↦ hA (ψ n), v, hv, hconv, hpt⟩

/-- **Gromov–Floer compactness in a closed manifold off finitely many points.** Let `ω` be a
nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed symplectic
manifold, and let the structures `J(z, x)` and the Hamiltonian vector fields of `K_s` and `K_t`,
read in the chart at every point, be `C²` on `U × (extChartAt I α).target` for an open set `U` of
the domain containing a compact window `D`, with `J(z, x)` tamed by `ω` for `z ∈ D`. Let
`e : M → F` be an injective differentiable map into a normed space, such as the Whitney embedding,
with the structures uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and
the pushforwards `d e (X_{K_s})`, `d e (X_{K_t})` at most `B`. There is a threshold `δ > 0` with
the following property. Let `uₖ` be `C³` solutions of the Floer equation `(du - X_K)^{0,1} = 0` on
an open set `Ω ⊆ D`, with integrable Floer energy densities `ρₖ` and Floer energy
`∫_Ω ρₖ ≤ E₀`. Then there are a subsequence `φ` and a finite set `Z ⊆ Ω` of bubbling points with
`#Z * δ ≤ E₀` such that, along `φ`,

* energy at least `δ` concentrates at every point of `Z`: every disc about it eventually carries
  energy at least `δ`;
* the energy densities are uniformly bounded on every compact subset of `Ω \ Z`;
* the solutions converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying `e`
  and pointwise in `M`.

Unlike the compactness theorems in one chart
(`TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold`), no condition is put on the images of
the solutions. This is the case of a one-point parameter window of
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset`. -/
theorem IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    {Ks Kt : ℝ × ℝ → M → ℝ} {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hω : ω.IsNondegenerate) {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {U D : Set (ℝ × ℝ)} (hU : IsOpen U) (hD : IsCompact D) (hDU : D ⊆ U)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (U ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u k y))
        (ω.perturbedMFDeriv Ks Kt (u k) y).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ y in Ω, ω.floerEnergyDensity Ks Kt (u k) y ≤ E₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A) ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- The constant family over the one-point parameter space `Unit`, on `W = univ × U`.
  set pr : (Unit × (ℝ × ℝ)) × E →L[ℝ] (ℝ × ℝ) × E :=
    (ContinuousLinearMap.snd ℝ Unit (ℝ × ℝ) ∘L ContinuousLinearMap.fst ℝ _ E).prod
      (ContinuousLinearMap.snd ℝ _ E)
  have hpr (α : M) : MapsTo pr ((univ ×ˢ U) ×ˢ (extChartAt I α).target)
      (U ×ˢ (extChartAt I α).target) := fun q hq ↦ ⟨hq.1.2, hq.2⟩
  obtain ⟨δ, hδ, h⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (C := univ) he he_inj
      (isOpen_univ.prod hU) isCompact_univ hD (prod_mono subset_rfl hDU)
      (fun α ↦ ((hJ α).comp pr.contDiff.contDiffOn (hpr α)).congr fun q _ ↦
        Floer.almostComplexInChartAt_uncurry _ _ _ _)
      (fun α ↦ (hXs α).comp pr.contDiff.contDiffOn (hpr α))
      (fun α ↦ (hXt α).comp pr.contDiff.contDiffOn (hpr α)) (fun _ _ ↦ hJt) hc (fun _ _ ↦ hJc)
      (fun _ _ ↦ hBs) fun _ _ ↦ hBt
  refine ⟨δ, hδ, fun Ω u E₀ hΩ hΩD hu hfl hint hE ↦ ?_⟩
  obtain ⟨φ, hφ, -, -, -, Z, hZΩ, hcard, hZ, hbd, v, hv, hconv, hpt⟩ :=
    h (p := fun _ ↦ ()) hΩ hΩD (fun _ ↦ mem_univ _) hu hfl hint hE
  exact ⟨φ, hφ, Z, hZΩ, hcard, hZ, hbd, v, hv, hconv, hpt⟩

end TauCeti.SmoothTwoForm
