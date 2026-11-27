/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Compactness.Uniform
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Atlas
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Regularity
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness for weak pseudoholomorphic maps from a Riemann surface

Let `X` be a second countable Riemann surface without boundary, with its fixed complex structure
`j`, and let `V` be a finite-dimensional real normed space. Let `J` be a smooth domain-dependent
almost complex structure on `V` and `ν` a smooth inhomogeneous term for `(j, J)`, and let `p > 2`,
possibly `p = ∞`. Let `U n ⊆ X` exhaust `X`, in the sense that every compact subset of `X` lies in
`U n` for all large `n`, and let `u n : X → V` be weakly pseudoholomorphic on `U n`
(`TauCeti.IsWeakPseudoholomorphicOn J ν p (u n) (U n)`). Suppose that for every compact `Q ⊆ X`
the images `u n (Q)` lie in one compact set for all large `n`, and that the derivatives of the
`u n` are bounded in `Lᵖ` on compact subsets of the preferred charts of `X` for all large `n`.
Then a subsequence of the `u n` converges in `C^∞` on compact subsets of `X`, read in the
preferred charts of `X`, to a smooth weak pseudoholomorphic map `v : X → V`
(`TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakPseudoholomorphicOn`). This is
the interior case of McDuff–Salamon, Theorem B.4.2 with Remark B.4.3, for maps into a vector space
with fixed smooth data, and in the form of McDuff–Salamon, Theorem 4.1.1.

## The argument

Near a point `z₀` of the target of a chart of `X`, the chart expressions of the `u n` solve the
planar equation `∂ₛw + J_φ(z, w) ∂ₜw = η_φ(z, w)` on a small ball, for all large `n`. Composing the
chart data with a smooth map of `ℂ` into the chart target that is the identity on the ball gives
smooth data on all of `ℂ × V`, and the planar smooth compactness theorem
`TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn` applies on the
ball: every subsequence has a further subsequence converging there in `C^∞`. Countably many such
balls cover `X`, so a diagonal extraction (`TauCeti.extraction_forall_of_antitone`) gives one
subsequence converging pointwise on `X`, to a map `v`. On every ball of every preferred chart, every
further subsequence then has a subsequence converging in `C^∞` to the chart expression of `v`, so
the whole subsequence does (`TauCeti.tendstoLocallyUniformlyOn_of_forall_exists_subseq`).

## Implementation notes

The target is a vector space `V` with its identity chart, so no chart of the target has to contain
the images of the `u n`; a manifold target would also need convergence in `C⁰` before reducing to
charts of the target. The derivative bounds and the `C^∞` convergence are both read in the
preferred charts `chartAt ℂ x` of `X`. The exhaustion hypothesis holds for an increasing sequence of
open sets with union `X`, by compactness.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Appendix B.4 (Theorem B.4.2 and Remark B.4.3).
-/

public section

open Set Filter TopologicalSpace MeasureTheory Metric
open scoped Manifold ContDiff Topology NNReal TauCeti.ComplexManifold

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) X ⊤}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ⊤) J}
  {p : ENNReal} {u : ℕ → X → V} {U : ℕ → Set X}

omit [FiniteDimensional ℝ V] in
/-- A weak pseudoholomorphic map on `s` solves, on every part of a preferred chart target of `X`
over `s`, the planar equation with the data read in that chart and the identity chart of `V`. -/
private theorem isWeakCauchyRiemannOn_chartAt {w : X → V} {s : Set X}
    (h : IsWeakPseudoholomorphicOn J ν p w s) (x : X) {W : Set ℂ}
    (hW : W ⊆ (chartAt ℂ x).target) (hWs : MapsTo (chartAt ℂ x).symm W s) :
    IsWeakCauchyRiemannOn p W
      (J.chartField (chartAt ℂ x) ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)))
      (ν.chartTerm (chartAt ℂ x) ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)))
      (w ∘ (chartAt ℂ x).symm) := by
  have h' := h.isWeakCauchyRiemannOn_chart (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas (0 : V))
  simp only [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, Function.id_comp] at h' ⊢
  exact h'.mono fun z hz ↦ ⟨hW hz, hWs hz, by simp⟩

omit [FiniteDimensional ℝ V] in
/-- Near each point `z₀` of a preferred chart target of `X`, the data read in that chart and the
identity chart of `V` agree, over a closed ball around `z₀` inside the chart target, with smooth
data on `ℂ × V` whose structure squares to `-1` everywhere. -/
private theorem exists_closedBall_contDiff_chartData (x : X) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (chartAt ℂ x).target) :
    ∃ r > 0, closedBall z₀ r ⊆ (chartAt ℂ x).target ∧
      ∃ (J' : ℂ → V → V →L[ℝ] V) (η' : ℂ → V → V),
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℂ × V ↦ J' q.1 q.2) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℂ × V ↦ η' q.1 q.2) ∧ (∀ z y, J' z y * J' z y = -1) ∧
        ∀ z ∈ closedBall z₀ r,
          J' z = J.chartField (chartAt ℂ x)
            ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)) z ∧
          η' z = ν.chartTerm (chartAt ℂ x)
            ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)) z := by
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 (chartAt ℂ x).open_target z₀ hz₀
  set r := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  -- A smooth map `c` of `ℂ` into the chart target, equal to the identity on `closedBall z₀ r`.
  let χ : ContDiffBump z₀ := ⟨r, 2 * r, hr, by linarith⟩
  let c : ℂ → ℂ := fun z ↦ z₀ + χ z • (z - z₀)
  have hc : ContDiff ℝ ∞ c :=
    contDiff_const.add (χ.contDiff.smul (contDiff_id.sub contDiff_const))
  have hcT (z : ℂ) : c z ∈ (chartAt ℂ x).target := by
    refine hεT ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg χ.nonneg]
    by_cases hz : ‖z - z₀‖ < ε
    · exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans_lt hz
    · rw [χ.zero_of_le_dist (by rw [dist_eq_norm]; simp only [χ]; linarith), zero_mul]
      exact hε
  -- The chart data composed with `c`.
  refine ⟨r, hr, (closedBall_subset_ball (by linarith)).trans hεT, fun z ↦ J.chartField _ _ (c z),
    fun z ↦ ν.chartTerm _ _ (c z),
    (J.contDiffOn_chartField_chartAt x (0 : V)).comp_contDiff (hc.prodMap contDiff_id)
      fun q ↦ ⟨hcT q.1, by simp⟩,
    (ν.contDiffOn_chartTerm_chartAt x (0 : V)).comp_contDiff (hc.prodMap contDiff_id)
      fun q ↦ ⟨hcT q.1, by simp⟩,
    fun z y ↦ ContinuousLinearMap.ext fun w ↦
      J.chartField_chartAt_apply_apply x (0 : V) (c z) (by simp) w, fun z hz ↦ ?_⟩
  simp only [c, χ.one_of_mem_closedBall hz, one_smul, add_sub_cancel, and_self]

/-- **The local step.** Near each point `z₀` of a preferred chart target of `X` there is a ball on
which, along every subsequence, a further subsequence of the chart expressions of the `u n`
converges in `C^∞` to a solution of the chart equation. -/
private theorem exists_ball_forall_exists_subseq (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn J ν p (u n) (U n))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C)
    (x : X) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target) :
    ∃ r > 0, ball z₀ r ⊆ (chartAt ℂ x).target ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ w : ℂ → V,
        IsWeakCauchyRiemannOn p (ball z₀ r)
          (J.chartField (chartAt ℂ x)
            ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)))
          (ν.chartTerm (chartAt ℂ x)
            ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V))) w ∧
        ∀ k : ℕ, TendstoLocallyUniformlyOn
          (fun n ↦ iteratedFDeriv ℝ k (u (ψ (ψ' n)) ∘ (chartAt ℂ x).symm))
          (iteratedFDeriv ℝ k w) atTop (ball z₀ r) := by
  set φ := chartAt ℂ x
  set e := (chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)
  obtain ⟨r, hr, hcl, J', η', hJ', hη', hJ2, hJη⟩ :=
    exists_closedBall_contDiff_chartData (J := J) (ν := ν) x hz₀
  have hdata {w : ℂ → V} : IsWeakCauchyRiemannOn p (ball z₀ r) J' η' w ↔
      IsWeakCauchyRiemannOn p (ball z₀ r) (J.chartField φ e) (ν.chartTerm φ e) w := by
    refine isWeakCauchyRiemannOn_congr_ae ?_ ?_ <;>
      refine ae_restrict_of_forall_mem measurableSet_interior fun z hz ↦ ?_
    · rw [(hJη z (ball_subset_closedBall (interior_subset hz))).1]
    · rw [(hJη z (ball_subset_closedBall (interior_subset hz))).2]
  -- From some index `N` on, the hypotheses hold uniformly over the ball.
  set K₀ := φ.symm '' closedBall z₀ r
  have hK₀ : IsCompact K₀ :=
    (isCompact_closedBall z₀ r).image_of_continuousOn (φ.continuousOn_symm.mono hcl)
  obtain ⟨K, hK, hKev⟩ := hK K₀ hK₀
  let W : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hWcl : closure (W : Set ℂ) ⊆ closedBall z₀ r := closure_ball_subset_closedBall
  obtain ⟨C, hCev⟩ := hd x W ((isCompact_closedBall z₀ r).of_isClosed_subset isClosed_closure hWcl)
    (hWcl.trans hcl)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hU K₀ hK₀).and (hKev.and hCev))
  refine ⟨r, hr, ball_subset_closedBall.trans hcl, fun ψ hψ ↦ ?_⟩
  have hNψ (n : ℕ) : N ≤ ψ (N + n) := (Nat.le_add_right N n).trans (hψ.id_le _)
  have hmaps : MapsTo φ.symm (ball z₀ r) K₀ := fun z hz ↦
    mem_image_of_mem _ (ball_subset_closedBall hz)
  -- The planar smooth compactness theorem on the ball, for the shifted subsequence.
  obtain ⟨ψ', w, hψ', -, hw, hconv⟩ :=
    exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn (Ω := W) hp
      (J := fun _ ↦ J') (η := fun _ ↦ η') (J₀ := J') (η₀ := η')
      (u := fun n ↦ u (ψ (N + n)) ∘ φ.symm) (fun _ ↦ hJ') (fun _ ↦ hη')
      (fun _ ↦ tendstoLocallyUniformly_const _) (fun _ ↦ tendstoLocallyUniformly_const _)
      (fun n ↦ Eventually.of_forall fun z ↦ hJ2 z _)
      (fun n ↦ hdata.2 (isWeakCauchyRiemannOn_chartAt (hu _) x (ball_subset_closedBall.trans hcl)
        (hmaps.mono_right (hN _ (hNψ n)).1)))
      (fun Q hQW _ ↦ ⟨K, hK, fun n z hz ↦ (hN _ (hNψ n)).2.1 (hmaps (hQW hz))⟩)
      fun W' _ hW'W ↦ ⟨C, fun n ↦ (hN _ (hNψ n)).2.2.imp fun D hD ↦
        ⟨hD.1.mono (subset_closure.trans hW'W),
          (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hW'W) le_rfl)).trans
            hD.2⟩⟩
  exact ⟨fun n ↦ N + ψ' n, fun m n hmn ↦ by simpa using hψ' hmn, w, hdata.1 hw, hconv⟩

/-- **The diagonal step.** A subsequence of the `u n` converges at every point of `X`. -/
private theorem exists_strictMono_forall_tendsto [SecondCountableTopology X] (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn J ν p (u n) (U n))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ y : X, ∃ b : V, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨id, strictMono_id, isEmptyElim⟩
  -- Countably many balls in preferred charts cover `X`.
  choose r hr _ hsub using fun x : X ↦
    exists_ball_forall_exists_subseq hp hU hu hK hd x (mem_chart_target ℂ x)
  set O : X → Set X := fun x ↦
    (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) (r x)
  obtain ⟨S, hSc, hSU⟩ := countable_cover_nhds (f := O) fun x ↦ inter_mem
    (chart_source_mem_nhds ℂ x)
    (((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds
      (ball_mem_nhds _ (hr x)))
  obtain ⟨_, hx₀S, -⟩ := mem_iUnion₂.1 (hSU ▸ mem_univ x₀ : x₀ ∈ ⋃ x ∈ S, O x)
  obtain ⟨a, rfl⟩ := hSc.exists_eq_range ⟨_, hx₀S⟩
  -- A diagonal subsequence converges locally uniformly on every ball of the cover.
  obtain ⟨σ, hσ, hP⟩ := extraction_forall_of_antitone
    (P := fun j l ↦ ∃ g : ℂ → V, TendstoLocallyUniformlyOn
      (fun n ↦ u n ∘ (chartAt ℂ (a j)).symm) g l (ball (chartAt ℂ (a j) (a j)) (r (a j))))
    (fun _ _ _ hl ⟨g, hg⟩ ↦ ⟨g, hg.comp_tendsto (tendsto_id'.2 hl)⟩) fun j ψ hψ ↦ by
      obtain ⟨ψ', hψ', w, -, hw⟩ := hsub (a j) ψ hψ
      exact ⟨ψ', hψ', w, tendstoLocallyUniformlyOn_map_iff.2
        (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hw 0))⟩
  choose g hg using hP
  refine ⟨σ, hσ, fun y ↦ ?_⟩
  obtain ⟨_, ⟨j, rfl⟩, hy⟩ := mem_iUnion₂.1 (hSU ▸ mem_univ y : y ∈ ⋃ x ∈ range a, O x)
  refine ⟨g j (chartAt ℂ (a j) y), ?_⟩
  simpa [Function.comp_def, (chartAt ℂ (a j)).left_inv hy.1] using
    (tendstoLocallyUniformlyOn_map_iff.1 (hg j)).tendsto_at hy.2

/-- **The identification step.** If a subsequence of the `u n` converges pointwise to `v`, then in
every preferred chart of `X` it converges to `v` in `C^∞` on compact subsets of the chart target,
and the chart expression of `v` solves the chart equation. -/
private theorem tendstoLocallyUniformlyOn_chartAt_of_tendsto (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn J ν p (u n) (U n))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {v : X → V}
    (hv : ∀ y, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y))) (x : X) :
    IsWeakCauchyRiemannOn p (chartAt ℂ x).target
        (J.chartField (chartAt ℂ x)
          ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)))
        (ν.chartTerm (chartAt ℂ x)
          ((chartAt V (0 : V)).extendTrans 𝓘(ℝ, V) (Homeomorph.refl V)))
        (v ∘ (chartAt ℂ x).symm) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ k (u (σ n) ∘ (chartAt ℂ x).symm))
        (iteratedFDeriv ℝ k (v ∘ (chartAt ℂ x).symm)) atTop (chartAt ℂ x).target := by
  choose ρ hρ hρT H using fun z (_ : z ∈ (chartAt ℂ x).target) ↦
    exists_ball_forall_exists_subseq hp hU hu hK hd x (z₀ := z) ‹_›
  -- On each ball, every subsequential limit is the chart expression of `v`.
  have heq {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {w : ℂ → V}
      (hw : TendstoLocallyUniformlyOn (fun n ↦ u (σ (ψ n)) ∘ (chartAt ℂ x).symm) w atTop
        (ball z (ρ z hz))) : EqOn w (v ∘ (chartAt ℂ x).symm) (ball z (ρ z hz)) := fun y hy ↦
    tendsto_nhds_unique (hw.tendsto_at hy) ((hv _).comp hψ.tendsto_atTop)
  have hTU : (⋃ z : (chartAt ℂ x).target, ball (z : ℂ) (ρ z z.property)) =
      (chartAt ℂ x).target :=
    Subset.antisymm (iUnion_subset fun z ↦ hρT z z.property) fun z hz ↦
      mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hρ z hz)⟩
  refine ⟨isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ⟨_,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (hρ z hz)), ?_⟩, fun k ↦ ?_⟩
  · obtain ⟨ψ', hψ', w, hw, hconv⟩ := H z hz σ hσ
    exact hw.congr (heq hz hψ' (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconv 0)))
  -- On each ball, every subsequence has a further subsequence converging to `v` in order `k`.
  rw [← hTU]
  refine tendstoLocallyUniformlyOn_iUnion (fun _ ↦ isOpen_ball) fun z ↦
    tendstoLocallyUniformlyOn_of_forall_exists_subseq isOpen_ball fun ψ hψ ↦ ?_
  obtain ⟨ψ', hψ', w, -, hconv⟩ := H z z.property (σ ∘ ψ) (hσ.comp hψ)
  have hw := heq z.property (hψ.comp hψ')
    (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconv 0))
  exact ⟨ψ', hψ', (hconv k).congr_right fun y hy ↦
    ((hw.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy)).iteratedFDeriv ℝ k).eq_of_nhds⟩

/-- **Compactness for weak pseudoholomorphic maps from a Riemann surface** (McDuff–Salamon,
Theorem B.4.2 with Remark B.4.3, interior case, and Theorem 4.1.1, for fixed smooth data and maps
into a vector space). Let `X` be a second countable Riemann surface, `V` a finite-dimensional real
normed space, `J` a smooth domain-dependent almost complex structure on `V`, `ν` a smooth
inhomogeneous term and `p > 2`, possibly `p = ∞`. Let every compact subset of `X` lie in `U n` for
all large `n`, and let `u n` be weakly pseudoholomorphic on `U n`. Suppose that for every compact
`Q ⊆ X` the images `u n (Q)` lie in one compact set for all large `n`, and that on every open `W`
with compact closure in the target of a preferred chart `chartAt ℂ x` the chart expressions
`u n ∘ (chartAt ℂ x).symm` have weak derivatives bounded in `Lᵖ(W)` for all large `n`.

Then a subsequence `u (σ n)` converges locally uniformly on `X`, and in every preferred chart in
`C^∞` on compact subsets of the chart target, to a smooth weak pseudoholomorphic map `v`.

The bound on images is needed: the constant maps `u n = n` on `X = ℂ`, for `J = i`, satisfy every
other hypothesis and have no convergent subsequence. -/
theorem exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakPseudoholomorphicOn
    [SecondCountableTopology X] (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn J ν p (u n) (U n))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C) :
    ∃ (σ : ℕ → ℕ) (v : X → V), StrictMono σ ∧ IsWeakPseudoholomorphic J ν p v ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, V) ∞ v ∧ TendstoLocallyUniformly (fun n ↦ u (σ n)) v atTop ∧
      ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ k (u (σ n) ∘ (chartAt ℂ x).symm))
        (iteratedFDeriv ℝ k (v ∘ (chartAt ℂ x).symm)) atTop (chartAt ℂ x).target := by
  obtain ⟨σ, hσ, hlim⟩ := exists_strictMono_forall_tendsto hp hU hu hK hd
  set v : X → V := fun y ↦ limUnder atTop fun n ↦ u (σ n) y
  have hv (y : X) : Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y)) := tendsto_nhds_limUnder (hlim y)
  have hchart := tendstoLocallyUniformlyOn_chartAt_of_tendsto hp hU hu hK hd hσ hv
  -- The limit is continuous and solves the equation in every preferred chart.
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x ↦
    ((((hchart x).1.continuousOn.continuousAt ((chartAt ℂ x).open_target.mem_nhds
      (mem_chart_target ℂ x))).comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)))).congr
        (((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).mono fun y hy ↦
          by simp [hy])
  have hvJ : IsWeakPseudoholomorphic J ν p v := by
    refine (isWeakPseudoholomorphic_iff_of_subset_maximalAtlas
      (A := range (chartAt ℂ : X → OpenPartialHomeomorph X ℂ))
      (B := {chartAt V (0 : V)}) (by rintro _ ⟨x, rfl⟩; exact IsManifold.chart_mem_maximalAtlas x)
      (fun x ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
      (singleton_subset_iff.2 (IsManifold.chart_mem_maximalAtlas (0 : V)))
      fun _ ↦ ⟨_, rfl, by simp⟩).2 ⟨hvc, ?_⟩
    rintro _ ⟨x, rfl⟩ _ rfl
    have hsrc : (chartAt V (0 : V)).source = univ := by simp
    simp only [hsrc, preimage_univ, inter_univ]
    have hx := (hchart x).1
    simp only [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl, chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply, Function.id_comp] at hx ⊢
    exact hx
  refine ⟨σ, v, hσ, hvJ, hvJ.contMDiff hp, ?_, fun x ↦ (hchart x).2⟩
  -- Locally uniform convergence on `X`, read off in the preferred charts.
  rw [← tendstoLocallyUniformlyOn_univ, ← iUnion_source_chartAt ℂ X]
  refine tendstoLocallyUniformlyOn_iUnion (fun x ↦ (chartAt ℂ x).open_source) fun x ↦ ?_
  have h := (tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 ((hchart x).2 0)).comp
    (chartAt ℂ x) (chartAt ℂ x).mapsTo (chartAt ℂ x).continuousOn
  refine (h.congr fun n y hy ↦ ?_).congr_right fun y hy ↦ ?_ <;>
    simp [(chartAt ℂ x).left_inv hy]

end TauCeti
