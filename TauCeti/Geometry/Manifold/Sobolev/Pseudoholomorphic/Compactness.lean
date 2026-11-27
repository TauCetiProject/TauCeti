/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.TendstoAt
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
`j`, and let `V` be a finite-dimensional real normed space. Let `J n` be smooth domain-dependent
almost complex structures on `V` and `ν n` smooth inhomogeneous terms for `(j, J n)`, converging in
`C^∞` on compact subsets of the preferred charts of `X` to `J₀` and `ν₀`, and let `p > 2`, possibly
`p = ∞`. Let `U n ⊆ X` exhaust `X`, in the sense that every compact subset of `X` lies in `U n` for
all large `n`, and let `u n : X → V` be weakly pseudoholomorphic on `U n`
(`TauCeti.IsWeakPseudoholomorphicOn (J n) (ν n) p (u n) (U n)`). Suppose that for every compact
`Q ⊆ X` the images `u n (Q)` lie in one compact set for all large `n`, and that the derivatives of
the `u n` are bounded in `Lᵖ` on compact subsets of the preferred charts of `X` for all large `n`.
Then a subsequence of the `u n` converges in `C^∞` on compact subsets of `X`, read in the
preferred charts of `X`, to a smooth map `v : X → V` that is weakly pseudoholomorphic for
`(J₀, ν₀)` (`TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakPseudoholomorphicOn`).
This is the interior case of McDuff–Salamon, Theorem B.4.2 with Remark B.4.3, for maps into a
vector space with smooth data converging in `C^∞` and a fixed complex structure on `X`, and in the
form of McDuff–Salamon, Theorem 4.1.1. Fixed data are the constant sequences, whose convergence is
`TauCeti.tendstoLocallyUniformly_const`.

## The argument

Near a point `z₀` of the target of a chart of `X`, the chart expressions of the `u n` solve the
planar equation `∂ₛw + J_φ(z, w) ∂ₜw = η_φ(z, w)` on a small ball, for all large `n`. Composing the
chart data with a smooth map of `ℂ` into the chart target that is the identity on the ball gives
smooth data on all of `ℂ × V`, still converging in `C^∞`
(`TauCeti.tendstoLocallyUniformlyOn_iteratedFDeriv_comp`), and the planar smooth compactness theorem
`TauCeti.exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn` applies on the
ball: every subsequence has a further subsequence converging there in `C^∞`. Countably many such
balls cover `X`, so a diagonal extraction (`TauCeti.extraction_forall_of_antitone`) gives one
subsequence converging pointwise on `X`, to a map `v`. On every ball of every preferred chart, every
further subsequence then has a subsequence converging in `C^∞` to the chart expression of `v`, so
the whole subsequence does (`TauCeti.tendstoLocallyUniformlyOn_of_forall_exists_subseq`).

## Implementation notes

The target is a vector space `V` with its identity chart, so no chart of the target has to contain
the images of the `u n`; a manifold target would also need convergence in `C⁰` before reducing to
charts of the target. The derivative bounds, the convergence of the data and the `C^∞` convergence
of the maps are all read in the preferred charts `chartAt ℂ x` of `X`, the data through
`ContMDiffAlmostComplexStructureFamily.chartField` and `InhomogeneousTerm.chartTerm` with the
identity chart of `V`. The exhaustion hypothesis holds for an increasing sequence of
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
  {J : ℕ → ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) X ⊤}
  {J₀ : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) X ⊤}
  {ν : (n : ℕ) →
    InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ⊤) (J n)}
  {ν₀ : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ⊤) J₀}
  {p : ENNReal} {u : ℕ → X → V} {U : ℕ → Set X}

omit [FiniteDimensional ℝ V] in
/-- A weak pseudoholomorphic map on `s` solves, on every part of a preferred chart target of `X`
over `s`, the planar equation with the data read in that chart and the identity chart of `V`. -/
private theorem isWeakCauchyRiemannOn_chartAt
    {J' : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℂ) X ⊤}
    {ν' : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ⊤) J'}
    {w : X → V} {s : Set X} (h : IsWeakPseudoholomorphicOn J' ν' p w s) (x : X) {W : Set ℂ}
    (hW : W ⊆ (chartAt ℂ x).target) (hWs : MapsTo (chartAt ℂ x).symm W s) :
    IsWeakCauchyRiemannOn p W (J'.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V))
      (ν'.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V)) (w ∘ (chartAt ℂ x).symm) := by
  have h' := h.isWeakCauchyRiemannOn_chart (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas (0 : V))
  simp only [OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, Function.id_comp] at h'
  exact h'.mono fun z hz ↦ ⟨hW hz, hWs hz, by simp⟩

omit [FiniteDimensional ℝ V] in
/-- On a ball on whose closure `c` is the identity, composing the data with `c` does not change the
planar equation. -/
private theorem isWeakCauchyRiemannOn_ball_comp_iff {p : ENNReal} {z₀ : ℂ} {r : ℝ} {c : ℂ → ℂ}
    (hc : ∀ z ∈ closedBall z₀ r, c z = z) {F : ℂ → V → V →L[ℝ] V} {G : ℂ → V → V} {w : ℂ → V} :
    IsWeakCauchyRiemannOn p (ball z₀ r) (fun z ↦ F (c z)) (fun z ↦ G (c z)) w ↔
      IsWeakCauchyRiemannOn p (ball z₀ r) F G w := by
  refine isWeakCauchyRiemannOn_congr_ae ?_ ?_ <;>
    refine ae_restrict_of_forall_mem measurableSet_interior fun z hz ↦ ?_ <;>
    rw [hc z (ball_subset_closedBall (interior_subset hz))]

omit [FiniteDimensional ℝ V] in
/-- Composed with `(z, y) ↦ (c z, y)` for a smooth `c` with values in a preferred chart target,
the chart data of `J n` and `ν n` are smooth on `ℂ × V` and converge in `C^∞` to those of `J₀`
and `ν₀`. -/
private theorem contDiff_tendstoLocallyUniformly_chartData_comp
    (hJt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hνt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (x : X) {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (hcT : ∀ z, c z ∈ (chartAt ℂ x).target) :
    (∀ n, ContDiff ℝ ∞ fun q : ℂ × V ↦
      (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2) ∧
    (∀ n, ContDiff ℝ ∞ fun q : ℂ × V ↦
      (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2) ∧
    (∀ k : ℕ, TendstoLocallyUniformly
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2) atTop) ∧
    ∀ k : ℕ, TendstoLocallyUniformly
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) (c q.1) q.2) atTop := by
  have hg : ContDiff ℝ ∞ (Prod.map c id : ℂ × V → ℂ × V) := hc.prodMap contDiff_id
  have hgT : MapsTo (Prod.map c id : ℂ × V → ℂ × V) univ ((chartAt ℂ x).target ×ˢ univ) :=
    fun q _ ↦ mk_mem_prod (hcT q.1) (mem_univ q.2)
  have hopen := (chartAt ℂ x).open_target.prod (isOpen_univ (X := V))
  refine ⟨fun n ↦ ((J n).contDiffOn_chartField_chartAt_refl x).comp_contDiff hg fun _ ↦ hgT trivial,
    fun n ↦ ((ν n).contDiffOn_chartTerm_chartAt_refl x).comp_contDiff hg fun _ ↦ hgT trivial,
    fun k ↦ tendstoLocallyUniformlyOn_univ.1 ?_, fun k ↦ tendstoLocallyUniformlyOn_univ.1 ?_⟩
  · exact tendstoLocallyUniformlyOn_iteratedFDeriv_comp hopen isOpen_univ hgT
      (Eventually.of_forall fun n ↦ (J n).contDiffOn_chartField_chartAt_refl x)
      (J₀.contDiffOn_chartField_chartAt_refl x) hg.contDiffOn (fun k _ ↦ hJt x k) k le_top
  · exact tendstoLocallyUniformlyOn_iteratedFDeriv_comp hopen isOpen_univ hgT
      (Eventually.of_forall fun n ↦ (ν n).contDiffOn_chartTerm_chartAt_refl x)
      (ν₀.contDiffOn_chartTerm_chartAt_refl x) hg.contDiffOn (fun k _ ↦ hνt x k) k le_top

/-- **The local step.** Near each point `z₀` of a preferred chart target of `X` there is a ball on
which, along every subsequence, a further subsequence of the chart expressions of the `u n`
converges in `C^∞` to a solution of the limiting chart equation. -/
private theorem exists_ball_forall_exists_subseq (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn (J n) (ν n) p (u n) (U n))
    (hJt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hνt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C)
    (x : X) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target) :
    ∃ r > 0, ball z₀ r ⊆ (chartAt ℂ x).target ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ w : ℂ → V,
        IsWeakCauchyRiemannOn p (ball z₀ r)
          (J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V))
          (ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V)) w ∧
        ∀ k : ℕ, TendstoLocallyUniformlyOn
          (fun n ↦ iteratedFDeriv ℝ k (u (ψ (ψ' n)) ∘ (chartAt ℂ x).symm))
          (iteratedFDeriv ℝ k w) atTop (ball z₀ r) := by
  set φ := chartAt ℂ x
  -- A smooth `c : ℂ → φ.target` equal to the identity on `closedBall z₀ r`.
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 φ.open_target z₀ hz₀
  obtain ⟨c, hc, hcε, hcid, -⟩ := exists_contDiff_cutoff_self z₀ (half_pos hε) (half_lt_self hε)
  set r := ε / 2
  have hcl : closedBall z₀ r ⊆ φ.target := (closedBall_subset_ball (half_lt_self hε)).trans hεT
  have hcT (z : ℂ) : c z ∈ φ.target := hεT (hcε z)
  obtain ⟨hJs, hνs, hJc, hνc⟩ :=
    contDiff_tendstoLocallyUniformly_chartData_comp hJt hνt x hc hcT
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
  refine ⟨r, half_pos hε, ball_subset_closedBall.trans hcl, fun ψ hψ ↦ ?_⟩
  have hNψ (n : ℕ) : N ≤ ψ (N + n) := (Nat.le_add_right N n).trans (hψ.id_le _)
  have hshift : Tendsto (fun n ↦ ψ (N + n)) atTop atTop :=
    (hψ.comp fun _ _ h ↦ Nat.add_lt_add_left h N).tendsto_atTop
  have hmaps : MapsTo φ.symm (ball z₀ r) K₀ := fun z hz ↦
    mem_image_of_mem _ (ball_subset_closedBall hz)
  -- The planar smooth compactness theorem on the ball, for the shifted subsequence.
  obtain ⟨ψ', w, hψ', -, hw, hconv⟩ :=
    exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakCauchyRiemannOn (Ω := W) hp
      (J := fun n z ↦ (J (ψ (N + n))).chartField φ (OpenPartialHomeomorph.refl V) (c z))
      (η := fun n z ↦ (ν (ψ (N + n))).chartTerm φ (OpenPartialHomeomorph.refl V) (c z))
      (J₀ := fun z ↦ J₀.chartField φ (OpenPartialHomeomorph.refl V) (c z))
      (η₀ := fun z ↦ ν₀.chartTerm φ (OpenPartialHomeomorph.refl V) (c z))
      (u := fun n ↦ u (ψ (N + n)) ∘ φ.symm)
      (fun n ↦ hJs _) (fun n ↦ hνs _) (fun k ↦ (hJc k).comp_tendsto hshift)
      (fun k ↦ (hνc k).comp_tendsto hshift)
      (fun n ↦ Eventually.of_forall fun _ ↦ (J _).chartField_refl_mul_self _ _ _)
      (fun n ↦ (isWeakCauchyRiemannOn_ball_comp_iff hcid).2 (isWeakCauchyRiemannOn_chartAt (hu _) x
        (ball_subset_closedBall.trans hcl) (hmaps.mono_right (hN _ (hNψ n)).1)))
      (fun Q hQW _ ↦ ⟨K, hK, fun n z hz ↦ (hN _ (hNψ n)).2.1 (hmaps (hQW hz))⟩)
      fun W' _ hW'W ↦ ⟨C, fun n ↦ (hN _ (hNψ n)).2.2.imp fun D hD ↦
        ⟨hD.1.mono (subset_closure.trans hW'W),
          (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hW'W) le_rfl)).trans
            hD.2⟩⟩
  exact ⟨fun n ↦ N + ψ' n, fun m n hmn ↦ by simpa using hψ' hmn, w,
    (isWeakCauchyRiemannOn_ball_comp_iff hcid).1 hw, hconv⟩

/-- **The diagonal step.** A subsequence of the `u n` converges at every point of `X`. -/
private theorem exists_strictMono_forall_tendsto [SecondCountableTopology X] (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn (J n) (ν n) p (u n) (U n))
    (hJt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hνt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
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
    exists_ball_forall_exists_subseq hp hU hu hJt hνt hK hd x (mem_chart_target ℂ x)
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
    (hu : ∀ n, IsWeakPseudoholomorphicOn (J n) (ν n) p (u n) (U n))
    (hJt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hνt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {v : X → V}
    (hv : ∀ y, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y))) (x : X) :
    IsWeakCauchyRiemannOn p (chartAt ℂ x).target
        (J₀.chartField (chartAt ℂ x)
          (OpenPartialHomeomorph.refl V))
        (ν₀.chartTerm (chartAt ℂ x)
          (OpenPartialHomeomorph.refl V))
        (v ∘ (chartAt ℂ x).symm) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ k (u (σ n) ∘ (chartAt ℂ x).symm))
        (iteratedFDeriv ℝ k (v ∘ (chartAt ℂ x).symm)) atTop (chartAt ℂ x).target := by
  choose ρ hρ hρT H using fun z (_ : z ∈ (chartAt ℂ x).target) ↦
    exists_ball_forall_exists_subseq hp hU hu hJt hνt hK hd x (z₀ := z) ‹_›
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
Theorem B.4.2 with Remark B.4.3, interior case, and Theorem 4.1.1, for smooth data converging in
`C^∞`, a fixed complex structure on the domain and maps into a vector space). Let `X` be a second
countable Riemann surface, `V` a finite-dimensional real normed space, `J n` smooth
domain-dependent almost complex structures on `V`, `ν n` smooth inhomogeneous terms and `p > 2`,
possibly `p = ∞`. Suppose that in every preferred chart `chartAt ℂ x`, read with the identity chart
of `V`, every derivative of `J n` and of `ν n` converges locally uniformly on
`(chartAt ℂ x).target ×ˢ univ` to that of `J₀` and of `ν₀`. Let every compact subset of `X` lie in
`U n` for all large `n`, and let `u n` be weakly pseudoholomorphic for `(J n, ν n)` on `U n`.
Suppose that for every compact `Q ⊆ X` the images `u n (Q)` lie in one compact set for all large
`n`, and that on every open `W` with compact closure in the target of a preferred chart
`chartAt ℂ x` the chart expressions `u n ∘ (chartAt ℂ x).symm` have weak derivatives bounded in
`Lᵖ(W)` for all large `n`.

Then a subsequence `u (σ n)` converges locally uniformly on `X`, and in every preferred chart in
`C^∞` on compact subsets of the chart target, to a smooth map `v` that is weakly pseudoholomorphic
for `(J₀, ν₀)`. For fixed data `J n = J₀` and `ν n = ν₀`, the convergence hypotheses hold by
`TauCeti.tendstoLocallyUniformly_const`.

The bound on images is needed: the constant maps `u n = n` on `X = ℂ`, for `J = i`, satisfy every
other hypothesis and have no convergent subsequence. -/
theorem exists_subseq_forall_tendstoLocallyUniformlyOn_of_isWeakPseudoholomorphicOn
    [SecondCountableTopology X] (hp : 2 < p)
    (hU : ∀ Q : Set X, IsCompact Q → ∀ᶠ n in atTop, Q ⊆ U n)
    (hu : ∀ n, IsWeakPseudoholomorphicOn (J n) (ν n) p (u n) (U n))
    (hJt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (J n).chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        J₀.chartField (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hνt : ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
      (fun n ↦ iteratedFDeriv ℝ k fun q : ℂ × V ↦
        (ν n).chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      (iteratedFDeriv ℝ k fun q : ℂ × V ↦
        ν₀.chartTerm (chartAt ℂ x) (OpenPartialHomeomorph.refl V) q.1 q.2)
      atTop ((chartAt ℂ x).target ×ˢ univ))
    (hK : ∀ Q : Set X, IsCompact Q → ∃ K : Set V, IsCompact K ∧ ∀ᶠ n in atTop, MapsTo (u n) Q K)
    (hd : ∀ (x : X) (W : Opens ℂ), IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ (chartAt ℂ x).target → ∃ C : ℝ≥0, ∀ᶠ n in atTop, ∃ D,
        HasWeakFDerivOn volume W (u n ∘ (chartAt ℂ x).symm) D ∧
          eLpNorm D p (volume.restrict W) ≤ C) :
    ∃ (σ : ℕ → ℕ) (v : X → V), StrictMono σ ∧ IsWeakPseudoholomorphic J₀ ν₀ p v ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, V) ∞ v ∧ TendstoLocallyUniformly (fun n ↦ u (σ n)) v atTop ∧
      ∀ (x : X) (k : ℕ), TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ k (u (σ n) ∘ (chartAt ℂ x).symm))
        (iteratedFDeriv ℝ k (v ∘ (chartAt ℂ x).symm)) atTop (chartAt ℂ x).target := by
  obtain ⟨σ, hσ, hlim⟩ := exists_strictMono_forall_tendsto hp hU hu hJt hνt hK hd
  set v : X → V := fun y ↦ limUnder atTop fun n ↦ u (σ n) y
  have hv (y : X) : Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y)) := tendsto_nhds_limUnder (hlim y)
  have hchart := tendstoLocallyUniformlyOn_chartAt_of_tendsto hp hU hu hJt hνt hK hd hσ hv
  -- The limit is continuous and solves the equation in every preferred chart.
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x ↦
    ((((hchart x).1.continuousOn.continuousAt ((chartAt ℂ x).open_target.mem_nhds
      (mem_chart_target ℂ x))).comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)))).congr
        (((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).mono fun y hy ↦
          by simp [hy])
  have hvJ : IsWeakPseudoholomorphic J₀ ν₀ p v := by
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
