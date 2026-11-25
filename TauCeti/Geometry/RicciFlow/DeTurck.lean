/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# The DeTurck vector field

For two Riemannian metrics `g` and `gbar`, the DeTurck vector field is the `g`-trace of the
difference of their Levi-Civita connections. Its sign convention is
`Wᵏ = gⁱʲ (Γ(g)ᵏᵢⱼ - Γ(gbar)ᵏᵢⱼ)`, as in the gauge construction of Topping, §5.2.
The difference of connections is tensorial, so this definition does not depend on a chart.

The characteristic equation `deTurckVectorField_eq_metricTrace` identifies the contraction.
The orthonormal-basis and Christoffel-map equations give its frame and coordinate presentations.
`contMDiff_deTurckVectorField` proves spatial regularity with one derivative lost from each metric.
The field vanishes for identical metrics and positive constant rescalings.

## References

* Peter Topping, *Lectures on the Ricci Flow*, §5.2, pp. 61–62.
  Author's notes: https://warwick.ac.uk/fac/sci/maths/people/staff/peter_topping/rfnotes/
-/

public section

open Bundle Riemannian.Tensor
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {k kbar : ℕ∞ω}

/-- The DeTurck vector field of `g` relative to the background metric `gbar`, with the convention
`Wᵏ = gⁱʲ (Γ(g)ᵏᵢⱼ - Γ(gbar)ᵏᵢⱼ)`. -/
def deTurckVectorField
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) : TangentSpace I x := by
  let cov := letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    CovariantDerivative.leviCivitaConnection I M
  let covbar :=
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hgbar
    CovariantDerivative.leviCivitaConnection I M
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact LinearMap.BilinMap.metricTrace
    (ContinuousLinearMap.toLinearMap₁₂ (cov.difference covbar x))

/-- The characteristic equation: the DeTurck field is the metric trace of the connection
difference tensor. Both Levi-Civita connections use their own metric. -/
theorem deTurckVectorField_eq_metricTrace
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) :
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covbar :=
      let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hgbar
      CovariantDerivative.leviCivitaConnection I M
    g.deTurckVectorField gbar hg hgbar x = LinearMap.BilinMap.metricTrace
      (ContinuousLinearMap.toLinearMap₁₂ (cov.difference covbar x)) := by
  unfold deTurckVectorField
  rfl

/-- A metric's DeTurck field relative to itself vanishes. -/
@[simp]
theorem deTurckVectorField_self
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) : g.deTurckVectorField g hg hg = 0 := by
  funext x
  rw [deTurckVectorField_eq_metricTrace]
  simp

/-- In a `g`-orthonormal basis the DeTurck vector is the sum of the diagonal connection
differences. -/
theorem deTurckVectorField_eq_sum_orthonormalBasis
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) :
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covbar :=
      let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hgbar
      CovariantDerivative.leviCivitaConnection I M
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)),
      g.deTurckVectorField gbar hg hgbar x =
        ∑ i, cov.difference covbar x (b i) (b i) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hg
  dsimp only
  intro ι _ b
  rw [deTurckVectorField_eq_metricTrace, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  rfl

/-- On a chart domain, the DeTurck vector is the inverse-metric contraction of the connection
difference in the chart frame. -/
theorem deTurckVectorField_eq_sum_chartInvGramMatrix
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) :
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covbar :=
      let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hgbar
      CovariantDerivative.leviCivitaConnection I M
    ∀ (α : M), x ∈ (chartAt H α).source →
      g.deTurckVectorField gbar hg hgbar x =
        ∑ i, ∑ j, chartInvGramMatrix (I := I) α x i j •
          cov.difference covbar x (chartLocalFrame (I := I) α i x)
            (chartLocalFrame (I := I) α j x) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hg
  dsimp only
  intro α hx
  rw [deTurckVectorField_eq_metricTrace,
    metricTrace_eq_sum_chartInvGramMatrix α hx]
  rfl

/-- Locally, the DeTurck field is a sum of covariant derivatives of the chart frame along its
metric-dual frame. This equation is useful for spatial regularity. -/
private theorem deTurckVectorField_eq_sum_chartDualFrame
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) :
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covbar :=
      let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hgbar
      CovariantDerivative.leviCivitaConnection I M
    ∀ (α : M), x ∈ (chartAt H α).source →
      g.deTurckVectorField gbar hg hgbar x =
        ∑ i, (cov (chartLocalFrame (I := I) α i) x
          (chartDualFrame (I := I) α i x) -
          covbar (chartLocalFrame (I := I) α i) x (chartDualFrame (I := I) α i x)) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hg
  dsimp only
  intro α hx
  rw [deTurckVectorField_eq_metricTrace, metricTrace_eq_sum_chartDualFrame α hx]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [CovariantDerivative.difference_apply _ _
    (mdifferentiableAt_chartLocalFrame α
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx) i)]
  rfl

/-- In chart coordinates the DeTurck field is `gⁱʲ (Γ(g) - Γ(gbar))`, transported from the model
space back to the tangent space. -/
theorem deTurckVectorField_eq_sum_christoffelMap
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar) (x : M) :
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    let cov := CovariantDerivative.leviCivitaConnection I M
    let covbar :=
      let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hgbar
      CovariantDerivative.leviCivitaConnection I M
    ∀ (α : M) (_hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet),
      let e := trivializationAt E (TangentSpace I) α
      let b := Module.finBasis ℝ E
      g.deTurckVectorField gbar hg hgbar x = ∑ i, ∑ j,
        chartInvGramMatrix (I := I) α x i j • e.symmL ℝ x
          (TauCeti.Manifold.christoffelMap b (cov.isCovariantDerivativeOn (s := e.baseSet))
              x (b i) (b j) -
            TauCeti.Manifold.christoffelMap b (covbar.isCovariantDerivativeOn (s := e.baseSet))
              x (b i) (b j)) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hg
  dsimp only
  intro α hx
  rw [deTurckVectorField_eq_sum_chartInvGramMatrix g gbar hg hgbar x α
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [chartLocalFrame_eq_symmL, chartLocalFrame_eq_symmL,
    TauCeti.Manifold.symmL_christoffelMap_sub_christoffelMap _ _ _ hx]

/-- The DeTurck field of two `C^(n+1)` metrics is spatially `C^n` on a `C^(n+2)` manifold.
The statement includes the smooth case `n = ∞`. -/
theorem contMDiff_deTurckVectorField {n m : ℕ∞ω} [IsManifold I m M]
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (gbar : ContMDiffRiemannianMetric I kbar E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) (hgbar : 1 ≤ kbar)
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) (hkbar : n + 1 ≤ kbar) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (g.deTurckVectorField gbar hg hgbar x)) := by
  have : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  have : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  let covbar :=
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hgbar
    CovariantDerivative.leviCivitaConnection I M
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hg
  let _ : IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := k) (le_self_add.trans hk)
  intro x
  let u := (trivializationAt E (TangentSpace I) x).baseSet
  have hu : IsOpen u := (trivializationAt E (TangentSpace I) x).open_baseSet
  have hframe (i : Fin (Module.finrank ℝ E)) :=
    contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x i
  have hdual (i : Fin (Module.finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y (chartDualFrame (I := I) x i y)) u :=
    fun y hy ↦ (contMDiffAt_chartDualFrame x hy i).contMDiffWithinAt
  have hbar (i : Fin (Module.finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y
        (covbar (chartLocalFrame (I := I) x i) y (chartDualFrame (I := I) x i y))) u := by
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gbar.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hgbar
    exact CovariantDerivative.contMDiffOn_leviCivitaConnection_apply hu hm hkbar
      (hdual i) (hframe i)
  have hs := ContMDiffOn.sum_section fun i (_ : i ∈ Finset.univ) ↦
    (CovariantDerivative.contMDiffOn_leviCivitaConnection_apply hu hm hk (hdual i) (hframe i))
      |>.sub_section (hbar i)
  apply (hs.contMDiffAt (hu.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x))).congr_of_eventuallyEq
  filter_upwards [hu.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  congr 1
  exact deTurckVectorField_eq_sum_chartDualFrame g gbar hg hgbar y x
    (by simpa only [u, TangentBundle.trivializationAt_baseSet] using hy)

/-- A positive constant multiple of a metric has zero DeTurck field relative to that metric. -/
@[simp]
theorem deTurckVectorField_rescale_const
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (hg : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).deTurckVectorField g hg hg = 0 := by
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  let cov :=
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g'.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    CovariantDerivative.leviCivitaConnection I M
  let covbar :=
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le hg
    CovariantDerivative.leviCivitaConnection I M
  have hzero : cov.difference covbar = 0 :=
    CovariantDerivative.difference_eq_zero_of_forall fun _ _ hY ↦
      g.leviCivitaConnection_rescale_const_apply hg hc hY
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g'.toRiemannianMetric⟩
  funext x
  rw [deTurckVectorField_eq_metricTrace]
  -- Keep the chosen connections named while rewriting their difference tensor.
  change LinearMap.BilinMap.metricTrace
    (ContinuousLinearMap.toLinearMap₁₂ (cov.difference covbar x)) = 0
  rw [hzero]
  simp

end Bundle.ContMDiffRiemannianMetric
