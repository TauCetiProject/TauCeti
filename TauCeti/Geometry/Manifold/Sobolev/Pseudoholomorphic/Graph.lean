/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Graph
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Graph
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Atlas

/-!
# Graphs of weak pseudoholomorphic maps

Let `X` be a Riemann surface with its structure `j`, `M` a manifold modelled on a boundaryless
model, `J` a domain-dependent almost complex structure on `M` and `ν` an inhomogeneous term for
`(j, J)`. Gromov's graph structure `ν.graphStructure` on `X × M` sends `(ζ, v)` at `(x, y)` to
`(j ζ, J v - 2 J ν ζ)` (`TauCeti.InhomogeneousTerm.graphStructure`); regard it as a structure on
`X × M` that does not depend on the domain point. This file proves Gromov's graph construction for
weak solutions on a Riemann surface: a map `u : X → M` is weakly pseudoholomorphic for `(J, ν)` on
`s` exactly when its graph `x ↦ (x, u x)` is weakly pseudoholomorphic on `s` for Gromov's
structure, with no inhomogeneous term. The exponent is arbitrary.

In a holomorphic chart `φ` of `X` and a chart `ψ` of `M`, the graph read in the product chart
`φ × ψ` is the planar graph `z ↦ (z, w z)` of the coordinate expression `w` of `u`, and Gromov's
structure read in that chart turns the homogeneous equation for the graph derivative `(id, D)`
into the coordinate equation `D 1 + J_φψ (D i) = η_φψ` for `D`. The planar graph equivalence
`TauCeti.isWeakCauchyRiemannOn_graph_iff` then compares the two coordinate equations. The product
charts are tested against their own first factor, which
`TauCeti.isWeakPseudoholomorphicOn_of_forall_exists_chart` allows.

## Main results

* `TauCeti.isWeakPseudoholomorphicOn_graph_iff`: the graph equivalence on a set.
* `TauCeti.isWeakPseudoholomorphic_graph_iff`: the graph equivalence on the whole surface.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 8.1 and Appendix B.4.
-/

public section

open Set
open scoped Manifold ContDiff TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-! ### The graph equation in product charts -/

omit [IsManifold 𝓘(ℂ) ∞ X] [IsManifold I ∞ M] in
/-- The preferred chart of `X × M` at `(x₀, y₀)`, read in `ℂ × E`, acts componentwise. -/
private theorem extendTrans_prod_apply (x₀ : X) (y₀ : M) (q : X × M) :
    (chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I) (Homeomorph.refl (ℂ × E)) q =
      (chartAt ℂ x₀ q.1, (chartAt H y₀).extendTrans I (Homeomorph.refl E) q.2) := by
  rw [OpenPartialHomeomorph.coe_extendTrans_refl, OpenPartialHomeomorph.coe_extendTrans_refl]
  exact (extChartAt_prod_apply (x₀, y₀) q).trans (Prod.ext (by simp) rfl)

/-- The preferred chart of `X × M` at `(x₀, y₀)`, read in `ℂ × E`, differentiates componentwise
on its source. -/
private theorem mfderiv_extendTrans_prod_apply (x₀ : X) (y₀ : M) {q : X × M}
    (hq : q ∈ (chartAt (ModelProd ℂ H) (x₀, y₀)).source) (v : TangentSpace (𝓘(ℝ, ℂ).prod I) q) :
    mfderiv (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ × E) ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans
        (𝓘(ℝ, ℂ).prod I) (Homeomorph.refl (ℂ × E))) q v =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x₀) q.1 v.1,
        mfderiv I 𝓘(ℝ, E) ((chartAt H y₀).extendTrans I (Homeomorph.refl E)) q.2 v.2) := by
  have hφ : ⇑(chartAt ℂ x₀) = extChartAt 𝓘(ℝ, ℂ) x₀ := by
    funext x
    simp
  rw [OpenPartialHomeomorph.coe_extendTrans_refl, OpenPartialHomeomorph.coe_extendTrans_refl, hφ]
  exact mfderiv_extChartAt_prod_apply (by rwa [extChartAt_source]) v

/-- The coordinate equation read in a chart `ψ` of `M`: at `(z, w)`, for the vectors
`c = dψ⁻¹ (D 1)`, `d = dψ⁻¹ (D i)` and `a = dφ⁻¹ 1`, the equation `c + J d = 2 ν a` at
`(φ⁻¹ z, ψ⁻¹ w)` is the coordinate equation `D 1 + J_φψ (D i) = η_φψ`. -/
private theorem add_tangentEndomorphism_eq_iff (φ : OpenPartialHomeomorph X ℂ) {y₀ : M} {z : ℂ}
    {w : E} (hw : w ∈ ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).target)
    (D : ℂ →L[ℝ] E) :
    mfderiv 𝓘(ℝ, E) I ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w (D 1) +
        J.tangentEndomorphism (φ.symm z, ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w)
          (mfderiv 𝓘(ℝ, E) I ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w
            (D Complex.I)) =
        (2 : ℝ) • ν.val.tangentHom
          (φ.symm z, ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)) ↔
      D 1 + J.chartField φ ((chartAt H y₀).extendTrans I (Homeomorph.refl E)) z w
          (D Complex.I) =
        ν.chartTerm φ ((chartAt H y₀).extendTrans I (Homeomorph.refl E)) z w := by
  set ψ := (chartAt H y₀).extendTrans I (Homeomorph.refl E)
  have hψm : chartAt H y₀ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hψ := (chartAt H y₀).mdifferentiableAt_extendTrans_refl hψm (by simp)
    (by simpa only [ψ, OpenPartialHomeomorph.extendTrans_source] using ψ.map_target hw)
  have hψs := (chartAt H y₀).mdifferentiableAt_extendTrans_refl_symm hψm (by simp) hw
  -- Push the equation forward along `ψ`, whose derivative at `ψ⁻¹ w` is injective.
  have hl := ψ.mfderiv_symm_apply_mfderiv_apply (ψ.map_target hw) hψ
    ((chartAt H y₀).mdifferentiableAt_extendTrans_refl_symm hψm (by simp)
      (ψ.map_source (ψ.map_target hw)))
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) ψ (ψ.symm w)) :=
    fun t t' h ↦ (hl t).symm.trans ((congrArg _ h).trans (hl t'))
  have hF : J.chartField φ ψ z w (D Complex.I) = mfderiv I 𝓘(ℝ, E) ψ (ψ.symm w)
      (J.tangentEndomorphism (φ.symm z, ψ.symm w) (mfderiv 𝓘(ℝ, E) I ψ.symm w (D Complex.I))) := by
    rw [ContMDiffAlmostComplexStructureFamily.chartField_apply,
      ContMDiffAlmostComplexStructure.chartPushforward_apply,
      ContMDiffAlmostComplexStructureFamily.freeze_apply]
  have hc : mfderiv I 𝓘(ℝ, E) ψ (ψ.symm w) (mfderiv 𝓘(ℝ, E) I ψ.symm w (D 1)) = D 1 :=
    ψ.mfderiv_apply_mfderiv_symm_apply hw hψ hψs _
  rw [← hinj.eq_iff, map_add, map_smul, hc, hF,
    InhomogeneousTerm.chartTerm_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact Iff.rfl

omit [I.Boundaryless] in
/-- The coordinate vector `∂ₜ = dφ⁻¹ i` of a holomorphic chart `φ` is `j ∂ₛ`. -/
private theorem mfderiv_symm_apply_I (ℓ : ℕ∞) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {z : ℂ} (hz : z ∈ φ.target) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z Complex.I =
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ (φ.symm z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ)) := by
  have hI := (mdifferentiableAt_symm_of_mem_maximalAtlas hφ hz).mfderiv_ofComplexManifold_apply
    (1 : ℂ)
  rw [SmoothAlmostComplexStructure.ofComplexManifold_apply (M := ℂ), smul_eq_mul, mul_one] at hI
  rw [hI, SmoothAlmostComplexStructure.toContMDiff_apply]

/-- **Pulling the graph equation back through a product chart.** In the preferred chart `φ` of `X`
at `x₀` and the product chart `Ψ = φ × ψ` of `X × M` at `(x₀, y₀)`, the vectors `(1, D 1)` and
`(i, D i)` at `(z, w)` are the images under `dΨ` of the vectors `(a, dψ⁻¹ (D 1))` and
`(j a, dψ⁻¹ (D i))` at `q₀ = (φ⁻¹ z, ψ⁻¹ w)`, where `a = dφ⁻¹ 1`, since the coordinate vector
`∂ₜ = dφ⁻¹ i` of the holomorphic chart `φ` is `j ∂ₛ`. As `dΨ` is injective and intertwines the
graph structure with its pushforward, the homogeneous equation in the chart is the homogeneous
equation at `q₀`. -/
private theorem add_chartPushforward_graphStructure_eq_zero_iff_add (x₀ : X) (y₀ : M) {z : ℂ}
    {w : E} (hz : z ∈ (chartAt ℂ x₀).target)
    (hw : w ∈ ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).target) (D : ℂ →L[ℝ] E) :
    ((1 : ℂ), D 1) + ν.graphStructure.chartPushforward
        ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
          (Homeomorph.refl (ℂ × E))) (z, w) (Complex.I, D Complex.I) = 0 ↔
      (Manifold.tangentSpaceProdEquiv
          ((chartAt ℂ x₀).symm z, ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w)).symm
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x₀).symm z (1 : ℂ),
            mfderiv 𝓘(ℝ, E) I ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w (D 1)) +
        ν.graphStructure
          ((chartAt ℂ x₀).symm z, ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w)
          ((Manifold.tangentSpaceProdEquiv
            ((chartAt ℂ x₀).symm z, ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w)).symm
            ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ
              ((chartAt ℂ x₀).symm z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x₀).symm z (1 : ℂ)),
            mfderiv 𝓘(ℝ, E) I ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).symm w
              (D Complex.I))) = 0 := by
  set Ψ := (chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
    (Homeomorph.refl (ℂ × E))
  set ψ := (chartAt H y₀).extendTrans I (Homeomorph.refl E)
  set φ := chartAt ℂ x₀
  have hφm : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X := IsManifold.chart_mem_maximalAtlas _
  have hφm' := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφm
  have hψm : chartAt H y₀ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hΨm := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℂ).prod I) (n := ∞) (x₀, y₀)
  have hψw : ψ.symm w ∈ (chartAt H y₀).source := by
    simpa only [ψ, OpenPartialHomeomorph.extendTrans_source] using ψ.map_target hw
  have hq₀ : (φ.symm z, ψ.symm w) ∈ (chartAt (ModelProd ℂ H) (x₀, y₀)).source := by
    rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source]
    exact Set.mk_mem_prod (φ.map_target hz) hψw
  have hq₀' : (φ.symm z, ψ.symm w) ∈ Ψ.source := by
    rwa [OpenPartialHomeomorph.extendTrans_source]
  have hΨq₀ : Ψ (φ.symm z, ψ.symm w) = (z, w) := by
    rw [extendTrans_prod_apply]
    exact Prod.ext (φ.right_inv hz) (ψ.right_inv hw)
  have hΨ := (chartAt _ (x₀, y₀)).mdifferentiableAt_extendTrans_refl hΨm (by simp) hq₀
  have hΨs := (chartAt _ (x₀, y₀)).mdifferentiableAt_extendTrans_refl_symm hΨm (by simp)
    (Ψ.map_source hq₀')
  have hφr := φ.mfderiv_apply_mfderiv_symm_apply hz
    (mdifferentiableAt_of_mem_maximalAtlas hφm' (φ.map_target hz))
    (mdifferentiableAt_symm_of_mem_maximalAtlas hφm' hz)
  have hψr := ψ.mfderiv_apply_mfderiv_symm_apply hw
    ((chartAt H y₀).mdifferentiableAt_extendTrans_refl hψm (by simp) hψw)
    ((chartAt H y₀).mdifferentiableAt_extendTrans_refl_symm hψm (by simp) hw)
  -- The derivative of `Ψ` intertwines the graph structure with its pushforward.
  have hint := ν.graphStructure.mfderiv_comp_toEndomorphism Ψ hq₀' hΨ hΨs
  rw [hΨq₀] at hint
  have hl := Ψ.mfderiv_symm_apply_mfderiv_apply hq₀' hΨ hΨs
  refine Iff.trans ?_ (map_eq_zero_iff _
    fun t t' h ↦ (hl t).symm.trans ((congrArg _ h).trans (hl t')))
  refine Iff.of_eq (congrArg (· = 0) ?_)
  have hint' : ∀ v, ν.graphStructure.chartPushforward Ψ (z, w)
      (mfderiv (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ × E) Ψ (φ.symm z, ψ.symm w) v) =
        mfderiv (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ × E) Ψ (φ.symm z, ψ.symm w)
          (ν.graphStructure (φ.symm z, ψ.symm w) v) :=
    fun v ↦ (DFunLike.congr_fun hint v).symm
  rw [map_add, ← hint']
  refine congrArg₂ (· + ·) ?_ (congrArg _ ?_) <;>
    rw [Manifold.tangentSpaceProdEquiv_symm_apply] <;>
    refine (Prod.ext ?_ (hψr _).symm).trans (mfderiv_extendTrans_prod_apply x₀ y₀ hq₀ _).symm
  · exact (hφr _).symm
  · exact (hφr _).symm.trans (congrArg _ (mfderiv_symm_apply_I ℓ hφm hz))

/-- **The graph equation in product charts.** In the preferred chart `φ` of `X` at `x₀` and the
product chart `φ × ψ` of `X × M` at `(x₀, y₀)`, Gromov's structure turns the homogeneous equation
for the graph derivative `(id, D)` at `(z, w)` into the coordinate equation
`D 1 + J_φψ (D i) = η_φψ` for `D`. -/
private theorem add_chartPushforward_graphStructure_eq_zero_iff (x₀ : X) (y₀ : M) {z : ℂ}
    {w : E} (hz : z ∈ (chartAt ℂ x₀).target)
    (hw : w ∈ ((chartAt H y₀).extendTrans I (Homeomorph.refl E)).target) (D : ℂ →L[ℝ] E) :
    ((1 : ℂ), D 1) + ν.graphStructure.chartPushforward
        ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
          (Homeomorph.refl (ℂ × E))) (z, w) (Complex.I, D Complex.I) = 0 ↔
      D 1 + J.chartField (chartAt ℂ x₀) ((chartAt H y₀).extendTrans I (Homeomorph.refl E)) z w
          (D Complex.I) =
        ν.chartTerm (chartAt ℂ x₀) ((chartAt H y₀).extendTrans I (Homeomorph.refl E)) z w :=
  (add_chartPushforward_graphStructure_eq_zero_iff_add x₀ y₀ hz hw D).trans
    ((InhomogeneousTerm.add_graphStructure_eq_zero_iff ν _ _ _ _).trans
      (add_tangentEndomorphism_eq_iff (chartAt ℂ x₀) hw D))

/-- In the preferred charts, the coordinate equation of the graph in the product chart at
`(x₀, y₀)` is the coordinate equation of `u` in the chart at `y₀`. -/
private theorem isWeakCauchyRiemannOn_chartAt_graph_iff [CompleteSpace E] (x₀ : X) (y₀ : M) :
    IsWeakCauchyRiemannOn p ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹'
        (s ∩ (fun x ↦ (x, u x)) ⁻¹' (chartAt (ModelProd ℂ H) (x₀, y₀)).source))
      ((ContMDiffAlmostComplexStructureFamily.const (IP := 𝓘(ℝ, ℂ)) (P := X)
          ν.graphStructure).chartField (chartAt ℂ x₀)
        ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
          (Homeomorph.refl (ℂ × E))))
      ((0 : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ)
          (ContMDiffAlmostComplexStructureFamily.const (IP := 𝓘(ℝ, ℂ)) (P := X)
            ν.graphStructure)).chartTerm (chartAt ℂ x₀)
        ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
          (Homeomorph.refl (ℂ × E))))
      ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
          (Homeomorph.refl (ℂ × E)) ∘ (fun x ↦ (x, u x)) ∘ (chartAt ℂ x₀).symm) ↔
      IsWeakCauchyRiemannOn p
        ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source))
        (J.chartField (chartAt ℂ x₀) ((chartAt H y₀).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x₀) ((chartAt H y₀).extendTrans I (Homeomorph.refl E)))
        ((chartAt H y₀).extendTrans I (Homeomorph.refl E) ∘ u ∘ (chartAt ℂ x₀).symm) := by
  set φ := chartAt ℂ x₀
  set ψ := (chartAt H y₀).extendTrans I (Homeomorph.refl E)
  have hset : φ.target ∩ φ.symm ⁻¹' (s ∩ (fun x ↦ (x, u x)) ⁻¹'
      (chartAt (ModelProd ℂ H) (x₀, y₀)).source) =
      φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source, mem_prod]
    exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.2⟩, fun h ↦ ⟨h.1, h.2.1, φ.map_target h.1, h.2.2⟩⟩
  -- On the chart target, the graph read in the product chart is the planar graph of `ψ ∘ u`.
  have hgraph : EqOn (fun z ↦ ContinuousLinearEquiv.refl ℝ (ℂ × E) (z, (ψ ∘ u ∘ φ.symm) z))
      ((chartAt (ModelProd ℂ H) (x₀, y₀)).extendTrans (𝓘(ℝ, ℂ).prod I)
        (Homeomorph.refl (ℂ × E)) ∘ (fun x ↦ (x, u x)) ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)) := fun z hz ↦ by
    simp only [Function.comp_apply, ContinuousLinearEquiv.refl_apply]
    rw [extendTrans_prod_apply]
    exact Prod.ext (φ.right_inv hz.1).symm rfl
  rw [hset, ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTerm_zero, ← isWeakCauchyRiemannOn_congr hgraph]
  refine isWeakCauchyRiemannOn_graph_iff _ fun z hz D ↦ ?_
  exact add_chartPushforward_graphStructure_eq_zero_iff x₀ y₀ hz.1
    (ψ.map_source (by simpa [ψ] using hz.2.2)) D

/-! ### The graph equivalence -/

variable [CompleteSpace E]

/-- **Gromov's graph construction for weak pseudoholomorphic maps.** For any exponent, a map
`u : X → M` is weakly pseudoholomorphic on `s` for `(J, ν)` exactly when its graph
`x ↦ (x, u x)` is weakly pseudoholomorphic on `s` for Gromov's graph structure
`TauCeti.InhomogeneousTerm.graphStructure` of `ν` on `X × M`, regarded as independent of the
domain point, with no inhomogeneous term. -/
theorem isWeakPseudoholomorphicOn_graph_iff :
    IsWeakPseudoholomorphicOn (ContMDiffAlmostComplexStructureFamily.const ν.graphStructure) 0 p
        (fun x ↦ (x, u x)) s ↔
      IsWeakPseudoholomorphicOn J ν p u s := by
  constructor
  · intro h
    refine isWeakPseudoholomorphicOn_iff_chartAt.2 ⟨continuousOn_snd.comp h.continuousOn
      (mapsTo_univ _ _), fun x₀ y₀ ↦ ?_⟩
    exact (isWeakCauchyRiemannOn_chartAt_graph_iff x₀ y₀).1
      (h.isWeakCauchyRiemannOn_chart (IsManifold.chart_mem_maximalAtlas x₀)
        (IsManifold.chart_mem_maximalAtlas (x₀, y₀)))
  · intro h
    refine isWeakPseudoholomorphicOn_of_forall_exists_chart (A := range (chartAt ℂ))
      (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
      (B := range (chartAt (ModelProd ℂ H)))
      (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
      (fun x _ ↦ ⟨_, mem_range_self _, mem_chart_source _ _⟩)
      (continuousOn_id.prodMk h.continuousOn) ?_
    rintro _ ⟨⟨x₀, y₀⟩, rfl⟩ x - hx
    refine ⟨chartAt ℂ x₀, mem_range_self x₀, (by simpa using hx : _ ∧ _).1, ?_⟩
    exact (isWeakCauchyRiemannOn_chartAt_graph_iff x₀ y₀).2
      (h.isWeakCauchyRiemannOn_chart (IsManifold.chart_mem_maximalAtlas x₀)
        (IsManifold.chart_mem_maximalAtlas y₀))

/-- **Gromov's graph construction for weak pseudoholomorphic maps on the whole surface.** For any
exponent, a map `u : X → M` is weakly pseudoholomorphic for `(J, ν)` exactly when its graph is
weakly pseudoholomorphic for Gromov's graph structure of `ν` on `X × M`, with no inhomogeneous
term. -/
theorem isWeakPseudoholomorphic_graph_iff :
    IsWeakPseudoholomorphic (ContMDiffAlmostComplexStructureFamily.const ν.graphStructure) 0 p
        (fun x ↦ (x, u x)) ↔
      IsWeakPseudoholomorphic J ν p u := by
  rw [← isWeakPseudoholomorphicOn_univ, ← isWeakPseudoholomorphicOn_univ,
    isWeakPseudoholomorphicOn_graph_iff]

end TauCeti
