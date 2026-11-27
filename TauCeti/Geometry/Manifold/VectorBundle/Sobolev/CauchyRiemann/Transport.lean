/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Invariance of the index under bundle isomorphisms

Let `M` be a complex curve without boundary and let `Φ x : V x ≃L[ℂ] W x` be an isomorphism of
complex vector bundles over `M`, smooth as a section of the real hom bundle. A real Cauchy–Riemann
operator `D` on `V` is transported to the operator `σ ↦ Φ ∘ D (Φ⁻¹ σ)` on `W`
(`TauCeti.sectionTransport`), which is again a real Cauchy–Riemann operator, smooth when `D` is
(`TauCeti.contMDiffCovariantDerivativeOn_sectionTransport`).
This file shows that on a closed surface the realizations of `D` and of its transport,
`W^{1,p} → L^p` for `1 < p < ∞`, have the same index (McDuff–Salamon, proof of Theorem C.1.10,
step 1: the index is invariant under bundle isomorphisms).

The Sobolev spaces of `W` are built on the charts of the finite bundle atlas `A` of `V`, as the
atlas `A.ofBaseSet h`. The isomorphism `Φ` induces isomorphisms of Banach spaces
`W^{1,p}(V) ≃ W^{1,p}(W)` (`TauCeti.SobolevSection.bundleEquivL`) and
`L^p(Λ^{0,1} ⊗ V) ≃ L^p(Λ^{0,1} ⊗ W)` (`TauCeti.zeroOneTransportEquivL`), the latter since a
complex linear map sends `(0,1)`-forms to `(0,1)`-forms. They intertwine the two realizations
(`TauCeti.IsRealCauchyRiemannOperator.zeroOneTransportEquivL_comp_sobolevL`): on smooth sections
the realizations are the operators themselves, and smooth sections are dense in `W^{1,p}`
(`TauCeti.SobolevSection.denseRange_ofContMDiffSection`). Conjugation by isomorphisms preserves
Fredholmness and the index.

## Main definitions

* `TauCeti.zeroOneTransportEquivL`: the isomorphism of Sobolev `(0,1)`-forms induced by `Φ`.

## Main results

* `TauCeti.chartValueL_zeroOneTransportEquivL_symm_ae_coord`: the inverse isomorphism of
  `(0,1)`-forms sends `θ` to `Φ⁻¹ ∘ θ`.
* `TauCeti.IsRealCauchyRiemannOperator.zeroOneTransportEquivL_comp_sobolevL`: the induced
  isomorphisms intertwine the realizations of `D` and of its transport.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_sectionTransport`: the realization of the
  transport has the index of the realization of `D`; it is Fredholm for `1 < p < ∞` by
  `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL` applied to
  `TauCeti.IsRealCauchyRiemannOperator.transport_of_contMDiff`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, proof of Theorem C.1.10, step 1.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℂ G W]

local instance instVectorBundleRealTransportV : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

local instance instVectorBundleRealTransportW : VectorBundle ℝ G W :=
  VectorBundle.restrictScalars ℝ ℂ G W

/-! ### Sobolev `(0,1)`-forms -/

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- **Complex linear maps preserve Sobolev `(0,1)`-forms.** An element of `W^{k,p}` of `W`-valued
one-forms whose chart data are the readings of `L ∘ θ`, for fibrewise complex linear maps `L` and a
one-form `θ` which is a `(0,1)`-form almost everywhere in every chart, is a Sobolev
`(0,1)`-form. -/
theorem mem_zeroOneSobolevSections_of_comp {B : FiniteBundleAtlas ℂ M G W}
    {w : SobolevSection B.tangentHom μ p k} (L : ∀ x, V x →L[ℂ] W x)
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, B.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (B.tangentHom.image i)]
        B.tangentHom.coord i fun x ↦ ((L x).restrictScalars ℝ).comp (θ x))
    (hθ : ∀ i, ∀ᵐ y ∂μ.restrict (B.image i),
      (ofComplexManifold ℂ M).IsZeroOneForm (θ ((B.chart i).symm y))) :
    w ∈ zeroOneSobolevSections B μ p k :=
  (mem_zeroOneSobolevSections_iff_isZeroOneForm hw).2 fun i ↦
    (ae_image_tangentHom_iff B μ i).2 <| (hθ i).mono fun _ hy ↦ hy.restrictScalars_comp _

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, ℂ)]
  {Φ : ∀ x, V x ≃L[ℂ] W x}
  (hΦ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F →L[ℝ] G)) ∞ fun x ↦
    TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
      ((Φ x).restrictScalars' ℝ : V x →L[ℝ] W x))
  (A : FiniteBundleAtlas ℂ M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)

include hΦ in
/-- A complex linear smooth bundle isomorphism sends Sobolev `(0,1)`-forms to `(0,1)`-forms. -/
theorem tangentHomEquivL_mem_zeroOneSobolevSections {w : SobolevSection A.tangentHom μ p k}
    (hw : w ∈ zeroOneSobolevSections A μ p k) :
    SobolevSection.tangentHomEquivL A h μ p k hΦ w ∈
      zeroOneSobolevSections (A.ofBaseSet h) μ p k := by
  obtain ⟨θ, hθ⟩ := SobolevSection.exists_ae_eq_coord w
  have h01 := (mem_zeroOneSobolevSections_iff_isZeroOneForm hθ).1 hw
  refine mem_zeroOneSobolevSections_of_comp μ p k (fun x ↦ (Φ x : V x →L[ℂ] W x))
    (θ := θ) (fun i ↦ ?_) fun (i : Fin A.n) ↦ ?_
  · rw [SobolevSection.tangentHomEquivL_apply]
    simpa [ContinuousLinearEquiv.toContinuousLinearMap_restrictScalars'] using
      SobolevSection.chartValueL_tangentHomMapL_ae_coord (h := h) (hΦ := hΦ) hθ i
  · have := (ae_image_tangentHom_iff A μ i).1 (h01 i)
    rwa [← image_ofBaseSet (h := h)] at this

include hΦ in
/-- The inverse of a complex linear smooth bundle isomorphism sends Sobolev `(0,1)`-forms to
`(0,1)`-forms. -/
theorem tangentHomEquivL_symm_mem_zeroOneSobolevSections
    {w : SobolevSection (A.ofBaseSet h).tangentHom μ p k}
    (hw : w ∈ zeroOneSobolevSections (A.ofBaseSet h) μ p k) :
    (SobolevSection.tangentHomEquivL A h μ p k hΦ).symm w ∈ zeroOneSobolevSections A μ p k := by
  obtain ⟨θ, hθ⟩ := SobolevSection.exists_ae_eq_coord w
  have h01 := (mem_zeroOneSobolevSections_iff_isZeroOneForm hθ).1 hw
  refine mem_zeroOneSobolevSections_of_comp μ p k (fun x ↦ ((Φ x).symm : W x →L[ℂ] V x))
    (θ := θ) (fun i ↦ ?_) fun i ↦ ?_
  · simpa [ContinuousLinearEquiv.restrictScalars'_symm,
      ContinuousLinearEquiv.toContinuousLinearMap_restrictScalars'] using
      SobolevSection.chartValueL_tangentHomEquivL_symm_ae_coord (hΦ := hΦ) hθ i
  · have := (ae_image_tangentHom_iff (A.ofBaseSet h) μ i).1 (h01 i)
    rwa [image_ofBaseSet] at this

/-- **Bundle isomorphisms act on Sobolev `(0,1)`-forms.** The isomorphism of Banach spaces
`W^{k,p}(Λ^{0,1} ⊗ V) ≃ W^{k,p}(Λ^{0,1} ⊗ W)` induced by a smooth complex bundle isomorphism `Φ`,
sending a `(0,1)`-form `θ` to `Φ ∘ θ`. It is the restriction of
`TauCeti.SobolevSection.tangentHomEquivL`. -/
def zeroOneTransportEquivL :
    zeroOneSobolevSections A μ p k ≃L[ℝ] zeroOneSobolevSections (A.ofBaseSet h) μ p k :=
  .ofContinuousLinearMap
    ((((SobolevSection.tangentHomEquivL A h μ p k hΦ :
        SobolevSection A.tangentHom μ p k →L[ℝ]
          SobolevSection (A.ofBaseSet h).tangentHom μ p k)).comp
      (zeroOneSobolevSections A μ p k).subtypeL).codRestrict _ fun w ↦
        tangentHomEquivL_mem_zeroOneSobolevSections μ p k hΦ A h w.property)
    ((((SobolevSection.tangentHomEquivL A h μ p k hΦ).symm :
        SobolevSection (A.ofBaseSet h).tangentHom μ p k →L[ℝ]
          SobolevSection A.tangentHom μ p k).comp
      (zeroOneSobolevSections (A.ofBaseSet h) μ p k).subtypeL).codRestrict _ fun w ↦
        tangentHomEquivL_symm_mem_zeroOneSobolevSections μ p k hΦ A h w.property)
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext <|
      (SobolevSection.tangentHomEquivL A h μ p k hΦ).apply_symm_apply _)
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext <|
      (SobolevSection.tangentHomEquivL A h μ p k hΦ).symm_apply_apply _)

/-- The underlying one-form of the image of a `(0,1)`-form under `zeroOneTransportEquivL`. -/
@[simp]
theorem coe_zeroOneTransportEquivL_apply (w : zeroOneSobolevSections A μ p k) :
    (zeroOneTransportEquivL μ p k hΦ A h w : SobolevSection (A.ofBaseSet h).tangentHom μ p k) =
      SobolevSection.tangentHomEquivL A h μ p k hΦ w :=
  (rfl)

/-- The underlying one-form of the image of a `(0,1)`-form under the inverse of
`zeroOneTransportEquivL`. -/
@[simp]
theorem coe_zeroOneTransportEquivL_symm_apply
    (w : zeroOneSobolevSections (A.ofBaseSet h) μ p k) :
    ((zeroOneTransportEquivL μ p k hΦ A h).symm w : SobolevSection A.tangentHom μ p k) =
      (SobolevSection.tangentHomEquivL A h μ p k hΦ).symm w :=
  (rfl)

variable {μ p k hΦ A h} in
/-- The image under the inverse of `zeroOneTransportEquivL` of a `(0,1)`-form with one-form `θ`
has one-form `Φ⁻¹ ∘ θ`. -/
theorem chartValueL_zeroOneTransportEquivL_symm_ae_coord
    {w : zeroOneSobolevSections (A.ofBaseSet h) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] W x}
    (hθ : ∀ i, (A.ofBaseSet h).tangentHom.sectionChartData.chartValueL μ p k i
      (w : SobolevSection (A.ofBaseSet h).tangentHom μ p k)
        =ᵐ[μ.restrict ((A.ofBaseSet h).tangentHom.image i)] (A.ofBaseSet h).tangentHom.coord i θ)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i
      ((zeroOneTransportEquivL μ p k hΦ A h).symm w : SobolevSection A.tangentHom μ p k)
        =ᵐ[μ.restrict (A.tangentHom.image i)]
          A.tangentHom.coord i fun x ↦
            (((Φ x).symm : W x →L[ℂ] V x).restrictScalars ℝ).comp (θ x) := by
  rw [coe_zeroOneTransportEquivL_symm_apply]
  simpa [ContinuousLinearEquiv.restrictScalars'_symm,
    ContinuousLinearEquiv.toContinuousLinearMap_restrictScalars'] using
    SobolevSection.chartValueL_tangentHomEquivL_symm_ae_coord (hΦ := hΦ) hθ i

/-! ### Invariance of the index -/

namespace IsRealCauchyRiemannOperator

variable [T2Space M] {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

/-- **The isomorphisms induced by `Φ` intertwine the realizations.** For `1 ≤ p < ∞`, the
realization `W^{1,p}(W) → L^p(Λ^{0,1} ⊗ W)` of the transport of `D` along `Φ`, composed with the
isomorphism `W^{1,p}(V) ≃ W^{1,p}(W)`, is the realization of `D` followed by the isomorphism
`L^p(Λ^{0,1} ⊗ V) ≃ L^p(Λ^{0,1} ⊗ W)`. -/
theorem zeroOneTransportEquivL_comp_sobolevL (hp : p ≠ ⊤) :
    (zeroOneTransportEquivL μ p 0 hΦ A h :
        zeroOneSobolevSections A μ p 0 →L[ℝ] zeroOneSobolevSections (A.ofBaseSet h) μ p 0).comp
      (hD.sobolevL A hDs μ p) =
    ((hD.transport_of_contMDiff hΦ).sobolevL
      (A.ofBaseSet h) (hDs.sectionTransport_of_contMDiff hΦ)
        μ p).comp
      (SobolevSection.bundleEquivL A h μ p 1 hΦ :
        SobolevSection A μ p 1 →L[ℝ] SobolevSection (A.ofBaseSet h) μ p 1) := by
  refine ContinuousLinearMap.ext fun w ↦
    (SobolevSection.denseRange_ofContMDiffSection A μ p 1 hp).induction_on w
      (isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _))
      fun s ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    SobolevSection.coe_bundleEquivL, SobolevSection.bundleMapL_ofContMDiffSection]
  -- Both sides are the `(0,1)`-form `Φ ∘ D s`.
  have hDs' : sectionTransport Φ D (fun x ↦ ((Φ x).restrictScalars' ℝ : V x →L[ℝ] W x) (s x)) =
      fun x ↦ ((Φ x).restrictScalars' ℝ : V x →L[ℝ] W x).comp (D s x) := by
    funext x
    simp only [sectionTransport_apply, ContinuousLinearEquiv.toContinuousLinearMap_restrictScalars',
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  refine Subtype.ext (SobolevSection.eq_of_ae_eq_coord
    (s := fun x ↦ ((Φ x).restrictScalars' ℝ : V x →L[ℝ] W x).comp (D s x))
    (fun (i : Fin A.n) ↦ ?_) fun (i : Fin A.n) ↦ ?_)
  · rw [ContinuousLinearEquiv.coe_coe, coe_zeroOneTransportEquivL_apply,
      SobolevSection.tangentHomEquivL_apply]
    refine SobolevSection.chartValueL_tangentHomMapL_ae_coord (fun (i : Fin A.n) ↦ ?_) i
    rw [image_tangentHom]
    exact chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs μ p s i
  · have key := chartValueL_sobolevL_ofContMDiffSection_ae (A.ofBaseSet h)
      (hD.transport_of_contMDiff hΦ)
      (hDs.sectionTransport_of_contMDiff hΦ) μ p
      ⟨fun x ↦ ((Φ x).restrictScalars' ℝ : V x →L[ℝ] W x) (s x),
        ContMDiff.clm_bundle_apply (hΦ.of_le (by exact_mod_cast le_top)) s.contMDiff⟩ i
    have hμ : μ.restrict ((A.ofBaseSet h).image i : Set ℂ) =
        μ.restrict ((A.ofBaseSet h).tangentHom.image i : Set ℂ) :=
      congrArg (fun U : TopologicalSpace.Opens ℂ ↦ μ.restrict (U : Set ℂ))
        ((A.ofBaseSet h).image_tangentHom i).symm
    simp only [hμ, ContMDiffSection.coeFn_mk, hDs'] at key
    exact key

/-- **The index is invariant under bundle isomorphisms** (McDuff–Salamon, proof of Theorem C.1.10,
step 1). On a closed surface, the realizations `W^{1,p} → L^p` of a smooth real Cauchy–Riemann
operator `D` on `V` and of its transport `σ ↦ Φ ∘ D (Φ⁻¹ σ)` along a smooth bundle isomorphism
`Φ : V ≃ W` have the same index, for every finite `p ≥ 1` (they are Fredholm for `p > 1`). -/
theorem index_sobolevL_sectionTransport (hp_top : p ≠ ⊤) :
    ((hD.transport_of_contMDiff hΦ).sobolevL
      (A.ofBaseSet h) (hDs.sectionTransport_of_contMDiff hΦ)
        μ p).index = (hD.sobolevL A hDs μ p).index := by
  have hS : (hD.transport_of_contMDiff hΦ).sobolevL
      (A.ofBaseSet h) (hDs.sectionTransport_of_contMDiff hΦ)
        μ p =
        ((zeroOneTransportEquivL μ p 0 hΦ A h : zeroOneSobolevSections A μ p 0 →L[ℝ]
          zeroOneSobolevSections (A.ofBaseSet h) μ p 0).comp
            (hD.sobolevL A hDs μ p)).comp ((SobolevSection.bundleEquivL A h μ p 1 hΦ).symm :
              SobolevSection (A.ofBaseSet h) μ p 1 →L[ℝ] SobolevSection A μ p 1) := by
    rw [zeroOneTransportEquivL_comp_sobolevL μ p hΦ A h hD hDs hp_top]
    ext w : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hS, ContinuousLinearMap.index_comp_equiv, ContinuousLinearMap.index_equiv_comp]

end IsRealCauchyRiemannOperator

end TauCeti
