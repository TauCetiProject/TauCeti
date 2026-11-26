/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Constructions
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Invariance of the index under bundle isomorphisms

Let `M` be a complex curve without boundary and let `Φ x : V x ≃L[ℂ] W x` be an isomorphism of
complex vector bundles over `M`, smooth as a section of the real hom bundle. A real Cauchy–Riemann
operator `D` on `V` is transported to the operator `σ ↦ Φ ∘ D (Φ⁻¹ σ)` on `W`
(`TauCeti.sectionTransport`), which is again a real Cauchy–Riemann operator, smooth when `D` is.
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

* `TauCeti.contMDiffCovariantDerivativeOn_sectionTransport`: the transport of a smooth operator
  along a smooth bundle isomorphism is smooth.
* `TauCeti.IsRealCauchyRiemannOperator.zeroOneTransportEquivL_comp_sobolevL`: the induced
  isomorphisms intertwine the realizations of `D` and of its transport.
* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL_sectionTransport`,
  `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_sectionTransport`: the realization of the
  transport is Fredholm with the index of the realization of `D`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, proof of Theorem C.1.10, step 1.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

/-! ### Smoothness of the transported operator -/

section Smooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W]
  {Φ : ∀ x, V x ≃L[ℂ] W x} {n : WithTop ℕ∞}

/-- `Φ x` as an isomorphism of real vector spaces. -/
private def realEquiv (Φ : ∀ x, V x ≃L[ℂ] W x) (x : M) : V x ≃L[ℝ] W x where
  toLinearEquiv := (Φ x).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (Φ x).continuous
  continuous_invFun := (Φ x).symm.continuous

/-- The inverses of a `Cⁿ` bundle isomorphism form a `Cⁿ` bundle isomorphism. -/
private theorem contMDiff_symm
    (hΦ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) n fun x ↦
      TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
        ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ)) :
    ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) n fun x ↦
      TotalSpace.mk' (G →L[ℝ] F) (E := fun x ↦ W x →L[ℝ] V x) x
        (((Φ x).symm : W x →L[ℂ] V x).restrictScalars ℝ) :=
  -- `realEquiv Φ x` is `Φ x` with the real structure, so its coercion is the realification.
  ContMDiff.clm_bundle_equiv_symm (Φ := realEquiv Φ) hΦ

/-- The inverse of a `Cⁿ` bundle isomorphism, `n ≠ 0`, preserves differentiability of sections. -/
theorem mdifferentiableAt_symm_apply_of_contMDiff
    (hΦ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) n fun x ↦
      TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
        ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ)) (hn : n ≠ 0) {σ : ∀ x, W x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, G)) (fun y ↦ TotalSpace.mk' G y (σ y)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y ((Φ y).symm (σ y))) x :=
  ((contMDiff_symm hΦ x).mdifferentiableAt hn).clm_bundle_apply hσ

/-- **Transport preserves smoothness.** If an operator `D` sends `C^(k + 1)` sections of `V` to
`Cᵏ` `V`-valued one-forms, then its transport along a `C^(k + 1)` bundle isomorphism `Φ` sends
`C^(k + 1)` sections of `W` to `Cᵏ` `W`-valued one-forms. -/
theorem contMDiffCovariantDerivativeOn_sectionTransport [IsManifold I 1 M] {k : WithTop ℕ∞}
    (hΦ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) (k + 1) fun x ↦
      TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
        ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ))
    {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
    (hDs : ContMDiffCovariantDerivativeOn F k D univ) :
    ContMDiffCovariantDerivativeOn G k (sectionTransport Φ D) univ where
  contMDiff {σ} hσ := by
    have hDτ := hDs.contMDiff (ContMDiffOn.clm_bundle_apply (contMDiff_symm hΦ).contMDiffOn hσ)
    simp only [sectionTransport_apply]
    exact fun x _ ↦ (((hΦ x).of_le le_self_add).clm_bundle_comp
      ((hDτ x (mem_univ x)).contMDiffAt Filter.univ_mem)).contMDiffWithinAt

end Smooth

/-! ### Closed surfaces -/

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

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, ℂ)]
  {Φ : ∀ x, V x ≃L[ℂ] W x}
  (hΦ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F →L[ℝ] G)) ∞ fun x ↦
    TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
      ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ))

/-! ### Sobolev `(0,1)`-forms -/

variable (A : FiniteBundleAtlas ℂ M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

include hΦ in
/-- A complex linear smooth bundle morphism sends Sobolev `(0,1)`-forms to `(0,1)`-forms. -/
theorem tangentHomMapL_mem_zeroOneSobolevSections {w : SobolevSection A.tangentHom μ p k}
    (hw : w ∈ zeroOneSobolevSections A μ p k) :
    SobolevSection.tangentHomMapL A h hΦ μ p k w ∈
      zeroOneSobolevSections (A.ofBaseSet h) μ p k := by
  obtain ⟨θ, hθ⟩ := SobolevSection.exists_ae_eq_coord w
  have h01 := (mem_zeroOneSobolevSections_iff_isZeroOneForm hθ).1 hw
  refine (mem_zeroOneSobolevSections_iff_isZeroOneForm (A := A.ofBaseSet h) fun i ↦
    SobolevSection.chartValueL_tangentHomMapL_ae_coord hθ i).2 fun i ↦ ?_
  have himage : ((A.ofBaseSet h).tangentHom.sectionChartData.image i : Set ℂ) =
      A.tangentHom.sectionChartData.image i :=
    ((A.ofBaseSet h).sectionChartData_image_tangentHom i).trans
      ((congrArg SetLike.coe (image_ofBaseSet (A := A) (h := h) i)).trans
        (A.sectionChartData_image_tangentHom i).symm)
  rw [himage]
  filter_upwards [h01 i] with y hy
  exact hy.restrictScalars_comp _

include hΦ in
/-- The inverse of a complex linear smooth bundle isomorphism sends Sobolev `(0,1)`-forms to
`(0,1)`-forms. -/
private theorem tangentHomEquivL_symm_mem_zeroOneSobolevSections
    {w : SobolevSection (A.ofBaseSet h).tangentHom μ p k}
    (hw : w ∈ zeroOneSobolevSections (A.ofBaseSet h) μ p k) :
    (SobolevSection.tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ).symm w ∈
      zeroOneSobolevSections A μ p k := by
  obtain ⟨θ, hθ⟩ := SobolevSection.exists_ae_eq_coord w
  have h01 := (mem_zeroOneSobolevSections_iff_isZeroOneForm hθ).1 hw
  refine (mem_zeroOneSobolevSections_iff_isZeroOneForm (A := A) fun i ↦
    SobolevSection.chartValueL_tangentHomEquivL_symm_ae_coord hθ i).2 fun i ↦ ?_
  have himage : (A.tangentHom.sectionChartData.image i : Set ℂ) =
      (A.ofBaseSet h).tangentHom.sectionChartData.image i :=
    (A.sectionChartData_image_tangentHom i).trans
      ((congrArg SetLike.coe (image_ofBaseSet (A := A) (h := h) i)).symm.trans
        ((A.ofBaseSet h).sectionChartData_image_tangentHom i).symm)
  rw [himage]
  filter_upwards [h01 i] with y hy
  exact hy.restrictScalars_comp ((Φ (((A.ofBaseSet h).chart i).symm y)).symm : W _ →L[ℂ] V _)

/-- `TauCeti.SobolevSection.tangentHomEquivL` for `realEquiv Φ` is
`TauCeti.SobolevSection.tangentHomMapL` for the realification of `Φ`. -/
private theorem coe_tangentHomEquivL_realEquiv :
    (SobolevSection.tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ :
      SobolevSection A.tangentHom μ p k →L[ℝ] SobolevSection (A.ofBaseSet h).tangentHom μ p k) =
      SobolevSection.tangentHomMapL A h hΦ μ p k :=
  -- `realEquiv Φ x` coerces to the realification of `Φ x`.
  SobolevSection.coe_tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ

/-- **Bundle isomorphisms act on Sobolev `(0,1)`-forms.** The isomorphism of Banach spaces
`W^{k,p}(Λ^{0,1} ⊗ V) ≃ W^{k,p}(Λ^{0,1} ⊗ W)` induced by a smooth complex bundle isomorphism `Φ`,
sending a `(0,1)`-form `θ` to `Φ ∘ θ`. It is the restriction of
`TauCeti.SobolevSection.tangentHomEquivL`. -/
def zeroOneTransportEquivL :
    zeroOneSobolevSections A μ p k ≃L[ℝ] zeroOneSobolevSections (A.ofBaseSet h) μ p k :=
  .ofContinuousLinearMap
    (((SobolevSection.tangentHomMapL A h hΦ μ p k).comp
      (zeroOneSobolevSections A μ p k).subtypeL).codRestrict _ fun w ↦
        tangentHomMapL_mem_zeroOneSobolevSections hΦ A h μ p k w.property)
    ((((SobolevSection.tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ).symm :
        SobolevSection (A.ofBaseSet h).tangentHom μ p k →L[ℝ]
          SobolevSection A.tangentHom μ p k).comp
      (zeroOneSobolevSections (A.ofBaseSet h) μ p k).subtypeL).codRestrict _ fun w ↦
        tangentHomEquivL_symm_mem_zeroOneSobolevSections hΦ A h μ p k w.property)
    (ContinuousLinearMap.ext fun w ↦ Subtype.ext <| by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_codRestrict_apply,
        Submodule.subtypeL_apply, ContinuousLinearMap.id_apply, ← coe_tangentHomEquivL_realEquiv,
        ContinuousLinearEquiv.coe_coe]
      exact (SobolevSection.tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ).apply_symm_apply _)
    (ContinuousLinearMap.ext fun w ↦ Subtype.ext <| by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ← coe_tangentHomEquivL_realEquiv]
      exact (SobolevSection.tangentHomEquivL A h μ p k (Φ := realEquiv Φ) hΦ).symm_apply_apply _)

/-- The underlying one-form of the image of a `(0,1)`-form under `zeroOneTransportEquivL`. -/
@[simp]
theorem coe_zeroOneTransportEquivL_apply (w : zeroOneSobolevSections A μ p k) :
    (zeroOneTransportEquivL hΦ A h μ p k w : SobolevSection (A.ofBaseSet h).tangentHom μ p k) =
      SobolevSection.tangentHomMapL A h hΦ μ p k w :=
  (rfl)

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
    (zeroOneTransportEquivL hΦ A h μ p 0 :
        zeroOneSobolevSections A μ p 0 →L[ℝ] zeroOneSobolevSections (A.ofBaseSet h) μ p 0).comp
      (hD.sobolevL A hDs μ p) =
    ((hD.transport fun _ _ ↦ mdifferentiableAt_symm_apply_of_contMDiff hΦ (by simp)).sobolevL
      (A.ofBaseSet h) (contMDiffCovariantDerivativeOn_sectionTransport (hΦ.of_le (by simp)) hDs)
        μ p).comp
      (SobolevSection.bundleMapL A h hΦ μ p 1) := by
  refine ContinuousLinearMap.ext fun w ↦
    (SobolevSection.denseRange_ofContMDiffSection A μ p 1 hp).induction_on w
      (isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _))
      fun s ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    SobolevSection.bundleMapL_ofContMDiffSection]
  -- Both sides are the `(0,1)`-form `Φ ∘ D s`.
  have hDs' : sectionTransport Φ D (fun x ↦ (Φ x : V x →L[ℂ] W x).restrictScalars ℝ (s x)) =
      fun x ↦ ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (D s x) := by
    funext x
    rw [sectionTransport_apply]
    congr 2
    funext y
    exact (Φ y).symm_apply_apply (s y)
  refine Subtype.ext (SobolevSection.eq_of_ae_eq_coord
    (s := fun x ↦ ((Φ x : V x →L[ℂ] W x).restrictScalars ℝ).comp (D s x))
    (fun (i : Fin A.n) ↦ ?_) fun (i : Fin A.n) ↦ ?_)
  · rw [ContinuousLinearEquiv.coe_coe, coe_zeroOneTransportEquivL_apply]
    refine SobolevSection.chartValueL_tangentHomMapL_ae_coord (fun (i : Fin A.n) ↦ ?_) i
    rw [image_tangentHom]
    exact chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs μ p s i
  · have key := chartValueL_sobolevL_ofContMDiffSection_ae (A.ofBaseSet h)
      (hD.transport fun _ _ ↦ mdifferentiableAt_symm_apply_of_contMDiff hΦ (by simp))
      (contMDiffCovariantDerivativeOn_sectionTransport (hΦ.of_le (by simp)) hDs) μ p
      ⟨fun x ↦ (Φ x : V x →L[ℂ] W x).restrictScalars ℝ (s x),
        ContMDiff.clm_bundle_apply (hΦ.of_le (by exact_mod_cast le_top)) s.contMDiff⟩ i
    have hμ : μ.restrict ((A.ofBaseSet h).image i : Set ℂ) =
        μ.restrict ((A.ofBaseSet h).tangentHom.image i : Set ℂ) :=
      congrArg (fun U : TopologicalSpace.Opens ℂ ↦ μ.restrict (U : Set ℂ))
        ((A.ofBaseSet h).image_tangentHom i).symm
    rw [hμ] at key
    exact key.trans
      (Filter.EventuallyEq.of_eq (congrArg ((A.ofBaseSet h).tangentHom.coord i) hDs'))

omit [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- **The transport of a smooth real Cauchy–Riemann operator is Fredholm.** On a closed surface,
the realization `W^{1,p} → L^p` of the transport of `D` along a smooth bundle isomorphism is
Fredholm, `1 < p < ∞`. -/
theorem isFredholm_sobolevL_sectionTransport (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ((hD.transport fun _ _ ↦ mdifferentiableAt_symm_apply_of_contMDiff hΦ (by simp)).sobolevL
      (A.ofBaseSet h) (contMDiffCovariantDerivativeOn_sectionTransport (hΦ.of_le (by simp)) hDs)
        volume p).IsFredholm :=
  isFredholm_sobolevL (A.ofBaseSet h) _ _ hp hp_top

/-- **The index is invariant under bundle isomorphisms** (McDuff–Salamon, proof of Theorem C.1.10,
step 1). On a closed surface, the realizations `W^{1,p} → L^p` of a smooth real Cauchy–Riemann
operator `D` on `V` and of its transport `σ ↦ Φ ∘ D (Φ⁻¹ σ)` along a smooth bundle isomorphism
`Φ : V ≃ W` have the same index, for every finite `p ≥ 1` (they are Fredholm for `p > 1`). -/
theorem index_sobolevL_sectionTransport (hp_top : p ≠ ⊤) :
    ((hD.transport fun _ _ ↦ mdifferentiableAt_symm_apply_of_contMDiff hΦ (by simp)).sobolevL
      (A.ofBaseSet h) (contMDiffCovariantDerivativeOn_sectionTransport (hΦ.of_le (by simp)) hDs)
        μ p).index = (hD.sobolevL A hDs μ p).index := by
  set e₁ := SobolevSection.bundleEquivL A h μ p 1 (Φ := realEquiv Φ) hΦ
  -- `realEquiv Φ` is `Φ` with the real structure, so `e₁` is `bundleMapL` for the realification.
  have he : (e₁ : SobolevSection A μ p 1 →L[ℝ] SobolevSection (A.ofBaseSet h) μ p 1) =
      SobolevSection.bundleMapL A h hΦ μ p 1 :=
    SobolevSection.coe_bundleEquivL A h μ p 1 (Φ := realEquiv Φ) hΦ
  have hc := zeroOneTransportEquivL_comp_sobolevL hΦ A h μ p hD hDs hp_top
  have hS : (hD.transport fun _ _ ↦ mdifferentiableAt_symm_apply_of_contMDiff hΦ (by simp)).sobolevL
      (A.ofBaseSet h) (contMDiffCovariantDerivativeOn_sectionTransport (hΦ.of_le (by simp)) hDs)
        μ p =
        ((zeroOneTransportEquivL hΦ A h μ p 0 : zeroOneSobolevSections A μ p 0 →L[ℝ]
          zeroOneSobolevSections (A.ofBaseSet h) μ p 0).comp
            (hD.sobolevL A hDs μ p)).comp (e₁.symm : SobolevSection (A.ofBaseSet h) μ p 1
              →L[ℝ] SobolevSection A μ p 1) := by
    rw [hc, ← he]
    ext w : 1
    simp
  rw [hS, ContinuousLinearMap.index_comp_equiv, ContinuousLinearMap.index_equiv_comp]

end IsRealCauchyRiemannOperator

end TauCeti
