/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Geometry.Manifold.Complex.Chart
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas

/-!
# One atlas of each suffices for weak pseudoholomorphic maps

The predicate `TauCeti.IsWeakPseudoholomorphicOn J ν p u s` tests the coordinate equation
`∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)` in every holomorphic chart `φ` of the Riemann surface `X` and
every smooth chart `ψ` of `M`. We show that it suffices to test the charts of any families covering
`s` and `u '' s`, in particular one atlas of each.

The structure `J_φψ` (`ContMDiffAlmostComplexStructureFamily.chartField`) and the term `η_φψ`
(`InhomogeneousTerm.chartTerm`) transform as the planar invariance theorems require.

* Under a change `ψ ↦ ψ'` of target chart, with transition `T = ψ' ∘ ψ⁻¹`, the derivative `dT`
  intertwines `J_φψ` with `J_φψ'` and carries `η_φψ` to `η_φψ'`. The equation then transfers by
  `TauCeti.IsWeakCauchyRiemannOn.contDiffOn_comp_of_intertwine`.
* Under a change `φ ↦ φ'` of holomorphic chart, with transition `σ = φ ∘ φ'⁻¹` and
  `σ'(z) = a + b i`, the coordinate vector `∂ₛ` of `φ'` is `a ∂ₛ + b ∂ₜ` in `φ`, and `∂ₜ = j ∂ₛ`.
  Since `ν` is complex antilinear, `η_φ'ψ(z, v) = a η_φψ(σ z, v) - b J_φψ(σ z, v) η_φψ(σ z, v)`,
  which is the term produced by `TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn`.

The two changes are glued by the locality of the planar equation,
`TauCeti.isWeakCauchyRiemannOn_iff_locally`.

## Main results

* `TauCeti.ContMDiffAlmostComplexStructure.chartPushforward_comp_fderiv_symm_trans`,
  `TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_comp_fderiv_symm_trans`,
  `TauCeti.InhomogeneousTerm.chartTerm_symm_trans`: change of target chart, pointwise.
* `TauCeti.InhomogeneousTerm.chartTerm_eq_of_symm_trans`: change of holomorphic chart, pointwise.
* `TauCeti.isWeakCauchyRiemannOn_chart_of_chart`: the coordinate equation in one pair of charts
  gives it in any other pair, on the overlap.
* `TauCeti.isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas`: **chart independence**, testing
  families of charts covering `s` and `u '' s`; `TauCeti.isWeakPseudoholomorphicOn_iff_atlas` and
  `TauCeti.isWeakPseudoholomorphicOn_iff_chartAt` for the atlases and the preferred charts, and the
  versions for `TauCeti.IsWeakPseudoholomorphic`.
* `TauCeti.isWeakPseudoholomorphicOn_complex_iff`: on `X = ℂ` with target a normed space, the
  identity charts decide the predicate, which is the planar equation `TauCeti.IsWeakCauchyRiemannOn`
  for `J(z, ·)` and `2ν(z, ·)(1)`, so the planar checks (`TauCeti.isWeakCauchyRiemannOn_id`,
  `TauCeti.not_isWeakCauchyRiemannOn_conj`) are checks of the predicate.
* `TauCeti.isWeakPseudoholomorphicOn_complex_iff_mulLeft_two_chart`: on `X = ℂ` the single chart
  `z ↦ 2 z` already decides the predicate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1 and 3.1.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology ComplexConjugate TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

/-! ### Change of target chart -/

section TargetChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ψ ψ' : OpenPartialHomeomorph M G} {y : M}

/-- **Chain rule for a transition of charts with values in a normed space.** At `ψ y`, the
derivative of the transition `ψ' ∘ ψ⁻¹` is the derivative of `ψ⁻¹` followed by that of `ψ'`. -/
theorem _root_.OpenPartialHomeomorph.fderiv_symm_trans_apply (hy : y ∈ ψ.source)
    (hψ' : MDifferentiableAt I 𝓘(ℝ, G) ψ' y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (w : G) :
    fderiv ℝ (ψ.symm.trans ψ') (ψ y) w = mvfderiv I ψ' y (mfderiv 𝓘(ℝ, G) I ψ.symm (ψ y) w) := by
  have hψ'' : MDifferentiableAt I 𝓘(ℝ, G) ψ' (ψ.symm (ψ y)) := by rwa [ψ.left_inv hy]
  have h := mfderiv_comp_apply (ψ y) hψ'' hψs w
  simp only [mfderiv_eq_fderiv] at h
  rw [← mvfderiv_apply_eq_mfderiv_apply] at h
  rw [OpenPartialHomeomorph.coe_trans]
  refine h.trans ?_
  -- `ψ.symm (ψ y)` is `y`.
  have key : ∀ y', y' = y → mvfderiv I ψ' y' (mfderiv 𝓘(ℝ, G) I ψ.symm (ψ y) w) =
      mvfderiv I ψ' y (mfderiv 𝓘(ℝ, G) I ψ.symm (ψ y) w) := by
    rintro _ rfl
    rfl
  exact key _ (ψ.left_inv hy)

variable [IsManifold I ∞ M] {n : ℕ∞}

/-- **A structure in two charts.** The derivative of the transition `ψ' ∘ ψ⁻¹` at `ψ y`
intertwines the structure read in `ψ` with the structure read in `ψ'`. -/
theorem ContMDiffAlmostComplexStructure.chartPushforward_comp_fderiv_symm_trans
    (J : ContMDiffAlmostComplexStructure I n M) (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (hψ' : MDifferentiableAt I 𝓘(ℝ, G) ψ' y)
    (hψ's : MDifferentiableAt 𝓘(ℝ, G) I ψ'.symm (ψ' y)) :
    (J.chartPushforward ψ' (ψ' y)).comp (fderiv ℝ (ψ.symm.trans ψ') (ψ y)) =
      (fderiv ℝ (ψ.symm.trans ψ') (ψ y)).comp (J.chartPushforward ψ (ψ y)) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ψ.fderiv_symm_trans_apply hy hψ' hψs, ψ.fderiv_symm_trans_apply hy hψ' hψs]
  -- Write `w` as the image under `dψ` of the tangent vector `v = dψ⁻¹ w` at `y`.
  set v : TangentSpace I y := mfderiv 𝓘(ℝ, G) I ψ.symm (ψ y) w
  have hw : w = mfderiv I 𝓘(ℝ, G) ψ y v := by
    have := ψ.mfderiv_apply_mfderiv_symm_apply (ψ.map_source hy) (by rwa [ψ.left_inv hy]) hψs w
    rw [ψ.left_inv hy] at this
    exact this.symm
  have hJ : mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J.chartPushforward ψ (ψ y) (mfderiv I 𝓘(ℝ, G) ψ y v) :=
    DFunLike.congr_fun (J.mfderiv_comp_toEndomorphism ψ hy hψ hψs) v
  have hJ' : mvfderiv I ψ' y (J y v) = J.chartPushforward ψ' (ψ' y) (mvfderiv I ψ' y v) :=
    DFunLike.congr_fun (J.mfderiv_comp_toEndomorphism ψ' hy' hψ' hψ's) v
  conv_rhs => rw [hw]
  rw [← hJ, ψ.mfderiv_symm_apply_mfderiv_apply hy hψ hψs, hJ']

/-- **A domain-dependent structure in two target charts.** For every domain chart `φ`, the
derivative of the transition `ψ' ∘ ψ⁻¹` at `ψ y` intertwines `J` read in `(φ, ψ)` with `J` read in
`(φ, ψ')`. -/
theorem ContMDiffAlmostComplexStructureFamily.chartField_comp_fderiv_symm_trans
    {EP HP P D : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace D]
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (φ : OpenPartialHomeomorph P D) (z : D)
    (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (hψ' : MDifferentiableAt I 𝓘(ℝ, G) ψ' y)
    (hψ's : MDifferentiableAt 𝓘(ℝ, G) I ψ'.symm (ψ' y)) :
    (J.chartField φ ψ' z (ψ' y)).comp (fderiv ℝ (ψ.symm.trans ψ') (ψ y)) =
      (fderiv ℝ (ψ.symm.trans ψ') (ψ y)).comp (J.chartField φ ψ z (ψ y)) := by
  rw [chartField_apply, chartField_apply]
  exact (J.freeze (φ.symm z)).chartPushforward_comp_fderiv_symm_trans hy hy' hψ hψs hψ' hψ's

end TargetChart

/-! ### Inhomogeneous terms in two charts -/

section Term

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [IsManifold IP ∞ P] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞}
  {j : ContMDiffAlmostComplexStructure IP n P}
  {J : ContMDiffAlmostComplexStructureFamily I M IP P n}
  {ψ ψ' : OpenPartialHomeomorph M G} {y : M}

namespace InhomogeneousTerm

/-- An inhomogeneous term read in charts, at the value `ψ y` of a point `y` of the chart source:
twice the value of `ν(φ⁻¹ z, y)` on `∂ₛ`, pushed forward by `dψ` at `y`. -/
theorem chartTerm_apply_of_mem_source (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ)
    (hy : y ∈ ψ.source) (z : ℂ) :
    ν.chartTerm φ ψ z (ψ y) = (2 : ℝ) • mvfderiv I ψ y
      (ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ))) := by
  -- `ψ.symm (ψ y)` is `y`.
  have key : ∀ y', y' = y → mvfderiv I ψ y'
      (ν.val.tangentHom (φ.symm z, y') (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ))) =
        mvfderiv I ψ y
          (ν.val.tangentHom (φ.symm z, y) (mfderiv 𝓘(ℝ, ℂ) IP φ.symm z (1 : ℂ))) := by
    rintro _ rfl
    rfl
  rw [chartTerm_apply, key _ (ψ.left_inv hy)]

/-- **An inhomogeneous term in two target charts.** The derivative of the transition `ψ' ∘ ψ⁻¹` at
`ψ y` carries the term read in `(φ, ψ)` to the term read in `(φ, ψ')`. -/
theorem chartTerm_symm_trans (ν : InhomogeneousTerm j J) (φ : OpenPartialHomeomorph P ℂ) (z : ℂ)
    (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y))
    (hψ' : MDifferentiableAt I 𝓘(ℝ, G) ψ' y) :
    ν.chartTerm φ ψ' z (ψ' y) =
      fderiv ℝ (ψ.symm.trans ψ') (ψ y) (ν.chartTerm φ ψ z (ψ y)) := by
  rw [chartTerm_apply_of_mem_source ν φ hy', chartTerm_apply_of_mem_source ν φ hy, map_smul,
    ψ.fderiv_symm_trans_apply hy hψ' hψs, mvfderiv_apply_eq_mfderiv_apply ψ,
    ψ.mfderiv_symm_apply_mfderiv_apply hy hψ hψs]

end InhomogeneousTerm

end Term

/-! ### Change of holomorphic chart -/

section DomainChart

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The coordinate vector `∂ₛ` of a holomorphic chart `φ'` at `z`, read in a second holomorphic
chart `φ` with transition `σ = φ ∘ φ'⁻¹`, is `σ'(z) = a + b i` applied in `φ`: the vector
`a ∂ₛ + b j ∂ₛ` at `σ z`. -/
private theorem mfderiv_symm_one_eq {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {z : ℂ} (hz : z ∈ (φ'.symm.trans φ).source) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ'.symm z (1 : ℂ) =
      (deriv (φ'.symm.trans φ) z).re • mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ) +
        (deriv (φ'.symm.trans φ) z).im •
          SmoothAlmostComplexStructure.ofComplexManifold ℂ X (φ.symm (φ'.symm.trans φ z))
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (φ'.symm.trans φ z) (1 : ℂ)) := by
  set σ := φ'.symm.trans φ
  have hσz : σ z ∈ φ.target := (σ.map_source hz).1
  -- Near `z`, the inverse of `φ'` is the inverse of `φ` after the transition.
  have heq : ⇑φ'.symm =ᶠ[𝓝 z] φ.symm ∘ σ := by
    filter_upwards [σ.open_source.mem_nhds hz] with w hw
    have hw' : φ'.symm w ∈ φ.source := by simpa [σ] using hw.2
    simp [σ, φ.left_inv hw']
  have hσd : DifferentiableAt ℂ σ z :=
    (differentiableOn_symm_trans hφ' hφ).differentiableAt (σ.open_source.mem_nhds hz)
  have hφs : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (σ z) :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ) hσz).mdifferentiableAt
      one_ne_zero
  have hσ1 : fderiv ℝ σ z 1 = deriv σ z := by
    rw [(hσd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hcomm := (isPseudoholomorphicAt_ofComplexManifold_iff.2
    (mdifferentiableAt_symm_of_mem_maximalAtlas hφ hσz)).mfderiv_apply_commute (1 : ℂ)
  rw [SmoothAlmostComplexStructure.ofComplexManifold_apply, smul_eq_mul, mul_one] at hcomm
  have h := (hφs.hasMFDerivAt.comp z
    (hσd.restrictScalars ℝ).mdifferentiableAt.hasMFDerivAt).congr_of_eventuallyEq heq
  rw [h.mfderiv]
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (σ z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) σ z (1 : ℂ)) = _
  rw [mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (σ z) (fderiv ℝ σ z (1 : ℂ)) = _
  rw [hσ1, ← hcomm]
  -- A real-linear map on `ℂ` is determined by its values on `1` and `i`.
  have key : ∀ (L : ℂ →L[ℝ] ℂ) (c : ℂ), L c = c.re • L 1 + c.im • L Complex.I := fun L c ↦ by
    calc L c = L (c.re • 1 + c.im • Complex.I) := by
          congr 1
          simp [Complex.real_smul, Complex.re_add_im]
      _ = _ := by rw [map_add, map_smul, map_smul]
  exact key (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (σ z)) (deriv σ z)

/-- **An inhomogeneous term in two holomorphic charts.** Let `φ` and `φ'` be holomorphic charts
with transition `σ = φ ∘ φ'⁻¹` and `σ'(z) = a + b i`. At the value `ψ y` of a point `y` of the
source of a chart `ψ` of `M`, differentiable at `y` with inverse differentiable at `ψ y`, the term
read in `(φ', ψ)` at `z` is `a η - b J_φψ η`, where `η` is the term read in `(φ, ψ)` at `σ z` and
`J_φψ` the structure read there. -/
theorem InhomogeneousTerm.chartTerm_eq_of_symm_trans
    (ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J)
    {φ φ' : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {z : ℂ} (hz : z ∈ (φ'.symm.trans φ).source)
    {ψ : OpenPartialHomeomorph M G} {y : M} (hy : y ∈ ψ.source)
    (hψ : MDifferentiableAt I 𝓘(ℝ, G) ψ y) (hψs : MDifferentiableAt 𝓘(ℝ, G) I ψ.symm (ψ y)) :
    ν.chartTerm φ' ψ z (ψ y) =
      (deriv (φ'.symm.trans φ) z).re • ν.chartTerm φ ψ (φ'.symm.trans φ z) (ψ y) -
        (deriv (φ'.symm.trans φ) z).im • J.chartField φ ψ (φ'.symm.trans φ z) (ψ y)
          (ν.chartTerm φ ψ (φ'.symm.trans φ z) (ψ y)) := by
  set σ := φ'.symm.trans φ
  have hx : φ'.symm z = φ.symm (σ z) := by
    have hz' : φ'.symm z ∈ φ.source := by simpa [σ] using hz.2
    simp [σ, φ.left_inv hz']
  set x := φ.symm (σ z)
  set m := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (σ z) (1 : ℂ)
  set a := ν.val.tangentHom (x, y) m
  have hJ : mvfderiv I ψ y (J.tangentEndomorphism (x, y) a) =
      (J.freeze x).chartPushforward ψ (ψ y) (mvfderiv I ψ y a) := by
    rw [← J.freeze_apply]
    exact DFunLike.congr_fun ((J.freeze x).mfderiv_comp_toEndomorphism ψ hy hψ hψs) a
  have hj := ν.tangentHom_apply_j (x, y) m
  simp only [SmoothAlmostComplexStructure.toContMDiff_apply] at hj
  rw [ν.chartTerm_apply_of_mem_source φ' hy, ν.chartTerm_apply_of_mem_source φ hy,
    mfderiv_symm_one_eq hφ hφ' hz, hx, map_add, map_smul, map_smul, hj, J.chartField_apply,
    map_smul, ← hJ]
  simp only [map_add, map_smul, map_neg, smul_add, smul_neg, smul_comm (2 : ℝ), sub_eq_add_neg]
  rfl

end DomainChart

/-! ### The coordinate equation in two pairs of charts -/

section ChartChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth chart of `M`, read in `E`, is differentiable at every point of its source. -/
private theorem mdifferentiableAt_extendTrans_refl {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) {y : M} (hy : y ∈ ψ.source) :
    MDifferentiableAt I 𝓘(ℝ, E) (ψ.extendTrans I (Homeomorph.refl E)) y :=
  (ψ.contMDiffAt_extendTrans hψ contDiff_id hy).mdifferentiableAt (by simp)

/-- The inverse of a smooth chart of `M`, read in `E`, is differentiable at the image of every
point of its source. -/
private theorem mdifferentiableAt_extendTrans_refl_symm {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) {y : M} (hy : y ∈ ψ.source) :
    MDifferentiableAt 𝓘(ℝ, E) I (ψ.extendTrans I (Homeomorph.refl E)).symm
      (ψ.extendTrans I (Homeomorph.refl E) y) :=
  (ψ.contMDiffAt_extendTrans_symm hψ contDiff_id
    ((ψ.extendTrans I _).map_source (by simpa using hy))).mdifferentiableAt (by simp)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  [CompleteSpace E] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- **Change of target chart.** On a set `U` of the target of a holomorphic chart `φ` over which
`u` maps into the sources of two smooth charts `ψ` and `ψ'`, the coordinate equation in `(φ, ψ)`
gives the coordinate equation in `(φ, ψ')`. -/
private theorem isWeakCauchyRiemannOn_chart_of_target {φ : OpenPartialHomeomorph X ℂ}
    {ψ ψ' : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I ∞ M) {U : Set ℂ}
    (hU : U ⊆ φ.target ∩ φ.symm ⁻¹' (u ⁻¹' (ψ.source ∩ ψ'.source)))
    (h : IsWeakCauchyRiemannOn p U (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm)) :
    IsWeakCauchyRiemannOn p U (J.chartField φ (ψ'.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ'.extendTrans I (Homeomorph.refl E)))
      (ψ'.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  set χ := ψ.extendTrans I (Homeomorph.refl E)
  set χ' := ψ'.extendTrans I (Homeomorph.refl E)
  set T := χ.symm.trans χ'
  have hT : ContDiffOn ℝ 1 T T.source :=
    (OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm I hψ hψ' contDiff_id contDiff_id).of_le
      (by exact_mod_cast le_top)
  -- At a point `z` of `U`, write `y = u (φ⁻¹ z)`.
  have hy : ∀ z ∈ U, u (φ.symm z) ∈ χ.source ∧ u (φ.symm z) ∈ χ'.source := fun z hz ↦ by
    simpa [χ, χ'] using (hU hz).2
  have hTy : ∀ z ∈ U, T (χ (u (φ.symm z))) = χ' (u (φ.symm z)) := fun z hz ↦ by
    simp [T, χ.left_inv (hy z hz).1]
  have hmaps : MapsTo (χ ∘ u ∘ φ.symm) U T.source := fun z hz ↦ by
    refine ⟨χ.map_source (hy z hz).1, ?_⟩
    simpa [χ.left_inv (hy z hz).1] using (hy z hz).2
  refine (h.contDiffOn_comp_of_intertwine T.open_source hT hmaps ?_ ?_).congr fun z hz ↦ hTy z hz
    <;> refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
    <;> obtain ⟨hyχ, hyχ'⟩ := hy z (interior_subset hz)
    <;> simp only [Function.comp_apply, hTy z (interior_subset hz)]
  · exact J.chartField_comp_fderiv_symm_trans φ z hyχ hyχ'
      (mdifferentiableAt_extendTrans_refl hψ (by simpa [χ] using hyχ))
      (mdifferentiableAt_extendTrans_refl_symm hψ (by simpa [χ] using hyχ))
      (mdifferentiableAt_extendTrans_refl hψ' (by simpa [χ'] using hyχ'))
      (mdifferentiableAt_extendTrans_refl_symm hψ' (by simpa [χ'] using hyχ'))
  · exact ν.chartTerm_symm_trans φ z hyχ hyχ'
      (mdifferentiableAt_extendTrans_refl hψ (by simpa [χ] using hyχ))
      (mdifferentiableAt_extendTrans_refl_symm hψ (by simpa [χ] using hyχ))
      (mdifferentiableAt_extendTrans_refl hψ' (by simpa [χ'] using hyχ'))

omit [CompleteSpace E] in
/-- **Change of holomorphic chart.** The coordinate equation in `(φ, ψ)` gives the coordinate
equation in `(φ', ψ)` on the part of the target of `φ'` over `s ∩ φ.source` where `u` maps into
the source of `ψ`. -/
private theorem isWeakCauchyRiemannOn_chart_of_domain {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    (h : IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm)) :
    IsWeakCauchyRiemannOn p (φ'.target ∩ φ'.symm ⁻¹' ((s ∩ φ.source) ∩ u ⁻¹' ψ.source))
      (J.chartField φ' (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ' (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ'.symm) := by
  set χ := ψ.extendTrans I (Homeomorph.refl E)
  set σ := φ'.symm.trans φ
  set W := φ'.target ∩ φ'.symm ⁻¹' ((s ∩ φ.source) ∩ u ⁻¹' ψ.source)
  have hWσ : W ⊆ σ.source := fun z hz ↦ by
    simpa [σ] using And.intro hz.1 hz.2.1.2
  -- The transition does not move the point of `X`.
  have hσs : ∀ z ∈ W, φ.symm (σ z) = φ'.symm z := fun z hz ↦ by
    simp [σ, φ.left_inv hz.2.1.2]
  have hyχ : ∀ z ∈ W, u (φ'.symm z) ∈ χ.source := fun z hz ↦ by simpa [χ] using hz.2.2
  have hmaps : MapsTo σ W (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := fun z hz ↦ by
    refine ⟨φ.map_source hz.2.1.2, ?_⟩
    rw [mem_preimage, hσs z hz]
    exact ⟨hz.2.1.1, hz.2.2⟩
  have hσ' : ∀ z ∈ W, deriv σ z ≠ 0 := fun z hz ↦ by
    have := deriv_symm_trans_ne_zero hφ' hφ (φ'.map_target hz.1) hz.2.1.2
    rwa [φ'.right_inv hz.1] at this
  have hJ : ∀ z ∈ interior W, J.chartField φ χ (σ z) ((χ ∘ u ∘ φ.symm) (σ z)) *
      J.chartField φ χ (σ z) ((χ ∘ u ∘ φ.symm) (σ z)) = -1 := fun z hz ↦ by
    have hzW := interior_subset hz
    refine ContinuousLinearMap.ext fun w ↦ ?_
    change J.chartField φ χ (σ z) _ (J.chartField φ χ (σ z) _ w) = -w
    simp only [Function.comp_apply, hσs z hzW]
    rw [J.chartField_apply]
    exact (J.freeze _).chartPushforward_apply_chartPushforward_apply χ
      (χ.map_source (hyχ z hzW)) (by
        rw [χ.left_inv (hyχ z hzW)]
        exact mdifferentiableAt_extendTrans_refl hψ (by simpa [χ] using hyχ z hzW))
      (mdifferentiableAt_extendTrans_refl_symm hψ (by simpa [χ] using hyχ z hzW)) w
  have h1 := h.comp_differentiableOn σ.open_source
    (by simpa only [σ, OpenPartialHomeomorph.coe_trans] using differentiableOn_symm_trans hφ' hφ)
    hWσ (σ.injOn.mono hWσ) hσ' hmaps hJ
  refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 (h1.congr fun z hz ↦ ?_)
    <;> try refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
  · simp only [Function.comp_apply, J.chartField_apply, hσs z (interior_subset hz)]
  · have hzW := interior_subset hz
    have hyψ : u (φ'.symm z) ∈ ψ.source := by simpa [χ] using hyχ z hzW
    simp only [Function.comp_apply]
    rw [ν.chartTerm_eq_of_symm_trans hφ hφ' (hWσ hzW) (hyχ z hzW)
      (mdifferentiableAt_extendTrans_refl hψ hyψ) (mdifferentiableAt_extendTrans_refl_symm hψ hyψ)]
  · simp only [Function.comp_apply, hσs z hz]

/-- **Change of charts.** For holomorphic charts `φ`, `φ'` and smooth charts `ψ`, `ψ'`, the
coordinate equation in `(φ, ψ)` gives the coordinate equation in `(φ', ψ')` on the part of the
target of `φ'` over `s ∩ φ.source` where `u` maps into the sources of both `ψ` and `ψ'`. -/
theorem isWeakCauchyRiemannOn_chart_of_chart {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ ψ' : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I ∞ M)
    (h : IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm)) :
    IsWeakCauchyRiemannOn p
      (φ'.target ∩ φ'.symm ⁻¹' ((s ∩ φ.source) ∩ u ⁻¹' (ψ.source ∩ ψ'.source)))
      (J.chartField φ' (ψ'.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ' (ψ'.extendTrans I (Homeomorph.refl E)))
      (ψ'.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ'.symm) :=
  isWeakCauchyRiemannOn_chart_of_target hψ hψ' (fun _ hz ↦ ⟨hz.1, hz.2.2⟩)
    ((isWeakCauchyRiemannOn_chart_of_domain hφ hφ' hψ h).mono fun _ hz ↦
      ⟨hz.1, hz.2.1, hz.2.2.1⟩)

end ChartChange

/-! ### Chart independence -/

section ChartIndependence

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {p : ENNReal} {u : X → M} {s : Set X}

/-- **Chart independence of weak pseudoholomorphic maps.** It suffices to test the coordinate
equation in the charts of a family `A` of holomorphic charts covering `s` and a family `B` of
smooth charts of `M` covering `u '' s`, together with continuity of `u` on `s`. -/
theorem isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  rw [isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn]
  refine ⟨fun ⟨hc, h⟩ ↦ ⟨hc, fun φ hφ ψ hψ ↦ h φ (hA hφ) ψ (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ ⟨hc, fun φ' hφ' ψ' hψ' ↦ isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_⟩⟩
  -- Near `z`, change from charts of `A` and `B` at `φ'⁻¹ z` and `u (φ'⁻¹ z)`.
  obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  refine ⟨_, ?_, isWeakCauchyRiemannOn_chart_of_chart (hA hφA) hφ' (hB hψB) hψ'
    (h φ hφA ψ hψB)⟩
  have hcφ : ContinuousWithinAt φ'.symm (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source)) z :=
    (φ'.continuousOn_symm z hz.1).mono inter_subset_left
  have hcu := (hc _ hz.2.1).comp hcφ fun w hw ↦ hw.2.1
  filter_upwards [self_mem_nhdsWithin, hcφ.preimage_mem_nhdsWithin
    (φ.open_source.mem_nhds hxφ), hcu.preimage_mem_nhdsWithin (ψ.open_source.mem_nhds hxψ)]
    with w hw hw₁ hw₂
  exact ⟨hw.1, ⟨hw.2.1, hw₁⟩, hw₂, hw.2.2⟩

/-- **Chart independence on the whole surface.** It suffices to test the coordinate equation in
the charts of a family `A` of holomorphic charts covering `X` and a family `B` of smooth charts
covering the image of `u`, together with continuity of `u`. -/
theorem isWeakPseudoholomorphic_iff_of_subset_maximalAtlas
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  rw [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas hA
    (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

/-- **One atlas of each suffices.** A map is weakly pseudoholomorphic on `s` exactly when it is
continuous on `s` and solves the coordinate equation in the charts of the atlases of `X` and
`M`. -/
theorem isWeakPseudoholomorphicOn_iff_atlas :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- **One atlas of each suffices on the whole surface.** A map is weakly pseudoholomorphic exactly
when it is continuous and solves the coordinate equation in the charts of the atlases of `X` and
`M`. -/
theorem isWeakPseudoholomorphic_iff_atlas :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  isWeakPseudoholomorphic_iff_of_subset_maximalAtlas IsManifold.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- **The preferred charts suffice.** A map is weakly pseudoholomorphic on `s` exactly when it is
continuous on `s` and solves the coordinate equation in the preferred charts of `X` and `M`. -/
theorem isWeakPseudoholomorphicOn_iff_chartAt :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ (x : X) (y : M),
      IsWeakCauchyRiemannOn p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        ((chartAt H y).extendTrans I (Homeomorph.refl E) ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range]

/-- **The preferred charts suffice on the whole surface.** A map is weakly pseudoholomorphic
exactly when it is continuous and solves the coordinate equation in the preferred charts of `X`
and `M`. -/
theorem isWeakPseudoholomorphic_iff_chartAt :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ (x : X) (y : M),
      IsWeakCauchyRiemannOn p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        ((chartAt H y).extendTrans I (Homeomorph.refl E) ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_iff_chartAt]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Checks on the plane -/

section Plane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F 𝓘(ℝ, ℂ) ℂ ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) J}
  {p : ENNReal} {u : ℂ → F} {s : Set ℂ}

/-- **The identity charts decide the predicate on the plane.** For maps from `ℂ` to a normed
space `F`, the predicate is the planar weak equation `∂ₛu + J(z, u) ∂ₜu = 2ν(z, u)(1)` on `s`. -/
theorem isWeakPseudoholomorphicOn_complex_iff :
    IsWeakPseudoholomorphicOn J ν p u s ↔ IsWeakCauchyRiemannOn p s
      (fun z v ↦ (J.freeze z).toEndomorphism v)
      (fun z v ↦ (2 : ℝ) • (ν.val.tangentHom (z, v) (1 : ℂ) : F)) u := by
  have hD : (OpenPartialHomeomorph.refl ℂ).target ∩ (OpenPartialHomeomorph.refl ℂ).symm ⁻¹'
      (s ∩ u ⁻¹' (OpenPartialHomeomorph.refl F).source) = s := by
    simp
  rw [isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas
    (singleton_subset_iff.2 (StructureGroupoid.id_mem_maximalAtlas _))
    (fun x _ ↦ ⟨_, rfl, mem_univ x⟩)
    (singleton_subset_iff.2 (StructureGroupoid.id_mem_maximalAtlas _))
    (fun x _ ↦ ⟨_, rfl, mem_univ (u x)⟩)]
  simp only [mem_singleton_iff, forall_eq,
    OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl]
  rw [hD]
  -- In the identity chart of `ℂ`, the coordinate vector `∂ₛ` is `1`.
  have hη : (fun z v ↦ (2 : ℝ) • (ν.val.tangentHom (OpenPartialHomeomorph.refl ℂ z, v)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OpenPartialHomeomorph.refl ℂ) z (1 : ℂ)) : F)) =
        fun z v ↦ (2 : ℝ) • (ν.val.tangentHom (z, v) (1 : ℂ) : F) := by
    funext z v
    rw [OpenPartialHomeomorph.refl_apply, mfderiv_id]
    rfl
  simp only [ContMDiffAlmostComplexStructureFamily.chartField_refl,
    InhomogeneousTerm.chartTerm_refl, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, Function.id_comp, Function.comp_id, id_eq]
  exact ⟨fun h ↦ hη ▸ h.2, fun h ↦ ⟨h.continuousOn, hη ▸ h⟩⟩

/-- **The chart `z ↦ 2 z` alone decides the predicate on the plane.** For maps from `ℂ` into any
manifold `M`, it suffices to test the coordinate equation in the single holomorphic chart
`z ↦ 2 z` and the charts of the atlas of `M`. -/
theorem isWeakPseudoholomorphicOn_complex_iff_mulLeft_two_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) ℂ ℓ}
    {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) J}
    {u : ℂ → M} :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ ψ ∈ atlas H M,
      IsWeakCauchyRiemannOn p
        ((Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.target ∩
          (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.symm ⁻¹'
            (s ∩ u ⁻¹' ψ.source))
        (J.chartField (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph
          (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph
          (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘
          (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.symm) := by
  rw [isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas
    (singleton_subset_iff.2 mulLeft_two_chart_mem_maximalAtlas) (fun x _ ↦ ⟨_, rfl, mem_univ x⟩)
    IsManifold.subset_maximalAtlas fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩]
  simp only [mem_singleton_iff, forall_eq]

end Plane

end TauCeti
