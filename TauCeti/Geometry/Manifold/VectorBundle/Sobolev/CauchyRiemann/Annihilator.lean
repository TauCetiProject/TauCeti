/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ChartSection
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Localization
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Annihilators of the range of a smooth real Cauchy–Riemann operator

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and
`D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` its realization
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`), for `1 < p < ∞`. The cokernel of `D` is
described by the continuous functionals `Λ` on the `Lᵖ` `(0,1)`-forms that vanish on the range of
`D`.

Every continuous functional `Λ` on the `Lᵖ` `(0,1)`-forms is, over every open `Q` with closure in
the image of chart `i`, integration against an `L^q` covector field `θ`, `q` the conjugate
exponent: `Λ w = ∫_Q θ (wᵢ(1))` for every `w` vanishing off the points of `Q`, where `wᵢ` is the
chart-`i` reading of `w` (`TauCeti.exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff`). A
`(0,1)`-form is complex antilinear, so it is determined by its value on `1`, and `θ` pairs with
that value. If `Λ` vanishes on the range of `D`, then `θ` is a weak solution of the adjoint
equation: `∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test function `φ` on `Q`, where `Zᵢ` is the
zeroth-order term of `D` in chart `i`
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`).
This is the hypothesis of the planar regularity theorem for annihilators of real Cauchy–Riemann
operators (`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`, for `J = i`
and `S = 2 Zᵢ(·)(1)`), which puts `θ` in `W^{k+1,r}_loc(Q)` for every `k` and every finite
`r`.

The proof extends `Λ` by Hahn–Banach to all chart data of one-forms
(`TauCeti.exists_extension_zeroOneSobolevSections`). Over `Q`, that extension is integration of the
chart-`i` components against `L^q` coefficients
(`TauCeti.SobolevSection.exists_memLp_forall_apply_eq_sum_setIntegral`, for any finite bundle
atlas), and the coefficients are assembled into `θ` through the complex antilinear map with a given
value on `1` (`ContinuousLinearMap.antilinearOfOneL`). A test function `φ` on `Q` is the reading
of a smooth section `ξ` (`TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`), and
`Λ (D ξ) = 0` is the weak equation.

The representing field is bounded by `Λ`: over `Q'` with closure in `Q`, the `L^q(Q')` norm of `θ`
is at most `C ‖Λ‖`, for a constant `C` independent of `Λ`
(`TauCeti.exists_eLpNorm_le_of_forall_eq_setIntegral`). For `v : F` and `g ∈ Lᵖ(Q')`, the
`(0,1)`-form with chart-`i` reading `g • (w ↦ conj w • v)`, extended by zero from chart `i`
(`TauCeti.zeroOneExtendByZeroL`), pairs with `Λ` to `∫_{Q'} g θ(·) v`. So the `L^q(Q')` norm of
`θ(·) v` is at most the norm of that extension times `‖Λ‖`, by the duality of `L^q` and `Lᵖ`.

## Main results

* `TauCeti.exists_extension_zeroOneSobolevSections`: functionals on `Lᵖ` `(0,1)`-forms extend to
  all chart data of one-forms.
* `TauCeti.exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff`: a continuous functional on the
  `Lᵖ` `(0,1)`-forms is, over a relatively compact open set of a chart image, integration against
  an `L^q` covector field.
* `TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`: for an annihilator of the range
  of `D`, that covector field is a weak solution of the adjoint equation.
* `TauCeti.exists_eLpNorm_le_of_forall_eq_setIntegral`: on a smaller set, the `L^q` norm of that
  covector field is at most a constant times the norm of the functional.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.2.3 (the cokernel step).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace Complex
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold Distributions Topology

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

section Annihilator

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannAnnihilator : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- **Extending functionals on Sobolev `(0,1)`-forms.** A continuous functional on the `Lᵖ`
`(0,1)`-forms extends, by Hahn–Banach, to the space of all chart data of `V`-valued one-forms. -/
theorem exists_extension_zeroOneSobolevSections
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) :
    ∃ Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ,
      ∀ w : zeroOneSobolevSections A volume p 0,
        Λ' ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0) = Λ w := by
  obtain ⟨g₁, hg₁, -⟩ := exists_extension_norm_eq (zeroOneSobolevSections A volume p 0) Λ
  obtain ⟨g₂, hg₂, -⟩ := exists_extension_norm_eq
    (A.tangentHom.sectionChartData.sobolevSections volume p 0) g₁
  exact ⟨g₂, fun w ↦ (hg₂ _).trans (hg₁ w)⟩

variable {q : ℝ≥0∞} [hq₁ : Fact (1 ≤ q)] [hpq : p.HolderConjugate q]

include hq₁ hpq in
/-- **Local representation of functionals on `(0,1)`-forms.** Let `1 < p < ∞`, `q` the conjugate
exponent, and `Λ` a continuous functional on the `Lᵖ` `(0,1)`-forms. For every open `Q` with
closure in the image of chart `i`, there is an `L^q` covector field `θ` on `Q` with
`Λ w = ∫_Q θ (wᵢ(1))` for every `(0,1)`-form `w` vanishing almost everywhere off the points of `M`
read in chart `i` inside `Q`, where `wᵢ` is the chart-`i` reading of `w`. -/
theorem exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (i : Fin A.n) {Q : Opens ℂ}
    (hQi : closure (Q : Set ℂ) ⊆ A.image i) :
    ∃ θ : ℂ → F →L[ℝ] ℝ, MemLp θ q (volume.restrict Q) ∧
      ∀ w : zeroOneSobolevSections A volume p 0,
        (w : SobolevSection A.tangentHom volume p 0) ∈
            SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
          Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
            ((w : SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) z 1) := by
  obtain ⟨Λ', hΛ'⟩ := exists_extension_zeroOneSobolevSections A Λ
  have hQi' : closure (Q : Set ℂ) ⊆ A.tangentHom.image i := by rwa [A.image_tangentHom]
  have hQs : (Q : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
    rw [sectionChartData_image_tangentHom]
    exact fun y hy ↦ hQi (subset_closure hy)
  -- `Λ` over `Q` is integration of the chart-`i` components against `H`.
  obtain ⟨H, hH, hHΛ⟩ := SobolevSection.exists_memLp_forall_apply_eq_sum_setIntegral (q := q)
    A.tangentHom hp hp_top Λ' i hQi'
  -- The coefficient field, assembled by a fixed continuous linear map: the `c`-th component of
  -- the complex antilinear map with value `v` on `1`, weighted by `H c`.
  let T : EuclideanSpace ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F))) →L[ℝ] F →L[ℝ] ℝ :=
    ∑ c, (EuclideanSpace.proj (𝕜 := ℝ) c).smulRight
      ((LinearMap.toContinuousLinearMap ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp
        (ContinuousLinearMap.antilinearOfOneL F))
  refine ⟨fun z ↦ T (H z), hH.continuousLinearMap_comp T, fun w hw ↦ ?_⟩
  rw [← hΛ', hHΛ _ hw]
  refine (integral_finsetSum _ fun c _ ↦
    (hH.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) c)).integrable_mul
      ((Lp.memLp _).mono_measure (Measure.restrict_mono hQs le_rfl))).symm.trans
    (integral_congr_ae ?_)
  -- Almost everywhere on `Q`, the chart-`i` data of `w` are complex antilinear, with components
  -- the values of its chart-`i` entries.
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hQs
      (mem_zeroOneSobolevSections_iff.1 w.prop i),
    ae_restrict_of_ae_restrict_of_subset hQs
      (A.tangentHom.sectionChartData.chartValueL_apply_ae volume p 0 i
        ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0))] with z hza hzs
  simp only [T, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul, PiLp.proj_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.antilinearOfOneL_apply_eq_of_antilinear _ hza,
    LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hzs]
  simp [Finsupp.single_apply]

variable {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

include hD hDs in
/-- The chart data of the realization of a smooth section `ξ` are, in chart `j`, the reading of
`D ξ`. -/
private theorem chartValueL_sobolevL_ae (ξ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) (j : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL volume p 0 j
      ((hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ) :
        SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0)
      =ᵐ[volume.restrict (A.tangentHom.sectionChartData.image j)]
        A.tangentHom.coord j (D ξ) :=
  (ae_image_tangentHom_iff A volume j).2
    (IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p ξ j)

include hD in
omit [T2Space M] in
/-- On the image of chart `i`, the reading of `D ξ` for a section `ξ` read as `φ` in chart `i` is
`∂bar φ + Zᵢ φ`. -/
private theorem coord_tangentHom_eq_of_eqOn {i : Fin A.n} {ξ : Π x, V x}
    (hξ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% ξ)) {φ : ℂ → F}
    (hξi : EqOn (A.coord i ξ) φ (A.image i)) {z : ℂ} (hz : z ∈ A.image i) :
    A.tangentHom.coord i (D ξ) z =
      complexAntilinearPartL (fderiv ℝ φ z) + A.chartZeroOrder D i z (φ z) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have hev : A.coord i ξ =ᶠ[𝓝 z] φ :=
    Filter.eventuallyEq_of_mem ((A.image i).isOpen.mem_nhds hz) hξi
  refine (A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
    ((hξ _).mdifferentiableAt (by simp))).trans ?_
  rw [hev.fderiv_eq, hξi hz]

include hD hDs hq₁ hpq in
/-- **Annihilators of the range are weak solutions of the adjoint equation, in a chart.** Let
`1 < p < ∞`, `q` the conjugate exponent, and `Λ` a continuous functional on the `Lᵖ` `(0,1)`-forms
vanishing on the range of the realization `W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of a smooth real
Cauchy–Riemann operator `D`. Let `Q` be open with closure in the image of chart `i`. Then the
`L^q` covector field `θ` on `Q` representing `Λ` over `Q`, `Λ w = ∫_Q θ (wᵢ(1))` for every
`(0,1)`-form `w` vanishing off the points read in chart `i` inside `Q`, satisfies
`∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test function `φ` on `Q`, where `Zᵢ` is the zeroth-order
term of `D` in chart `i`. -/
theorem exists_memLp_forall_integral_eq_zero_of_annihilator (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) (i : Fin A.n) {Q : Opens ℂ}
    (hQi : closure (Q : Set ℂ) ⊆ A.image i) :
    ∃ θ : ℂ → F →L[ℝ] ℝ, MemLp θ q (volume.restrict Q) ∧
      (∀ w : zeroOneSobolevSections A volume p 0,
        (w : SobolevSection A.tangentHom volume p 0) ∈
            SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
          Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
            ((w : SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) z 1)) ∧
      ∀ φ : 𝓓(Q, F), ∫ z, θ z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
        A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0 := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  obtain ⟨θ, hθ, hrep⟩ :=
    exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff (q := q) A hp hp_top Λ i hQi
  refine ⟨θ, hθ, hrep, fun φ ↦ ?_⟩
  -- The smooth section read as `φ` in chart `i`.
  have hQimg : (Q : Set ℂ) ⊆ A.image i := fun y hy ↦ hQi (subset_closure hy)
  have hQs : (Q : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
    rw [sectionChartData_image_tangentHom]
    exact hQimg
  obtain ⟨ξ, hξ, hξi, hξK⟩ := A.exists_contMDiff_eqOn_coord (i := i) φ.contDiff
    φ.hasCompactSupport (φ.tsupport_subset.trans hQimg)
  let ξ₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨ξ, hξ.of_le (by simp)⟩
  -- `D ξ` vanishes off the points of `Q`, so `Λ (D ξ)` is the integral of `θ` against its reading.
  have hmem : (hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ₁) :
      SobolevSection A.tangentHom volume p 0) ∈
        SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) :=
    SobolevSection.mem_aeZeroOff_of_ae_eq_coord (fun j ↦ chartValueL_sobolevL_ae A hD hDs ξ₁ j)
      fun x hx ↦ hD.apply_eq_zero_of_notMem_closure fun h ↦
        hx (image_mono φ.tsupport_subset (hξK h))
  have hw0 := hΛ (SobolevSection.ofContMDiffSection A volume p 1 ξ₁)
  rw [hrep _ hmem] at hw0
  -- Off `Q` the test function and its derivative vanish.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Q : Set ℂ)) fun z hz ↦ by
    have hzφ : z ∉ tsupport (φ : ℂ → F) := fun h ↦ hz (φ.tsupport_subset h)
    simp [fderiv_of_notMem_tsupport ℝ hzφ, image_eq_zero_of_notMem_tsupport hzφ]]
  -- On `Q`, the reading of `D ξ` in chart `i` is `∂bar φ + Zᵢ φ`.
  refine Eq.trans (integral_congr_ae ?_) hw0
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hQs
      (chartValueL_sobolevL_ae A (p := p) hD hDs ξ₁ i),
    ae_restrict_mem Q.isOpen.measurableSet] with z hz hzQ
  rw [hz, coord_tangentHom_eq_of_eqOn A hD (ξ := ξ₁) hξ hξi (hQimg hzQ)]

/-! ### The `L^q` bound of the representing field -/

section Bound

variable {i : Fin A.n} {Q' : Opens ℂ}

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- A subset of the image of chart `i` of `A` lies in the image of chart `i` of the atlas
`A.tangentHom` of `V`-valued one-forms: the two chart images agree. -/
private theorem subset_image_tangentHom {s : Set ℂ} (h : s ⊆ A.image i) :
    s ⊆ A.tangentHom.image i := by
  rwa [A.image_tangentHom]

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- A subset of the image of chart `i` of `A` lies in the image of chart `i` of the section chart
data of `V`-valued one-forms. -/
private theorem subset_sectionChartData_image_tangentHom {s : Set ℂ} (h : s ⊆ A.image i) :
    s ⊆ A.tangentHom.sectionChartData.image i := by
  rwa [sectionChartData_image_tangentHom]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Chart-`i` data of one-forms built from `g ∈ Lᵖ(Q')` and `v : F`: the components, in
`Module.finBasis ℝ (ℂ →L[ℝ] F)`, of `g₀ • antilinearOfOneL v`, where `g₀` is `g` extended by zero to
the chart image. -/
private def antilinearChartDataL (hQ' : (Q' : Set ℂ) ⊆ A.tangentHom.image i) (v : F) :
    Lp ℝ p (volume.restrict (Q' : Set ℂ)) →L[ℝ]
      (Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp volume (A.tangentHom.image i) p 0) :=
  -- `Wkp _ _ p 0` is `Lᵖ` by definition (`Wkp.value_zero` is `rfl`).
  ContinuousLinearMap.pi fun c ↦
    (finBasis ℝ (ℂ →L[ℝ] F)).repr (ContinuousLinearMap.antilinearOfOneL F v) c •
      (extendByZeroLpₗᵢ ℝ volume Q'.isOpen.measurableSet.nullMeasurableSet
        hQ').toContinuousLinearMap

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The components of `antilinearChartDataL` are the coefficients times the extension of `g` by
zero, almost everywhere on the chart image. -/
private theorem value_antilinearChartDataL_ae (hQ' : (Q' : Set ℂ) ⊆ A.tangentHom.image i) (v : F)
    (g : Lp ℝ p (volume.restrict (Q' : Set ℂ))) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    (Wkp.value 0 (antilinearChartDataL A hQ' v g c) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.tangentHom.image i : Set ℂ)] fun y ↦
        (finBasis ℝ (ℂ →L[ℝ] F)).repr (ContinuousLinearMap.antilinearOfOneL F v) c *
          extendByZeroLpₗᵢ ℝ volume Q'.isOpen.measurableSet.nullMeasurableSet hQ' g y := by
  rw [Wkp.value_zero]
  exact Lp.coeFn_smul _ _

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The data `antilinearChartDataL` vanish off the points read in chart `i` inside `closure Q'`. -/
private theorem antilinearChartDataL_mem (hQ' : (Q' : Set ℂ) ⊆ A.tangentHom.image i) (v : F)
    (g : Lp ℝ p (volume.restrict (Q' : Set ℂ))) :
    antilinearChartDataL A hQ' v g ∈ SobolevSection.chartAeZeroOff A.tangentHom volume p 0 i
      ((A.tangentHom.chart i).symm '' closure (Q' : Set ℂ)) :=
  SobolevSection.mem_chartAeZeroOff.2 fun c ↦ by
    filter_upwards [value_antilinearChartDataL_ae A hQ' v g c, ae_extendByZeroLpₗᵢ_eq_zero_of_notMem
      ℝ Q'.isOpen.measurableSet.nullMeasurableSet hQ' g] with y h₁ h₂ hL
    rw [h₁, h₂ fun hy ↦ hL ⟨y, subset_closure hy, rfl⟩, mul_zero]

/-- The `(0,1)`-forms built from `g ∈ Lᵖ(Q')` and `v : F`: the extension by zero of
`antilinearChartDataL`, a `(0,1)`-form vanishing off the points read in chart `i` inside
`closure Q'` whose chart-`i` reading is `g₀ • antilinearOfOneL v`. -/
private def antilinearExtL (hQ' : closure (Q' : Set ℂ) ⊆ A.tangentHom.image i) (v : F) :
    Lp ℝ p (volume.restrict (Q' : Set ℂ)) →L[ℝ] zeroOneSobolevSections A volume p 0 :=
  zeroOneExtendByZeroL (SobolevSection.hasExtensionByZero_of_le_one zero_le_one)
    (((A.tangentHom.isCompact_closure_image i).of_isClosed_subset isClosed_closure
      (hQ'.trans subset_closure)).image_of_continuousOn
        ((A.tangentHom.continuousOn_chart_symm i).mono hQ')).isClosed
    (by rintro _ ⟨z, hz, rfl⟩; exact A.tangentHom.symm_mem_dom (hQ' hz)) |>.comp
    ((antilinearChartDataL A (subset_closure.trans hQ') v).codRestrict _
      (antilinearChartDataL_mem A (subset_closure.trans hQ') v))

/-- On the chart image, the chart-`i` reading of `antilinearExtL v g`, evaluated on `1`, is
`g₀ • v`, where `g₀` is `g` extended by zero. -/
private theorem chartValueL_antilinearExtL_ae (hQ' : closure (Q' : Set ℂ) ⊆ A.tangentHom.image i)
    (v : F) (g : Lp ℝ p (volume.restrict (Q' : Set ℂ))) :
    ∀ᵐ y ∂volume.restrict (A.tangentHom.sectionChartData.image i : Set ℂ),
      A.tangentHom.sectionChartData.chartValueL volume p 0 i
        ((antilinearExtL A hQ' v g : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0) y 1 =
        extendByZeroLpₗᵢ ℝ volume Q'.isOpen.measurableSet.nullMeasurableSet
          (subset_closure.trans hQ') g y • v := by
  unfold antilinearExtL
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [chartValueL_zeroOneExtendByZeroL_ae (μ := volume) (p := p) (k := 0) _ _ _
      ((antilinearChartDataL A (subset_closure.trans hQ') v).codRestrict _
        (antilinearChartDataL_mem A (subset_closure.trans hQ') v) g),
    ae_all_iff.2 (value_antilinearChartDataL_ae A (subset_closure.trans hQ') v g)] with y h₁ h₂
  -- `h₁` is stated with the local real structure of the extension file, which is the same
  -- `VectorBundle.restrictScalars ℝ ℂ F V` as here, so it is used through `trans`.
  refine (congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h₁).trans ?_
  simp only [ContinuousLinearMap.coe_codRestrict_apply, h₂]
  -- The data are `g₀ y • antilinearOfOneL v`, which is complex antilinear.
  have hsum : ∑ c, ((finBasis ℝ (ℂ →L[ℝ] F)).repr (ContinuousLinearMap.antilinearOfOneL F v) c *
      extendByZeroLpₗᵢ ℝ volume Q'.isOpen.measurableSet.nullMeasurableSet
        (subset_closure.trans hQ') g y) • finBasis ℝ (ℂ →L[ℝ] F) c =
      extendByZeroLpₗᵢ ℝ volume Q'.isOpen.measurableSet.nullMeasurableSet
        (subset_closure.trans hQ') g y • ContinuousLinearMap.antilinearOfOneL F v := by
    simp only [mul_comm _ (extendByZeroLpₗᵢ _ _ _ _ g y), mul_smul, ← Finset.smul_sum,
      (finBasis ℝ (ℂ →L[ℝ] F)).sum_repr]
  rw [hsum, map_smul, ContinuousLinearMap.complexAntilinearPartL_eq_self_iff.2
    (ContinuousLinearMap.antilinearOfOneL_apply_I_smul v), smul_apply,
    ContinuousLinearMap.antilinearOfOneL_apply_apply_one]

/-- **Pairing with `antilinearExtL`.** If `Λ` is represented over `Q` by `θ`, then on
`antilinearExtL v g` it is the pairing of `g` with `θ(·) v` over `Q'`. -/
private theorem apply_antilinearExtL_eq {Q : Opens ℂ} (hQi : (Q : Set ℂ) ⊆ A.image i)
    (hQ' : closure (Q' : Set ℂ) ⊆ Q)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) {θ : ℂ → F →L[ℝ] ℝ}
    (hrep : ∀ w : zeroOneSobolevSections A volume p 0,
      (w : SobolevSection A.tangentHom volume p 0) ∈
          SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
        Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
          ((w : SobolevSection A.tangentHom volume p 0) :
            A.tangentHom.sectionChartData.SobolevData volume p 0) z 1))
    (v : F) (g : Lp ℝ p (volume.restrict (Q' : Set ℂ))) :
    Λ (antilinearExtL A (subset_image_tangentHom A (hQ'.trans hQi)) v g) =
      ∫ z in Q', g z * θ z v := by
  have hQ'' := subset_image_tangentHom A (hQ'.trans hQi)
  -- `antilinearExtL v g` vanishes off the points read in chart `i` inside `closure Q' ⊆ Q`. The
  -- charts of `A.tangentHom` are those of `A` by definition.
  have hmem : (antilinearExtL A hQ'' v g : SobolevSection A.tangentHom volume p 0) ∈
      SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) :=
    SobolevSection.aeZeroOff_mono (image_mono hQ')
      (zeroOneExtendByZeroL_mem_aeZeroOff _ _ _ _)
  -- Over `Q`, the reading on `1` is `g₀ • v`, with `g₀` the extension of `g` by zero.
  rw [hrep _ hmem]
  refine Eq.trans ?_ ((setIntegral_indicator Q'.isOpen.measurableSet).trans
    (by rw [inter_eq_right.2 (subset_closure.trans hQ')]))
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (subset_sectionChartData_image_tangentHom A hQi) (chartValueL_antilinearExtL_ae A hQ'' v g),
    ae_restrict_of_ae_restrict_of_subset (subset_image_tangentHom A hQi) (coeFn_extendByZeroLpₗᵢ ℝ
      Q'.isOpen.measurableSet.nullMeasurableSet (subset_closure.trans hQ'') g)] with z h₁ h₂
  rw [h₁, map_smul, smul_eq_mul, h₂, Set.indicator_mul_left]

omit hq₁ in
include hpq in
/-- **The `L^q` bound of the representing field, in one direction.** For `v : F`, the `L^q(Q')`
norm of `θ(·) v` is at most `‖antilinearExtL v‖ ‖Λ‖`: by the duality of `L^q` and `Lᵖ`, it is
the norm of `g ↦ ∫_{Q'} g θ(·) v = Λ (antilinearExtL v g)`. -/
private theorem eLpNorm_apply_le {Q : Opens ℂ} (hQi : (Q : Set ℂ) ⊆ A.image i)
    (hQ' : closure (Q' : Set ℂ) ⊆ Q)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) {θ : ℂ → F →L[ℝ] ℝ}
    (hθ : MemLp θ q (volume.restrict Q'))
    (hrep : ∀ w : zeroOneSobolevSections A volume p 0,
      (w : SobolevSection A.tangentHom volume p 0) ∈
          SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
        Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
          ((w : SobolevSection A.tangentHom volume p 0) :
            A.tangentHom.sectionChartData.SobolevData volume p 0) z 1))
    (v : F) :
    (eLpNorm (fun z ↦ θ z v) q (volume.restrict Q')).toReal ≤
      ‖antilinearExtL (p := p) A (subset_image_tangentHom A (hQ'.trans hQi)) v‖ * ‖Λ‖ := by
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hQ'' := subset_image_tangentHom A (hQ'.trans hQi)
  have hθv : MemLp (fun z ↦ θ z v) q (volume.restrict (Q' : Set ℂ)) :=
    hθ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ v)
  rw [← Lp.norm_toLp _ hθv, ← (Lp.toDual ℝ (volume.restrict (Q' : Set ℂ)) q p).norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g ↦ ?_
  rw [Lp.toDual_apply]
  -- The pairing is `Λ (antilinearExtL v g)`.
  have hpair : ∫ z in Q', hθv.toLp _ z * g z = Λ (antilinearExtL A hQ'' v g) := by
    rw [apply_antilinearExtL_eq A hQi hQ' Λ hrep v g]
    refine integral_congr_ae ?_
    filter_upwards [hθv.coeFn_toLp] with z hz
    rw [hz, mul_comm]
  rw [hpair]
  calc ‖Λ (antilinearExtL A hQ'' v g)‖ ≤ ‖Λ‖ * ‖antilinearExtL A hQ'' v g‖ := Λ.le_opNorm _
    _ ≤ ‖Λ‖ * (‖antilinearExtL (p := p) A hQ'' v‖ * ‖g‖) :=
        mul_le_mul_of_nonneg_left ((antilinearExtL (p := p) A hQ'' v).le_opNorm g) (norm_nonneg _)
    _ = _ := by ring

omit hq₁ in
include hpq in
/-- **The `L^q` bound of the field representing a functional.** Let `Q` be an open subset of the
image of chart `i`, and `Q'` open with closure in `Q`. There is a constant `C` such that, whenever
`θ ∈ L^q(Q')` represents a continuous functional `Λ` on the `Lᵖ` `(0,1)`-forms over `Q`,
`Λ w = ∫_Q θ (wᵢ(1))` for every `(0,1)`-form `w` vanishing off the points read in chart `i` inside
`Q`, the `L^q(Q')` norm of `θ` is at most `C ‖Λ‖`. -/
theorem exists_eLpNorm_le_of_forall_eq_setIntegral (i : Fin A.n) {Q Q' : Opens ℂ}
    (hQi : (Q : Set ℂ) ⊆ A.image i) (hQ' : closure (Q' : Set ℂ) ⊆ Q) :
    ∃ C : ℝ, ∀ (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (θ : ℂ → F →L[ℝ] ℝ),
      MemLp θ q (volume.restrict Q') →
      (∀ w : zeroOneSobolevSections A volume p 0,
        (w : SobolevSection A.tangentHom volume p 0) ∈
            SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
          Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
            ((w : SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) z 1)) →
      (eLpNorm θ q (volume.restrict Q')).toReal ≤ C * ‖Λ‖ := by
  have hq₁ : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hQ'' := subset_image_tangentHom A (hQ'.trans hQi)
  let b := finBasis ℝ F
  -- `κ` is the dual basis of `b`, as continuous functionals.
  let κ : Module.Basis (Fin (finrank ℝ F)) ℝ (F →L[ℝ] ℝ) :=
    b.dualBasis.map LinearMap.toContinuousLinearMap
  refine ⟨∑ c, ‖κ c‖ * ‖antilinearExtL (p := p) A hQ'' (b c)‖, fun Λ θ hθ hrep ↦ ?_⟩
  -- The coordinates of `θ z` in `κ` are its values on `b`.
  have hcoord (c : Fin (finrank ℝ F)) (z : ℂ) : κ.coord c (θ z) = θ z (b c) := by
    simp [κ, Module.Basis.coord_apply, Module.Basis.map_repr, Module.Basis.dualBasis_repr]
  have hle : eLpNorm θ q (volume.restrict Q') ≤ ∑ c, ENNReal.ofReal ‖κ c‖ *
      eLpNorm (fun z ↦ θ z (b c)) q (volume.restrict Q') := by
    simpa only [hcoord, ofReal_norm] using
      κ.eLpNorm_le_sum_enorm_mul_eLpNorm_coord hθ.aestronglyMeasurable
  have hfin (c : Fin (finrank ℝ F)) :
      ENNReal.ofReal ‖κ c‖ * eLpNorm (fun z ↦ θ z (b c)) q (volume.restrict Q') ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hθ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ (b c))).eLpNorm_ne_top
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun c _ ↦ hfin c) hle).trans ?_
  rw [ENNReal.toReal_sum fun c _ ↦ hfin c, Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (eLpNorm_apply_le A hQi hQ' Λ hθ hrep (b c)) (norm_nonneg _)

end Bound

end Annihilator

end TauCeti
