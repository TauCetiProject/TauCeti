/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Green
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Annihilator
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.PartitionOfUnity
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOne.Gram
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChartHaar
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.SemiFredholm
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.ExtendByZero
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Cokernel

/-!
# Duality for smooth real Cauchy–Riemann operators on closed surfaces

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact), smooth metrics on `TM` and `V`, and the Riemannian volume `dV`. Let `D` be a
smooth real Cauchy–Riemann operator on `V`, realized as
`D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` (`TauCeti.IsRealCauchyRiemannOperator.sobolevL`),
`1 < p < ∞`, and `D*` its formal adjoint on smooth `(0,1)`-forms, for compatible metrics and a
smooth metric connection.

* *Annihilators of the range.* Every continuous functional `Λ` on the `Lᵖ` `(0,1)`-forms that
  vanishes on the range of `D` is the `L²` pairing `w ↦ ∫ ⟪η, w⟫ dV`
  (`TauCeti.zeroOneHilbertSchmidtL`) with a smooth `(0,1)`-form `η` satisfying `D* η = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.exists_zeroOneHilbertSchmidtL_eq_of_annihilator`).
  Conversely, by Green's formula, such pairings vanish on the range of `D`
  (`TauCeti.IsRealCauchyRiemannOperator.annihilator_iff_exists_zeroOneHilbertSchmidtL_eq`).
* *The duality (C.1.3).* A `(0,1)`-form is in the range of `D` exactly when it is
  `L²`-orthogonal to every smooth `(0,1)`-form `η` with `D* η = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.mem_range_sobolevL_iff`): the range is closed, so it is
  cut out by the functionals vanishing on it.
* *The cokernel.* The pairing identifies the smooth `(0,1)`-forms `η` with `D* η = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjoint`) with the annihilator of the range, the
  kernel of the transpose of `D`
  (`TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivKerPrecomp`): it is onto by the first
  item, and one-to-one because `∫ ⟪η, η⟫ dV = 0` forces `η = 0`. So `dim coker D = dim ker D*`
  and `index D = dim ker D - dim ker D*`. Since no nonzero `η` with `D* η = 0` is in the range of
  `D`, sending `η` to its class is a linear equivalence `ker D* ≃ coker D`
  (`TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivQuotientRange`).

## The argument

Take a smooth partition of unity `χᵢ` subordinate to the charts and open sets `Q₀ ⋐ Q₁` of the
chart images with the support of `χᵢ` read in chart `i` inside `Q₀`
(`TauCeti.FiniteBundleAtlas.exists_nested_chart_sets`). Over `Q₁`, `Λ` is integration
`w ↦ ∫ θ (wᵢ(1)) dz` against a covector field `θ` that solves the adjoint equation weakly
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`), so `θ` is smooth
(`TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`). In
chart `i` the Riemannian volume is `ρ dz` for the smooth positive chart density `ρ`
(`TauCeti.chartHaarDensity`), and inverting the chart Gram form of the metrics
(`TauCeti.FiniteBundleAtlas.exists_contDiffOn_hilbertSchmidtInner_eq`) gives a smooth
`(0,1)`-form `ηᵢ` over `Q₁` with `ρ ⟪ηᵢ, w⟫ = θ (wᵢ(1))`. Then `η = ∑ χᵢ ηᵢ` is smooth and
represents `Λ = ∑ Λ (χᵢ ·)`. Finally `∫ ⟪D* η, ξ⟫ dV = ∫ ⟪η, D ξ⟫ dV = Λ (D ξ) = 0` for every
smooth section `ξ`, so `D* η = 0`
(`TauCeti.IsRealCauchyRiemannOperator.eq_formalAdjoint_of_forall_integral_inner_eq`).

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointToZeroOne`: a smooth solution of `D* η = 0`
  as an `Lᵖ` `(0,1)`-form (`TauCeti.IsRealCauchyRiemannOperator.coe_kerFormalAdjointToZeroOne`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_zeroOneHilbertSchmidtL_eq_of_annihilator`: an
  annihilator of the range is the `L²` pairing with a smooth solution of `D* η = 0`.
* `TauCeti.IsRealCauchyRiemannOperator.annihilator_iff_exists_zeroOneHilbertSchmidtL_eq`: the
  annihilators of the range are exactly these pairings.
* `TauCeti.IsRealCauchyRiemannOperator.mem_range_sobolevL_iff`: McDuff–Salamon's duality (C.1.3).
* `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivKerPrecomp`: the kernel of `D*` is the
  kernel of the transpose of `D`.
* `TauCeti.IsRealCauchyRiemannOperator.finrank_quotient_range_sobolevL_eq_finrank_kerFormalAdjoint`,
  `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_finrank_sub`:
  `dim coker D = dim ker D*` and `index D = dim ker D - dim ker D*`.
* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_kerFormalAdjoint`: `ker D*` is
  finite-dimensional.
* `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivQuotientRange`: `ker D* ≃ coker D`,
  sending `η` to its class.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, the duality (C.1.3), and Theorem C.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (antilinearOfOneL complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold RealInnerProductSpace

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannDuality : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  (A : FiniteBundleAtlas ℂ M F V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance instIsContinuousRiemannianBundleDuality : IsContinuousRiemannianBundle F V :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, ℂ)) (n := ∞)

local instance instIsContinuousRiemannianBundleTangentDuality :
    IsContinuousRiemannianBundle ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, ℂ)) (n := ∞)

/-! ### Representing an annihilator in one chart -/

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x] in
/-- **The chart piece, pointwise.** If `R` represents `ρ⁻¹ g` through the Hilbert–Schmidt inner
product in chart `i` on `Q`, `ρ` the chart density of the Riemannian volume against Lebesgue
measure, then the one-form `η` reading as the antilinear maps with values `R z` at `1` satisfies
`ρ z ⟪η, t⟫ = g z (tᵢ(z)(1))` at the point read at `z ∈ Q`, for every one-form `t` read as a
complex antilinear map there. -/
private theorem chartHaarDensity_mul_hilbertSchmidtInner_chartSection {i : Fin A.n} {Q : Set ℂ}
    (hQ : Q ⊆ A.image i) {g : ℂ → F →L[ℝ] ℝ} {R : ℂ → F}
    (hRg : ∀ z ∈ Q, ∀ a : ℂ →L[ℝ] F, (∀ w, a (Complex.I • w) = -(Complex.I • a w)) →
      ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z)
        (antilinearOfOneL F (R z))).hilbertSchmidtInner
          ((A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z) a) =
            ((chartHaarDensity volume (A.center i) z)⁻¹ • g z) (a 1))
    {z : ℂ} (hz : z ∈ Q) (t : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (ht : ∀ w, A.tangentHom.coord i t z (Complex.I • w) =
      -(Complex.I • A.tangentHom.coord i t z w)) :
    chartHaarDensity volume (A.center i) z *
        (A.tangentHom.chartSection i (fun z ↦ antilinearOfOneL F (R z))
          ((A.chart i).symm z)).hilbertSchmidtInner (t ((A.chart i).symm z)) =
      g z (A.tangentHom.coord i t z 1) := by
  have himage := A.tangentHom.image_subset_target_inter_preimage_baseSet i
  simp only [image_tangentHom, chart_tangentHom] at himage
  have hb := (himage (hQ hz)).2
  have hco (u : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) :
      (A.tangentHom.triv i).symmL ℝ ((A.chart i).symm z) (A.tangentHom.coord i u z) =
        u ((A.chart i).symm z) := by
    have h := A.tangentHom.symmL_coord (i := i) (y := z) (by rw [chart_tangentHom]; exact hb) u
    rwa [chart_tangentHom] at h
  have hη : A.tangentHom.coord i (A.tangentHom.chartSection i
      (fun z ↦ antilinearOfOneL F (R z))) z = antilinearOfOneL F (R z) :=
    coord_chartSection _ (by rw [image_tangentHom]; exact hQ hz)
  rw [← hco (A.tangentHom.chartSection i _), ← hco t, hη, hRg z hz _ ht, smul_apply, smul_eq_mul,
    mul_inv_cancel_left₀ (chartHaarDensity_pos volume (himage (hQ hz)).1).ne']

omit [T2Space M] in
/-- **One chart of the representing form.** Let `Q₀ ⊆ Q₁` be open subsets of the image of chart
`i`, `χ` a smooth function with support read in chart `i` inside `Q₀`, and `Λ` a functional on the
`Lᵖ` `(0,1)`-forms represented over `Q₁` by `θ`, `Λ w = ∫_{Q₁} θ (wᵢ(1))`, with `θ` almost
everywhere equal on `Q₁` to a field `g` smooth on `Q₁`. Then there is a smooth `(0,1)`-form `ζ`
with `Λ (χ w) = ∫ ⟪ζ, w⟫ dV` for every `(0,1)`-form `w`, for the Riemannian volume `dV`. -/
private theorem exists_zeroOneForm_chart {i : Fin A.n} {Q₀ Q₁ : Opens ℂ}
    (hQ₀₁ : Q₀ ≤ Q₁) (hQ₁ : (Q₁ : Set ℂ) ⊆ A.image i)
    {χ : M → ℝ} (hχs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχ : tsupport χ ⊆ (A.chart i).symm '' Q₀)
    {Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ} {θ : ℂ → F →L[ℝ] ℝ}
    (hrep : ∀ w : zeroOneSobolevSections A volume p 0,
      (w : SobolevSection A.tangentHom volume p 0) ∈
          SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q₁) →
        Λ w = ∫ z in Q₁, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
          ((w : SobolevSection A.tangentHom volume p 0) :
            A.tangentHom.sectionChartData.SobolevData volume p 0) z 1))
    {g : ℂ → F →L[ℝ] ℝ} (hg : ContDiffOn ℝ ∞ g Q₁) (hθg : θ =ᵐ[volume.restrict Q₁] g) :
    ∃ ζ : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ (fun x ↦
        TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (ζ x)) ∧
      (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (ζ x)) ∧
      ∀ (w : zeroOneSobolevSections A volume p 0)
        (s : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x),
        (∀ j, A.tangentHom.sectionChartData.chartValueL volume p 0 j
          ((w : SobolevSection A.tangentHom volume p 0) :
            A.tangentHom.sectionChartData.SobolevData volume p 0)
              =ᵐ[volume.restrict (A.image j)] A.tangentHom.coord j s) →
        Λ (zeroOnePartSobolevL A volume p 0
            (SobolevSection.contMDiffSMulL A.tangentHom volume p 0 hχs w)) =
          ∫ x, (ζ x).hilbertSchmidtInner (s x) ∂riemannianVolume 𝓘(ℝ, ℂ) M := by
  have himage := A.tangentHom.image_subset_target_inter_preimage_baseSet i
  simp only [image_tangentHom, chart_tangentHom] at himage
  -- The values at `1` of the representing form, in chart `i`: `g / ρ` through the Gram form.
  have hρ (z : ℂ) (hz : z ∈ Q₁) : chartHaarDensity volume (A.center i) z ≠ 0 :=
    (chartHaarDensity_pos volume (himage (hQ₁ hz)).1).ne'
  obtain ⟨R, hR, hRg⟩ := A.exists_contDiffOn_hilbertSchmidtInner_eq i (hQ₁.trans himage)
    (g := fun z ↦ (chartHaarDensity volume (A.center i) z)⁻¹ • g z)
    ((((contDiffOn_chartHaarDensity volume (A.center i)).mono
      fun z hz ↦ (himage (hQ₁ hz)).1).inv hρ).smul hg)
  set η := A.tangentHom.chartSection i (fun z ↦ antilinearOfOneL F (R z))
  refine ⟨fun x ↦ χ x • η x, ?_, fun x ↦ ?_, fun w s hs ↦ ?_⟩
  · refine contMDiff_smul_chartSection hχs Q₁.isOpen (hχ.trans ?_)
      ((antilinearOfOneL F).contDiff.comp_contDiffOn hR)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨A.symm_mem_dom (hQ₁ (hQ₀₁ hz)), by
      simpa [(A.chart i).right_inv (himage (hQ₁ (hQ₀₁ hz))).1] using hQ₀₁ hz⟩
  · exact A.isZeroOneForm_smul_chartSection
      (fun _ _ ↦ ContinuousLinearMap.antilinearOfOneL_apply_I_smul _) (χ x) x
  · -- `w` vanishes off the points read in chart `i` inside `Q₁`, where `Λ` is represented by `θ`.
    have hmem := SobolevSection.aeZeroOff_mono (hχ.trans (image_mono hQ₀₁))
      (zeroOnePartSobolevL_mem_aeZeroOff (SobolevSection.contMDiffSMulL_mem_aeZeroOff hχs
        (w : SobolevSection A.tangentHom volume p 0)))
    have hQ₁s : (Q₁ : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
      rwa [sectionChartData_image_tangentHom]
    rw [hrep _ hmem, integral_riemannianVolume_eq_setIntegral_chartHaarDensity volume
      (α := A.center i) Q₁.isOpen (fun z hz ↦ (himage (hQ₁ hz)).1) fun x hx ↦ by
      beta_reduce
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (image_mono hQ₀₁ (hχ h)), zero_smul,
        ContinuousLinearMap.hilbertSchmidtInner_zero_left]]
    refine integral_congr_ae ?_
    filter_upwards [hθg, ae_restrict_of_ae_restrict_of_subset hQ₁s
        (chartValueL_zeroOnePartSobolevL_ae
          (SobolevSection.contMDiffSMulL A.tangentHom volume p 0 hχs
            (w : SobolevSection A.tangentHom volume p 0)) i),
      ae_restrict_of_ae_restrict_of_subset hQ₁s ((ae_image_tangentHom_iff A volume i).2
        ((A.image_tangentHom i).symm ▸ SobolevSection.chartValueL_contMDiffSMulL_ae hχs
          (w : SobolevSection A.tangentHom volume p 0) i)),
      ae_restrict_of_ae_restrict_of_subset hQ₁ (hs i),
      ae_restrict_of_ae_restrict_of_subset hQ₁s (mem_zeroOneSobolevSections_iff.1 w.prop i),
      ae_restrict_mem Q₁.isOpen.measurableSet] with z hθz h₁ h₂ h₃ hw hz
    simp only [chart_tangentHom, h₃] at h₂ hw
    rw [hθz, h₁, h₂, map_smul, ContinuousLinearMap.complexAntilinearPartL_eq_self_iff.2 hw,
      smul_apply, map_smul,
      ← chartHaarDensity_mul_hilbertSchmidtInner_chartSection A hQ₁ hRg hz s hw]
    simp only [smul_eq_mul, ContinuousLinearMap.hilbertSchmidtInner_smul_left]
    ring

/-! ### Annihilators of the range -/

namespace IsRealCauchyRiemannOperator

variable {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

include hD hDs in
/-- An annihilator of the range of `D` is the `L²` pairing with a smooth `(0,1)`-form. -/
private theorem exists_eq_zeroOneHilbertSchmidtL (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) :
    ∃ (η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
      (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
        TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x)),
      (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) ∧
        zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
          hη.continuous = Λ := by
  have hpq : p.HolderConjugate p.conjExponent := .conjExponent hp.le
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  have hq : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt (p := p) (q := p.conjExponent)).1 hp_top.lt_top
  obtain ⟨χ, Q₀, Q₁, Q₂, Q₃, hχ, hQ₀, hQ₁, hQ₂, hQ₃, -⟩ := A.exists_nested_chart_sets
  have hQ₁i (i : Fin A.n) : closure (Q₁ i : Set ℂ) ⊆ A.image i :=
    (hQ₁ i).2.trans (subset_closure.trans ((hQ₂ i).trans (subset_closure.trans (hQ₃ i))))
  -- In every chart, `Λ` is represented over `Q₁` by a smooth field, giving one piece `ζᵢ`.
  choose θ hθ hrep hweak using fun i ↦
    exists_memLp_forall_integral_eq_zero_of_annihilator (q := p.conjExponent) A hD hDs hp
      hp_top Λ hΛ i (hQ₁i i)
  choose g hg hθg using fun i ↦ exists_contDiffOn_ae_eq_of_forall_integral_eq_zero A hD hDs
    (subset_closure.trans (hQ₁i i)) hq (hθ i).memLpLoc (hweak i)
  choose ζ hζs hζ01 hζΛ using fun i ↦ exists_zeroOneForm_chart A
    (subset_closure.trans (hQ₀ i).2) (subset_closure.trans (hQ₁i i)) (χ i).contMDiff (hχ i)
    (hrep i) (hg i) (hθg i)
  have hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x
        (∑ i, ζ i x) :=
    ContMDiff.sum_section fun i _ ↦ hζs i
  refine ⟨fun x ↦ ∑ i, ζ i x, hη, fun x ↦ isZeroOneForm_iff.2 fun v ↦ ?_, ?_⟩
  · simp only [FunLike.coe_sum, Finset.sum_apply, isZeroOneForm_iff.1 (hζ01 _ x),
      Finset.sum_neg_distrib, Finset.smul_sum]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  obtain ⟨s, hs⟩ := SobolevSection.exists_ae_eq_coord (w : SobolevSection A.tangentHom volume p 0)
  have hs' (j : Fin A.n) : A.tangentHom.sectionChartData.chartValueL volume p 0 j
      ((w : SobolevSection A.tangentHom volume p 0) :
        A.tangentHom.sectionChartData.SobolevData volume p 0)
        =ᵐ[volume.restrict (A.image j)] A.tangentHom.coord j s :=
    A.image_tangentHom j ▸ hs j
  -- `w` is the sum of the `(0,1)`-projections of the `χᵢ w`, and `Λ (χᵢ w) = ∫ ⟪ζᵢ, w⟫ dV`.
  have h1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  have hint (i : Fin A.n) : Integrable (fun x ↦ (ζ i x).hilbertSchmidtInner (s x))
      (riemannianVolume 𝓘(ℝ, ℂ) M) := by
    simpa only [ContinuousLinearMap.hilbertSchmidtInnerL_apply] using
      SobolevSection.integrable_apply (A := A.tangentHom) isPositiveDensityMeasure_riemannianVolume
        (L := fun x ↦ (ζ i x).hilbertSchmidtInnerL)
        (fun x₀ ↦ Bundle.Trivialization.continuousOn_hilbertSchmidtInnerL_comp_symmL _
          (trivializationAt _ _ x₀).open_baseSet subset_rfl (hζs i).continuous.continuousOn) hs
  rw [zeroOneHilbertSchmidtL_apply _ _ hs',
    ← sum_zeroOnePartSobolevL_contMDiffSMulL_eq_self (fun i ↦ (χ i).contMDiff) h1 w, map_sum,
    Finset.sum_congr rfl fun i _ ↦ hζΛ i w s hs', ← integral_finsetSum _ fun i _ ↦ hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [ContinuousLinearMap.hilbertSchmidtInner_comm _ (s x),
    ← ContinuousLinearMap.hilbertSchmidtInnerL_apply, map_sum]

variable (cov : _root_.CovariantDerivative 𝓘(ℝ, ℂ) F V)
  [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] [∀ x, ContinuousSMul ℂ (V x)]

include hD hDs in
/-- **Annihilators of the range are pairings with solutions of the adjoint equation**
(McDuff–Salamon, (C.1.3) and the proof of Theorem C.2.3, on a closed surface). For compatible
metrics, a smooth metric connection, the Riemannian volume and `1 < p < ∞`, every continuous
functional `Λ` on the `Lᵖ` `(0,1)`-forms vanishing on the range of
`D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` is the `L²` pairing `w ↦ ∫ ⟪η, w⟫ dV`
(`TauCeti.zeroOneHilbertSchmidtL`) with a smooth `(0,1)`-form `η` satisfying `D* η = 0`. -/
theorem exists_zeroOneHilbertSchmidtL_eq_of_annihilator (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) :
    ∃ (η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
      (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
        TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x)),
      (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) ∧ (∀ x, hD.formalAdjoint cov η x = 0) ∧
        zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
          hη.continuous = Λ := by
  have := A.compactSpace
  obtain ⟨η, hη, hη01, rfl⟩ := exists_eq_zeroOneHilbertSchmidtL A hD hDs hp hp_top Λ hΛ
  refine ⟨η, hη, hη01, fun x ↦ ?_, rfl⟩
  -- `∫ ⟪0, ξ⟫ dV = 0 = Λ (D ξ) = ∫ ⟪η, D ξ⟫ dV` for smooth `ξ`, so `0 = D* η`.
  have h0 := hD.eq_formalAdjoint_of_forall_integral_inner_eq cov hcov hDs hJ hV hη hη01
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℂ)) (n := ∞) ℝ (E := V)) fun ξ hξ _ ↦ by
      let ξ₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨ξ, hξ.of_le (by simp)⟩
      have h := hΛ (SobolevSection.ofContMDiffSection A volume p 1 ξ₁)
      rw [zeroOneHilbertSchmidtL_apply _ _
        (chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p ξ₁)] at h
      simpa [ξ₁] using h.symm
  exact (congrFun h0 x).symm

include hD hDs in
/-- **The annihilator of the range of `D`.** For compatible metrics, a smooth metric connection,
the Riemannian volume and `1 < p < ∞`, a continuous functional on the `Lᵖ` `(0,1)`-forms vanishes on
the range of `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` exactly when it is the `L²` pairing
(`TauCeti.zeroOneHilbertSchmidtL`) with a smooth `(0,1)`-form `η` satisfying `D* η = 0`. -/
theorem annihilator_iff_exists_zeroOneHilbertSchmidtL_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) :
    (∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) ↔
      ∃ (η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
        (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
          TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x)),
        (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) ∧
          (∀ x, hD.formalAdjoint cov η x = 0) ∧
            zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
              hη.continuous = Λ := by
  refine ⟨exists_zeroOneHilbertSchmidtL_eq_of_annihilator A hD hDs cov hp hp_top hcov hJ hV Λ,
    ?_⟩
  rintro ⟨η, hη, hη01, hDη, rfl⟩ w
  exact range_sobolevL_le_ker_zeroOneHilbertSchmidtL hD hDs cov hp_top hcov hJ hV hη hη01 hDη
    ⟨w, rfl⟩

include hD hDs in
/-- **McDuff–Salamon's duality (C.1.3)** on a closed surface. For compatible metrics, a smooth
metric connection, the Riemannian volume and `1 < p < ∞`, an `Lᵖ` `(0,1)`-form `y` is in the range
of `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` exactly when it is `L²`-orthogonal,
`∫ ⟪η, y⟫ dV = 0`, to every smooth `(0,1)`-form `η` with `D* η = 0`. -/
theorem mem_range_sobolevL_iff (hp : 1 < p) (hp_top : p ≠ ⊤) (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (y : zeroOneSobolevSections A volume p 0) :
    y ∈ (hD.sobolevL A hDs volume p).range ↔
      ∀ (η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
        (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
          TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x)),
        (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) →
          (∀ x, hD.formalAdjoint cov η x = 0) →
            zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
              hη.continuous y = 0 := by
  refine ⟨fun hy η hη hη01 hDη ↦
    range_sobolevL_le_ker_zeroOneHilbertSchmidtL hD hDs cov hp_top hcov hJ hV hη hη01 hDη hy,
    fun h ↦ ?_⟩
  -- The range is closed, so it is cut out by the functionals vanishing on it.
  rw [← (isClosed_range_sobolevL A hD hDs hp hp_top).submodule_topologicalClosure_eq,
    Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero]
  intro Λ hΛ
  obtain ⟨η, hη, hη01, hDη, rfl⟩ := exists_zeroOneHilbertSchmidtL_eq_of_annihilator A hD hDs cov
    hp hp_top hcov hJ hV Λ fun w ↦ hΛ _ ⟨w, rfl⟩
  exact h η hη hη01 hDη

/-! ### The cokernel is the kernel of the formal adjoint -/

variable (p) in
/-- **Smooth solutions of `D* η = 0` as `Lᵖ` `(0,1)`-forms.** The linear map sending a smooth
`(0,1)`-form `η` with `D* η = 0` (`TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjoint`) to the
element of `Lᵖ(M, Λ^{0,1} ⊗ V)` it defines. -/
def kerFormalAdjointToZeroOne :
    hD.kerFormalAdjoint cov →ₗ[ℝ] zeroOneSobolevSections A volume p 0 :=
  ((SobolevSection.ofContMDiffSection A.tangentHom volume p 0).comp
    ({ toFun η := ⟨η, ((hD.mem_kerFormalAdjoint cov).1 η.property).1.of_le (by simp)⟩
       map_add' _ _ := ContMDiffSection.ext fun _ ↦ by simp
       map_smul' _ _ := ContMDiffSection.ext fun _ ↦ by simp } :
      hD.kerFormalAdjoint cov →ₗ[ℝ]
        Cₛ^(0 : ℕ)⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯)).codRestrict
    _ fun η ↦
    ofContMDiffSection_mem_zeroOneSobolevSections ((hD.mem_kerFormalAdjoint cov).1 η.property).2.1

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] in
/-- `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointToZeroOne` sends `η` to the Sobolev form of
the continuous section `η`. -/
@[simp]
theorem coe_kerFormalAdjointToZeroOne (η : hD.kerFormalAdjoint cov) :
    (hD.kerFormalAdjointToZeroOne A p cov η : SobolevSection A.tangentHom volume p 0) =
      SobolevSection.ofContMDiffSection A.tangentHom volume p 0
        ⟨η, ((hD.mem_kerFormalAdjoint cov).1 η.property).1.of_le (by simp)⟩ := by
  simp only [kerFormalAdjointToZeroOne, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

omit [T2Space M] [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] in
/-- The `L²` pairing of a continuous `(0,1)`-form `η` with the `Lᵖ` form of `η'` in the kernel of
`D*` is `∫ ⟪η, η'⟫ dV`. -/
theorem zeroOneHilbertSchmidtL_kerFormalAdjointToZeroOne
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (η' : hD.kerFormalAdjoint cov) :
    zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η hη
        (hD.kerFormalAdjointToZeroOne A p cov η') =
      ∫ x, (η x).hilbertSchmidtInner ((η' : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x)
        ∂riemannianVolume 𝓘(ℝ, ℂ) M := by
  have hσ := ofContMDiffSection_mem_zeroOneSobolevSections (A := A) (μ := volume) (p := p) (k := 0)
    (σ := ⟨η', ((hD.mem_kerFormalAdjoint cov).1 η'.property).1.of_le (by simp)⟩)
    ((hD.mem_kerFormalAdjoint cov).1 η'.property).2.1
  rw [show hD.kerFormalAdjointToZeroOne A p cov η' = ⟨_, hσ⟩ from
    Subtype.ext (coe_kerFormalAdjointToZeroOne A hD cov η'),
    zeroOneHilbertSchmidtL_ofContMDiffSection _ hη hσ, ContMDiffSection.coeFn_mk]

omit [T2Space M] [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] in
/-- A smooth solution of `D* η = 0` whose `L²` pairing with its own `Lᵖ` form vanishes is zero:
`∫ ⟪η, η⟫ dV = 0` for a continuous `η` and the Riemannian volume. -/
private theorem eq_zero_of_zeroOneHilbertSchmidtL_kerFormalAdjointToZeroOne
    (η : hD.kerFormalAdjoint cov)
    (h : zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
      ((hD.mem_kerFormalAdjoint cov).1 η.property).1.continuous
        (hD.kerFormalAdjointToZeroOne A p cov η) = 0) :
    η = 0 := by
  have := A.compactSpace
  have hη := ((hD.mem_kerFormalAdjoint cov).1 η.property).1
  rw [zeroOneHilbertSchmidtL_kerFormalAdjointToZeroOne] at h
  set f : M → ℝ := fun x ↦ ((η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x).hilbertSchmidtInner
    ((η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x)
  have hf : Continuous f := (hη.hilbertSchmidtInner_bundle hη).continuous
  have hf0 : 0 ≤ f := fun x ↦ ContinuousLinearMap.hilbertSchmidtInner_self_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg hf0
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))).1 h
  have hf_eq : f = 0 := (hf.ae_eq_iff_eq _ continuous_const).1 hae
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  exact (ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero_iff _).1 (congrFun hf_eq x)

variable (p) in
/-- The pairing of a smooth solution of `D* η = 0` with `Lᵖ` `(0,1)`-forms, as a linear map into the
continuous functionals. -/
private def kerFormalAdjointToDual :
    hD.kerFormalAdjoint cov →ₗ[ℝ] StrongDual ℝ (zeroOneSobolevSections A volume p 0) where
  toFun η := zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
    ((hD.mem_kerFormalAdjoint cov).1 η.property).1.continuous
  map_add' _ _ := zeroOneHilbertSchmidtL_add _ _ _ _
  map_smul' c _ := zeroOneHilbertSchmidtL_smul _ c _ _

omit [T2Space M] [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] in
private theorem kerFormalAdjointToDual_apply (η : hD.kerFormalAdjoint cov) :
    kerFormalAdjointToDual A p hD cov η =
      zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
        ((hD.mem_kerFormalAdjoint cov).1 η.property).1.continuous := by
  rw [kerFormalAdjointToDual, LinearMap.coe_mk, AddHom.coe_mk]

include hDs in
/-- No nonzero smooth solution of `D* η = 0` is in the range of `D`: its `L²` pairing with itself
would vanish by Green's formula. -/
private theorem injective_mkQ_comp_kerFormalAdjointToZeroOne (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    Function.Injective
      ((hD.sobolevL A hDs volume p).range.mkQ ∘ₗ hD.kerFormalAdjointToZeroOne A p cov) := by
  refine (injective_iff_map_eq_zero _).2 fun η h ↦ ?_
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨hη, hη01, hDη⟩ := (hD.mem_kerFormalAdjoint cov).1 η.property
  refine eq_zero_of_zeroOneHilbertSchmidtL_kerFormalAdjointToZeroOne A hD cov (p := p) η ?_
  exact LinearMap.mem_ker.1
    (range_sobolevL_le_ker_zeroOneHilbertSchmidtL hD hDs cov hp_top hcov hJ hV hη hη01 hDη h)

include hDs in
/-- The `L²` pairing with a smooth solution of `D* η = 0` vanishes on the range of `D`. -/
private theorem kerFormalAdjointToDual_mem_ker_precomp (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (η : hD.kerFormalAdjoint cov) :
    kerFormalAdjointToDual A p hD cov η ∈
      (ContinuousLinearMap.precomp ℝ (hD.sobolevL A hDs volume p) :
        StrongDual ℝ (zeroOneSobolevSections A volume p 0) →L[ℝ]
          StrongDual ℝ (SobolevSection A volume p 1)).ker := by
  obtain ⟨hη, hη01, hDη⟩ := (hD.mem_kerFormalAdjoint cov).1 η.property
  rw [ContinuousLinearMap.ker_precomp_eq_orthogonalBilin_range]
  refine Submodule.mem_orthogonalBilin.2 fun _ hy ↦ ?_
  rw [LinearMap.flip_apply, topDualPairing_apply, kerFormalAdjointToDual_apply]
  exact LinearMap.mem_ker.1 (range_sobolevL_le_ker_zeroOneHilbertSchmidtL hD hDs cov hp_top
    hcov hJ hV hη hη01 hDη hy)

include hD hDs in
/-- The `L²` pairing is a bijection from smooth solutions of `D* η = 0` onto the annihilator of the
range of `D`: one-to-one by `∫ ⟪η, η⟫ dV`, onto by
`TauCeti.IsRealCauchyRiemannOperator.exists_zeroOneHilbertSchmidtL_eq_of_annihilator`. -/
private theorem bijective_codRestrict_kerFormalAdjointToDual (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    Function.Bijective ((kerFormalAdjointToDual A p hD cov).codRestrict _
      (kerFormalAdjointToDual_mem_ker_precomp A hD hDs cov hp_top hcov hJ hV)) :=
  ⟨(injective_iff_map_eq_zero _).2 fun η h ↦ by
    have h' := congrArg Subtype.val h
    rw [LinearMap.codRestrict_apply, kerFormalAdjointToDual_apply, ZeroMemClass.coe_zero] at h'
    refine eq_zero_of_zeroOneHilbertSchmidtL_kerFormalAdjointToZeroOne A hD cov (p := p) η ?_
    rw [h', _root_.zero_apply],
    fun Λ ↦ by
      have hΛ (w : SobolevSection A volume p 1) :
          (Λ : StrongDual ℝ (zeroOneSobolevSections A volume p 0))
            (hD.sobolevL A hDs volume p w) = 0 := by
        have h := DFunLike.congr_fun (LinearMap.mem_ker.1 Λ.property) w
        rwa [ContinuousLinearMap.coe_coe, ContinuousLinearMap.precomp_apply,
          ContinuousLinearMap.comp_apply, _root_.zero_apply] at h
      obtain ⟨η, hη, hη01, hDη, hηΛ⟩ := exists_zeroOneHilbertSchmidtL_eq_of_annihilator A hD hDs
        cov hp hp_top hcov hJ hV _ hΛ
      refine ⟨⟨η, (hD.mem_kerFormalAdjoint cov).2 ⟨hη, hη01, hDη⟩⟩, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, kerFormalAdjointToDual_apply]
      exact hηΛ⟩

include hD hDs in
/-- **The kernel of `D*` is the kernel of the transpose of `D`** (McDuff–Salamon, (C.1.3) and the
proof of Theorem C.2.3, on a closed surface). For compatible metrics, a smooth metric connection,
the Riemannian volume and `1 < p < ∞`, the `L²` pairing `η ↦ (w ↦ ∫ ⟪η, w⟫ dV)` identifies the
smooth `(0,1)`-forms `η` with `D* η = 0` with the continuous functionals on the `Lᵖ` `(0,1)`-forms
vanishing on the range of `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`. -/
def kerFormalAdjointEquivKerPrecomp (hp : 1 < p) (hp_top : p ≠ ⊤) (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    hD.kerFormalAdjoint cov ≃ₗ[ℝ]
      (ContinuousLinearMap.precomp ℝ (hD.sobolevL A hDs volume p) :
        StrongDual ℝ (zeroOneSobolevSections A volume p 0) →L[ℝ]
          StrongDual ℝ (SobolevSection A volume p 1)).ker :=
  LinearEquiv.ofBijective
    ((kerFormalAdjointToDual A p hD cov).codRestrict _
      (kerFormalAdjointToDual_mem_ker_precomp A hD hDs cov hp_top hcov hJ hV))
    (bijective_codRestrict_kerFormalAdjointToDual A hD hDs cov hp hp_top hcov hJ hV)

/-- `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivKerPrecomp` sends `η` to the `L²`
pairing `w ↦ ∫ ⟪η, w⟫ dV`. -/
@[simp]
theorem coe_kerFormalAdjointEquivKerPrecomp_apply (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (η : hD.kerFormalAdjoint cov) :
    (kerFormalAdjointEquivKerPrecomp A hD hDs cov hp hp_top hcov hJ hV η :
        StrongDual ℝ (zeroOneSobolevSections A volume p 0)) =
      zeroOneHilbertSchmidtL A volume p 0 isPositiveDensityMeasure_riemannianVolume η
        ((hD.mem_kerFormalAdjoint cov).1 η.property).1.continuous :=
  -- The equivalence is `LinearEquiv.ofBijective` of the pairing map, restricted to its codomain.
  (congrArg Subtype.val (LinearEquiv.ofBijective_apply
    (hf := bijective_codRestrict_kerFormalAdjointToDual A hD hDs cov hp hp_top hcov hJ hV) _
      η)).trans (kerFormalAdjointToDual_apply A hD cov η)

include hD hDs in
/-- **`dim coker D = dim ker D*`** (McDuff–Salamon, (C.1.3), on a closed surface). For compatible
metrics, a smooth metric connection, the Riemannian volume and `1 < p < ∞`, the cokernel of
`D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` has the dimension of the space of smooth `(0,1)`-forms `η`
with `D* η = 0`. -/
theorem finrank_quotient_range_sobolevL_eq_finrank_kerFormalAdjoint (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    finrank ℝ (zeroOneSobolevSections A volume p 0 ⧸ (hD.sobolevL A hDs volume p).range) =
      finrank ℝ (hD.kerFormalAdjoint cov) := by
  have := finiteDimensional_quotient_range_sobolevL A hD hDs hp hp_top
  rw [(kerFormalAdjointEquivKerPrecomp A hD hDs cov hp hp_top hcov hJ hV).finrank_eq,
    ContinuousLinearMap.finrank_ker_precomp_eq_finrank_quotient_range
      (hD.sobolevL A hDs volume p) (isClosed_range_sobolevL A hD hDs hp hp_top)]

include A hD hDs in
/-- **The kernel of `D*` is finite-dimensional.** On a closed surface, for compatible metrics and a
smooth metric connection, the smooth `(0,1)`-forms `η` with `D* η = 0` form a finite-dimensional
space. -/
theorem finiteDimensional_kerFormalAdjoint (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    FiniteDimensional ℝ (hD.kerFormalAdjoint cov) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨ENNReal.one_lt_two.le⟩
  have hp : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have := finiteDimensional_quotient_range_sobolevL A hD hDs hp hp_top
  exact FiniteDimensional.of_injective _
    (injective_mkQ_comp_kerFormalAdjointToZeroOne A hD hDs cov hp_top hcov hJ hV)

include hD hDs in
/-- Every class in the cokernel of `D` contains exactly one smooth solution of `D* η = 0`. -/
private theorem bijective_mkQ_comp_kerFormalAdjointToZeroOne (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    Function.Bijective
      ((hD.sobolevL A hDs volume p).range.mkQ ∘ₗ hD.kerFormalAdjointToZeroOne A p cov) := by
  have := finiteDimensional_quotient_range_sobolevL A hD hDs hp hp_top
  have := finiteDimensional_kerFormalAdjoint A hD hDs cov hcov hJ hV
  have hinj := injective_mkQ_comp_kerFormalAdjointToZeroOne A hD hDs cov hp_top hcov hJ hV
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_quotient_range_sobolevL_eq_finrank_kerFormalAdjoint A hD hDs cov hp hp_top hcov hJ
      hV).symm).1 hinj⟩

include hD hDs in
/-- **The cokernel of `D` is the kernel of `D*`** (McDuff–Salamon, (C.1.3), on a closed surface).
For compatible metrics, a smooth metric connection, the Riemannian volume and `1 < p < ∞`, every
class in the cokernel of `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` contains exactly one smooth
`(0,1)`-form `η` with `D* η = 0`: the map sending `η` to its class is a linear equivalence. -/
def kerFormalAdjointEquivQuotientRange (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    hD.kerFormalAdjoint cov ≃ₗ[ℝ]
      zeroOneSobolevSections A volume p 0 ⧸ (hD.sobolevL A hDs volume p).range :=
  LinearEquiv.ofBijective _
    (bijective_mkQ_comp_kerFormalAdjointToZeroOne A hD hDs cov hp hp_top hcov hJ hV)

/-- `TauCeti.IsRealCauchyRiemannOperator.kerFormalAdjointEquivQuotientRange` sends `η` to the
class of its `Lᵖ` form. -/
@[simp]
theorem kerFormalAdjointEquivQuotientRange_apply (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (η : hD.kerFormalAdjoint cov) :
    kerFormalAdjointEquivQuotientRange A hD hDs cov hp hp_top hcov hJ hV η =
      Submodule.Quotient.mk (hD.kerFormalAdjointToZeroOne A p cov η) := by
  rw [kerFormalAdjointEquivQuotientRange, LinearEquiv.ofBijective_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply]

include hD hDs in
/-- **The index is `dim ker D - dim ker D*`** (McDuff–Salamon, Theorem C.1.10 (i), on a closed
surface). For compatible metrics, a smooth metric connection, the Riemannian volume and
`1 < p < ∞`, the index of `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` is the dimension of its kernel
minus the dimension of the space of smooth `(0,1)`-forms `η` with `D* η = 0`. -/
theorem index_sobolevL_eq_finrank_sub (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫) :
    (hD.sobolevL A hDs volume p).index =
      finrank ℝ (hD.sobolevL A hDs volume p).ker - finrank ℝ (hD.kerFormalAdjoint cov) := by
  rw [ContinuousLinearMap.index_eq_finrank_sub,
    ← finrank_quotient_range_sobolevL_eq_finrank_kerFormalAdjoint A hD hDs cov hp hp_top hcov hJ hV]

end IsRealCauchyRiemannOperator

end TauCeti
