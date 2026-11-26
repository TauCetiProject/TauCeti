/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
import Mathlib.Tactic.Module
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Deriv
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq

/-!
# Regularity of the kernel and cokernel of smooth real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V`. In chart `i` it
reads `∂bar uᵢ + Zᵢ uᵢ`, where `Zᵢ` is the smooth zeroth-order term
`TauCeti.FiniteBundleAtlas.chartZeroOrder`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ae`).
A `(0,1)`-form is complex antilinear, so it is determined by its value on `1`, and the equation
`∂bar u + Z u = 0` is the real Cauchy–Riemann equation `∂ₛu + i ∂ₜu + 2 Z(u)(1) = 0` of the
planar theory.

* **Kernel.** For `1 < p ≤ ∞`, an element `w` of `W^{1,p}(Σ, V)` with `D w = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.sobolevL`) is a smooth section `s` with `D s = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`). In chart `i`, the
  chart data `u` of `w` and their weak derivative solve `∂ₛu + i ∂ₜu + 2 Zᵢ(u)(1) = 0` almost
  everywhere, so `u` agrees almost everywhere with a smooth function
  (`TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_chartValueL_of_sobolevL_eq_zero`).
  The planar theorem behind this,
  `TauCeti.exists_contDiffOn_ae_eq_of_hasWeakFDerivOn_cauchyRiemann`, works by duality and needs
  no exponent above `2`. The smooth chart functions glue to a smooth section
  (`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn_of_ae_eq`,
  `TauCeti.FiniteBundleAtlas.contMDiff_of_forall_contDiffOn_coord`).
* **Independence of the exponent.** Conversely, the Sobolev section of a `C¹` section `s` with
  `D s = 0` is in the kernel at every exponent
  (`TauCeti.IsRealCauchyRiemannOperator.ofContMDiffSection_mem_ker_sobolevL_iff`). So for
  `1 < p, p' ≤ ∞` the kernels at `p` and `p'` are linearly equivalent through the smooth sections
  they consist of (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEquiv`), and have the same
  dimension.
* **The adjoint equation, in a chart.** A locally `L^q` covector field `ηᵢ : ℂ → (F →L[ℝ] ℝ)`,
  `q > 1`, that annihilates the value on `1` of `∂bar φ + Zᵢ φ` for every test function `φ` on an
  open subset of the image of chart `i` agrees almost everywhere there with a smooth field
  (`TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`). This
  is the planar statement
  `TauCeti.exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero` for `J = i` and
  `S = 2 Zᵢ(·)(1)`. The fields representing an annihilator of the range of the realization of `D`
  in a chart solve this equation (`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_chartValueL_of_sobolevL_eq_zero`:
  the chart data of a kernel element agree almost everywhere with smooth functions.
* `TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`: a kernel element of
  the `W^{1,p} → Lᵖ` realization, `p > 1`, is the Sobolev section of a smooth section in the
  kernel of `D`.
* `TauCeti.IsRealCauchyRiemannOperator.ofContMDiffSection_mem_ker_sobolevL_iff`: the Sobolev
  section of a `C¹` section `s` is in the kernel exactly when `D s = 0`.
* `TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEquiv`,
  `TauCeti.IsRealCauchyRiemannOperator.finrank_ker_sobolevL_eq`: the kernels at two
  exponents `p, p' > 1` are linearly equivalent, so they have the same dimension.
* `TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`:
  a weak solution of the adjoint equation of `D` in a chart is smooth.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i) and its proof, Theorem C.2.3, and Appendix B.4.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace Complex
open ContinuousLinearMap
  (complexAntilinearPartL complexAntilinearPartL_apply_one lsmul lsmul_I_mul_lsmul_I)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold Distributions

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannRegularity : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

/-! ### The kernel -/

include hD hDs in
/-- **Smooth kernel elements.** A `C¹` section `s` with `D s = 0` has its Sobolev section in the
kernel of the realization `W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)`, for every `1 ≤ p ≤ ∞`. -/
theorem sobolevL_ofContMDiffSection_eq_zero {s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯} (hs : ∀ x, D s x = 0) :
    hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s) = 0 := by
  refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_)
  refine (ae_image_tangentHom_iff A volume i).2 ?_
  filter_upwards [chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p s i,
    chartValueL_zero_zeroOneSobolevSections_ae (A := A) (μ := volume) (p := p) (k := 0) i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h₁ h₂ hy
  rw [h₁, h₂, show D s = 0 from funext hs]
  exact A.tangentHom.coord_zero (i := (i : Fin A.tangentHom.n)) (A.image_tangentHom i ▸ hy)

include hD hDs in
/-- **The kernel equation for smooth sections.** If the Sobolev section of a `C¹` section `s` that
is smooth is in the kernel of the realization of `D`, then `D s = 0` everywhere: `D s` is
continuous and its chart readings vanish almost everywhere. -/
theorem apply_eq_zero_of_sobolevL_ofContMDiffSection_eq_zero {s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% (⇑s)))
    (h : hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s) = 0)
    (x : M) : D s x = 0 := by
  have hDsc : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x (D s x) :=
    (contMDiffOn_univ.1 (hDs.contMDiff (by simpa using hs.contMDiffOn))).continuous
  refine congrFun (A.tangentHom.eq_of_continuous_of_coord_ae_eq (μ := volume)
    (s := D s) (t := 0) hDsc
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℂ)) (n := 0) ℝ
      (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)).continuous fun (i : Fin A.n) ↦ ?_) x
  have h' := chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p s i
  rw [h] at h'
  rw [A.image_tangentHom]
  filter_upwards [h'.symm.trans
      (chartValueL_zero_zeroOneSobolevSections_ae (A := A) (μ := volume) (p := p) (k := 0) i),
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyi
  exact hy.trans (A.tangentHom.coord_zero (i := (i : Fin A.tangentHom.n))
    (A.image_tangentHom i ▸ hyi)).symm

include hD hDs in
/-- **The chart data of a kernel element are smooth.** For `1 < p ≤ ∞` and `w ∈ W^{1,p}(Σ, V)` with
`D w = 0`, the chart data of `w` in chart `i` agree almost everywhere on the chart image with a
smooth function. They solve `∂ₛu + i ∂ₜu + 2 Zᵢ(u)(1) = 0` almost everywhere, for their weak
derivative, so the planar regularity theorem applies with no lower bound on `p` beyond `1`. -/
theorem exists_contDiffOn_ae_eq_chartValueL_of_sobolevL_eq_zero (hp : 1 < p)
    {w : SobolevSection A volume p 1} (hw : hD.sobolevL A hDs volume p w = 0) (i : Fin A.n) :
    ∃ g : ℂ → F, ContDiffOn ℝ ∞ g (A.image i) ∧
      A.sectionChartData.chartValueL volume p 1 i w =ᵐ[volume.restrict (A.image i)] g := by
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL volume p i w
  have hchart := chartValueL_sobolevL_ae A hD hDs volume p w hDu
  rw [hw] at hchart
  refine exists_contDiffOn_ae_eq_of_hasWeakFDerivOn_cauchyRiemann (ℓ := ⊤)
    (J := fun _ ↦ lsmul ℝ ℂ Complex.I) (S := fun z ↦ (2 : ℝ) •
      (ContinuousLinearMap.apply ℝ F (1 : ℂ)).comp (A.chartZeroOrder D i z))
    contDiffOn_const
    ((contDiffOn_const.clm_comp (A.contDiffOn_chartZeroOrder_image hD hDs i)).const_smul _)
    (fun _ _ ↦ lsmul_I_mul_lsmul_I) hp (Lp.memLp _).memLpLoc hDu ?_
  filter_upwards [hchart,
    chartValueL_zero_zeroOneSobolevSections_ae (A := A) (μ := volume) (p := p) (k := 0) i]
    with y h₁ h₂
  rw [h₂] at h₁
  have h1 := congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h₁
  simp only [Pi.zero_apply, zero_apply, add_apply, complexAntilinearPartL_apply_one] at h1
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  linear_combination (norm := module) (-2 : ℝ) • h1

include hD hDs in
/-- **Kernel regularity on closed surfaces** (McDuff–Salamon, Theorem C.1.10 (i), proved as
Theorem C.2.3, for smooth operators). For `1 < p ≤ ∞`, an element `w` of the kernel of the
realization `W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator `D` is
the Sobolev section of a smooth section `s` with `D s = 0`. -/
theorem exists_contMDiff_of_sobolevL_eq_zero (hp : 1 < p) {w : SobolevSection A volume p 1}
    (hw : hD.sobolevL A hDs volume p w = 0) :
    ∃ (s : Π x : M, V x) (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s)),
      w = SobolevSection.ofContMDiffSection A volume p 1 ⟨s, hs.of_le (by simp)⟩ ∧
        ∀ x, D s x = 0 := by
  -- The smooth chart representatives glue to a smooth section.
  choose g hg hwg using exists_contDiffOn_ae_eq_chartValueL_of_sobolevL_eq_zero A hD hDs hp hw
  obtain ⟨s₀, hs₀⟩ := SobolevSection.exists_ae_eq_coord w
  obtain ⟨s, -, hsg⟩ := A.exists_continuous_coord_eqOn_of_ae_eq (μ := volume)
    (fun i ↦ (hg i).continuousOn) fun i ↦ (hs₀ i).symm.trans (hwg i)
  have hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s) :=
    A.contMDiff_of_forall_contDiffOn_coord fun i ↦ (hg i).congr (hsg i)
  set s₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨s, hs.of_le (by simp)⟩
  have hws : w = SobolevSection.ofContMDiffSection A volume p 1 s₁ :=
    SobolevSection.eq_of_ae_eq_coord (s := s)
      (fun i ↦ (hwg i).trans (ae_restrict_of_forall_mem (A.image i).isOpen.measurableSet
        fun y hy ↦ (hsg i hy).symm))
      (fun i ↦ SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s₁ i)
  exact ⟨s, hs, hws,
    apply_eq_zero_of_sobolevL_ofContMDiffSection_eq_zero A hD hDs (s := s₁) hs (hws ▸ hw)⟩

/-! ### Independence of the exponent -/

include hD hDs in
/-- **The kernel is the space of `C¹` solutions.** For `1 < p ≤ ∞`, the Sobolev section of a `C¹`
section `s` is in the kernel of the realization `W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` exactly when
`D s = 0`. The condition does not involve `p`. -/
theorem ofContMDiffSection_mem_ker_sobolevL_iff (hp : 1 < p)
    (s : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯) :
    SobolevSection.ofContMDiffSection A volume p 1 s ∈ (hD.sobolevL A hDs volume p).ker ↔
      ∀ x, D s x = 0 := by
  refine ⟨fun h ↦ ?_, sobolevL_ofContMDiffSection_eq_zero A hD hDs⟩
  obtain ⟨t, ht, hst, hDt⟩ := exists_contMDiff_of_sobolevL_eq_zero A hD hDs hp h
  rw [SobolevSection.ofContMDiffSection_injective A volume p 1 hst]
  exact hDt

include hD hDs in
/-- For `1 < p ≤ ∞`, every element of the kernel of the realization of `D` at exponent `p` is the
Sobolev section of a `C¹` section whose Sobolev section is in that kernel. -/
private theorem map_comap_ker_sobolevL (hp : 1 < p) :
    (((hD.sobolevL A hDs volume p).ker).comap
        (SobolevSection.ofContMDiffSection A volume p 1)).map
      (SobolevSection.ofContMDiffSection A volume p 1) =
      (hD.sobolevL A hDs volume p).ker := by
  refine le_antisymm (Submodule.map_comap_le _ _) fun w hw ↦ ?_
  obtain ⟨s, hs, rfl, -⟩ := exists_contMDiff_of_sobolevL_eq_zero A hD hDs hp hw
  exact ⟨_, hw, rfl⟩

/-- The kernel of the realization of `D` at exponent `p`, as the space of `C¹` sections whose
Sobolev sections lie in it. -/
private def kerSobolevLEquivComap (hp : 1 < p) :
    ((hD.sobolevL A hDs volume p).ker).comap
        (SobolevSection.ofContMDiffSection A volume p 1) ≃ₗ[ℝ]
      (hD.sobolevL A hDs volume p).ker :=
  (Submodule.equivMapOfInjective _ (SobolevSection.ofContMDiffSection_injective A volume p 1)
    _).trans (LinearEquiv.ofEq _ _ (map_comap_ker_sobolevL A hD hDs hp))

/-- `kerSobolevLEquivComap` sends a `C¹` section to its Sobolev section. -/
@[simp]
private theorem coe_kerSobolevLEquivComap_apply (hp : 1 < p)
    (t : (hD.sobolevL A hDs volume p).ker.comap (SobolevSection.ofContMDiffSection A volume p 1)) :
    (kerSobolevLEquivComap A hD hDs hp t : SobolevSection A volume p 1) =
      SobolevSection.ofContMDiffSection A volume p 1 t := by
  simp [kerSobolevLEquivComap, Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_ofEq_apply]

variable {p' : ℝ≥0∞} [Fact (1 ≤ p')]

/-- **The kernel does not depend on the exponent** (McDuff–Salamon, Theorem C.1.10 (i), proved as
Theorem C.2.3, for smooth operators). For `1 < p, p' ≤ ∞`, the kernels of the realizations
`W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` and `W^{1,p'}(Σ, V) → L^{p'}(Σ, Λ^{0,1} ⊗ V)` of a smooth
real Cauchy–Riemann operator are linearly equivalent: both consist of the Sobolev sections of the
smooth sections `s` with `D s = 0`, and the equivalence keeps `s`
(`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEquiv_apply_ofContMDiffSection`). -/
def kerSobolevLEquiv (hp : 1 < p) (hp' : 1 < p') :
    (hD.sobolevL A hDs volume p).ker ≃ₗ[ℝ]
      (hD.sobolevL A hDs volume p').ker :=
  (kerSobolevLEquivComap A hD hDs hp).symm.trans <|
    (LinearEquiv.ofEq _ _ (Submodule.ext fun s ↦
      (ofContMDiffSection_mem_ker_sobolevL_iff A hD hDs hp s).trans
        (ofContMDiffSection_mem_ker_sobolevL_iff A hD hDs hp' s).symm)).trans
      (kerSobolevLEquivComap A hD hDs hp')

/-- The equivalence of kernels at two exponents sends the Sobolev section of a `C¹` solution `s`
of `D s = 0` at one exponent to its Sobolev section at the other. -/
@[simp]
theorem kerSobolevLEquiv_apply_ofContMDiffSection (hp : 1 < p) (hp' : 1 < p')
    {s : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯}
    (hs : SobolevSection.ofContMDiffSection A volume p 1 s ∈
      (hD.sobolevL A hDs volume p).ker) :
    (kerSobolevLEquiv A hD hDs hp hp' ⟨_, hs⟩ : SobolevSection A volume p' 1) =
      SobolevSection.ofContMDiffSection A volume p' 1 s := by
  have h : (kerSobolevLEquivComap A hD hDs hp).symm ⟨_, hs⟩ = ⟨s, hs⟩ :=
    (kerSobolevLEquivComap A hD hDs hp).symm_apply_eq.2
      (Subtype.ext (coe_kerSobolevLEquivComap_apply A hD hDs hp ⟨s, hs⟩).symm)
  simp [kerSobolevLEquiv, h]

/-- **The dimension of the kernel does not depend on the exponent.** -/
theorem finrank_ker_sobolevL_eq (hp : 1 < p) (hp' : 1 < p') :
    finrank ℝ ((hD.sobolevL A hDs volume p).ker) =
      finrank ℝ ((hD.sobolevL A hDs volume p').ker) :=
  (kerSobolevLEquiv A hD hDs hp hp').finrank_eq

/-! ### The cokernel, in a chart -/

include hD hDs in
/-- **Weak solutions of the adjoint equation are smooth in a chart.** Let `Ω` be an open subset of
the image of chart `i` and `η` a locally `L^q` covector field on `Ω`, `q > 1`, such that
`∫ η (∂bar φ + Zᵢ φ)(1) = 0` for every test function `φ` on `Ω`, where `Zᵢ` is the zeroth-order
term of `D` in chart `i`. Then `η` agrees almost everywhere on `Ω` with a smooth covector field.
The fields representing an annihilator of the range of the realization of `D` satisfy this
equation (`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`). -/
theorem exists_contDiffOn_ae_eq_of_forall_integral_eq_zero {i : Fin A.n} {Ω : Opens ℂ}
    (hΩ : (Ω : Set ℂ) ⊆ A.image i) {η : ℂ → F →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q)
    (hη : MemLpLoc q Ω η)
    (h : ∀ φ : 𝓓(Ω, F), ∫ z, η z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
      A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0) :
    ∃ g : ℂ → F →L[ℝ] ℝ, ContDiffOn ℝ ∞ g Ω ∧ η =ᵐ[volume.restrict Ω] g := by
  have hZ := (A.contDiffOn_chartZeroOrder_image hD hDs i).mono hΩ
  -- The planar form of the equation: `J = i` and `S = 2 Zᵢ(·)(1)`.
  refine exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero
    (J := fun _ ↦ lsmul ℝ ℂ Complex.I) (S := fun z ↦ (2 : ℝ) •
      (ContinuousLinearMap.apply ℝ F (1 : ℂ)).comp (A.chartZeroOrder D i z))
    contDiffOn_const ((contDiffOn_const.clm_comp hZ).const_smul _)
    (fun _ _ ↦ lsmul_I_mul_lsmul_I) hq hη fun φ ↦
      integral_apply_cauchyRiemann_eq_zero_of_integral_eq_zero (h φ)

end IsRealCauchyRiemannOperator

end TauCeti
