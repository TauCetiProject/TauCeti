/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Holomorphic frames of complex linear Cauchy–Riemann operators

Let `D` be a complex linear real Cauchy–Riemann operator on a complex vector bundle `V` over a
complex manifold `M`, for the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of `M`. A *nonvanishing holomorphic
section* of `D` on a set `U` is a smooth section of `V` which is nowhere zero on `U` and in the
kernel of `D` on `U`. On a complex line bundle, such a section is a *holomorphic frame* of `D` on
`U`: its value at each point of `U` is a basis of the fibre.

On a complex line bundle over a complex curve, such an operator has holomorphic frames near every
point, by the similarity principle; two of them differ by nowhere-zero holomorphic functions, and
the kernel of `D` near a point consists of the holomorphic multiples of a holomorphic frame. So `D`
is a holomorphic structure on `V`, whose holomorphic sections are the kernel of `D`.

The frame near `x₀` is built from the frame `s` of the trivialization `e` of `V` at `x₀` and the
chart `φ` at `x₀`. Over the chart domain and the base set of `e`, `D s = (B • conj dz) ⊗ s` for
the coefficient `B = TauCeti.cauchyRiemannChartCoeff D b x₀`
(`TauCeti.IsRealCauchyRiemannOperator.apply_localFrame_mfderivWithin_extChartAt_symm`), assumed
smooth near the chart point of `x₀`. A smooth solution `g` of `∂bar g = -B`
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`) gives the holomorphic frame
`exp (g ∘ φ) • s`, by the complex Leibniz rule
`TauCeti.IsRealCauchyRiemannOperator.leibniz_complex`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff` and
  `TauCeti.IsRealCauchyRiemannOperator.forall_apply_smul_eq_zero_iff`: against a nonvanishing
  holomorphic section `σ`, the section `f • σ` is in the kernel of `D` exactly when `f` is
  holomorphic.
* `TauCeti.IsRealCauchyRiemannOperator.apply_localFrame_mfderivWithin_extChartAt_symm`: the
  operator on the frame of a trivialization, through its chart coefficient.
* `TauCeti.IsRealCauchyRiemannOperator.exists_isNonvanishingHolomorphicOn`: local
  holomorphic frames on a line bundle over a complex curve.
* `TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul`: on a line bundle, every
  section in the kernel of `D` is a holomorphic multiple of a holomorphic frame.
* `IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul_of_isNonvanishingHolomorphicOn`:
  two holomorphic frames differ by a nowhere-zero holomorphic function.

## Implementation notes

In the curve construction, the model fibre may be any complex rank-one normed space. A
continuous complex-linear equivalence `b` with `ℂ` chooses the scalar coordinate. The chart
coefficient is assumed smooth
near the chart centre. `HolomorphicFrame.Smooth` derives the assumption from native covariant
regularity of the given operator; `CauchyRiemann.LineBundle` constructs its actual
holomorphic bundle and the smooth comparison with the original bundle.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1.
* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

variable (F) in
/-- A *nonvanishing holomorphic section* of an operator `D` on a set `U`: a smooth section of `V`
which is nowhere zero on `U` and is in the kernel of `D` at every point of `U`. On a line bundle
it is a holomorphic frame of `D` on `U`. -/
structure IsNonvanishingHolomorphicOn (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x)
    (σ : Π x : M, V x) (U : Set M) : Prop where
  contMDiffOn : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% σ) U
  ne_zero : ∀ x ∈ U, σ x ≠ 0
  apply_eq_zero : ∀ x ∈ U, D σ x = 0

theorem IsNonvanishingHolomorphicOn.mono {σ : Π x : M, V x} {U U' : Set M}
    (hσ : IsNonvanishingHolomorphicOn F D σ U) (h : U' ⊆ U) :
    IsNonvanishingHolomorphicOn F D σ U' where
  contMDiffOn := hσ.contMDiffOn.mono h
  ne_zero x hx := hσ.ne_zero x (h hx)
  apply_eq_zero x hx := hσ.apply_eq_zero x (h hx)

theorem IsNonvanishingHolomorphicOn.mdifferentiableAt {σ : Π x : M, V x} {U : Set M}
    (hσ : IsNonvanishingHolomorphicOn F D σ U) (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    MDiffAt (T% σ) x :=
  (hσ.contMDiffOn.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)

/-- A local kernel frame depends only on its values on an open set. The original real
Cauchy–Riemann law supplies locality of the operator, so this does not hold for arbitrary
nonlocal operators on global sections. -/
theorem IsNonvanishingHolomorphicOn.congr [IsManifold I ∞ M] [VectorBundle ℝ F V]
    [∀ x, Module ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    {j : SmoothAlmostComplexStructure I M} {σ τ : Π x : M, V x} {U : Set M}
    (hσ : IsNonvanishingHolomorphicOn F D σ U)
    (hD : IsRealCauchyRiemannOperator F j D) (hU : IsOpen U)
    (h : ∀ x ∈ U, τ x = σ x) :
    IsNonvanishingHolomorphicOn F D τ U where
  contMDiffOn := hσ.contMDiffOn.congr fun x hx ↦ congrArg (TotalSpace.mk' F x) (h x hx)
  ne_zero x hx := (h x hx).trans_ne (hσ.ne_zero x hx)
  apply_eq_zero x hx :=
    (hD.apply_eq_of_eventuallyEq (hσ.mdifferentiableAt hU hx)
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ h y hy)).trans (hσ.apply_eq_zero x hx)

end General

section ComplexManifold

open scoped TauCeti.ComplexManifold
open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}

namespace IsRealCauchyRiemannOperator

variable (hD : IsRealCauchyRiemannOperator F (ofComplexManifold E M) D)
  (hDℂ : IsComplexLinearOperator F D)
include hD hDℂ

/-- Against a nonzero section `σ` in the kernel of a complex linear real Cauchy–Riemann operator
on a complex manifold, `f • σ` is in the kernel at a point exactly when `f` is holomorphic
there. -/
theorem apply_smul_eq_zero_iff {σ : Π x : M, V x} {f : M → ℂ} {x : M}
    (hσ : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (T% σ) x) (hσ0 : σ x ≠ 0)
    (hDσ : D σ x = 0) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f x) :
    D (f • σ) x = 0 ↔ MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f x := by
  rw [hD.leibniz_complex hDℂ hσ hf, hDσ, smul_zero, zero_add,
    zeroOnePart_smulRight_eq_zero_iff _ hσ0,
    mdifferentiableAt_iff_mvfderiv_ofComplexManifold_apply hf]

/-- **Holomorphic multiples of a nonvanishing holomorphic section.** If `σ` is a nonvanishing
holomorphic section of a complex linear real Cauchy–Riemann operator `D` on an open set `U` of a
complex manifold, a section `f • σ`
with `f` real differentiable on `U` is in the kernel of `D` on `U` exactly when `f` is holomorphic
on `U`. -/
theorem forall_apply_smul_eq_zero_iff {σ : Π x : M, V x} {U : Set M}
    (hσ : IsNonvanishingHolomorphicOn F D σ U) (hU : IsOpen U) {f : M → ℂ}
    (hf : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f U) :
    (∀ x ∈ U, D (f • σ) x = 0) ↔ MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f U := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · refine (((hD.apply_smul_eq_zero_iff hDℂ (hσ.mdifferentiableAt hU hx) (hσ.ne_zero x hx)
      (hσ.apply_eq_zero x hx) ((hf x hx).mdifferentiableAt (hU.mem_nhds hx))).1
      (h x hx))).mdifferentiableWithinAt
  · exact (hD.apply_smul_eq_zero_iff hDℂ (hσ.mdifferentiableAt hU hx) (hσ.ne_zero x hx)
      (hσ.apply_eq_zero x hx) ((hf x hx).mdifferentiableAt (hU.mem_nhds hx))).2
      ((h x hx).mdifferentiableAt (hU.mem_nhds hx))

end IsRealCauchyRiemannOperator

end ComplexManifold

/-! ### Line bundles -/

section LineBundle

open scoped TauCeti.ComplexManifold
open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {V : M → Type*} [TopologicalSpace (TotalSpace ℂ V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle ℂ V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ ℂ V] [VectorBundle ℝ ℂ V]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}

namespace IsRealCauchyRiemannOperator

variable (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold E M) D)
  (hDℂ : IsComplexLinearOperator ℂ D)
include hD hDℂ

/-- **The kernel is the space of holomorphic sections.** If `σ` is a holomorphic frame of a complex
linear real Cauchy–Riemann operator on a line bundle over a complex manifold, on an open set `U`,
every section `τ` differentiable on `U` and in the kernel of `D` on `U` is `h • σ` on `U` for a
function `h` holomorphic on `U`. -/
theorem exists_mdifferentiableOn_eq_smul {σ τ : Π x : M, V x} {U : Set M}
    (hσ : IsNonvanishingHolomorphicOn ℂ D σ U) (hU : IsOpen U)
    (hτ : ∀ x ∈ U, MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℂ)) (T% τ) x)
    (hDτ : ∀ x ∈ U, D τ x = 0) :
    ∃ h : M → ℂ, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h U ∧ ∀ x ∈ U, τ x = h x • σ x := by
  let h : M → ℂ := fun x ↦ (trivializationAt ℂ V x).coordRatio (σ x) (τ x)
  have hτh : ∀ x ∈ U, τ x = h x • σ x := fun x hx ↦
    Trivialization.eq_coordRatio_smul _ (mem_baseSet_trivializationAt ℂ V x) (hσ.ne_zero x hx) _
  refine ⟨h, fun x₀ hx₀ ↦ ?_, hτh⟩
  set e₀ := trivializationAt ℂ V x₀
  have hx₀e : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt ℂ V x₀
  -- Near `x₀`, `h` is the ratio of the coordinates of `τ` and `σ` in the trivialization at `x₀`.
  have hloc : h =ᶠ[𝓝 x₀] fun x ↦ (e₀ ⟨x, τ x⟩).2 / (e₀ ⟨x, σ x⟩).2 := by
    filter_upwards [hU.mem_nhds hx₀, e₀.open_baseSet.mem_nhds hx₀e] with x hx hxe
    rw [← e₀.continuousLinearMapAt_apply_of_mem (R := ℂ) hxe,
      ← e₀.continuousLinearMapAt_apply_of_mem (R := ℂ) hxe, ← e₀.coordRatio_def]
    exact (e₀.coordRatio_eq_of_eq_smul hxe (hσ.ne_zero x hx) (hτh x hx)).symm
  have hnum := (mdifferentiableAt_section 𝓘(ℝ, E) τ).1 (hτ x₀ hx₀)
  have hden := (mdifferentiableAt_section 𝓘(ℝ, E) σ).1 (hσ.mdifferentiableAt hU hx₀)
  have hden0 : (e₀ ⟨x₀, σ x₀⟩).2 ≠ 0 := by
    rw [← e₀.continuousLinearMapAt_apply_of_mem (R := ℂ) hx₀e]
    intro h0
    apply hσ.ne_zero x₀ hx₀
    rw [← e₀.symmL_continuousLinearMapAt (R := ℂ) hx₀e (σ x₀), h0, map_zero]
  have hhR : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) h x₀ :=
    (hnum.div hden hden0).congr_of_eventuallyEq hloc
  -- `h • σ` agrees with `τ` near `x₀`, so it is in the kernel of `D` at `x₀`.
  have hker : D (h • σ) x₀ = 0 := by
    rw [hD.apply_eq_of_eventuallyEq (σ := h • σ) (hτ x₀ hx₀)
      (Filter.mem_of_superset (hU.mem_nhds hx₀) fun x hx ↦ (hτh x hx).symm)]
    exact hDτ x₀ hx₀
  exact ((hD.apply_smul_eq_zero_iff hDℂ (hσ.mdifferentiableAt hU hx₀) (hσ.ne_zero x₀ hx₀)
    (hσ.apply_eq_zero x₀ hx₀) hhR).1 hker).mdifferentiableWithinAt

/-- **Holomorphic transition functions.** Two holomorphic frames of a complex linear real
Cauchy–Riemann operator on a line bundle over a complex manifold differ, on the overlap of their
open domains, by a nowhere-zero holomorphic function. -/
theorem exists_mdifferentiableOn_eq_smul_of_isNonvanishingHolomorphicOn {σ σ' : Π x : M, V x}
    {U U' : Set M} (hσ : IsNonvanishingHolomorphicOn ℂ D σ U)
    (hσ' : IsNonvanishingHolomorphicOn ℂ D σ' U') (hU : IsOpen U) (hU' : IsOpen U') :
    ∃ h : M → ℂ, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h (U ∩ U') ∧
      ∀ x ∈ U ∩ U', h x ≠ 0 ∧ σ' x = h x • σ x := by
  obtain ⟨h, hh, hσ'h⟩ := hD.exists_mdifferentiableOn_eq_smul hDℂ
    (hσ.mono inter_subset_left) (hU.inter hU') (fun x hx ↦ hσ'.mdifferentiableAt hU' hx.2)
    (fun x hx ↦ hσ'.apply_eq_zero x hx.2)
  refine ⟨h, hh, fun x hx ↦ ⟨fun h0 ↦ hσ'.ne_zero x hx.2 ?_, hσ'h x hx⟩⟩
  rw [hσ'h x hx, h0, zero_smul]

end IsRealCauchyRiemannOperator

end LineBundle

/-! ### Holomorphic frames on complex curves -/

section Curve

open scoped TauCeti.ComplexManifold
open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]

/-- The coefficient of an operator `D` on a complex line bundle `V` over a complex curve, in the
chart `φ` and the trivialization `e` at `x₀`: at `z`, the coordinate through `b` in `e` of
`D s`, for the frame `s = e⁻¹ (b⁻¹ 1)` of `e` (`Bundle.Trivialization.localFrame`), evaluated on the
coordinate vector `∂/∂x = dφ⁻¹ 1` of the chart. For a real Cauchy–Riemann operator, whose values
are `(0,1)`-forms, `D s = (B • conj dz) ⊗ s` at the points of the chart domain in the base set
of `e`, where `B` is this coefficient
(`TauCeti.IsRealCauchyRiemannOperator.apply_localFrame_mfderivWithin_extChartAt_symm`). -/
def cauchyRiemannChartCoeff (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (b : F ≃L[ℂ] ℂ) (x₀ : M) (z : ℂ) : ℂ :=
  b ((trivializationAt F V x₀).continuousLinearMapAt ℂ ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
    (D ((trivializationAt F V x₀).localFrame
        ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ())
      ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm
            (range 𝓘(ℝ, ℂ)) z (1 : ℂ))))

omit [IsManifold 𝓘(ℂ, ℂ) ∞ M] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℝ F V] in
/-- The defining equation of `TauCeti.cauchyRiemannChartCoeff`. -/
theorem cauchyRiemannChartCoeff_apply
    (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (b : F ≃L[ℂ] ℂ) (x₀ : M) (z : ℂ) :
    cauchyRiemannChartCoeff D b x₀ z =
      b ((trivializationAt F V x₀).continuousLinearMapAt ℂ ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
        (D ((trivializationAt F V x₀).localFrame
        ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ())
          ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
          (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm
            (range 𝓘(ℝ, ℂ)) z (1 : ℂ)))) :=
  (rfl)

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- The scalar chart coefficient is the hom-bundle coordinate of the operator applied to the
constant local frame, evaluated on the model vector `1`. This identifies the native hom-bundle
reading used for covariant smoothness with the inverse-chart formula. -/
theorem cauchyRiemannChartCoeff_eq_hom_trivializationAt
    (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (b : F ≃L[ℂ] ℂ) (x₀ : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).target)
    (hze : (extChartAt 𝓘(ℝ, ℂ) x₀).symm z ∈ (trivializationAt F V x₀).baseSet) :
    cauchyRiemannChartCoeff D b x₀ z =
      b (((trivializationAt (ℂ →L[ℝ] F)
        (fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x₀)
          ⟨(extChartAt 𝓘(ℝ, ℂ) x₀).symm z,
            D ((trivializationAt F V x₀).localFrame
              ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ())
              ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)⟩).2 1) := by
  have hy : (extChartAt 𝓘(ℝ, ℂ) x₀).symm z ∈ (chartAt ℂ x₀).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, ℂ) x₀).map_target hz
  symm
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [TangentBundle.symmL_trivializationAt hy, (extChartAt 𝓘(ℝ, ℂ) x₀).right_inv hz]
  rw [cauchyRiemannChartCoeff_apply,
    (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem (R := ℂ) hze,
    (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem (R := ℝ) hze]
  -- The remaining inverse-chart derivative has source the model tangent space `ℂ`;
  -- only its tangent-space type alias and continuous-linear-map coercions differ.
  rfl

variable (b : F ≃L[ℂ] ℂ)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}

omit [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℝ F V] in
/-- **The operator in a chart and a trivialization.** At a point `φ⁻¹ z` of the chart domain at
`x₀` lying in the base set of the trivialization `e` at `x₀`, a real Cauchy–Riemann operator sends
the frame `s` of `e` to `(B • conj dz) ⊗ s`: on the tangent vector `dφ⁻¹ w` it is
`(conj w * B z) • s`, for the chart coefficient `B = TauCeti.cauchyRiemannChartCoeff D b x₀`. -/
theorem IsRealCauchyRiemannOperator.apply_localFrame_mfderivWithin_extChartAt_symm
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D) {x₀ : M} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).target)
    (hze : (extChartAt 𝓘(ℝ, ℂ) x₀).symm z ∈ (trivializationAt F V x₀).baseSet) (w : ℂ) :
    D ((trivializationAt F V x₀).localFrame
        ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ())
        ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm (range 𝓘(ℝ, ℂ)) z w) =
      (starRingEnd ℂ w * cauchyRiemannChartCoeff D b x₀ z) •
        (trivializationAt F V x₀).localFrame
          ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
          ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z) := by
  set e := trivializationAt F V x₀
  set s : Π x : M, V x := e.localFrame ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  set y := (extChartAt 𝓘(ℝ, ℂ) x₀).symm z
  -- Read in `e`, the value of `D s` on `∂/∂x` is `B • s`, since `s` has coordinate `1`.
  have h1 : D s y (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm
      (range 𝓘(ℝ, ℂ)) z (1 : ℂ)) = cauchyRiemannChartCoeff D b x₀ z • s y := by
    apply (e.continuousLinearEquivAt ℂ y hze).injective
    apply b.injective
    rw [Trivialization.coe_continuousLinearEquivAt_eq, map_smul,
      Manifold.continuousLinearMapAt_localFrame _ hze, Module.Basis.map_apply,
      Module.Basis.singleton_apply]
    rw [ContinuousLinearEquiv.coe_toLinearEquiv, map_smul, b.apply_symm_apply,
      smul_eq_mul, mul_one]
    exact (cauchyRiemannChartCoeff_apply D b x₀ z).symm
  rw [(hD.isZeroOneForm s y).apply_mfderivWithin_extChartAt_symm hz, h1, smul_smul]

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

namespace IsRealCauchyRiemannOperator

variable (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDℂ : IsComplexLinearOperator F D)
include hD hDℂ

omit [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
private theorem apply_exp_smul_localFrame_one_eq_zero (x₀ : M) {G : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).target)
    (hze : (extChartAt 𝓘(ℝ, ℂ) x₀).symm z ∈ (trivializationAt F V x₀).baseSet)
    (hsx : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F))
      (T% ((trivializationAt F V x₀).localFrame
        ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()))
      ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)) (hG : DifferentiableAt ℝ G z)
    (hGeq : conjWirtingerDeriv G z 1 = -cauchyRiemannChartCoeff D b x₀ z) :
    D ((fun x ↦ Complex.exp (G (extChartAt 𝓘(ℝ, ℂ) x₀ x))) •
      (trivializationAt F V x₀).localFrame
        ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ())
      ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm
        (range 𝓘(ℝ, ℂ)) z (1 : ℂ)) = 0 := by
  set φ := extChartAt 𝓘(ℝ, ℂ) x₀
  set e := trivializationAt F V x₀
  set s := e.localFrame ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  set H : ℂ → ℂ := fun w ↦ Complex.exp (G w)
  set f : M → ℂ := H ∘ φ
  set y := φ.symm z
  set L := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm (range 𝓘(ℝ, ℂ)) z
  have hhy : DifferentiableAt ℝ H (φ y) := by
    simpa only [y, φ.right_inv hz] using (show DifferentiableAt ℝ H z from hG.cexp)
  have hφ := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ℂ))
    (by simpa only [φ, extChartAt_source] using φ.map_target hz)
  have hchain (w : ℂ) : mvfderiv 𝓘(ℝ, ℂ) f y (L w) = fderiv ℝ H z w := by
    -- Expanding `f` here also normalizes `L`'s source `TangentSpace 𝓘(ℝ, ℂ) z` to
    -- its model `ℂ`, before applying the chain rule to the displayed composition.
    change mvfderiv 𝓘(ℝ, ℂ) (H ∘ φ) y (L w) = _
    rw [mvfderiv_comp_apply_of_differentiableAt hhy hφ,
      mvfderiv_apply_eq_mfderiv_apply, φ.right_inv hz]
    exact congrArg (fderiv ℝ H z)
      congr($(mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, ℂ)) hz) w)
  have hdI : mvfderiv 𝓘(ℝ, ℂ) f y (ofComplexManifold ℂ M y (L (1 : ℂ))) =
      fderiv ℝ H z Complex.I := by
    rw [ofComplexManifold_apply_mfderivWithin_extChartAt_symm_one hz]
    exact hchain Complex.I
  have hs1 : e.continuousLinearMapAt ℂ y (s y) = b.symm 1 :=
    e.continuousLinearMapAt_localFrame_singleton b hze
  have hval : D (f • s) y (L (1 : ℂ)) = f y • D s y (L (1 : ℂ)) +
      (2⁻¹ : ℝ) • (mvfderiv 𝓘(ℝ, ℂ) f y (L (1 : ℂ)) • s y +
        Complex.I • (mvfderiv 𝓘(ℝ, ℂ) f y (ofComplexManifold ℂ M y (L (1 : ℂ))) • s y)) := by
    simp only [hD.leibniz_complex (σ := s) (f := f) (x := y) hDℂ hsx
      (hhy.mdifferentiableAt.comp y hφ), add_apply, smul_apply, zeroOnePart_apply,
      ContinuousLinearMap.smulRight_apply]
  have hfz : f y = Complex.exp (G z) := by simp [f, H, y, φ.right_inv hz]
  have hBz : b (e.continuousLinearMapAt ℂ y (D s y (L (1 : ℂ)))) =
      cauchyRiemannChartCoeff D b x₀ z := (cauchyRiemannChartCoeff_apply D b x₀ z).symm
  have hfd : fderiv ℝ H z = Complex.exp (G z) • fderiv ℝ G z := hG.hasFDerivAt.cexp.fderiv
  -- Fold the displayed exponential section and inverse-chart differential into the local
  -- names `f`, `s`, `y`, `L` used by the Leibniz identity `hval`.
  change D (f • s) y (L (1 : ℂ)) = 0
  apply (e.continuousLinearEquivAt ℂ y hze).injective
  apply b.injective
  rw [Trivialization.coe_continuousLinearEquivAt_eq, map_zero, map_zero, hval,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (E := V y) (2⁻¹ : ℝ)]
  rw [conjWirtingerDeriv_apply] at hGeq
  simp only [map_add, map_smul, hBz, hs1, hchain 1, hdI, hfz, hfd, smul_apply,
    b.apply_symm_apply, smul_eq_mul, mul_one] at hGeq ⊢
  push_cast
  linear_combination Complex.exp (G z) * hGeq

/-- **Local holomorphic frames** (McDuff–Salamon, Appendix C, via the similarity principle).
A complex linear real Cauchy–Riemann operator on a complex line bundle over a complex curve,
whose coefficient in the chart and trivialization at `x₀` is smooth near `x₀`, has a holomorphic
frame on an open neighbourhood of `x₀`: a smooth section, nowhere zero there, in the kernel of
`D`. -/
theorem exists_isNonvanishingHolomorphicOn (x₀ : M)
    (hB : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, ℂ) x₀ x₀), ContDiffAt ℝ ∞ (cauchyRiemannChartCoeff D b x₀) z) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ σ : Π x : M, V x, IsNonvanishingHolomorphicOn F D σ U := by
  set φ := extChartAt 𝓘(ℝ, ℂ) x₀
  set e := trivializationAt F V x₀
  set s : Π x : M, V x :=
    e.localFrame ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  -- The frame has constant nonzero coordinate `b⁻¹ 1` in `e`.
  have hs1 (x : M) (hx : x ∈ e.baseSet) : e.continuousLinearMapAt ℂ x (s x) = b.symm 1 :=
    e.continuousLinearMapAt_localFrame_singleton b hx
  have hcoord (x : M) (hx : x ∈ e.baseSet) (c : ℂ) : (e ⟨x, c • s x⟩).2 = b.symm c := by
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx, map_smul, hs1 x hx,
      ← map_smul, smul_eq_mul, mul_one]
  have hs_smooth : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet_of_basis
      ((Module.Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  -- A smooth solution `G` of `∂bar G = -B` near the chart point of `x₀`.
  obtain ⟨W₁, hW₁, hW₁o, hz₀W₁⟩ := eventually_nhds_iff.mp hB
  obtain ⟨G, hG, hGeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq le_top hW₁o
      (fun z hz ↦ (hW₁ z hz).neg.contDiffWithinAt) hz₀W₁
  obtain ⟨W₂, hW₂, hW₂o, hz₀W₂⟩ := eventually_nhds_iff.mp hGeq
  let U : Set M := (φ.source ∩ e.baseSet) ∩ φ ⁻¹' W₂
  have hUo : IsOpen U :=
    ((continuousOn_extChartAt x₀).mono inter_subset_left).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter e.open_baseSet) hW₂o
  have hUe : U ⊆ e.baseSet := fun x hx ↦ hx.1.2
  have hx₀U : x₀ ∈ U :=
    ⟨⟨mem_extChartAt_source x₀, mem_baseSet_trivializationAt F V x₀⟩, hz₀W₂⟩
  set f : M → ℂ := fun x ↦ Complex.exp (G (φ x))
  have hf_smooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f U :=
    (Complex.contDiff_exp.comp hG).contMDiff.comp_contMDiffOn
      ((contMDiffOn_extChartAt (x := x₀)).mono fun x hx ↦ by
      simpa [φ] using hx.1.1)
  refine ⟨U, hUo, hx₀U, f • s, ⟨?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩⟩
  · rw [e.contMDiffOn_section_iff hUo hUe]
    exact ((b.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
      hf_smooth).congr
      fun x hx ↦ hcoord x (hUe hx) (f x)
  · refine smul_ne_zero (Complex.exp_ne_zero _) fun h0 ↦ ?_
    have := congrArg b (hs1 x (hUe hx))
    simp [h0] at this
  · -- Read the point in the chart: `x = φ⁻¹ z`.
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ φ.target, φ.symm z = x :=
      ⟨φ x, φ.map_source hx.1.1, φ.left_inv hx.1.1⟩
    have hzW₂ : z ∈ W₂ := by simpa [φ.right_inv hz] using hx.2
    have hsx : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) (T% s) (φ.symm z) :=
      (hs_smooth.contMDiffAt (e.open_baseSet.mem_nhds hx.1.2)).mdifferentiableAt (by simp)
    have hform := hD.isZeroOneForm (f • s) (φ.symm z)
    exact (hform.eq_zero_iff_apply_mfderivWithin_extChartAt_symm_one hz).2
      (apply_exp_smul_localFrame_one_eq_zero b hD hDℂ x₀ hz hx.1.2 hsx
        (hG.differentiable (by simp) z) (hW₂ z hzW₂))

end IsRealCauchyRiemannOperator

end Curve

end TauCeti
