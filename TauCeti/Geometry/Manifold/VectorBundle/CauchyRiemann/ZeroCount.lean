/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.CauchyRiemann

/-!
# The zero count for the kernel of a real Cauchy–Riemann operator on a line bundle

Let `L` be a complex line bundle over a compact connected Riemann surface `X`, smooth as a real
vector bundle, and let `D` be a real Cauchy–Riemann operator on `L` of class `C^n` for some
`n`, which may be `0`. A `C¹` section `s` with
`D s = 0` which is not identically zero has finitely many zeros
(`TauCeti.IsRealCauchyRiemannOperator.finite_setOf_eq_zero`). For a section in the kernel with
finitely many zeros, their number is at most the first Chern number `c₁(L)[X]`, the Euler class of
`L` with its complex orientation (`TauCeti.complexEulerClass`) evaluated on the fundamental class
of `X` (`TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`). So a
section in the kernel vanishing at more than `c₁(L)[X]` points vanishes identically
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard`),
and if `c₁(L)[X] < 0` the kernel on `C¹` sections is zero
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_neg`).
This is the injectivity half of the vanishing theorem of McDuff–Salamon, Theorem C.1.10 (iii), in
the closed case.

The proof reads `s` in the charts of a finite bundle atlas, which are preferred charts of `X` and
preferred trivializations of `L`. There `D s = 0` reads `\bar∂ sᵢ = -Zᵢ sᵢ`
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`),
with a bounded zeroth-order term `Zᵢ`
(`TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`), so the reading satisfies the
Cauchy–Riemann inequality `‖\bar∂ sᵢ‖ ≤ C ‖sᵢ‖`
(`TauCeti.FiniteBundleAtlas.exists_norm_complexAntilinearPartL_fderiv_coord_le`). The holomorphic
charts carry the canonical local orientation of `X` to that of `ℂ`
(`TauCeti.localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas`), and the
complex-linear trivializations read the complex orientation of `L` as that of `ℂ`
(`TauCeti.VectorBundleOrientation.mapOrientation_reindex_complex_eq_orientation`), so the zero
count for sections solving a Cauchy–Riemann inequality
(`ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le` in the namespace
`TauCeti.VectorBundleOrientation`) applies.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.finite_setOf_eq_zero`: on a connected `X`, a nonzero `C¹`
  section in the kernel has finitely many zeros.
* `TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`: a `C¹`
  section in the kernel with finitely many zeros has at most `c₁(L)[X]` of them.
* `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard`
  and `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_evalFundamentalClass_complexEulerClass_neg`:
  the kernel is detected by values at any `c₁(L)[X] + 1` distinct points, and is zero if
  `c₁(L)[X] < 0`.

## Implementation notes

Kernel elements are assumed `C¹`. For the Sobolev realizations of `D` this needs elliptic
regularity of the kernel, which is not used here.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), Theorem C.1.10 (iii) and its proof (p. 603).
-/

public section

noncomputable section

open Bundle Module Set Filter Topology
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X] [T2Space X]
  {L : X → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, ContinuousSMul ℂ (L x)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealZeroCount : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

variable [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]
  {D : (Π x : X, L x) → Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] L x}
  (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ X) D)
  {n : ℕ∞ω} [ENat.LEInfty n] (hDs : ContMDiffCovariantDerivativeOn ℂ n D univ)

/-- Chart data at a point `z` for the zero count: a centre `c` whose preferred chart and
trivialization contain `z`, and an open set `Ω ∋ φ_c z` on which the reading of `s` is `C¹` and
satisfies `‖\bar∂ f‖ ≤ C ‖f‖`. -/
private structure ChartData (s : Π x, L x) (z : X) where
  /-- The centre of the preferred chart and trivialization. -/
  c : X
  /-- The open set of the chart target on which the inequality holds. -/
  Ω : Set ℂ
  /-- The constant of the Cauchy–Riemann inequality. -/
  C : ℝ
  mem_source : z ∈ (chartAt ℂ c).source
  mem_baseSet : z ∈ (trivializationAt ℂ L c).baseSet
  isOpen : IsOpen Ω
  mem : chartAt ℂ c z ∈ Ω
  contDiffOn : ContDiffOn ℝ 1 (preferredChartReading ℂ ℂ s c) Ω
  norm_le : ∀ y ∈ Ω, ‖conjWirtingerDeriv (preferredChartReading ℂ ℂ s c) y‖ ≤
    C * ‖preferredChartReading ℂ ℂ s c y‖

include hD hDs in
/-- Around every point, a `C¹` section in the kernel has chart data for the zero count. -/
private theorem nonempty_chartData [CompactSpace X] {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) : Nonempty (∀ z, ChartData s z) := by
  obtain ⟨A⟩ := FiniteBundleAtlas.nonempty (E := ℂ) (M := X) (F := ℂ) (V := L)
  choose i hi using A.exists_mem_dom
  choose C hC₀ hC using fun j ↦
    A.exists_norm_complexAntilinearPartL_fderiv_coord_le hD hDs j hs hs0
  refine ⟨fun z ↦ ⟨A.center (i z), A.image (i z), C (i z), A.dom_subset_chart_source _ (hi z),
    A.dom_subset_baseSet _ (hi z), (A.image _).isOpen, A.mem_image.2 ⟨z, hi z, rfl⟩, ?_, ?_⟩⟩
  · rw [A.preferredChartReading_center]
    -- The reading of `s` is `C¹` on the chart image.
    exact A.contDiffOn_coord_image hs (i z)
  · rw [A.preferredChartReading_center]
    -- On `ℂ`, `\bar∂` is the complex antilinear part of the derivative.
    exact fun y hy ↦ ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (hC₀ _) (norm_nonneg _)) fun v ↦ by
        rw [conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
        exact ((ContinuousLinearMap.le_opNorm _ v).trans (by gcongr; exact hC (i z) y hy))

variable [CompactSpace X]

include hD hDs in
/-- **The zeros of a nonzero section in the kernel are finite in number.** On a compact connected
Riemann surface, a `C¹` section of a complex line bundle in the kernel of a `C^n` real
Cauchy–Riemann operator, not identically zero, has finitely many zeros. -/
theorem finite_setOf_eq_zero [ConnectedSpace X] {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) (hne : ∃ x, s x ≠ 0) : {x | s x = 0}.Finite := by
  obtain ⟨d⟩ := nonempty_chartData hD hDs hs hs0
  exact finite_setOf_section_eq_zero_of_norm_conjWirtingerDeriv_le (fun z ↦ chartAt ℂ (d z).c)
    (fun z ↦ trivializationAt ℂ L (d z).c) (fun z ↦ (d z).mem_source) (fun z ↦ (d z).mem_baseSet)
    (fun z ↦ (d z).Ω) (fun z ↦ (d z).isOpen) (fun z ↦ (d z).mem) (fun z ↦ (d z).contDiffOn)
    (fun z _ ↦ (d z).C) (fun z _ _ ↦ ⟨(d z).C, Eventually.of_forall fun _ ↦ le_rfl⟩)
    (fun z ↦ (d z).norm_le) hne

include hD hDs in
/-- **The zero count.** On a compact Riemann surface, a `C¹` section of a complex line bundle `L`
in the kernel of a `C^n` real Cauchy–Riemann operator, with finitely many zeros, has at most
`c₁(L)[X]` zeros: the Euler class of `L` with its complex orientation, evaluated on the
fundamental class of `X`. -/
theorem ncard_le_evalFundamentalClass_complexEulerClass {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) (hZ : {x | s x = 0}.Finite) :
    ({x | s x = 0}.ncard : ℤ) ≤
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down := by
  obtain ⟨d⟩ := nonempty_chartData hD hDs hs hs0
  rw [complexEulerClass_def]
  exact
    VectorBundleOrientation.ncard_le_evalFundamentalClass_eulerClass_of_norm_conjWirtingerDeriv_le
    _ Complex.finrank_real_complex _ hs.continuous (fun z ↦ chartAt ℂ (d z).c)
    (fun z ↦ trivializationAt ℂ L (d z).c) (fun _ ↦ Complex.orientation)
    (fun z _ ↦ (d z).mem_source) (fun z ↦ (d z).Ω) (fun z _ ↦ (d z).C) hZ
    (fun z _ ↦ (d z).mem_baseSet)
    (fun z _ ↦ Eventually.of_forall fun _ hx ↦
      VectorBundleOrientation.mapOrientation_reindex_complex_eq_orientation _ _ hx)
    (fun z _ ↦ localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (n := 1) (d z).c) (d z).mem_source)
    (fun z _ ↦ (d z).isOpen) (fun z _ ↦ (d z).mem) (fun z _ ↦ (d z).contDiffOn)
    (fun z _ _ _ ↦ ⟨(d z).C, Eventually.of_forall fun _ ↦ le_rfl⟩) (fun z _ ↦ (d z).norm_le)

include hD hDs in
/-- **A section in the kernel vanishing at more than `c₁(L)[X]` points vanishes identically.** On
a compact connected Riemann surface, a `C¹` section of a complex line bundle `L` in the kernel of a
`C^n` real Cauchy–Riemann operator which vanishes on a finite set with more than `c₁(L)[X]` points
is zero. The condition is `c₁(L)[X] < S.ncard`, and `Set.ncard` is `0` for an infinite set. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard [ConnectedSpace X]
    {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) {S : Set X} (hS : ∀ x ∈ S, s x = 0)
    (hlt : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < S.ncard) :
    s = 0 := by
  -- A nonzero section has finitely many zeros, at most `c₁(L)[X]` of them, while it vanishes on
  -- `S`, which has more.
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hZ := finite_setOf_eq_zero hD hDs hs hs0 ⟨x, hx⟩
  have hle := ncard_le_evalFundamentalClass_complexEulerClass hD hDs hs hs0 hZ
  have hSZ : S.ncard ≤ {x | s x = 0}.ncard := ncard_le_ncard hS hZ
  omega

include hD hDs in
/-- **Vanishing of the kernel in negative degree.** On a compact connected Riemann surface, if the
first Chern number `c₁(L)[X]` of a complex line bundle `L` is negative, every `C¹` section of `L` in
the kernel of a `C^n` real Cauchy–Riemann operator is zero. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_neg [ConnectedSpace X]
    (hneg : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < 0)
    {s : Π x, L x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 1 fun x ↦ TotalSpace.mk' ℂ x (s x))
    (hs0 : D s = 0) : s = 0 :=
  eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard hD hDs hs hs0
    (S := ∅) (fun _ h ↦ h.elim) (by simpa using hneg)

end IsRealCauchyRiemannOperator

end TauCeti
