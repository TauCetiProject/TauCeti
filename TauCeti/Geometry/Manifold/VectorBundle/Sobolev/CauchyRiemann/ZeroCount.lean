/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.WeakCauchyRiemann

/-!
# The zero count for the kernel of a real Cauchy–Riemann operator with an `Lᵖ` zeroth-order term

Let `M` be a closed complex curve and `V → M` a complex vector bundle with a finite bundle atlas
`A`. Let `D₀` be a smooth real Cauchy–Riemann operator on `V` and `α` a zeroth-order term of class
`Lᵖ`, `p > 2`, and let `ξ ∈ W^{1,q}(M, V)`, `2 < q ≤ p`, lie in the kernel of the realization of
`D₀ + α` (`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL`). By Morrey's embedding `ξ` has a
continuous representative `s` (`TauCeti.SobolevSection.toSection`), which is in general not `C¹`,
since `α` is only `Lᵖ`.

**The inequality in a chart.** In chart `i` the realization reads
`\bar∂ uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}` for the weak derivative of the chart data `uᵢ`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevL_ae`), where the zeroth-order
term `Zᵢ` of `D₀` is bounded on the chart image by some `C`
(`TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`) and the chart data `αᵢ` of `α`
are `Lᵖ`. So the reading `sᵢ` of `s` has a weak derivative whose complex antilinear part satisfies
`‖\bar∂ sᵢ‖ ≤ (C + c ‖αᵢ‖) ‖sᵢ‖` almost everywhere on the chart image, where `c` is the norm of
the projection to the complex antilinear part, and `C + c ‖αᵢ‖` is locally `Lᵖ`
(`exists_hasWeakFDerivOn_coord_toSection_of_perturbedSobolevL_eq_zero` in the namespace
`TauCeti.IsRealCauchyRiemannOperator`).
On a line bundle, the value on `1` of this complex antilinear part is the weak conjugate Wirtinger
derivative of `sᵢ`.

**The zero count.** On a line bundle `L` over a compact Riemann surface `X` this is the hypothesis
of the zero count for sections solving a weak Cauchy–Riemann inequality
(`TauCeti.Topology.VectorBundle.Orientation.SectionIndex.WeakCauchyRiemann`), read in the charts of
`A`, which are preferred charts of `X` and preferred trivializations of `L`. As in the zero count
for `C¹` kernel elements of operators with continuous coefficients
(`TauCeti.IsRealCauchyRiemannOperator.ncard_le_evalFundamentalClass_complexEulerClass`), the
holomorphic charts and the complex-linear trivializations carry the complex orientations of `X`
and `L` to that of `ℂ`. So if `X` is connected (`[ConnectedSpace X]`) and `s` is not identically
zero, it has finitely many zeros; if it has finitely many zeros, it has at most `c₁(L)[X]` of them;
and if `X` is connected and `c₁(L)[X] < 0`, the kernel is zero.

Kernel elements of the realization of a smooth operator are smooth
(`TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`), so for `α = 0` the
`C¹` zero count already applies; this file is about rough `α`.

## Main results

In the namespace `TauCeti.IsRealCauchyRiemannOperator`:

* `exists_hasWeakFDerivOn_coord_toSection_of_perturbedSobolevL_eq_zero`: in every chart, a kernel
  element solves a weak Cauchy–Riemann inequality with an `Lᵖ_loc` bound.
* `finite_setOf_toSection_eq_zero_of_perturbedSobolevL_eq_zero`: on a connected `X`, a nonzero
  kernel element on a line bundle has finitely many zeros.
* `ncard_le_evalFundamentalClass_complexEulerClass_of_perturbedSobolevL_eq_zero`: a kernel
  element with finitely many zeros has at most `c₁(L)[X]` of them.
* `eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard_of_perturbedSobolevL_eq_zero` and
  `eq_zero_of_evalFundamentalClass_complexEulerClass_neg_of_perturbedSobolevL_eq_zero`: a kernel
  element vanishing at more than `c₁(L)[X]` points is zero, and the kernel is zero if
  `c₁(L)[X] < 0`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52 (2012), Definition C.1.5, Theorem C.1.10 (iii) and its proof
  (p. 603).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set Filter Topology TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

section Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannZeroCount : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V) [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

omit [T2Space M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- For `q > 2`, the elements of `W^{1,q}` have continuous representatives. -/
private theorem hasContinuousRepresentatives (hq : 2 < q) :
    SobolevSection.HasContinuousRepresentatives A volume q 1 :=
  .of_two_lt_mul (by rw [Nat.cast_one, one_mul]; exact_mod_cast hq)

include hD hDs in
/-- **A kernel element solves a weak Cauchy–Riemann inequality in every chart.** Let `D₀` be a
smooth real Cauchy–Riemann operator, `α` an `Lᵖ` zeroth-order term, `p > 2`, and `ξ ∈ W^{1,q}`,
`2 < q ≤ p`, with `(D₀ + α) ξ = 0`. In chart `i`, the reading `sᵢ` of the continuous
representative of `ξ` has a weak derivative `Du` on the chart image whose complex antilinear part
satisfies `‖\bar∂ sᵢ‖ ≤ g ‖sᵢ‖` almost everywhere there, for some `g ∈ Lᵖ_loc` of the chart image:
`g = C + c ‖αᵢ‖`, where `C` bounds the zeroth-order term `Zᵢ` of `D₀` on the chart image, `αᵢ` are
the chart data of `α` and `c` is the norm of the projection to the complex antilinear part. -/
theorem exists_hasWeakFDerivOn_coord_toSection_of_perturbedSobolevL_eq_zero
    (hp : 2 < p) (hq : 2 < q) (hqp : q ≤ p)
    (α : SobolevSection
      (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0)
    {ξ : SobolevSection A volume q 1} (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0)
    (i : Fin A.n) :
    ∃ (Du : ℂ → ℂ →L[ℝ] F) (g : ℂ → ℝ),
      HasWeakFDerivOn volume (A.image i) (A.coord i (SobolevSection.toSection ξ)) Du ∧
      MemLpLoc p (A.image i) g ∧ ∀ᵐ y ∂volume.restrict (A.image i),
        ‖complexAntilinearPartL (Du y)‖ ≤ g y * ‖A.coord i (SobolevSection.toSection ξ) y‖ := by
  have hrep := hasContinuousRepresentatives A hq
  have hae := SobolevSection.chartValueL_ae_eq_coord_toSection hrep ξ i
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL volume q i ξ
  -- The chart data of `α`, an `Lᵖ` function on the chart image.
  set a := (A.hom (𝕜 := ℝ)
    (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL volume p 0 i α
  have ha : MemLp (a : ℂ → F →L[ℝ] ℂ →L[ℝ] F) p (volume.restrict (A.image i)) :=
    (Lp.memLp a).mono_measure (Measure.restrict_mono (congrArg SetLike.coe
      (FiniteBundleAtlas.image_hom (A := A) (𝕜 := ℝ)
        (h := (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) i)).ge le_rfl)
  obtain ⟨C, hC⟩ := A.exists_norm_chartZeroOrder_apply_le hD hDs i
  set c₀ := ‖complexAntilinearPartL (E := ℂ) (F := F)‖
  have hg : MemLpLoc p (A.image i) fun y ↦ C + c₀ * ‖a y‖ := by
    simpa only [Pi.add_def] using (memLpLoc_const C).add (ha.norm.const_mul c₀).memLpLoc
  refine ⟨_, _, hDu.congr_ae hae, hg, ?_⟩
  -- The chart formula, for the kernel element: `\bar∂ uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1} = 0`.
  have hchart := hD.chartValueL_perturbedSobolevL_ae A hDs volume hp hqp α ξ hDu
  rw [hξ] at hchart
  filter_upwards [hchart,
    chartValueL_zero_zeroOneSobolevSections_ae (μ := volume) (p := q) (k := 0) i, hae,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h₁ h₂ h₃ hy
  have h := h₁.symm.trans h₂
  rw [h₃, Pi.zero_apply, add_assoc, add_eq_zero_iff_eq_neg] at h
  rw [h, norm_neg]
  set c := A.coord i (SobolevSection.toSection ξ) y
  calc _ ≤ ‖A.chartZeroOrder D i y c‖ + ‖complexAntilinearPartL (a y c)‖ := norm_add_le _ _
    _ ≤ C * ‖c‖ + c₀ * (‖a y‖ * ‖c‖) := by
        gcongr
        · exact hC y (subset_closure hy) c
        · exact ((complexAntilinearPartL (E := ℂ) (F := F)).le_opNorm (a y c)).trans
            (by gcongr; exact (a y).le_opNorm c)
    _ = _ := by ring

end Chart

section LineBundle

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X] [T2Space X]
  {L : X → Type} [TopologicalSpace (TotalSpace ℂ L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealWeakZeroCount : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

variable (A : FiniteBundleAtlas ℂ X ℂ L) [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]
  {D : (Π x : X, L x) → Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] L x}
  (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ X) D)
  (hDs : ContMDiffCovariantDerivativeOn ℂ ∞ D univ)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 2 < p) (hq : 2 < q)
  (hqp : q ≤ p)
  (α : SobolevSection
    (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0)
  {ξ : SobolevSection A volume q 1}

include hD hDs hq in
/-- In every chart of `A`, the reading of the continuous representative of a kernel element is
continuous, with a weak conjugate Wirtinger derivative bounded by an `Lᵖ_loc` multiple of it. -/
private theorem exists_weakChartData (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0) :
    ∃ (g : Fin A.n → ℂ → ℝ) (G : Fin A.n → ℂ → ℂ), ∀ j,
      ContinuousOn (preferredChartReading ℂ ℂ ξ.toSection (A.center j)) (A.image j) ∧
      MemLpLoc p (A.image j) (g j) ∧
      HasWeakConjWirtingerDerivOn volume (A.image j)
        (preferredChartReading ℂ ℂ ξ.toSection (A.center j)) (G j) ∧
      ∀ᵐ y ∂volume.restrict (A.image j), ‖G j y‖ ≤
        g j y * ‖preferredChartReading ℂ ℂ ξ.toSection (A.center j) y‖ := by
  have hrep := hasContinuousRepresentatives A hq
  simp only [A.preferredChartReading_center]
  choose Du g hDu hg hle using fun j ↦
    exists_hasWeakFDerivOn_coord_toSection_of_perturbedSobolevL_eq_zero A hD hDs hp hq hqp α hξ j
  refine ⟨g, fun j y ↦ (2 : ℂ)⁻¹ • (Du j y 1 + Complex.I • Du j y Complex.I), fun j ↦
    ⟨A.continuousOn_coord (SobolevSection.continuous_toSection hrep ξ) j, hg j,
      (hDu j).hasWeakConjWirtingerDerivOn, ?_⟩⟩
  filter_upwards [hle j] with y hy
  -- On `ℂ`, the weak conjugate Wirtinger derivative is the value on `1` of `\bar∂`.
  refine le_trans ?_ hy
  rw [show (2 : ℂ)⁻¹ • (Du j y 1 + Complex.I • Du j y Complex.I) =
      complexAntilinearPartL (Du j y) 1 by
    simp only [ContinuousLinearMap.complexAntilinearPartL_apply_apply, smul_eq_mul, mul_one,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]]
  simpa using (complexAntilinearPartL (Du j y)).le_opNorm 1

include hD hDs hq in
/-- **The zeros of a nonzero kernel element are finite in number.** On a connected compact Riemann
surface `X`, let `ξ ∈ W^{1,q}(X, L)`, `2 < q ≤ p`, be a nonzero element of the kernel of the
realization of `D₀ + α`, for a smooth real Cauchy–Riemann operator `D₀` on a complex line bundle
`L` and an `Lᵖ` zeroth-order term `α`, `p > 2`. Then the continuous representative of `ξ` has
finitely many zeros. -/
theorem finite_setOf_toSection_eq_zero_of_perturbedSobolevL_eq_zero [ConnectedSpace X]
    (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0) (hne : ξ ≠ 0) :
    {x | SobolevSection.toSection ξ x = 0}.Finite := by
  have := A.compactSpace
  obtain ⟨g, G, h⟩ := exists_weakChartData A hD hDs hp hq hqp α hξ
  choose i hi using A.exists_mem_dom
  exact finite_setOf_section_eq_zero_of_hasWeakConjWirtingerDerivOn_of_norm_le
    (fun z ↦ chartAt ℂ (A.center (i z))) (fun z ↦ trivializationAt ℂ L (A.center (i z)))
    (fun z ↦ A.dom_subset_chart_source _ (hi z)) (fun z ↦ A.dom_subset_baseSet _ (hi z))
    (by exact_mod_cast hp) (fun z ↦ A.image (i z)) (fun z ↦ A.mem_image.2 ⟨z, hi z, rfl⟩)
    (fun z ↦ g (i z)) (fun z ↦ (h (i z)).2.1) (fun z ↦ G (i z)) (fun z ↦ (h (i z)).1)
    (fun z ↦ (h (i z)).2.2.1) (fun z ↦ (h (i z)).2.2.2)
    (Function.ne_iff.1 ((SobolevSection.toSection_eq_zero_iff
      (hasContinuousRepresentatives A hq)).not.2 hne))

open VectorBundleOrientation in
include hD hDs hq in
/-- **The zero count.** On a compact Riemann surface `X`, let `ξ ∈ W^{1,q}(X, L)`, `2 < q ≤ p`,
lie in the kernel of the realization of `D₀ + α`, for a smooth real Cauchy–Riemann operator `D₀`
on a complex line bundle `L` and an `Lᵖ` zeroth-order term `α`, `p > 2`. If the continuous
representative of `ξ` has finitely many zeros, it has at most `c₁(L)[X]` of them: the Euler class
of `L` with its complex orientation, evaluated on the fundamental class of `X`. -/
theorem ncard_le_evalFundamentalClass_complexEulerClass_of_perturbedSobolevL_eq_zero
    [CompactSpace X] (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0)
    (hZ : {x | SobolevSection.toSection ξ x = 0}.Finite) :
    ({x | SobolevSection.toSection ξ x = 0}.ncard : ℤ) ≤
      ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down := by
  have hrep := hasContinuousRepresentatives A hq
  obtain ⟨g, G, h⟩ := exists_weakChartData A hD hDs hp hq hqp α hξ
  choose i hi using A.exists_mem_dom
  rw [complexEulerClass_def]
  exact ncard_le_evalFundamentalClass_eulerClass_of_hasWeakConjWirtingerDerivOn_of_norm_le
    _ Complex.finrank_real_complex _ (SobolevSection.continuous_toSection hrep ξ)
    (fun z ↦ chartAt ℂ (A.center (i z))) (fun z ↦ trivializationAt ℂ L (A.center (i z)))
    (fun _ ↦ Complex.orientation) (fun z _ ↦ A.dom_subset_chart_source _ (hi z))
    (fun z ↦ A.image (i z)) (fun z ↦ g (i z)) (fun z ↦ G (i z)) hZ
    (fun z _ ↦ A.dom_subset_baseSet _ (hi z))
    (fun z _ ↦ Eventually.of_forall fun _ hx ↦
      VectorBundleOrientation.mapOrientation_reindex_complex_eq_orientation _ _ hx)
    (fun z _ ↦ localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (n := 1) (A.center (i z)))
      (A.dom_subset_chart_source _ (hi z)))
    (by exact_mod_cast hp) (fun z _ ↦ A.mem_image.2 ⟨z, hi z, rfl⟩) (fun z _ ↦ (h (i z)).2.1)
    (fun z _ ↦ (h (i z)).1) (fun z _ ↦ (h (i z)).2.2.1) (fun z _ ↦ (h (i z)).2.2.2)

include hD hDs hq in
/-- **A kernel element vanishing at more than `c₁(L)[X]` points is zero.** On a connected compact
Riemann surface `X`, let `ξ ∈ W^{1,q}(X, L)`, `2 < q ≤ p`, lie in the kernel of the realization of
`D₀ + α`, for a smooth real Cauchy–Riemann operator `D₀` on a complex line bundle `L` and an `Lᵖ`
zeroth-order term `α`, `p > 2`. If the continuous representative of `ξ` vanishes on a set `S`
with more than `c₁(L)[X]` points, then `ξ = 0`. The condition is `c₁(L)[X] < S.ncard`, and
`Set.ncard` is `0` for an infinite set. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard_of_perturbedSobolevL_eq_zero
    [CompactSpace X] [ConnectedSpace X] (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0)
    {S : Set X}
    (hS : ∀ x ∈ S, SobolevSection.toSection ξ x = 0)
    (hlt : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < S.ncard) :
    ξ = 0 := by
  -- A nonzero kernel element has finitely many zeros, at most `c₁(L)[X]` of them, while its
  -- continuous representative vanishes on `S`, which has more.
  by_contra hne
  have hZ :=
    finite_setOf_toSection_eq_zero_of_perturbedSobolevL_eq_zero A hD hDs hp hq hqp α hξ hne
  have hle :=
    ncard_le_evalFundamentalClass_complexEulerClass_of_perturbedSobolevL_eq_zero A hD hDs hp hq hqp
      α hξ hZ
  have hSZ : S.ncard ≤ {x | SobolevSection.toSection ξ x = 0}.ncard := ncard_le_ncard hS hZ
  omega

include hD hDs hq in
/-- **Vanishing of the kernel in negative degree.** On a connected compact Riemann surface `X`, if
the first Chern number `c₁(L)[X]` of a complex line bundle `L` is negative, every element `ξ` of
`W^{1,q}(X, L)`, `2 < q ≤ p`, in the kernel of the realization of `D₀ + α` is zero, for every
smooth real Cauchy–Riemann operator `D₀` on `L` and every `Lᵖ` zeroth-order term `α`, `p > 2`. -/
theorem eq_zero_of_evalFundamentalClass_complexEulerClass_neg_of_perturbedSobolevL_eq_zero
    [CompactSpace X] [ConnectedSpace X]
    (hneg : ((complexHomologicalOrientation X).evalFundamentalClass Complex.finrank_real_complex
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id X)
        (complexEulerClass ℂ L (r := 0) (finrank_self ℂ))).down < 0)
    (hξ : hD.perturbedSobolevL A hDs volume hp hqp α ξ = 0) : ξ = 0 :=
  eq_zero_of_evalFundamentalClass_complexEulerClass_lt_ncard_of_perturbedSobolevL_eq_zero A hD hDs
    hp hq hqp α hξ (S := ∅) (fun _ h ↦ h.elim) (by simp at hneg ⊢; omega)

end LineBundle

end IsRealCauchyRiemannOperator

end TauCeti
