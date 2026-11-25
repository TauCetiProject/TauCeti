/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Unique continuation for real Cauchy–Riemann operators on a Riemann surface

Let `M` be a compact connected complex curve, `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, and `D` a real Cauchy–Riemann
operator on `V` with continuous coefficients. A `C¹` section `s` with `D s = 0` that vanishes on a
nonempty open set vanishes identically
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_eqOn_zero`), and so does one whose reading in a
chart of a finite bundle atlas `A` of `V` vanishes to infinite order at a point
(`TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_forall_isBigO`).

In chart `i`, the reading `u` of `s` solves `∂ₛu + i ∂ₜu + 2 Zᵢ(u)(1) = 0`, where `Zᵢ` is the
continuous zeroth-order term of `D` in chart `i`
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`).
This is a linear Cauchy–Riemann equation for the constant complex structure `i` on `F`, so by
the Carleman similarity principle `u` vanishes on every disc in the chart image on which it vanishes
near one point (`TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure`) or to infinite
order at one point (`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure`).
Hence the set of points near which `s` vanishes is open and closed in `M`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_eqOn_zero`: unique continuation from a nonempty
  open set.
* `TauCeti.IsRealCauchyRiemannOperator.eq_zero_of_forall_isBigO`: unique continuation from a zero
  of infinite order in a chart.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the similarity principle) and Theorem C.1.10 (iii).
-/

public section

noncomputable section

open Bundle Filter Metric Module Set
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F 0 D univ)
  {s : Π x, V x} (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) 1 (T% s)) (hs0 : D s = 0)

/-- The coefficient `2 Zᵢ(z)(·)(1)` of the equation of a reading in chart `i`. -/
private def coeff (i : Fin A.n) (z : ℂ) : F →L[ℝ] F :=
  ((2 : ℝ) • ContinuousLinearMap.compL ℝ F (ℂ →L[ℝ] F) F (ContinuousLinearMap.apply ℝ F 1))
    (A.chartZeroOrder D i z)

omit [T2Space M] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  [∀ x, Module ℂ (V x)] in
private theorem coeff_apply (i : Fin A.n) (z : ℂ) (v : F) :
    coeff A (D := D) i z v = (2 : ℝ) • A.chartZeroOrder D i z v 1 :=
  rfl

include hD hDs hs hs0 in
/-- **The equation in a chart.** On the image of chart `i`, the reading `u` of a `C¹` section in
the kernel of `D` is `C¹` and solves `∂ₛu + i ∂ₜu + 2 Zᵢ(u)(1) = 0`, with a continuous, hence
measurable and locally bounded, coefficient. -/
private theorem coord_equation (i : Fin A.n) :
    ContDiffOn ℝ 1 (A.coord i s) (A.image i) ∧
      MeasureTheory.AEStronglyMeasurable (coeff A (D := D) i)
        (MeasureTheory.volume.restrict (A.image i)) ∧
      (∀ z ∈ A.image i, ∃ K, ∀ᶠ w in 𝓝 z, ‖coeff A (D := D) i w‖ ≤ K) ∧
      ∀ z ∈ A.image i, fderiv ℝ (A.coord i s) z 1 +
        (ContinuousLinearMap.lsmul ℝ ℂ Complex.I : F →L[ℝ] F) (fderiv ℝ (A.coord i s) z Complex.I) +
          coeff A (D := D) i z (A.coord i s z) = 0 := by
  have : ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ) := .of_le (n := ∞) (mod_cast le_top)
  -- `contDiffOn_coord_image` is stated for `k : ℕ`, so the order `1` is cast.
  have hu : ContDiffOn ℝ 1 (A.coord i s) (A.image i) := by
    have : IsManifold 𝓘(ℝ, ℂ) ((1 : ℕ) : WithTop ℕ∞) M := .of_le (n := ∞) (mod_cast le_top)
    have : ContMDiffVectorBundle ((1 : ℕ) : WithTop ℕ∞) F V 𝓘(ℝ, ℂ) :=
      .of_le (n := ∞) (mod_cast le_top)
    exact_mod_cast A.contDiffOn_coord_image (k := 1) (by exact_mod_cast hs) i
  have hC : ContinuousOn (coeff A (D := D) i) (A.image i) :=
    (ContinuousLinearMap.continuous _).comp_continuousOn
      (A.contDiffOn_chartZeroOrder_image hD hDs i).continuousOn
  refine ⟨hu,
    hC.aestronglyMeasurable (A.image i).isOpen.measurableSet, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · exact ⟨‖coeff A (D := D) i w‖ + 1, ((hC.continuousAt
      ((A.image i).isOpen.mem_nhds hw)).norm.eventually (Iic_mem_nhds (lt_add_one _)))⟩
  · -- The chart formula for `D s = 0`, evaluated on `1` and doubled.
    have h := A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hw
      ((hs _).mdifferentiableAt one_ne_zero)
    rw [hs0, A.tangentHom.coord_zero i (by rwa [A.image_tangentHom])] at h
    -- On `1`: `0 = ½ (∂ₛu + i ∂ₜu) + Zᵢ(u)(1)`, since `∂bar L (1) = ½ (L 1 + i L i)`.
    have h1 := congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h
    simp only [add_apply, zero_apply, ContinuousLinearMap.complexAntilinearPartL_apply_apply,
      smul_eq_mul, mul_one] at h1
    rw [coeff_apply, ContinuousLinearMap.lsmul_apply]
    -- Doubling cancels the `½`.
    linear_combination (norm := module) -(2 : ℝ) • h1

omit [T2Space M] [IsManifold 𝓘(ℂ) ∞ M] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [∀ x, Module ℂ (V x)] in
/-- If the reading of `s` in chart `i` vanishes on a disc, then `s` vanishes at the points of `M`
read in chart `i` inside the disc. -/
private theorem eq_zero_of_coord_eq_zero {i : Fin A.n} {y : ℂ} {r : ℝ}
    (hu : EqOn (A.coord i s) 0 (ball y r)) :
    ∀ x ∈ A.dom i ∩ A.chart i ⁻¹' ball y r, s x = 0 := by
  intro x ⟨hx, hxb⟩
  have hxi : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
  have h := (A.coord_eq_zero_iff hxi).1 (hu hxb)
  rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hx)] at h

include hD hDs hs hs0 in
/-- If the reading of `s` in chart `i` vanishes near one point of a disc in the chart image, then
`s` vanishes on the points of `M` read in chart `i` inside the disc. -/
private theorem eqOn_zero_of_eventually_coord_eq_zero {i : Fin A.n} {y : ℂ} {r : ℝ}
    (hr : ball y r ⊆ A.image i) {z₀ : ℂ} (hz₀ : z₀ ∈ ball y r)
    (h₀ : ∀ᶠ z in 𝓝 z₀, A.coord i s z = 0) :
    ∀ x ∈ A.dom i ∩ A.chart i ⁻¹' ball y r, s x = 0 := by
  obtain ⟨hu, hCm, hCb, heq⟩ := coord_equation A hD hDs hs hs0 i
  obtain ⟨t, hts, hto, hzt⟩ := _root_.eventually_nhds_iff.1 h₀
  refine eq_zero_of_coord_eq_zero A (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure
    isOpen_ball isPreconnected_ball contDiffOn_const
    (fun _ _ ↦ ContinuousLinearMap.lsmul_I_mul_lsmul_I) (hu.mono hr) (hCm.mono_set hr)
    (fun z hz ↦ hCb z (hr hz)) (fun z hz ↦ heq z (hr hz))
    (hto.inter isOpen_ball) ⟨z₀, hzt, hz₀⟩ inter_subset_right fun z hz ↦ hts z hz.1)

include hD hDs hs hs0 in
/-- **Unique continuation.** On a compact connected complex curve, a `C¹` section of a smooth
complex vector bundle with finite-dimensional fibre, in the kernel of a real Cauchy–Riemann
operator with continuous coefficients, that vanishes on a nonempty open set vanishes identically. -/
theorem IsRealCauchyRiemannOperator.eq_zero_of_eqOn_zero [CompactSpace M] [ConnectedSpace M]
    {U : Set M} (hU : IsOpen U) (hUne : U.Nonempty) (hsU : ∀ x ∈ U, s x = 0) : s = 0 := by
  obtain ⟨A⟩ := FiniteBundleAtlas.nonempty (E := ℂ) (M := M) (F := F) (V := V)
  -- The set of points near which `s` vanishes is open, nonempty and closed.
  let Z : Set M := {x | ∀ᶠ y in 𝓝 x, s y = 0}
  have hZo : IsOpen Z := isOpen_setOfPred_eventually_nhds
  obtain ⟨x₀, hx₀⟩ := hUne
  have hZne : Z.Nonempty := ⟨x₀, eventually_of_mem (hU.mem_nhds hx₀) hsU⟩
  have hZc : IsClosed Z := isClosed_of_closure_subset fun x hx ↦ by
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (A.iUnion_dom ▸ mem_univ x)
    have hyi : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hxi, rfl⟩
    obtain ⟨r, hr, hri⟩ := isOpen_iff.1 (A.image i).isOpen _ hyi
    -- An open neighbourhood of `x` read in chart `i` inside a disc of the chart image.
    let N : Set M := A.dom i ∩ A.chart i ⁻¹' ball (A.chart i x) r
    have hNo : IsOpen N := A.isOpen_dom_inter_preimage i isOpen_ball
    have hxN : x ∈ N := ⟨hxi, mem_ball_self hr⟩
    obtain ⟨x', hx'N, hx'Z⟩ := mem_closure_iff.1 hx N hNo hxN
    -- The reading of `s` vanishes near the chart point of `x'`.
    have hz' : A.chart i x' ∈ A.image i := A.mem_image.2 ⟨x', hx'N.1, rfl⟩
    have hsymm : ContinuousAt (A.chart i).symm (A.chart i x') :=
      (A.continuousOn_chart_symm i).continuousAt ((A.image i).isOpen.mem_nhds hz')
    have hx' : (A.chart i).symm (A.chart i x') = x' :=
      (A.chart i).left_inv (A.dom_subset_chart_source i hx'N.1)
    have h₀ : ∀ᶠ z in 𝓝 (A.chart i x'), A.coord i s z = 0 := by
      filter_upwards [hsymm.eventually (hx' ▸ hx'Z),
        (A.image i).isOpen.mem_nhds hz'] with z hz hzi
      exact A.coord_eq_zero hzi hz
    exact eventually_of_mem (hNo.mem_nhds hxN)
      (eqOn_zero_of_eventually_coord_eq_zero A hD hDs hs hs0 hri hx'N.2 h₀)
  have hZu : Z = univ := IsClopen.eq_univ ⟨hZc, hZo⟩ hZne
  funext x
  exact (hZu ▸ mem_univ x : x ∈ Z).self_of_nhds

include hD hDs hs hs0 in
/-- **Unique continuation from a zero of infinite order.** On a compact connected complex curve with
a finite bundle atlas `A` of a smooth complex vector bundle `V`, a `C¹` section in the kernel of a
real Cauchy–Riemann operator with continuous coefficients, whose reading in a chart of `A`
vanishes to infinite order at a point of the chart domain, vanishes identically. -/
theorem IsRealCauchyRiemannOperator.eq_zero_of_forall_isBigO [ConnectedSpace M] {i : Fin A.n}
    {x₀ : M} (hx₀ : x₀ ∈ A.dom i)
    (h₀ : ∀ n : ℕ, A.coord i s =O[𝓝 (A.chart i x₀)] fun z ↦ (z - A.chart i x₀) ^ n) :
    s = 0 := by
  have hy : A.chart i x₀ ∈ A.image i := A.mem_image.2 ⟨x₀, hx₀, rfl⟩
  obtain ⟨r, hr, hri⟩ := isOpen_iff.1 (A.image i).isOpen _ hy
  obtain ⟨hu, hCm, hCb, heq⟩ := coord_equation A hD hDs hs hs0 i
  have hzero := eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure isOpen_ball
    isPreconnected_ball contDiffOn_const (fun _ _ ↦ ContinuousLinearMap.lsmul_I_mul_lsmul_I)
    (hu.mono hri)
    (hCm.mono_set hri) (fun z hz ↦ hCb z (hri hz)) (fun z hz ↦ heq z (hri hz)) (mem_ball_self hr)
    h₀
  have := A.compactSpace
  refine hD.eq_zero_of_eqOn_zero hDs hs hs0 (A.isOpen_dom_inter_preimage i isOpen_ball)
    ⟨x₀, hx₀, mem_ball_self hr⟩
    (eq_zero_of_coord_eq_zero A hzero)

end TauCeti
