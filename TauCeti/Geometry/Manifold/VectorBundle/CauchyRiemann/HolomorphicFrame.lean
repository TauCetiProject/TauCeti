/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Analysis.Complex.Wirtinger.Potential

/-!
# Holomorphic frames of complex linear Cauchy–Riemann operators

Let `D` be a complex linear real Cauchy–Riemann operator on a complex vector bundle `V` over a
complex manifold `M`, for the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold` of `M`. A *holomorphic frame* of `D` on a
set `U` is a smooth section of `V` which is nowhere zero on `U` and in the kernel of `D` on `U`.

On a complex line bundle over a complex curve, such an operator has holomorphic frames near every
point, by the similarity principle; two of them differ by nowhere-zero holomorphic functions, and
the kernel of `D` near a point consists of the holomorphic multiples of a holomorphic frame. So `D`
is a holomorphic structure on `V`, whose holomorphic sections are the kernel of `D`.

The frame near `x₀` is built from the frame `s` of the trivialization of `V` at `x₀` and the chart
at `x₀`. There `D s = (B dz̄) ⊗ s` for the coefficient `B = TauCeti.cauchyRiemannChartCoeff D x₀`,
assumed smooth near the chart point of `x₀`. A smooth solution `g` of `∂bar g = -B`
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`) gives the holomorphic frame
`exp (g ∘ φ) • s`, by the complex Leibniz rule.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.leibniz_complex`: the Leibniz rule
  `D (f • ξ) = f • D ξ + (∂bar f) ⊗ ξ` of a complex linear real Cauchy–Riemann operator for
  complex valued `f`.
* `TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff` and
  `TauCeti.IsRealCauchyRiemannOperator.forall_apply_smul_eq_zero_iff`: against a holomorphic
  frame `σ`, the section `f • σ` is in the kernel of `D` exactly when `f` is holomorphic.
* `TauCeti.IsRealCauchyRiemannOperator.exists_isHolomorphicFrameOn`: local holomorphic frames on a
  line bundle over a complex curve.
* `TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul`: on a line bundle, every
  section in the kernel of `D` is a holomorphic multiple of a holomorphic frame.
* `TauCeti.IsRealCauchyRiemannOperator.exists_mdifferentiableOn_eq_smul_of_isHolomorphicFrameOn`:
  two holomorphic frames differ by a nowhere-zero holomorphic function.

## Implementation notes

Only operators with smooth coefficients are treated: the coefficient
`TauCeti.cauchyRiemannChartCoeff D x₀` is assumed smooth near the chart point of `x₀`. Assembling
the holomorphic frames into a holomorphic vector bundle structure on `V` is not done here.

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
/-- A *holomorphic frame* of an operator `D` on a set `U`: a smooth section of `V` which is nowhere
zero on `U` and is in the kernel of `D` at every point of `U`. -/
structure IsHolomorphicFrameOn (D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x)
    (σ : Π x : M, V x) (U : Set M) : Prop where
  contMDiffOn : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% σ) U
  ne_zero : ∀ x ∈ U, σ x ≠ 0
  apply_eq_zero : ∀ x ∈ U, D σ x = 0

theorem IsHolomorphicFrameOn.mono {σ : Π x : M, V x} {U U' : Set M}
    (hσ : IsHolomorphicFrameOn F D σ U) (h : U' ⊆ U) : IsHolomorphicFrameOn F D σ U' where
  contMDiffOn := hσ.contMDiffOn.mono h
  ne_zero x hx := hσ.ne_zero x (h hx)
  apply_eq_zero x hx := hσ.apply_eq_zero x (h hx)

theorem IsHolomorphicFrameOn.mdifferentiableAt {σ : Π x : M, V x} {U : Set M}
    (hσ : IsHolomorphicFrameOn F D σ U) (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    MDiffAt (T% σ) x :=
  (hσ.contMDiffOn.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)

variable [∀ x, Module ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [IsManifold I ∞ M] {j : SmoothAlmostComplexStructure I M}

open SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

/-- Locality: at `x`, a real Cauchy–Riemann operator only sees the germ of a section
differentiable at `x`. -/
private theorem apply_eq_of_eventuallyEq_aux [VectorBundle ℝ F V]
    (hD : IsRealCauchyRiemannOperator F j D)
    {σ σ' : Π x : M, V x} {x : M} (hσ' : MDiffAt (T% σ') x) (h : ∀ᶠ y in 𝓝 x, σ y = σ' y) :
    D σ x = D σ' x := by
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp h
  classical
  -- `τ = σ - σ'` vanishes on `U`; the indicator `g` of `Uᶜ` is `0` near `x` and `g • τ = τ`.
  set τ : Π x : M, V x := σ - σ'
  let g : M → ℝ := Set.indicator Uᶜ 1
  have hg0 : g =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hUo.mem_nhds hxU] with y hy
    simp [g, hy]
  have hσ : MDiffAt (T% σ) x :=
    hσ'.congr_of_eventuallyEq (h.mono fun y hy ↦ by simp [hy])
  have hτ : MDiffAt (T% τ) x := by
    simpa [τ, sub_eq_add_neg] using
      mdifferentiableAt_add_section hσ (mdifferentiableAt_neg_section hσ')
  have hgτ : g • τ = τ := by
    ext y
    by_cases hy : y ∈ U
    · simp [τ, hU y hy]
    · simp [g, hy]
  have hgx : MDiffAt g x := mdifferentiableAt_const.congr_of_eventuallyEq hg0
  have hτx : τ x = 0 := by simp [τ, hU x hxU]
  have hDτ : D τ x = 0 := by
    have hl := hD.leibniz hτ hgx
    rw [hgτ] at hl
    have : j.dbarSMulRight g τ x = 0 := by
      ext v
      rw [dbarSMulRight_apply, hτx]
      simp only [smul_zero, add_zero, zero_apply]
    rw [this, add_zero, show g x = 0 from hg0.self_of_nhds, zero_smul] at hl
    exact hl
  have hστ : σ = σ' + τ := by
    ext y
    simp [τ]
  rw [hστ, hD.add hσ' hτ, hDτ, add_zero]

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℂ F V] [VectorBundle ℝ F V]

/-- **Complex Leibniz rule.** A complex linear real Cauchy–Riemann operator satisfies
`D (f • ξ) = f • D ξ + (∂bar f) ⊗ ξ` for complex valued `f`, where `(∂bar f) ⊗ ξ` is the
`(0,1)`-part of `df ⊗ ξ`. -/
theorem leibniz_complex (hD : IsRealCauchyRiemannOperator F j D)
    (hDℂ : IsComplexLinearOperator F D) {σ : Π x : M, V x} {f : M → ℂ} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDifferentiableAt I 𝓘(ℝ, ℂ) f x) :
    D (f • σ) x = f x • D σ x + j.zeroOnePart ((d% f x).smulRight (σ x)) := by
  set a : M → ℝ := fun y ↦ (f y).re
  set b : M → ℝ := fun y ↦ (f y).im
  have ha : MDiffAt a x := Complex.reCLM.differentiableAt.comp_mdifferentiableAt hf
  have hb : MDiffAt b x := Complex.imCLM.differentiableAt.comp_mdifferentiableAt hf
  have hda (v : TangentSpace I x) : d% a x v = (d% f x v).re := by
    have h := (Complex.reCLM.hasFDerivAt.hasMFDerivAt).comp x hf.hasMFDerivAt
    simp only [mvfderiv_apply_eq_mfderiv_apply]
    rw [show a = Complex.reCLM ∘ f from rfl, h.mfderiv]
    rfl
  have hdb (v : TangentSpace I x) : d% b x v = (d% f x v).im := by
    have h := (Complex.imCLM.hasFDerivAt.hasMFDerivAt).comp x hf.hasMFDerivAt
    simp only [mvfderiv_apply_eq_mfderiv_apply]
    rw [show b = Complex.imCLM ∘ f from rfl, h.mfderiv]
    rfl
  have hIσ := hσ.const_smul_section Complex.I
  have hsplit : f • σ = a • σ + b • (Complex.I • σ) := by
    ext y
    simp only [Pi.smul_apply', Pi.add_apply, Pi.smul_apply, a, b]
    conv_lhs => rw [← Complex.re_add_im (f y)]
    rw [add_smul, mul_smul, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ) (f y).im]
    rfl
  rw [hsplit, hD.add (ha.smul_section hσ) (hb.smul_section hIσ), hD.leibniz hσ ha,
    hD.leibniz hIσ hb, hDℂ.complex_I_smul hσ, dbarSMulRight_complex_I_smul]
  ext v
  simp only [add_apply, smul_apply, dbarSMulRight_apply, zeroOnePart_apply,
    ContinuousLinearMap.smulRight_apply, hda, hdb]
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℝ, d% f x v = p + q * Complex.I :=
    ⟨_, _, (Complex.re_add_im _).symm⟩
  obtain ⟨p', q', hpq'⟩ : ∃ p q : ℝ, d% f x (j.toEndomorphism x v) = p + q * Complex.I :=
    ⟨_, _, (Complex.re_add_im _).symm⟩
  conv_rhs => rw [← Complex.re_add_im (f x)]
  simp only [hpq, hpq', Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := V x)]
  simp only [a, b, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  module

end IsRealCauchyRiemannOperator

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

/-- For a nonzero vector `w`, the `(0,1)`-part of `η ⊗ w` vanishes exactly when the complex valued
one-form `η` is complex linear for `j`. -/
private theorem zeroOnePart_smulRight_eq_zero_iff {x : M} (η : TangentSpace I x →L[ℝ] ℂ)
    {w : V x} (hw : w ≠ 0) :
    j.zeroOnePart (η.smulRight w) = 0 ↔ ∀ v, η (j x v) = Complex.I * η v := by
  have key (v : TangentSpace I x) :
      j.zeroOnePart (η.smulRight w) v = ((2⁻¹ : ℂ) * (η v + Complex.I * η (j x v))) • w := by
    rw [zeroOnePart_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  constructor
  · intro h v
    have hv := congrArg (· v) h
    simp only [key, zero_apply, smul_eq_zero, hw, or_false, mul_eq_zero, inv_eq_zero,
      two_ne_zero, false_or] at hv
    linear_combination (-Complex.I) * hv + η (j x v) * Complex.I_mul_I
  · intro h
    ext v
    rw [key, h, zero_apply]
    simp only [← mul_assoc, Complex.I_mul_I]
    simp

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

/-- A real differentiable complex valued function on a complex manifold is holomorphic at a point
exactly when its real differential there is complex linear. -/
private theorem mdifferentiableAt_complex_iff {f : M → ℂ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f x) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f x ↔
      ∀ v : TangentSpace 𝓘(ℝ, E) x,
        mvfderiv 𝓘(ℝ, E) f x (ofComplexManifold E M x v) = Complex.I * mvfderiv 𝓘(ℝ, E) f x v := by
  rw [← isPseudoholomorphicAt_ofComplexManifold_iff (E' := ℂ) (N := ℂ),
    isPseudoholomorphicAt_iff_mfderiv]
  simp only [hf, true_and]
  refine forall_congr' fun v ↦ ?_
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact Iff.of_eq (congrArg (_ = ·) (ofComplexManifold_apply (E := ℂ) (f x) _))

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
    zeroOnePart_smulRight_eq_zero_iff _ hσ0, mdifferentiableAt_complex_iff hf]

/-- **Holomorphic sections in a holomorphic frame.** If `σ` is a holomorphic frame of a complex
linear real Cauchy–Riemann operator `D` on an open set `U` of a complex manifold, a section `f • σ`
with `f` real differentiable on `U` is in the kernel of `D` on `U` exactly when `f` is holomorphic
on `U`. -/
theorem forall_apply_smul_eq_zero_iff {σ : Π x : M, V x} {U : Set M}
    (hσ : IsHolomorphicFrameOn F D σ U) (hU : IsOpen U) {f : M → ℂ}
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

omit [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℝ ℂ V] in
/-- In a line bundle, the ratio of two vectors read in a trivialization. -/
private def trivRatio (e : Trivialization ℂ (π ℂ V)) [e.IsLinear ℂ] {x : M} (v w : V x) : ℂ :=
  e.continuousLinearMapAt ℂ x w / e.continuousLinearMapAt ℂ x v

omit [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ ℂ V]
  [VectorBundle ℝ ℂ V] in
private theorem eq_trivRatio_smul (e : Trivialization ℂ (π ℂ V)) [e.IsLinear ℂ] {x : M}
    (hx : x ∈ e.baseSet) {v : V x} (hv : v ≠ 0) (w : V x) :
    w = trivRatio e v w • v := by
  have hinj : Function.Injective (e.continuousLinearMapAt ℂ x) := fun a b hab ↦ by
    rw [← e.symmL_continuousLinearMapAt (R := ℂ) hx a, hab,
      e.symmL_continuousLinearMapAt (R := ℂ) hx b]
  have hv' : e.continuousLinearMapAt ℂ x v ≠ 0 := fun h ↦ hv (hinj (h.trans (map_zero _).symm))
  apply hinj
  rw [map_smul, trivRatio, smul_eq_mul, div_mul_cancel₀ _ hv']

omit [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℂ ℂ V]
  [VectorBundle ℝ ℂ V] in
private theorem trivRatio_eq (e : Trivialization ℂ (π ℂ V)) [e.IsLinear ℂ] {x : M}
    (hx : x ∈ e.baseSet) {v : V x} (hv : v ≠ 0) {w : V x} {c : ℂ} (hw : w = c • v) :
    trivRatio e v w = c := by
  subst hw
  exact (smul_left_injective ℂ hv (eq_trivRatio_smul e hx hv (c • v))).symm

namespace IsRealCauchyRiemannOperator

variable (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold E M) D)
  (hDℂ : IsComplexLinearOperator ℂ D)
include hD hDℂ

/-- **The kernel is the space of holomorphic sections.** If `σ` is a holomorphic frame of a complex
linear real Cauchy–Riemann operator on a line bundle over a complex manifold, on an open set `U`,
every section `τ` differentiable on `U` and in the kernel of `D` on `U` is `h • σ` on `U` for a
function `h` holomorphic on `U`. -/
theorem exists_mdifferentiableOn_eq_smul {σ τ : Π x : M, V x} {U : Set M}
    (hσ : IsHolomorphicFrameOn ℂ D σ U) (hU : IsOpen U)
    (hτ : ∀ x ∈ U, MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℂ)) (T% τ) x)
    (hDτ : ∀ x ∈ U, D τ x = 0) :
    ∃ h : M → ℂ, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h U ∧ ∀ x ∈ U, τ x = h x • σ x := by
  let h : M → ℂ := fun x ↦ trivRatio (trivializationAt ℂ V x) (σ x) (τ x)
  have hτh : ∀ x ∈ U, τ x = h x • σ x := fun x hx ↦
    eq_trivRatio_smul _ (mem_baseSet_trivializationAt ℂ V x) (hσ.ne_zero x hx) _
  refine ⟨h, fun x₀ hx₀ ↦ ?_, hτh⟩
  set e₀ := trivializationAt ℂ V x₀
  have hx₀e : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt ℂ V x₀
  -- Near `x₀`, `h` is the ratio of the coordinates of `τ` and `σ` in the trivialization at `x₀`.
  have hloc : h =ᶠ[𝓝 x₀] fun x ↦ (e₀ ⟨x, τ x⟩).2 / (e₀ ⟨x, σ x⟩).2 := by
    filter_upwards [hU.mem_nhds hx₀, e₀.open_baseSet.mem_nhds hx₀e] with x hx hxe
    rw [← e₀.continuousLinearMapAt_apply_of_mem (R := ℂ) hxe,
      ← e₀.continuousLinearMapAt_apply_of_mem (R := ℂ) hxe]
    exact (trivRatio_eq e₀ hxe (hσ.ne_zero x hx) (hτh x hx)).symm
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
    rw [apply_eq_of_eventuallyEq_aux (σ := h • σ) hD (hτ x₀ hx₀)
      (Filter.mem_of_superset (hU.mem_nhds hx₀) fun x hx ↦ (hτh x hx).symm)]
    exact hDτ x₀ hx₀
  exact ((hD.apply_smul_eq_zero_iff hDℂ (hσ.mdifferentiableAt hU hx₀) (hσ.ne_zero x₀ hx₀)
    (hσ.apply_eq_zero x₀ hx₀) hhR).1 hker).mdifferentiableWithinAt

/-- **Holomorphic transition functions.** Two holomorphic frames of a complex linear real
Cauchy–Riemann operator on a line bundle over a complex manifold differ, on the overlap of their
open domains, by a nowhere-zero holomorphic function. -/
theorem exists_mdifferentiableOn_eq_smul_of_isHolomorphicFrameOn {σ σ' : Π x : M, V x}
    {U U' : Set M} (hσ : IsHolomorphicFrameOn ℂ D σ U) (hσ' : IsHolomorphicFrameOn ℂ D σ' U')
    (hU : IsOpen U) (hU' : IsOpen U') :
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

/-- The real derivative of the inverse of a holomorphic chart is complex linear. -/
private theorem mfderiv_extChartAt_symm_I_smul {x₀ : M} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).target) (w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm z (ofComplexManifold ℂ ℂ z w) =
      ofComplexManifold ℂ M _ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm z w) := by
  have hhol : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x₀).symm z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := x₀) (z := z) hz
    simpa [mdifferentiableWithinAt_univ] using h
  have hps := (isPseudoholomorphicAt_ofComplexManifold_iff (E := ℂ) (M := ℂ) (N := M)).2 hhol
  exact hps.mfderiv_apply_commute w

/-- The derivative of a function read in a chart: for `H` differentiable at `z`, the derivative
of `H ∘ φ` at `φ⁻¹ z` along `dφ⁻¹ w` is `dH w`. -/
private theorem mvfderiv_comp_extChartAt_apply {x₀ : M} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x₀).target) {H : ℂ → ℂ} (hH : DifferentiableAt ℝ H z)
    (w : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) (fun y ↦ H (extChartAt 𝓘(ℝ, ℂ) x₀ y)) ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm z w) =
      fderiv ℝ H z w := by
  set φ := extChartAt 𝓘(ℝ, ℂ) x₀
  have hsrc : φ.symm z ∈ (chartAt ℂ x₀).source := by
    simpa [φ] using φ.map_target hz
  have hHφ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y ↦ H (φ y)) (φ.symm z) := by
    have h : DifferentiableAt ℝ H (φ (φ.symm z)) := by rwa [φ.right_inv hz]
    exact h.comp_mdifferentiableAt (mdifferentiableAt_extChartAt hsrc)
  have hsymm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z := by
    simpa [φ, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (x := x₀) hz
  have heq : (fun y ↦ H (φ y)) ∘ φ.symm =ᶠ[𝓝 z] H := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hz] with w hw
    simp [φ.right_inv hw]
  rw [← mvfderiv_comp_apply z hHφ hsymm w, heq.mvfderiv_eq]
  exact mvfderiv_eq_fderiv_apply H z w

/-- A real linear map on `ℂ` which is complex antilinear and vanishes on a nonzero vector
vanishes. -/
private theorem eq_zero_of_apply_I_smul {W : Type*} [AddCommGroup W] [Module ℂ W] [Module ℝ W]
    [TopologicalSpace W] {η : ℂ →L[ℝ] W} (hη : ∀ v, η (Complex.I • v) = -(Complex.I • η v))
    {u : ℂ} (hu : u ≠ 0) (hηu : η u = 0) : η = 0 := by
  ext v
  have hv : v = (v / u).re • u + (v / u).im • (Complex.I • u) := by
    simp only [Complex.real_smul, smul_eq_mul]
    conv_lhs => rw [← div_mul_cancel₀ v hu, ← Complex.re_add_im (v / u)]
    ring
  rw [hv, map_add, map_smul, map_smul, hη, hηu]
  simp

variable {V : M → Type*} [TopologicalSpace (TotalSpace ℂ V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle ℂ V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ ℂ V] [VectorBundle ℝ ℂ V]

/-- The coefficient of an operator `D` on a complex line bundle `V` over a complex curve, in the
chart `φ` and the trivialization `e` at `x₀`: at the chart point `z`, the coordinate in `e` of
`D s`, for the frame `s = e⁻¹ 1` of `e` (`Bundle.Trivialization.localFrame`), evaluated on the
coordinate vector `∂/∂x = dφ⁻¹ 1` of the chart. For a real Cauchy–Riemann operator, whose values
are `(0,1)`-forms, `D s = (B dz̄) ⊗ s` on the chart domain, where `B` is this coefficient. -/
def cauchyRiemannChartCoeff (D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (x₀ : M) (z : ℂ) : ℂ :=
  (trivializationAt ℂ V x₀).continuousLinearMapAt ℂ ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
    (D ((trivializationAt ℂ V x₀).localFrame (Module.Basis.singleton Unit ℂ) ())
      ((extChartAt 𝓘(ℝ, ℂ) x₀).symm z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (extChartAt 𝓘(ℝ, ℂ) x₀).symm z (1 : ℂ)))

variable [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}

namespace IsRealCauchyRiemannOperator

variable (hD : IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ M) D)
  (hDℂ : IsComplexLinearOperator ℂ D)
include hD hDℂ

/-- **Local holomorphic frames** (McDuff–Salamon, Appendix C, via the similarity principle).
A complex linear real Cauchy–Riemann operator on a complex line bundle over a complex curve,
whose coefficient in the chart and trivialization at `x₀` is smooth near `x₀`, has a holomorphic
frame on an open neighbourhood of `x₀`: a smooth section, nowhere zero there, in the kernel of
`D`. -/
theorem exists_isHolomorphicFrameOn (x₀ : M)
    (hB : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, ℂ) x₀ x₀), ContDiffAt ℝ ∞ (cauchyRiemannChartCoeff D x₀) z) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ σ : Π x : M, V x, IsHolomorphicFrameOn ℂ D σ U := by
  set φ := extChartAt 𝓘(ℝ, ℂ) x₀
  set e := trivializationAt ℂ V x₀
  set s : Π x : M, V x := e.localFrame (Module.Basis.singleton Unit ℂ) () with hs
  -- The frame `s` has coordinate `1` in `e`, so it is smooth and nowhere zero on `e.baseSet`.
  have hinj (x : M) (hx : x ∈ e.baseSet) : Function.Injective (e.continuousLinearMapAt ℂ x) :=
    fun a b hab ↦ by
      rw [← e.symmL_continuousLinearMapAt (R := ℂ) hx a, hab,
        e.symmL_continuousLinearMapAt (R := ℂ) hx b]
  have hs1 (x : M) (hx : x ∈ e.baseSet) : e.continuousLinearMapAt ℂ x (s x) = 1 := by
    rw [hs, Trivialization.localFrame_apply_of_mem_baseSet _ _ hx, Trivialization.basisAt,
      Module.Basis.map_apply, Module.Basis.singleton_apply,
      e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx,
      ← e.linearEquivAt_apply (R := ℂ) x hx, LinearEquiv.apply_symm_apply]
  have hcoord (x : M) (hx : x ∈ e.baseSet) (c : ℂ) : (e ⟨x, c • s x⟩).2 = c := by
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx, map_smul, hs1 x hx, smul_eq_mul,
      mul_one]
  have hs_smooth : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (T% s) e.baseSet := by
    rw [e.contMDiffOn_section_iff e.open_baseSet subset_rfl]
    refine (contMDiffOn_const (c := (1 : ℂ))).congr fun x hx ↦ ?_
    simpa using hcoord x hx 1
  -- A smooth solution `G` of `∂bar G = -B` near the chart point of `x₀`.
  obtain ⟨W₁, hW₁, hW₁o, hz₀W₁⟩ := eventually_nhds_iff.mp hB
  have hBW : ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ -cauchyRiemannChartCoeff D x₀ z) W₁ :=
    fun z hz ↦ (hW₁ z hz).neg.contDiffWithinAt
  obtain ⟨G, hG, hGeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq le_top hW₁o hBW hz₀W₁
  obtain ⟨W₂, hW₂, hW₂o, hz₀W₂⟩ := eventually_nhds_iff.mp hGeq
  set H : ℂ → ℂ := fun w ↦ Complex.exp (G w)
  have hHd : ContDiff ℝ (⊤ : ℕ∞) H := Complex.contDiff_exp.comp hG
  let U : Set M := (φ.source ∩ e.baseSet) ∩ φ ⁻¹' W₂
  have hUo : IsOpen U :=
    ((continuousOn_extChartAt x₀).mono inter_subset_left).isOpen_inter_preimage
      ((isOpen_extChartAt_source x₀).inter e.open_baseSet) hW₂o
  have hUe : U ⊆ e.baseSet := fun x hx ↦ hx.1.2
  have hx₀U : x₀ ∈ U :=
    ⟨⟨mem_extChartAt_source x₀, mem_baseSet_trivializationAt ℂ V x₀⟩, hz₀W₂⟩
  set f : M → ℂ := fun x ↦ H (φ x)
  have hf_smooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f U :=
    hHd.contMDiff.comp_contMDiffOn ((contMDiffOn_extChartAt (x := x₀)).mono fun x hx ↦ by
      simpa [φ] using hx.1.1)
  refine ⟨U, hUo, hx₀U, f • s, ⟨?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩⟩
  · rw [e.contMDiffOn_section_iff hUo hUe]
    exact hf_smooth.congr fun x hx ↦ hcoord x (hUe hx) (f x)
  · refine smul_ne_zero (Complex.exp_ne_zero _) fun h0 ↦ ?_
    have := hs1 x (hUe hx)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  · -- Read the point in the chart: `x = φ⁻¹ z`.
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ φ.target, φ.symm z = x :=
      ⟨φ x, φ.map_source hx.1.1, φ.left_inv hx.1.1⟩
    have hzW₂ : z ∈ W₂ := by simpa [φ.right_inv hz] using hx.2
    have hsx : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) (T% s) (φ.symm z) :=
      (hs_smooth.contMDiffAt (e.open_baseSet.mem_nhds hx.1.2)).mdifferentiableAt (by simp)
    have hfx : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (φ.symm z) :=
      (hf_smooth.contMDiffAt (hUo.mem_nhds hx)).mdifferentiableAt (by simp)
    set y := φ.symm z
    set u : TangentSpace 𝓘(ℝ, ℂ) y := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z (1 : ℂ) with hu_def
    have hu : u ≠ 0 := by
      obtain ⟨L, hL⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (x := x₀) hz
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hL
      intro h0
      have h1 := (L.map_eq_zero_iff (x := (1 : ℂ))).1 ((congrArg (· (1 : ℂ)) hL).trans h0)
      exact one_ne_zero (show (1 : ℂ) = 0 from h1)
    have hval : D (f • s) y u = f y • D s y u +
        (2⁻¹ : ℝ) • (mvfderiv 𝓘(ℝ, ℂ) f y u • s y +
          Complex.I • (mvfderiv 𝓘(ℝ, ℂ) f y (ofComplexManifold ℂ M y u) • s y)) := by
      rw [hD.leibniz_complex hDℂ hsx hfx, add_apply, smul_apply, zeroOnePart_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply]
    have hHz : DifferentiableAt ℝ H z := hHd.differentiable (by simp) z
    have hd1 : mvfderiv 𝓘(ℝ, ℂ) f y u = fderiv ℝ H z 1 :=
      mvfderiv_comp_extChartAt_apply hz hHz 1
    have hdI : mvfderiv 𝓘(ℝ, ℂ) f y (ofComplexManifold ℂ M y u) = fderiv ℝ H z Complex.I := by
      rw [hu_def, ← mfderiv_extChartAt_symm_I_smul hz]
      refine (mvfderiv_comp_extChartAt_apply hz hHz _).trans (congrArg (fderiv ℝ H z) ?_)
      exact (ofComplexManifold_apply (E := ℂ) (M := ℂ) z (1 : ℂ)).trans (mul_one Complex.I)
    have hfz : f y = Complex.exp (G z) := by simp [f, H, y, φ.right_inv hz]
    have hBz : e.continuousLinearMapAt ℂ y (D s y u) = cauchyRiemannChartCoeff D x₀ z := rfl
    have hfd : fderiv ℝ H z = Complex.exp (G z) • fderiv ℝ G z :=
      ((hG.differentiable (by simp) z).hasFDerivAt.cexp).fderiv
    have hcw := hW₂ z hzW₂
    rw [conjWirtingerDeriv_apply] at hcw
    have key : D (f • s) y u = 0 := by
      apply hinj _ hx.1.2
      rw [map_zero, hval, map_add, map_smul, hBz,
        RCLike.real_smul_eq_coe_smul (K := ℂ) (E := V y) (2⁻¹ : ℝ), map_smul, map_add, map_smul,
        map_smul, map_smul, hs1 y hx.1.2, hd1, hdI, hfz, hfd]
      simp only [smul_apply, smul_eq_mul, mul_one] at hcw ⊢
      push_cast
      linear_combination Complex.exp (G z) * hcw
    refine eq_zero_of_apply_I_smul (fun v ↦ ?_) hu key
    have h := isZeroOneForm_iff.1 (hD.isZeroOneForm (f • s) y) v
    rwa [ofComplexManifold_apply] at h

end IsRealCauchyRiemannOperator

end Curve

end TauCeti
