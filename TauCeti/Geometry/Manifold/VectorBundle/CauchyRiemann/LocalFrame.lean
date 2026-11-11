/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Notation

/-!
# Real Cauchy–Riemann operators read in a local frame

Let `V` be a complex vector bundle of finite rank over a manifold `M` with an almost complex
structure `j`, let `e` be a trivialization of `V` and `b` a basis of the model fibre over `ℝ`, so
that `e.localFrame b` is a smooth real frame of `V` over `e.baseSet`. This file reads a real
Cauchy–Riemann operator `D` on `V` in that frame.

A real Cauchy–Riemann operator is local: for sections differentiable at `x`, `D σ x` depends only
on the germ of `σ` at `x` (`TauCeti.IsRealCauchyRiemannOperator.apply_eq_of_eventuallyEq`).
Writing `σ = ∑ i, σⁱ • eᵢ` over `e.baseSet`, with real coefficients `σⁱ`, the Leibniz rule gives

`D σ = ∑ i, (∂bar σⁱ) ⊗ eᵢ + ∑ i, σⁱ • D eᵢ`

at points of `e.baseSet` where `σ` is differentiable. The first summand is the `(0,1)`-part of
the flat covariant derivative of the frame; it is `frameCauchyRiemannOperator`, which satisfies the
axioms of a real Cauchy–Riemann operator over `e.baseSet` and kills the frame sections. The second
summand is a zeroth-order term.

Finally, if two real Cauchy–Riemann operators send smooth sections to smooth `V`-valued one-forms,
then their difference, the zeroth-order term `IsRealCauchyRiemannOperator.difference`, is a smooth
section of the bundle `Hom(V, Hom(TM, V))`, and so is the antilinear part
`IsRealCauchyRiemannOperator.antilinearPart` of such an operator. This is the smoothness of the
zeroth-order term in McDuff–Salamon's statement that two smooth real Cauchy–Riemann operators differ
by a smooth section of `Λ^{0,1} ⊗ End_ℝ V`. The smoothness of an operator is phrased with Mathlib's
`ContMDiffCovariantDerivativeOn`, which only asks that the operator sends `C^(n + 1)` sections over
a set to `C^n` sections of `Hom(TM, V)` there.

## Main results

* `TauCeti.Manifold.frameCauchyRiemannOperator`: the flat real Cauchy–Riemann operator of a local
  frame, with `TauCeti.Manifold.frameCauchyRiemannOperator_eq_sum` computing it as
  `∑ i, (∂bar σⁱ) ⊗ eᵢ`, and `TauCeti.Manifold.frameCauchyRiemannOperator_add` and
  `TauCeti.Manifold.frameCauchyRiemannOperator_leibniz` its Cauchy–Riemann axioms over the base
  set.
* `TauCeti.IsRealCauchyRiemannOperator.eq_frameCauchyRiemannOperator_add_sum`: the local frame
  formula.
* `TauCeti.IsRealCauchyRiemannOperator.contMDiffOn_difference` and
  `TauCeti.IsRealCauchyRiemannOperator.contMDiffOn_antilinearPart`: smoothness of the zeroth-order
  terms of smooth real Cauchy–Riemann operators.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Definition C.1.5 and Exercise C.1.7.
-/

public section

open Bundle FiberBundle Filter Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {j : SmoothAlmostComplexStructure I M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
  {σ σ' : Π x : M, V x} {x : M}

open SmoothAlmostComplexStructure

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

/-! ### The flat real Cauchy–Riemann operator of a local frame -/

namespace Manifold

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

variable (j) in
/-- The flat real Cauchy–Riemann operator of the local frame induced by a trivialization `e` of
`V` and a real basis `b` of the model fibre: the `(0,1)`-part of the flat covariant derivative
`TauCeti.Manifold.frameCovariantDerivative` of the frame. It satisfies the axioms of a real
Cauchy–Riemann operator over `e.baseSet`; outside that set it carries a junk value. -/
def frameCauchyRiemannOperator (b : Basis ι ℝ F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
  j.zeroOnePart (frameCovariantDerivative I b e σ x)

omit [FiniteDimensional ℝ F] in
theorem frameCauchyRiemannOperator_apply :
    frameCauchyRiemannOperator j b e σ x = j.zeroOnePart (frameCovariantDerivative I b e σ x) :=
  (rfl)

omit [FiniteDimensional ℝ F] in
/-- The flat real Cauchy–Riemann operator of a frame is `∑ i, (∂bar σⁱ) ⊗ eᵢ`, where `σⁱ` are the
real coefficients of `σ` in the frame. -/
theorem frameCauchyRiemannOperator_eq_sum :
    frameCauchyRiemannOperator j b e σ x =
      ∑ i, j.dbarSMulRight ((LinearMap.piApply (e.localFrameCoeff I b i)) σ)
        (e.localFrame b i) x := by
  have h : frameCovariantDerivative I b e σ x = ∑ i,
      (d% ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight (e.localFrame b i x) := by
    ext v
    simp [frameCovariantDerivative_apply]
  rw [frameCauchyRiemannOperator_apply, h, zeroOnePart_sum]
  exact Finset.sum_congr rfl fun i _ ↦ zeroOnePart_smulRight _ _ x

omit [FiniteDimensional ℝ F] in
/-- The flat real Cauchy–Riemann operator of a frame takes values in `(0,1)`-forms. -/
theorem isZeroOneForm_frameCauchyRiemannOperator :
    j.IsZeroOneForm (frameCauchyRiemannOperator j b e σ x) :=
  isZeroOneForm_zeroOnePart _

/-- The flat real Cauchy–Riemann operator of a frame is additive at points of the base set. -/
theorem frameCauchyRiemannOperator_add (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x) :
    frameCauchyRiemannOperator j b e (σ + σ') x =
      frameCauchyRiemannOperator j b e σ x + frameCauchyRiemannOperator j b e σ' x := by
  simp only [frameCauchyRiemannOperator_apply,
    (isCovariantDerivativeOn_frameCovariantDerivative b).zeroOnePart_add j hx hσ hσ']

/-- The flat real Cauchy–Riemann operator of a frame satisfies the Leibniz rule
`D (g • σ) = g • D σ + (∂bar g) ⊗ σ` at points of the base set. -/
theorem frameCauchyRiemannOperator_leibniz (hx : x ∈ e.baseSet) {g : M → ℝ}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) :
    frameCauchyRiemannOperator j b e (g • σ) x =
      g x • frameCauchyRiemannOperator j b e σ x + j.dbarSMulRight g σ x := by
  simp only [frameCauchyRiemannOperator_apply,
    (isCovariantDerivativeOn_frameCovariantDerivative b).zeroOnePart_leibniz j hx hσ hg]

/-- The flat real Cauchy–Riemann operator of a frame kills the frame sections on the base set. -/
@[simp]
theorem frameCauchyRiemannOperator_localFrame (hx : x ∈ e.baseSet) (i : ι) :
    frameCauchyRiemannOperator j b e (e.localFrame b i) x = 0 := by
  classical
  have hconst : HasMFDerivAt (M' := F) I 𝓘(ℝ, F) (fun _ : M ↦ b i) x
      (0 : TangentSpace I x →L[ℝ] F) := hasMFDerivAt_const _ _
  have hcoeff (k : ι) : (fun z ↦ e.localFrameCoeff I b k z (e.localFrame b i z)) =ᶠ[𝓝 x]
      fun _ ↦ b.coord k (b i) :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun z hz ↦ by
      simp [localFrameCoeff_localFrame b hz, Finsupp.single_apply, eq_comm]
  rw [frameCauchyRiemannOperator_apply,
    frameCovariantDerivative_eq_symmL_comp b hconst hcoeff hx, ContinuousLinearMap.comp_zero,
    zeroOnePart_zero]

end Manifold

namespace IsRealCauchyRiemannOperator

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-- **The local frame formula.** Over the base set of a trivialization, a real Cauchy–Riemann
operator is the flat real Cauchy–Riemann operator `∑ i, (∂bar σⁱ) ⊗ eᵢ` of the frame plus the
zeroth-order term `∑ i, σⁱ • D eᵢ`. -/
theorem eq_frameCauchyRiemannOperator_add_sum (hD : IsRealCauchyRiemannOperator F j D)
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    D σ x = Manifold.frameCauchyRiemannOperator j b e σ x +
      ∑ i, e.localFrameCoeff I b i x (σ x) • D (e.localFrame b i) x := by
  set c : ι → M → ℝ := fun i ↦ (LinearMap.piApply (e.localFrameCoeff I b i)) σ
  have hcd (i : ι) : MDiffAt (c i) x := mdifferentiableAt_localFrameCoeff b hx hσ i
  have hframe (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    ((e.contMDiffOn_localFrame_baseSet 1 b i).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds hx)
  have hterm (i : ι) : MDiffAt (T% (c i • e.localFrame b i)) x := (hcd i).smul_section (hframe i)
  have heq : ∀ᶠ y in 𝓝 x, σ y = (∑ i, c i • e.localFrame b i) y :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by
      simpa [Finset.sum_apply, c] using e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) hy
  rw [hD.apply_eq_of_eventuallyEq hσ heq, hD.apply_sum fun i _ ↦ hterm i,
    Manifold.frameCauchyRiemannOperator_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hD.leibniz (hframe i) (hcd i), add_comm]
  simp only [c, LinearMap.piApply_apply_apply]

end IsRealCauchyRiemannOperator

/-! ### Smoothness of the zeroth-order terms -/

section Smooth

variable [FiniteDimensional ℝ E] [T2Space M] {u : Set M} {n : ℕ∞ω}

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- If two real Cauchy–Riemann operators send `C^(n + 1)` sections over `u` to `C^n` sections of
`Hom(TM, V)` over `u`, then their difference is a `C^n` section over `u` of the bundle
`Hom(V, Hom(TM, V))`: the zeroth-order term by which two smooth real Cauchy–Riemann operators
differ is smooth. -/
theorem IsRealCauchyRiemannOperator.contMDiffOn_difference [VectorBundle ℝ F V]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] {D' : (Π x : M, V x) → Π x : M,
      TangentSpace I x →L[ℝ] V x}
    (hD : IsRealCauchyRiemannOperator F j D) (hD' : IsRealCauchyRiemannOperator F j D')
    (hn : n + 1 ≤ ∞) (hDs : ContMDiffCovariantDerivativeOn F n D u)
    (hD's : ContMDiffCovariantDerivativeOn F n D' u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] V x) y (hD.difference hD' y)) u := by
  have : ContMDiffVectorBundle n F V I := .of_le (le_self_add.trans hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    .of_le (le_self_add.trans hn)
  refine Manifold.contMDiffOn_hom_of_forall_contMDiff (le_self_add.trans hn) fun τ hτ ↦ ?_
  have hτu : CMDiff[u] (n + 1) (T% τ) := (hτ.of_le hn).contMDiffOn
  refine ((hDs.contMDiff hτu).sub_section (hD's.contMDiff hτu)).congr fun y _ ↦ ?_
  rw [hD.difference_apply hD' ((hτ y).mdifferentiableAt (by simp)), Pi.sub_apply]

/-- Multiplying a `C^n` section of `Hom(TM, V)` by a complex scalar acting on `V` gives a `C^n`
section. -/
private theorem contMDiffOn_complex_smul_hom (hn : n ≤ ∞) [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
    [ContMDiffVectorBundle ∞ F V I] (c : ℂ) {η : Π x : M, TangentSpace I x →L[ℝ] V x}
    (hη : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun x ↦ TangentSpace I x →L[ℝ] V x) y (η y))
      u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun x ↦ TangentSpace I x →L[ℝ] V x) y
        ((c • η) y)) u := by
  have : ContMDiffVectorBundle n F V I := .of_le hn
  refine Manifold.contMDiffOn_hom_of_forall_contMDiff hn fun τ hτ ↦ ?_
  exact ContMDiffOn.smul_totalSpace (a := fun _ ↦ c) contMDiffOn_const
    (hη.clm_bundle_apply ((hτ.of_le hn).contMDiffOn))

/-- The complex linear part `D^ℂ ξ = ½ (D ξ - i • D (i • ξ))` of an operator sending `C^(n + 1)`
sections over `u` to `C^n` sections of `Hom(TM, V)` over `u` does the same. -/
theorem contMDiffCovariantDerivativeOn_sectionComplexLinearPart (hn : n + 1 ≤ ∞)
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
    [ContMDiffVectorBundle ∞ F V I] (hDs : ContMDiffCovariantDerivativeOn F n D u) :
    ContMDiffCovariantDerivativeOn F n (sectionComplexLinearPart D) u where
  contMDiff {σ} hσ := by
    have hIσ : CMDiff[u] (n + 1) (T% (Complex.I • σ)) :=
      ContMDiffOn.smul_totalSpace (a := fun _ ↦ Complex.I) contMDiffOn_const hσ
    have h := ((hDs.contMDiff hσ).sub_section (contMDiffOn_complex_smul_hom
      (le_self_add.trans hn) Complex.I (hDs.contMDiff hIσ))).const_smul_section (a := (2⁻¹ : ℝ))
    exact h.congr fun y _ ↦ by
      simp only [sectionComplexLinearPart_apply, Pi.smul_apply, Pi.sub_apply]

/-- The antilinear part of a real Cauchy–Riemann operator sending `C^(n + 1)` sections over `u`
to `C^n` sections of `Hom(TM, V)` over `u` is a `C^n` section over `u` of the bundle
`Hom(V, Hom(TM, V))`. -/
theorem IsRealCauchyRiemannOperator.contMDiffOn_antilinearPart [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [VectorBundle ℂ F V] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] (hD : IsRealCauchyRiemannOperator F j D)
    (hn : n + 1 ≤ ∞) (hDs : ContMDiffCovariantDerivativeOn F n D u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] V x) y (hD.antilinearPart y)) u := by
  rw [antilinearPart_eq_difference]
  exact hD.contMDiffOn_difference hD.isRealCauchyRiemannOperator_sectionComplexLinearPart hn hDs
    (contMDiffCovariantDerivativeOn_sectionComplexLinearPart hn hDs)

end Smooth

end TauCeti
