/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import Mathlib.Geometry.Manifold.Notation

/-!
# Real Cauchy–Riemann operators read in a local frame

Let `V` be a complex vector bundle of finite rank over a manifold `M` with an almost complex
structure `j`, let `e` be a trivialization of `V` and `b` a basis of the model fibre over `ℝ`, so
that `e.localFrame b` is a smooth real frame of `V` over `e.baseSet`. This file reads a real
Cauchy–Riemann operator `D` on `V` in that frame.

Writing `σ = ∑ i, σⁱ • eᵢ` over `e.baseSet`, with real coefficients `σⁱ`, the Leibniz rule gives

`D σ = ∑ i, (∂bar σⁱ) ⊗ eᵢ + ∑ i, σⁱ • D eᵢ`

at points of `e.baseSet` where `σ` is differentiable. The first summand is the `(0,1)`-part of
the flat covariant derivative of the frame; it is `frameCauchyRiemannOperator`, which satisfies the
axioms of a real Cauchy–Riemann operator over `e.baseSet` and kills the frame sections. The second
summand is a zeroth-order term: the difference of `D` and the flat operator is tensorial at each
point of `e.baseSet` (`TauCeti.IsRealCauchyRiemannOperator.tensorialAt_sub_zeroOnePart`).

## Main results

* `TauCeti.Manifold.frameCauchyRiemannOperator`: the flat real Cauchy–Riemann operator of a local
  frame, with `TauCeti.Manifold.frameCauchyRiemannOperator_eq_sum` computing it as
  `∑ i, (∂bar σⁱ) ⊗ eᵢ`, and `TauCeti.Manifold.frameCauchyRiemannOperator_add` and
  `TauCeti.Manifold.frameCauchyRiemannOperator_leibniz` its Cauchy–Riemann axioms over the base
  set.
* `TauCeti.IsRealCauchyRiemannOperator.eq_frameCauchyRiemannOperator_add_sum`: the local frame
  formula.

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

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
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

theorem frameCauchyRiemannOperator_apply :
    frameCauchyRiemannOperator j b e σ x = j.zeroOnePart (frameCovariantDerivative I b e σ x) :=
  (rfl)

/-- The flat real Cauchy–Riemann operator of a frame is `∑ i, (∂bar σⁱ) ⊗ eᵢ`, where `σⁱ` are the
real coefficients of `σ` in the frame. -/
theorem frameCauchyRiemannOperator_eq_sum :
    frameCauchyRiemannOperator j b e σ x =
      ∑ i, j.dbarSMulRight ((LinearMap.piApply (e.localFrameCoeff I b i)) σ)
        (e.localFrame b i) x := by
  -- The body of `frameCovariantDerivative` is not exposed outside its module, so its sum formula
  -- is recovered from `frameCovariantDerivative_apply`.
  have h : frameCovariantDerivative I b e σ x = ∑ i,
      (d% ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight (e.localFrame b i x) := by
    ext v
    simp [frameCovariantDerivative_apply]
  rw [frameCauchyRiemannOperator_apply, h, zeroOnePart_sum]
  exact Finset.sum_congr rfl fun i _ ↦ zeroOnePart_smulRight _ _ x

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

variable [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-- **The local frame formula.** At points of the base set of a trivialization where `σ` is
differentiable, a real Cauchy–Riemann operator is the flat real Cauchy–Riemann operator
`∑ i, (∂bar σⁱ) ⊗ eᵢ` of the frame plus the zeroth-order term `∑ i, σⁱ • D eᵢ`. -/
theorem eq_frameCauchyRiemannOperator_add_sum (hD : IsRealCauchyRiemannOperator F j D)
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    D σ x = Manifold.frameCauchyRiemannOperator j b e σ x +
      ∑ i, e.localFrameCoeff I b i x (σ x) • D (e.localFrame b i) x := by
  have : FiniteDimensional ℝ F := Module.Finite.of_basis b
  set c : ι → M → ℝ := fun i ↦ (LinearMap.piApply (e.localFrameCoeff I b i)) σ
  have hcd (i : ι) : MDiffAt (c i) x := mdifferentiableAt_localFrameCoeff b hx hσ i
  have hframe (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    ((e.contMDiffOn_localFrame_baseSet 1 b i).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds hx)
  have hterm (i : ι) : MDiffAt (T% (c i • e.localFrame b i)) x := (hcd i).smul_section (hframe i)
  have heq : ∀ᶠ y in 𝓝 x, σ y = ∑ i, (c i • e.localFrame b i) y :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by
      simpa [c] using e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) hy
  -- `D` differs from the flat operator of the frame by a term tensorial at `x`, and the flat
  -- operator kills the frame sections.
  have Φ := hD.tensorialAt_sub_zeroOnePart
    (Manifold.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b) hx
  rw [← sub_eq_iff_eq_add', Manifold.frameCauchyRiemannOperator_apply,
    Φ.local hσ (.sum_section fun i _ ↦ hterm i) heq, Φ.sum _ fun i _ ↦ hterm i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Φ.smul (hcd i) (hframe i), ← Manifold.frameCauchyRiemannOperator_apply,
    Manifold.frameCauchyRiemannOperator_localFrame b hx, sub_zero]
  simp only [c, LinearMap.piApply_apply_apply]

end IsRealCauchyRiemannOperator

end TauCeti
