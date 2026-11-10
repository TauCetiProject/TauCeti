/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import Mathlib.Geometry.Manifold.Notation

/-!
# Real Cauchy–Riemann operators read in a local frame

Let `V` be a complex vector bundle of finite rank over a manifold `M` with an almost complex
structure `j`, let `e` be a trivialization of `V` and `b` a basis of the model fibre over `ℝ`, so
that `e.localFrame b` is a smooth real frame of `V` over `e.baseSet`. This file reads a real
Cauchy–Riemann operator `D` on `V` in that frame.

A real Cauchy–Riemann operator is local: `D σ x` depends only on the germ of `σ` at `x`. Writing
`σ = ∑ i, σⁱ • eᵢ` over `e.baseSet`, with real coefficients `σⁱ`, the Leibniz rule gives

`D σ = ∑ i, (∂bar σⁱ) ⊗ eᵢ + ∑ i, σⁱ • D eᵢ`

on `e.baseSet`. The first summand is the `(0,1)`-part of the flat covariant derivative of the
frame; it is `frameCauchyRiemannOperator`, which satisfies the axioms of a real Cauchy–Riemann
operator over `e.baseSet` and kills the frame sections. The second summand is a zeroth-order
term.

Finally, if two real Cauchy–Riemann operators send smooth sections to smooth `V`-valued one-forms,
then their difference, the zeroth-order term `IsRealCauchyRiemannOperator.difference`, is a smooth
section of the bundle `Hom(V, Hom(TM, V))`, and so is the antilinear part
`IsRealCauchyRiemannOperator.antilinearPart` of such an operator. This is the smoothness of the
zeroth-order term in McDuff–Salamon's statement that two smooth real Cauchy–Riemann operators differ
by a smooth section of `Λ^{0,1} ⊗ End_ℝ V`. The smoothness of an operator is phrased with Mathlib's
`ContMDiffCovariantDerivativeOn`, which only asks that the operator sends `C^(n + 1)` sections over
a set to `C^n` sections of `Hom(TM, V)` there.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.apply_eq_of_eventuallyEq`: locality of real Cauchy–Riemann
  operators.
* `TauCeti.IsRealCauchyRiemannOperator.tensorialAt_sub_zeroOnePart`: a real Cauchy–Riemann
  operator differs from the `(0,1)`-part of a covariant derivative over a set by a tensorial term
  at each point of that set.
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

namespace IsRealCauchyRiemannOperator

/-! ### Locality -/

/-- A real Cauchy–Riemann operator vanishes on the zero section. -/
theorem apply_zero [VectorBundle ℝ F V] (hD : IsRealCauchyRiemannOperator F j D) (x : M) :
    D 0 x = 0 := by
  simpa using hD.smul_const 0 (σ := 0) (x := x) (mdifferentiableAt_zeroSection ℝ V)

/-- A real Cauchy–Riemann operator commutes with finite sums of sections differentiable at a
point. -/
theorem apply_sum [VectorBundle ℝ F V] (hD : IsRealCauchyRiemannOperator F j D) {κ : Type*}
    {s : Finset κ} {τ : κ → Π x : M, V x} (hτ : ∀ i ∈ s, MDiffAt (T% (τ i)) x) :
    D (∑ i ∈ s, τ i) x = ∑ i ∈ s, D (τ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD.apply_zero x
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hτ
    have hsum : MDiffAt (T% (∑ k ∈ s, τ k)) x := by
      simpa [Finset.sum_apply] using
        MDifferentiableAt.sum_section (t := fun k (y : M) ↦ τ k y) (s := s) hτ.2
    rw [Finset.sum_insert hi, hD.add hτ.1 hsum, ih hτ.2, Finset.sum_insert hi]

/-- **Locality.** If two sections differentiable at `x` agree on a neighbourhood of `x`, then a
real Cauchy–Riemann operator takes the same value on them at `x`. -/
theorem apply_eq_of_eqOn (hD : IsRealCauchyRiemannOperator F j D) {s : Set M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hs : s ∈ 𝓝 x) (h : ∀ y ∈ s, σ y = σ' y) :
    D σ x = D σ' x := by
  classical
  -- Multiply by the indicator `ψ` of `s`: it is locally constant at `x`, so `D (ψ • σ) x = D σ x`.
  let ψ : M → ℝ := s.indicator 1
  have hψ : ψ =ᶠ[𝓝 x] fun _ ↦ 1 :=
    eventually_of_mem hs fun y hy ↦ by simp [ψ, indicator_of_mem hy]
  have hψx : ψ x = 1 := hψ.eq_of_nhds
  have hψ' : HasMFDerivAt I 𝓘(ℝ) ψ x 0 := (hasMFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hψ
  have hψd : MDiffAt ψ x := hψ'.mdifferentiableAt
  have hdψ : d% ψ x = 0 := by simp [mvfderiv, hψ'.mfderiv]
  have hdbar (τ : Π x : M, V x) : j.dbarSMulRight ψ τ x = 0 := by
    ext v
    simp [dbarSMulRight_apply, hdψ]
  have hsmul : ψ • σ = ψ • σ' := by
    ext y
    by_cases hy : y ∈ s
    · simp [h y hy]
    · simp [ψ, indicator_of_notMem hy]
  calc D σ x = D (ψ • σ) x := by rw [hD.leibniz hσ hψd, hψx, one_smul, hdbar, add_zero]
    _ = D (ψ • σ') x := by rw [hsmul]
    _ = D σ' x := by rw [hD.leibniz hσ' hψd, hψx, one_smul, hdbar, add_zero]

/-- **Locality.** A real Cauchy–Riemann operator at `x` only depends on the germ at `x` of a section
differentiable at `x`. -/
theorem apply_eq_of_eventuallyEq (hD : IsRealCauchyRiemannOperator F j D)
    (hσ : MDiffAt (T% σ) x) (h : ∀ᶠ y in 𝓝 x, σ y = σ' y) : D σ x = D σ' x := by
  have hσ' : MDiffAt (T% σ') x :=
    hσ.congr_of_eventuallyEq (h.mono fun y hy ↦ congrArg (TotalSpace.mk' F y) hy.symm)
  obtain ⟨s, hs, hss⟩ := h.exists_mem
  exact hD.apply_eq_of_eqOn hσ hσ' hs hss

end IsRealCauchyRiemannOperator

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

namespace SmoothAlmostComplexStructure

omit [FiberBundle F V] in
/-- The `(0,1)`-part of the zero one-form is zero. -/
@[simp]
theorem zeroOnePart_zero {x : M} : j.zeroOnePart (0 : TangentSpace I x →L[ℝ] V x) = 0 := by
  ext v
  simp [zeroOnePart_apply]

omit [FiberBundle F V] in
/-- The `(0,1)`-projection commutes with finite sums. -/
theorem zeroOnePart_sum {κ : Type*} (s : Finset κ) {x : M}
    (η : κ → TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePart (∑ i ∈ s, η i) = ∑ i ∈ s, j.zeroOnePart (η i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, zeroOnePart_add, ih, Finset.sum_insert hi]

end SmoothAlmostComplexStructure

namespace IsRealCauchyRiemannOperator

/-! ### Comparison with the `(0,1)`-part of a covariant derivative -/

/-- At a point of a set over which `cov` is a covariant derivative, a real Cauchy–Riemann operator
differs from the `(0,1)`-part of `cov` by a tensorial term. -/
theorem tensorialAt_sub_zeroOnePart (hD : IsRealCauchyRiemannOperator F j D)
    {cov : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) (hx : x ∈ s) :
    TensorialAt I F (fun σ ↦ D σ x - j.zeroOnePart (cov σ x)) x where
  smul hg hσ := by
    simp only [hD.leibniz hσ hg, hcov.leibniz hσ hg hx, zeroOnePart_add, zeroOnePart_smul,
      zeroOnePart_smulRight, smul_sub]
    abel
  add hσ hσ' := by
    simp only [hD.add hσ hσ', hcov.add hσ hσ' hx, zeroOnePart_add]
    abel

end IsRealCauchyRiemannOperator

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
    (isCovariantDerivativeOn_frameCovariantDerivative b).add hσ hσ' hx, zeroOnePart_add]

/-- The flat real Cauchy–Riemann operator of a frame satisfies the Leibniz rule
`D (g • σ) = g • D σ + (∂bar g) ⊗ σ` at points of the base set. -/
theorem frameCauchyRiemannOperator_leibniz (hx : x ∈ e.baseSet) {g : M → ℝ}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) :
    frameCauchyRiemannOperator j b e (g • σ) x =
      g x • frameCauchyRiemannOperator j b e σ x + j.dbarSMulRight g σ x := by
  simp only [frameCauchyRiemannOperator_apply,
    (isCovariantDerivativeOn_frameCovariantDerivative b).leibniz hσ hg hx, zeroOnePart_add,
    zeroOnePart_smul, zeroOnePart_smulRight]

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
  rfl

end IsRealCauchyRiemannOperator

/-! ### Smoothness of the zeroth-order terms -/

section Smooth

variable [FiniteDimensional ℝ E] [T2Space M] {u : Set M} {n : ℕ∞ω}

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [FiberBundle F V]
  [∀ x, Module ℂ (V x)] in
/-- Over a Hausdorff manifold, a section of a bundle of continuous linear maps out of a `C^∞`
bundle of finite rank is `C^n` on a set as soon as its evaluations on the globally `C^∞` sections
are. -/
private theorem contMDiffOn_hom_of_forall_contMDiff (hn : n ≤ ∞)
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, TopologicalSpace (W x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [ContMDiffVectorBundle n G W I] {A : Π x : M, V₁ x →L[ℝ] W x}
    (hA : ∀ τ : Π x : M, V₁ x, CMDiff ∞ (T% τ) →
      ContMDiffOn I (I.prod 𝓘(ℝ, G)) n (fun y ↦ TotalSpace.mk' G y (A y (τ y))) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] G)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] G) (E := fun x ↦ V₁ x →L[ℝ] W x) y (A y)) u := by
  have : ContMDiffVectorBundle n F₁ V₁ I := .of_le hn
  refine contMDiffOn_of_locally_contMDiffOn fun x _ ↦ ?_
  let e := trivializationAt F₁ V₁ x
  let e' := trivializationAt G W x
  let b := Basis.ofVectorSpace ℝ F₁
  have := FiniteDimensional.fintypeBasisIndex b
  obtain ⟨τ, hτ, hτe⟩ :=
    e.exists_contMDiff_eventuallyEq_localFrame (I := I) b (mem_baseSet_trivializationAt F₁ V₁ x)
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (eventually_all.2 hτe)
  refine ⟨t ∩ (e.baseSet ∩ e'.baseSet), hto.inter (e.open_baseSet.inter e'.open_baseSet),
    ⟨hxt, mem_baseSet_trivializationAt F₁ V₁ x, mem_baseSet_trivializationAt G W x⟩, ?_⟩
  refine Manifold.contMDiffOn_hom_of_localFrame (n := n) (b := b) (e := e) (e' := e') (f := id)
    (u := u ∩ (t ∩ (e.baseSet ∩ e'.baseSet))) (A := A)
    (contMDiffOn_id (I := I)) (fun y hy ↦ hy.2.2) fun i ↦ ?_
  refine ((hA (τ i) (hτ i)).mono inter_subset_left).congr fun y hy ↦ ?_
  simp [ht y hy.2.1 i]

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
  refine contMDiffOn_hom_of_forall_contMDiff (le_self_add.trans hn) fun τ hτ ↦ ?_
  have hτu : CMDiff[u] (n + 1) (T% τ) := (hτ.of_le hn).contMDiffOn
  refine ((hDs.contMDiff hτu).sub_section (hD's.contMDiff hτu)).congr fun y _ ↦ ?_
  rw [hD.difference_apply hD' ((hτ y).mdifferentiableAt (by simp))]
  rfl

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
  refine contMDiffOn_hom_of_forall_contMDiff hn fun τ hτ ↦ ?_
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
    exact h.congr fun y _ ↦ by rw [sectionComplexLinearPart_apply]; rfl

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
  have hDℂ := hD.isRealCauchyRiemannOperator_sectionComplexLinearPart
  refine (hD.contMDiffOn_difference hDℂ hn hDs
    (contMDiffCovariantDerivativeOn_sectionComplexLinearPart hn hDs)).congr fun y _ ↦ ?_
  have h : hD.antilinearPart y = hD.difference hDℂ y := by
    ext v : 1
    have hσ := mdifferentiableAt_extend I F v
    have h₁ := hD.sectionComplexLinearPart_add_antilinearPart hσ
    rw [hD.eq_add_difference hDℂ hσ, add_right_inj, extend_apply_self] at h₁
    exact h₁
  rw [h]

end Smooth

end TauCeti
