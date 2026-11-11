/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
import Mathlib.Geometry.Manifold.Complex
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The kernel of `∂bar` on functions

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, regarded with the same charts as a real
manifold modelled on `𝓘(ℝ, E)`, with its almost complex structure
`j = TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`. For a function `u : M → F` into a
complex normed space, `∂bar u` at `x` is the `(0,1)`-part
`j.zeroOnePart (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x)` of its real differential, a one-form with values in
the trivial bundle with fibre `F`.

We show that `∂bar u = 0` at a point where `u` is real differentiable exactly when `u` is complex
differentiable there, so the kernel of `∂bar` on functions consists of the holomorphic functions.
On a compact connected complex manifold these are the constants, so the kernel of `∂bar` on smooth
functions is a real vector space isomorphic to `F`; for `F = ℂ` it has real dimension `2`. This is
the kernel half of step 6 (the trivial bundle) of the Riemann–Roch index computation for
Cauchy–Riemann operators on closed Riemann surfaces.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_zero_iff`: the `(0,1)`-part of a one-form
  `η` vanishes exactly when `η (j v) = i • η v` for all `v`.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartFunctionKernel`: the real subspace of the smooth
  functions `u : M → F` with `j.zeroOnePart (mfderiv I 𝓘(ℝ, F) u x) = 0` at every point, for an
  arbitrary smooth almost complex structure `j`.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff`:
  for `u` real differentiable at `x`, `∂bar u = 0` at `x` if and only if `u` is complex
  differentiable at `x`;
  `TauCeti.SmoothAlmostComplexStructure.forall_zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff`
  is the global form.
* `TauCeti.SmoothAlmostComplexStructure.forall_zeroOnePart_mfderiv_eq_zero_iff_exists_eq_const`:
  on a compact preconnected complex manifold, `∂bar u = 0` everywhere if and only if `u` is
  constant.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartFunctionKernelEquivOfCompactSpace` and
  `TauCeti.SmoothAlmostComplexStructure.finrank_zeroOnePartFunctionKernel_complex`:
  on a compact connected complex manifold the kernel of `∂bar` on smooth functions is real linearly
  equivalent to `F`, and for `F = ℂ` it has real dimension `2`.

The examples at the end check that compactness is needed (the identity of `ℂ` is in the kernel
and is not constant) and that complex conjugation is not in the kernel.

## References

* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second
  edition, AMS Colloquium Publications 52, 2012, Appendix C.1 and the proof of Theorem C.1.10.
-/

public section

open Bundle
open scoped ContDiff Manifold TauCeti.ComplexManifold ComplexConjugate

noncomputable section

namespace TauCeti

namespace SmoothAlmostComplexStructure

/-! ### Vanishing of the `(0,1)`-part -/

section ZeroOnePart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {j : SmoothAlmostComplexStructure I M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

/-- The `(0,1)`-part of a one-form `η` vanishes exactly when `η` is complex linear for `j` and
multiplication by `i`: `η (j v) = i • η v` for all `v`. -/
theorem zeroOnePart_eq_zero_iff {x : M} {η : TangentSpace I x →L[ℝ] V x} :
    j.zeroOnePart η = 0 ↔ ∀ v, η (j x v) = Complex.I • η v := by
  rw [ContinuousLinearMap.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [zeroOnePart_apply, zero_apply, smul_eq_zero,
    or_iff_right (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
  constructor
  · intro h
    have h' := congrArg (Complex.I • ·) h
    simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, smul_zero] at h'
    rw [add_comm] at h'
    exact neg_add_eq_zero.1 h'
  · intro h
    rw [h, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel]

end ZeroOnePart

/-! ### The kernel of `∂bar` on smooth functions -/

section Kernel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The kernel of `∂bar` on smooth functions `u : M → F` into a complex normed space: the real
subspace of the smooth functions whose differential has vanishing `(0,1)`-part
`j.zeroOnePart (mfderiv I 𝓘(ℝ, F) u x)` at every point `x`. -/
def zeroOnePartFunctionKernel : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, F), F⟯ where
  carrier := {u | ∀ x, j.zeroOnePart (V := Trivial M F) (mfderiv I 𝓘(ℝ, F) u x) = 0}
  add_mem' {u v} hu hv x := by
    have hux : MDifferentiableAt I 𝓘(ℝ, F) u x := u.contMDiff.mdifferentiableAt (by simp)
    have hvx : MDifferentiableAt I 𝓘(ℝ, F) v x := v.contMDiff.mdifferentiableAt (by simp)
    rw [ContMDiffMap.coe_add, mfderiv_add hux hvx]
    exact (j.zeroOnePart_add (V := Trivial M F) _ _).trans (by rw [hu x, hv x, add_zero])
  zero_mem' x := by
    rw [ContMDiffMap.coe_zero, Pi.zero_def, mfderiv_const]
    exact zeroOnePart_eq_zero_iff.2 fun _ ↦
      show (0 : F) = Complex.I • (0 : F) from (smul_zero _).symm
  smul_mem' c {u} hu x := by
    have hux : MDifferentiableAt I 𝓘(ℝ, F) u x := u.contMDiff.mdifferentiableAt (by simp)
    rw [ContMDiffMap.coe_smul, (hux.hasMFDerivAt.const_smul c).mfderiv]
    exact (j.zeroOnePart_smul (V := Trivial M F) c _).trans (by rw [hu x, smul_zero])

variable {j F}

theorem mem_zeroOnePartFunctionKernel {u : C^∞⟮I, M; 𝓘(ℝ, F), F⟯} :
    u ∈ j.zeroOnePartFunctionKernel F ↔
      ∀ x, j.zeroOnePart (V := Trivial M F) (mfderiv I 𝓘(ℝ, F) u x) = 0 :=
  Iff.rfl

end Kernel

/-! ### The kernel of `∂bar` on a complex manifold -/

section ComplexManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On a complex manifold, a function `u : M → F` real differentiable at `x` satisfies
`∂bar u = 0` at `x`, for the almost complex structure of `M`, if and only if it is complex
differentiable at `x`. -/
theorem zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff {u : M → F} {x : M}
    (hu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) u x) :
    (ofComplexManifold E M).zeroOnePart (V := Trivial M F) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x) = 0 ↔
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) u x := by
  refine zeroOnePart_eq_zero_iff.trans ?_
  rw [← isPseudoholomorphicAt_ofComplexManifold_iff (E' := F) (N := F),
    isPseudoholomorphicAt_iff_mfderiv, and_iff_right hu]
  exact forall_congr' fun w ↦
    iff_of_eq (congrArg (_ = ·) (ofComplexManifold_apply (E := F) (M := F) (u x) _).symm)

/-- On a complex manifold, a function `u : M → F` is real differentiable with `∂bar u = 0`
everywhere, for the almost complex structure of `M`, if and only if it is holomorphic. -/
theorem forall_zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff {u : M → F} :
    (∀ x, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) u x ∧
        (ofComplexManifold E M).zeroOnePart (V := Trivial M F)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x) = 0) ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) u :=
  ⟨fun h x ↦ (zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff (h x).1).1 (h x).2,
    fun h x ↦ ⟨(h x).restrictScalars ℝ,
      (zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff ((h x).restrictScalars ℝ)).2 (h x)⟩⟩

/-- On a compact preconnected complex manifold, a function `u : M → F` is real differentiable with
`∂bar u = 0` everywhere, for the almost complex structure of `M`, if and only if it is constant. -/
theorem forall_zeroOnePart_mfderiv_eq_zero_iff_exists_eq_const
    [CompactSpace M] [PreconnectedSpace M] {u : M → F} :
    (∀ x, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) u x ∧
        (ofComplexManifold E M).zeroOnePart (V := Trivial M F)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x) = 0) ↔
      ∃ c : F, u = fun _ ↦ c := by
  rw [forall_zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff]
  refine ⟨fun h ↦ h.exists_eq_const_of_compactSpace, ?_⟩
  rintro ⟨c, rfl⟩
  exact mdifferentiable_const

/-- On a complex manifold, a smooth function lies in the kernel of `∂bar`, for the almost complex
structure of `M`, if and only if it is holomorphic. -/
theorem mem_zeroOnePartFunctionKernel_ofComplexManifold_iff {u : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯} :
    u ∈ (ofComplexManifold E M).zeroOnePartFunctionKernel F ↔
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) u := by
  rw [← forall_zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff, mem_zeroOnePartFunctionKernel]
  exact forall_congr' fun x ↦ (and_iff_right (u.contMDiff.mdifferentiableAt (by simp))).symm

variable (E M) in
/-- On a complex manifold, the constant functions lie in the kernel of `∂bar`, as a real linear
map from `F`. -/
def constZeroOnePartFunctionKernel :
    F →ₗ[ℝ] (ofComplexManifold E M).zeroOnePartFunctionKernel F where
  toFun c := ⟨ContMDiffMap.const c,
    mem_zeroOnePartFunctionKernel_ofComplexManifold_iff.2 mdifferentiable_const⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem constZeroOnePartFunctionKernel_apply (c : F) (x : M) :
    (constZeroOnePartFunctionKernel E M c : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯) x = c := by
  simp [constZeroOnePartFunctionKernel, ContMDiffMap.const]

variable (E M F) in
/-- On a compact connected complex manifold, the kernel of `∂bar` on smooth functions `M → F` is
real linearly equivalent to `F`: it consists of the constant functions. -/
def zeroOnePartFunctionKernelEquivOfCompactSpace [CompactSpace M] [ConnectedSpace M] :
    (ofComplexManifold E M).zeroOnePartFunctionKernel F ≃ₗ[ℝ] F :=
  (LinearEquiv.ofBijective (constZeroOnePartFunctionKernel E M)
    ⟨fun c c' h ↦ by
      have x : M := Classical.arbitrary M
      simpa using congrArg (fun u : (ofComplexManifold E M).zeroOnePartFunctionKernel F ↦
        (u : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯) x) h,
    fun u ↦ by
      obtain ⟨c, hc⟩ := (mem_zeroOnePartFunctionKernel_ofComplexManifold_iff.1
        u.2).exists_eq_const_of_compactSpace
      exact ⟨c, Subtype.ext (ContMDiffMap.ext fun x ↦ (congrFun hc x).symm)⟩⟩).symm

@[simp]
theorem zeroOnePartFunctionKernelEquivOfCompactSpace_symm_apply [CompactSpace M]
    [ConnectedSpace M] (c : F) :
    (zeroOnePartFunctionKernelEquivOfCompactSpace E M F).symm c =
      constZeroOnePartFunctionKernel E M c := by
  rw [zeroOnePartFunctionKernelEquivOfCompactSpace, LinearEquiv.symm_symm]
  rfl

/-- On a compact connected complex manifold, the value of a function in the kernel of `∂bar` at
any point is its image under `zeroOnePartFunctionKernelEquivOfCompactSpace`. -/
theorem zeroOnePartFunctionKernelEquivOfCompactSpace_apply [CompactSpace M] [ConnectedSpace M]
    (u : (ofComplexManifold E M).zeroOnePartFunctionKernel F) (x : M) :
    zeroOnePartFunctionKernelEquivOfCompactSpace E M F u =
      (u : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), F⟯) x := by
  conv_rhs => rw [← (zeroOnePartFunctionKernelEquivOfCompactSpace E M F).symm_apply_apply u]
  rw [zeroOnePartFunctionKernelEquivOfCompactSpace_symm_apply, constZeroOnePartFunctionKernel_apply]

/-- On a compact connected complex manifold, the kernel of `∂bar` on smooth functions `M → F` has
the real dimension of `F`. -/
theorem finrank_zeroOnePartFunctionKernel_ofComplexManifold [CompactSpace M] [ConnectedSpace M] :
    Module.finrank ℝ ((ofComplexManifold E M).zeroOnePartFunctionKernel F) = Module.finrank ℝ F :=
  (zeroOnePartFunctionKernelEquivOfCompactSpace E M F).finrank_eq

/-- On a compact connected complex manifold, for instance a closed Riemann surface, the kernel of
`∂bar` on smooth complex valued functions has real dimension `2`. -/
theorem finrank_zeroOnePartFunctionKernel_complex [CompactSpace M]
    [ConnectedSpace M] :
    Module.finrank ℝ ((ofComplexManifold E M).zeroOnePartFunctionKernel ℂ) = 2 := by
  rw [finrank_zeroOnePartFunctionKernel_ofComplexManifold, Complex.finrank_real_complex]

end ComplexManifold

/-! ### Checks -/

section Checks

/-- Compactness is needed for the kernel of `∂bar` on functions to be the constants: on the
noncompact complex manifold `ℂ`, the identity function lies in the kernel and is not constant. -/
theorem exists_mem_zeroOnePartFunctionKernel_ofComplexManifold_complex_ne_const :
    ∃ u ∈ (ofComplexManifold ℂ ℂ).zeroOnePartFunctionKernel ℂ,
      ∀ c : ℂ, u ≠ ContMDiffMap.const c := by
  refine ⟨⟨id, contMDiff_id⟩, mem_zeroOnePartFunctionKernel_ofComplexManifold_iff.2
    mdifferentiable_id, fun c h ↦ ?_⟩
  have h0 := congrArg (fun u : C^∞⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯ ↦ u 0) h
  have h1 := congrArg (fun u : C^∞⟮𝓘(ℝ, ℂ), ℂ; 𝓘(ℝ, ℂ), ℂ⟯ ↦ u 1) h
  simp only [ContMDiffMap.coeFn_mk, id_eq] at h0 h1
  exact one_ne_zero (h1.trans (h0.trans rfl).symm)

/-- Complex conjugation on `ℂ` is real differentiable, but its differential is its own
`(0,1)`-part, so `∂bar conj ≠ 0` and conjugation is not in the kernel of `∂bar`. -/
theorem zeroOnePart_ofComplexManifold_mfderiv_conj_ne_zero (z : ℂ) :
    (ofComplexManifold ℂ ℂ).zeroOnePart (V := Trivial ℂ ℂ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ ↦ conj w) z) ≠ 0 := by
  have hconj : (fun w : ℂ ↦ conj w) = Complex.conjCLE := rfl
  intro h
  have h1 := zeroOnePart_eq_zero_iff.1 h (1 : ℂ)
  rw [hconj, (hasMFDerivAt_iff_hasFDerivAt.2 Complex.conjCLE.hasFDerivAt).mfderiv,
    ofComplexManifold_apply] at h1
  have h2 : conj (Complex.I • (1 : ℂ)) = Complex.I • conj (1 : ℂ) := h1
  norm_num [Complex.ext_iff] at h2

/-- Complex conjugation is not holomorphic at any point of `ℂ`, read off from
`zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff`. -/
theorem not_mdifferentiableAt_conj (z : ℂ) :
    ¬ MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun w : ℂ ↦ conj w) z := by
  have hconj : (fun w : ℂ ↦ conj w) = Complex.conjCLE := rfl
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ ↦ conj w) z := by
    rw [hconj]
    exact Complex.conjCLE.differentiableAt.mdifferentiableAt
  rw [← zeroOnePart_ofComplexManifold_mfderiv_eq_zero_iff hu]
  exact zeroOnePart_ofComplexManifold_mfderiv_conj_ne_zero z

end Checks

end SmoothAlmostComplexStructure

end TauCeti
