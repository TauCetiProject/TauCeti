/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
public import TauCeti.LinearAlgebra.Alternating.RestrictScalars
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Sections of fibrewise continuous alternating maps

For a `C^n` vector bundle `V → M` with model fibre `F` and a normed space `G`, sections of the
bundle `fun x ↦ V x [⋀^ι]→L[𝕜] G` are `C^n` families of fibrewise continuous alternating maps.
Because the codomain `G` is fixed, reading a fibre map in the trivialization at `x₀` simply
precomposes it with `(trivializationAt F V x₀).symmL 𝕜 x`, with no base-set restriction
(`FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd`).

This file develops the basic section-level operations on such alternating bundles:
* **Empty-index / degree-zero identification** (`ContMDiffSection.alternatingIsEmptyLinearEquiv`,
  `ContMDiffSection.alternatingIsEmptyEquiv`): when `ι` is empty (such as `Fin 0`), sections of
  `fun x ↦ V x [⋀^ι]→L[𝕜] G` identify with `C^n` maps `M → G`.
* **Evaluation on sections** (`ContMDiffSection.evalSection`,
  `ContMDiffSection.evalAlternatingMap`): evaluating an alternating section pointwise on `C^n`
  sections of `V` produces a `C^n` function, and for `G = 𝕜` defines a `C^n(M)`-multilinear
  alternating map on `Cₛ^n⟮I; F, V⟯`.
* **Interior product** (`ContMDiffSection.curryLeft`): inserting a `C^n` section into the first
  slot via `ContinuousAlternatingMap.curryLeftTopological` preserves `C^n` regularity without
  requiring chosen norms on the fibres `V x`.
* **Multilinear tensoriality** (`ContMDiffSection.alternatingEquiv`): over a smooth
  finite-dimensional Hausdorff real manifold and a smooth finite-rank real vector bundle `V`,
  evaluation identifies smooth sections of `fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` `C^∞(M)`-linearly with
  `C^∞(M)`-multilinear alternating maps `Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Lemma 14.9.
* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §2.1 and §7.1.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace ContMDiffSection

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-! ### Degree transport -/

/-- Transporting an alternating bundle section across an equality of degrees reindexes the input
tuple by `Fin.cast`. -/
theorem cast_alternating_apply {p q : ℕ} (h : p = q)
    (φ : Cₛ^n⟮I; F [⋀^Fin p]→L[𝕜] G, fun x ↦ V x [⋀^Fin p]→L[𝕜] G⟯)
    (x : M) (v : Fin q → V x) :
    (LinearEquiv.cast (R := 𝕜)
      (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[𝕜] G, fun x ↦ V x [⋀^Fin r]→L[𝕜] G⟯) h φ) x v =
      φ x (v ∘ Fin.cast h) := by
  cases h
  rfl

/-! ### Empty-index / degree-zero sections -/

section IsEmpty

variable {ι : Type*} [Fintype ι] [IsEmpty ι]

variable (I F G n V ι) in
/-- When the index type `ι` is empty (for instance `ι = Fin 0`), sections of
`fun x ↦ V x [⋀^ι]→L[𝕜] G` identify `𝕜`-linearly with `C^n` maps `M → G`. -/
def alternatingIsEmptyLinearEquiv :
    Cₛ^n⟮I; F [⋀^ι]→L[𝕜] G, fun x ↦ V x [⋀^ι]→L[𝕜] G⟯ ≃ₗ[𝕜] C^n⟮I, M; 𝓘(𝕜, G), G⟯ where
  toFun φ :=
    ⟨fun x ↦ φ x 0, fun x₀ ↦ by
      have hφ := (contMDiffAt_section_iff x₀).1 (φ.contMDiff x₀)
      have heq : (fun x ↦ φ x 0) = fun x ↦
          (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F G ι).symm
            (trivializationAt (F [⋀^ι]→L[𝕜] G) (fun y ↦ V y [⋀^ι]→L[𝕜] G) x₀ ⟨x, φ x⟩).2 := by
        ext x
        rw [ContinuousAlternatingMap.constOfIsEmptyLIE_symm_apply,
          FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
          ContinuousAlternatingMap.compContinuousLinearMap_apply]
        exact congrArg (φ x) (Subsingleton.elim _ _)
      rw [heq]
      exact (contMDiffAt_const (c := (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F G
        ι).symm.toLinearIsometry.toContinuousLinearMap)).clm_apply hφ⟩
  invFun f :=
    { toFun x := ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V x) ι (f x)
      contMDiff_toFun x₀ := by
        rw [contMDiffAt_section_iff]
        have heq :
            (fun x ↦ (trivializationAt (F [⋀^ι]→L[𝕜] G) (fun y ↦ V y [⋀^ι]→L[𝕜] G) x₀
              ⟨x, ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V x) ι (f x)⟩).2) =
            fun x ↦ ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F G ι (f x) := by
          ext x v
          simp [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd]
        rw [heq]
        exact (contMDiffAt_const (c := (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F G
          ι).toLinearIsometry.toContinuousLinearMap)).clm_apply (f.contMDiff x₀) }
  left_inv φ := by
    ext x v
    exact congrArg (φ x) (Subsingleton.elim (0 : ι → V x) v)
  right_inv f := by
    ext x
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem alternatingIsEmptyLinearEquiv_apply
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] G, fun x ↦ V x [⋀^ι]→L[𝕜] G⟯) (x : M) :
    alternatingIsEmptyLinearEquiv I F G n V ι φ x = φ x 0 :=
  (rfl)

@[simp]
theorem alternatingIsEmptyLinearEquiv_symm_apply
    (f : C^n⟮I, M; 𝓘(𝕜, G), G⟯) (x : M) (v : ι → V x) :
    (alternatingIsEmptyLinearEquiv I F G n V ι).symm f x v = f x :=
  (rfl)

variable (I F n V ι) in
/-- Scalar-valued alternating bundle sections indexed by an empty type (such as `Fin 0`) identify
`C^n⟮I, M; 𝕜⟯`-linearly with scalar `C^n` functions on `M`. -/
def alternatingIsEmptyEquiv :
    Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun := alternatingIsEmptyLinearEquiv I F 𝕜 n V ι
  invFun := (alternatingIsEmptyLinearEquiv I F 𝕜 n V ι).symm
  left_inv := (alternatingIsEmptyLinearEquiv I F 𝕜 n V ι).left_inv
  right_inv := (alternatingIsEmptyLinearEquiv I F 𝕜 n V ι).right_inv
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp

@[simp]
theorem alternatingIsEmptyEquiv_apply
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) (x : M) :
    alternatingIsEmptyEquiv I F n V ι φ x = φ x 0 :=
  (rfl)

@[simp]
theorem alternatingIsEmptyEquiv_symm_apply
    (f : C^n⟮I, M; 𝕜⟯) (x : M) (v : ι → V x) :
    (alternatingIsEmptyEquiv I F n V ι).symm f x v = f x :=
  (rfl)

end IsEmpty

/-! ### Pointwise evaluation on `C^n` sections -/

section Eval

variable {ι : Type*} [Fintype ι]

/-- Pointwise evaluation of a `C^n` alternating bundle section on a tuple of `C^n` sections of `V`,
as a `C^n` map `M → G`. -/
def evalSection (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] G, fun x ↦ V x [⋀^ι]→L[𝕜] G⟯)
    (s : ι → Cₛ^n⟮I; F, V⟯) : C^n⟮I, M; 𝓘(𝕜, G), G⟯ :=
  ⟨fun x ↦ φ x (s · x), fun x₀ ↦ by
    let e := trivializationAt F V x₀
    have hφ := (contMDiffAt_section_iff x₀).1 (φ.contMDiff x₀)
    have hs (i : ι) : ContMDiffAt I 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s i x⟩).2) x₀ :=
      (contMDiffAt_section_iff x₀).1 ((s i).contMDiff x₀)
    refine (hφ.continuousAlternatingMap_apply hs).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x₀)] with x hx
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    rw [Function.comp_apply, e.symmL_apply hx, e.symm_apply_apply_mk hx]⟩

@[simp]
theorem evalSection_apply (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] G, fun x ↦ V x [⋀^ι]→L[𝕜] G⟯)
    (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    φ.evalSection s x = φ x (s · x) :=
  (rfl)

/-- A scalar-valued `C^n` alternating bundle section induces a `C^n⟮I, M; 𝕜⟯`-multilinear
alternating map on `C^n` sections of `V`. -/
def evalAlternatingMap (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s := φ.evalSection s
  map_update_add' := by
    intro _ s i a b
    ext x
    have hup (z : Cₛ^n⟮I; F, V⟯) :
        (fun j ↦ Function.update s i z j x) = Function.update (s · x) i (z x) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    simp [hup]
  map_update_smul' := by
    intro _ s i f a
    ext x
    have hup (z : Cₛ^n⟮I; F, V⟯) :
        (fun j ↦ Function.update s i z j x) = Function.update (s · x) i (z x) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    simp [hup]
  map_eq_zero_of_eq' s i j h hne := by
    ext x
    simp [evalSection_apply, (φ x).map_eq_zero_of_eq (s · x) (congrArg (· x) h) hne]

@[simp]
theorem evalAlternatingMap_apply (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯)
    (s : ι → Cₛ^n⟮I; F, V⟯) :
    φ.evalAlternatingMap s = φ.evalSection s :=
  (rfl)

theorem evalAlternatingMap_apply_apply (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯)
    (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    φ.evalAlternatingMap s x = φ x (s · x) :=
  (rfl)

variable (I F n V ι) in
/-- `ContMDiffSection.evalAlternatingMap` bundled as a `C^n⟮I, M; 𝕜⟯`-linear map. -/
def evalAlternatingLinearMap :
    Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      (Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯) where
  toFun := evalAlternatingMap
  map_add' φ₁ φ₂ := by ext s x; simp
  map_smul' f φ := by ext s x; simp

@[simp]
theorem evalAlternatingLinearMap_apply
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    evalAlternatingLinearMap I F n V ι φ = φ.evalAlternatingMap :=
  (rfl)

end Eval

/-! ### Smooth interior product -/

section CurryLeft

variable {k : ℕ}

/-- The interior product `ι_a φ` of an alternating bundle section `φ` of degree `k + 1` with a
section `a` of `V`, defined fibrewise via `ContinuousAlternatingMap.curryLeftTopological`. -/
def curryLeft
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    Cₛ^n⟮I; F [⋀^Fin k]→L[𝕜] G, fun x ↦ V x [⋀^Fin k]→L[𝕜] G⟯ where
  toFun x := (φ x).curryLeftTopological (a x)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_section_iff]
    let e := trivializationAt F V x₀
    have hφ := (contMDiffAt_section_iff x₀).1 (φ.contMDiff x₀)
    have ha := (contMDiffAt_section_iff x₀).1 (a.contMDiff x₀)
    let L : (F [⋀^Fin (k + 1)]→L[𝕜] G) →L[𝕜] F →L[𝕜] F [⋀^Fin k]→L[𝕜] G :=
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := 𝕜) (E := F) (F := G)
        (n := k)).toContinuousLinearMap
    have hmodel : ContMDiffAt I 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] G) n
        (fun x ↦ L (trivializationAt (F [⋀^Fin (k + 1)]→L[𝕜] G)
          (fun y ↦ V y [⋀^Fin (k + 1)]→L[𝕜] G) x₀ ⟨x, φ x⟩).2 (e ⟨x, a x⟩).2) x₀ :=
      ((contMDiffAt_const (c := L)).clm_apply hφ).clm_apply ha
    refine hmodel.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x₀)] with x hx
    ext v
    simp only [L, FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeftTopological_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      ContinuousAlternatingMap.curryLeftLI_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 1
    ext i
    cases i using Fin.cases with
    | zero =>
      simp only [Matrix.cons_val_zero, Function.comp_apply]
      rw [(trivializationAt F V x₀).symmL_apply hx, e.symm_apply_apply_mk hx]
    | succ j =>
      simp only [Matrix.cons_val_succ, Function.comp_apply]

@[simp]
theorem curryLeft_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) (x : M) :
    φ.curryLeft a x = (φ x).curryLeftTopological (a x) :=
  (rfl)

theorem curryLeft_apply_apply
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) (x : M) (v : Fin k → V x) :
    φ.curryLeft a x v = φ x (Matrix.vecCons (a x) v) :=
  ContinuousAlternatingMap.curryLeftTopological_apply_apply (φ x) (a x) v

@[simp]
theorem curryLeft_zero_left (a : Cₛ^n⟮I; F, V⟯) :
    (0 : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G,
      fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯).curryLeft a = 0 := by
  ext x v
  simp

@[simp]
theorem curryLeft_zero_right
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯) :
    φ.curryLeft 0 = 0 := by
  ext x v
  simp

@[simp]
theorem curryLeft_add_left
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ₁ + φ₂).curryLeft a = φ₁.curryLeft a + φ₂.curryLeft a := by
  ext x v
  simp

@[simp]
theorem curryLeft_add_right
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    φ.curryLeft (a + b) = φ.curryLeft a + φ.curryLeft b := by
  ext x v
  simp [map_add]

@[simp]
theorem curryLeft_smul_left (c : 𝕜)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (c • φ).curryLeft a = c • φ.curryLeft a := by
  ext x v
  simp

@[simp]
theorem curryLeft_fun_smul_left (f : C^n⟮I, M; 𝕜⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (f • φ).curryLeft a = f • φ.curryLeft a := by
  ext x v
  simp

@[simp]
theorem curryLeft_smul_right (c : 𝕜)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    φ.curryLeft (c • a) = c • φ.curryLeft a := by
  ext x v
  simp [map_smul]

@[simp]
theorem curryLeft_fun_smul_right (f : C^n⟮I, M; 𝕜⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    φ.curryLeft (f • a) = f • φ.curryLeft a := by
  ext x v
  simp [map_smul]

@[simp]
theorem curryLeft_neg_left
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (-φ).curryLeft a = -φ.curryLeft a := by
  ext x v
  simp

@[simp]
theorem curryLeft_neg_right
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    φ.curryLeft (-a) = -φ.curryLeft a := by
  ext x v
  simp [map_neg]

@[simp]
theorem curryLeft_sub_left
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ₁ - φ₂).curryLeft a = φ₁.curryLeft a - φ₂.curryLeft a := by
  ext x v
  simp

@[simp]
theorem curryLeft_sub_right
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] G⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    φ.curryLeft (a - b) = φ.curryLeft a - φ.curryLeft b := by
  ext x v
  simp [map_sub]

/-- Inserting the same section twice vanishes. -/
@[simp]
theorem curryLeft_same
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 2)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 2)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.curryLeft a).curryLeft a = 0 := by
  ext x v
  simp

/-- Interior products with two sections anticommute. -/
theorem curryLeft_curryLeft_eq_neg
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 2)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (k + 2)]→L[𝕜] G⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    (φ.curryLeft a).curryLeft b = -(φ.curryLeft b).curryLeft a := by
  have h := φ.curryLeft_same (a + b)
  simp only [curryLeft_add_right, curryLeft_add_left, curryLeft_same, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `ContMDiffSection.curryLeft` commutes with `LinearEquiv.cast` across successor degree
equalities. -/
theorem curryLeft_cast_alternating {p q : ℕ} (h : p + 1 = q + 1)
    (φ : Cₛ^n⟮I; F [⋀^Fin (p + 1)]→L[𝕜] G, fun x ↦ V x [⋀^Fin (p + 1)]→L[𝕜] G⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    ContMDiffSection.curryLeft
      (LinearEquiv.cast (R := 𝕜)
        (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[𝕜] G, fun x ↦ V x [⋀^Fin r]→L[𝕜] G⟯) h φ) a =
      LinearEquiv.cast (R := 𝕜)
        (M := fun r : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin r]→L[𝕜] G, fun x ↦ V x [⋀^Fin r]→L[𝕜] G⟯)
        (Nat.succ.inj h) (φ.curryLeft a) := by
  obtain rfl := Nat.succ.inj h
  rfl

/-- Evaluation on sections intertwines `ContMDiffSection.curryLeft` with
`AlternatingMap.curryLeft`. -/
@[simp]
theorem evalAlternatingMap_curryLeft
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] 𝕜, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] 𝕜⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.curryLeft a).evalAlternatingMap = φ.evalAlternatingMap.curryLeft a := by
  ext s x
  simp only [evalAlternatingMap_apply_apply, curryLeft_apply_apply,
    AlternatingMap.curryLeft_apply_apply]
  congr 1
  ext i
  cases i using Fin.cases <;> simp

end CurryLeft

end General

/-! ### Separation by global sections and multilinear tensoriality -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Two `C^n` alternating bundle sections of positive degree are equal as soon as all their
interior products with global `C^n` sections agree. -/
theorem curryLeft_injective {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n F V I] {k : ℕ}
    {φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] G, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] G⟯}
    (h : ∀ a : Cₛ^n⟮I; F, V⟯, φ₁.curryLeft a = φ₂.curryLeft a) :
    φ₁ = φ₂ := by
  ext x v
  obtain ⟨a, ha⟩ := evalLinearMap_surjective (I := I) (F := F) (V := V) n x (v 0)
  rw [evalLinearMap_apply] at ha
  have hcons : Matrix.vecCons (a x) (Fin.tail v) = v := by
    ext i
    cases i using Fin.cases with
    | zero => exact ha
    | succ j => rfl
  rw [← hcons, ← curryLeft_apply_apply, h a, curryLeft_apply_apply]

section Tensoriality

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- If a section `u` vanishes at `x`, any `C^∞(M)`-multilinear alternating map `Φ` on smooth
sections vanishes at `x` when `u` is inserted into one slot. -/
private theorem alternatingMap_update_apply_eq_zero_of_apply_eq_zero {ι : Type*} [DecidableEq ι]
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (w : ι → Cₛ^∞⟮I; F, V⟯) (i : ι) {x : M} {u : Cₛ^∞⟮I; F, V⟯} (hu : u x = 0) :
    Φ (Function.update w i u) x = 0 := by
  have hmem := TauCeti.mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero (I := I) hu
  refine Submodule.smul_induction_on
    (p := fun z : Cₛ^∞⟮I; F, V⟯ ↦ Φ (Function.update w i z) x = 0) hmem ?_ ?_
  · intro f hf t _
    simp [Φ.map_update_smul, TauCeti.mem_smoothVanishingIdeal_iff.mp hf]
  · intro s t hs ht
    simp [Φ.map_update_add, hs, ht]

/-- **Multilinear section tensoriality**: the value at `x` of a `C^∞(M)`-multilinear alternating
map on smooth sections of a finite-rank bundle depends only on the values of its arguments at
`x`. -/
theorem alternatingMap_apply_eq_of_eval_eq {ι : Type*} [Finite ι]
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    {s t : ι → Cₛ^∞⟮I; F, V⟯} {x : M} (hst : ∀ i, s i x = t i x) :
    Φ s x = Φ t x := by
  classical
  cases nonempty_fintype ι
  -- Induct over a finite set `q` of indices outside which `s` and `t` already agree globally.
  suffices ∀ (q : Finset ι) (s' : ι → Cₛ^∞⟮I; F, V⟯),
      (∀ i ∈ q, s' i x = t i x) → (∀ i ∉ q, s' i = t i) → Φ s' x = Φ t x from
    this Finset.univ s (fun i _ ↦ hst i) (fun _ h ↦ (h (Finset.mem_univ _)).elim)
  intro q
  induction q using Finset.induction_on with
  | empty =>
    intro s' _ hout
    exact congrArg (Φ · x) (funext fun i ↦ hout i (Finset.notMem_empty i))
  | @insert j q hj ih =>
    intro s' hin hout
    let s'' := Function.update s' j (t j)
    have hdiff : s' = Function.update s'' j (t j + (s' j - t j)) := by
      ext k
      by_cases hk : k = j <;> simp [s'', hk]
    have hzero : Φ (Function.update s'' j (s' j - t j)) x = 0 :=
      alternatingMap_update_apply_eq_zero_of_apply_eq_zero Φ s'' j
        (by simp [hin j (Finset.mem_insert_self j q)])
    have hstep : Φ s' x = Φ s'' x := by
      conv_lhs => rw [hdiff]
      rw [Φ.map_update_add, ContMDiffMap.coe_add, Pi.add_apply, hzero, add_zero]
      congr 2
      ext k
      by_cases hk : k = j <;> simp [s'', hk]
    rw [hstep]
    refine ih s'' (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · simp only [s'', Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      exact hin i (Finset.mem_insert_of_mem hi)
    · rcases eq_or_ne i j with rfl | hij
      · simp [s'']
      · simp only [s'', Function.update_of_ne hij]
        exact hout i fun hmem ↦ hi ((Finset.mem_insert.1 hmem).resolve_left hij)

/-- Pointwise fibre alternating map reconstructed from a `C^∞(M)`-multilinear alternating map `Φ`
on smooth sections, by splitting evaluation at `x` and transporting continuity from the
finite-dimensional model fibre `F`. -/
private def fiberAlternatingOfSections {ι' : Type*} [Finite ι']
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι']→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) (x : M) :
    V x [⋀^ι']→L[ℝ] ℝ :=
  let hsurj := LinearMap.range_eq_top.2 (evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x)
  let Lx : V x →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
    Classical.choose ((evalLinearMap I F ∞ V x).exists_rightInverse_of_surjective hsurj)
  let ex := trivializationAt F V x
  let βx : F [⋀^ι']→ₗ[ℝ] ℝ :=
    ((ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ).toLinearMap.compAlternatingMap
      (Φ.restrictScalars ℝ)).compLinearMap (Lx.comp (ex.symmL ℝ x).toLinearMap)
  (AlternatingMap.toContinuousAlternatingMap βx).compContinuousLinearMap
    (ex.continuousLinearMapAt ℝ x)

private theorem fiberAlternatingOfSections_eval {ι' : Type*} [Finite ι']
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι']→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : ι' → Cₛ^∞⟮I; F, V⟯) (x : M) :
    fiberAlternatingOfSections Φ x (s · x) = Φ s x := by
  let hsurj := LinearMap.range_eq_top.2 (evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x)
  let Lx : V x →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
    Classical.choose ((evalLinearMap I F ∞ V x).exists_rightInverse_of_surjective hsurj)
  have hLx (v : V x) : Lx v x = v := by
    simpa only [LinearMap.comp_apply, evalLinearMap_apply, LinearMap.id_apply] using
      LinearMap.congr_fun
        (Classical.choose_spec ((evalLinearMap I F ∞ V x).exists_rightInverse_of_surjective hsurj))
        v
  let ex := trivializationAt F V x
  have hx : x ∈ ex.baseSet := mem_baseSet_trivializationAt F V x
  change AlternatingMap.toContinuousAlternatingMap
      (((ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ).toLinearMap.compAlternatingMap
        (Φ.restrictScalars ℝ)).compLinearMap (Lx.comp (ex.symmL ℝ x).toLinearMap))
      (fun i ↦ ex.continuousLinearMapAt ℝ x (s i x)) = Φ s x
  rw [AlternatingMap.coe_toContinuousAlternatingMap, AlternatingMap.compLinearMap_apply,
    LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply, ContMDiffMap.evalAlgHom_apply,
    AlternatingMap.restrictScalars_apply]
  refine alternatingMap_apply_eq_of_eval_eq Φ fun i ↦ ?_
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hLx, ex.symmL_continuousLinearMapAt hx]

section Fintype

variable {ι : Type*} [Fintype ι]

/-- Reconstruct a smooth section of `fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` from a `C^∞(M)`-multilinear
alternating map on global smooth sections of `V`. -/
def ofSectionAlternatingMap
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    Cₛ^∞⟮I; F [⋀^ι]→L[ℝ] ℝ, fun x ↦ V x [⋀^ι]→L[ℝ] ℝ⟯ where
  toFun := fiberAlternatingOfSections Φ
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_section_iff]
    let e := trivializationAt F V x₀
    have hmem : e.baseSet ∈ 𝓝 x₀ := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x₀)
    -- In coordinates at `x₀`, smoothness reduces by `contMDiffAt_continuousAlternatingMap_apply`
    -- to evaluating on each constant tuple `v : ι → F`, realized near `x₀` by cut-off sections.
    refine (TauCeti.contMDiffAt_continuousAlternatingMap_apply (𝕜 := ℝ)).2 fun v ↦ ?_
    obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.mp hmem
    let s (i : ι) : Cₛ^∞⟮I; F, V⟯ :=
      ⟨(ρ : M → ℝ) • fun y ↦ e.symm y (v i),
        ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet hρ
          (TauCeti.Manifold.contMDiffOn_symm_baseSet (v i))⟩
    refine (Φ s).contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [ρ.eventuallyEq_one, hmem] with y hρy hy
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have h1 : (ρ : M → ℝ) y = 1 := hρy
    have hsy : (e.symmL ℝ y ∘ v) = (s · y) := by
      ext i
      change e.symmL ℝ y (v i) = (ρ : M → ℝ) y • e.symm y (v i)
      rw [h1, one_smul, e.symmL_apply hy]
    rw [hsy, fiberAlternatingOfSections_eval]

@[simp]
theorem ofSectionAlternatingMap_eval
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : ι → Cₛ^∞⟮I; F, V⟯) (x : M) :
    ofSectionAlternatingMap Φ x (s · x) = Φ s x :=
  fiberAlternatingOfSections_eval Φ s x

variable (I F V ι) in
/-- **Tensoriality equivalence for alternating sections**: over a smooth finite-dimensional
Hausdorff real manifold and a smooth finite-rank real vector bundle `V`, evaluation identifies
smooth sections of `fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` `C^∞(M)`-linearly with `C^∞(M)`-multilinear
alternating maps on smooth sections of `V`. -/
def alternatingEquiv :
    Cₛ^∞⟮I; F [⋀^ι]→L[ℝ] ℝ, fun x ↦ V x [⋀^ι]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) where
  toFun := evalAlternatingLinearMap I F ∞ V ι
  invFun := ofSectionAlternatingMap
  left_inv φ := by
    ext x v
    choose s hs using fun i ↦ evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x (v i)
    have hv : (s · x) = v := funext fun i ↦ by simpa only [evalLinearMap_apply] using hs i
    rw [← hv, ofSectionAlternatingMap_eval, evalAlternatingLinearMap_apply,
      evalAlternatingMap_apply_apply]
  right_inv Φ := by
    ext s x
    rw [evalAlternatingLinearMap_apply, evalAlternatingMap_apply_apply]
    exact ofSectionAlternatingMap_eval Φ s x
  map_add' := (evalAlternatingLinearMap I F ∞ V ι).map_add
  map_smul' := (evalAlternatingLinearMap I F ∞ V ι).map_smul

@[simp]
theorem alternatingEquiv_apply
    (φ : Cₛ^∞⟮I; F [⋀^ι]→L[ℝ] ℝ, fun x ↦ V x [⋀^ι]→L[ℝ] ℝ⟯) :
    alternatingEquiv I F V ι φ = φ.evalAlternatingMap :=
  (rfl)

@[simp]
theorem alternatingEquiv_symm_apply_eval
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : ι → Cₛ^∞⟮I; F, V⟯) (x : M) :
    (alternatingEquiv I F V ι).symm Φ x (s · x) = Φ s x :=
  ofSectionAlternatingMap_eval Φ s x

end Fintype

@[simp]
theorem alternatingEquiv_symm_curryLeft {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) :
    ((alternatingEquiv I F V (Fin (k + 1))).symm Φ).curryLeft a =
      (alternatingEquiv I F V (Fin k)).symm (Φ.curryLeft a) :=
  (alternatingEquiv I F V (Fin k)).injective <| by
    rw [alternatingEquiv_apply, evalAlternatingMap_curryLeft, ← alternatingEquiv_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end Tensoriality

end Real

end ContMDiffSection
