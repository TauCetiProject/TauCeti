/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.LinearAlgebra.Alternating.RestrictScalars
import TauCeti.Topology.Algebra.Module.Alternating.Curry
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Sections of bundles of continuous alternating maps

For a vector bundle `V → M` with model fibre `F`, the continuous alternating maps
`V x [⋀^ι]→L[𝕜] 𝕜` form a vector bundle over `M` (viewing the scalar codomain as the trivial
bundle `Bundle.Trivial M 𝕜`). This file provides the algebraic and calculus operations on
`ContMDiffSection` needed to treat these sections as intrinsic cochains on `V`:

* evaluation `ContMDiffSection.evalAlternating` on tuples of `C^n` sections of `V`, bundled as a
  `C^n(M)`-multilinear alternating map (and evaluation extensionality
  `ContMDiffSection.eq_of_evalAlternating_eq` for `n ≤ ∞`);
* the degree-zero `C^n(M)`-linear equivalence `ContMDiffSection.constOfIsEmptyEquiv` between scalar
  functions `C^n⟮I, M; 𝕜⟯` and sections of `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜` for `[IsEmpty ι]`;
* the interior product `ContMDiffSection.interior` contracting the first slot of a
  bundle-valued alternating section with a section of `V`, intertwining evaluation with
  `AlternatingMap.curryLeft`, together with `ContMDiffSection.apply_eq_interior_tail`;
* the smooth fibrewise wedge product `ContMDiffSection.wedge` of real scalar alternating sections,
  together with its graded commutativity, associativity, and interior-product antiderivation laws
  on sections via `LinearEquiv.cast`;
* the tensoriality equivalence `ContMDiffSection.evalAlternatingEquiv` identifying `C^n` sections
  of `fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` on a finite-rank `C^n` real vector bundle over a
  finite-dimensional Hausdorff `C^n` manifold (`1 ≤ n ≤ ∞`) with `C^n(M)`-multilinear alternating
  maps `Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; ℝ⟯] C^n⟮I, M; ℝ⟯`.

The coordinate-smoothness proof for `ContMDiffSection.wedge` delegates directly to
`ContMDiffAt.pairedWedge_bundle` from
`TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` and
`TauCeti.contMDiff_const_bundlePairing`, and `ContMDiffSection.ofAlternating` combines
`TauCeti.Manifold.eq_of_contMDiff_tensorial` with `ContMDiffSection.liftModel` from
`TauCeti.Geometry.Manifold.VectorBundle.Section.Extension`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapters 12 and 14.
* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3 and §7.1.
-/

public section

open Bundle Function
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

section General

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

local notation "Ω[" ι "]" => Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯

/-! ### Evaluation on sections -/

private def evalSectionFun {ι : Type*} [Fintype ι] (φ : Ω[ι]) (s : ι → Cₛ^n⟮I; F, V⟯) :
    C^n⟮I, M; 𝕜⟯ :=
  ⟨fun x ↦ φ x (fun i ↦ s i x),
    (Bundle.Trivial.contMDiff_mk_iff.1
      (φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ (s i).contMDiff)).2⟩

@[simp]
private theorem evalSectionFun_apply {ι : Type*} [Fintype ι] (φ : Ω[ι])
    (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    evalSectionFun φ s x = φ x (fun i ↦ s i x) := (rfl)

/-- Evaluate a `C^n` section of the scalar alternating-map bundle `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜` on
tuples of `C^n` sections of `V`, as a `C^n(M)`-multilinear alternating map to `C^n` scalar
functions. -/
def evalAlternating {ι : Type*} [Fintype ι] (φ : Ω[ι]) :
    Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun := evalSectionFun φ
  map_update_add' := fun [DecidableEq ι] s i u v ↦ by
    ext x
    have hupd (t : Cₛ^n⟮I; F, V⟯) : (fun j ↦ update s i t j x) = update (fun j ↦ s j x) i (t x) :=
      funext (apply_update (fun _ (w : Cₛ^n⟮I; F, V⟯) ↦ w x) s i t)
    simp [hupd]
  map_update_smul' := fun [DecidableEq ι] s i f u ↦ by
    ext x
    have hupd (t : Cₛ^n⟮I; F, V⟯) : (fun j ↦ update s i t j x) = update (fun j ↦ s j x) i (t x) :=
      funext (apply_update (fun _ (w : Cₛ^n⟮I; F, V⟯) ↦ w x) s i t)
    simp [hupd, smul_eq_mul]
  map_eq_zero_of_eq' s i j hij hne := by
    ext x
    exact (φ x).map_eq_zero_of_eq (fun r ↦ s r x) (i := i) (j := j) congr(($hij) x) hne

@[simp]
theorem evalAlternating_apply {ι : Type*} [Fintype ι] (φ : Ω[ι])
    (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    φ.evalAlternating s x = φ x (fun i ↦ s i x) := (rfl)

@[simp]
theorem evalAlternating_zero {ι : Type*} [Fintype ι] :
    (0 : Ω[ι]).evalAlternating = 0 := by ext s x; simp

@[simp]
theorem evalAlternating_add {ι : Type*} [Fintype ι] (φ ψ : Ω[ι]) :
    (φ + ψ).evalAlternating = φ.evalAlternating + ψ.evalAlternating := by ext s x; simp

@[simp]
theorem evalAlternating_smul {ι : Type*} [Fintype ι] (f : C^n⟮I, M; 𝕜⟯) (φ : Ω[ι]) :
    (f • φ).evalAlternating = f • φ.evalAlternating := by ext s x; simp

@[simp]
theorem evalAlternating_const_smul {ι : Type*} [Fintype ι] (c : 𝕜) (φ : Ω[ι]) :
    (c • φ).evalAlternating = c • φ.evalAlternating := by ext s x; simp

@[simp]
theorem evalAlternating_neg {ι : Type*} [Fintype ι] (φ : Ω[ι]) :
    (-φ).evalAlternating = -φ.evalAlternating := by ext s x; simp

@[simp]
theorem evalAlternating_sub {ι : Type*} [Fintype ι] (φ ψ : Ω[ι]) :
    (φ - ψ).evalAlternating = φ.evalAlternating - ψ.evalAlternating := by ext s x; simp

variable (I F n V) in
/-- `ContMDiffSection.evalAlternating` bundled as a `C^n(M)`-linear map. -/
def evalAlternatingLinear (ι : Type*) [Fintype ι] :
    Ω[ι] →ₗ[C^n⟮I, M; 𝕜⟯] (Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯) where
  toFun := evalAlternating
  map_add' := evalAlternating_add
  map_smul' := evalAlternating_smul

@[simp]
theorem evalAlternatingLinear_apply {ι : Type*} [Fintype ι] (φ : Ω[ι]) :
    evalAlternatingLinear I F n V ι φ = φ.evalAlternating := (rfl)

/-! ### Degree zero -/

noncomputable section DegreeZero

variable (I F n V)

/-- Package `x ↦ constOfIsEmpty 𝕜 (V x) ι (f x)` as a `C^n` section. -/
private def constOfIsEmptySection (ι : Type*) [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) : Ω[ι] where
  toFun x := ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V x) ι (f x)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    let e : 𝕜 →L[𝕜] F [⋀^ι]→L[𝕜] 𝕜 :=
      (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 F 𝕜 ι).toContinuousLinearEquiv
        |>.toContinuousLinearMap
    have hcoord :
        (fun y ↦ ContinuousAlternatingMap.inCoordinates F 𝕜
          (E₁ := V) (E₂ := Bundle.Trivial M 𝕜) x₀ y x₀ y
          (ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V y) ι (f y))) =
          fun y ↦ e (f y) := by
      ext y w; simp [e, ContinuousAlternatingMap.inCoordinates]
    rw [hcoord]
    exact e.contMDiffAt.comp x₀ f.contMDiff.contMDiffAt

@[simp]
private theorem constOfIsEmptySection_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) (x : M) (v : ι → V x) :
    constOfIsEmptySection I F n V ι f x v = f x := (rfl)

/-- In degree zero (`[IsEmpty ι]`), `C^n` scalar functions identify `C^n(M)`-linearly with `C^n`
sections of `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜`. -/
def constOfIsEmptyEquiv (ι : Type*) [Fintype ι] [IsEmpty ι] :
    C^n⟮I, M; 𝕜⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] Ω[ι] where
  toFun := constOfIsEmptySection I F n V ι
  invFun φ :=
    ⟨fun x ↦ φ x isEmptyElim,
      (Bundle.Trivial.contMDiff_mk_iff.1
        (φ.contMDiff.continuousAlternatingMap_bundle_apply fun i : ι ↦ isEmptyElim i)).2⟩
  map_add' f g := by ext x v; simp
  map_smul' f g := by ext x v; simp [smul_eq_mul]
  left_inv f := by ext x; simp
  right_inv φ := by ext x v; rw [Subsingleton.elim v isEmptyElim]; rfl

variable {I F n V}

@[simp]
theorem constOfIsEmptyEquiv_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) (x : M) (v : ι → V x) :
    constOfIsEmptyEquiv I F n V ι f x v = f x := (rfl)

@[simp]
theorem constOfIsEmptyEquiv_symm_apply {ι : Type*} [Fintype ι] [IsEmpty ι] (φ : Ω[ι]) (x : M) :
    (constOfIsEmptyEquiv I F n V ι).symm φ x = φ x isEmptyElim := (rfl)

@[simp]
theorem evalAlternating_constOfIsEmptyEquiv {ι : Type*} [Fintype ι] [IsEmpty ι] (f : C^n⟮I, M; 𝕜⟯) :
    (constOfIsEmptyEquiv I F n V ι f).evalAlternating =
      AlternatingMap.constOfIsEmpty C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ ι f := by ext s x; rfl

end DegreeZero

end General

/-! ### Interior product -/

noncomputable section Interior

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F F₂ : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {n : ℕ∞ω} {V V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

local notation "Ω₂[" k "]" => Cₛ^n⟮I; F [⋀^Fin k]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin k]→L[𝕜] V₂ x⟯

/-- Evaluating a degree-transported `C^n` alternating section on a tuple transports the tuple by
`Fin.cast h`. -/
theorem cast_apply {k l : ℕ} (h : k = l) (φ : Ω₂[k]) (x : M) (v : Fin l → V x) :
    LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯) (M := fun q : ℕ ↦ Ω₂[q]) h φ x v =
      φ x (v ∘ Fin.cast h) := by
  subst h; rfl

/-- Pointwise evaluation of `LinearEquiv.cast h φ + c • ψ`. -/
theorem add_cast_smul_apply {k l : ℕ} (h : k = l) (φ : Ω₂[k]) (c : 𝕜) (ψ : Ω₂[l])
    (x : M) (v : Fin l → V x) :
    (LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯) (M := fun q : ℕ ↦ Ω₂[q]) h φ + c • ψ) x v =
      φ x (v ∘ Fin.cast h) + c • ψ x v := by
  simp only [coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, cast_apply,
    coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]

/-- Contract the first argument of a `C^n` section of `fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x`
with a `C^n` section `a` of `V`. -/
def interior {k : ℕ} (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) : Ω₂[k] where
  toFun x := (φ x).curryLeftTopological (a x)
  contMDiff_toFun x₀ := by
    have hφ := (contMDiffAt_continuousAlternatingMap_bundle
      (E₁ := V) (E₂ := V₂) _).1 (φ.contMDiff x₀)
    have ha := (contMDiffAt_section_iff x₀).1 (a.contMDiff x₀)
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    refine (((ContinuousAlternatingMap.curryLeftLI (𝕜 := 𝕜) (E := F) (F := F₂)
      (n := k)).toContinuousLinearMap.contDiff.comp_contMDiffAt hφ.2).clm_apply
        ha).congr_of_eventuallyEq ?_
    let e₁ := FiberBundle.trivializationAt F V x₀
    filter_upwards [e₁.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V x₀)]
      with y hy
    ext w
    have hcons :
        (fun i : Fin (k + 1) ↦ e₁.symmL 𝕜 y (Matrix.vecCons (e₁ ⟨y, a y⟩).2 w i)) =
          Matrix.vecCons (a y) (fun j ↦ e₁.symmL 𝕜 y (w j)) := by
      ext i
      refine Fin.cases ?_ (fun _ ↦ rfl) i
      simp [e₁, Trivialization.symmL_apply e₁ hy, e₁.symm_apply_apply_mk hy]
    simp [ContinuousAlternatingMap.inCoordinates, Function.comp_def, e₁, hcons]

@[simp]
theorem interior_apply {k : ℕ} (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) (x : M) (v : Fin k → V x) :
    φ.interior a x v = φ x (Matrix.vecCons (a x) v) :=
  ContinuousAlternatingMap.curryLeftTopological_apply_apply (φ x) (a x) v

/-- Evaluating a `C^n` alternating section at `x` on `v : Fin (k + 1) → V x` equals contracting
first with any `C^n` section `a` satisfying `a x = v 0` and evaluating on `Fin.tail v`. -/
theorem apply_eq_interior_tail {k : ℕ} (φ : Ω₂[k + 1]) {a : Cₛ^n⟮I; F, V⟯}
    {x : M} {v : Fin (k + 1) → V x} (ha : a x = v 0) :
    φ x v = φ.interior a x (Fin.tail v) := by
  rw [interior_apply]
  exact congrArg (φ x) (funext fun i ↦ Fin.cases ha.symm (fun _ ↦ rfl) i)

/-- Interior product commutes with degree transport. -/
theorem interior_cast {k l : ℕ} (h : k + 1 = l + 1) (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯) (M := fun q : ℕ ↦ Ω₂[q]) h φ).interior a =
      LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯) (M := fun q : ℕ ↦ Ω₂[q]) (Nat.succ.inj h)
        (φ.interior a) := by
  obtain rfl : k = l := Nat.succ.inj h
  rfl

@[simp]
theorem interior_zero_left {k : ℕ} (a : Cₛ^n⟮I; F, V⟯) :
    (0 : Ω₂[k + 1]).interior a = 0 := by ext x v; simp

@[simp]
theorem interior_zero_right {k : ℕ} (φ : Ω₂[k + 1]) : φ.interior 0 = 0 := by
  ext x v; exact congr($((φ x).curryLeftTopological.map_zero) v)

@[simp]
theorem interior_add_left {k : ℕ} (φ ψ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ + ψ).interior a = φ.interior a + ψ.interior a := by ext x v; simp

@[simp]
theorem interior_add_right {k : ℕ} (φ : Ω₂[k + 1]) (a b : Cₛ^n⟮I; F, V⟯) :
    φ.interior (a + b) = φ.interior a + φ.interior b := by
  ext x v; exact congr($((φ x).curryLeftTopological.map_add (a x) (b x)) v)

@[simp]
theorem interior_smul_left {k : ℕ} (f : C^n⟮I, M; 𝕜⟯) (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (f • φ).interior a = f • φ.interior a := by ext x v; simp

@[simp]
theorem interior_smul_right {k : ℕ} (f : C^n⟮I, M; 𝕜⟯) (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    φ.interior (f • a) = f • φ.interior a := by
  ext x v
  simpa only [ContinuousAlternatingMap.curryLeftTopological_apply_apply, interior_apply,
    smul_apply, ContinuousAlternatingMap.smul_apply] using
    congr($((φ x).curryLeftTopological.map_smul (f x) (a x)) v)

@[simp]
theorem interior_const_smul_left {k : ℕ} (c : 𝕜) (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (c • φ).interior a = c • φ.interior a := by ext x v; simp

@[simp]
theorem interior_const_smul_right {k : ℕ} (c : 𝕜) (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    φ.interior (c • a) = c • φ.interior a := by
  ext x v; exact congr($((φ x).curryLeftTopological.map_smul c (a x)) v)

@[simp]
theorem interior_neg_left {k : ℕ} (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (-φ).interior a = -φ.interior a := by ext x v; simp

@[simp]
theorem interior_neg_right {k : ℕ} (φ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    φ.interior (-a) = -φ.interior a := by
  ext x v; exact congr($((φ x).curryLeftTopological.map_neg (a x)) v)

@[simp]
theorem interior_sub_left {k : ℕ} (φ ψ : Ω₂[k + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ - ψ).interior a = φ.interior a - ψ.interior a := by ext x v; simp

@[simp]
theorem interior_sub_right {k : ℕ} (φ : Ω₂[k + 1]) (a b : Cₛ^n⟮I; F, V⟯) :
    φ.interior (a - b) = φ.interior a - φ.interior b := by
  rw [sub_eq_add_neg, interior_add_right, interior_neg_right, sub_eq_add_neg]

/-- Contracting twice with the same section gives zero. -/
@[simp]
theorem interior_interior_self {k : ℕ} (φ : Ω₂[k + 2]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ.interior a).interior a = 0 := by
  ext x v; exact congr($((φ x).curryLeftTopological_curryLeftTopological (a x)) v)

/-- Interior products anticommute: `ι_b (ι_a φ) = -ι_a (ι_b φ)`. -/
theorem interior_interior_comm {k : ℕ} (φ : Ω₂[k + 2]) (a b : Cₛ^n⟮I; F, V⟯) :
    (φ.interior a).interior b = -(φ.interior b).interior a := by
  have h := interior_interior_self φ (a + b)
  simp only [interior_add_left, interior_add_right, interior_interior_self,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Evaluation intertwines `ContMDiffSection.interior` with `AlternatingMap.curryLeft`. -/
@[simp]
theorem evalAlternating_interior {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] 𝕜, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] 𝕜⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.interior a).evalAlternating = φ.evalAlternating.curryLeft a := by
  ext s x
  simp only [evalAlternating_apply, interior_apply, AlternatingMap.curryLeft_apply_apply]
  exact congrArg (φ x) (funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i)

end Interior

section

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Evaluating a degree-transported `C^n` scalar alternating section on a tuple of `C^n`
sections transports the tuple by `Fin.cast h`. -/
theorem evalAlternating_cast {k l : ℕ} (h : k = l)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[𝕜] 𝕜, fun x ↦ V x [⋀^Fin k]→L[𝕜] 𝕜⟯)
    (s : Fin l → Cₛ^n⟮I; F, V⟯) :
    (LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
        (M := fun q : ℕ ↦ Cₛ^n⟮I; F [⋀^Fin q]→L[𝕜] 𝕜, fun x ↦ V x [⋀^Fin q]→L[𝕜] 𝕜⟯) h
        φ).evalAlternating s =
      φ.evalAlternating (s ∘ Fin.cast h) := by
  subst h; rfl

end

/-! ### Fibrewise wedge product -/

noncomputable section Wedge

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

local notation "Ω[" k "]" => Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯

/-- The `C^n` fibrewise wedge product of two `C^n` scalar alternating sections on a real vector
bundle `V`, normalized by `1 / (k! l!)` so that the wedge of two `1`-cochains is their two-term
determinant. No finite-dimensionality, Hausdorff, or manifold-smoothness assumptions are needed. -/
def wedge {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) : Ω[k + l] where
  toFun x :=
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x)
  contMDiff_toFun x₀ :=
    ContMDiffAt.pairedWedge_bundle (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂)
      (TauCeti.contMDiff_const_bundlePairing (ContinuousLinearMap.mul ℝ ℝ) x₀)
      (φ.contMDiff x₀) (ψ.contMDiff x₀)

theorem wedge_apply {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (x : M) :
    φ.wedge ψ x =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) := (rfl)

/-- Pointwise signed-permutation expansion of the fibrewise wedge product. -/
theorem wedge_apply_sum {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (x : M) (v : Fin (k + l) → V x) :
    φ.wedge ψ x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ x (fun i ↦ v (σ (Fin.castAdd l i))) *
            ψ x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simpa only [wedge_apply, ContinuousLinearMap.mul_apply'] using
    ContinuousAlternatingMap.pairedWedge_apply (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v

/-- Evaluation of `φ.wedge ψ` on a tuple of `C^n` sections as a signed sum of products in
`C^n⟮I, M; ℝ⟯`. -/
theorem evalAlternating_wedge_apply {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l])
    (s : Fin (k + l) → Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).evalAlternating s =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ.evalAlternating (fun i ↦ s (σ (Fin.castAdd l i))) *
            ψ.evalAlternating (fun j ↦ s (σ (Fin.natAdd k j)))) := by
  ext x
  rw [← ContMDiffMap.evalAlgHom_apply ℝ x, ← ContMDiffMap.evalAlgHom_apply ℝ x]
  simp [map_smul, map_sum, evalAlternating_apply, wedge_apply_sum]

@[simp]
theorem wedge_zero_left {k l : ℕ} (ψ : Ω[l]) : (0 : Ω[k]).wedge ψ = 0 := by
  ext x v; simp [wedge_apply, ContinuousAlternatingMap.pairedWedge_zero_left]

@[simp]
theorem wedge_zero_right {k l : ℕ} (φ : Ω[k]) : φ.wedge (0 : Ω[l]) = 0 := by
  ext x v; simp [wedge_apply, ContinuousAlternatingMap.pairedWedge_zero_right]

@[simp]
theorem wedge_add_left {k l : ℕ} (φ₁ φ₂ : Ω[k]) (ψ : Ω[l]) :
    (φ₁ + φ₂).wedge ψ = φ₁.wedge ψ + φ₂.wedge ψ := by
  ext x v
  exact congr($(ContinuousAlternatingMap.pairedWedge_add_left (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ₁ x) (φ₂ x) (ψ x)) v)

@[simp]
theorem wedge_add_right {k l : ℕ} (φ : Ω[k]) (ψ₁ ψ₂ : Ω[l]) :
    φ.wedge (ψ₁ + ψ₂) = φ.wedge ψ₁ + φ.wedge ψ₂ := by
  ext x v
  exact congr($(ContinuousAlternatingMap.pairedWedge_add_right (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ₁ x) (ψ₂ x)) v)

@[simp]
theorem wedge_smul_left {k l : ℕ} (f : C^n⟮I, M; ℝ⟯) (φ : Ω[k]) (ψ : Ω[l]) :
    (f • φ).wedge ψ = f • φ.wedge ψ := by ext x v; simp [wedge_apply]

@[simp]
theorem wedge_smul_right {k l : ℕ} (f : C^n⟮I, M; ℝ⟯) (φ : Ω[k]) (ψ : Ω[l]) :
    φ.wedge (f • ψ) = f • φ.wedge ψ := by ext x v; simp [wedge_apply]

@[simp]
theorem wedge_const_smul_left {k l : ℕ} (c : ℝ) (φ : Ω[k]) (ψ : Ω[l]) :
    (c • φ).wedge ψ = c • φ.wedge ψ := by ext x v; simp [wedge_apply]

@[simp]
theorem wedge_const_smul_right {k l : ℕ} (c : ℝ) (φ : Ω[k]) (ψ : Ω[l]) :
    φ.wedge (c • ψ) = c • φ.wedge ψ := by ext x v; simp [wedge_apply]

@[simp]
theorem wedge_neg_left {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) : (-φ).wedge ψ = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ φ, wedge_const_smul_left]; ext x v; simp

@[simp]
theorem wedge_neg_right {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) : φ.wedge (-ψ) = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ ψ, wedge_const_smul_right]; ext x v; simp

@[simp]
theorem wedge_sub_left {k l : ℕ} (φ₁ φ₂ : Ω[k]) (ψ : Ω[l]) :
    (φ₁ - φ₂).wedge ψ = φ₁.wedge ψ - φ₂.wedge ψ := by
  rw [sub_eq_add_neg, wedge_add_left, wedge_neg_left, sub_eq_add_neg]

@[simp]
theorem wedge_sub_right {k l : ℕ} (φ : Ω[k]) (ψ₁ ψ₂ : Ω[l]) :
    φ.wedge (ψ₁ - ψ₂) = φ.wedge ψ₁ - φ.wedge ψ₂ := by
  rw [sub_eq_add_neg, wedge_add_right, wedge_neg_right, sub_eq_add_neg]

/-- Transporting the left factor across a degree equality commutes with the fibrewise wedge
product. -/
theorem wedge_cast_left {k k' l : ℕ} (h : k = k') (φ : Ω[k]) (ψ : Ω[l]) :
    (LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) h φ).wedge ψ =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (congrArg (· + l) h)
        (φ.wedge ψ) := by
  subst h; rfl

/-- Transporting the right factor across a degree equality commutes with the fibrewise wedge
product. -/
theorem wedge_cast_right {k l l' : ℕ} (h : l = l') (φ : Ω[k]) (ψ : Ω[l]) :
    φ.wedge (LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) h ψ) =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (congrArg (k + ·) h)
        (φ.wedge ψ) := by
  subst h; rfl

/-- Pointwise left degree-zero multiplication of the fibrewise wedge product. -/
theorem wedge_apply_zero_left {l : ℕ} (φ : Ω[0]) (ψ : Ω[l]) (x : M) (v : Fin (0 + l) → V x) :
    φ.wedge ψ x v = φ x 0 * ψ x (v ∘ Fin.cast (Nat.zero_add l).symm) :=
  ContinuousAlternatingMap.pairedWedge_apply_zero_left (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v

/-- Left degree-zero multiplication of the fibrewise wedge product on sections, transported across
`0 + l = l`. -/
@[simp]
theorem wedge_eq_cast_smul_left {l : ℕ} (φ : Ω[0]) (ψ : Ω[l]) :
    φ.wedge ψ =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (Nat.zero_add l).symm
        ((constOfIsEmptyEquiv I F n V (Fin 0)).symm φ • ψ) := by
  ext x v
  rw [cast_apply, smul_apply, constOfIsEmptyEquiv_symm_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, wedge_apply_zero_left]
  exact congrArg (· * _) (congrArg (φ x) (Subsingleton.elim _ _))

/-- Right degree-zero multiplication of the fibrewise wedge product on sections. -/
@[simp]
theorem wedge_eq_smul_right {k : ℕ} (φ : Ω[k]) (ψ : Ω[0]) :
    φ.wedge ψ = (constOfIsEmptyEquiv I F n V (Fin 0)).symm ψ • φ := by
  ext x v
  have h0 : (0 : Fin 0 → V x) = isEmptyElim := Subsingleton.elim _ _
  rw [wedge_apply, ContinuousAlternatingMap.pairedWedge_apply_zero_right, h0]
  simp [smul_eq_mul, mul_comm]

@[simp]
theorem wedge_apply_one_one (φ ψ : Ω[1]) (x : M) (u v : V x) :
    φ.wedge ψ x ![u, v] = φ x ![u] * ψ x ![v] - φ x ![v] * ψ x ![u] :=
  ContinuousAlternatingMap.pairedWedge_apply_one_one (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (φ x) (ψ x) u v

/-- Pointwise graded commutativity of the fibrewise wedge product:
`(φ ∧ ψ)_x = (-1)^(k * l) (ψ ∧ φ)_x` up to `Fin.cast (Nat.add_comm l k)`. -/
theorem wedge_comm_apply {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (x : M) (v : Fin (k + l) → V x) :
    φ.wedge ψ x v = (-1 : ℝ) ^ (k * l) • ψ.wedge φ x (v ∘ Fin.cast (Nat.add_comm l k)) :=
  ContinuousAlternatingMap.pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b : ℝ ↦ mul_comm a b) (φ x) (ψ x) v

/-- Graded commutativity of the fibrewise wedge product on sections:
`φ ∧ ψ = (-1)^(k * l) • LinearEquiv.cast ... (Nat.add_comm l k) (ψ ∧ φ)`. -/
theorem wedge_comm {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) :
    φ.wedge ψ =
      (-1 : ℝ) ^ (k * l) •
        LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (Nat.add_comm l k)
          (ψ.wedge φ) := by
  ext x v
  simpa [-LinearEquiv.cast_apply, cast_apply] using wedge_comm_apply φ ψ x v

/-- Pointwise associativity of the fibrewise wedge product up to
`Fin.cast (Nat.add_assoc k l m).symm`. -/
theorem wedge_assoc_apply {k l m : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (θ : Ω[m])
    (x : M) (v : Fin (k + l + m) → V x) :
    (φ.wedge ψ).wedge θ x v =
      φ.wedge (ψ.wedge θ) x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) :=
  ContinuousAlternatingMap.pairedWedge_assoc _ _ _ _
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b c : ℝ ↦ mul_assoc a b c) (φ x) (ψ x) (θ x) v

/-- Associativity of the fibrewise wedge product on sections:
`(φ ∧ ψ) ∧ θ = LinearEquiv.cast ... (Nat.add_assoc k l m).symm (φ ∧ (ψ ∧ θ))`. -/
theorem wedge_assoc {k l m : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (θ : Ω[m]) :
    (φ.wedge ψ).wedge θ =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (Nat.add_assoc k l m).symm
        (φ.wedge (ψ.wedge θ)) := by
  ext x v
  simpa only [cast_apply] using wedge_assoc_apply φ ψ θ x v

/-- Contracting a wedge whose left factor has degree zero multiplies by that scalar function:
`ι_a (φ ∧ ψ) = φ ∧ (ι_a ψ)`. -/
theorem interior_wedge_zero_left {l : ℕ}
    (φ : Ω[0]) (ψ : Ω[l + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).interior a = φ.wedge (ψ.interior a) := by
  ext x w
  rw [interior_apply, wedge_apply_zero_left, wedge_apply_zero_left, interior_apply]
  exact congrArg (_ * ψ x ·) (funext fun j ↦ Fin.cases (by simp) (fun i ↦ by simp) j)

/-- Contracting a wedge whose right factor has degree zero multiplies by that scalar function:
`ι_a (φ ∧ ψ) = (ι_a φ) ∧ ψ`. -/
theorem interior_wedge_zero_right {k : ℕ}
    (φ : Ω[k + 1]) (ψ : Ω[0]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).interior a = (φ.interior a).wedge ψ := by
  rw [wedge_eq_smul_right, wedge_eq_smul_right, interior_smul_left]

/-- Pointwise graded antiderivation law for `ContMDiffSection.interior` across a fibrewise
wedge of two sections of positive degree:
`ι_a (φ ∧ ψ) = ι_a φ ∧ ψ + (-1)^(k + 1) φ ∧ ι_a ψ` up to
`Fin.cast (Nat.add_right_comm k 1 l).symm`. -/
theorem interior_wedge_succ_apply {k l : ℕ}
    (φ : Ω[k + 1]) (ψ : Ω[l + 1]) (a : Cₛ^n⟮I; F, V⟯) (x : M) (w : Fin (k + 1 + l) → V x) :
    (φ.wedge ψ).interior a x w =
      (φ.interior a).wedge ψ x (w ∘ Fin.cast (Nat.add_right_comm k 1 l).symm) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interior a) x w :=
  ContinuousAlternatingMap.curryLeftTopological_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) (a x) w

/-- Graded antiderivation law for `ContMDiffSection.interior` across a fibrewise wedge of two
sections of positive degree:
`ι_a (φ ∧ ψ) = LinearEquiv.cast ... (Nat.add_right_comm k 1 l).symm (ι_a φ ∧ ψ)`
`  + (-1)^(k + 1) • (φ ∧ ι_a ψ)`. -/
theorem interior_wedge_succ {k l : ℕ}
    (φ : Ω[k + 1]) (ψ : Ω[l + 1]) (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).interior a =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q])
          (Nat.add_right_comm k 1 l).symm ((φ.interior a).wedge ψ) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interior a) := by
  ext x w
  rw [add_cast_smul_apply]
  exact interior_wedge_succ_apply φ ψ a x w

end Wedge

section EvalExt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

/-- Two `C^n` alternating sections (`n ≤ ∞`) on a `C^n` real vector bundle over a
finite-dimensional Hausdorff `C^n` manifold are equal whenever they agree on all tuples of
global `C^n` sections. -/
theorem eq_of_evalAlternating_eq {ι : Type*} [Fintype ι]
    {φ ψ : Cₛ^n⟮I; F [⋀^ι]→L[ℝ] ℝ, fun x ↦ V x [⋀^ι]→L[ℝ] ℝ⟯}
    (h : φ.evalAlternating = ψ.evalAlternating) : φ = ψ := by
  ext x v
  choose s hs using fun i ↦ exists_apply_eq (I := I) (F := F) (V := V) n x (v i)
  have hs' : (fun i ↦ s i x) = v := funext hs
  simpa only [evalAlternating_apply, hs'] using congr($h s x)

end EvalExt

/-! ### Tensoriality equivalence -/

noncomputable section Tensoriality

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

local notation "Ω[" ι "]" => Cₛ^n⟮I; F [⋀^ι]→L[ℝ] ℝ, fun x ↦ V x [⋀^ι]→L[ℝ] ℝ⟯
local notation "Alt[" ι "]" => Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; ℝ⟯] C^n⟮I, M; ℝ⟯

/-- A `C^n(M)`-multilinear alternating map on `C^n` sections of `V` (`1 ≤ n ≤ ∞`) is pointwise
tensorial: its value at `x` depends only on the values of the input sections at `x`. -/
theorem apply_eq_of_eval_eq {ι : Type*} [Finite ι] (Φ : Alt[ι]) {s s' : ι → Cₛ^n⟮I; F, V⟯} {x : M}
    (h : ∀ i, s i x = s' i x) (hn : 1 ≤ n := by simp) : Φ s x = Φ s' x := by
  classical
  cases nonempty_fintype ι
  -- Update the entries of `s` to those of `s'` over a growing subset `q : Finset ι`.
  suffices ∀ q : Finset ι, Φ (fun i ↦ if i ∈ q then s' i else s i) x = Φ s x by
    simpa using (this Finset.univ).symm
  intro q
  induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih =>
    let w : ι → Cₛ^n⟮I; F, V⟯ := fun i ↦ if i ∈ q then s' i else s i
    have hw : (fun i ↦ if i ∈ insert j q then s' i else s i) = update w j (s' j) := by
      ext i; by_cases hij : i = j <;> simp_all [w]
    have hself : update w j (s j) = w := by ext i; by_cases hij : i = j <;> simp_all [w]
    -- Apply single-slot tensoriality in slot `j` with the remaining slots fixed to `w`.
    let Ψ : (Π y : M, V y) → ℝ := fun u ↦
      if hu : CMDiff n (T% u) then Φ (update w j ⟨u, hu⟩) x else 0
    have hΨ_eq (t : Cₛ^n⟮I; F, V⟯) : Ψ t = Φ (update w j t) x := by
      have ht : (⟨t, t.contMDiff⟩ : Cₛ^n⟮I; F, V⟯) = t := ext fun _ ↦ rfl
      simp [Ψ, t.contMDiff, ht]
    have hstep : Φ (update w j (s' j)) x = Φ (update w j (s j)) x := by
      rw [← hΨ_eq, ← hΨ_eq]
      refine TauCeti.Manifold.eq_of_contMDiff_tensorial (G := F) (W := V) Ψ x
        (fun {u₁ u₂} hu₁ hu₂ ↦ ?_) (fun {f u} hf hu ↦ ?_)
        (s' j).contMDiff (s j).contMDiff (h j).symm hn
      · have hsum : CMDiff n (T% (u₁ + u₂)) := (⟨u₁, hu₁⟩ + ⟨u₂, hu₂⟩ : Cₛ^n⟮I; F, V⟯).contMDiff
        simp only [Ψ, hu₁, hu₂, hsum, ↓reduceDIte]
        exact congr($(Φ.map_update_add w j ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) x)
      · have hsm : CMDiff n (T% (f • u)) := hf.smul_section hu
        let gf : C^n⟮I, M; ℝ⟯ := ⟨f, hf⟩
        have hsm_eq : gf • (⟨u, hu⟩ : Cₛ^n⟮I; F, V⟯) = ⟨f • u, hsm⟩ := by
          ext y; rw [smul_apply]; rfl
        simp only [Ψ, hu, hsm, ↓reduceDIte, ← hsm_eq]
        exact congr($(Φ.map_update_smul w j gf ⟨u, hu⟩) x)
    rw [hw, hstep, hself, ih]

/-- The continuous alternating map on the fibre `V x` induced by a `C^n(M)`-multilinear
alternating map `Φ` on global `C^n` sections: read `Φ` on the model space `F` via
`ContMDiffSection.liftModel` (where continuity is automatic by finite-dimensionality of `F`), and
pull back to `V x`. -/
private def fibreAlternatingAt {ι : Type*} [Fintype ι] (Φ : Alt[ι]) (x : M) :
    V x [⋀^ι]→L[ℝ] ℝ :=
  let fModel : F [⋀^ι]→ₗ[ℝ] ℝ :=
    ((ContMDiffMap.evalAlgHom x : C^n⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ).toLinearMap.compAlternatingMap
      (Φ.restrictScalars ℝ)).compLinearMap (liftModel I F V n x)
  (AlternatingMap.toContinuousAlternatingMap fModel).compContinuousLinearMap
    ((FiberBundle.trivializationAt F V x).continuousLinearMapAt ℝ x)

private theorem fibreAlternatingAt_apply_sections {ι : Type*} [Fintype ι] (Φ : Alt[ι])
    (hn : 1 ≤ n) (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    fibreAlternatingAt Φ x (fun i ↦ s i x) = Φ s x := by
  have hx : x ∈ (FiberBundle.trivializationAt F V x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F V x
  have hsec : Φ (fun i ↦ liftModel I F V n x
      ((FiberBundle.trivializationAt F V x).continuousLinearMapAt ℝ x (s i x))) x = Φ s x :=
    apply_eq_of_eval_eq Φ (fun i ↦ by
      simp only [liftModel_apply_self]
      exact (FiberBundle.trivializationAt F V x).symmL_continuousLinearMapAt hx (s i x)) hn
  simpa [fibreAlternatingAt, Function.comp_def] using hsec

/-- Reconstruct a `C^n` section of `fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` from a `C^n(M)`-multilinear
alternating map on `C^n` sections of `V` (`1 ≤ n ≤ ∞`). -/
def ofAlternating {ι : Type*} [Fintype ι] (Φ : Alt[ι]) (hn : 1 ≤ n := by simp) : Ω[ι] where
  toFun := fibreAlternatingAt Φ
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun w ↦ ?_⟩
    let sw : ι → Cₛ^n⟮I; F, V⟯ := fun i ↦ liftModel I F V n x₀ (w i)
    refine (Φ sw).contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Filter.eventually_all.2 fun i ↦
        liftModel_eventuallyEq (I := I) (F := F) (V := V) (n := n) x₀ (w i)] with y hsw
    have hsw' : (fun i ↦ (FiberBundle.trivializationAt F V x₀).symmL ℝ y (w i)) =
        fun i ↦ sw i y := funext fun i ↦ (hsw i).symm
    simp [ContinuousAlternatingMap.inCoordinates, Function.comp_def, hsw',
      fibreAlternatingAt_apply_sections Φ hn]

@[simp]
theorem ofAlternating_apply_sections {ι : Type*} [Fintype ι] (Φ : Alt[ι])
    (hn : 1 ≤ n) (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    ofAlternating Φ hn x (fun i ↦ s i x) = Φ s x :=
  fibreAlternatingAt_apply_sections Φ hn s x

@[simp]
theorem evalAlternating_ofAlternating {ι : Type*} [Fintype ι] (Φ : Alt[ι]) (hn : 1 ≤ n) :
    (ofAlternating Φ hn).evalAlternating = Φ := by
  ext s x; exact ofAlternating_apply_sections Φ hn s x

@[simp]
theorem ofAlternating_evalAlternating {ι : Type*} [Fintype ι] (φ : Ω[ι]) (hn : 1 ≤ n) :
    ofAlternating φ.evalAlternating hn = φ :=
  eq_of_evalAlternating_eq (evalAlternating_ofAlternating φ.evalAlternating hn)

variable (I F n V) in
/-- **Tensoriality of alternating bundle cochains**: `C^n` sections of
`fun x ↦ V x [⋀^ι]→L[ℝ] ℝ` on a finite-rank `C^n` real vector bundle over a
finite-dimensional Hausdorff `C^n` manifold (`1 ≤ n ≤ ∞`) are `C^n(M)`-linearly equivalent to
`C^n(M)`-multilinear alternating maps `Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; ℝ⟯] C^n⟮I, M; ℝ⟯`. -/
def evalAlternatingEquiv (ι : Type*) [Fintype ι] (hn : 1 ≤ n := by simp) :
    Ω[ι] ≃ₗ[C^n⟮I, M; ℝ⟯] Alt[ι] where
  __ := evalAlternatingLinear I F n V ι
  invFun Φ := ofAlternating Φ hn
  left_inv φ := ofAlternating_evalAlternating φ hn
  right_inv Φ := evalAlternating_ofAlternating Φ hn

@[simp]
theorem evalAlternatingEquiv_apply {ι : Type*} [Fintype ι] (hn : 1 ≤ n) (φ : Ω[ι]) :
    evalAlternatingEquiv I F n V ι hn φ = φ.evalAlternating := (rfl)

@[simp]
theorem evalAlternatingEquiv_symm_apply {ι : Type*} [Fintype ι] (hn : 1 ≤ n) (Φ : Alt[ι]) :
    (evalAlternatingEquiv I F n V ι hn).symm Φ = ofAlternating Φ hn := (rfl)

@[simp]
theorem interior_ofAlternating {k : ℕ} (Φ : Alt[Fin (k + 1)]) (hn : 1 ≤ n)
    (a : Cₛ^n⟮I; F, V⟯) :
    (ofAlternating Φ hn).interior a = ofAlternating (Φ.curryLeft a) hn :=
  eq_of_evalAlternating_eq (by simp)

end Tensoriality

end ContMDiffSection
