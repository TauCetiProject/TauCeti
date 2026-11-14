/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Sections of bundles of continuous alternating maps

For a vector bundle `V → M` with model fibre `F`, the continuous alternating maps
`V x [⋀^ι]→L[𝕜] 𝕜` form a vector bundle over `M` (viewing the scalar codomain as the trivial
bundle `Bundle.Trivial M 𝕜`). This file provides the algebraic and calculus operations on
`ContMDiffSection` needed to treat these sections as intrinsic cochains on `V`:

* evaluation `ContMDiffSection.evalAlternating` on tuples of `C^n` sections of `V`, bundled as a
  `C^n(M)`-multilinear alternating map;
* the degree-zero `C^n(M)`-linear equivalence `ContMDiffSection.constOfIsEmptyEquiv` between scalar
  functions `C^n⟮I, M; 𝕜⟯` and sections of `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜` for `[IsEmpty ι]`;
* the interior product `ContMDiffSection.interiorProd` contracting the first slot of a
  bundle-valued alternating section with a section of `V`, intertwining evaluation with
  `AlternatingMap.curryLeft`;
* the smooth fibrewise wedge product `ContMDiffSection.wedge` of real scalar alternating sections,
  together with its graded commutativity, associativity, and interior-product antiderivation laws;
* the tensoriality equivalence `ContMDiffSection.evalAlternatingEquiv` identifying smooth sections
  of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` on a finite-rank smooth real vector bundle over a
  finite-dimensional Hausdorff manifold with `C^∞(M)`-multilinear alternating maps
  `Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`.

The coordinate-smoothness proof for `ContMDiffSection.wedge` adapts the bundle-valued wedge
regularity proof of `TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` to sections on
an arbitrary vector bundle `V`, and `ContMDiffSection.ofAlternating` combines
`TauCeti.Manifold.eq_of_contMDiff_tensorial` with global section extensions from
`TauCeti.Geometry.Manifold.VectorBundle.Section.Extension`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapters 12 and 14.
* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3 and §7.1.
-/

public section

noncomputable section

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

/-! ### Evaluation on sections -/

/-- Evaluate a `C^n` section of the scalar alternating-map bundle `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜` on
tuples of `C^n` sections of `V`, as a `C^n(M)`-multilinear alternating map to `C^n` scalar
functions. -/
def evalAlternating {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s :=
    ⟨fun x ↦ φ x (fun i ↦ s i x),
      (Bundle.Trivial.contMDiff_mk_iff.1
        (φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ (s i).contMDiff)).2⟩
  map_update_add' := fun [DecidableEq ι] s i u v ↦ by
    ext x
    have h (w : Cₛ^n⟮I; F, V⟯) :
        (fun j ↦ update s i w j x) = update (fun j ↦ s j x) i (w x) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    change φ x (fun j ↦ update s i (u + v) j x) =
      φ x (fun j ↦ update s i u j x) + φ x (fun j ↦ update s i v j x)
    simp only [h, coe_add, Pi.add_apply]
    exact (φ x).map_update_add (fun j ↦ s j x) i (u x) (v x)
  map_update_smul' := fun [DecidableEq ι] s i f u ↦ by
    ext x
    have h (w : Cₛ^n⟮I; F, V⟯) :
        (fun j ↦ update s i w j x) = update (fun j ↦ s j x) i (w x) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    change φ x (fun j ↦ update s i (f • u) j x) =
      f x • φ x (fun j ↦ update s i u j x)
    simp only [h, smul_apply]
    exact (φ x).map_update_smul (fun j ↦ s j x) i (f x) (u x)
  map_eq_zero_of_eq' s i j hij hne := by
    ext x
    exact (φ x).map_eq_zero_of_eq (fun r ↦ s r x) (i := i) (j := j) congr(($hij) x) hne

@[simp]
theorem evalAlternating_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯)
    (s : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    φ.evalAlternating s x = φ x (fun i ↦ s i x) :=
  (rfl)

@[simp]
theorem evalAlternating_zero {ι : Type*} [Fintype ι] :
    (0 : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯).evalAlternating = 0 := by
  ext s x
  simp

@[simp]
theorem evalAlternating_add {ι : Type*} [Fintype ι]
    (φ ψ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    (φ + ψ).evalAlternating = φ.evalAlternating + ψ.evalAlternating := by
  ext s x
  simp

@[simp]
theorem evalAlternating_smul {ι : Type*} [Fintype ι] (f : C^n⟮I, M; 𝕜⟯)
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    (f • φ).evalAlternating = f • φ.evalAlternating := by
  ext s x
  simp

@[simp]
theorem evalAlternating_const_smul {ι : Type*} [Fintype ι] (c : 𝕜)
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    (c • φ).evalAlternating = c • φ.evalAlternating := by
  ext s x
  simp

@[simp]
theorem evalAlternating_neg {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    (-φ).evalAlternating = -φ.evalAlternating := by
  ext s x
  simp

@[simp]
theorem evalAlternating_sub {ι : Type*} [Fintype ι]
    (φ ψ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    (φ - ψ).evalAlternating = φ.evalAlternating - ψ.evalAlternating := by
  ext s x
  simp

variable (I F n V) in
/-- `ContMDiffSection.evalAlternating` bundled as a `C^n(M)`-linear map. -/
def evalAlternatingLinear (ι : Type*) [Fintype ι] :
    Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      (Cₛ^n⟮I; F, V⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯) where
  toFun := evalAlternating
  map_add' := evalAlternating_add
  map_smul' := evalAlternating_smul

@[simp]
theorem evalAlternatingLinear_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) :
    evalAlternatingLinear I F n V ι φ = φ.evalAlternating :=
  (rfl)

/-! ### Degree zero -/

section DegreeZero

variable (I F n V)

/-- Degree-zero continuous alternating maps on a normed space as a continuous linear map from the
field of scalars. -/
private def constOfIsEmptyCLM (ι : Type*) [Fintype ι] [IsEmpty ι] :
    𝕜 →L[𝕜] F [⋀^ι]→L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun c := ContinuousAlternatingMap.constOfIsEmpty 𝕜 F ι c
      map_add' c₁ c₂ := by ext v; simp
      map_smul' r c := by ext v; simp }
    1 fun c ↦ by
      rw [one_mul]
      refine ContinuousAlternatingMap.opNorm_le_bound _ (norm_nonneg c) fun v ↦ ?_
      simp

/-- Package `x ↦ constOfIsEmpty 𝕜 (V x) ι (f x)` as a `C^n` section. -/
private def constOfIsEmptySection (ι : Type*) [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) :
    Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯ where
  toFun x := ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V x) ι (f x)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hcoord :
        (fun y ↦ ContinuousAlternatingMap.inCoordinates F 𝕜
          (E₁ := V) (E₂ := Bundle.Trivial M 𝕜) x₀ y x₀ y
          (ContinuousAlternatingMap.constOfIsEmpty 𝕜 (V y) ι (f y))) =
          fun y ↦ constOfIsEmptyCLM F ι (f y) := by
      ext y w
      simp [constOfIsEmptyCLM, ContinuousAlternatingMap.inCoordinates]
    rw [hcoord]
    exact (constOfIsEmptyCLM F ι).contMDiffAt.comp x₀ f.contMDiff.contMDiffAt

@[simp]
private theorem constOfIsEmptySection_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) (x : M) (v : ι → V x) :
    constOfIsEmptySection I F n V ι f x v = f x :=
  (rfl)

/-- In degree zero (`[IsEmpty ι]`), `C^n` scalar functions identify `C^n(M)`-linearly with `C^n`
sections of `fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜`. -/
def constOfIsEmptyEquiv (ι : Type*) [Fintype ι] [IsEmpty ι] :
    C^n⟮I, M; 𝕜⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯ where
  toFun := constOfIsEmptySection I F n V ι
  invFun φ :=
    ⟨fun x ↦ φ x isEmptyElim,
      (Bundle.Trivial.contMDiff_mk_iff.1
        (φ.contMDiff.continuousAlternatingMap_bundle_apply fun i : ι ↦ isEmptyElim i)).2⟩
  map_add' f g := by ext x v; simp
  map_smul' f g := by ext x v; simp [smul_eq_mul]
  left_inv f := by ext x; simp
  right_inv φ := by
    ext x v
    rw [Subsingleton.elim v isEmptyElim]
    rfl

variable {I F n V}

@[simp]
theorem constOfIsEmptyEquiv_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) (x : M) (v : ι → V x) :
    constOfIsEmptyEquiv I F n V ι f x v = f x :=
  (rfl)

@[simp]
theorem constOfIsEmptyEquiv_symm_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (φ : Cₛ^n⟮I; F [⋀^ι]→L[𝕜] 𝕜, fun x ↦ V x [⋀^ι]→L[𝕜] 𝕜⟯) (x : M) :
    (constOfIsEmptyEquiv I F n V ι).symm φ x = φ x isEmptyElim :=
  (rfl)

@[simp]
theorem evalAlternating_constOfIsEmptyEquiv {ι : Type*} [Fintype ι] [IsEmpty ι]
    (f : C^n⟮I, M; 𝕜⟯) :
    (constOfIsEmptyEquiv I F n V ι f).evalAlternating =
      AlternatingMap.constOfIsEmpty C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ ι f := by
  ext s x
  rfl

end DegreeZero

end General

/-! ### Interior product -/

section InteriorProd

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F F₂ : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {n : ℕ∞ω} {V V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- Contract the first argument of a `C^n` section of `fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x`
with a `C^n` section `a` of `V`. -/
def interiorProd {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    Cₛ^n⟮I; F [⋀^Fin k]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin k]→L[𝕜] V₂ x⟯ where
  toFun x := (φ x).curryLeftTopological (a x)
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun w ↦ ?_⟩
    let e₁ := FiberBundle.trivializationAt F V x₀
    let e₂ := FiberBundle.trivializationAt F₂ V₂ x₀
    have he₁ : x₀ ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
    have he₂ : x₀ ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x₀
    -- Assemble `(a, e₁⁻¹ (w 0), …, e₁⁻¹ (w (k - 1)))` as a tuple of sections smooth at `x₀`.
    let u : Fin (k + 1) → Π y : M, V y :=
      Fin.cons (fun y ↦ a y) (fun j y ↦ e₁.symm y (w j))
    have hu (i : Fin (k + 1)) :
        ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F y (u i y)) x₀ := by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact a.contMDiff.contMDiffAt
      · simp only [u, Fin.cons_succ]
        rw [contMDiffAt_section_iff]
        refine (contMDiffAt_const (c := w j)).congr_of_eventuallyEq ?_
        filter_upwards [e₁.open_baseSet.mem_nhds he₁] with y hy
        exact congrArg Prod.snd (e₁.apply_mk_symm hy (w j))
    have happ := (contMDiffAt_section_iff x₀).1
      (φ.contMDiff.contMDiffAt.continuousAlternatingMap_bundle_apply hu)
    refine happ.congr_of_eventuallyEq ?_
    filter_upwards [e₁.open_baseSet.mem_nhds he₁, e₂.open_baseSet.mem_nhds he₂] with y hy₁ hy₂
    have hcons :
        (Matrix.vecCons (a y) fun j ↦ (FiberBundle.trivializationAt F V x₀).symmL 𝕜 y (w j)) =
          fun i ↦ u i y := by
      ext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      simp [u, e₁, Trivialization.symmL_apply _ hy₁]
    simp only [ContinuousAlternatingMap.inCoordinates,
      ContinuousLinearMap.compContinuousAlternatingMap_coe,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      ContinuousAlternatingMap.curryLeftTopological_apply_apply, hcons]
    exact (FiberBundle.trivializationAt F₂ V₂ x₀).continuousLinearMapAt_apply_of_mem 𝕜 hy₂ _

@[simp]
theorem interiorProd_apply {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) (x : M) (v : Fin k → V x) :
    φ.interiorProd a x v = φ x (Matrix.vecCons (a x) v) :=
  ContinuousAlternatingMap.curryLeftTopological_apply_apply (φ x) (a x) v

@[simp]
theorem interiorProd_zero_left {k : ℕ} (a : Cₛ^n⟮I; F, V⟯) :
    (0 : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂,
      fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯).interiorProd a = 0 := by
  ext x v
  simp

@[simp]
theorem interiorProd_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯) :
    φ.interiorProd 0 = 0 := by
  ext x v
  exact congr($((φ x).curryLeftTopological.map_zero) v)

@[simp]
theorem interiorProd_add_left {k : ℕ}
    (φ ψ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ + ψ).interiorProd a = φ.interiorProd a + ψ.interiorProd a := by
  ext x v
  simp

@[simp]
theorem interiorProd_add_right {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    φ.interiorProd (a + b) = φ.interiorProd a + φ.interiorProd b := by
  ext x v
  exact congr($((φ x).curryLeftTopological.map_add (a x) (b x)) v)

@[simp]
theorem interiorProd_smul_left {k : ℕ} (f : C^n⟮I, M; 𝕜⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (f • φ).interiorProd a = f • φ.interiorProd a := by
  ext x v
  simp

@[simp]
theorem interiorProd_smul_right {k : ℕ} (f : C^n⟮I, M; 𝕜⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    φ.interiorProd (f • a) = f • φ.interiorProd a := by
  ext x v
  have h := congr($((φ x).curryLeftTopological.map_smul (f x) (a x)) v)
  simpa only [ContinuousAlternatingMap.curryLeftTopological_apply_apply, interiorProd_apply,
    smul_apply, ContinuousAlternatingMap.smul_apply] using h

@[simp]
theorem interiorProd_const_smul_left {k : ℕ} (c : 𝕜)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (c • φ).interiorProd a = c • φ.interiorProd a := by
  ext x v
  simp

@[simp]
theorem interiorProd_const_smul_right {k : ℕ} (c : 𝕜)
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    φ.interiorProd (c • a) = c • φ.interiorProd a := by
  ext x v
  exact congr($((φ x).curryLeftTopological.map_smul c (a x)) v)

@[simp]
theorem interiorProd_sub_left {k : ℕ}
    (φ ψ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ - ψ).interiorProd a = φ.interiorProd a - ψ.interiorProd a := by
  ext x v
  simp

@[simp]
theorem interiorProd_sub_right {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] V₂ x⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    φ.interiorProd (a - b) = φ.interiorProd a - φ.interiorProd b := by
  rw [sub_eq_add_neg, interiorProd_add_right, ← neg_one_smul 𝕜 b, interiorProd_const_smul_right,
    neg_one_smul, sub_eq_add_neg]

/-- Contracting twice with the same section gives zero. -/
@[simp]
theorem interiorProd_interiorProd_self {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 2)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 2)]→L[𝕜] V₂ x⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.interiorProd a).interiorProd a = 0 := by
  ext x v
  exact congr($((φ x).curryLeftTopological_curryLeftTopological (a x)) v)

/-- Interior products anticommute: `ι_b (ι_a φ) = -ι_a (ι_b φ)`. -/
theorem interiorProd_interiorProd_comm {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 2)]→L[𝕜] F₂, fun x ↦ V x [⋀^Fin (k + 2)]→L[𝕜] V₂ x⟯)
    (a b : Cₛ^n⟮I; F, V⟯) :
    (φ.interiorProd a).interiorProd b = -(φ.interiorProd b).interiorProd a := by
  have h := interiorProd_interiorProd_self φ (a + b)
  simp only [interiorProd_add_left, interiorProd_add_right, interiorProd_interiorProd_self,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Evaluation intertwines `ContMDiffSection.interiorProd` with `AlternatingMap.curryLeft`. -/
@[simp]
theorem evalAlternating_interiorProd {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[𝕜] 𝕜, fun x ↦ V x [⋀^Fin (k + 1)]→L[𝕜] 𝕜⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.interiorProd a).evalAlternating = φ.evalAlternating.curryLeft a := by
  ext s x
  simp only [evalAlternating_apply, interiorProd_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1
  ext i
  refine Fin.cases rfl (fun _ ↦ rfl) i

end InteriorProd

/-! ### Fibrewise wedge product -/

section Wedge

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- The `C^n` fibrewise wedge product of two `C^n` scalar alternating sections on a real vector
bundle `V`, normalized by `1 / (k! l!)` so that the wedge of two `1`-cochains is their two-term
determinant. No finite-dimensionality, Hausdorff, or manifold-smoothness assumptions are needed. -/
def wedge {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    Cₛ^n⟮I; F [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ where
  toFun x :=
    ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x)
  contMDiff_toFun x₀ := by
    have hφ := (contMDiffAt_continuousAlternatingMap_bundle
      (E₁ := V) (E₂ := Bundle.Trivial M ℝ) _).1 (φ.contMDiff x₀)
    have hψ := (contMDiffAt_continuousAlternatingMap_bundle
      (E₁ := V) (E₂ := Bundle.Trivial M ℝ) _).1 (ψ.contMDiff x₀)
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hcoord :
        (fun y ↦ ContinuousAlternatingMap.inCoordinates F ℝ
          (E₁ := V) (E₂ := Bundle.Trivial M ℝ) x₀ y x₀ y
          (ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
            (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y))) =
          fun y ↦ ContinuousAlternatingMap.pairedWedgeCLM (ContinuousLinearMap.mul ℝ ℝ)
            (ContinuousAlternatingMap.inCoordinates F ℝ
              (E₁ := V) (E₂ := Bundle.Trivial M ℝ) x₀ y x₀ y (φ y))
            (ContinuousAlternatingMap.inCoordinates F ℝ
              (E₁ := V) (E₂ := Bundle.Trivial M ℝ) x₀ y x₀ y (ψ y)) := by
      ext y w
      simp [ContinuousAlternatingMap.inCoordinates,
        ContinuousAlternatingMap.pairedWedge_compContinuousLinearMap]
    rw [hcoord]
    exact (((ContinuousAlternatingMap.pairedWedgeCLM
      (E := F) (k := k) (l := l)
        (ContinuousLinearMap.mul ℝ ℝ)).contDiff.comp_contMDiffAt hφ.2).clm_apply hψ.2)

theorem wedge_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) (x : M) :
    φ.wedge ψ x =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) :=
  (rfl)

/-- Pointwise signed-permutation expansion of the fibrewise wedge product. -/
theorem wedge_apply_sum {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l) → V x) :
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
theorem evalAlternating_wedge_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
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
theorem wedge_zero_left {k l : ℕ}
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (0 : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯).wedge ψ = 0 := by
  ext x v
  simp [wedge_apply_sum]

@[simp]
theorem wedge_zero_right {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    φ.wedge (0 : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) = 0 := by
  ext x v
  simp [wedge_apply_sum]

@[simp]
theorem wedge_add_left {k l : ℕ}
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (φ₁ + φ₂).wedge ψ = φ₁.wedge ψ + φ₂.wedge ψ := by
  ext x v
  exact congr($(ContinuousAlternatingMap.pairedWedge_add_left (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ₁ x) (φ₂ x) (ψ x)) v)

@[simp]
theorem wedge_add_right {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ₁ ψ₂ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (ψ₁ + ψ₂) = φ.wedge ψ₁ + φ.wedge ψ₂ := by
  ext x v
  exact congr($(ContinuousAlternatingMap.pairedWedge_add_right (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ₁ x) (ψ₂ x)) v)

@[simp]
theorem wedge_smul_left {k l : ℕ} (f : C^n⟮I, M; ℝ⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (f • φ).wedge ψ = f • φ.wedge ψ := by
  ext x v
  simp [wedge_apply]

@[simp]
theorem wedge_smul_right {k l : ℕ} (f : C^n⟮I, M; ℝ⟯)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (f • ψ) = f • φ.wedge ψ := by
  ext x v
  simp [wedge_apply]

@[simp]
theorem wedge_const_smul_left {k l : ℕ} (c : ℝ)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (c • φ).wedge ψ = c • φ.wedge ψ := by
  ext x v
  simp [wedge_apply]

@[simp]
theorem wedge_const_smul_right {k l : ℕ} (c : ℝ)
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (c • ψ) = c • φ.wedge ψ := by
  ext x v
  simp [wedge_apply]

@[simp]
theorem wedge_neg_left {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (-φ).wedge ψ = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ φ, wedge_const_smul_left]
  ext x v
  simp

@[simp]
theorem wedge_neg_right {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (-ψ) = -(φ.wedge ψ) := by
  rw [← neg_one_smul ℝ ψ, wedge_const_smul_right]
  ext x v
  simp

@[simp]
theorem wedge_sub_left {k l : ℕ}
    (φ₁ φ₂ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    (φ₁ - φ₂).wedge ψ = φ₁.wedge ψ - φ₂.wedge ψ := by
  rw [sub_eq_add_neg, wedge_add_left, wedge_neg_left, sub_eq_add_neg]

@[simp]
theorem wedge_sub_right {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ₁ ψ₂ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    φ.wedge (ψ₁ - ψ₂) = φ.wedge ψ₁ - φ.wedge ψ₂ := by
  rw [sub_eq_add_neg, wedge_add_right, wedge_neg_right, sub_eq_add_neg]

@[simp]
theorem wedge_apply_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (0 + l) → V x) :
    φ.wedge ψ x v = φ x 0 * ψ x (v ∘ Fin.cast (Nat.zero_add l).symm) :=
  ContinuousAlternatingMap.pairedWedge_apply_zero_left (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) v

@[simp]
theorem wedge_apply_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯) :
    φ.wedge ψ = (constOfIsEmptyEquiv I F n V (Fin 0)).symm ψ • φ := by
  ext x v
  have h0 : (0 : Fin 0 → V x) = isEmptyElim := Subsingleton.elim _ _
  rw [wedge_apply, ContinuousAlternatingMap.pairedWedge_apply_zero_right, h0]
  simp [smul_eq_mul, mul_comm]

@[simp]
theorem wedge_apply_one_one
    (φ ψ : Cₛ^n⟮I; F [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 1]→L[ℝ] ℝ⟯)
    (x : M) (u v : V x) :
    φ.wedge ψ x ![u, v] = φ x ![u] * ψ x ![v] - φ x ![v] * ψ x ![u] :=
  ContinuousAlternatingMap.pairedWedge_apply_one_one (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (φ x) (ψ x) u v

/-- Graded commutativity of the fibrewise wedge product:
`(φ ∧ ψ)_x = (-1)^(k * l) (ψ ∧ φ)_x` up to `Fin.cast (Nat.add_comm l k)`. -/
theorem wedge_comm {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l) → V x) :
    φ.wedge ψ x v = (-1 : ℝ) ^ (k * l) • ψ.wedge φ x (v ∘ Fin.cast (Nat.add_comm l k)) :=
  ContinuousAlternatingMap.pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b : ℝ ↦ mul_comm a b) (φ x) (ψ x) v

/-- Associativity of the fibrewise wedge product up to `Fin.cast (Nat.add_assoc k l m).symm`. -/
theorem wedge_assoc {k l m : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (θ : Cₛ^n⟮I; F [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin m]→L[ℝ] ℝ⟯)
    (x : M) (v : Fin (k + l + m) → V x) :
    (φ.wedge ψ).wedge θ x v =
      φ.wedge (ψ.wedge θ) x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) :=
  ContinuousAlternatingMap.pairedWedge_assoc _ _ _ _
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b c : ℝ ↦ mul_assoc a b c) (φ x) (ψ x) (θ x) v

/-- Contracting a wedge whose left factor has degree zero multiplies by that scalar function:
`ι_a (φ ∧ ψ) = φ ∧ (ι_a ψ)`. -/
theorem interiorProd_wedge_zero_left [FiniteDimensional ℝ F] {l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).interiorProd a = φ.wedge (ψ.interiorProd a) := by
  ext x w
  rw [interiorProd_apply, wedge_apply_zero_left, wedge_apply_zero_left, interiorProd_apply]
  congr 2
  ext j
  refine Fin.cases (by simp) (fun i ↦ by simp) j

/-- Contracting a wedge whose right factor has degree zero multiplies by that scalar function:
`ι_a (φ ∧ ψ) = (ι_a φ) ∧ ψ`. -/
theorem interiorProd_wedge_zero_right [FiniteDimensional ℝ F] {k : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) :
    (φ.wedge ψ).interiorProd a = (φ.interiorProd a).wedge ψ := by
  rw [wedge_apply_zero_right, wedge_apply_zero_right, interiorProd_smul_left]

/-- Graded antiderivation law for `ContMDiffSection.interiorProd` across a fibrewise wedge of two
sections of positive degree:
`ι_a (φ ∧ ψ) = ι_a φ ∧ ψ + (-1)^(k + 1) φ ∧ ι_a ψ` up to the degree cast
`k + (l + 1) = k + 1 + l`. -/
theorem interiorProd_wedge_succ [FiniteDimensional ℝ F] {k l : ℕ}
    (φ : Cₛ^n⟮I; F [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; F [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (a : Cₛ^n⟮I; F, V⟯) (x : M) (w : Fin (k + 1 + l) → V x) :
    (φ.wedge ψ).interiorProd a x w =
      (φ.interiorProd a).wedge ψ x (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • φ.wedge (ψ.interiorProd a) x w :=
  ContinuousAlternatingMap.curryLeftTopological_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ x) (ψ x) (a x) w

end Wedge

/-! ### Tensoriality equivalence -/

section Tensoriality

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- A `C^∞(M)`-multilinear alternating map on smooth sections of `V` is pointwise tensorial: its
value at `x` depends only on the values of the input sections at `x`. -/
theorem apply_eq_of_eval_eq {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    {s s' : Fin k → Cₛ^∞⟮I; F, V⟯} {x : M} (h : ∀ i, s i x = s' i x) :
    Φ s x = Φ s' x := by
  -- Update the entries of `s` to those of `s'` over a growing subset `q : Finset (Fin k)`.
  suffices ∀ q : Finset (Fin k),
      Φ (fun i ↦ if i ∈ q then s' i else s i) x = Φ s x by
    simpa using (this Finset.univ).symm
  intro q
  induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih =>
    let w : Fin k → Cₛ^∞⟮I; F, V⟯ := fun i ↦ if i ∈ q then s' i else s i
    have hw (t : Cₛ^∞⟮I; F, V⟯) (hjw : t = s' j) :
        (fun i ↦ if i ∈ insert j q then s' i else s i) = update w j t := by
      ext i
      by_cases hij : i = j
      · subst hij; simp [w, hjw]
      · simp [w, hij]
    have hself : update w j (s j) = w := by
      ext i
      by_cases hij : i = j
      · subst hij; simp [w, hj]
      · simp [hij]
    -- Apply single-slot tensoriality in slot `j` with the remaining slots fixed to `w`.
    classical
    let Ψ : (Π y : M, V y) → ℝ := fun u ↦
      if hu : CMDiff ∞ (T% u) then Φ (update w j ⟨u, hu⟩) x else 0
    have hΨ_eq (t : Cₛ^∞⟮I; F, V⟯) : Ψ t = Φ (update w j t) x := by
      have ht : (⟨t, t.contMDiff⟩ : Cₛ^∞⟮I; F, V⟯) = t := ext fun _ ↦ rfl
      simp [Ψ, t.contMDiff, ht]
    have hstep : Φ (update w j (s' j)) x = Φ (update w j (s j)) x := by
      rw [← hΨ_eq, ← hΨ_eq]
      refine TauCeti.Manifold.eq_of_contMDiff_tensorial (G := F) (W := V) Ψ x
        (fun {u₁ u₂} hu₁ hu₂ ↦ ?_) (fun {f u} hf hu ↦ ?_)
        (s' j).contMDiff (s j).contMDiff (h j).symm
      · have hsum : CMDiff ∞ (T% (u₁ + u₂)) := (⟨u₁, hu₁⟩ + ⟨u₂, hu₂⟩ : Cₛ^∞⟮I; F, V⟯).contMDiff
        simp only [Ψ, hu₁, hu₂, hsum, ↓reduceDIte]
        exact congr($(Φ.map_update_add w j ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) x)
      · have hsm : CMDiff ∞ (T% (f • u)) := hf.smul_section hu
        let gf : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
        have hsm_eq : gf • (⟨u, hu⟩ : Cₛ^∞⟮I; F, V⟯) = ⟨f • u, hsm⟩ := by
          ext y
          rw [smul_apply]
          rfl
        simp only [Ψ, hu, hsm, ↓reduceDIte, ← hsm_eq]
        exact congr($(Φ.map_update_smul w j gf ⟨u, hu⟩) x)
    rw [hw (s' j) rfl, hstep, hself, ih]

/-- Choose a global smooth section taking a prescribed value `v : V x` at `x`. -/
private def liftFibreVec (x : M) (v : V x) : Cₛ^∞⟮I; F, V⟯ :=
  (evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose

omit [FiniteDimensional ℝ F] in
private theorem liftFibreVec_apply_self (x : M) (v : V x) :
    liftFibreVec (I := I) (F := F) x v x = v := by
  simpa [liftFibreVec] using (evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v).choose_spec

/-- The continuous alternating map on the fibre `V x` induced by a `C^∞(M)`-multilinear
alternating map `Φ` on global smooth sections: read `Φ` on the model space `F` via the
trivialization at `x` (where continuity is automatic by finite-dimensionality of `F`), and pull
back to `V x`. -/
private def fibreAlternatingAt {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) (x : M) :
    V x [⋀^Fin k]→L[ℝ] ℝ :=
  let e := FiberBundle.trivializationAt F V x
  let fModel : F [⋀^Fin k]→ₗ[ℝ] ℝ :=
    { toFun w := Φ (fun i ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (w i))) x
      map_update_add' := fun [_] w i u₁ u₂ ↦ by
        let s : Fin k → Cₛ^∞⟮I; F, V⟯ :=
          fun j ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (w j))
        let t₁ := liftFibreVec (I := I) (F := F) x (e.symmL ℝ x u₁)
        let t₂ := liftFibreVec (I := I) (F := F) x (e.symmL ℝ x u₂)
        have heq₁ : Φ (fun j ↦ liftFibreVec (I := I) (F := F) x
            (e.symmL ℝ x (update w i (u₁ + u₂) j))) x = Φ (update s i (t₁ + t₂)) x := by
          refine apply_eq_of_eval_eq Φ fun j ↦ ?_
          by_cases hj : j = i
          · subst hj
            simp [t₁, t₂, liftFibreVec_apply_self]
          · simp [s, hj, liftFibreVec_apply_self]
        have heq₂ (u : F) :
            Φ (update s i (liftFibreVec (I := I) (F := F) x (e.symmL ℝ x u))) x =
              Φ (fun j ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (update w i u j))) x := by
          refine apply_eq_of_eval_eq Φ fun j ↦ ?_
          by_cases hj : j = i <;> simp [s, hj, liftFibreVec_apply_self]
        rw [heq₁, congr($(Φ.map_update_add s i t₁ t₂) x), ContMDiffMap.coe_add, Pi.add_apply,
          heq₂ u₁, heq₂ u₂]
      map_update_smul' := fun [_] w i c u ↦ by
        let s : Fin k → Cₛ^∞⟮I; F, V⟯ :=
          fun j ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (w j))
        let t := liftFibreVec (I := I) (F := F) x (e.symmL ℝ x u)
        have heq₁ : Φ (fun j ↦ liftFibreVec (I := I) (F := F) x
            (e.symmL ℝ x (update w i (c • u) j))) x =
              Φ (update s i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c • t)) x := by
          refine apply_eq_of_eval_eq Φ fun j ↦ ?_
          by_cases hj : j = i
          · subst hj
            simp [t, liftFibreVec_apply_self]
          · simp [s, hj, liftFibreVec_apply_self]
        have heq₂ :
            Φ (update s i t) x =
              Φ (fun j ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (update w i u j))) x := by
          refine apply_eq_of_eval_eq Φ fun j ↦ ?_
          by_cases hj : j = i <;> simp [s, t, hj, liftFibreVec_apply_self]
        rw [heq₁, congr($(Φ.map_update_smul s i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c) t) x)]
        simp [heq₂, smul_eq_mul]
      map_eq_zero_of_eq' w i j hwij hij :=
        congr($(Φ.map_eq_zero_of_eq
          (fun r ↦ liftFibreVec (I := I) (F := F) x (e.symmL ℝ x (w r)))
          (i := i) (j := j) (congrArg _ (congrArg _ hwij)) hij) x) }
  (AlternatingMap.toContinuousAlternatingMap fModel).compContinuousLinearMap
    (e.continuousLinearMapAt ℝ x)

private theorem fibreAlternatingAt_apply_sections {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    fibreAlternatingAt Φ x (fun i ↦ s i x) = Φ s x := by
  have hx : x ∈ (FiberBundle.trivializationAt F V x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F V x
  simp only [fibreAlternatingAt, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap, AlternatingMap.coe_mk, MultilinearMap.coe_mk]
  refine apply_eq_of_eval_eq Φ fun i ↦ ?_
  rw [liftFibreVec_apply_self]
  exact (FiberBundle.trivializationAt F V x).symmL_continuousLinearMapAt hx (s i x)

/-- Reconstruct a smooth section of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` from a `C^∞(M)`-multilinear
alternating map on smooth sections of `V`. -/
def ofAlternating {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ where
  toFun := fibreAlternatingAt Φ
  contMDiff_toFun x₀ := by
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun w ↦ ?_⟩
    let e := FiberBundle.trivializationAt F V x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x₀
    obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I)
      (e.open_baseSet.mem_nhds hx₀)).mem_iff.mp (e.open_baseSet.mem_nhds hx₀)
    -- Cut off the constant-coordinate local sections `y ↦ e.symm y (w i)` by `ρ`.
    let sw : Fin k → Cₛ^∞⟮I; F, V⟯ := fun i ↦
      ⟨(ρ : M → ℝ) • fun y ↦ e.symm y (w i),
        ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet hρ
          (TauCeti.Manifold.contMDiffOn_symm_baseSet (e := e) (w i))⟩
    refine (Φ sw).contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx₀, ρ.eventuallyEq_one] with y hy hρy
    have hsw :
        (fun i ↦ (FiberBundle.trivializationAt F V x₀).symmL ℝ y (w i)) = fun i ↦ sw i y := by
      ext i
      simp [sw, e, hρy, Trivialization.symmL_apply _ hy]
    simp [ContinuousAlternatingMap.inCoordinates, Function.comp_def, hsw,
      fibreAlternatingAt_apply_sections]

@[simp]
theorem ofAlternating_apply_sections {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) (x : M) :
    ofAlternating Φ x (fun i ↦ s i x) = Φ s x :=
  fibreAlternatingAt_apply_sections Φ s x

@[simp]
theorem evalAlternating_ofAlternating {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    (ofAlternating Φ).evalAlternating = Φ := by
  ext s x
  exact ofAlternating_apply_sections Φ s x

@[simp]
theorem ofAlternating_evalAlternating {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    ofAlternating φ.evalAlternating = φ := by
  ext x v
  have hv : v = fun i ↦ liftFibreVec (I := I) (F := F) x (v i) x := by
    ext i
    exact (liftFibreVec_apply_self x (v i)).symm
  conv_lhs => rw [hv]
  rw [ofAlternating_apply_sections, evalAlternating_apply, ← hv]

variable (I F V) in
/-- **Tensoriality of alternating bundle cochains**: smooth sections of
`fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` on a finite-rank smooth real vector bundle over a
finite-dimensional Hausdorff manifold are `C^∞(M)`-linearly equivalent to `C^∞(M)`-multilinear
alternating maps `Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯`. -/
def evalAlternatingEquiv (k : ℕ) :
    Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) where
  toFun := evalAlternating
  invFun := ofAlternating
  map_add' := evalAlternating_add
  map_smul' := evalAlternating_smul
  left_inv := ofAlternating_evalAlternating
  right_inv := evalAlternating_ofAlternating

@[simp]
theorem evalAlternatingEquiv_apply {k : ℕ}
    (φ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    evalAlternatingEquiv I F V k φ = φ.evalAlternating :=
  (rfl)

@[simp]
theorem evalAlternatingEquiv_symm_apply {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    (evalAlternatingEquiv I F V k).symm Φ = ofAlternating Φ :=
  (rfl)

/-- Two smooth alternating sections are equal whenever they agree on all tuples of global smooth
sections. -/
theorem eq_of_evalAlternating_eq {k : ℕ}
    {φ ψ : Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯}
    (h : φ.evalAlternating = ψ.evalAlternating) : φ = ψ :=
  (evalAlternatingEquiv I F V k).injective h

@[simp]
theorem interiorProd_ofAlternating {k : ℕ}
    (Φ : Cₛ^∞⟮I; F, V⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (a : Cₛ^∞⟮I; F, V⟯) :
    (ofAlternating Φ).interiorProd a = ofAlternating (Φ.curryLeft a) :=
  eq_of_evalAlternating_eq (by simp)

end Tensoriality

end ContMDiffSection
