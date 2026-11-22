/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Exterior algebra and tensoriality of alternating bundle sections

Sections of the continuous-alternating-map bundle `x ↦ W x [⋀^Fin k]→L[ℝ] V x` on an arbitrary
vector bundle `W` carry `ContMDiffSection.interior`, `ContMDiffSection.pairedWedge`,
`ContMDiffSection.wedge`, and the empty-arity identification
`ContMDiffSection.alternatingIsEmptyEquiv`. The coordinate formula
`TauCeti.inCoordinates_pairedWedge` and regularity lemmas
`ContMDiffWithinAt.pairedWedge_section` (and its `At`/`On`/global variants) factor out and
generalize the paired-wedge regularity proofs of
`TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` (`inCoordinates_bundleWedgeWith`,
`ContMDiffWithinAt.bundleWedgeWith_form`), built over `ContinuousAlternatingMap.pairedWedge` and
`ContinuousAlternatingMap.pairedWedgeCLM`.

Over a finite-dimensional Hausdorff smooth manifold and a finite-rank smooth domain bundle `W`,
`C^∞(M, ℝ)`-multilinear alternating maps on sections are pointwise by
`AlternatingMap.contMDiffSection_eval_congr`, and pointwise evaluation identifies smooth sections
of `Alt^ι(W, V)` `C^∞(M, ℝ)`-linearly with `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] Γ(V)`
(`ContMDiffSection.alternatingEquiv`, `ContMDiffSection.scalarAlternatingEquiv`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer (2013), Chs. 12, 14.
* Kirill C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, LMS Lecture Note
  Series 213, Cambridge University Press (2005), §7.1.
* The paired-wedge coordinate and regularity design follows
  `TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` (`inCoordinates_bundleWedgeWith`,
  `ContMDiffWithinAt.bundleWedgeWith_form`), built on `ContinuousAlternatingMap.pairedWedge` /
  `ContinuousAlternatingMap.pairedWedgeCLM` and Yury Kudryashov's `DeRhamCohomology` project.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti

section Coordinates
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {FW FV : Type*}
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW] [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {M : Type*} [TopologicalSpace M] {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, ContinuousAdd (V x)] [∀ x, ContinuousConstSMul 𝕜 (V x)]

/-- Coordinate expression of `φ.curryLeftTopological w` in a domain trivialization. -/
theorem inCoordinates_curryLeftTopological {k : ℕ} {x₀ y : M}
    (w : W y) (φ : W y [⋀^Fin (k + 1)]→L[𝕜] V y)
    (hy : y ∈ (trivializationAt FW W x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y (φ.curryLeftTopological w) =
      (ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y φ).curryLeft
        ((trivializationAt FW W x₀ ⟨y, w⟩).2) := by
  ext v; simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Function.comp_apply]
  congr 2; funext i; refine Fin.cases ?_ (fun _ ↦ rfl) i
  simp only [Function.comp_apply, Matrix.cons_val_zero, Trivialization.symmL_apply _ hy,
    (trivializationAt FW W x₀).symm_apply_apply_mk hy]
end Coordinates

section PairedWedgeCoordinates
variable {FW F₁ F₂ F₃ M : Type*} [TopologicalSpace M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {W V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

/-- Coordinate expression of a fibrewise paired wedge in valid coefficient trivializations. -/
theorem inCoordinates_pairedWedge {k l : ℕ} {x₀ y : M}
    (μ : V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y) (hμ : Continuous (Function.uncurry fun a b ↦ μ a b))
    (φ : W y [⋀^Fin k]→L[ℝ] V₁ y) (ψ : W y [⋀^Fin l]→L[ℝ] V₂ y)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet) (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW F₃ x₀ y x₀ y
        (ContinuousAlternatingMap.pairedWedge μ hμ φ ψ) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y μ)
        (ContinuousAlternatingMap.inCoordinates FW F₁ x₀ y x₀ y φ)
        (ContinuousAlternatingMap.inCoordinates FW F₂ x₀ y x₀ y ψ) := by
  ext v; simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousAlternatingMap.pairedWedge_apply, map_smul, map_sum]
  congr 2; funext σ
  rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symm_linearMapAt _ h₁,
    Trivialization.symm_linearMapAt _ h₂, Function.comp_def]
end PairedWedgeCoordinates

end TauCeti

section GeneralField
variable {𝕜 E H M FW FV : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW] [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] {n : ℕ∞ω}

section CurryRegularity
variable {k : ℕ} {u : Set M} {x : M}

/-- Inserting a `C^n` section of `W` into a `C^n` alternating section preserves regularity within a
set at a point. -/
theorem _root_.ContMDiffWithinAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiffAt[u] n (T% s) x)
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y)) u x) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) u x := by
  rw [contMDiffWithinAt_section_iff] at hs
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ ⊢
  refine ⟨hφ.1, ?_⟩
  let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := 𝕜) (E := FW) (F := FV)
    (n := k)).toContinuousLinearMap
  have hL := (L.contDiff.comp_contMDiffWithinAt hφ.2).clm_apply hs
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW FV x y x y
      ((φ y).curryLeftTopological (s y))) =ᶠ[𝓝 x]
      fun y ↦ L (ContinuousAlternatingMap.inCoordinates FW FV x y x y (φ y))
        ((trivializationAt FW W x ⟨y, s y⟩).2) := by
    filter_upwards [(trivializationAt FW W x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt FW W x)] with y hy
    exact TauCeti.inCoordinates_curryLeftTopological (s y) (φ y) hy
  exact hL.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem _root_.ContMDiffAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiffAt n (T% s) x)
    (hφ : ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) x :=
  ContMDiffWithinAt.curryLeftTopological_section hs hφ

theorem _root_.ContMDiffOn.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff[u] n (T% s))
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) u :=
  fun y hy ↦ (hs y hy).curryLeftTopological_section (hφ y hy)

theorem _root_.ContMDiff.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff n (T% s))
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y))) :
    ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) :=
  fun y ↦ (hs y).curryLeftTopological_section (hφ y)
end CurryRegularity

namespace ContMDiffSection

/-- Fibrewise interior product inserting a `C^n` section of `W` into a `C^n` alternating section. -/
def interior {k : ℕ} :
    Cₛ^n⟮I; FW, W⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
        Cₛ^n⟮I; FW [⋀^Fin k]→L[𝕜] FV, fun x ↦ W x [⋀^Fin k]→L[𝕜] V x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; 𝕜⟯
    (fun s φ ↦ ⟨fun x ↦ (φ x).curryLeftTopological (s x),
      s.contMDiff.curryLeftTopological_section φ.contMDiff⟩)
    (fun _ _ _ ↦ by ext x v; simp) (fun _ _ _ ↦ by ext x v; simp)
    (fun _ _ _ ↦ by ext x v; simp) (fun _ _ _ ↦ by ext x v; simp)

theorem interior_eq_curryLeftTopological {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯) (x : M) :
    interior s φ x = (φ x).curryLeftTopological (s x) := by
  rw [interior, LinearMap.mk₂_apply, coeFn_mk]

@[simp] theorem interior_apply {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯)
    (x : M) (v : Fin k → W x) :
    interior s φ x v = φ x (Matrix.vecCons (s x) v) := by
  rw [interior_eq_curryLeftTopological, ContinuousAlternatingMap.curryLeftTopological_apply_apply]

@[simp] theorem interior_self {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 2)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 2)]→L[𝕜] V x⟯) :
    interior s (interior s φ) = 0 := by ext x v; simp [interior_eq_curryLeftTopological]

/-- Anticommutativity of the interior product: `ι_s (ι_t φ) = -ι_t (ι_s φ)`. -/
theorem interior_swap {k : ℕ} (s t : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 2)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 2)]→L[𝕜] V x⟯) :
    interior s (interior t φ) = -interior t (interior s φ) := by
  have h := interior_self (s + t) φ
  simp only [map_add, LinearMap.add_apply, interior_self, zero_add, add_zero,
    add_eq_zero_iff_eq_neg] at h
  exact neg_eq_iff_eq_neg.mp h.symm

/-- Pointwise evaluation of a degree cast on alternating bundle sections. -/
theorem alternating_cast_apply {m k : ℕ} (h : m = k)
    (φ : Cₛ^n⟮I; FW [⋀^Fin m]→L[𝕜] FV, fun x ↦ W x [⋀^Fin m]→L[𝕜] V x⟯)
    (x : M) (v : Fin k → W x) :
    LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯) h φ x v =
        φ x (v ∘ Fin.cast h) := by cases h; rfl

/-- The interior product commutes with degree casts on alternating bundle sections. -/
theorem interior_cast {m k : ℕ} (h : m + 1 = k + 1) (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (m + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (m + 1)]→L[𝕜] V x⟯) :
    interior s (LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯) h φ) =
      LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
        (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯)
        (Nat.succ_injective h) (interior s φ) := by cases Nat.succ_injective h; rfl

/-- Evaluating a `C^n` alternating bundle section pointwise on `C^n` global sections of `W` gives
an alternating `C^n(M, 𝕜)`-multilinear map `Γ^n(W) [⋀^ι]→ₗ[C^n(M, 𝕜)] Γ^n(V)`. -/
def toAlternatingMap {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯) :
    Cₛ^n⟮I; FW, W⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; FV, V⟯ where
  toFun s := ⟨fun x ↦ φ x (fun i ↦ s i x),
    φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ (s i).contMDiff⟩
  map_update_add' := by
    intro _ s i u₁ u₂; ext x
    have hf (t) : (fun j ↦ Function.update s i t j x) = Function.update (fun j ↦ s j x) i (t x) :=
      funext fun j ↦ Function.apply_update (fun _ (r : Cₛ^n⟮I; FW, W⟯) ↦ r x) s i t j
    simpa only [coe_add, Pi.add_apply, coeFn_mk, hf] using
      (φ x).map_update_add (fun j ↦ s j x) i (u₁ x) (u₂ x)
  map_update_smul' := by
    intro _ s i f u; ext x
    have hf (t) : (fun j ↦ Function.update s i t j x) = Function.update (fun j ↦ s j x) i (t x) :=
      funext fun j ↦ Function.apply_update (fun _ (r : Cₛ^n⟮I; FW, W⟯) ↦ r x) s i t j
    simpa only [RingHom.id_apply, smul_apply, coeFn_mk, hf] using
      (φ x).map_update_smul (fun j ↦ s j x) i (f x) (u x)
  map_eq_zero_of_eq' s i j hij hne := by
    ext x; exact (φ x).map_eq_zero_of_eq (fun r ↦ s r x) (congr_arg (· x) hij) hne

@[simp] theorem toAlternatingMap_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯)
    (s : ι → Cₛ^n⟮I; FW, W⟯) (x : M) :
    toAlternatingMap φ s x = φ x (fun i ↦ s i x) := (rfl)

/-- Pointwise evaluation intertwines `interior` with `AlternatingMap.curryLeft`. -/
@[simp] theorem toAlternatingMap_interior {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯) :
    toAlternatingMap (interior s φ) = (toAlternatingMap φ).curryLeft s := by
  ext t x; simp only [toAlternatingMap_apply, interior_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1; funext i; exact Fin.cases rfl (fun _ ↦ rfl) i

/-- For an empty index type `ι`, `C^n` sections of `x ↦ W x [⋀^ι]→L[𝕜] V x` are
`C^n(M, 𝕜)`-linearly equivalent to `C^n` sections of `V`. -/
def alternatingIsEmptyEquiv {ι : Type*} [Fintype ι] [IsEmpty ι] :
    Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; FV, V⟯ where
  toFun φ := ⟨fun x ↦ φ x 0,
    φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ isEmptyElim i⟩
  invFun s :=
    ⟨fun x ↦ ContinuousAlternatingMap.constOfIsEmpty 𝕜 (W x) ι (s x), fun x₀ ↦ by
      rw [contMDiffAt_continuousAlternatingMap_bundle]; refine ⟨contMDiffAt_id, ?_⟩
      have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW (E₁ := W) FV (E₂ := V) x₀ y x₀ y
          (ContinuousAlternatingMap.constOfIsEmpty 𝕜 (W y) ι (s y))) =ᶠ[𝓝 x₀]
          fun y ↦ (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 FW FV ι).toLinearIsometry
            |>.toContinuousLinearMap ((trivializationAt FV V x₀ ⟨y, s y⟩).2) := by
        filter_upwards [(trivializationAt FV V x₀).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt FV V x₀)] with y hy
        ext v; simp [ContinuousAlternatingMap.inCoordinates, hy]
      exact ((ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 FW FV ι).toLinearIsometry
        |>.toContinuousLinearMap.contDiff.comp_contMDiffAt
          (contMDiffAt_totalSpace_iff.mp (s.contMDiff x₀)).2).congr_of_eventuallyEq heq⟩
  left_inv φ := by ext x v; simpa using congr_arg (φ x) (Subsingleton.elim 0 v)
  right_inv s := by ext x; exact ContinuousAlternatingMap.constOfIsEmpty_apply 𝕜 (W x) ι (s x) 0
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp [smul_apply]

@[simp] theorem alternatingIsEmptyEquiv_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯) (x : M) :
    alternatingIsEmptyEquiv φ x = φ x 0 := (rfl)
@[simp] theorem alternatingIsEmptyEquiv_symm_apply {ι : Type*} [Fintype ι] [IsEmpty ι]
    (s : Cₛ^n⟮I; FV, V⟯) (x : M) (v : ι → W x) :
    (alternatingIsEmptyEquiv (FW := FW) (W := W) (ι := ι)).symm s x v = s x :=
  ContinuousAlternatingMap.constOfIsEmpty_apply 𝕜 (W x) ι (s x) v
end ContMDiffSection
end GeneralField

section PairedWedgeRegularity
variable {E H M FW F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {W V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  {k l : ℕ} {n : ℕ∞ω} {u : Set M} {x : M}

/-- Regularity within a set at a point of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffWithinAt.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃)
        (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) u x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁)
        (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) u x)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂)
        (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) u x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃)
        (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u x := by
  rw [contMDiffWithinAt_hom_bundle] at hpair
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ hψ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := (((ContinuousAlternatingMap.pairedWedgeCLM
    (E := FW) (k := k) (l := l)).contDiff.comp_contMDiffWithinAt hpair.2).clm_apply
      hφ.2).clm_apply hψ.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW F₃ x y x y
      (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) =ᶠ[𝓝 x]
      fun y ↦ ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x y x y (μ y))
        (ContinuousAlternatingMap.inCoordinates FW F₁ x y x y (φ y))
        (ContinuousAlternatingMap.inCoordinates FW F₂ x y x y (ψ y)) := by
    filter_upwards [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x),
      (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x),
      (trivializationAt F₃ V₃ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₃ V₃ x)] with y h₁ h₂ h₃
    exact TauCeti.inCoordinates_pairedWedge (μ y) (hμ y) (φ y) (ψ y) h₁ h₂ h₃
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem _root_.ContMDiffAt.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃)
        (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁)
        (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂)
        (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃)
        (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) x :=
  ContMDiffWithinAt.pairedWedge_section hμ hpair hφ hψ

theorem _root_.ContMDiffOn.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃)
        (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) u)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁)
        (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) u)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂)
        (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃)
        (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u :=
  fun y hy ↦ ContMDiffWithinAt.pairedWedge_section hμ (hpair y hy) (hφ y hy) (hψ y hy)

theorem _root_.ContMDiff.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃)
        (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)))
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁)
        (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)))
    (hψ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂)
        (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃)
        (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) :=
  fun y ↦ ContMDiffAt.pairedWedge_section hμ (hpair y) (hφ y) (hψ y)
end PairedWedgeRegularity

namespace ContMDiffSection

section ExtOfInterior
variable {E H M FW FV : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV] {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n FW W I]

/-- Positive-degree alternating sections on `W` are determined by their interior products with
global `C^n` sections of `W`. -/
theorem ext_of_interior {k : ℕ}
    {φ ψ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯}
    (h : ∀ s : Cₛ^n⟮I; FW, W⟯, interior s φ = interior s ψ) : φ = ψ := by
  ext x v
  obtain ⟨s, hsx⟩ := evalLinearMap_surjective (I := I) (F := FW) n (V := W) x (v 0)
  have hcons : Matrix.vecCons (s x) (Fin.tail v) = v := by
    rw [evalLinearMap_apply] at hsx; rw [hsx]; exact Matrix.cons_head_tail v
  simpa only [interior_apply, hcons] using congr($(h s) x (Fin.tail v))
end ExtOfInterior

section Wedge
variable {E H M FW : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W] {n : ℕ∞ω}

section Paired
variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

/-- Fibrewise paired wedge on sections of `Alt^•(W, Vᵢ)` along a `C^n` pairing section `μ`. -/
def pairedWedge {k l : ℕ}
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b)) :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] F₃, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] V₃ x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; ℝ⟯
    (fun φ ψ ↦ ⟨fun y ↦ ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y),
      μ.contMDiff.pairedWedge_section hμ φ.contMDiff ψ.contMDiff⟩)
    (fun _ _ _ ↦ by ext y v; simp) (fun _ _ _ ↦ by ext y v; simp)
    (fun _ _ _ ↦ by ext y v; simp) (fun _ _ _ ↦ by ext y v; simp)

@[simp] theorem pairedWedge_apply {k l : ℕ}
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯) (y : M) :
    pairedWedge μ hμ φ ψ y = ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y) := by
  rw [pairedWedge, LinearMap.mk₂_apply, coeFn_mk]
end Paired

/-- `C^n(M, ℝ)`-bilinear scalar wedge product on alternating bundle sections valued in `ℝ`. -/
def wedge {k l : ℕ} :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ :=
  pairedWedge (F₁ := ℝ) (F₂ := ℝ) (F₃ := ℝ)
    (V₁ := Bundle.Trivial M ℝ) (V₂ := Bundle.Trivial M ℝ) (V₃ := Bundle.Trivial M ℝ)
    ⟨fun _ ↦ ContinuousLinearMap.mul ℝ ℝ,
      TauCeti.contMDiff_const_bundlePairing (ContinuousLinearMap.mul ℝ ℝ)⟩
    (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂)

theorem wedge_apply' {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) (y : M) :
    wedge φ ψ y = ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) := by
  simp only [wedge, pairedWedge_apply, coeFn_mk]

theorem wedge_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v = (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
      ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
        (φ y (fun i ↦ v (σ (Fin.castAdd l i))) * ψ y (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [wedge_apply', ContinuousAlternatingMap.pairedWedge_apply]
  simp [ContinuousLinearMap.mul_apply']

@[simp] theorem wedge_apply_one_one
    (φ ψ : Cₛ^n⟮I; FW [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 1]→L[ℝ] ℝ⟯) (y : M) (v w : W y) :
    wedge φ ψ y ![v, w] = φ y ![v] * ψ y ![w] - φ y ![w] * ψ y ![v] := by
  rw [wedge_apply']; simp [ContinuousLinearMap.mul_apply']

@[simp] theorem wedge_apply_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (0 + l) → W y) :
    wedge φ ψ y v = φ y 0 * ψ y (v ∘ Fin.cast (Nat.zero_add l).symm) := by
  rw [wedge_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp [ContinuousLinearMap.mul_apply']

/-- Pointwise graded commutativity of the scalar wedge product:
`(φ ∧ ψ)_y = (-1)^(k * l) (ψ ∧ φ)_y` after reindexing. -/
theorem wedge_comm_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v = (-1 : ℝ) ^ (k * l) • wedge ψ φ y (v ∘ Fin.cast (Nat.add_comm l k)) := by
  rw [wedge_apply', wedge_apply']; exact ContinuousAlternatingMap.pairedWedge_comm
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ mul_comm (φ y) (ψ y) v

@[simp] theorem wedge_apply_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 0) → W y) :
    wedge φ ψ y v = φ y (v ∘ Fin.cast (Nat.add_zero k).symm) * ψ y 0 := by
  rw [wedge_apply', ContinuousAlternatingMap.pairedWedge_apply_zero_right]
  simp [ContinuousLinearMap.mul_apply']

/-- Pointwise associativity of the scalar wedge product: `(φ ∧ ψ) ∧ χ = φ ∧ (ψ ∧ χ)`. -/
theorem wedge_assoc_apply {k l m : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (χ : Cₛ^n⟮I; FW [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin m]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l + m) → W y) :
    wedge (wedge φ ψ) χ y v =
      wedge φ (wedge ψ χ) y (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [wedge_apply', wedge_apply', wedge_apply', wedge_apply']
  exact ContinuousAlternatingMap.pairedWedge_assoc _ _ _ _
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    mul_assoc (φ y) (ψ y) (χ y) v

/-- Graded antiderivation rule for `interior` across `wedge`. -/
theorem interior_wedge_apply {k l : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 1 + l) → W y) :
    interior (k := k + 1 + l) s (wedge φ ψ) y v =
      wedge (interior s φ) ψ y (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interior s ψ) y v := by
  simp only [interior_eq_curryLeftTopological, wedge_apply']
  exact ContinuousAlternatingMap.curryLeftTopological_pairedWedge
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) (s y) v

/-- Wedging on the left with a degree-`0` section scales by the underlying function. -/
theorem wedge_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    wedge φ ψ = LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.zero_add l).symm (trivialEquiv (alternatingIsEmptyEquiv φ) • ψ) := by
  ext x v; rw [wedge_apply_zero_left, alternating_cast_apply]; simp [smul_apply]

/-- Wedging on the right with a degree-`0` section scales by the underlying function. -/
theorem wedge_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯) :
    wedge φ ψ = LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.add_zero k).symm (trivialEquiv (alternatingIsEmptyEquiv ψ) • φ) := by
  ext x v; rw [wedge_apply_zero_right, alternating_cast_apply]; simp [smul_apply, mul_comm]

/-- Graded commutativity of the scalar wedge product as an identity of sections. -/
theorem wedge_comm {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    wedge φ ψ = (-1 : ℝ) ^ (k * l) • LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.add_comm l k) (wedge ψ φ) := by
  ext x v; rw [wedge_comm_apply, coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    alternating_cast_apply]

/-- Bundled graded antiderivation rule for `interior` across `wedge`. -/
theorem interior_wedge {k l : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯) :
    interior (k := k + 1 + l) s (wedge φ ψ) =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
        (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
        (show k + (l + 1) = k + 1 + l by omega) (wedge (interior s φ) ψ) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interior s ψ) := by
  ext x v; rw [interior_wedge_apply, coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    alternating_cast_apply, coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
end Wedge

section RealManifold
variable {E H M FW : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [NormedAddCommGroup FW] [NormedSpace ℝ FW] [FiniteDimensional ℝ FW]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [ContMDiffVectorBundle ∞ FW W I]

section Tensoriality
variable {FV : Type*} [NormedAddCommGroup FV] [NormedSpace ℝ FV] {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

private def liftSection (x : M) (w : W x) : Cₛ^∞⟮I; FW, W⟯ :=
  Classical.choose (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

omit [FiniteDimensional ℝ FW] in
private lemma liftSection_apply (x : M) (w : W x) : liftSection (I := I) (FW := FW) x w x = w := by
  rw [liftSection]; simpa only [evalLinearMap_apply] using
    Classical.choose_spec (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private lemma fiberAlternatingMap_update {ι : Type*} [Finite ι] [instDec : DecidableEq ι]
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (x : M) (w : ι → W x) (i : ι) (t : Cₛ^∞⟮I; FW, W⟯) (u : W x) (ht : t x = u) :
    Φ (fun r ↦ liftSection x (Function.update w i u r)) x =
      Φ (Function.update (fun r ↦ liftSection x (w r)) i t) x := by
  let _ := Fintype.ofFinite ι
  exact Φ.contMDiffSection_eval_congr x fun r ↦ by
    by_cases hr : r = i <;> simp [hr, liftSection_apply, ht]

section FixedIndex
variable {ι : Type*} [Fintype ι]

private def fiberAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) : W x [⋀^ι]→ₗ[ℝ] V x where
  toFun w := Φ (fun i ↦ liftSection x (w i)) x
  map_update_add' := by
    intro inst w i u₁ u₂
    have hU := fiberAlternatingMap_update (instDec := inst) Φ x w i
    rw [hU (liftSection x u₁ + liftSection x u₂) (u₁ + u₂) (by simp [liftSection_apply]),
      hU (liftSection x u₁) u₁ (liftSection_apply x u₁),
      hU (liftSection x u₂) u₂ (liftSection_apply x u₂)]
    exact congr_arg (· x)
      (Φ.map_update_add (fun r ↦ liftSection x (w r)) i (liftSection x u₁) (liftSection x u₂))
  map_update_smul' := by
    intro inst w i c u
    have hU := fiberAlternatingMap_update (instDec := inst) Φ x w i
    rw [hU (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c • liftSection x u) (c • u) (by simp [liftSection_apply]),
      hU (liftSection x u) u (liftSection_apply x u)]
    simpa only [RingHom.id_apply, smul_apply, ContMDiffMap.algebraMap_apply,
      Algebra.algebraMap_self] using congr_arg (· x)
      (Φ.map_update_smul (fun r ↦ liftSection x (w r)) i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c)
        (liftSection x u))
  map_eq_zero_of_eq' w i j hij hne := by
    classical
    let s : ι → Cₛ^∞⟮I; FW, W⟯ :=
      Function.update (fun r ↦ liftSection x (w r)) j (liftSection x (w i))
    rw [Φ.contMDiffSection_eval_congr x (s' := s) fun r ↦ by
      by_cases hr : r = j <;> simp [s, hr, hij, liftSection_apply]]
    exact congr_arg (· x) (Φ.map_eq_zero_of_eq s (by simp [s, hne]) hne)

private def fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) : W x [⋀^ι]→L[ℝ] V x :=
  let eW := VectorBundle.continuousLinearEquivAt ℝ FW W x
  (AlternatingMap.toContinuousAlternatingMap
    ((fiberAlternatingMap Φ x).compLinearMap eW.symm.toLinearMap)).compContinuousLinearMap
      (eW : W x →L[ℝ] FW)

private lemma fiberContinuousAlternatingMap_apply
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) (w : ι → W x) :
    fiberContinuousAlternatingMap Φ x w = Φ (fun i ↦ liftSection x (w i)) x := by
  simp only [fiberContinuousAlternatingMap, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap, AlternatingMap.compLinearMap_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, fiberAlternatingMap,
    AlternatingMap.coe_mk, MultilinearMap.coe_mk]
  exact congr_arg (Φ · x) <| funext fun i ↦ congr_arg (liftSection x) <|
    (VectorBundle.continuousLinearEquivAt ℝ FW W x).symm_apply_apply (w i)

private lemma fiberContinuousAlternatingMap_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    fiberContinuousAlternatingMap Φ x (fun i ↦ s i x) = Φ s x := by
  rw [fiberContinuousAlternatingMap_apply]
  exact Φ.contMDiffSection_eval_congr x fun i ↦ liftSection_apply x (s i x)

private lemma contMDiff_fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^ι]→L[ℝ] FV)) ∞
      (fun y ↦ TotalSpace.mk' (FW [⋀^ι]→L[ℝ] FV)
        (E := fun z ↦ W z [⋀^ι]→L[ℝ] V z) y (fiberContinuousAlternatingMap Φ y)) := by
  intro x₀; rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.mpr fun v ↦ ?_⟩
  set eW := trivializationAt FW W x₀ with heW
  have hnhds : eW.baseSet ∈ 𝓝 x₀ :=
    eW.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt FW W x₀)
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  let s : ι → Cₛ^∞⟮I; FW, W⟯ := fun i ↦
    ⟨(ρ : M → ℝ) • fun y ↦ eW.symm y (v i),
      ρ.contMDiff.contMDiffOn.smul_section_of_tsupport eW.open_baseSet hρ
        (TauCeti.Manifold.contMDiffOn_symm_baseSet (v i))⟩
  set eV := trivializationAt FV V x₀ with heV
  have hΦs : ContMDiffAt I 𝓘(ℝ, FV) ∞ (fun y ↦ (eV ⟨y, Φ s y⟩).2) x₀ :=
    (contMDiffAt_totalSpace_iff.mp ((Φ s).contMDiff x₀)).2
  refine hΦs.congr_of_eventuallyEq ?_
  filter_upwards [ρ.eventuallyEq_one, hnhds,
    eV.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt FV V x₀)] with y hρ1 hyW hyV
  have hs_eq : (fun i ↦ eW.symmL ℝ y (v i)) = fun i ↦ s i y := by
    funext i; simp [s, hρ1, Trivialization.symmL_apply _ hyW]
  rw [ContinuousAlternatingMap.inCoordinates]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, ← heW, ← heV,
    hs_eq, fiberContinuousAlternatingMap_apply_sections,
    eV.continuousLinearMapAt_apply_of_mem ℝ hyV]

/-- Smooth sections of `x ↦ W x [⋀^ι]→L[ℝ] V x` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] Γ(V)`. -/
def alternatingEquiv :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) where
  toFun := toAlternatingMap
  invFun Φ := ⟨fiberContinuousAlternatingMap Φ, contMDiff_fiberContinuousAlternatingMap Φ⟩
  left_inv φ := by ext x w; simp [fiberContinuousAlternatingMap_apply, liftSection_apply]
  right_inv Φ := by
    ext s x; rw [toAlternatingMap_apply]; exact fiberContinuousAlternatingMap_apply_sections Φ s x
  map_add' _ _ := by ext s x; simp
  map_smul' _ _ := by ext s x; simp

@[simp] theorem alternatingEquiv_apply
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) : alternatingEquiv φ s x = φ x (fun i ↦ s i x) := (rfl)
@[simp] theorem alternatingEquiv_symm_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) : (alternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [alternatingEquiv]; exact fiberContinuousAlternatingMap_apply_sections Φ s x
end FixedIndex

@[simp] theorem alternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯) :
    alternatingEquiv (interior s φ) = (alternatingEquiv φ).curryLeft s :=
  toAlternatingMap_interior s φ
@[simp] theorem alternatingEquiv_symm_curryLeft {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) :
    alternatingEquiv.symm (Φ.curryLeft s) = interior s (alternatingEquiv.symm Φ) := by
  apply alternatingEquiv.injective; simp
end Tensoriality

section ScalarTensoriality
/-- Scalar-valued smooth alternating bundle sections on `W` are `C^∞(M, ℝ)`-linearly equivalent to
`Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] C^∞(M, ℝ)`. -/
def scalarAlternatingEquiv {ι : Type*} [Fintype ι] :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (alternatingEquiv (FV := ℝ) (V := Bundle.Trivial M ℝ)).trans
    trivialEquiv.alternatingMapCongrRight

@[simp] theorem scalarAlternatingEquiv_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    scalarAlternatingEquiv φ s x = φ x (fun i ↦ s i x) := by rw [scalarAlternatingEquiv]; simp
@[simp] theorem scalarAlternatingEquiv_symm_apply_sections {ι : Type*} [Fintype ι]
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    (scalarAlternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [scalarAlternatingEquiv]; simp

@[simp] theorem scalarAlternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    scalarAlternatingEquiv (interior s φ) = (scalarAlternatingEquiv φ).curryLeft s := by
  simp only [scalarAlternatingEquiv, LinearEquiv.trans_apply, alternatingEquiv_interior]
  ext t x; simp
@[simp] theorem scalarAlternatingEquiv_symm_curryLeft {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    scalarAlternatingEquiv.symm (Φ.curryLeft s) = interior s (scalarAlternatingEquiv.symm Φ) := by
  apply scalarAlternatingEquiv.injective; simp
end ScalarTensoriality
end RealManifold

end ContMDiffSection
