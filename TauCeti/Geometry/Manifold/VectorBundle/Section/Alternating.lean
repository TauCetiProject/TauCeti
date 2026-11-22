/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Exterior algebra of alternating bundle sections

Sections of the continuous-alternating-map bundle `x ↦ W x [⋀^Fin k]→L[𝕜] V x` on an arbitrary
vector bundle `W` carry `ContMDiffSection.interior`, `ContMDiffSection.toAlternatingMap`, and the
empty-arity identification `ContMDiffSection.alternatingIsEmptyEquiv`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer (2013), Chs. 12, 14.
* Kirill C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, LMS Lecture Note
  Series 213, Cambridge University Press (2005), §7.1.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology

section GeneralField
variable {𝕜 E H M FW FV : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup FW] [NormedSpace 𝕜 FW] [NormedAddCommGroup FV]
  [NormedSpace 𝕜 FV] {W V : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W]
  [VectorBundle 𝕜 FW W] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle 𝕜 FV V] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] {n : ℕ∞ω}

section CurryRegularity
variable {k : ℕ} {u : Set M} {x : M}

/-- Inserting a `C^n` section of `W` into a `C^n` alternating section preserves regularity within a
set at a point. -/
theorem _root_.ContMDiffWithinAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiffAt[u] n (T% s) x)
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) y (φ y)) u x) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) y ((φ y).curryLeftTopological (s y))) u x := by
  rw [contMDiffWithinAt_section_iff] at hs
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ ⊢; refine ⟨hφ.1, ?_⟩
  let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := 𝕜) (E := FW) (F := FV)
    (n := k)).toContinuousLinearMap
  have hL := (L.contDiff.comp_contMDiffWithinAt hφ.2).clm_apply hs
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW FV x y x y
      ((φ y).curryLeftTopological (s y))) =ᶠ[𝓝 x] fun y ↦
      L (ContinuousAlternatingMap.inCoordinates FW FV x y x y (φ y))
        ((trivializationAt FW W x ⟨y, s y⟩).2) := by
    filter_upwards [(trivializationAt FW W x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt FW W x)] with y hy using
      TauCeti.inCoordinates_curryLeftTopological (s y) (φ y) hy
  exact hL.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem _root_.ContMDiffAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiffAt n (T% s) x)
    (hφ : ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) y (φ y)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) y ((φ y).curryLeftTopological (s y))) x :=
  ContMDiffWithinAt.curryLeftTopological_section hs hφ

theorem _root_.ContMDiffOn.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff[u] n (T% s))
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) y (φ y)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) y ((φ y).curryLeftTopological (s y))) u :=
  fun y hy ↦ (hs y hy).curryLeftTopological_section (hφ y hy)

theorem _root_.ContMDiff.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff n (T% s))
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) y (φ y))) :
    ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) y ((φ y).curryLeftTopological (s y))) :=
  fun y ↦ (hs y).curryLeftTopological_section (hφ y)
end CurryRegularity

namespace ContMDiffSection

/-- Fibrewise interior product inserting a `C^n` section of `W` into a `C^n` alternating section. -/
def interior {k : ℕ} : Cₛ^n⟮I; FW, W⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
    Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; FW [⋀^Fin k]→L[𝕜] FV, fun x ↦ W x [⋀^Fin k]→L[𝕜] V x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; 𝕜⟯ (fun s φ ↦ ⟨fun x ↦ (φ x).curryLeftTopological (s x),
      s.contMDiff.curryLeftTopological_section φ.contMDiff⟩)
    (fun _ _ _ ↦ by ext x v; simp) (fun _ _ _ ↦ by ext x v; simp)
    (fun _ _ _ ↦ by ext x v; simp) (fun _ _ _ ↦ by ext x v; simp)

theorem interior_eq_curryLeftTopological {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯) (x : M) :
    interior s φ x = (φ x).curryLeftTopological (s x) := by rw [interior]; simp

@[simp] theorem interior_apply {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯) (x : M)
    (v : Fin k → W x) : interior s φ x v = φ x (Matrix.vecCons (s x) v) := by
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
    add_eq_zero_iff_eq_neg] at h; exact neg_eq_iff_eq_neg.mp h.symm

/-- Pointwise evaluation of a degree cast on alternating bundle sections. -/
theorem alternating_cast_apply {m k : ℕ} (h : m = k)
    (φ : Cₛ^n⟮I; FW [⋀^Fin m]→L[𝕜] FV, fun x ↦ W x [⋀^Fin m]→L[𝕜] V x⟯) (x : M)
    (v : Fin k → W x) : LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
      (M := fun q ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯) h φ x v =
        φ x (v ∘ Fin.cast h) := by cases h; rfl

/-- The interior product commutes with degree casts on alternating bundle sections. -/
theorem interior_cast {m k : ℕ} (h : m + 1 = k + 1) (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (m + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (m + 1)]→L[𝕜] V x⟯) :
    interior s (LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
      (M := fun q ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯) h φ) =
      LinearEquiv.cast (R := C^n⟮I, M; 𝕜⟯)
        (M := fun q ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[𝕜] FV, fun x ↦ W x [⋀^Fin q]→L[𝕜] V x⟯)
        (Nat.succ_injective h) (interior s φ) := by cases Nat.succ_injective h; rfl

/-- Evaluating a `C^n` alternating bundle section pointwise on `C^n` global sections of `W` gives
an alternating `C^n(M, 𝕜)`-multilinear map `Γ^n(W) [⋀^ι]→ₗ[C^n(M, 𝕜)] Γ^n(V)`. -/
def toAlternatingMap {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯) :
    Cₛ^n⟮I; FW, W⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; FV, V⟯ where
  toFun s := ⟨fun x ↦ φ x (fun i ↦ s i x),
    φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ (s i).contMDiff⟩
  map_update_add' := fun {inst} s i u₁ u₂ ↦ by
    ext x; simp [Function.apply_update (fun _ (r : Cₛ^n⟮I; FW, W⟯) ↦ r x)]
  map_update_smul' := fun {inst} s i f u ↦ by
    ext x; simp [smul_apply, Function.apply_update (fun _ (r : Cₛ^n⟮I; FW, W⟯) ↦ r x)]
  map_eq_zero_of_eq' s i j hij hne := by
    ext x; exact (φ x).map_eq_zero_of_eq (fun r ↦ s r x) (congr_arg (· x) hij) hne

@[simp] theorem toAlternatingMap_apply {ι : Type*} [Fintype ι]
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯) (s : ι → Cₛ^n⟮I; FW, W⟯)
    (x : M) : toAlternatingMap φ s x = φ x (fun i ↦ s i x) := (rfl)

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
  toFun φ :=
    ⟨fun x ↦ φ x 0, φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ isEmptyElim i⟩
  invFun s := ⟨fun x ↦ ContinuousAlternatingMap.constOfIsEmpty 𝕜 (W x) ι (s x), fun x₀ ↦ by
    rw [contMDiffAt_continuousAlternatingMap_bundle]; refine ⟨contMDiffAt_id, ?_⟩
    have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW (E₁ := W) FV (E₂ := V)
        x₀ y x₀ y (ContinuousAlternatingMap.constOfIsEmpty 𝕜 (W y) ι (s y))) =ᶠ[𝓝 x₀] fun y ↦
        (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 FW FV ι).toLinearIsometry
          |>.toContinuousLinearMap ((trivializationAt FV V x₀ ⟨y, s y⟩).2) := by
      filter_upwards [(trivializationAt FV V x₀).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt FV V x₀)] with y hy using by
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
