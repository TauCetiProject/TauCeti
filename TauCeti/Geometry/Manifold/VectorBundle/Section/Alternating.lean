/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Exterior algebra and wedge regularity of alternating bundle sections

Sections of the continuous-alternating-map bundle `x ↦ W x [⋀^Fin k]→L[ℝ] V x` on an arbitrary
vector bundle `W` carry `ContMDiffSection.interior`, `ContMDiffSection.pairedWedge`,
`ContMDiffSection.wedge`, `ContMDiffSection.toAlternatingMap`, and the empty-arity identification
`ContMDiffSection.alternatingIsEmptyEquiv`. The regularity lemmas
`ContMDiffWithinAt.pairedWedge_section` (and its `At`/`On`/global variants) factor out and
generalize the paired-wedge regularity proofs of
`TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` (`inCoordinates_bundleWedgeWith`,
`ContMDiffWithinAt.bundleWedgeWith_form`), built over `ContinuousAlternatingMap.pairedWedge` and
`ContinuousAlternatingMap.pairedWedgeCLM`.

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
    (hφ : ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z)
        y (φ y)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z)
        y ((φ y).curryLeftTopological (s y))) x :=
  ContMDiffWithinAt.curryLeftTopological_section hs hφ

theorem _root_.ContMDiffOn.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff[u] n (T% s))
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z)
        y (φ y)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z)
        y ((φ y).curryLeftTopological (s y))) u :=
  fun y hy ↦ (hs y hy).curryLeftTopological_section (hφ y hy)

theorem _root_.ContMDiff.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y} (hs : CMDiff n (T% s))
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z)
        y (φ y))) :
    ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV) (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z)
        y ((φ y).curryLeftTopological (s y))) :=
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
    (x : M) (v : Fin k → W x) : interior s φ x v = φ x (Matrix.vecCons (s x) v) := by
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
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) x :=
  ContMDiffWithinAt.pairedWedge_section hμ hpair hφ hψ

theorem _root_.ContMDiffOn.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) u)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) u)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u :=
  fun y hy ↦ ContMDiffWithinAt.pairedWedge_section hμ (hpair y hy) (hφ y hy) (hψ y hy)

theorem _root_.ContMDiff.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)))
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)))
    (hψ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) :=
  fun y ↦ ContMDiffAt.pairedWedge_section hμ (hpair y) (hφ y) (hψ y)

/-- Fibrewise paired wedge on sections of `Alt^•(W, Vᵢ)` along a `C^n` pairing section `μ`. -/
def _root_.ContMDiffSection.pairedWedge
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

@[simp] theorem _root_.ContMDiffSection.pairedWedge_apply
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯) (y : M) :
    ContMDiffSection.pairedWedge μ hμ φ ψ y =
      ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y) := by
  rw [ContMDiffSection.pairedWedge, LinearMap.mk₂_apply, ContMDiffSection.coeFn_mk]
end PairedWedgeRegularity

namespace ContMDiffSection

section Wedge
variable {E H M FW : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W] {n : ℕ∞ω}

/-- `C^n(M, ℝ)`-bilinear scalar wedge product on alternating bundle sections valued in `ℝ`. -/
def wedge {k l : ℕ} :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ :=
  pairedWedge (F₁ := ℝ) (F₂ := ℝ) (F₃ := ℝ) (V₁ := Bundle.Trivial M ℝ) (V₂ := Bundle.Trivial M ℝ)
    (V₃ := Bundle.Trivial M ℝ) ⟨fun _ ↦ ContinuousLinearMap.mul ℝ ℝ,
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

end ContMDiffSection
