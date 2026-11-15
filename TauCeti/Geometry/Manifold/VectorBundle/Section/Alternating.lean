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
public import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Exterior algebra and tensoriality of alternating bundle sections

Sections of the continuous-alternating-map bundle `x ↦ W x [⋀^Fin k]→L[ℝ] V x` on an arbitrary
vector bundle `W` carry a fibrewise interior product `ContMDiffSection.interior`, a fibrewise paired
wedge `ContMDiffSection.pairedWedge`, and (for scalar values `V x = ℝ`) a `C^n(M, ℝ)`-bilinear
exterior product `ContMDiffSection.wedge`. These extend the tangent-bundle operations on
differential forms to arbitrary vector bundles, in particular to the underlying bundle of a Lie
algebroid.

Over a finite-dimensional Hausdorff smooth manifold and a finite-rank smooth domain bundle `W`,
evaluating a smooth section of `x ↦ W x [⋀^ι]→L[ℝ] V x` pointwise on global smooth sections of `W`
identifies `Γ(Alt^ι(W, V))` `C^∞(M)`-linearly with the alternating `C^∞(M)`-multilinear maps
`Γ(W) [⋀^ι]→ₗ[C^∞(M)] Γ(V)` (`ContMDiffSection.alternatingEquiv`), with scalar specialization
`ContMDiffSection.scalarAlternatingEquiv`. The codomain bundle `V` need not have finite rank or
smooth transition functions.

## Main definitions

* `ContMDiffSection.trivialEquiv`: `C^n(M, 𝕜)`-linear equivalence between `C^n` sections of
  `Bundle.Trivial M FV` and `C^n⟮I, M; 𝓘(𝕜, FV), FV⟯`.
* `ContMDiffSection.interior`: `C^n(M, 𝕜)`-bilinear interior product inserting a section of `W` into
  the first slot of an alternating section.
* `ContMDiffSection.pairedWedge`: `C^n(M, ℝ)`-bilinear wedge of alternating sections along a `C^n`
  pairing section.
* `ContMDiffSection.wedge`: `C^n(M, ℝ)`-bilinear scalar wedge product on sections of
  `x ↦ W x [⋀^Fin k]→L[ℝ] ℝ`.
* `ContMDiffSection.alternatingEquiv`, `ContMDiffSection.scalarAlternatingEquiv`: `C^∞(M, ℝ)`-linear
  equivalences between smooth alternating bundle sections and `C^∞(M, ℝ)`-multilinear alternating
  maps on `Γ(W)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapters 12 and 14.
* Kirill C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Mathematical
  Society Lecture Note Series 213, Cambridge University Press (2005), §7.1.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti

section Coordinates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {FW FV : Type*} [NormedAddCommGroup FW] [NormedSpace 𝕜 FW]
  [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {M : Type*} [TopologicalSpace M]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, ContinuousAdd (V x)] [∀ x, ContinuousConstSMul 𝕜 (V x)]

/-- In a trivialization of the domain bundle `W`, the coordinate expression of the fibrewise
interior product `(φ y).curryLeftTopological (s y)` is the normed `curryLeft` applied to the
coordinates of `φ y` and of `s y`. -/
theorem inCoordinates_curryLeftTopological {k : ℕ}
    (s : ∀ y, W y) (φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y)
    (x₀ y : M) (hy : y ∈ (trivializationAt FW W x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y ((φ y).curryLeftTopological (s y)) =
      (ContinuousAlternatingMap.inCoordinates FW FV x₀ y x₀ y (φ y)).curryLeft
        ((trivializationAt FW W x₀ ⟨y, s y⟩).2) := by
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeftTopological_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Function.comp_apply]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j ↦ rfl) i
  simp only [Function.comp_apply, Matrix.cons_val_zero, Trivialization.symmL_apply _ hy,
    (trivializationAt FW W x₀).symm_apply_apply_mk hy]

end Coordinates

section PairedWedgeCoordinates

variable {FW F₁ F₂ F₃ M : Type*} [TopologicalSpace M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
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

/-- In valid coefficient trivializations, the coordinate expression of a fibrewise paired wedge on
an arbitrary vector bundle `W` is the normed paired wedge of the coordinate expressions. -/
theorem inCoordinates_pairedWedge {k l : ℕ}
    (μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y) (ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y)
    (x₀ y : M)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet)
    (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW F₃ x₀ y x₀ y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y)) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y (μ y))
        (ContinuousAlternatingMap.inCoordinates FW F₁ x₀ y x₀ y (φ y))
        (ContinuousAlternatingMap.inCoordinates FW F₂ x₀ y x₀ y (ψ y)) := by
  ext v
  simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousAlternatingMap.pairedWedge_apply, map_smul, map_sum]
  congr 2
  funext σ
  rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.symm_linearMapAt _ h₁, Trivialization.symm_linearMapAt _ h₂,
    Function.comp_def]

end PairedWedgeCoordinates

end TauCeti

section Regularity

section CurryRegularity

variable {𝕜 E H M FW FV : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW]
  [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  {k : ℕ} {n : ℕ∞ω} {u : Set M} {x : M}

/-- Inserting a `C^n` section of `W` into the first slot of a `C^n` alternating section preserves
`C^n` regularity within a set at a point. -/
theorem _root_.ContMDiffWithinAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y}
    (hs : CMDiffAt[u] n (T% s) x)
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
    exact TauCeti.inCoordinates_curryLeftTopological s φ x y hy
  exact hL.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- Inserting a `C^n` section of `W` into a `C^n` alternating section preserves regularity at a
point. -/
theorem _root_.ContMDiffAt.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y}
    (hs : CMDiffAt n (T% s) x)
    (hφ : ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) x :=
  ContMDiffWithinAt.curryLeftTopological_section hs hφ

/-- Inserting a `C^n` section of `W` into a `C^n` alternating section preserves regularity on a
set. -/
theorem _root_.ContMDiffOn.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y}
    (hs : CMDiff[u] n (T% s))
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) u :=
  fun y hy ↦ (hs y hy).curryLeftTopological_section (hφ y hy)

/-- Inserting a `C^n` section of `W` into a `C^n` alternating section yields a `C^n` alternating
section. -/
theorem _root_.ContMDiff.curryLeftTopological_section
    {s : ∀ y, W y} {φ : ∀ y, W y [⋀^Fin (k + 1)]→L[𝕜] V y}
    (hs : CMDiff n (T% s))
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin (k + 1)]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin (k + 1)]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin (k + 1)]→L[𝕜] V z) y (φ y))) :
    ContMDiff I (I.prod 𝓘(𝕜, FW [⋀^Fin k]→L[𝕜] FV)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[𝕜] FV)
        (E := fun z ↦ W z [⋀^Fin k]→L[𝕜] V z) y ((φ y).curryLeftTopological (s y))) :=
  fun y ↦ (hs y).curryLeftTopological_section (hφ y)

end CurryRegularity

section PairedWedgeRegularity

variable {E H M FW F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
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

/-- A `C^n` bundle pairing sends two `C^n` alternating bundle sections on `W` to a `C^n`
alternating bundle section within a set at a point. -/
theorem _root_.ContMDiffWithinAt.pairedWedge_section
    {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
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
    exact TauCeti.inCoordinates_pairedWedge μ hμ φ ψ x y h₁ h₂ h₃
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- Pointwise regularity of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffAt.pairedWedge_section
    {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
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

/-- Regularity on a set of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffOn.pairedWedge_section
    {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
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

/-- Global `C^n` regularity of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiff.pairedWedge_section
    {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
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

end Regularity

namespace ContMDiffSection

section TrivialEquiv

variable {𝕜 E H M FV : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FV] [NormedSpace 𝕜 FV] {n : ℕ∞ω}

/-- `C^n` sections of the trivial bundle `Bundle.Trivial M FV` are `C^n(M, 𝕜)`-linearly equivalent
to `C^n` maps `M → FV`. -/
def trivialEquiv : Cₛ^n⟮I; FV, Bundle.Trivial M FV⟯ ≃ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝓘(𝕜, FV), FV⟯ where
  toFun s := ⟨⇑s, (Bundle.Trivial.contMDiff_mk_iff.mp s.contMDiff).2⟩
  invFun f := ⟨⇑f, Bundle.Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_id, f.contMDiff⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' f s := by ext x; exact smul_apply f s x

@[simp]
theorem trivialEquiv_apply (s : Cₛ^n⟮I; FV, Bundle.Trivial M FV⟯) (x : M) :
    trivialEquiv s x = s x := by
  rw [trivialEquiv]
  rfl

@[simp]
theorem trivialEquiv_symm_apply (f : C^n⟮I, M; 𝓘(𝕜, FV), FV⟯) (x : M) :
    trivialEquiv.symm f x = f x := by
  rw [trivialEquiv]
  rfl

end TrivialEquiv

section Interior

variable {𝕜 E H M FW FV : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW]
  [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  {n : ℕ∞ω}

/-- The fibrewise interior product inserting a `C^n` section of `W` into the first slot of a `C^n`
alternating section, bundled as a `C^n(M, 𝕜)`-bilinear map. -/
def interior {k : ℕ} :
    Cₛ^n⟮I; FW, W⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
      Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯ →ₗ[C^n⟮I, M; 𝕜⟯]
        Cₛ^n⟮I; FW [⋀^Fin k]→L[𝕜] FV, fun x ↦ W x [⋀^Fin k]→L[𝕜] V x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; 𝕜⟯
    (fun s φ ↦ ⟨fun x ↦ (φ x).curryLeftTopological (s x),
      s.contMDiff.curryLeftTopological_section φ.contMDiff⟩)
    (fun s t φ ↦ by ext x v; simp)
    (fun f s φ ↦ by ext x v; simp)
    (fun s φ ψ ↦ by ext x v; simp)
    (fun f s φ ↦ by ext x v; simp)

/-- Fibrewise characterization of `ContMDiffSection.interior` via `curryLeftTopological`. -/
theorem interior_eq_curryLeftTopological {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯) (x : M) :
    interior s φ x = (φ x).curryLeftTopological (s x) := by
  rw [interior, LinearMap.mk₂_apply]
  rfl

@[simp]
theorem interior_apply {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[𝕜] V x⟯)
    (x : M) (v : Fin k → W x) :
    interior s φ x v = φ x (Matrix.vecCons (s x) v) := by
  rw [interior_eq_curryLeftTopological, ContinuousAlternatingMap.curryLeftTopological_apply_apply]

/-- Inserting the same section twice gives zero. -/
@[simp]
theorem interior_self {k : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 2)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 2)]→L[𝕜] V x⟯) :
    interior s (interior s φ) = 0 := by
  ext x v
  simp [interior_eq_curryLeftTopological]

/-- Interior products with two sections anticommute. -/
theorem interior_comm {k : ℕ} (s t : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 2)]→L[𝕜] FV, fun x ↦ W x [⋀^Fin (k + 2)]→L[𝕜] V x⟯) :
    interior s (interior t φ) = -interior t (interior s φ) := by
  have h := interior_self (s + t) φ
  simp only [map_add, LinearMap.add_apply, interior_self, zero_add, add_zero,
    add_eq_zero_iff_eq_neg] at h
  exact neg_eq_iff_eq_neg.mp h.symm

end Interior

section ExtOfInterior

variable {E H M FW FV : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n FW W I]

/-- On a `C^n` real vector bundle (`n ≤ ∞`) over a finite-dimensional Hausdorff smooth manifold,
two alternating sections of positive degree are equal as soon as all their interior products with
global `C^n` sections of `W` agree. -/
theorem ext_of_interior {k : ℕ}
    {φ ψ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯}
    (h : ∀ s : Cₛ^n⟮I; FW, W⟯, interior s φ = interior s ψ) :
    φ = ψ := by
  ext x v
  obtain ⟨s, hsx⟩ := evalLinearMap_surjective (I := I) (F := FW) n (V := W) x (v 0)
  have hcons : Matrix.vecCons (s x) (Fin.tail v) = v := by
    rw [evalLinearMap_apply] at hsx
    rw [hsx]
    exact Matrix.cons_head_tail v
  have hs := congr($(h s) x (Fin.tail v))
  simpa only [interior_apply, hcons] using hs

end ExtOfInterior

section Wedge

variable {E H M FW : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  {n : ℕ∞ω}

section Paired

variable {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
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

/-- The fibrewise paired wedge on sections of `Alt^•(W, Vᵢ)` along a `C^n` pairing section `μ`,
bundled as a `C^n(M, ℝ)`-bilinear map. -/
def pairedWedge {k l : ℕ}
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b)) :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] F₃, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] V₃ x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; ℝ⟯
    (fun φ ψ ↦ ⟨fun y ↦ ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y),
      μ.contMDiff.pairedWedge_section hμ φ.contMDiff ψ.contMDiff⟩)
    (fun φ φ' ψ ↦ by ext y v; simp)
    (fun f φ ψ ↦ by ext y v; simp)
    (fun φ ψ ψ' ↦ by ext y v; simp)
    (fun f φ ψ ↦ by ext y v; simp)

@[simp]
theorem pairedWedge_apply_section {k l : ℕ}
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯) (y : M) :
    pairedWedge μ hμ φ ψ y =
      ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y) := by
  rw [pairedWedge, LinearMap.mk₂_apply]
  rfl

end Paired

/-- The `C^n(M, ℝ)`-bilinear scalar wedge product on alternating bundle sections valued in `ℝ`,
normalized so that the wedge of two `1`-cochains is their two-term determinant. -/
def wedge {k l : ℕ} :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ :=
  pairedWedge
    (F₁ := ℝ) (F₂ := ℝ) (F₃ := ℝ)
    (V₁ := Bundle.Trivial M ℝ) (V₂ := Bundle.Trivial M ℝ) (V₃ := Bundle.Trivial M ℝ)
    ⟨fun _ ↦ ContinuousLinearMap.mul ℝ ℝ,
      TauCeti.contMDiff_const_bundlePairing (ContinuousLinearMap.mul ℝ ℝ)⟩
    (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂)

/-- Fibrewise characterization of `ContMDiffSection.wedge` via `pairedWedge` along
`ℝ`-multiplication. -/
theorem wedge_apply_section {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) (y : M) :
    wedge φ ψ y =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) := by
  rw [wedge, pairedWedge_apply_section]
  rfl

/-- Evaluation of the scalar wedge of two alternating sections on `W` as a normalized signed sum
over permutations. -/
theorem wedge_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ y (fun i ↦ v (σ (Fin.castAdd l i))) *
            ψ y (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [wedge_apply_section, ContinuousAlternatingMap.pairedWedge_apply]
  simp only [ContinuousLinearMap.mul_apply']

/-- The wedge of two `1`-cochains on `W` evaluates as a `2 × 2` determinant. -/
@[simp]
theorem wedge_apply_one_one
    (φ ψ : Cₛ^n⟮I; FW [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 1]→L[ℝ] ℝ⟯)
    (y : M) (v w : W y) :
    wedge φ ψ y ![v, w] = φ y ![v] * ψ y ![w] - φ y ![w] * ψ y ![v] := by
  rw [wedge_apply_section]
  simpa only [ContinuousLinearMap.mul_apply'] using
    ContinuousAlternatingMap.pairedWedge_apply_one_one (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (φ y) (ψ y) v w

/-- Wedging on the left with a degree-zero section multiplies by its scalar value on the empty
tuple. -/
@[simp]
theorem wedge_apply_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (0 + l) → W y) :
    wedge φ ψ y v = φ y 0 * ψ y (v ∘ Fin.cast (Nat.zero_add l).symm) := by
  rw [wedge_apply_section, ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  rfl

/-- Graded commutativity of the scalar wedge on alternating bundle sections:
`(φ ∧ ψ) y v = (-1)^(k * l) • (ψ ∧ φ) y (v ∘ Fin.cast _)`. -/
theorem wedge_comm_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v =
      (-1 : ℝ) ^ (k * l) • wedge ψ φ y (v ∘ Fin.cast (Nat.add_comm l k)) := by
  rw [wedge_apply_section, wedge_apply_section]
  exact ContinuousAlternatingMap.pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    mul_comm (φ y) (ψ y) v

/-- Wedging on the right with a degree-zero section multiplies by its scalar value on the empty
tuple. -/
@[simp]
theorem wedge_apply_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 0) → W y) :
    wedge φ ψ y v = φ y (v ∘ Fin.cast (Nat.add_zero k).symm) * ψ y 0 := by
  rw [wedge_comm_apply, wedge_apply_zero_left]
  simp only [Nat.mul_zero, pow_zero, one_smul, mul_comm]
  rfl

/-- Associativity of the scalar wedge on alternating bundle sections up to degree reassociation. -/
theorem wedge_assoc_apply {k l m : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (χ : Cₛ^n⟮I; FW [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin m]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l + m) → W y) :
    wedge (wedge φ ψ) χ y v =
      wedge φ (wedge ψ χ) y (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [wedge_apply_section, wedge_apply_section, wedge_apply_section, wedge_apply_section]
  exact ContinuousAlternatingMap.pairedWedge_assoc _ _ _ _
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    mul_assoc (φ y) (ψ y) (χ y) v

/-- Graded antiderivation rule for the interior product of a scalar wedge of positive-degree
sections: `ι_s (φ ∧ ψ) = ι_s φ ∧ ψ + (-1)^(k + 1) • φ ∧ ι_s ψ`. -/
theorem interior_wedge_apply {k l : ℕ}
    (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 1 + l) → W y) :
    interior (k := k + 1 + l) s (wedge φ ψ) y v =
      wedge (interior s φ) ψ y (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interior s ψ) y v := by
  simp only [interior_eq_curryLeftTopological, wedge_apply_section]
  exact ContinuousAlternatingMap.curryLeftTopological_pairedWedge
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) (s y) v

end Wedge

section ToAlternatingMap

variable {𝕜 E H M FW FV ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace 𝕜 FW]
  [NormedAddCommGroup FV] [NormedSpace 𝕜 FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle 𝕜 FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle 𝕜 FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  {n : ℕ∞ω}

/-- Evaluating a `C^n` alternating bundle section pointwise on `C^n` global sections of `W`
gives an alternating `C^n(M, 𝕜)`-multilinear map `Γ^n(W) [⋀^ι]→ₗ[C^n(M, 𝕜)] Γ^n(V)`. -/
def toAlternatingMap
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯) :
    Cₛ^n⟮I; FW, W⟯ [⋀^ι]→ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; FV, V⟯ where
  toFun s := ⟨fun x ↦ φ x (fun i ↦ s i x),
    φ.contMDiff.continuousAlternatingMap_bundle_apply fun i ↦ (s i).contMDiff⟩
  map_update_add' := by
    intro inst s i u₁ u₂
    ext x
    have hupd (v : Cₛ^n⟮I; FW, W⟯) :
        (fun j ↦ Function.update s i v j x) = Function.update (fun j ↦ s j x) i (v x) :=
      funext fun j ↦ Function.apply_update (fun _ (t : Cₛ^n⟮I; FW, W⟯) ↦ t x) s i v j
    simp only [coe_add, Pi.add_apply, coeFn_mk, hupd]
    exact (φ x).toAlternatingMap.map_update_add (fun j ↦ s j x) i (u₁ x) (u₂ x)
  map_update_smul' := by
    intro inst s i f u
    ext x
    have hupd (v : Cₛ^n⟮I; FW, W⟯) :
        (fun j ↦ Function.update s i v j x) = Function.update (fun j ↦ s j x) i (v x) :=
      funext fun j ↦ Function.apply_update (fun _ (t : Cₛ^n⟮I; FW, W⟯) ↦ t x) s i v j
    simp only [RingHom.id_apply, smul_apply, coeFn_mk, hupd]
    exact (φ x).toAlternatingMap.map_update_smul (fun j ↦ s j x) i (f x) (u x)
  map_eq_zero_of_eq' s i j hij hne := by
    ext x
    exact (φ x).map_eq_zero_of_eq (fun r ↦ s r x) (congr_arg (· x) hij) hne

@[simp]
theorem toAlternatingMap_apply
    (φ : Cₛ^n⟮I; FW [⋀^ι]→L[𝕜] FV, fun x ↦ W x [⋀^ι]→L[𝕜] V x⟯)
    (s : ι → Cₛ^n⟮I; FW, W⟯) (x : M) :
    toAlternatingMap φ s x = φ x (fun i ↦ s i x) := by
  rw [toAlternatingMap]
  rfl

end ToAlternatingMap

section EvalCongr

variable {E H M FW FV ι : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [FiniteDimensional ℝ FW]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle FV V] [VectorBundle ℝ FV V]
  [ContMDiffVectorBundle ∞ FW W I]

/-- A `C^∞(M, ℝ)`-multilinear alternating map on `Γ(W)` depends at `x` only on the values of its
input sections at `x`. -/
theorem alternatingMap_eval_congr
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (x : M) {s s' : ι → Cₛ^∞⟮I; FW, W⟯} (h : ∀ i, s i x = s' i x) :
    Φ s x = Φ s' x := by
  classical
  cases nonempty_fintype ι
  suffices ∀ q : Finset ι,
      Φ (fun i ↦ if i ∈ q then s' i else s i) x = Φ s x by
    simpa using (this Finset.univ).symm
  intro q
  induction q using Finset.induction_on with
  | empty => simp
  | @insert j q hj ih =>
    let u : ι → Cₛ^∞⟮I; FW, W⟯ := fun i ↦ if i ∈ q then s' i else s i
    have ih' : Φ u x = Φ s x := ih
    have hu_self : Function.update u j (s j) = u :=
      Function.update_eq_self_iff.mpr (by simp [u, hj])
    have hins : (fun i ↦ if i ∈ insert j q then s' i else s i) = Function.update u j (s' j) := by
      ext i
      by_cases hij : i = j <;> simp [u, hij]
    rw [hins, ← ih']
    conv_rhs => rw [← hu_self]
    let Ψ : (Π y : M, W y) → V x := fun t ↦
      if ht : CMDiff ∞ (T% t) then Φ (Function.update u j ⟨t, ht⟩) x else 0
    have hΨ (t : Cₛ^∞⟮I; FW, W⟯) : Φ (Function.update u j t) x = Ψ ⇑t := by
      simp only [Ψ, t.contMDiff, ↓reduceDIte]
      rfl
    rw [hΨ (s' j), hΨ (s j)]
    refine TauCeti.Manifold.eq_of_contMDiff_tensorial Ψ x
      (fun {t₁ t₂} ht₁ ht₂ ↦ ?_) (fun {f t} hf ht ↦ ?_) (s' j).contMDiff (s j).contMDiff (h j).symm
    · simp only [Ψ, ht₁, ht₂, ht₁.add_section ht₂, ↓reduceDIte]
      exact congr_arg (· x) (Φ.map_update_add u j ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩)
    · simp only [Ψ, ht, hf.smul_section ht, ↓reduceDIte]
      let F : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
      have hF : ⇑F = f := ContMDiffMap.coeFn_mk f hf
      have hft : (⟨f • t, hf.smul_section ht⟩ : Cₛ^∞⟮I; FW, W⟯) = F • ⟨t, ht⟩ := by
        ext y
        simp [smul_apply, hF]
      rw [hft]
      simpa only [RingHom.id_apply, smul_apply, hF] using
        congr_arg (· x) (Φ.map_update_smul u j F ⟨t, ht⟩)

end EvalCongr

section Tensoriality

variable {E H M FW FV ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  {W V : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ FW W I]

private def liftSection (x : M) (w : W x) : Cₛ^∞⟮I; FW, W⟯ :=
  Classical.choose (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

private lemma liftSection_apply (x : M) (w : W x) :
    liftSection (I := I) (FW := FW) x w x = w := by
  rw [liftSection]
  simpa only [evalLinearMap_apply] using
    Classical.choose_spec (evalLinearMap_surjective (I := I) (F := FW) ∞ (V := W) x w)

variable [FiniteDimensional ℝ FW]

/-- Pointwise fibre alternating map induced at `x` by an alternating `C^∞(M, ℝ)`-multilinear map
on `Γ(W)`. -/
private def fiberAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) :
    W x [⋀^ι]→ₗ[ℝ] V x where
  toFun w := Φ (fun i ↦ liftSection x (w i)) x
  map_update_add' := by
    intro inst w i u₁ u₂
    classical
    obtain rfl : inst = Classical.decEq ι := Subsingleton.elim _ _
    let s : ι → Cₛ^∞⟮I; FW, W⟯ := fun r ↦ liftSection x (w r)
    rw [alternatingMap_eval_congr Φ x
        (s' := Function.update s i (liftSection x u₁ + liftSection x u₂))
        (fun r ↦ by by_cases hr : r = i <;> simp [s, hr, liftSection_apply]),
      alternatingMap_eval_congr Φ x (s := fun r ↦ liftSection x (Function.update w i u₁ r))
        (s' := Function.update s i (liftSection x u₁))
        (fun r ↦ by by_cases hr : r = i <;> simp [s, hr, liftSection_apply]),
      alternatingMap_eval_congr Φ x (s := fun r ↦ liftSection x (Function.update w i u₂ r))
        (s' := Function.update s i (liftSection x u₂))
        (fun r ↦ by by_cases hr : r = i <;> simp [s, hr, liftSection_apply])]
    exact congr_arg (· x) (Φ.map_update_add s i (liftSection x u₁) (liftSection x u₂))
  map_update_smul' := by
    intro inst w i c u
    classical
    obtain rfl : inst = Classical.decEq ι := Subsingleton.elim _ _
    let s : ι → Cₛ^∞⟮I; FW, W⟯ := fun r ↦ liftSection x (w r)
    rw [alternatingMap_eval_congr Φ x
        (s' := Function.update s i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c • liftSection x u))
        (fun r ↦ by by_cases hr : r = i <;> simp [s, hr, liftSection_apply]),
      alternatingMap_eval_congr Φ x (s := fun r ↦ liftSection x (Function.update w i u r))
        (s' := Function.update s i (liftSection x u))
        (fun r ↦ by by_cases hr : r = i <;> simp [s, hr, liftSection_apply])]
    simpa only [RingHom.id_apply, smul_apply, ContMDiffMap.algebraMap_apply,
      Algebra.algebraMap_self] using
      congr_arg (· x) (Φ.map_update_smul s i (algebraMap ℝ C^∞⟮I, M; ℝ⟯ c) (liftSection x u))
  map_eq_zero_of_eq' w i j hij hne := by
    classical
    let s : ι → Cₛ^∞⟮I; FW, W⟯ :=
      Function.update (fun r ↦ liftSection x (w r)) j (liftSection x (w i))
    rw [alternatingMap_eval_congr Φ x (s' := s) (fun r ↦ by
      by_cases hr : r = j
      · subst hr; simp [s, hij, liftSection_apply]
      · simp [s, hr, liftSection_apply])]
    have hsij : s i = s j := by simp [s, hne]
    exact congr_arg (· x) (Φ.map_eq_zero_of_eq s hsij hne)

private def fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) (x : M) :
    W x [⋀^ι]→L[ℝ] V x :=
  let eW := VectorBundle.continuousLinearEquivAt ℝ FW W x
  (AlternatingMap.toContinuousAlternatingMap
    ((fiberAlternatingMap Φ x).compLinearMap eW.symm.toLinearMap)).compContinuousLinearMap
      (eW : W x →L[ℝ] FW)

private lemma fiberContinuousAlternatingMap_apply
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (x : M) (w : ι → W x) :
    fiberContinuousAlternatingMap Φ x w = Φ (fun i ↦ liftSection x (w i)) x := by
  rw [fiberContinuousAlternatingMap]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    AlternatingMap.coe_toContinuousAlternatingMap, AlternatingMap.compLinearMap_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, fiberAlternatingMap,
    AlternatingMap.coe_mk, MultilinearMap.coe_mk]
  congr 2
  funext i
  congr 1
  exact (VectorBundle.continuousLinearEquivAt ℝ FW W x).symm_apply_apply (w i)

private lemma fiberContinuousAlternatingMap_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    fiberContinuousAlternatingMap Φ x (fun i ↦ s i x) = Φ s x := by
  rw [fiberContinuousAlternatingMap_apply]
  exact alternatingMap_eval_congr Φ x fun i ↦ liftSection_apply x (s i x)

private lemma contMDiff_fiberContinuousAlternatingMap
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^ι]→L[ℝ] FV)) ∞
      (fun y ↦ TotalSpace.mk' (FW [⋀^ι]→L[ℝ] FV)
        (E := fun z ↦ W z [⋀^ι]→L[ℝ] V z) y (fiberContinuousAlternatingMap Φ y)) := by
  intro x₀
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.mpr fun v ↦ ?_⟩
  set eW := trivializationAt FW W x₀
  have hxW : x₀ ∈ eW.baseSet := FiberBundle.mem_baseSet_trivializationAt FW W x₀
  have hnhds : eW.baseSet ∈ 𝓝 x₀ := eW.open_baseSet.mem_nhds hxW
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hnhds).mem_iff.mp hnhds
  let s : ι → Cₛ^∞⟮I; FW, W⟯ := fun i ↦
    ⟨(ρ : M → ℝ) • fun y ↦ eW.symm y (v i),
      ρ.contMDiff.contMDiffOn.smul_section_of_tsupport eW.open_baseSet hρ
        (TauCeti.Manifold.contMDiffOn_symm_baseSet (v i))⟩
  set eV := trivializationAt FV V x₀
  have hxV : x₀ ∈ eV.baseSet := FiberBundle.mem_baseSet_trivializationAt FV V x₀
  have hΦs : ContMDiffAt I 𝓘(ℝ, FV) ∞ (fun y ↦ (eV ⟨y, Φ s y⟩).2) x₀ :=
    (contMDiffAt_totalSpace_iff.mp ((Φ s).contMDiff x₀)).2
  refine hΦs.congr_of_eventuallyEq ?_
  filter_upwards [ρ.eventuallyEq_one, hnhds, eV.open_baseSet.mem_nhds hxV] with y hρ1 hyW hyV
  have hs_eq : (fun i ↦ eW.symmL ℝ y (v i)) = fun i ↦ s i y := by
    funext i
    simp [s, hρ1, Trivialization.symmL_apply _ hyW]
  rw [ContinuousAlternatingMap.inCoordinates]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  change eV.continuousLinearMapAt ℝ y
      (fiberContinuousAlternatingMap Φ y (fun i ↦ eW.symmL ℝ y (v i))) = (eV ⟨y, Φ s y⟩).2
  rw [hs_eq, fiberContinuousAlternatingMap_apply_sections,
    eV.continuousLinearMapAt_apply_of_mem ℝ hyV]

/-- Smooth sections of `x ↦ W x [⋀^ι]→L[ℝ] V x` are `C^∞(M, ℝ)`-linearly equivalent to alternating
`C^∞(M, ℝ)`-multilinear maps `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] Γ(V)` when `W` is a finite-rank smooth real
vector bundle over a finite-dimensional Hausdorff smooth manifold. -/
def alternatingEquiv :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯) where
  toFun := toAlternatingMap
  invFun Φ := ⟨fiberContinuousAlternatingMap Φ, contMDiff_fiberContinuousAlternatingMap Φ⟩
  left_inv φ := by
    ext x w
    change fiberContinuousAlternatingMap (toAlternatingMap φ) x w = φ x w
    simp [fiberContinuousAlternatingMap_apply, liftSection_apply]
  right_inv Φ := by
    ext s x
    rw [toAlternatingMap_apply]
    exact fiberContinuousAlternatingMap_apply_sections Φ s x
  map_add' _ _ := by ext s x; simp
  map_smul' _ _ := by ext s x; simp

@[simp]
theorem alternatingEquiv_apply
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] FV, fun x ↦ W x [⋀^ι]→L[ℝ] V x⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    alternatingEquiv φ s x = φ x (fun i ↦ s i x) := by
  rw [alternatingEquiv]
  exact toAlternatingMap_apply φ s x

@[simp]
theorem alternatingEquiv_symm_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; FV, V⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    (alternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [alternatingEquiv]
  exact fiberContinuousAlternatingMap_apply_sections Φ s x

end Tensoriality

section ScalarTensoriality

variable {E H M FW ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [FiniteDimensional ℝ FW]
  {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [ContMDiffVectorBundle ∞ FW W I]

/-- Scalar-valued smooth alternating bundle sections on `W` are `C^∞(M, ℝ)`-linearly equivalent to
`C^∞(M, ℝ)`-multilinear alternating maps `Γ(W) [⋀^ι]→ₗ[C^∞(M, ℝ)] C^∞(M, ℝ)`. -/
def scalarAlternatingEquiv :
    Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯]
      (Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (alternatingEquiv (FV := ℝ) (V := Bundle.Trivial M ℝ)).trans
    { toFun Φ := trivialEquiv.toLinearMap.compAlternatingMap Φ
      invFun Ψ := trivialEquiv.symm.toLinearMap.compAlternatingMap Ψ
      left_inv Φ := by ext s x; simp
      right_inv Ψ := by ext s x; simp
      map_add' _ _ := by ext s x; simp
      map_smul' _ _ := by ext s x; simp }

@[simp]
theorem scalarAlternatingEquiv_apply
    (φ : Cₛ^∞⟮I; FW [⋀^ι]→L[ℝ] ℝ, fun x ↦ W x [⋀^ι]→L[ℝ] ℝ⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    scalarAlternatingEquiv φ s x = φ x (fun i ↦ s i x) := by
  rw [scalarAlternatingEquiv]
  simp

@[simp]
theorem scalarAlternatingEquiv_symm_apply_sections
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^ι]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (s : ι → Cₛ^∞⟮I; FW, W⟯) (x : M) :
    (scalarAlternatingEquiv.symm Φ) x (fun i ↦ s i x) = Φ s x := by
  rw [scalarAlternatingEquiv]
  simp

end ScalarTensoriality

section TensorialityInterior

variable {E H M FW : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] [FiniteDimensional ℝ FW]
  {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [ContMDiffVectorBundle ∞ FW W I]

section GeneralValue

variable {FV : Type*} [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V] [VectorBundle ℝ FV V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- `alternatingEquiv` intertwines `ContMDiffSection.interior` with `AlternatingMap.curryLeft`. -/
@[simp]
theorem alternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] FV, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] V x⟯) :
    alternatingEquiv (interior s φ) = (alternatingEquiv φ).curryLeft s := by
  ext t x
  simp only [alternatingEquiv_apply, interior_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

end GeneralValue

/-- `scalarAlternatingEquiv` intertwines `ContMDiffSection.interior` with
`AlternatingMap.curryLeft`. -/
@[simp]
theorem scalarAlternatingEquiv_interior {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (φ : Cₛ^∞⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯) :
    scalarAlternatingEquiv (interior s φ) = (scalarAlternatingEquiv φ).curryLeft s := by
  ext t x
  simp only [scalarAlternatingEquiv_apply, interior_apply, AlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

@[simp]
theorem scalarAlternatingEquiv_symm_curryLeft {k : ℕ} (s : Cₛ^∞⟮I; FW, W⟯)
    (Φ : Cₛ^∞⟮I; FW, W⟯ [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :
    scalarAlternatingEquiv.symm (Φ.curryLeft s) =
      interior s (scalarAlternatingEquiv.symm Φ) := by
  apply scalarAlternatingEquiv.injective
  simp

end TensorialityInterior

end ContMDiffSection
