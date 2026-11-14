/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.LocallyFinite
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Convex
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Compactness.Paracompact
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Smooth good covers of smooth manifolds

A *smooth good cover* (`TauCeti.SmoothGoodCover`) of a manifold `M` modelled on `I` is a locally
finite indexed open cover `openSet : Index → Opens M` equipped, for every nonempty finite set `s`
of indices whose open intersection `W = s.inf openSet` is nonempty, with a chosen centre in `W` and
a smooth homotopy `contract s hs hW : ℝ × W → W` equal to the constant map at the centre at time
`0`, equal to the identity at time `1`, and fixing the centre at all times.

Parametrizing the contraction over all of `ℝ` makes each slice and time reparametrization globally
smooth without boundary conditions, while `SmoothGoodCover.cylinderContract` restricts and swaps
the factors to `W × [0, 1]` with model `I.prod (𝓡∂ 1)`, matching the cylinder domain of
`TauCeti.homotopyOperator`. Every nonempty finite intersection is therefore contractible,
path-connected, and connected (`SmoothGoodCover.contractibleSpace_inf`,
`SmoothGoodCover.isPathConnected_inf`, `SmoothGoodCover.isConnected_inf`).

To refine an arbitrary open cover of a finite-dimensional Hausdorff second-countable boundaryless
smooth manifold by a smooth good cover (`TauCeti.exists_smoothGoodCover_refining`), we equip `M`
with an auxiliary smooth Riemannian metric via `TauCeti.nonempty_contMDiffRiemannianMetric` and its
extended metric `EMetricSpace.ofRiemannianMetric`, reducing to the Riemannian ball-refinement
theorem `TauCeti.exists_smoothGoodCover_eball_refining`. By Whitehead's theorem in the form of
`TauCeti.Manifold.exists_pos_isStronglyGeodesicallyConvex_eball`, small open Riemannian balls form
a neighbourhood basis at each point consisting of strongly geodesically convex, uniformly normal
open sets. Paracompactness refines the given open cover by a locally finite cover of such balls.
Nonempty finite intersections inherit strong geodesic convexity and uniform normality, so radial
geodesic contraction reparametrized by `Real.smoothTransition`
(`TauCeti.Manifold.geodesicOpenContract`) contracts each intersection smoothly inside itself to a
chosen point. On a compact manifold, second countability is automatic and extracting a finite
subcover gives `TauCeti.exists_finite_smoothGoodCover_eball_refining` and
`TauCeti.exists_finite_smoothGoodCover_refining`.

## Main definitions and results

* `TauCeti.SmoothGoodCover`: locally finite open cover with smooth basepoint-fixing contractions on
  all nonempty finite intersections.
* `TauCeti.SmoothGoodCover.cylinderContract`: the cylinder-ordered contraction `W × [0, 1] → W`
  smooth for `I.prod (𝓡∂ 1)`.
* `TauCeti.SmoothGoodCover.contractibleSpace_inf`, `isPathConnected_inf`, `isConnected_inf`:
  topological consequences on nonempty finite intersections.
* `TauCeti.SmoothGoodCover.comap`, `SmoothGoodCover.exists_finite`, `SmoothGoodCover.ofIsEmpty`:
  pullback along an index map, finite subcover extraction on compact spaces, and the empty cover.
* `TauCeti.exists_smoothGoodCover_eball_refining`,
  `TauCeti.exists_smoothGoodCover_refining`: smooth good refinement of any open cover on a
  finite-dimensional Hausdorff second-countable boundaryless smooth manifold.
* `TauCeti.exists_finite_smoothGoodCover_eball_refining`,
  `TauCeti.exists_finite_smoothGoodCover_refining`: finite smooth good refinement on a compact
  finite-dimensional Hausdorff boundaryless smooth manifold.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982), §5.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Theorem 6.17.
-/

public section

noncomputable section

open Bundle Filter Function Set TopologicalSpace Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

universe u

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- A *smooth good cover* of a manifold `M` modelled on `I`: a locally finite open cover whose
every nonempty finite intersection `W` carries a chosen centre in `W` and a smooth homotopy
`ℝ × W → W` from the constant map at the centre (at time `0`) to the identity (at time `1`) fixing
the centre at all times. -/
structure SmoothGoodCover where
  /-- The index type of the cover. -/
  Index : Type u
  /-- The open sets of the cover. -/
  openSet : Index → TopologicalSpace.Opens M
  covers : ∀ x : M, ∃ i, x ∈ openSet i
  locallyFinite : LocallyFinite fun i ↦ (openSet i : Set M)
  /-- The chosen centre of a nonempty finite intersection. -/
  centre : ∀ (s : Finset Index), s.Nonempty →
    Set.Nonempty ((s.inf openSet : TopologicalSpace.Opens M) : Set M) →
      ↥(s.inf openSet)
  /-- The chosen smooth contraction of a nonempty finite intersection to its centre. -/
  contract : ∀ (s : Finset Index) (_hs : s.Nonempty)
    (_hW : Set.Nonempty ((s.inf openSet : TopologicalSpace.Opens M) : Set M)),
      ℝ × ↥(s.inf openSet) → ↥(s.inf openSet)
  smooth : ∀ s hs hW, ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (contract s hs hW)
  at_zero : ∀ s hs hW x, contract s hs hW (0, x) = centre s hs hW
  at_one : ∀ s hs hW x, contract s hs hW (1, x) = x
  fixes_centre : ∀ s hs hW t, contract s hs hW (t, centre s hs hW) = centre s hs hW

attribute [simp] SmoothGoodCover.at_zero SmoothGoodCover.at_one SmoothGoodCover.fixes_centre

namespace SmoothGoodCover

variable {I} (C : SmoothGoodCover I (M := M))

/-- Two smooth good covers with equal index types, open-set families, and contractions are equal;
each centre is uniquely determined as the value of its contraction at time `0`. -/
theorem ext {C₁ C₂ : SmoothGoodCover I (M := M)} (hIdx : C₁.Index = C₂.Index)
    (hOpen : HEq C₁.openSet C₂.openSet) (hContract : HEq C₁.contract C₂.contract) :
    C₁ = C₂ := by
  cases C₁ with | mk Idx₁ open₁ cov₁ lf₁ cen₁ con₁ sm₁ z₁ o₁ f₁ =>
  cases C₂ with | mk Idx₂ open₂ cov₂ lf₂ cen₂ con₂ sm₂ z₂ o₂ f₂ =>
  subst hIdx
  rcases eq_of_heq hOpen with rfl
  rcases eq_of_heq hContract with rfl
  simp only [mk.injEq, heq_eq_eq, true_and, and_true]
  funext s hs hW
  let x₀ : ↥(s.inf open₁) := ⟨hW.some, hW.some_mem⟩
  exact (z₁ s hs hW x₀).symm.trans (z₂ s hs hW x₀)

/-- The open sets of a smooth good cover cover `Set.univ`. -/
theorem iUnion_openSet : (⋃ i, (C.openSet i : Set M)) = univ :=
  iUnion_eq_univ_iff.2 C.covers

/-- The supremum in `Opens M` of the members of a smooth good cover is `⊤`. -/
theorem iSup_openSet : (⨆ i, C.openSet i) = ⊤ := by
  ext x
  simp [C.covers x]

/-- The underlying set of a finite intersection `s.inf C.openSet` is `⋂ i ∈ s, C.openSet i`. -/
theorem coe_inf_openSet (s : Finset C.Index) :
    ((s.inf C.openSet : Opens M) : Set M) = ⋂ i ∈ s, (C.openSet i : Set M) :=
  (Opens.coe_finset_inf C.openSet s).trans (Finset.inf_set_eq_iInter s _)

/-- Membership in `s.inf C.openSet` is membership in `C.openSet i` for each `i ∈ s`. -/
theorem mem_inf_openSet {s : Finset C.Index} {x : M} :
    x ∈ (s.inf C.openSet : Opens M) ↔ ∀ i ∈ s, x ∈ C.openSet i := by
  rw [← SetLike.mem_coe, C.coe_inf_openSet, mem_iInter₂]
  rfl

/-- Each fixed-time slice `x ↦ C.contract s hs hW (t, x)` is smooth on `s.inf C.openSet`. -/
theorem contMDiff_contract_const_left (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) (t : ℝ) :
    ContMDiff I I ∞ (fun x ↦ C.contract s hs hW (t, x)) :=
  (C.smooth s hs hW).comp (contMDiff_const.prodMk contMDiff_id)

/-- Each fixed-point trajectory `t ↦ C.contract s hs hW (t, x)` is smooth on `ℝ`. -/
theorem contMDiff_contract_const_right (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) (x : ↥(s.inf C.openSet)) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t ↦ C.contract s hs hW (t, x)) :=
  (C.smooth s hs hW).comp (contMDiff_id.prodMk contMDiff_const)

/-- Cylinder-ordered smooth contraction `W × [0, 1] → W` modelled on `I.prod (𝓡∂ 1)`, matching the
domain factor order of `TauCeti.homotopyOperator`. -/
def cylinderContract (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty)
    (p : ↥(s.inf C.openSet) × Icc (0 : ℝ) 1) : ↥(s.inf C.openSet) :=
  C.contract s hs hW (p.2.1, p.1)

theorem cylinderContract_apply (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty)
    (p : ↥(s.inf C.openSet) × Icc (0 : ℝ) 1) :
    C.cylinderContract s hs hW p = C.contract s hs hW (p.2.1, p.1) :=
  (rfl)

/-- The cylinder-ordered contraction `W × [0, 1] → W` is smooth for `I.prod (𝓡∂ 1)`. -/
theorem contMDiff_cylinderContract (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    ContMDiff (I.prod (𝓡∂ 1)) I ∞ (C.cylinderContract s hs hW) :=
  (C.smooth s hs hW).comp
    (((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_snd).prodMk contMDiff_fst)

@[simp]
theorem cylinderContract_zero (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) (x : ↥(s.inf C.openSet)) :
    C.cylinderContract s hs hW (x, 0) = C.centre s hs hW :=
  C.at_zero s hs hW x

@[simp]
theorem cylinderContract_one (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) (x : ↥(s.inf C.openSet)) :
    C.cylinderContract s hs hW (x, 1) = x :=
  C.at_one s hs hW x

@[simp]
theorem cylinderContract_centre (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) (t : Icc (0 : ℝ) 1) :
    C.cylinderContract s hs hW (C.centre s hs hW, t) = C.centre s hs hW :=
  C.fixes_centre s hs hW t.1

/-- Every nonempty finite intersection of a smooth good cover is a contractible space. -/
theorem contractibleSpace_inf (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    ContractibleSpace ↥(s.inf C.openSet) := by
  let H : ContinuousMap.Homotopy (.id _) (.const _ (C.centre s hs hW)) :=
    { toFun := fun p : unitInterval × ↥(s.inf C.openSet) ↦ C.contract s hs hW (1 - p.1.1, p.2)
      continuous_toFun := (C.smooth s hs hW).continuous.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  exact (contractible_iff_id_nullhomotopic _).2 ⟨C.centre s hs hW, ⟨H⟩⟩

/-- Every nonempty finite intersection of a smooth good cover is a path-connected space. -/
theorem pathConnectedSpace_inf (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    PathConnectedSpace ↥(s.inf C.openSet) := by
  have := C.contractibleSpace_inf s hs hW
  infer_instance

/-- Every nonempty finite intersection of a smooth good cover is path-connected in `M`. -/
theorem isPathConnected_inf (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    IsPathConnected ((s.inf C.openSet : Opens M) : Set M) :=
  isPathConnected_iff_pathConnectedSpace.2 (C.pathConnectedSpace_inf s hs hW)

/-- Every nonempty finite intersection of a smooth good cover is a connected space. -/
theorem connectedSpace_inf (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    ConnectedSpace ↥(s.inf C.openSet) := by
  have := C.pathConnectedSpace_inf s hs hW
  infer_instance

/-- Every nonempty finite intersection of a smooth good cover is connected in `M`. -/
theorem isConnected_inf (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty) :
    IsConnected ((s.inf C.openSet : Opens M) : Set M) :=
  (C.isPathConnected_inf s hs hW).isConnected

/-- Every nonempty member of a smooth good cover is a contractible space. -/
theorem contractibleSpace_openSet (i : C.Index) (hi : (C.openSet i : Set M).Nonempty) :
    ContractibleSpace ↥(C.openSet i) := by
  let s : Finset C.Index := {i}
  have hW : ((s.inf C.openSet : Opens M) : Set M).Nonempty := by simpa [s] using hi
  have := C.contractibleSpace_inf s (Finset.singleton_nonempty i) hW
  have heq : ((s.inf C.openSet : Opens M) : Set M) = (C.openSet i : Set M) := by simp [s]
  exact (Homeomorph.setCongr heq).symm.contractibleSpace

/-- Every nonempty member of a smooth good cover is path-connected in `M`. -/
theorem isPathConnected_openSet (i : C.Index) (hi : (C.openSet i : Set M).Nonempty) :
    IsPathConnected (C.openSet i : Set M) := by
  have := C.contractibleSpace_openSet i hi
  exact isPathConnected_iff_pathConnectedSpace.2 inferInstance

/-- Every nonempty member of a smooth good cover is connected in `M`. -/
theorem isConnected_openSet (i : C.Index) (hi : (C.openSet i : Set M).Nonempty) :
    IsConnected (C.openSet i : Set M) :=
  (C.isPathConnected_openSet i hi).isConnected

variable (I) in
/-- On an empty manifold, the empty open family indexed by `PEmpty` is a smooth good cover. -/
def ofIsEmpty [IsEmpty M] : SmoothGoodCover I (M := M) where
  Index := PEmpty.{u + 1}
  openSet := PEmpty.elim
  covers x := isEmptyElim x
  locallyFinite x := isEmptyElim x
  centre _ _ hW := isEmptyElim hW.some
  contract _ _ hW := isEmptyElim hW.some
  smooth _ _ hW := isEmptyElim hW.some
  at_zero _ _ hW := isEmptyElim hW.some
  at_one _ _ hW := isEmptyElim hW.some
  fixes_centre _ _ hW := isEmptyElim hW.some

/-- Pull back a smooth good cover along a reindexing `f : α → C.Index` whose open sets still cover
`M` and remain locally finite (for instance, the inclusion of a finite subcover). -/
def comap {α : Type u} (f : α → C.Index) (hcov : ∀ x : M, ∃ a, x ∈ C.openSet (f a))
    (hlf : LocallyFinite fun a ↦ (C.openSet (f a) : Set M)) :
    SmoothGoodCover I (M := M) :=
  letI := Classical.decEq C.Index
  { Index := α
    openSet := C.openSet ∘ f
    covers := hcov
    locallyFinite := hlf
    centre := fun s hs hW ↦
      let hinf := Finset.inf_image s f C.openSet
      let hWt : (((s.image f).inf C.openSet : Opens M) : Set M).Nonempty :=
        ⟨hW.some, (congrArg (hW.some ∈ ·) hinf).mpr hW.some_mem⟩
      let c := C.centre (s.image f) (hs.image f) hWt
      ⟨c.1, (congrArg (c.1 ∈ ·) hinf).mp c.2⟩
    contract := fun s hs hW p ↦
      let hinf := Finset.inf_image s f C.openSet
      let hWt : (((s.image f).inf C.openSet : Opens M) : Set M).Nonempty :=
        ⟨hW.some, (congrArg (hW.some ∈ ·) hinf).mpr hW.some_mem⟩
      let y := C.contract (s.image f) (hs.image f) hWt
        (p.1, ⟨p.2.1, (congrArg (p.2.1 ∈ ·) hinf).mpr p.2.2⟩)
      ⟨y.1, (congrArg (y.1 ∈ ·) hinf).mp y.2⟩
    smooth := fun s hs hW ↦ by
      let hinf := Finset.inf_image s f C.openSet
      let hWt : (((s.image f).inf C.openSet : Opens M) : Set M).Nonempty :=
        ⟨hW.some, (congrArg (hW.some ∈ ·) hinf).mpr hW.some_mem⟩
      let incl : ↥(s.inf (C.openSet ∘ f)) → ↥((s.image f).inf C.openSet) :=
        fun y ↦ ⟨y.1, (congrArg (y.1 ∈ ·) hinf).mpr y.2⟩
      have hincl : ContMDiff I I ∞ incl :=
        (TauCeti.ContMDiff.subtypeVal_comp_iff ((s.image f).inf C.openSet) incl).1
          contMDiff_subtype_val
      have harg : ContMDiff ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod I) ∞
          (fun p : ℝ × ↥(s.inf (C.openSet ∘ f)) ↦ (p.1, incl p.2)) :=
        contMDiff_fst.prodMk (hincl.comp contMDiff_snd)
      have hcomp : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞
          (fun p : ℝ × ↥(s.inf (C.openSet ∘ f)) ↦
            C.contract (s.image f) (hs.image f) hWt (p.1, incl p.2)) :=
        (C.smooth (s.image f) (hs.image f) hWt).comp harg
      refine (TauCeti.ContMDiff.subtypeVal_comp_iff (s.inf (C.openSet ∘ f)) _).1 ?_
      exact (contMDiff_subtype_val (U := (s.image f).inf C.openSet)).comp hcomp
    at_zero := fun s hs _ x ↦ Subtype.ext <| by
      dsimp only
      exact congrArg (@Subtype.val M (· ∈ (s.image f).inf C.openSet))
        (C.at_zero (s.image f) (hs.image f) _
          ⟨x.1, (congrArg (x.1 ∈ ·) (Finset.inf_image s f C.openSet)).mpr x.2⟩)
    at_one := fun s hs _ x ↦ Subtype.ext <| by
      dsimp only
      exact congrArg (@Subtype.val M (· ∈ (s.image f).inf C.openSet))
        (C.at_one (s.image f) (hs.image f) _
          ⟨x.1, (congrArg (x.1 ∈ ·) (Finset.inf_image s f C.openSet)).mpr x.2⟩)
    fixes_centre := fun s hs _ t ↦ Subtype.ext <| by
      dsimp only
      exact congrArg (@Subtype.val M (· ∈ (s.image f).inf C.openSet))
        (C.fixes_centre (s.image f) (hs.image f) _ t) }

/-- Identification of the index type of `C.comap f hcov hlf` with `α`. -/
def comapIndexEquiv {α : Type u} (f : α → C.Index) (hcov : ∀ x : M, ∃ a, x ∈ C.openSet (f a))
    (hlf : LocallyFinite fun a ↦ (C.openSet (f a) : Set M)) :
    (C.comap f hcov hlf).Index ≃ α :=
  Equiv.refl α

instance instFiniteComapIndex {α : Type u} [Finite α] (f : α → C.Index)
    (hcov : ∀ x : M, ∃ a, x ∈ C.openSet (f a))
    (hlf : LocallyFinite fun a ↦ (C.openSet (f a) : Set M)) :
    Finite (C.comap f hcov hlf).Index :=
  ‹Finite α›

@[simp]
theorem openSet_comap {α : Type u} (f : α → C.Index) (hcov : ∀ x : M, ∃ a, x ∈ C.openSet (f a))
    (hlf : LocallyFinite fun a ↦ (C.openSet (f a) : Set M))
    (i : (C.comap f hcov hlf).Index) :
    (C.comap f hcov hlf).openSet i = C.openSet (f (C.comapIndexEquiv f hcov hlf i)) :=
  (rfl)

/-- On a compact space, any smooth good cover admits a smooth good subcover with finite index type
whose members are members of the original cover. -/
theorem exists_finite [CompactSpace M] :
    ∃ C' : SmoothGoodCover I (M := M),
      Finite C'.Index ∧ ∀ a', ∃ a, C'.openSet a' = C.openSet a := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun a ↦ (C.openSet a : Set M))
    (fun a ↦ (C.openSet a).isOpen) (by rw [C.iUnion_openSet])
  have hcov : ∀ x : M, ∃ a : ↥t, x ∈ C.openSet a.1 := fun x ↦ by
    obtain ⟨a, hat, hxa⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact ⟨⟨a, hat⟩, hxa⟩
  exact ⟨C.comap Subtype.val hcov (locallyFinite_of_finite _), inferInstance,
    fun a' ↦ ⟨(C.comapIndexEquiv Subtype.val hcov (locallyFinite_of_finite _) a').1,
      C.openSet_comap Subtype.val hcov (locallyFinite_of_finite _) a'⟩⟩

end SmoothGoodCover

end Carrier

/-! ### Constructing smooth good refinements from Riemannian convex balls -/

section Existence

open TauCeti.Manifold

/-- Any locally finite open cover of a Riemannian manifold by strongly geodesically convex and
uniformly normal open sets assembles into a `SmoothGoodCover` via radial geodesic contractions. -/
private def smoothGoodCoverOfGeodesicallyConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type u} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {α : Type u} (V : α → Opens M) (hcov : ∀ x : M, ∃ a, x ∈ V a)
    (hlf : LocallyFinite fun a ↦ (V a : Set M))
    (hconv : ∀ a, IsStronglyGeodesicallyConvex I (V a : Set M))
    (hnorm : ∀ a, IsUniformlyNormal I (V a : Set M)) :
    SmoothGoodCover I (M := M) :=
  let hW_conv : ∀ (s : Finset α), s.Nonempty →
      IsStronglyGeodesicallyConvex I ((s.inf V : Opens M) : Set M) := fun s hs ↦ by
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    exact IsStronglyGeodesicallyConvex.biInter hs fun a _ ↦ hconv a
  let hW_norm : ∀ (s : Finset α), s.Nonempty →
      IsUniformlyNormal I ((s.inf V : Opens M) : Set M) := fun s hs ↦ by
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    exact IsUniformlyNormal.biInter (Finset.coe_nonempty.2 hs) fun a _ ↦ hnorm a
  { Index := α
    openSet := V
    covers := hcov
    locallyFinite := hlf
    centre := fun _ _ hW ↦ ⟨hW.some, hW.some_mem⟩
    contract := fun s hs hW ↦
      geodesicOpenContract I (s.inf V) (hW_conv s hs) hW.some_mem
        ((hW_norm s hs).isNormalDomain_ball hW.some_mem)
        ((hW_norm s hs).subset_image_riemannianExp_ball hW.some_mem)
    smooth := fun s hs hW ↦
      contMDiff_geodesicOpenContract (s.inf V) (hW_conv s hs) hW.some_mem
        ((hW_norm s hs).isNormalDomain_ball hW.some_mem)
        ((hW_norm s hs).subset_image_riemannianExp_ball hW.some_mem)
    at_zero := fun s hs hW x ↦
      geodesicOpenContract_zero_left (s.inf V) (hW_conv s hs) hW.some_mem
        ((hW_norm s hs).isNormalDomain_ball hW.some_mem)
        ((hW_norm s hs).subset_image_riemannianExp_ball hW.some_mem) x
    at_one := fun s hs hW x ↦
      geodesicOpenContract_one_left (s.inf V) (hW_conv s hs) hW.some_mem
        ((hW_norm s hs).isNormalDomain_ball hW.some_mem)
        ((hW_norm s hs).subset_image_riemannianExp_ball hW.some_mem) x
    fixes_centre := fun s hs hW t ↦
      geodesicOpenContract_centre (s.inf V) (hW_conv s hs) hW.some_mem
        ((hW_norm s hs).isNormalDomain_ball hW.some_mem)
        ((hW_norm s hs).subset_image_riemannianExp_ball hW.some_mem) t }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- **Existence of smooth good covers by geodesically convex Riemannian balls.** Every open cover
of a finite-dimensional second-countable boundaryless smooth Riemannian manifold admits a
refinement by a smooth good cover whose members are strongly geodesically convex, uniformly normal
open Riemannian balls `Metric.eball x (ENNReal.ofReal r)` of positive radius. -/
theorem exists_smoothGoodCover_eball_refining
    {M : Type u} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [SecondCountableTopology M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {ι : Type*} (U : ι → TopologicalSpace.Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M),
      (∀ a, ∃ i, C.openSet a ≤ U i) ∧
      ∀ a, IsStronglyGeodesicallyConvex I (C.openSet a : Set M) ∧
        IsUniformlyNormal I (C.openSet a : Set M) ∧
        ∃ x : M, ∃ r > 0, (C.openSet a : Set M) = Metric.eball x (ENNReal.ofReal r) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose idx hidx using hU
  have hsub_ball : ∀ x : M, ∃ δ > 0, Metric.eball x (ENNReal.ofReal δ) ⊆ U (idx x) := fun x ↦ by
    obtain ⟨ε, hε, hεU⟩ := EMetric.isOpen_iff.1 (U (idx x)).isOpen x (hidx x)
    obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    exact ⟨δ, ENNReal.ofReal_pos.1 hδ0, (Metric.eball_subset_eball hδε.le).trans hεU⟩
  choose δ hδ0 hδU using hsub_ball
  choose r_conv hr_conv _ hball using
    exists_pos_isStronglyGeodesicallyConvex_eball (I := I) (M := M)
  let R : M → ℝ := fun x ↦ min (r_conv x) (δ x)
  have hR : ∀ x, 0 < R x := fun x ↦ lt_min (hr_conv x) (hδ0 x)
  have hbasis : ∀ x : M, (𝓝 x).HasBasis (fun r : ℝ ↦ 0 < r ∧ r ≤ R x)
      (fun r ↦ Metric.eball x (ENNReal.ofReal r)) := fun x ↦ by
    refine Metric.nhds_basis_eball.to_hasBasis' (fun ε hε ↦ ?_) fun r hr ↦
      Metric.eball_mem_nhds x (ENNReal.ofReal_pos.2 hr.1)
    obtain ⟨η, -, hη0, hηε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    exact ⟨min η (R x), ⟨lt_min (ENNReal.ofReal_pos.1 hη0) (hR x), min_le_right _ _⟩,
      Metric.eball_subset_eball ((ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hηε.le)⟩
  obtain ⟨α, c, r, hr, hcov_univ, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis hbasis
  let V : α → Opens M := fun a ↦ ⟨Metric.eball (c a) (ENNReal.ofReal (r a)), Metric.isOpen_eball⟩
  have hcov : ∀ x : M, ∃ a, x ∈ V a := fun x ↦ mem_iUnion.1 (hcov_univ.ge (mem_univ x))
  have hra : ∀ a, r a ∈ Ioc 0 (r_conv (c a)) :=
    fun a ↦ ⟨(hr a).1, (hr a).2.trans (min_le_left _ _)⟩
  refine ⟨smoothGoodCoverOfGeodesicallyConvex I V hcov hlf
    (fun a ↦ (hball (c a) (r a) (hra a)).1) (fun a ↦ (hball (c a) (r a) (hra a)).2),
    fun a ↦ ⟨idx (c a), (Metric.eball_subset_eball
      (ENNReal.ofReal_le_ofReal ((hr a).2.trans (min_le_right _ _)))).trans (hδU (c a))⟩,
    fun a ↦ ⟨(hball (c a) (r a) (hra a)).1, (hball (c a) (r a) (hra a)).2,
      c a, r a, (hr a).1, rfl⟩⟩

/-- **Existence of smooth good covers refining a given open cover.** Every open cover of a
finite-dimensional Hausdorff second-countable boundaryless smooth manifold admits a refinement by a
smooth good cover. -/
theorem exists_smoothGoodCover_refining
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M] [I.Boundaryless] {ι : Type*}
    (U : ι → TopologicalSpace.Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), ∀ a, ∃ i, C.openSet a ≤ U i := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let : EMetricSpace M := .ofRiemannianMetric I M
  have : IsRiemannianManifold I M := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨C, href, -⟩ := exists_smoothGoodCover_eball_refining I U hU
  exact ⟨C, href⟩

/-- **Existence of finite smooth good covers by geodesically convex Riemannian balls.** On a
compact finite-dimensional boundaryless smooth Riemannian manifold, every open cover admits a
finite smooth good refinement whose members are strongly geodesically convex, uniformly normal open
Riemannian balls `Metric.eball x (ENNReal.ofReal r)` of positive radius. -/
theorem exists_finite_smoothGoodCover_eball_refining
    {M : Type u} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {ι : Type*} (U : ι → TopologicalSpace.Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M),
      Finite C.Index ∧ (∀ a, ∃ i, C.openSet a ≤ U i) ∧
      ∀ a, IsStronglyGeodesicallyConvex I (C.openSet a : Set M) ∧
        IsUniformlyNormal I (C.openSet a : Set M) ∧
        ∃ x : M, ∃ r > 0, (C.openSet a : Set M) = Metric.eball x (ENNReal.ofReal r) := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  obtain ⟨C, href, hball⟩ := exists_smoothGoodCover_eball_refining I U hU
  obtain ⟨C', hfin, hsub⟩ := C.exists_finite
  refine ⟨C', hfin, fun a' ↦ ?_, fun a' ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hsub a'
    obtain ⟨i, hi⟩ := href a
    exact ⟨i, ha.le.trans hi⟩
  · obtain ⟨a, ha⟩ := hsub a'
    rw [ha]
    exact hball a

/-- **Existence of finite smooth good covers refining a given open cover.** On a compact
finite-dimensional Hausdorff boundaryless smooth manifold, every open cover admits a finite smooth
good refinement. -/
theorem exists_finite_smoothGoodCover_refining
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] [I.Boundaryless] {ι : Type*}
    (U : ι → TopologicalSpace.Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), Finite C.Index ∧ ∀ a, ∃ i, C.openSet a ≤ U i := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  obtain ⟨C, hC⟩ := exists_smoothGoodCover_refining I U hU
  obtain ⟨C', hfin, hsub⟩ := C.exists_finite
  refine ⟨C', hfin, fun a' ↦ ?_⟩
  obtain ⟨a, ha⟩ := hsub a'
  obtain ⟨i, hi⟩ := hC a
  exact ⟨i, ha.le.trans hi⟩

end Existence

end TauCeti

end
