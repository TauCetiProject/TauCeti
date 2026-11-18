/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Hom.Conj
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
public import TauCeti.Topology.Homotopy.Homotopic.Rel

import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
import TauCeti.AlgebraicTopology.PathComponent
import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
import TauCeti.Topology.CWComplex.Classical.Extension
import TauCeti.Topology.CWComplex.Classical.Image
import TauCeti.Topology.CWComplex.Comparison
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel
import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Classification of maps from a CW complex into an aspherical space

Let `X` be a path-connected Hausdorff CW complex with base point `x₀`, and let `(Y, y₀)` be a
based space whose homotopy groups `πₙ(Y, y₀)` vanish for `n ≥ 2` (in particular any `K(G, 1)`
space). This file completes the proof of Hatcher's Proposition 1B.9 in full generality, with `X`
and `Y` in independent universes:

* **Existence (`TauCeti.exists_mapOfEq`, `TauCeti.exists_mapOfEq_of_cwComplex`):** every group
  homomorphism `π₁(X, x₀) →* π₁(Y, y₀)` is induced by a continuous map `(X, x₀) → (Y, y₀)`,
  without requiring `Y` to be path connected or to have CW type.
* **Pointed classification (`TauCeti.pointedHomotopyEquivMonoidHom`,
  `TauCeti.pointedHomotopyEquivMonoidHomOfCWComplex`):** pointed homotopy classes of maps
  `(X, x₀) → (Y, y₀)` are in canonical bijection with `π₁(X, x₀) →* π₁(Y, y₀)`.
* **Unbased classification (`TauCeti.homotopicQuotientEquivMonoidHomConjQuotient`,
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex`):** when `Y` is path
  connected, free homotopy classes `[X, Y]` are in canonical bijection with conjugacy classes of
  homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)` (`TauCeti.monoidHomConjSetoid`), with explicit computation
  along any basepoint-connecting path
  (`TauCeti.homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path`,
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path`).

To construct pointed maps out of an arbitrary CW complex `C` into a space in another universe,
we first produce a universal pointed map `u : C → cellularClassifyingSpace R` in the universe of
`C` inducing an isomorphism on `π₁` (`TauCeti.exists_bijective_mapOfEq_cellularClassifyingSpace`):
the inclusion of the `2`-skeleton `E` into `killHomotopyGroups 2 E a₀` extends over the cells of
`C` of dimension at least `3` because the higher homotopy groups of `killHomotopyGroups 2 E a₀`
vanish, and composing with a pointed homotopy inverse of `cellularClassifyingSpaceHomotopyEquiv`
lands in a cellular classifying space `cellularClassifyingSpace R`. Every homomorphism out of the
fundamental group of `cellularClassifyingSpace R` into `(Z, z)` in an arbitrary universe is then
realized by corestricting to `pathComponent z` and extending across the relative CW cells above
the presentation complex (`TauCeti.exists_mapOfEq_cellularClassifyingSpace_of_subsingleton`).

## Main definitions

* `TauCeti.pointedHomotopyEquivMonoidHom` and
  `TauCeti.pointedHomotopyEquivMonoidHomOfCWComplex`: the bijection between pointed homotopy
  classes `[(X, x₀), (Y, y₀)]_*` and `π₁(X, x₀) →* π₁(Y, y₀)`.
* `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex`: the bijection between free
  homotopy classes `[X, Y]` and `Quotient (monoidHomConjSetoid (π₁(X, x₀)) (π₁(Y, y₀)))`.

## Main results

* `TauCeti.exists_mapOfEq_cellularClassifyingSpace_of_subsingleton`: universe-polymorphic
  realization of homomorphisms out of `π₁(cellularClassifyingSpace R)` into `(Z, z)`.
* `TauCeti.exists_bijective_mapOfEq_cellularClassifyingSpace`: every path-connected Hausdorff CW
  complex admits a pointed map to a cellular classifying space inducing an isomorphism on `π₁`.
* `TauCeti.exists_mapOfEq` and `TauCeti.exists_mapOfEq_of_cwComplex`: Hatcher's Proposition 1B.9
  (existence of pointed maps inducing any prescribed homomorphism on `π₁`).
* `TauCeti.homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path` and
  `TauCeti.homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path`: computation of the
  unbased classification bijection on an arbitrary map via a path from `f x₀` to `y₀`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Proposition 1B.9.
-/

public section

noncomputable section

open Metric Module Set Topology Topology.RelCWComplex
open scoped Topology.Homotopy ContinuousMap

universe u v

namespace TauCeti

/-! ### Universe-polymorphic extension over cellular classifying spaces -/

/-- Extend a map `f₀ : PresentationComplex R → S` into a path-connected space `S` (in any universe)
whose homotopy groups `π_{n+2}(S, s₀)` vanish across the cells of `cellularClassifyingSpace R`. -/
private lemma exists_extension_cellularClassifyingSpace_of_subsingleton {S : Type u}
    (R : Set (FreeGroup S)) {W : Type v} [TopologicalSpace W] [PathConnectedSpace W] (w₀ : W)
    (hW : ∀ n : ℕ, Subsingleton (π_ (n + 2) W w₀)) (f₀ : C(PresentationComplex R, W)) :
    ∃ F : C(cellularClassifyingSpace R, W), ∀ p : PresentationComplex R,
      F (killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
        (PresentationComplex.basepoint R) p) = f₀ p := by
  let incl := killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
    (PresentationComplex.basepoint R)
  let c := killHomotopyGroupsRelativeCWComplex 2 (TopCat.of (PresentationComplex R))
    (PresentationComplex.basepoint R)
  let _ := c.toRelCWComplex
  let hEmb := c.isClosedEmbedding.isEmbedding.toHomeomorph
  obtain ⟨F, hF⟩ :=
    exists_extension_of_nullhomotopic (C := (univ : Set (cellularClassifyingSpace R)))
    (fun m ⟨i⟩ g ↦ by
      have hm : 3 ≤ m := by
        by_contra hlt
        exact (isEmpty_killHomotopyGroupsRelativeCWComplex_attachCells_ι 2
          (TopCat.of (PresentationComplex R)) (PresentationComplex.basepoint R) (by omega)).false
          (c.toRelCWComplexCellEquiv m i)
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      exact nullhomotopic_sphere_of_subsingleton_homotopyGroup (by simp) (hW k) g)
    (f₀.comp (hEmb.symm : C(range incl, PresentationComplex R)))
  let eUniv : cellularClassifyingSpace R ≃ₜ (univ : Set (cellularClassifyingSpace R)) :=
    (Homeomorph.Set.univ (cellularClassifyingSpace R)).symm
  refine ⟨F.comp (eUniv : C(cellularClassifyingSpace R, (univ : Set (cellularClassifyingSpace R)))),
    fun p ↦ (hF (hEmb p)).trans (congrArg f₀ (hEmb.symm_apply_apply p))⟩

/-- **Universe-polymorphic realization of `π₁`-homomorphisms out of a cellular classifying space.**
If `π_{n+2}(Z, z)` is trivial for every `n : ℕ` (with `Z` in any universe, and without assuming
`Z` is path connected), every homomorphism `π₁(cellularClassifyingSpace R, b₀) →* π₁(Z, z)` is
induced by a pointed map. -/
theorem exists_mapOfEq_cellularClassifyingSpace_of_subsingleton {S : Type u}
    (R : Set (FreeGroup S)) {Z : Type v} [TopologicalSpace Z] {z : Z}
    (hZ : ∀ n : ℕ, Subsingleton (π_ (n + 2) Z z))
    (fπ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) →*
      FundamentalGroup Z z) :
    ∃ (f : C(cellularClassifyingSpace R, Z))
      (hf : f (cellularClassifyingSpaceBasepoint R) = z),
      FundamentalGroup.mapOfEq f hf = fπ := by
  let z' : pathComponent z := pathComponentSelf z
  let eZ := FundamentalGroup.pathComponentMulEquiv z z'
  have hZ' (n : ℕ) : Subsingleton (π_ (n + 2) (pathComponent z) z') :=
    (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset Subset.rfl rfl).1.subsingleton
  let eR := cellularClassifyingSpaceFundamentalGroupMulEquiv R
  obtain ⟨f₀, hf₀, hf₀π⟩ := PresentationComplex.exists_mapOfEq_comp_fundamentalGroupHom
    ((eZ.symm.toMonoidHom.comp fπ).comp eR.symm.toMonoidHom)
  obtain ⟨F, hF⟩ := exists_extension_cellularClassifyingSpace_of_subsingleton R z' hZ' f₀
  let f : C(cellularClassifyingSpace R, Z) := (ContinuousMap.subtypeVal (pathComponent z)).comp F
  let incl := killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
    (PresentationComplex.basepoint R)
  have hf_val (p : PresentationComplex R) : f (incl p) = (f₀ p : Z) := congrArg Subtype.val (hF p)
  have hf : f (cellularClassifyingSpaceBasepoint R) = z :=
    (hf_val (PresentationComplex.basepoint R)).trans (congrArg Subtype.val hf₀)
  refine ⟨f, hf, MonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨w, rfl⟩ := eR.symm.surjective g
  rw [cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply]
  have hcomp : f.comp incl.hom = (ContinuousMap.subtypeVal (pathComponent z)).comp f₀ :=
    ContinuousMap.ext hf_val
  have hsubf₀ : ((ContinuousMap.subtypeVal (pathComponent z)).comp f₀)
      (PresentationComplex.basepoint R) = z :=
    congrArg Subtype.val hf₀
  have h₁ : FundamentalGroup.mapOfEq f hf
      (FundamentalGroup.map incl.hom (PresentationComplex.basepoint R)
        (PresentationComplex.fundamentalGroupHom R w)) =
      eZ (FundamentalGroup.mapOfEq f₀ hf₀ (PresentationComplex.fundamentalGroupHom R w)) := by
    dsimp only [eZ]
    rw [← FundamentalGroup.mapOfEq_rfl incl.hom,
      FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq hcomp rfl hf hsubf₀,
      FundamentalGroup.pathComponentMulEquiv_apply,
      ← FundamentalGroup.mapOfEq_rfl
        (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent z, Z))]
    exact (FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq
      (ContinuousMap.ext fun _ ↦ rfl) hf₀ rfl hsubf₀ _).symm
  rw [h₁]
  have h₂ := DFunLike.congr_fun hf₀π w
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h₂
  rw [h₂, MulEquiv.apply_symm_apply]
  dsimp only [eR]
  rw [cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply]

/-! ### Universal `π₁`-isomorphism to a cellular classifying space -/

section CW

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Extending the inclusion of the `2`-skeleton `E = skeletonLT C 3` into
`killHomotopyGroups 2 E a₀` over the cells of `C` of dimension at least `3` yields a map out of
`C` inducing a bijection on `π₁`. -/
private lemma exists_bijective_mapOfEq_killHomotopyGroups_skeletonLT {C : Set X} [CWComplex C]
    [PathConnectedSpace C] :
    let E : Set X := skeletonLT C ((3 : ℕ) : ℕ∞)
    let hEC : E ⊆ C := (skeletonLT C ((3 : ℕ) : ℕ∞)).subset_complex
    ∃ (a₀ : E) (_ : PathConnectedSpace E)
      (u₀ : C(C, killHomotopyGroups 2 (TopCat.of E) a₀))
      (hu₀ : u₀ (inclusion hEC a₀) = killHomotopyGroupsIncl 2 (TopCat.of E) a₀ a₀),
      Function.Bijective (FundamentalGroup.mapOfEq u₀ hu₀) := by
  intro E hEC
  have hE : (skeletonLT C ((2 + 1 : ℕ) : ℕ∞) : Set X) = E := rfl
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  obtain ⟨a₀, -⟩ := exists_joined_skeletonLT (C := C) (n := 2) hE hEC c₀
  have : PathConnectedSpace E :=
    ⟨⟨a₀⟩, fun a b ↦ (joined_skeletonLT_iff (C := C) (n := 2) zero_lt_two hE hEC).1
      (PathConnectedSpace.joined (inclusion hEC a) (inclusion hEC b))⟩
  have : PathConnectedSpace (TopCat.of E) := ‹PathConnectedSpace E›
  let inclK := killHomotopyGroupsIncl 2 (TopCat.of E) a₀
  obtain ⟨u₀, hu₀_ext⟩ := exists_extension_skeletonLT_of_nullhomotopic (C := C) 3
    (fun m hm _ g ↦ by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      exact nullhomotopic_sphere_of_subsingleton_homotopyGroup (n := k + 2) (x := inclK a₀)
        (by simp) (subsingleton_homotopyGroup_killHomotopyGroups 2 (TopCat.of E) a₀ (by omega)) g)
    inclK.hom
  have hu₀ : u₀ (inclusion hEC a₀) = inclK a₀ := hu₀_ext a₀
  refine ⟨a₀, ‹PathConnectedSpace E›, u₀, hu₀, ?_⟩
  have hcomp : u₀.comp (ContinuousMap.inclusion hEC) = inclK.hom := ContinuousMap.ext hu₀_ext
  have hbij_inclE : Function.Bijective
      (FundamentalGroup.mapOfEq (ContinuousMap.inclusion hEC) (rfl : inclusion hEC a₀ = _)) :=
    (HomotopyGroup.bijective_map_iff_bijective_mapOfEq (ContinuousMap.inclusion hEC) rfl).1
      ⟨injective_homotopyGroupMap_skeletonLT (C := C) (n := 2) (N := Fin 1) (by simp) hE hEC a₀,
        surjective_homotopyGroupMap_skeletonLT (C := C) (n := 2) (N := Fin 1) (by simp) hE hEC a₀⟩
  have hbij_inclK : Function.Bijective (FundamentalGroup.mapOfEq inclK.hom (rfl : inclK a₀ = _)) :=
    (HomotopyGroup.bijective_map_iff_bijective_mapOfEq inclK.hom rfl).1
      (bijective_homotopyGroupMap_killHomotopyGroupsIncl 2 (TopCat.of E) a₀ (N := Fin 1) (by simp))
  have hcomp_fn : ⇑(FundamentalGroup.mapOfEq u₀ hu₀) ∘
      ⇑(FundamentalGroup.mapOfEq (ContinuousMap.inclusion hEC) (rfl : inclusion hEC a₀ = _)) =
      ⇑(FundamentalGroup.mapOfEq inclK.hom (rfl : inclK a₀ = _)) :=
    funext fun g ↦
      (FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq hcomp
        (rfl : inclusion hEC a₀ = _) hu₀ (rfl : inclK a₀ = _) g)
  exact (Function.Bijective.of_comp_iff (FundamentalGroup.mapOfEq u₀ hu₀) hbij_inclE).1
    (hcomp_fn.symm ▸ hbij_inclK)

/-- Composing the map into `killHomotopyGroups 2 E a₀` with a pointed homotopy inverse of
`cellularClassifyingSpaceHomotopyEquiv` produces a map into a cellular classifying space inducing
a bijection on `π₁` at `inclusion hEC a₀`. -/
private lemma exists_bijective_mapOfEq_cellularClassifyingSpace_some {C : Set X} [CWComplex C]
    [PathConnectedSpace C] :
    ∃ (S : Type u) (R : Set (FreeGroup S)) (c₀ : C) (v : C(C, cellularClassifyingSpace R))
      (hv : v c₀ = cellularClassifyingSpaceBasepoint R),
      Function.Bijective (FundamentalGroup.mapOfEq v hv) := by
  let E : Set X := skeletonLT C ((3 : ℕ) : ℕ∞)
  let hEC : E ⊆ C := (skeletonLT C ((3 : ℕ) : ℕ∞)).subset_complex
  obtain ⟨a₀, _, u₀, hu₀, hbij_u₀⟩ :=
    exists_bijective_mapOfEq_killHomotopyGroups_skeletonLT (C := C)
  have : PathConnectedSpace (TopCat.of E) := ‹PathConnectedSpace E›
  let cE := toRelativeCWComplex E
  let _ := cE.toRelCWComplex
  have hD0 : id '' range (ContinuousMap.inclusion (base_subset_complex (C := E))) =
      (∅ : Set (TopCat.of E)) := by simp
  let eCell (m : ℕ) := Topology.IsClosedEmbedding.relCWComplexCellEquiv
    Topology.IsClosedEmbedding.id (image_id (univ : Set (TopCat.of E))) hD0 m
  let _ : RelCWComplex (univ : Set (TopCat.of E)) ∅ :=
    Topology.IsClosedEmbedding.id.relCWComplex (image_id (univ : Set (TopCat.of E))) hD0
  let _ : CWComplex (univ : Set (TopCat.of E)) := RelCWComplex.toCWComplex _
  have hEmpty (m : ℕ) (hm : 2 < m) : IsEmpty (cell (univ : Set (TopCat.of E)) m) :=
    ⟨fun i ↦ by
      have hi := (cE.toRelCWComplexCellEquiv m (eCell m i)).2
      simp only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] at hi
      omega⟩
  let K := killHomotopyGroups 2 (TopCat.of E) a₀
  let k₀ : K := killHomotopyGroupsIncl 2 (TopCat.of E) a₀ a₀
  let _ : CWComplex (univ : Set K) := killHomotopyGroupsCWComplex 2 (TopCat.of E) a₀ hEmpty
  have hK : IsAspherical K k₀ :=
    (isEilenbergMacLaneSpaceOne_killHomotopyGroups (TopCat.of E) a₀).isAspherical
  obtain ⟨R, -, -, hCR⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup K k₀)
  obtain ⟨ψ⟩ := hCR.nonempty_fundamentalGroupMulEquiv
  let e := cellularClassifyingSpaceHomotopyEquiv R hK ψ
  have he : e.toFun (cellularClassifyingSpaceBasepoint R) = k₀ :=
    cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hK ψ
  obtain ⟨r, hr, hre, her⟩ :=
    (hasHomotopyExtensionProperty_singleton_univ (cellularClassifyingSpaceBasepoint R))
      |>.exists_basedInverse_homotopicRel (hasHomotopyExtensionProperty_singleton_univ k₀) e he
  have hbij_r := (⟨r, e.toFun, her.homotopic, hre.homotopic⟩ :
    K ≃ₕ cellularClassifyingSpace R).fundamentalGroup_mapOfEq_bijective hr
  refine ⟨FundamentalGroup K k₀, R, inclusion hEC a₀, r.comp u₀, (congrArg r hu₀).trans hr, ?_⟩
  have hru : ⇑(FundamentalGroup.mapOfEq (r.comp u₀) ((congrArg r hu₀).trans hr)) =
      ⇑(FundamentalGroup.mapOfEq r hr) ∘ ⇑(FundamentalGroup.mapOfEq u₀ hu₀) :=
    funext fun g ↦ (FundamentalGroup.mapOfEq_comp r u₀ hu₀ hr g).symm
  exact hru ▸ hbij_r.comp hbij_u₀

/-- **Every path-connected Hausdorff CW complex admits a pointed map to a cellular classifying
space inducing an isomorphism on `π₁`.** -/
theorem exists_bijective_mapOfEq_cellularClassifyingSpace {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) :
    ∃ (S : Type u) (R : Set (FreeGroup S)) (u : C(C, cellularClassifyingSpace R))
      (hu : u x₀ = cellularClassifyingSpaceBasepoint R),
      Function.Bijective (FundamentalGroup.mapOfEq u hu) := by
  obtain ⟨S, R, c₀, v, hv, hbij_v⟩ :=
    exists_bijective_mapOfEq_cellularClassifyingSpace_some (C := C)
  have : PathConnectedSpace (cellularClassifyingSpace R) :=
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical.pathConnectedSpace
  let γ : Path (v x₀) (cellularClassifyingSpaceBasepoint R) :=
    PathConnectedSpace.somePath (v x₀) (cellularClassifyingSpaceBasepoint R)
  obtain ⟨H, hH₀, hH₁⟩ := (hasHomotopyExtensionProperty_singleton x₀).exists_extension_of_isClosed
    isClosed_singleton v (γ.toContinuousMap.comp ContinuousMap.fst) fun a ↦ by
      rcases a with ⟨_, rfl⟩
      exact γ.source
  let u : C(C, cellularClassifyingSpace R) := ⟨fun x ↦ H (1, x), by fun_prop⟩
  have hu : u x₀ = cellularClassifyingSpaceBasepoint R :=
    (hH₁ 1 ⟨x₀, rfl⟩).trans γ.target
  let Hhom : v.Homotopy u :=
    { toContinuousMap := H, map_zero_left := hH₀, map_one_left := fun _ ↦ rfl }
  have hbij_vc₀ : Function.Bijective (FundamentalGroup.map v c₀) := by
    have haux {z : cellularClassifyingSpace R} (hz : v c₀ = z)
        (hb : Function.Bijective (FundamentalGroup.mapOfEq v hz)) :
        Function.Bijective (FundamentalGroup.map v c₀) := by
      rcases hz with rfl
      rwa [FundamentalGroup.mapOfEq_rfl] at hb
    exact haux hv hbij_v
  have hbij_vx₀ : Function.Bijective (FundamentalGroup.map v x₀) :=
    FundamentalGroup.map_bijective_of_path v (PathConnectedSpace.somePath c₀ x₀) hbij_vc₀
  have hbij_ux₀ : Function.Bijective (FundamentalGroup.map u x₀) := by
    have heq : ⇑(FundamentalGroup.map u x₀) =
        ⇑(FundamentalGroup.fundamentalGroupMulEquivOfPath (Hhom.evalAt x₀)) ∘
          ⇑(FundamentalGroup.map v x₀) :=
      funext fun a ↦ (Hhom.fundamentalGroupMulEquivOfPath_evalAt_map x₀ a).symm
    exact heq ▸ (FundamentalGroup.fundamentalGroupMulEquivOfPath _).bijective.comp hbij_vx₀
  refine ⟨S, R, u, hu, ?_⟩
  have haux {z : cellularClassifyingSpace R} (hz : u x₀ = z) :
      Function.Bijective (FundamentalGroup.mapOfEq u hz) := by
    rcases hz with rfl
    rwa [FundamentalGroup.mapOfEq_rfl]
  exact haux hu

/-! ### Hatcher's Proposition 1B.9: existence and classification of maps -/

/-- **Pointed maps out of a path-connected Hausdorff CW complex realize every `π₁`-homomorphism
(Hatcher, Proposition 1B.9, existence).** Let `C` be a path-connected CW complex in a Hausdorff
space `X` with base point `x₀`, and let `(Y, y₀)` be a based space (in any universe, without
assuming `Y` is path connected) with `πₙ(Y, y₀) = 0` for all `n ≥ 2`. Every homomorphism
`φ : π₁(C, x₀) →* π₁(Y, y₀)` is induced by a continuous map `(C, x₀) → (Y, y₀)`. -/
theorem exists_mapOfEq {C : Set X} [CWComplex C] [PathConnectedSpace C] {x₀ : C} {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (φ : FundamentalGroup C x₀ →* FundamentalGroup Y y₀) :
    ∃ (f : C(C, Y)) (hf : f x₀ = y₀), FundamentalGroup.mapOfEq f hf = φ := by
  obtain ⟨S, R, u, hu, hbij_u⟩ := exists_bijective_mapOfEq_cellularClassifyingSpace (C := C) x₀
  let α := MulEquiv.ofBijective (FundamentalGroup.mapOfEq u hu) hbij_u
  obtain ⟨g, hg, hgφ⟩ := exists_mapOfEq_cellularClassifyingSpace_of_subsingleton R hY
    (φ.comp α.symm.toMonoidHom)
  refine ⟨g.comp u, (congrArg g hu).trans hg, MonoidHom.ext fun a ↦ ?_⟩
  rw [← FundamentalGroup.mapOfEq_comp g u hu hg a, hgφ, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  exact congrArg φ (α.symm_apply_apply a)

/-- **Pointed maps out of a path-connected Hausdorff space with a CW structure on `univ` realize
every `π₁`-homomorphism (Hatcher, Proposition 1B.9, existence).** -/
theorem exists_mapOfEq_of_cwComplex [CWComplex (univ : Set X)] [PathConnectedSpace X]
    {x₀ : X} {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (φ : FundamentalGroup X x₀ →* FundamentalGroup Y y₀) :
    ∃ (f : C(X, Y)) (hf : f x₀ = y₀), FundamentalGroup.mapOfEq f hf = φ := by
  let e := Homeomorph.Set.univ X
  let x₀' : (univ : Set X) := e.symm x₀
  have : PathConnectedSpace (univ : Set X) := e.symm.surjective.pathConnectedSpace e.symm.continuous
  let eπ : FundamentalGroup (univ : Set X) x₀' ≃* FundamentalGroup X x₀ :=
    FundamentalGroup.homeomorphMulEquivOfEq e (e.apply_symm_apply x₀)
  obtain ⟨f', hf', hf'φ⟩ := exists_mapOfEq hY (φ.comp eπ.toMonoidHom)
  let f : C(X, Y) := f'.comp (e.symm : C(X, (univ : Set X)))
  have hf : f x₀ = y₀ := hf'
  refine ⟨f, hf, MonoidHom.ext fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := eπ.surjective a
  have hcomp : f.comp (e : C((univ : Set X), X)) = f' :=
    ContinuousMap.ext fun z ↦ congrArg f' (e.symm_apply_apply z)
  have hb : eπ b = FundamentalGroup.mapOfEq (e : C((univ : Set X), X))
      (e.apply_symm_apply x₀) b :=
    FundamentalGroup.homeomorphMulEquivOfEq_apply e (e.apply_symm_apply x₀) b
  rw [hb, FundamentalGroup.mapOfEq_mapOfEq_eq_mapOfEq hcomp _ hf hf',
    hf'φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hb]

/-- **Pointed homotopy classification of maps out of a CW complex on `univ` (Hatcher, Proposition
1B.9, pointed form).** -/
def pointedHomotopyEquivMonoidHomOfCWComplex [CWComplex (univ : Set X)] [PathConnectedSpace X]
    (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (pointedHomotopySetoid x₀ y₀) ≃
      (FundamentalGroup X x₀ →* FundamentalGroup Y y₀) :=
  Equiv.ofBijective
    (Quotient.lift (fun f : {f : C(X, Y) // f x₀ = y₀} ↦ FundamentalGroup.mapOfEq f.1 f.2)
      fun f g h ↦ FundamentalGroup.mapOfEq_eq_of_homotopicRel f.2 g.2 (mem_singleton x₀)
        (pointedHomotopySetoid_iff.1 h))
    ⟨Quotient.ind₂ fun f g hfg ↦ Quotient.sound
        (pointedHomotopySetoid_iff.2 (homotopicRel_of_mapOfEq_eq_of_cwComplex hY f.2 g.2 hfg)),
      fun φ ↦ by
        obtain ⟨f, hf, hfφ⟩ := exists_mapOfEq_of_cwComplex hY φ
        exact ⟨⟦⟨f, hf⟩⟧, hfφ⟩⟩

@[simp]
theorem pointedHomotopyEquivMonoidHomOfCWComplex_mk [CWComplex (univ : Set X)]
    [PathConnectedSpace X] (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : {f : C(X, Y) // f x₀ = y₀}) :
    pointedHomotopyEquivMonoidHomOfCWComplex x₀ hY ⟦f⟧ = FundamentalGroup.mapOfEq f.1 f.2 := by
  unfold pointedHomotopyEquivMonoidHomOfCWComplex
  rfl

/-- **Pointed homotopy classification of maps into an aspherical space (Hatcher, Proposition 1B.9,
pointed form).** For a path-connected Hausdorff CW complex `C` with base point `x₀` and a based
space `(Y, y₀)` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, sending a pointed map `(C, x₀) → (Y, y₀)` to its
induced homomorphism on `π₁` is a bijection from pointed homotopy classes to
`π₁(C, x₀) →* π₁(Y, y₀)`. -/
def pointedHomotopyEquivMonoidHom {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient (pointedHomotopySetoid x₀ y₀) ≃
      (FundamentalGroup C x₀ →* FundamentalGroup Y y₀) :=
  letI := cwComplexUniv C
  pointedHomotopyEquivMonoidHomOfCWComplex x₀ hY

@[simp]
theorem pointedHomotopyEquivMonoidHom_mk {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : {f : C(C, Y) // f x₀ = y₀}) :
    pointedHomotopyEquivMonoidHom x₀ hY ⟦f⟧ = FundamentalGroup.mapOfEq f.1 f.2 := by
  let _ := cwComplexUniv C
  exact pointedHomotopyEquivMonoidHomOfCWComplex_mk x₀ hY f

end CW

/-! ### Unbased homotopy classification via conjugacy classes of homomorphisms -/

section Unbased

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [PathConnectedSpace Y]

/-- Transporting `FundamentalGroup.map f x₀` back to `y₀` along a chosen path in `Y`; its class
modulo `monoidHomConjSetoid` is independent of the path and depends only on the free homotopy
class of `f`. -/
private def unbasedInducedMonoidHom {Z : Type*} [TopologicalSpace Z] (x₀ : Z) (y₀ : Y)
    (f : C(Z, Y)) : FundamentalGroup Z x₀ →* FundamentalGroup Y y₀ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath y₀ (f x₀))).symm.toMonoidHom.comp (FundamentalGroup.map f x₀)

private lemma monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f g : C(X, Y)) :
    monoidHomConjSetoid _ _ (unbasedInducedMonoidHom x₀ y₀ f) (unbasedInducedMonoidHom x₀ y₀ g) ↔
      f.Homotopic g := by
  have hYg (n : ℕ) : Subsingleton (π_ (n + 2) Y (g x₀)) :=
    (homotopyGroupEquivOfPath (PathConnectedSpace.somePath y₀ (g x₀))).subsingleton_congr.mp (hY n)
  rw [homotopic_iff_exists_path_fundamentalGroupMulEquivOfPath_of_cwComplex x₀ hYg,
    monoidHomConjSetoid_iff]
  set αf := PathConnectedSpace.somePath y₀ (f x₀)
  set αg := PathConnectedSpace.somePath y₀ (g x₀)
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨δ, hδ⟩ := Quotient.exists_rep c.asHom
    have hc_eq : c = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) := by
      ext
      exact hδ.symm
    refine ⟨αf.symm.trans (δ.trans αg), fun a ↦ ?_⟩
    have hconj : FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (unbasedInducedMonoidHom x₀ y₀ f a) = unbasedInducedMonoidHom x₀ y₀ g a := by
      rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj, MulAut.conj_apply, ← hc_eq]
      exact hc a
    have hstep : FundamentalGroup.fundamentalGroupMulEquivOfPath (αf.symm.trans (δ.trans αg))
        (FundamentalGroup.map f x₀ a) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath αg
          (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
            ((FundamentalGroup.fundamentalGroupMulEquivOfPath αf).symm
              (FundamentalGroup.map f x₀ a))) := by
      rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_trans,
        FundamentalGroup.fundamentalGroupMulEquivOfPath_trans,
        FundamentalGroup.fundamentalGroupMulEquivOfPath_symm]
      rfl
    rw [hstep]
    exact (congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath αg) hconj).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath αg).apply_symm_apply _)
  · rintro ⟨γ, hγ⟩
    let δ : Path y₀ y₀ := (αf.trans γ).trans αg.symm
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ), fun a ↦ ?_⟩
    rw [← MulAut.conj_apply, ← FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj]
    have hstep : FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (unbasedInducedMonoidHom x₀ y₀ f a) =
        (FundamentalGroup.fundamentalGroupMulEquivOfPath αg).symm
          (FundamentalGroup.fundamentalGroupMulEquivOfPath γ
            (FundamentalGroup.fundamentalGroupMulEquivOfPath αf
              ((FundamentalGroup.fundamentalGroupMulEquivOfPath αf).symm
                (FundamentalGroup.map f x₀ a)))) := by
      rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_trans,
        FundamentalGroup.fundamentalGroupMulEquivOfPath_trans,
        FundamentalGroup.fundamentalGroupMulEquivOfPath_symm]
      rfl
    rw [hstep, MulEquiv.apply_symm_apply, hγ a]
    rfl

/-- **Unbased homotopy classification of maps out of a CW complex on `univ` (Hatcher, Proposition
1B.9).** For a path-connected Hausdorff CW complex `X` with base point `x₀` and a path-connected
space `Y` with `πₙ(Y, y₀) = 0` for `n ≥ 2`, free homotopy classes `[X, Y]` are in canonical
bijection with conjugacy classes of homomorphisms `π₁(X, x₀) →* π₁(Y, y₀)`. -/
def homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex [CWComplex (univ : Set X)]
    [PathConnectedSpace X] (x₀ : X) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := Y), ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient (monoidHomConjSetoid (FundamentalGroup X x₀) (FundamentalGroup Y y₀)) :=
  let s : Setoid C(X, Y) := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩
  Equiv.ofBijective
    (Quotient.lift (s := s)
      (fun f : C(X, Y) ↦ Quotient.mk (monoidHomConjSetoid _ _) (unbasedInducedMonoidHom x₀ y₀ f))
      fun f g h ↦ Quotient.sound
        ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).2 h))
    ⟨Quotient.ind₂ (s₁ := s) (s₂ := s) fun f g h ↦ Quotient.sound (s := s)
        ((monoidHomConjSetoid_unbasedInducedMonoidHom_iff_of_cwComplex x₀ hY f g).1
          (Quotient.exact h)),
      Quotient.ind fun ψ ↦ by
        obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_of_cwComplex hY ψ
        refine ⟨Quotient.mk s f, Quotient.sound (monoidHomConjSetoid_iff.2 ?_)⟩
        rcases hf with rfl
        let α := PathConnectedSpace.somePath (f x₀) (f x₀)
        refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α), fun a ↦ ?_⟩
        rw [← MulAut.conj_apply, ← FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj, ← hfψ,
          FundamentalGroup.mapOfEq_rfl]
        exact (FundamentalGroup.fundamentalGroupMulEquivOfPath α).apply_symm_apply _⟩

/-- On any map `f : C(X, Y)` and any path `γ : Path (f x₀) y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the free homotopy class of `f` to
the conjugacy class of `(fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)`. -/
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) (f : C(X, Y)) (γ : Path (f x₀) y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _)
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp
          (FundamentalGroup.map f x₀)) := by
  unfold homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex
  refine Quotient.sound (monoidHomConjSetoid_iff.2 ?_)
  let α := PathConnectedSpace.somePath y₀ (f x₀)
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (α.trans γ)), fun a ↦ ?_⟩
  rw [← MulAut.conj_apply, ← FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply]
  exact congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath γ)
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath α).apply_symm_apply _)

/-- On any map `f : C(X, Y)` sending `x₀` to `y₀`,
`homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex` sends the class of `f` to the conjugacy
class of `FundamentalGroup.mapOfEq f hf`. -/
@[simp]
theorem homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq
    [CWComplex (univ : Set X)] [PathConnectedSpace X] (x₀ : X) {y₀ : Y}
    (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) {f : C(X, Y)} (hf : f x₀ = y₀) :
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _) (FundamentalGroup.mapOfEq f hf) := by
  rcases hf with rfl
  simpa [FundamentalGroup.mapOfEq_rfl] using
    homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path x₀ hY f (Path.refl (f x₀))

/-- **Unbased homotopy classification of maps into a path-connected aspherical space (Hatcher,
Proposition 1B.9).** -/
def homotopicQuotientEquivMonoidHomConjQuotient {C : Set X} [CWComplex C] [PathConnectedSpace C]
    (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀)) :
    Quotient ⟨ContinuousMap.Homotopic (X := C) (Y := Y), ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient (monoidHomConjSetoid (FundamentalGroup C x₀) (FundamentalGroup Y y₀)) :=
  letI := cwComplexUniv C
  homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex x₀ hY

/-- On any map `f : C(C, Y)` and any path `γ : Path (f x₀) y₀`,
`homotopicQuotientEquivMonoidHomConjQuotient` sends the free homotopy class of `f` to the
conjugacy class of `(fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp (map f x₀)`. -/
theorem homotopicQuotientEquivMonoidHomConjQuotient_mk_of_path {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    (f : C(C, Y)) (γ : Path (f x₀) y₀) :
    homotopicQuotientEquivMonoidHomConjQuotient x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _)
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom.comp
          (FundamentalGroup.map f x₀)) := by
  let _ := cwComplexUniv C
  exact homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_path x₀ hY f γ

/-- On any map `f : C(C, Y)` sending `x₀` to `y₀`,
`homotopicQuotientEquivMonoidHomConjQuotient` sends the class of `f` to the conjugacy class of
`FundamentalGroup.mapOfEq f hf`. -/
@[simp]
theorem homotopicQuotientEquivMonoidHomConjQuotient_mk_of_eq {C : Set X} [CWComplex C]
    [PathConnectedSpace C] (x₀ : C) {y₀ : Y} (hY : ∀ n : ℕ, Subsingleton (π_ (n + 2) Y y₀))
    {f : C(C, Y)} (hf : f x₀ = y₀) :
    homotopicQuotientEquivMonoidHomConjQuotient x₀ hY
        (Quotient.mk ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ f) =
      Quotient.mk (monoidHomConjSetoid _ _) (FundamentalGroup.mapOfEq f hf) := by
  let _ := cwComplexUniv C
  exact homotopicQuotientEquivMonoidHomConjQuotientOfCWComplex_mk_of_eq x₀ hY hf

end Unbased

end TauCeti
