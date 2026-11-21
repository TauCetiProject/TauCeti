/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Convenient.HomSpace
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Products with locally compact spaces and compact-open comparisons

Given a family of topological spaces `G : ι → Type u`, Mathlib equips the type
`ContinuousMapGeneratedBy G Y Z` of `G`-continuous maps `Y → Z` with the initial topology induced
by precomposition along continuous maps `G i → Y` into compact-open mapping spaces `C(G i, Z)`.

This file supplies two complements:

* **Products with locally compact factors**
  (`Topology.IsGeneratedBy.prod_of_locallyCompactSpace_right`,
  `Topology.IsGeneratedBy.prod_of_locallyCompactSpace_left`): assuming each test space `G i` is
  locally compact and each pairwise product `G i × G j` is `G`-generated, if `Y` and `Z` are
  `G`-generated and one of them is locally compact, then the ordinary product topology on `Y × Z`
  is already `G`-generated, with no universe restriction between `G`, `Y`, and `Z`.
* **Comparison with the compact-open topology** (`ContinuousMap.toContinuousMapGeneratedBy`,
  `Topology.ContinuousMapGeneratedBy.equivContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapOfExistsIUnionIsCompactImageEq`):
  every continuous map `Y → Z` is `G`-continuous and the inclusion
  `C(Y, Z) → ContinuousMapGeneratedBy G Y Z` is continuous for the compact-open topology on
  `C(Y, Z)`. When `Y` is `G`-generated, this map is a bijection; when, in addition, every compact
  subset of `Y` is the continuous image of a compact subset of some generator `G i` (or more
  generally a finite union of such images), it is a homeomorphism. This applies immediately to
  every test space `G i` (`Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapIndex`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.14–A.15.
-/

public section

open Topology

universe v v' t u

namespace Topology.IsGeneratedBy

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- Auxiliary product-generation criterion: if `Y` and `Z` are `G`-generated, `Z` is locally
compact, and every `G i × Z` is `G`-generated, then `Y × Z` is `G`-generated. -/
theorem prod_of_locallyCompactSpace_right_of_forall [IsGeneratedBy G Y] [IsGeneratedBy G Z]
    [LocallyCompactSpace Z] (hGZ : ∀ i, IsGeneratedBy G (G i × Z)) :
    IsGeneratedBy G (Y × Z) :=
  letI := hGZ; prod_right

/-- If a generator `G i` is locally compact and `G j × G i` is `G`-generated for every `j`, then
the product of any `G`-generated space with `G i` on the right is `G`-generated. -/
theorem prod_index (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy G Y] (i : ι)
    [LocallyCompactSpace (G i)] [∀ j, IsGeneratedBy G (G j × G i)] :
    IsGeneratedBy G (Y × G i) :=
  prod_of_locallyCompactSpace_right_of_forall fun _ ↦ inferInstance

/-- If a generator `G i` is locally compact and `G j × G i` is `G`-generated for every `j`, then
the product of `G i` on the left with any `G`-generated space is `G`-generated. -/
theorem index_prod (i : ι) (Z : Type v') [TopologicalSpace Z] [IsGeneratedBy G Z]
    [LocallyCompactSpace (G i)] [∀ j, IsGeneratedBy G (G j × G i)] :
    IsGeneratedBy G (G i × Z) :=
  have : IsGeneratedBy G (Z × G i) := prod_index Z i
  (Homeomorph.prodComm Z (G i)).isGeneratedBy

section LocallyCompactGenerators

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]
  (Y : Type v) (Z : Type v') [TopologicalSpace Y] [TopologicalSpace Z]
  [IsGeneratedBy G Y] [IsGeneratedBy G Z]

/-- Assuming all generators `G i` are locally compact with `G`-generated pairwise products
`G i × G j`, if `Y` and `Z` are `G`-generated and `Z` is locally compact, then the ordinary product
`Y × Z` is `G`-generated. -/
theorem prod_of_locallyCompactSpace_right [LocallyCompactSpace Z] : IsGeneratedBy G (Y × Z) :=
  prod_of_locallyCompactSpace_right_of_forall fun i ↦ index_prod i Z

/-- Assuming all generators `G i` are locally compact with `G`-generated pairwise products
`G i × G j`, if `Y` and `Z` are `G`-generated and `Y` is locally compact, then the ordinary product
`Y × Z` is `G`-generated. -/
theorem prod_of_locallyCompactSpace_left [LocallyCompactSpace Y] : IsGeneratedBy G (Y × Z) :=
  have : IsGeneratedBy G (Z × Y) := prod_of_locallyCompactSpace_right Z Y
  (Homeomorph.prodComm Z Y).isGeneratedBy

end LocallyCompactGenerators

end Topology.IsGeneratedBy

section HomSpace

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace ContinuousMap

/-- Every continuous map `Y → Z` is `G`-continuous. -/
@[expose]
def toContinuousMapGeneratedBy (G : ι → Type u) [∀ i, TopologicalSpace (G i)] (f : C(Y, Z)) :
    ContinuousMapGeneratedBy G Y Z :=
  ⟨f, f.continuous.continuousGeneratedBy⟩

@[simp]
theorem toContinuousMapGeneratedBy_apply (f : C(Y, Z)) (y : Y) :
    f.toContinuousMapGeneratedBy G y = f y := rfl

/-- The canonical inclusion from the compact-open mapping space `C(Y, Z)` to
`ContinuousMapGeneratedBy G Y Z` is continuous. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMapGeneratedBy :
    Continuous (toContinuousMapGeneratedBy G : C(Y, Z) → ContinuousMapGeneratedBy G Y Z) :=
  ContinuousMapGeneratedBy.continuous_iff.2 fun _ p ↦ p.continuous_precomp

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

@[simp]
theorem coe_mk (f : Y → Z) (hf : ContinuousGeneratedBy G f) :
    ⇑(ContinuousMapGeneratedBy.mk f hf) = f := (rfl)

/-- When the source `Y` is `G`-generated, every `G`-continuous map `Y → Z` is continuous. -/
@[expose]
def toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) : C(Y, Z) :=
  ⟨f, (IsGeneratedBy.continuous_iff G f).2 f.prop⟩

@[simp]
theorem toContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) (y : Y) :
    f.toContinuousMap y = f y := rfl

@[simp]
theorem coe_toContinuousMap [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    (f.toContinuousMap : Y → Z) = f := rfl

@[simp]
theorem toContinuousMap_toContinuousMapGeneratedBy [IsGeneratedBy G Y] (g : C(Y, Z)) :
    (g.toContinuousMapGeneratedBy G).toContinuousMap = g := by
  ext y; rfl

@[simp]
theorem toContinuousMapGeneratedBy_toContinuousMap [IsGeneratedBy G Y]
    (g : ContinuousMapGeneratedBy G Y Z) :
    g.toContinuousMap.toContinuousMapGeneratedBy G = g :=
  DFunLike.ext _ _ fun _ ↦ rfl

/-- When `Y` is `G`-generated, `G`-continuous maps `Y → Z` coincide with continuous maps `Y → Z`. -/
@[expose]
def equivContinuousMap [IsGeneratedBy G Y] : ContinuousMapGeneratedBy G Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy G
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy G Y] (f : ContinuousMapGeneratedBy G Y Z) :
    equivContinuousMap f = f.toContinuousMap := (rfl)

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy G Y] (f : C(Y, Z)) :
    (equivContinuousMap (G := G)).symm f = f.toContinuousMapGeneratedBy G := (rfl)

section CompactCover

variable [IsGeneratedBy G Y]
  (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
    ∃ (m : ℕ) (i : Fin m → ι) (L : ∀ j, Set (G (i j))) (p : ∀ j, C(G (i j), Y)),
      (∀ j, IsCompact (L j)) ∧ ⋃ j, p j '' L j = K)

include hK

/-- If every compact subset of a `G`-generated space `Y` is a finite union of images of compact
subsets of test spaces `G i` under continuous maps `G i → Y`, then `toContinuousMap` is continuous
into the compact-open topology on `C(Y, Z)`. -/
theorem continuous_toContinuousMap_of_exists_iUnion_isCompact_image_eq :
    Continuous (toContinuousMap : ContinuousMapGeneratedBy G Y Z → C(Y, Z)) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro K hKc U hUo
  obtain ⟨m, i, L, p, hLc, rfl⟩ := hK hKc
  have hset : {f : ContinuousMapGeneratedBy G Y Z |
      Set.MapsTo f.toContinuousMap (⋃ j, p j '' L j) U} =
      ⋂ j, precomp (p j) ⁻¹' {h : C(G (i j), Z) | Set.MapsTo h (L j) U} := by
    ext f; simp [Set.mapsTo_iUnion, Set.mapsTo_image_iff, Function.comp_def]
  rw [hset]
  exact isOpen_iInter_of_finite fun j ↦
    (ContinuousMap.isOpen_setOfPred_mapsTo (hLc j) hUo).preimage (continuous_precomp (p j))

/-- If `Y` is `G`-generated and every compact subset of `Y` is a finite union of images of compact
subsets of test spaces `G i` under continuous maps, then `ContinuousMapGeneratedBy G Y Z` is
homeomorphic to the compact-open mapping space `C(Y, Z)`. -/
@[expose]
def homeomorphContinuousMapOfExistsIUnionIsCompactImageEq :
    ContinuousMapGeneratedBy G Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap_of_exists_iUnion_isCompact_image_eq hK
  continuous_invFun := ContinuousMap.continuous_toContinuousMapGeneratedBy

@[simp]
theorem homeomorphContinuousMapOfExistsIUnionIsCompactImageEq_apply
    (f : ContinuousMapGeneratedBy G Y Z) :
    homeomorphContinuousMapOfExistsIUnionIsCompactImageEq hK f = f.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMapOfExistsIUnionIsCompactImageEq_symm_apply (f : C(Y, Z)) :
    (homeomorphContinuousMapOfExistsIUnionIsCompactImageEq (Z := Z) hK).symm f =
      f.toContinuousMapGeneratedBy G := (rfl)

end CompactCover

/-- If every compact subset of `Y` is the image of a compact subset of some generator `G i` along a
continuous map `G i → Y`, then `toContinuousMap` is continuous into the compact-open topology on
`C(Y, Z)`. -/
theorem continuous_toContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    Continuous (toContinuousMap : ContinuousMapGeneratedBy G Y Z → C(Y, Z)) :=
  continuous_toContinuousMap_of_exists_iUnion_isCompact_image_eq fun _ hK ↦
    let ⟨i, L, p, hL, hp⟩ := hG hK
    ⟨1, fun _ ↦ i, fun _ ↦ L, fun _ ↦ p, fun _ ↦ hL, by simpa [Set.iUnion_const] using hp⟩

/-- When `Y` is `G`-generated and every compact subset of `Y` is the continuous image of a compact
subset of some generator `G i`, the `G`-probed mapping space `ContinuousMapGeneratedBy G Y Z` is
homeomorphic to `C(Y, Z)` with the compact-open topology. -/
@[expose]
def homeomorphContinuousMap [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) :
    ContinuousMapGeneratedBy G Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap hG
  continuous_invFun := ContinuousMap.continuous_toContinuousMapGeneratedBy

@[simp]
theorem homeomorphContinuousMap_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K)
    (f : ContinuousMapGeneratedBy G Y Z) :
    homeomorphContinuousMap hG f = f.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMap_symm_apply [IsGeneratedBy G Y]
    (hG : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (G i)) (p : C(G i, Y)), IsCompact L ∧ p '' L = K) (f : C(Y, Z)) :
    (homeomorphContinuousMap (Z := Z) hG).symm f = f.toContinuousMapGeneratedBy G := (rfl)

/-- For any member `G i` of the generating family, `ContinuousMapGeneratedBy G (G i) Z` is
homeomorphic to the compact-open mapping space `C(G i, Z)`. -/
@[expose]
def homeomorphContinuousMapIndex (i : ι) :
    ContinuousMapGeneratedBy G (G i) Z ≃ₜ C(G i, Z) :=
  homeomorphContinuousMap fun K hKc ↦ ⟨i, K, ContinuousMap.id (G i), hKc, Set.image_id K⟩

@[simp]
theorem homeomorphContinuousMapIndex_apply (i : ι)
    (g : ContinuousMapGeneratedBy G (G i) Z) :
    homeomorphContinuousMapIndex i g = g.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMapIndex_symm_apply (i : ι) (g : C(G i, Z)) :
    (homeomorphContinuousMapIndex i).symm g = g.toContinuousMapGeneratedBy G := (rfl)

end Topology.ContinuousMapGeneratedBy

end HomSpace
