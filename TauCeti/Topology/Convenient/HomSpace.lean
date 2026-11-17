/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Convenient.HomSpace
public import TauCeti.Topology.Convenient.ContinuousMapGeneratedBy
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Products with locally compact spaces and compact-open comparisons

Let `X : ι → Type u` be a generating family of topological spaces. When each test space `X i` is
locally compact and each product `X i × X j` is `X`-generated, Mathlib's
`Topology.ContinuousMapGeneratedBy.curryEquiv` identifies `X`-continuous maps `Y × Z → T` with
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`.

This file supplies two complements needed to compare the resulting convenient category with
ordinary products and compact-open mapping spaces:

* **Products with locally compact factors**
  (`Topology.IsGeneratedBy.prod_of_locallyCompactSpace_right`,
  `Topology.IsGeneratedBy.prod_of_locallyCompactSpace_left`): assuming each test space `X i` is
  locally compact and each pairwise product `X i × X j` is `X`-generated, if `Y` and `Z` are
  `X`-generated and one of them is locally compact, then the ordinary product topology on `Y × Z`
  is already `X`-generated, with no universe restriction between `X`, `Y`, and `Z`. In particular,
  taking the product with a locally compact `X`-generated space such as `[0, 1]` needs no
  `X`-generated refinement.
* **Comparison with the compact-open topology** (`ContinuousMap.toContinuousMapGeneratedBy`,
  `Topology.ContinuousMapGeneratedBy.equivContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapOfExistsIUnionIsCompactImageEq`): every
  continuous map `Y → Z` is `X`-continuous and the inclusion
  `C(Y, Z) → ContinuousMapGeneratedBy X Y Z` is continuous for the compact-open topology on
  `C(Y, Z)`. When `Y` is `X`-generated, this map is a bijection; when, in addition, every compact
  subset of `Y` is a finite union of images of compact subsets of test spaces `X i` under
  continuous maps, it is a homeomorphism. This applies immediately to every test space `X i`
  (`Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapIndex`) and, for compact Hausdorff
  generators in `Type u`, to every `u`-small Hausdorff `u`-compactly generated space.

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948),
  1125–1132.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.14–A.15.
-/

public section

universe v v' v'' t u

open Topology

namespace Topology.IsGeneratedBy

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- Auxiliary product-generation criterion: if `Y` and `Z` are `X`-generated, `Z` is locally
compact, and every `X i × Z` is `X`-generated, then `Y × Z` is `X`-generated. -/
theorem prod_of_locallyCompactSpace_right_of_forall [IsGeneratedBy X Y] [IsGeneratedBy X Z]
    [LocallyCompactSpace Z] (hXZ : ∀ i, IsGeneratedBy X (X i × Z)) :
    IsGeneratedBy X (Y × Z) := by
  constructor
  let e := WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)
  have hslice (y : Y) : Continuous fun z : Z ↦ e.symm (y, z) :=
    (equiv_symm_comp_continuous_iff (X := X) (fun z : Z ↦ (y, z))).2 (Continuous.prodMk_right y)
  let G : Y → C(Z, WithGeneratedByTopology X (Y × Z)) := fun y ↦ ⟨fun z ↦ e.symm (y, z), hslice y⟩
  have hG : Continuous G := (continuous_iff X G).2 fun i f ↦ by
    have := hXZ i
    exact (ContinuousMap.curry ⟨_, (equiv_symm_comp_continuous_iff (X := X)
      (fun q : X i × Z ↦ (f q.1, q.2))).2 (f.continuous.prodMap continuous_id)⟩).continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩

/-- If a generator `X i` is locally compact and `X j × X i` is `X`-generated for every `j`, then
the product of any `X`-generated space with `X i` on the right is `X`-generated. -/
theorem prod_index (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] (i : ι)
    [LocallyCompactSpace (X i)] [∀ j, IsGeneratedBy X (X j × X i)] :
    IsGeneratedBy X (Y × X i) :=
  prod_of_locallyCompactSpace_right_of_forall fun _ ↦ inferInstance

/-- If a generator `X i` is locally compact and `X j × X i` is `X`-generated for every `j`, then
the product of `X i` on the left with any `X`-generated space is `X`-generated. -/
theorem index_prod (i : ι) (Z : Type v') [TopologicalSpace Z] [IsGeneratedBy X Z]
    [LocallyCompactSpace (X i)] [∀ j, IsGeneratedBy X (X j × X i)] :
    IsGeneratedBy X (X i × Z) :=
  have : IsGeneratedBy X (Z × X i) := prod_index Z i
  (Homeomorph.prodComm Z (X i)).isGeneratedBy

section LocallyCompactGenerators

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
  (Y : Type v) (Z : Type v') [TopologicalSpace Y] [TopologicalSpace Z]
  [IsGeneratedBy X Y] [IsGeneratedBy X Z]

/-- Assuming all generators `X i` are locally compact with `X`-generated pairwise products
`X i × X j`, if `Y` and `Z` are `X`-generated and `Z` is locally compact, then the ordinary product
`Y × Z` is `X`-generated. -/
theorem prod_of_locallyCompactSpace_right [LocallyCompactSpace Z] : IsGeneratedBy X (Y × Z) :=
  prod_of_locallyCompactSpace_right_of_forall fun i ↦ index_prod i Z

/-- Assuming all generators `X i` are locally compact with `X`-generated pairwise products
`X i × X j`, if `Y` and `Z` are `X`-generated and `Y` is locally compact, then the ordinary product
`Y × Z` is `X`-generated. -/
theorem prod_of_locallyCompactSpace_left [LocallyCompactSpace Y] : IsGeneratedBy X (Y × Z) :=
  have : IsGeneratedBy X (Z × Y) := prod_of_locallyCompactSpace_right Z Y
  (Homeomorph.prodComm Z Y).isGeneratedBy

end LocallyCompactGenerators

end Topology.IsGeneratedBy

namespace ContinuousMap

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- Every continuous map is `X`-continuous, giving a continuous inclusion from the compact-open
mapping space `C(Y, Z)` into `ContinuousMapGeneratedBy X Y Z`. -/
def toContinuousMapGeneratedBy : C(C(Y, Z), ContinuousMapGeneratedBy X Y Z) where
  toFun g := ⟨g, g.continuous.continuousGeneratedBy⟩
  continuous_toFun :=
    ContinuousMapGeneratedBy.continuous_iff.2 fun _ f ↦ ContinuousMap.continuous_precomp f

@[simp] theorem toContinuousMapGeneratedBy_apply_apply (g : C(Y, Z)) (y : Y) :
    toContinuousMapGeneratedBy X g y = g y := (rfl)

@[simp] theorem coe_toContinuousMapGeneratedBy_apply (g : C(Y, Z)) :
    ⇑(toContinuousMapGeneratedBy X g) = g := (rfl)

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

section GeneratedDomain

variable [IsGeneratedBy X Y]

@[simp] theorem toContinuousMap_toContinuousMapGeneratedBy (g : C(Y, Z)) :
    (g.toContinuousMapGeneratedBy X).toContinuousMap = g := by ext y; simp

@[simp] theorem toContinuousMapGeneratedBy_toContinuousMap (g : ContinuousMapGeneratedBy X Y Z) :
    g.toContinuousMap.toContinuousMapGeneratedBy X = g :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- On an `X`-generated domain `Y`, `X`-continuous maps `Y → Z` correspond bijectively to
ordinary continuous maps `C(Y, Z)`. -/
def equivContinuousMap : ContinuousMapGeneratedBy X Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy X
  left_inv := toContinuousMapGeneratedBy_toContinuousMap
  right_inv := toContinuousMap_toContinuousMapGeneratedBy

@[simp] theorem equivContinuousMap_apply (g : ContinuousMapGeneratedBy X Y Z) :
    equivContinuousMap g = g.toContinuousMap := (rfl)

@[simp] theorem equivContinuousMap_symm_apply (g : C(Y, Z)) :
    equivContinuousMap.symm g = g.toContinuousMapGeneratedBy X := (rfl)

section CompactCover

variable (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
  ∃ (m : ℕ) (i : Fin m → ι) (L : ∀ j, Set (X (i j))) (f : ∀ j, C(X (i j), Y)),
    (∀ j, IsCompact (L j)) ∧ ⋃ j, f j '' L j = K)

include hK

/-- If every compact subset of an `X`-generated space `Y` is a finite union of images of compact
subsets of test spaces `X i` under continuous maps `X i → Y`, then `toContinuousMap` is continuous
into the compact-open topology on `C(Y, Z)`. -/
theorem continuous_toContinuousMap_of_exists_iUnion_isCompact_image_eq :
    Continuous (toContinuousMap (X := X) (Y := Y) (Z := Z)) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro K hKc U hUo
  obtain ⟨m, i, L, f, hLc, rfl⟩ := hK hKc
  have hset : {g : ContinuousMapGeneratedBy X Y Z |
      Set.MapsTo g.toContinuousMap (⋃ j, f j '' L j) U} =
      ⋂ j, precomp (f j) ⁻¹' {h : C(X (i j), Z) | Set.MapsTo h (L j) U} := by
    ext g; simp [Set.mapsTo_iUnion, Set.mapsTo_image_iff, Function.comp_def]
  rw [hset]
  exact isOpen_iInter_of_finite fun j ↦
    (ContinuousMap.isOpen_setOfPred_mapsTo (hLc j) hUo).preimage (continuous_precomp (f j))

/-- If `Y` is `X`-generated and every compact subset of `Y` is a finite union of images of compact
subsets of test spaces `X i` under continuous maps, then `ContinuousMapGeneratedBy X Y Z` is
homeomorphic to the compact-open mapping space `C(Y, Z)`. -/
def homeomorphContinuousMapOfExistsIUnionIsCompactImageEq :
    ContinuousMapGeneratedBy X Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap_of_exists_iUnion_isCompact_image_eq hK
  continuous_invFun := (ContinuousMap.toContinuousMapGeneratedBy X).continuous

@[simp] theorem homeomorphContinuousMapOfExistsIUnionIsCompactImageEq_apply
    (g : ContinuousMapGeneratedBy X Y Z) :
    homeomorphContinuousMapOfExistsIUnionIsCompactImageEq hK g = g.toContinuousMap := (rfl)

@[simp] theorem homeomorphContinuousMapOfExistsIUnionIsCompactImageEq_symm_apply (g : C(Y, Z)) :
    (homeomorphContinuousMapOfExistsIUnionIsCompactImageEq hK).symm g =
      g.toContinuousMapGeneratedBy X := (rfl)

end CompactCover

end GeneratedDomain

/-- For any member `X i` of the generating family, `ContinuousMapGeneratedBy X (X i) Z` is
homeomorphic to the compact-open mapping space `C(X i, Z)`. -/
def homeomorphContinuousMapIndex (i : ι) :
    ContinuousMapGeneratedBy X (X i) Z ≃ₜ C(X i, Z) :=
  homeomorphContinuousMapOfExistsIUnionIsCompactImageEq fun K hKc ↦
    ⟨1, fun _ ↦ i, fun _ ↦ K, fun _ ↦ ContinuousMap.id (X i), fun _ ↦ hKc,
      by simp [Set.iUnion_const]⟩

@[simp] theorem homeomorphContinuousMapIndex_apply (i : ι)
    (g : ContinuousMapGeneratedBy X (X i) Z) :
    homeomorphContinuousMapIndex i g = g.toContinuousMap := (rfl)

@[simp] theorem homeomorphContinuousMapIndex_symm_apply (i : ι) (g : C(X i, Z)) :
    (homeomorphContinuousMapIndex i).symm g = g.toContinuousMapGeneratedBy X := (rfl)

end Topology.ContinuousMapGeneratedBy
