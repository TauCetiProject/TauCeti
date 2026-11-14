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

Let `X : ι → Type u` be a generating family of topological spaces. When each test space `X i` is
locally compact and each product `X i × X j` is `X`-generated, Mathlib's
`Topology.ContinuousMapGeneratedBy.curryEquiv` identifies `X`-continuous maps `Y × Z → T` with
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`.

This file supplies two complements needed to compare the resulting convenient category with
ordinary products and compact-open mapping spaces:

* **Products with locally compact factors**
  (`Topology.IsGeneratedBy.prod_of_locallyCompactSpace_right`,
  `Topology.IsGeneratedBy.prod_of_locallyCompactSpace_left`): if `Y` and `Z` are `X`-generated and
  one of them is locally compact, then the ordinary product topology on `Y × Z` is already
  `X`-generated, with no universe restriction between `X`, `Y`, and `Z`. In particular, taking the
  product with a locally compact `X`-generated space such as `[0, 1]` needs no `X`-generated
  refinement.
* **Comparison with the compact-open topology** (`ContinuousMap.toContinuousMapGeneratedBy`,
  `Topology.ContinuousMapGeneratedBy.equivContinuousMap`,
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapOfCompactLift`): every continuous map
  `Y → Z` is `X`-continuous and the inclusion `C(Y, Z) → ContinuousMapGeneratedBy X Y Z` is
  continuous for the compact-open topology on `C(Y, Z)`. When `Y` is `X`-generated, this map is a
  bijection; when, in addition, every compact subset of `Y` is the continuous image of a compact
  subset of some test space `X i`, it is a homeomorphism. This applies immediately to every test
  space `X i` (`Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapIndex`) and, for compact
  Hausdorff generators, to every Hausdorff compactly generated space.

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948),
  1125–1132.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.14–A.16.
-/

public section

universe v v' v'' t u

open Topology

namespace Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- On an `X`-generated domain, `X`-continuity is ordinary continuity. -/
@[simp]
theorem continuousGeneratedBy_iff_continuous [IsGeneratedBy X Y] (g : Y → Z) :
    ContinuousGeneratedBy X g ↔ Continuous g :=
  (IsGeneratedBy.continuous_iff X g).symm

namespace IsGeneratedBy

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
  have hG : Continuous G := by
    rw [continuous_iff X]
    intro i f
    have := hXZ i
    have hp : Continuous fun q : X i × Z ↦ e.symm (f q.1, q.2) :=
      (equiv_symm_comp_continuous_iff (X := X) (fun q : X i × Z ↦ (f q.1, q.2))).2
        (f.continuous.prodMap continuous_id)
    exact (ContinuousMap.curry ⟨_, hp⟩).continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩

section LocallyCompactGenerators

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- Under locally compact generators closed under binary products, the product of any
`X`-generated space with a generator `X i` on the right is `X`-generated. -/
theorem prod_index (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] (i : ι) :
    IsGeneratedBy X (Y × X i) :=
  prod_of_locallyCompactSpace_right_of_forall fun _ ↦ inferInstance

/-- Under locally compact generators closed under binary products, the product of a generator
`X i` on the left with any `X`-generated space is `X`-generated. -/
theorem index_prod (i : ι) (Z : Type v') [TopologicalSpace Z] [IsGeneratedBy X Z] :
    IsGeneratedBy X (X i × Z) :=
  have : IsGeneratedBy X (Z × X i) := prod_index Z i
  of_homeomorph (Homeomorph.prodComm Z (X i))

/-- If `Y` and `Z` are `X`-generated and `Z` is locally compact, then the ordinary product `Y × Z`
is `X`-generated. -/
theorem prod_of_locallyCompactSpace_right (Y : Type v) (Z : Type v')
    [TopologicalSpace Y] [TopologicalSpace Z] [IsGeneratedBy X Y] [IsGeneratedBy X Z]
    [LocallyCompactSpace Z] : IsGeneratedBy X (Y × Z) :=
  prod_of_locallyCompactSpace_right_of_forall fun i ↦ index_prod i Z

/-- If `Y` and `Z` are `X`-generated and `Y` is locally compact, then the ordinary product `Y × Z`
is `X`-generated. -/
theorem prod_of_locallyCompactSpace_left (Y : Type v) (Z : Type v')
    [TopologicalSpace Y] [TopologicalSpace Z] [IsGeneratedBy X Y] [IsGeneratedBy X Z]
    [LocallyCompactSpace Y] : IsGeneratedBy X (Y × Z) :=
  have : IsGeneratedBy X (Z × Y) := prod_of_locallyCompactSpace_right Z Y
  of_homeomorph (Homeomorph.prodComm Z Y)

end LocallyCompactGenerators

end IsGeneratedBy

end Topology

namespace ContinuousMap

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

/-- Every continuous map is `X`-continuous, giving a continuous inclusion from the compact-open
mapping space `C(Y, Z)` into `ContinuousMapGeneratedBy X Y Z`. -/
def toContinuousMapGeneratedBy : C(C(Y, Z), ContinuousMapGeneratedBy X Y Z) where
  toFun g := ⟨g, g.continuous.continuousGeneratedBy⟩
  continuous_toFun := by
    rw [ContinuousMapGeneratedBy.continuous_iff]
    intro i f
    exact ContinuousMap.continuous_precomp f

@[simp]
theorem toContinuousMapGeneratedBy_apply_apply (g : C(Y, Z)) (y : Y) :
    toContinuousMapGeneratedBy X g y = g y :=
  (rfl)

@[simp]
theorem coe_toContinuousMapGeneratedBy_apply (g : C(Y, Z)) :
    ⇑(toContinuousMapGeneratedBy X g) = g :=
  (rfl)

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

section GeneratedDomain

variable [IsGeneratedBy X Y]

/-- On an `X`-generated domain `Y`, an `X`-continuous map `Y → Z` is an ordinary continuous map. -/
def toContinuousMap (g : ContinuousMapGeneratedBy X Y Z) : C(Y, Z) :=
  ⟨g, (continuousGeneratedBy_iff_continuous g).1 g.prop⟩

@[simp]
theorem toContinuousMap_apply (g : ContinuousMapGeneratedBy X Y Z) (y : Y) :
    g.toContinuousMap y = g y :=
  (rfl)

@[simp]
theorem coe_toContinuousMap (g : ContinuousMapGeneratedBy X Y Z) :
    ⇑g.toContinuousMap = g :=
  (rfl)

@[simp]
theorem toContinuousMap_toContinuousMapGeneratedBy (g : C(Y, Z)) :
    (g.toContinuousMapGeneratedBy X).toContinuousMap = g :=
  (rfl)

@[simp]
theorem toContinuousMapGeneratedBy_toContinuousMap (g : ContinuousMapGeneratedBy X Y Z) :
    g.toContinuousMap.toContinuousMapGeneratedBy X = g :=
  (rfl)

/-- On an `X`-generated domain `Y`, `X`-continuous maps `Y → Z` correspond bijectively to
ordinary continuous maps `C(Y, Z)`. -/
def equivContinuousMap : ContinuousMapGeneratedBy X Y Z ≃ C(Y, Z) where
  toFun := toContinuousMap
  invFun := ContinuousMap.toContinuousMapGeneratedBy X
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivContinuousMap_apply (g : ContinuousMapGeneratedBy X Y Z) :
    equivContinuousMap g = g.toContinuousMap :=
  (rfl)

@[simp]
theorem equivContinuousMap_symm_apply (g : C(Y, Z)) :
    equivContinuousMap.symm g = g.toContinuousMapGeneratedBy X :=
  (rfl)

/-- If every compact subset of an `X`-generated space `Y` is the image of a compact subset of some
test space `X i` under a continuous map `X i → Y`, then `toContinuousMap` is continuous into the
compact-open topology on `C(Y, Z)`. -/
theorem continuous_toContinuousMap_of_compact_lift
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K) :
    Continuous (toContinuousMap (X := X) (Y := Y) (Z := Z)) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro K hKc U hUo
  obtain ⟨i, L, f, hLc, rfl⟩ := hK hKc
  have hset : {g : ContinuousMapGeneratedBy X Y Z | Set.MapsTo g.toContinuousMap (f '' L) U} =
      precomp f ⁻¹' {h : C(X i, Z) | Set.MapsTo h L U} := by
    ext g
    exact Set.mapsTo_image_iff
  rw [hset]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hLc hUo).preimage (continuous_precomp f)

/-- If `Y` is `X`-generated and every compact subset of `Y` lifts to a compact subset of some test
space `X i`, then `ContinuousMapGeneratedBy X Y Z` is homeomorphic to the compact-open mapping
space `C(Y, Z)`. -/
def homeomorphContinuousMapOfCompactLift
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K) :
    ContinuousMapGeneratedBy X Y Z ≃ₜ C(Y, Z) where
  toEquiv := equivContinuousMap
  continuous_toFun := continuous_toContinuousMap_of_compact_lift hK
  continuous_invFun := (ContinuousMap.toContinuousMapGeneratedBy X).continuous

@[simp]
theorem homeomorphContinuousMapOfCompactLift_apply
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (g : ContinuousMapGeneratedBy X Y Z) :
    homeomorphContinuousMapOfCompactLift hK g = g.toContinuousMap :=
  (rfl)

@[simp]
theorem homeomorphContinuousMapOfCompactLift_symm_apply
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (g : C(Y, Z)) :
    (homeomorphContinuousMapOfCompactLift hK).symm g = g.toContinuousMapGeneratedBy X :=
  (rfl)

end GeneratedDomain

/-- For any member `X i` of the generating family, `ContinuousMapGeneratedBy X (X i) Z` is
homeomorphic to the compact-open mapping space `C(X i, Z)`. -/
def homeomorphContinuousMapIndex (i : ι) :
    ContinuousMapGeneratedBy X (X i) Z ≃ₜ C(X i, Z) :=
  homeomorphContinuousMapOfCompactLift fun K hKc ↦
    ⟨i, K, ContinuousMap.id (X i), hKc, Set.image_id K⟩

@[simp]
theorem homeomorphContinuousMapIndex_apply (i : ι) (g : ContinuousMapGeneratedBy X (X i) Z) :
    homeomorphContinuousMapIndex i g = g.toContinuousMap :=
  (rfl)

@[simp]
theorem homeomorphContinuousMapIndex_symm_apply (i : ι) (g : C(X i, Z)) :
    (homeomorphContinuousMapIndex i).symm g = g.toContinuousMapGeneratedBy X :=
  (rfl)

end Topology.ContinuousMapGeneratedBy
