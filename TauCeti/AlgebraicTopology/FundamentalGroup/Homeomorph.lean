/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# The fundamental group is a homeomorphism invariant

Mathlib records the homomorphism `FundamentalGroup.map` induced by a continuous map and the
variant `FundamentalGroup.mapOfEq` that adjusts the target basepoint along an equality, but it
stops short of packaging a homeomorphism as an *isomorphism* of fundamental groups. This file
supplies that: a homeomorphism `e : X ≃ₜ Y` induces a group isomorphism
`π₁(X, x) ≃* π₁(Y, e x)`, and more generally `π₁(X, x) ≃* π₁(Y, y)` whenever `e x = y`.

The forward map is the basepoint-adjusted induced map `FundamentalGroup.mapOfEq` of `e` and the
inverse is that of `e.symm`. `TauCeti.AlgebraicTopology.FundamentalGroup.Basic` records the
composition and identity transport laws for `mapOfEq`, which also serve as the general transport
facts for basepoint-adjusted induced maps.

For nested subspaces, the induced isomorphisms commute with inclusions. The two subspace
naturality squares are public so that other fundamental-group diagrams can reuse this transport.

Transporting a fundamental-group computation across a homeomorphism is the group-level tool behind
computing fundamental groups of spaces identified with already-known ones: for example the
fundamental group of the unit circle `Circle ⊆ ℂ` is read off from the additive-circle computation
through Mathlib's `AddCircle.homeomorphCircle`, and the same transport feeds the computation of
`π₁(ℝPⁿ)`. The construction mirrors `TauCeti.FundamentalGroup.prodMulEquiv`, the analogous
product-group isomorphism used in the torus computation.

## Main declarations

* `FundamentalGroup.homeomorphMulEquivOfEq`: `π₁(X, x) ≃* π₁(Y, y)` from `e : X ≃ₜ Y`
  with `e x = y`.
* `FundamentalGroup.homeomorphMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)`.
* `TauCeti.FundamentalGroup.subspace_inclusion_square`: naturality for nested inclusions.
* `TauCeti.FundamentalGroup.subspace_subtypeVal_square`: naturality for subtype inclusion.
-/

public section

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, y)`. The forward map is `FundamentalGroup.mapOfEq` of `e`; the inverse is
`FundamentalGroup.mapOfEq` of `e.symm`. -/
noncomputable def homeomorphMulEquivOfEq (e : X ≃ₜ Y) (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y where
  toFun := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv p :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ h
      (e.symm_apply_eq.mpr h.symm) (ContinuousMap.ext fun t => e.symm_apply_apply t) p
  right_inv q :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e, e.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (e.symm_apply_eq.mpr h.symm) h (ContinuousMap.ext fun t => e.apply_symm_apply t) q
  map_mul' := (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h).map_mul

@[simp]
theorem homeomorphMulEquivOfEq_apply (e : X ≃ₜ Y) (h : e x = y) (p : FundamentalGroup X x) :
    homeomorphMulEquivOfEq e h p = FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h p :=
  (rfl)

@[simp]
theorem homeomorphMulEquivOfEq_symm_apply (e : X ≃ₜ Y) (h : e x = y)
    (q : FundamentalGroup Y y) : (homeomorphMulEquivOfEq e h).symm q =
      FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) q :=
  (rfl)

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, e x)`. -/
noncomputable def homeomorphMulEquiv (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  homeomorphMulEquivOfEq e rfl

@[simp]
theorem homeomorphMulEquiv_apply (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup X x) :
    homeomorphMulEquiv e x p =
      FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ rfl p :=
  (rfl)

@[simp]
theorem homeomorphMulEquiv_symm_apply (e : X ≃ₜ Y) (x : X) (q : FundamentalGroup Y (e x)) :
    (homeomorphMulEquiv e x).symm q =
      FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) q :=
  (rfl)

end FundamentalGroup

namespace TauCeti

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X]

section Subspace

open CategoryTheory Set

/-- Inclusions between nested subspaces commute on fundamental groups after the canonical
homeomorphisms that forget the containing subspace. -/
theorem subspace_inclusion_square {C S T : Set X}
    (hSC : S ⊆ C) (hTC : T ⊆ C) (hST : S ⊆ T) (x : X) (hxS : x ∈ S) :
    let S' : Set C := Subtype.val ⁻¹' S
    let T' : Set C := Subtype.val ⁻¹' T
    let eS : S' ≃ₜ S := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun s hs => ⟨⟨s, hSC hs⟩, rfl⟩)
    let eT : T' ≃ₜ T := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun t ht => ⟨⟨t, hTC ht⟩, rfl⟩)
    let x' : C := ⟨x, hSC hxS⟩
    GrpCat.ofHom (FundamentalGroup.map
        (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')) ⟨x', hxS⟩) ≫
        (FundamentalGroup.homeomorphMulEquivOfEq eT rfl).toGrpIso.hom =
      (FundamentalGroup.homeomorphMulEquivOfEq eS rfl).toGrpIso.hom ≫
        GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion hST) ⟨x, hxS⟩) := by
  intro S' T' eS eT x'
  apply GrpCat.ext
  intro p
  -- Pin the group carriers before unfolding the categorical wrappers: composition simp
  -- cannot infer them through the homeomorphism-induced isomorphisms at nested subtypes.
  change FundamentalGroup.homeomorphMulEquivOfEq eT rfl
      (FundamentalGroup.map (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T'))
        (⟨x', hxS⟩ : S') p) =
    FundamentalGroup.map (ContinuousMap.inclusion hST) ⟨x, hxS⟩
      (FundamentalGroup.homeomorphMulEquivOfEq eS rfl p)
  rw [FundamentalGroup.homeomorphMulEquivOfEq_apply,
    FundamentalGroup.homeomorphMulEquivOfEq_apply,
    ← FundamentalGroup.mapOfEq_rfl (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')),
    ← FundamentalGroup.mapOfEq_rfl (ContinuousMap.inclusion hST)]
  exact (FundamentalGroup.mapOfEq_comp ⟨eT, eT.continuous⟩
    (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')) rfl rfl p).trans
    ((FundamentalGroup.mapOfEq_congr
      (f₂ := (ContinuousMap.inclusion hST).comp ⟨eS, eS.continuous⟩)
      (by ext z; rfl) _ _ p).trans
      (FundamentalGroup.mapOfEq_comp (ContinuousMap.inclusion hST)
        ⟨eS, eS.continuous⟩ rfl rfl p).symm)

/-- Inclusion of a nested subspace into its ambient subspace factors through the canonical
homeomorphism that forgets one subtype layer. -/
theorem subspace_subtypeVal_square {C S : Set X}
    (hSC : S ⊆ C) (x : X) (hxS : x ∈ S) :
    let S' : Set C := Subtype.val ⁻¹' S
    let eS : S' ≃ₜ S := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun s hs => ⟨⟨s, hSC hs⟩, rfl⟩)
    let x' : C := ⟨x, hSC hxS⟩
    GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal S') ⟨x', hxS⟩) =
      (FundamentalGroup.homeomorphMulEquivOfEq eS rfl).toGrpIso.hom ≫
        GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion hSC) ⟨x, hxS⟩) := by
  intro S' eS x'
  apply GrpCat.ext
  intro p
  -- As in the overlap square, expose the induced maps after fixing their group carriers.
  change FundamentalGroup.map (ContinuousMap.subtypeVal S') ⟨x', hxS⟩ p =
    FundamentalGroup.map (ContinuousMap.inclusion hSC) ⟨x, hxS⟩
      (FundamentalGroup.homeomorphMulEquivOfEq eS rfl p)
  rw [FundamentalGroup.homeomorphMulEquivOfEq_apply,
    ← FundamentalGroup.mapOfEq_rfl (ContinuousMap.inclusion hSC),
    ← FundamentalGroup.mapOfEq_rfl (ContinuousMap.subtypeVal S')]
  -- The canonical homeomorphism forgets the outer subtype, so composing it with
  -- inclusion is definitionally the subtype-value map.
  exact (FundamentalGroup.mapOfEq_comp (ContinuousMap.inclusion hSC)
    ⟨eS, eS.continuous⟩ rfl rfl p).symm

end Subspace

end FundamentalGroup

end TauCeti
