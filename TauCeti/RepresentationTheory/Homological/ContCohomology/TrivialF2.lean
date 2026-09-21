/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The trivial F₂ coefficient representation

The Evens norm is an operation on continuous cohomology with trivial `𝔽₂` coefficients.  Its
canonical cohomology groups use an object of `TopRep ℤ G`, while its explicit cocycle formulas are
valued in `ZMod 2`.  This file supplies the canonical coefficient object and its restriction API.

For a group `G : Type u`, Mathlib's continuous-cohomology resolution requires the coefficient
module to live in `Type u`.  The carrier of `trivialF2 G` is therefore `ULift.{u} (ZMod 2)`, not
`ZMod 2`.  The action is trivial.  Restriction to a subgroup has the same carrier and action, but
the two `TopRep` objects arise from different constructions; `trivialF2Res` gives their canonical
identification and `trivialF2ResMap` includes that identification in cohomological restriction.

## Main definitions

* `TauCeti.trivialF2`: trivial `𝔽₂` coefficients over an arbitrary
  universe.
* `TauCeti.trivialF2Res`: the canonical identification after restriction to
  a subgroup.
* `TauCeti.trivialF2ResMap`: restriction on continuous cohomology with these
  coefficients.

## Main result

* `TauCeti.trivialF2_isSmoothDiscrete`: the coefficient object is smooth
  discrete, as required by corestriction.

This is the coefficient-object prerequisite in the explicit index-two form of Layer 13 of the
human-authored `ProfiniteCohomology` roadmap.  It is the bridge needed to turn the roadmap's
`ZMod 2`-valued graph cocycle into a class of canonical continuous cohomology.
-/

public section

open CategoryTheory

namespace TauCeti

open _root_.ContinuousCohomology ContinuousCohomology

universe u

variable (G : Type u) [Group G]

/-- Trivial `𝔽₂` coefficients as an object of `TopRep ℤ G` in the universe of `G`.

The lift is forced by the universe of Mathlib's continuous-cohomology resolution.  Explicit
cochain formulas may remain `ZMod 2`-valued and cross this lift only when entering the canonical
complex. -/
@[expose] noncomputable def trivialF2 : TopRep ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} (ZMod 2)))

/-- The carrier of `trivialF2 G` is the universe lift of `ZMod 2`. -/
@[simp]
theorem trivialF2_V : (trivialF2 G).V = ULift.{u} (ZMod 2) :=
  rfl

/-- The lifted carrier of `trivialF2 G` has the discrete topology. -/
instance : DiscreteTopology (trivialF2 G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod 2)))

/-- Every group element acts trivially on `trivialF2 G`. -/
@[simp]
theorem trivialF2_ρ_apply_apply (g : G) (x : ULift.{u} (ZMod 2)) :
    (trivialF2 G).ρ g x = x :=
  rfl

/-- Restriction preserves the trivial `𝔽₂` coefficient object.

Although the source and target have definitionally the same carrier and both actions are trivial,
they are distinct `TopRep` expressions.  This isomorphism is the identity on their common carrier.
-/
@[expose] noncomputable def trivialF2Res (S : Subgroup G) :
    (TopRep.resFunctor S.subtype).obj (trivialF2 G) ≅ trivialF2 S where
  hom := TopRep.ofHom <| (ContRepresentation.Equiv.mk
    (ContinuousLinearEquiv.refl ℤ (ULift.{u} (ZMod 2))) (by
      intro s
      ext x
      rfl)).toContIntertwiningMap
  inv := TopRep.ofHom <| (ContRepresentation.Equiv.mk
    (ContinuousLinearEquiv.refl ℤ (ULift.{u} (ZMod 2))) (by
      intro s
      ext x
      rfl)).toContIntertwiningMap
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The forward restriction identification fixes every coefficient. -/
@[simp]
theorem trivialF2Res_hom_apply (S : Subgroup G) (x : ULift.{u} (ZMod 2)) :
    (trivialF2Res G S).hom.hom x = x :=
  rfl

/-- The inverse restriction identification fixes every coefficient. -/
@[simp]
theorem trivialF2Res_inv_apply (S : Subgroup G) (x : ULift.{u} (ZMod 2)) :
    (trivialF2Res G S).inv.hom x = x :=
  rfl

section TopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction on continuous cohomology with trivial `𝔽₂` coefficients.

The generic restriction map lands in the restriction of the ambient coefficient object.  The
second factor applies `trivialF2Res` so that the codomain is expressed using the coefficient object
constructed directly over the subgroup. -/
@[expose] noncomputable def trivialF2ResMap (S : Subgroup G) (n : ℕ) :
    (continuousCohomologyFunctor ℤ G n).obj (trivialF2 G) ⟶
      (continuousCohomologyFunctor ℤ S n).obj (trivialF2 S) :=
  res S (trivialF2 G) n ≫
    (continuousCohomologyFunctor ℤ S n).map (trivialF2Res G S).hom

/-- The defining factorization of restriction with trivial `𝔽₂` coefficients. -/
theorem trivialF2ResMap_def (S : Subgroup G) (n : ℕ) :
    trivialF2ResMap G S n =
      res S (trivialF2 G) n ≫
        (continuousCohomologyFunctor ℤ S n).map (trivialF2Res G S).hom :=
  rfl

omit [IsTopologicalGroup G] in
/-- The trivial `𝔽₂` coefficient object is smooth discrete.

Its carrier is discrete, and every point stabilizer is the whole group because the action is
trivial. -/
theorem trivialF2_isSmoothDiscrete : IsSmoothDiscrete ℤ (trivialF2 G) := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  have hstabilizer : {g : G | (trivialF2 G).ρ g x = x} = Set.univ := by
    ext g
    change ((ContRepresentation.trivial ℤ G (ULift.{u} (ZMod 2))) g x = x) ↔ _
    constructor
    · exact fun _ ↦ Set.mem_univ g
    · intro _
      exact ContRepresentation.trivial_apply (R := ℤ) (G := G)
        (V := ULift.{u} (ZMod 2)) g x
  rw [hstabilizer]
  exact isOpen_univ

end TopologicalGroup

end TauCeti
