/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The affine fpqc site

The topology on opposite commutative `R`-algebras is induced by the big fpqc topology over
`Spec R` along relative spectrum. In particular it uses all commutative `R`-algebras,
including nonreduced ones. Full faithfulness of relative spectrum makes this topology
subcanonical, so affine schemes define sheaves on it.
The construction follows `TauCeti.CommAlgCat.fppfTopology` for the fpqc topology.

## References

* The Stacks Project, Tag 022A, the fpqc topology.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.CommAlgCat

universe u

/-- The fpqc topology on affine schemes over `Spec R`, presented on opposite `R`-algebras. -/
noncomputable def fpqcTopology (R : Type u) [CommRing R] :
    GrothendieckTopology (CommAlgCat.{u} R)ᵒᵖ :=
  (algSpec (CommRingCat.of R)).inducedTopology
    (Scheme.fpqcTopology.over (Spec (CommRingCat.of R)))

/-- The affine fpqc topology is induced from the big fpqc topology over the base scheme. -/
theorem fpqcTopology_def (R : Type u) [CommRing R] :
    fpqcTopology R = (algSpec (CommRingCat.of R)).inducedTopology
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) := (rfl)

/-- Affine representable presheaves are fpqc sheaves. -/
noncomputable instance fpqcTopology_subcanonical (R : Type u) [CommRing R] :
    (fpqcTopology R).Subcanonical := by
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fpqcTopology_def]
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (algSpec (CommRingCat.of R)) _ (Scheme.fpqcTopology.over (Spec (CommRingCat.of R)))

/-- Restricting an fpqc sheaf over `Spec R` to affine schemes gives an affine fpqc sheaf. -/
instance isContinuous_algSpec_fpqc (R : Type u) [CommRing R] :
    (algSpec (CommRingCat.of R)).IsContinuous (fpqcTopology R)
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) := by
  rw [fpqcTopology_def]
  exact Functor.le_inducedTopology_iff.mp le_rfl

end TauCeti.CommAlgCat
