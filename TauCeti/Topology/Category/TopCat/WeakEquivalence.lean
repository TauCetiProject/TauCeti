/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Weak homotopy equivalences in `TopCat`

The weak homotopy equivalences, the continuous maps inducing a bijection on path components and on
every homotopy group at every base point (`ContinuousMap.IsWeakHomotopyEquivalence`), form a class
of morphisms `TauCeti.TopCat.weakEquivalences` of `TopCat`. They are the weak equivalences of the
Quillen model structure on topological spaces, whose fibrations are the Serre fibrations
`TauCeti.TopCat.serreFibrations`, and, through geometric realization, of the Kan–Quillen model
structure on simplicial sets.

This file records the closure properties of this class required of the weak equivalences of a model
category: it contains the isomorphisms, satisfies two out of three, and is stable under retracts.

## Main declarations

* `TauCeti.TopCat.weakEquivalences`: the weak homotopy equivalences, as a class of morphisms.
* The instances `HasTwoOutOfThreeProperty`, `IsMultiplicative` and `IsStableUnderRetracts` for
  `TauCeti.TopCat.weakEquivalences`; the isomorphisms belong to the class through
  `MorphismProperty.isomorphisms_le_of_containsIdentities`.

## References

* D. Quillen, *Homotopical algebra*, Lecture Notes in Mathematics 43, Springer, 1967, Chapter II,
  Section 3.
* M. Hovey, *Model categories*, Mathematical Surveys and Monographs 63, AMS, 1999, Section 2.4.
-/

public section

open CategoryTheory MorphismProperty

universe u

namespace TauCeti.TopCat

/-- The **weak homotopy equivalences**: the morphisms of `TopCat` whose underlying continuous map
induces a bijection on path components and on every homotopy group at every base point. -/
def weakEquivalences : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ f.hom.IsWeakHomotopyEquivalence

@[simp]
theorem mem_weakEquivalences_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    weakEquivalences f ↔ f.hom.IsWeakHomotopyEquivalence :=
  Iff.rfl

instance : weakEquivalences.{u}.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := (mem_weakEquivalences_iff _).2 <| by
    rw [_root_.TopCat.hom_comp]
    exact ((mem_weakEquivalences_iff g).1 hg).comp hf
  of_postcomp f g hg hfg := by
    rw [mem_weakEquivalences_iff, _root_.TopCat.hom_comp] at hfg
    exact hg.of_postcomp hfg
  of_precomp f g hf hfg := by
    rw [mem_weakEquivalences_iff, _root_.TopCat.hom_comp] at hfg
    exact hf.of_precomp hfg

instance : weakEquivalences.{u}.IsMultiplicative where
  comp_mem := weakEquivalences.comp_mem
  id_mem X := (mem_weakEquivalences_iff _).2 <| by
    rw [_root_.TopCat.hom_id]
    exact ContinuousMap.IsWeakHomotopyEquivalence.id

instance : weakEquivalences.{u}.IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg :=
    ((mem_weakEquivalences_iff g).1 hg).of_retract h.i.left.hom h.r.left.hom h.i.right.hom
      h.r.right.hom (by rw [← _root_.TopCat.hom_comp, h.retract_left]; simp)
      (by rw [← _root_.TopCat.hom_comp, h.retract_right]; simp)
      (by rw [← _root_.TopCat.hom_comp, ← _root_.TopCat.hom_comp, h.i_w])
      (by rw [← _root_.TopCat.hom_comp, ← _root_.TopCat.hom_comp, h.r_w])

example : weakEquivalences.{u}.RespectsIso := inferInstance

end TauCeti.TopCat
