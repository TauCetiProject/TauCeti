/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Symmetrified quivers as Serre graphs

`SerreGraph.ofQuiver` retains all arrows of a quiver and adds their formal reverses.
Its darts are the total arrows of Mathlib's `Quiver.Symmetrify`, including two distinct
directions for every loop. The prefunctor `SerreGraph.ofQuiverPrefunctor` transports paths
from that symmetrification to the associated Serre quiver, preserving reversal.
This allows constructions such as Schreier quivers to use the Serre path calculus.
-/

public section

namespace TauCeti.SerreGraph

variable (V : Type*) [Quiver V]

/-- Regard a quiver with formal reverse arrows as a Serre graph. -/
@[expose, instance_reducible] def ofQuiver : SerreGraph where
  V := Quiver.Symmetrify V
  E := Quiver.Total (Quiver.Symmetrify V)
  src := Quiver.Total.left
  rev := fun e => ⟨e.right, e.left, Quiver.reverse e.hom⟩
  rev_rev := by rintro ⟨a, b, e⟩; simp
  rev_ne := by
    rintro ⟨a, b, e⟩ h
    have hsign := congrArg (fun f : Quiver.Total (Quiver.Symmetrify V) => f.hom.isLeft) h
    cases e <;> simp [Quiver.symmetrify_reverse] at hsign

@[simp] theorem ofQuiver_src (e : Quiver.Total (Quiver.Symmetrify V)) :
    (ofQuiver V).src e = e.left := (rfl)

@[simp] theorem ofQuiver_tgt (e : Quiver.Total (Quiver.Symmetrify V)) :
    (ofQuiver V).tgt e = e.right := by rw [tgt_def]; rfl

@[simp] theorem ofQuiver_rev (e : Quiver.Total (Quiver.Symmetrify V)) :
    (ofQuiver V).rev e = ⟨e.right, e.left, Quiver.reverse e.hom⟩ := (rfl)

/-- The identity on vertices, retaining each symmetrified arrow as a Serre dart. -/
def ofQuiverPrefunctor : Quiver.Symmetrify V ⥤q (ofQuiver V).V where
  obj := id
  map := fun {a b} e => ⟨⟨a, b, e⟩, rfl, ofQuiver_tgt V _⟩

@[simp] theorem ofQuiverPrefunctor_obj (a : Quiver.Symmetrify V) :
    (ofQuiverPrefunctor V).obj a = a := (rfl)

@[simp] theorem ofQuiverPrefunctor_map_val {a b : Quiver.Symmetrify V}
    (e : Quiver.Hom a b) :
    ((ofQuiverPrefunctor V).map e).1 = ⟨a, b, e⟩ := (rfl)

instance : (ofQuiverPrefunctor V).MapReverse where
  map_reverse' e := by
    apply Subtype.ext
    simp only [ofQuiverPrefunctor_map_val, reverse_val, ofQuiver_rev]

end TauCeti.SerreGraph
