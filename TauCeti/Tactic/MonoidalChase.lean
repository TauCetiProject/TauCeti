/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CategoryTheory.Coherence
public import Aesop

/-!
# Monoidal Chase Tactic

This file defines the `monoidal_chase` tactic, which automates the process of
rewriting associativity and unit coherences in monoidal categories. It is
primarily used to prove equalities of morphisms such as isomorphisms of
pullback and pushforward sheaves.

This advances the Tau Ceti Jacobian roadmap.
-/

public section

open Lean Meta Elab Tactic CategoryTheory

namespace TauCeti.Tactic

/--
`monoidal_chase` automates the process of rewriting associativity and unit coherences
in monoidal categories to prove equalities of morphisms (e.g., isomorphisms of 
pullback/pushforward sheaves).



It performs the following steps:
1. Identifies and validates that the goal is an equality of morphisms in a monoidal category.
2. Automatically applies monoidal coherence theorems (`pure_coherence`, `coherence`).
3. Uses specific `simp` naturality lemmas and the category theory simplifier (`aesop_cat`)
   to discharge the remaining goal.
-/
macro (name := monoidalChase) "monoidal_chase" : tactic => `(tactic|
  focus
    try pure_coherence
    try coherence
    try simp only [
      CategoryTheory.Category.assoc,
      CategoryTheory.Category.id_comp,
      CategoryTheory.Category.comp_id,
      CategoryTheory.MonoidalCategory.tensor_id,
      CategoryTheory.MonoidalCategory.tensor_comp,
      CategoryTheory.MonoidalCategory.associator_naturality,
      CategoryTheory.MonoidalCategory.leftUnitor_naturality,
      CategoryTheory.MonoidalCategory.rightUnitor_naturality,
      CategoryTheory.MonoidalCategory.pentagon,
      CategoryTheory.MonoidalCategory.triangle,
      CategoryTheory.Iso.hom_inv_id,
      CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Iso.hom_inv_id_assoc,
      CategoryTheory.Iso.inv_hom_id_assoc
    ]
    try aesop_cat
)

end TauCeti.Tactic
