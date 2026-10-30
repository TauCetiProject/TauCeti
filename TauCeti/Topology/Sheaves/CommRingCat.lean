/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Gluing sections of sheaves of rings on disjoint opens

Sections of a sheaf of commutative rings on two disjoint open sets glue to a section on their
union. The proof uses Mathlib's `TopCat.Sheaf.objSupIsoProdEqLocus`: the compatibility condition
on the intersection is automatic, since the sections over the empty open form the zero ring.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe w

namespace TopCat.Sheaf

variable {X : TopCat.{w}}

/-- Sections of a sheaf of rings on two disjoint opens glue to a section on their union. -/
theorem exists_section_sup_of_disjoint (F : X.Sheaf CommRingCat.{w}) {A B : Opens X}
    (hAB : Disjoint A B) (σ : F.obj.obj (op A)) (ρ : F.obj.obj (op B)) :
    ∃ τ : F.obj.obj (op (A ⊔ B)),
      F.obj.map (homOfLE le_sup_left).op τ = σ ∧ F.obj.map (homOfLE le_sup_right).op τ = ρ :=
  ⟨_, objSupIsoProdEqLocus_inv_fst F A B ⟨(σ, ρ),
      (CommRingCat.subsingleton_of_isTerminal (F.isTerminalOfEqEmpty hAB.eq_bot)).elim _ _⟩,
    objSupIsoProdEqLocus_inv_snd F A B _⟩

end TopCat.Sheaf
