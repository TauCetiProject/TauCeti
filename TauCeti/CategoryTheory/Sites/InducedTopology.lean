/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Induced topologies of subcanonical topologies

Let `G : C ⥤ D` be a fully faithful functor and `K` a Grothendieck topology on `D`. If `K` is
subcanonical, so is the induced topology `G.inducedTopology K` on `C`: the presheaf represented by
`X : C` is the restriction along `G` of the presheaf represented by `G.obj X`, which is a sheaf for
`K`, and restriction along the continuous functor `G` preserves sheaves.

## Main results

* `CategoryTheory.Functor.subcanonical_inducedTopology`: the topology induced by a subcanonical
  topology along a fully faithful functor is subcanonical.
-/

public section

universe v u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- **Induced topologies of subcanonical topologies are subcanonical.** If `G : C ⥤ D` is fully
faithful and `K` is a subcanonical topology on `D`, the topology induced by `K` on `C` is
subcanonical. -/
theorem subcanonical_inducedTopology (G : C ⥤ D) [G.Full] [G.Faithful]
    (K : GrothendieckTopology D) [K.Subcanonical] :
    (G.inducedTopology K).Subcanonical :=
  .of_isSheaf_yoneda_obj _ fun X ↦ by
    have := (isSheaf_iff_isSheaf_of_type _ _).1
      (G.op_comp_isSheaf (G.inducedTopology K) K (K.yoneda.obj (G.obj X)))
    exact Presieve.isSheaf_iso _
      (NatIso.ofComponents (fun Y ↦ (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.toIso.symm)
        fun f ↦ by ext; simp) this

end CategoryTheory.Functor
