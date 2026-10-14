/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice

import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Epimorphisms of differences of restrictions for presheaves of abelian groups

Let `P` be a presheaf of abelian groups on a meet-semilattice `X` with a greatest element, and let
`U` and `V` be elements of `X`. The difference of restrictions `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` (the
second map of the Mayer-Vietoris sequence) is an epimorphism of abelian groups exactly when every
element of `P(U ⊓ V)` is the difference of the restrictions of an element of `P(U)` and an
element of `P(V)`. The categorical product `U ⨯ V` is the meet `U ⊓ V`
(`CategoryTheory.Limits.CompleteLattice.prod_eq_inf`), and epimorphisms in `AddCommGrpCat` are
the surjections (`AddCommGrpCat.epi_iff_surjective`).

## Main results

* `CategoryTheory.Functor.epi_biprod_desc_map_prod_fst_neg_map_prod_snd_iff_surjective`: the
  difference of restrictions `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` is an epimorphism if and only if the
  difference of restrictions `P(U) × P(V) → P(U ⊓ V)` is surjective.
-/

public section

open CategoryTheory Limits Opposite

universe w u

namespace CategoryTheory.Functor

variable {X : Type u} [SemilatticeInf X] [OrderTop X]

/-- **Surjectivity of a difference of restrictions.** For a presheaf `P` of abelian groups on a
meet-semilattice with a greatest element, the map `P(U) ⊞ P(V) ⟶ P(U ⨯ V)` sending `(s, t)` to the
difference of the restrictions of `s` and `t` is an epimorphism exactly when the difference of
restrictions `P(U) × P(V) → P(U ⊓ V)` is surjective. -/
theorem epi_biprod_desc_map_prod_fst_neg_map_prod_snd_iff_surjective
    (P : Xᵒᵖ ⥤ AddCommGrpCat.{w}) (U V : X) :
    Epi (biprod.desc (P.map (prod.fst : U ⨯ V ⟶ U).op) (-P.map (prod.snd : U ⨯ V ⟶ V).op)) ↔
      Function.Surjective fun x : P.obj (op U) × P.obj (op V) ↦
        P.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op x.1 -
          P.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op x.2 := by
  -- the product `U ⨯ V` is the meet `U ⊓ V`, so restriction between them is invertible
  let e := iso_of_both_ways (homOfLE (CompleteLattice.prod_eq_inf U V).ge)
    (homOfLE (CompleteLattice.prod_eq_inf U V).le)
  have he : biprod.desc (P.map (prod.fst : U ⨯ V ⟶ U).op)
      (-P.map (prod.snd : U ⨯ V ⟶ V).op) ≫ P.map e.hom.op =
        biprod.desc (P.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
          (-P.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op) := by
    -- morphisms of `X` are unique, so `e` followed by a projection is the inequality of the meet
    have h₀ : e.hom ≫ prod.fst = homOfLE inf_le_left := Subsingleton.elim _ _
    have h₁ : e.hom ≫ prod.snd = homOfLE inf_le_right := Subsingleton.elim _ _
    apply biprod.hom_ext' <;> simp [← P.map_comp, ← op_comp, h₀, h₁]
  rw [← epi_comp_iff_of_isIso _ (P.map e.hom.op), he,
    ← epi_comp_iff_of_epi (AddCommGrpCat.biprodIsoProd _ _).inv, AddCommGrpCat.epi_iff_surjective]
  refine Iff.of_eq (congrArg _ (funext fun x ↦ ?_))
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc_apply, sub_eq_add_neg]

end CategoryTheory.Functor
