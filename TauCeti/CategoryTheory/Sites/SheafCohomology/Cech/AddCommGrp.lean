/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.MayerVietoris

import Mathlib.Algebra.Category.Grp.EpiMono
import TauCeti.Algebra.Category.Grp.IsSheafFor

/-!
# Čech complexes of two-member covers for presheaves of abelian groups

Let `X` be a meet-semilattice with a greatest element `⊤`, for instance the opens of a topological
space contained in a fixed open, and let `P` be a presheaf of abelian groups on `X`. For two
elements `U 0` and `U 1`, `quasiIso_cechAugmentation_fin_two_iff` says that the augmented Čech
complex `0 ⟶ P(⊤) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact exactly when the Mayer-Vietoris sequence
`0 ⟶ P(⊤) ⟶ P(U 0) ⊞ P(U 1) ⟶ P(U 0 ⨯ U 1) ⟶ 0` is short exact. This file restates that criterion
elementwise, in the form in which it is checked in practice: the underlying presheaf of sets
satisfies the sheaf condition for the family `U i ≤ ⊤`, and every element of `P(U 0 ⊓ U 1)` is a
difference of restrictions of elements of `P(U 0)` and `P(U 1)`. The categorical product
`U 0 ⨯ U 1` is the meet `U 0 ⊓ U 1` (`CategoryTheory.Limits.CompleteLattice.prod_eq_inf`).

## Main results

* `TauCeti.CategoryTheory.quasiIso_cechAugmentation_fin_two_iff_surjective`: the augmented Čech
  complex of a presheaf of abelian groups on a meet-semilattice with top, for a two-member family,
  is exact if and only if the underlying presheaf of sets satisfies the sheaf condition for the
  family and the difference of restrictions `P(U 0) × P(U 1) → P(U 0 ⊓ U 1)` is surjective.
-/

public section

open CategoryTheory Limits Opposite

universe w u

namespace TauCeti.CategoryTheory

variable {X : Type u} [SemilatticeInf X] [OrderTop X] (P : Xᵒᵖ ⥤ AddCommGrpCat.{w})
  (U : Fin 2 → X)

/-- In `AddCommGrpCat`, the map `P(U 0) ⊞ P(U 1) ⟶ P(U 0 ⨯ U 1)` of the Mayer-Vietoris sequence
is an epimorphism exactly when the difference of restrictions to `U 0 ⊓ U 1` is surjective. -/
private lemma epi_biprod_desc_iff_surjective :
    Epi (biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
        (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op)) ↔
      Function.Surjective fun x : P.obj (op (U 0)) × P.obj (op (U 1)) ↦
        P.map (homOfLE inf_le_left : U 0 ⊓ U 1 ⟶ U 0).op x.1 -
          P.map (homOfLE inf_le_right : U 0 ⊓ U 1 ⟶ U 1).op x.2 := by
  -- the product `U 0 ⨯ U 1` is the meet `U 0 ⊓ U 1`, so restriction between them is invertible
  let e := iso_of_both_ways (homOfLE (CompleteLattice.prod_eq_inf (U 0) (U 1)).ge)
    (homOfLE (CompleteLattice.prod_eq_inf (U 0) (U 1)).le)
  have he : biprod.desc (P.map (prod.fst : U 0 ⨯ U 1 ⟶ U 0).op)
      (-P.map (prod.snd : U 0 ⨯ U 1 ⟶ U 1).op) ≫ P.map e.hom.op =
        biprod.desc (P.map (homOfLE inf_le_left : U 0 ⊓ U 1 ⟶ U 0).op)
          (-P.map (homOfLE inf_le_right : U 0 ⊓ U 1 ⟶ U 1).op) := by
    -- morphisms of `X` are unique, so `e` followed by a projection is the inequality of the meet
    have h₀ : e.hom ≫ prod.fst = homOfLE inf_le_left := Subsingleton.elim _ _
    have h₁ : e.hom ≫ prod.snd = homOfLE inf_le_right := Subsingleton.elim _ _
    apply biprod.hom_ext' <;> simp [← P.map_comp, ← op_comp, h₀, h₁]
  rw [← epi_comp_iff_of_isIso _ (P.map e.hom.op), he,
    ← epi_comp_iff_of_epi (AddCommGrpCat.biprodIsoProd _ _).inv, AddCommGrpCat.epi_iff_surjective]
  refine Iff.of_eq (congrArg _ (funext fun x ↦ ?_))
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc_apply, sub_eq_add_neg]

/-- **The Čech complex of a two-member cover, elementwise.** Let `P` be a presheaf of abelian groups
on a meet-semilattice `X` with a greatest element `⊤`, and let `U 0`, `U 1` be two elements of
`X`. The augmented Čech complex `0 ⟶ P(⊤) ⟶ Č⁰(U, P) ⟶ Č¹(U, P) ⟶ ⋯` is exact if and only if the
underlying presheaf of sets of `P` satisfies the sheaf condition for the family `U i ≤ ⊤`, and
every element of `P(U 0 ⊓ U 1)` is the difference of the restrictions of an element of `P(U 0)`
and an element of `P(U 1)`. -/
theorem quasiIso_cechAugmentation_fin_two_iff_surjective :
    QuasiIso (cechAugmentation U isTerminalTop P) ↔
      (Presieve.ofArrows U fun _ ↦ homOfLE le_top).IsSheafFor (P ⋙ forget AddCommGrpCat) ∧
        Function.Surjective fun x : P.obj (op (U 0)) × P.obj (op (U 1)) ↦
          P.map (homOfLE inf_le_left : U 0 ⊓ U 1 ⟶ U 0).op x.1 -
            P.map (homOfLE inf_le_right : U 0 ⊓ U 1 ⟶ U 1).op x.2 := by
  -- the maps to the terminal object `⊤` are the inequalities `U i ≤ ⊤`
  have hπ : (fun i ↦ isTerminalTop.from (U i)) = fun _ ↦ homOfLE le_top :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [quasiIso_cechAugmentation_fin_two_iff, epi_biprod_desc_iff_surjective,
    TauCeti.AddCommGrpCat.isSheafFor_forget_iff, hπ]

end TauCeti.CategoryTheory
