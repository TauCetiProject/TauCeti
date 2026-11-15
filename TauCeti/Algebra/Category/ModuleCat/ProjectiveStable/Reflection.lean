/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Functor.Indecomposable
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Reflecting indecomposability from the projective stable category

The projective stable quotient forgets projective summands. If a module has no nonzero
projective retract, however, indecomposability of its stable image implies indecomposability
of the module itself. This recovers actual indecomposability from stable constructions such
as the Auslander–Bridger transpose, once projective summands have been excluded.

No finite-length, Artinian, or field hypothesis is needed for this implication.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

variable {A : Type u} [Ring A]

/-- For a module whose stable image is indecomposable, actual indecomposability is equivalent
to every projective retract being zero. -/
theorem indecomposable_iff_isZero_projective_retract (M : ModuleCat.{v} A)
    (hM : Indecomposable
      ((ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableFunctor.obj M)) :
    Indecomposable M ↔
      ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P := by
  let F := (ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableFunctor
  let _ : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  constructor
  · intro h P r hP
    have h0 : IsZero (F.obj P) :=
      (ExactStructure.isZero_projectiveStableFunctor_obj_iff _ P).mpr
        ((ExactStructure.abelian_isProjective_iff P).mpr hP)
    have hr : (r.r ≫ r.i) ≫ (r.r ≫ r.i) = r.r ≫ r.i := by simp
    rcases idempotent_eq_zero_or_id_of_indecomposable h hr with he | he
    · apply (IsZero.iff_id_eq_zero P).mpr
      have := congrArg (fun e : M ⟶ M ↦ r.i ≫ e ≫ r.r) he
      simpa using this
    · exact False.elim (hM.1 ((IsZero.iff_id_eq_zero (F.obj M)).mpr (by
        rw [← F.map_id, ← he, F.map_comp, h0.eq_of_tgt (F.map r.r) 0, zero_comp])))
  · intro hP
    apply Functor.indecomposable_of_indecomposable_obj_of_reflects_isZero_retract F hM
    intro P r h0
    exact hP r ((ExactStructure.abelian_isProjective_iff P).mp
      ((ExactStructure.isZero_projectiveStableFunctor_obj_iff _ P).mp h0))

end ModuleCat
