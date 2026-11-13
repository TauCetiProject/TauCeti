/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength.Isomorphism

/-!
# Recovering isomorphisms from the projective stable category

The projective stable quotient detects invertibility and isomorphism classes between finite-length
modules with no nonzero projective retracts. Indecomposability is not required: the modules may be
sums of non-projective indecomposables. This lets stable inverse comparisons recover actual modules
after projective summands have been excluded.

This is the case of `ModuleCat.isIso_map_iff_of_reflects_isZero_retract` for the
projective stable functor, which sends exactly the projective modules to zero.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

variable {A : Type u} [Ring A]

local notation "S" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

/-- A retract killed by the projective stable functor is projective, hence zero when `M` has no
nonzero projective retract. -/
private theorem isZero_of_retract_of_isZero_projectiveStableFunctor_obj {M : ModuleCat.{v} A}
    (hP : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    {K : ModuleCat.{v} A} (r : Retract K M) (hK : IsZero ((S).obj K)) : IsZero K :=
  hP r ((ExactStructure.abelian_isProjective_iff _).mp
    ((ExactStructure.isZero_projectiveStableFunctor_obj_iff _ _).mp hK))

/-- The projective stable quotient detects invertibility between finite-length modules
whose projective retracts are all zero. The modules need not be indecomposable. -/
theorem isIso_projectiveStableFunctor_map_iff_of_isZero_projective_retract
    {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Projective P → IsZero P) :
    IsIso ((S).map f) ↔ IsIso f :=
  ModuleCat.isIso_map_iff_of_reflects_isZero_retract (S) f ((S).map_surjective) hM hN
    (isZero_of_retract_of_isZero_projectiveStableFunctor_obj hPM)
    (isZero_of_retract_of_isZero_projectiveStableFunctor_obj hPN)

/-- Stable isomorphism is equivalent to actual isomorphism for finite-length modules
with no nonzero projective retracts. In particular this removes projective ambiguity
without assuming that either module is indecomposable. -/
theorem nonempty_iso_projectiveStableFunctor_obj_iff_of_isZero_projective_retract
    (M N : ModuleCat.{v} A) (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Projective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Projective P → IsZero P) :
    Nonempty ((S).obj M ≅ (S).obj N) ↔ Nonempty (M ≅ N) :=
  ModuleCat.nonempty_iso_obj_iff_of_reflects_isZero_retract (S) M N ((S).map_surjective)
    ((S).map_surjective) hM hN
    (isZero_of_retract_of_isZero_projectiveStableFunctor_obj hPM)
    (isZero_of_retract_of_isZero_projectiveStableFunctor_obj hPN)

end ModuleCat
