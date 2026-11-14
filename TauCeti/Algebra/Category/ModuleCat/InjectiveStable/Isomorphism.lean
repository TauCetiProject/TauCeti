/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Injective
public import TauCeti.Algebra.Category.ModuleCat.FiniteLength.Isomorphism

/-!
# Recovering isomorphisms from the injective stable category

The injective stable quotient detects invertibility and isomorphism classes between finite-length
modules with no nonzero injective retracts. Indecomposability is not required. This is the dual of
`TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.Isomorphism`, and the case of
`CategoryTheory.Functor.isIso_map_iff_of_isFiniteLength_of_reflects_isZero_retract` for the
injective stable functor,
which sends exactly the injective modules to zero.

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
  ExactStructure.injectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

/-- A retract killed by the injective stable functor is injective, hence zero when `M` has no
nonzero injective retract. -/
private theorem isZero_of_retract_of_isZero_injectiveStableFunctor_obj {M : ModuleCat.{v} A}
    (hP : ∀ {P : ModuleCat.{v} A}, Retract P M → Injective P → IsZero P)
    {K : ModuleCat.{v} A} (r : Retract K M) (hK : IsZero ((S).obj K)) : IsZero K :=
  hP r ((ExactStructure.abelian_isInjective_iff _).mp
    ((ExactStructure.isZero_injectiveStableFunctor_obj_iff _ _).mp hK))

/-- The injective stable quotient detects invertibility between finite-length modules
whose injective retracts are all zero. The modules need not be indecomposable. -/
theorem isIso_injectiveStableFunctor_map_iff_of_isZero_injective_retract
    {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Injective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Injective P → IsZero P) :
    IsIso ((S).map f) ↔ IsIso f :=
  (S).isIso_map_iff_of_isFiniteLength_of_reflects_isZero_retract f ((S).map_surjective) hM hN
    (isZero_of_retract_of_isZero_injectiveStableFunctor_obj hPM)
    (isZero_of_retract_of_isZero_injectiveStableFunctor_obj hPN)

/-- Isomorphism in the injective stable category is equivalent to actual isomorphism for
finite-length modules
with no nonzero injective retracts. In particular this removes injective ambiguity
without assuming that either module is indecomposable. -/
theorem nonempty_iso_injectiveStableFunctor_obj_iff_of_isZero_injective_retract
    (M N : ModuleCat.{v} A) (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hPM : ∀ {P : ModuleCat.{v} A}, Retract P M → Injective P → IsZero P)
    (hPN : ∀ {P : ModuleCat.{v} A}, Retract P N → Injective P → IsZero P) :
    Nonempty ((S).obj M ≅ (S).obj N) ↔ Nonempty (M ≅ N) :=
  (S).nonempty_iso_obj_iff_of_isFiniteLength_of_reflects_isZero_retract M N ((S).map_surjective)
    ((S).map_surjective) hM hN
    (isZero_of_retract_of_isZero_injectiveStableFunctor_obj hPM)
    (isZero_of_retract_of_isZero_injectiveStableFunctor_obj hPN)

end ModuleCat
