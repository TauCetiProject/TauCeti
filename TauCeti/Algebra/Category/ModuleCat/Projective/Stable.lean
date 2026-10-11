/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.CategoryTheory.Exact.Stable.Basic
import TauCeti.CategoryTheory.Functor.LocalEnd

/-!
# Indecomposable modules in the projective stable category

A finite-length indecomposable module remains indecomposable modulo maps through projectives
exactly when it is not projective. Between two such non-projective modules, the quotient
reflects isomorphisms and detects isomorphism classes.

These results connect stable equivalences, such as the Auslander--Bridger transpose, to
isomorphism classes of actual modules. They use Fitting's local-endomorphism-ring criterion
and the fact that precisely projective modules become zero in the stable category. The ring
is arbitrary; no self-injectivity or field hypothesis is needed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section IV.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v

variable {A : Type u} [Ring A]

local notation "S" =>
  TauCeti.ExactStructure.projectiveStableFunctor (TauCeti.ExactStructure.abelian (ModuleCat A))

/-- A finite-length indecomposable module remains indecomposable in the projective stable
category exactly when it is not projective. -/
@[simp]
theorem indecomposable_projectiveStableFunctor_obj_iff (M : ModuleCat.{v} A)
    (hM : IsFiniteLength A M) (hiM : Indecomposable M) :
    Indecomposable ((S).obj M) ↔ ¬ Projective M := by
  have : IsLocalRing (End M) := (TauCeti.indecomposable_iff_isLocalRing_end M hM).mp hiM
  have hzero : IsZero ((S).obj M) ↔ Projective M := by
    rw [TauCeti.ExactStructure.isZero_projectiveStableFunctor_obj_iff,
      TauCeti.ExactStructure.abelian_isProjective_iff]
  exact ⟨fun h ↦ h.1 ∘ hzero.mpr,
    fun h ↦ (S).indecomposable_obj_of_map_surjective_of_isLocalRing_end
      (h ∘ hzero.mp) (S).map_surjective⟩

/-- The projective stable quotient reflects invertibility between non-projective,
finite-length indecomposable modules. -/
@[simp]
theorem isIso_projectiveStableFunctor_map_iff {M N : ModuleCat.{v} A}
    (f : M ⟶ N) (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : Indecomposable M) (hiN : Indecomposable N) (hpM : ¬ Projective M) :
    IsIso ((S).map f) ↔ IsIso f := by
  have : IsLocalRing (End M) := (TauCeti.indecomposable_iff_isLocalRing_end M hM).mp hiM
  have : IsLocalRing (End N) := (TauCeti.indecomposable_iff_isLocalRing_end N hN).mp hiN
  have hnonzero := ((indecomposable_projectiveStableFunctor_obj_iff M hM hiM).mpr hpM).1
  exact ⟨fun _ ↦ (S).isIso_of_map_isIso_of_isLocalRing_end hnonzero (S).map_surjective f,
    fun _ ↦ inferInstance⟩

/-- Two non-projective finite-length indecomposable modules are stably isomorphic exactly
when they are isomorphic as modules. Only the source needs an explicit non-projectivity
hypothesis: a stable isomorphism forces the other module to be non-projective as well. -/
@[simp]
theorem nonempty_iso_projectiveStableFunctor_obj_iff (M N : ModuleCat.{v} A)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : Indecomposable M) (hiN : Indecomposable N) (hpM : ¬ Projective M) :
    Nonempty ((S).obj M ≅ (S).obj N) ↔ Nonempty (M ≅ N) := by
  have : IsLocalRing (End M) := (TauCeti.indecomposable_iff_isLocalRing_end M hM).mp hiM
  have : IsLocalRing (End N) := (TauCeti.indecomposable_iff_isLocalRing_end N hN).mp hiN
  exact (S).nonempty_iso_obj_iff_of_isLocalRing_end
    (((indecomposable_projectiveStableFunctor_obj_iff M hM hiM).mpr hpM).1)
    (S).map_surjective (S).map_surjective

end ModuleCat
