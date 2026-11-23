/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# Contractions of schemes

A contraction is a proper morphism `f : X ⟶ Y` whose canonical map
`𝒪_Y ⟶ f_*𝒪_X` is an isomorphism. We express this on sections over every open of `Y`.
In particular this is not a condition only on global functions or on the underlying fibres.

Contractions are surjective epimorphisms, compose, and remain contractions upon restriction
to an open of the target. An affine contraction is an isomorphism. No Noetherianity,
reducedness or connectedness assumptions on either scheme are needed for these results.
These elementary properties provide the cancellation and locality needed when descending maps
along contractions. Descent of a map constant on fibres can use
`AlgebraicGeometry.Scheme.Hom.existsUnique_comp_eq_of_universallyClosed` from
`TauCeti.AlgebraicGeometry.Descent.Contraction`, with `IsContraction.isIso_app`.

## References

* S. Schröer, *There is no Enriques surface over the integers*, Annals of Mathematics 197
  (2023), §1, for the convention that a contraction is proper with `f_*𝒪_X = 𝒪_Y`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- A **contraction** is a proper morphism whose canonical structure-sheaf map is an
isomorphism, expressed by its maps on sections over all opens of the target. -/
@[mk_iff]
class IsContraction (f : X ⟶ Y) : Prop extends IsProper f where
  /-- The canonical map on sections over each open of the target is an isomorphism. -/
  isIso_app (U : Y.Opens) : IsIso (f.app U)

attribute [instance] IsContraction.isIso_app

namespace IsContraction

/-- An isomorphism is a contraction. -/
instance (priority := 100) of_isIso (f : X ⟶ Y) [IsIso f] : IsContraction f where
  isIso_app _ := inferInstance

/-- The composite of two contractions is a contraction. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsContraction f] [IsContraction g] :
    IsContraction (f ≫ g) where
  isIso_app U := by
    rw [Scheme.Hom.comp_app]
    exact IsIso.comp_isIso' (isIso_app (f := g) U) (isIso_app (f := f) (g ⁻¹ᵁ U))

/-- A contraction is scheme-theoretically dominant, including when its target is nonreduced. -/
instance (priority := 100) isSchemeTheoreticallyDominant (f : X ⟶ Y) [IsContraction f] :
    IsSchemeTheoreticallyDominant f where
  ker_eq_bot := by
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (ConcreteCategory.bijective_of_isIso (f.app U)).1

/-- A contraction is an epimorphism of schemes, without a separatedness hypothesis on the
schemes to which maps are compared. -/
instance (priority := 100) epi (f : X ⟶ Y) [IsContraction f] : Epi f :=
  f.epi_of_surjective_of_app_injective fun U ↦
    (ConcreteCategory.bijective_of_isIso (f.app U)).1

/-- Restricting a contraction over an open of its target gives a contraction. -/
instance morphismRestrict (f : X ⟶ Y) [IsContraction f] (U : Y.Opens) :
    IsContraction (f ∣_ U) where
  isIso_app V := by
    rw [morphismRestrict_app]
    refine IsIso.comp_isIso' (isIso_app (f := f) (U.ι ''ᵁ V)) ?_
    apply Functor.map_isIso

end IsContraction

/-- An affine morphism is a contraction exactly when it is an isomorphism. In particular,
a finite birational morphism need not be a contraction. -/
theorem isContraction_iff_isIso (f : X ⟶ Y) [IsAffineHom f] :
    IsContraction f ↔ IsIso f := by
  constructor
  · intro hf
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := .isomorphisms _) fun y ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
    exact ⟨U, hyU, (isIso_morphismRestrict_iff_isIso_app f hU).mpr (hf.isIso_app U)⟩
  · intro hf
    infer_instance

end TauCeti.AlgebraicGeometry
