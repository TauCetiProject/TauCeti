/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Additive functors on objects with local endomorphism rings

A full additive functor sends a local endomorphism ring to a local endomorphism ring,
provided the image object is nonzero. It also reflects isomorphisms between objects with
local endomorphism rings whose images are nonzero. Only surjectivity on the relevant hom-sets
is needed. These results let additive quotients retain indecomposability and distinguish
isomorphism classes even though they are not faithful.

No splitting of idempotents in the quotient is required: locality of its endomorphism ring
already rules out nontrivial biproduct decompositions.
-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive] {X Y : C}

/-- An endomorphism of an object with local endomorphism ring is invertible if an additive
functor sends it to the identity of a nonzero object. -/
theorem isIso_of_map_eq_id_of_isLocalRing_end [IsLocalRing (End X)]
    (hX : ¬ IsZero (F.obj X)) (f : X ⟶ X) (hf : F.map f = 𝟙 (F.obj X)) : IsIso f := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (R := End X) f with hu | hu
  · exact (isUnit_iff_isIso f).mp hu
  · have : Nontrivial (End (F.obj X)) :=
      nontrivial_of_ne (𝟙 (F.obj X)) 0 (fun h ↦ hX ((IsZero.iff_id_eq_zero _).mpr h))
    have hunit := hu.map (F.mapEnd X)
    have hzero : F.mapEnd X (1 - End.of f) = 0 := by
      simp only [mapEnd_apply, F.map_sub, End.one_def, F.map_id, hf, sub_self]
    rw [hzero] at hunit
    exact (not_isUnit_zero hunit).elim

/-- A nonzero image under an additive functor is indecomposable if the original object's
endomorphism ring is local and the functor is surjective on its endomorphisms. -/
theorem indecomposable_obj_of_map_surjective_of_isLocalRing_end [HasBinaryBiproducts D]
    [IsLocalRing (End X)] (hX : ¬ IsZero (F.obj X))
    (hF : Function.Surjective (F.map : End X → End (F.obj X))) : Indecomposable (F.obj X) := by
  have : Nontrivial (End (F.obj X)) :=
    nontrivial_of_ne (𝟙 (F.obj X)) 0 (fun h ↦ hX ((IsZero.iff_id_eq_zero _).mpr h))
  have := IsLocalRing.of_surjective'
    ({ F.mapEnd X, F.mapAddHom with } : End X →+* End (F.obj X)) hF
  exact TauCeti.indecomposable_of_injective_of_isLocalRing hX (id : End (F.obj X) → _)
    Function.injective_id rfl rfl (fun _ ↦ rfl)

/-- An additive functor surjective on morphisms from `Y` to `X` reflects invertibility
of a morphism from `X` to `Y` when their endomorphism rings are local and the source image
is nonzero. -/
theorem isIso_of_map_isIso_of_isLocalRing_end [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (hX : ¬ IsZero (F.obj X))
    (hF : Function.Surjective (F.map : (Y ⟶ X) → (F.obj Y ⟶ F.obj X)))
    (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f := by
  obtain ⟨g, hg⟩ := hF (CategoryTheory.inv (F.map f))
  have : IsIso (f ≫ g) := F.isIso_of_map_eq_id_of_isLocalRing_end hX _ (by
    rw [F.map_comp, hg, IsIso.hom_inv_id])
  refine TauCeti.isIso_of_isIso_comp
    (by simpa only [End.one_def] using one_ne_zero (α := End X))
    (fun e he ↦ ?_) f g inferInstance
  simpa only [End.one_def] using
    TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem (R := End Y)
      (a := e) (by simpa only [IsIdempotentElem, End.mul_def] using he)

/-- An additive functor surjective on morphisms in both directions between two objects
detects their isomorphism classes when their endomorphism rings are local and the source
image is nonzero. -/
theorem nonempty_iso_obj_iff_of_isLocalRing_end [IsLocalRing (End X)] [IsLocalRing (End Y)]
    (hX : ¬ IsZero (F.obj X))
    (hF : Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)))
    (hF' : Function.Surjective (F.map : (Y ⟶ X) → (F.obj Y ⟶ F.obj X))) :
    Nonempty (F.obj X ≅ F.obj Y) ↔ Nonempty (X ≅ Y) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f, hf⟩ := hF e.hom
    have : IsIso (F.map f) := hf.symm ▸ e.isIso_hom
    have : IsIso f := F.isIso_of_map_isIso_of_isLocalRing_end hX hF' f
    exact ⟨asIso f⟩
  · exact fun ⟨e⟩ ↦ ⟨F.mapIso e⟩

end CategoryTheory.Functor
