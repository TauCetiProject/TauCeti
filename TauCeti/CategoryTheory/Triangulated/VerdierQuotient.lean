/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Kernels and triangle functors out of Verdier quotients

Let `C` be a triangulated category and `P` a triangulated subcategory. The Verdier quotient of
`C` by `P` is a localization of `C` at `P.trW`, the morphisms whose cone satisfies `P`; Mathlib
constructs it as `P.trW.Localization` and makes it triangulated. This file records the two
facts that identify what such a quotient kills and what maps out of it.

* **The kernel.** An object becomes zero in the Verdier quotient exactly when it is a retract of
  an object satisfying `P`. In particular, when `P` is thick (stable under retracts) the objects
  killed are exactly those satisfying `P`. The proof uses the left calculus of fractions: the
  identity of `X` becomes zero exactly when some `s : X ⟶ Z` in `P.trW` vanishes, and the cone
  of a zero map `X ⟶ Z` is `Z ⊞ X⟦1⟧`.
* **The universal property among triangle functors.** A triangle functor inverts `P.trW`
  exactly when it sends every object satisfying `P` to zero, that is, when `P` lies in its
  kernel `Functor.kernel`. For the thick closure `P.triangEnvelope` it suffices to kill `P`
  itself, because the kernel of a triangle functor is a thick triangulated subcategory. A
  triangle functor killing `P` then descends to a triangle functor out of every localization of
  `C` at `P.trW`.

Comparison functors between Verdier quotients by nested subcategories `P ≤ Q` are the descents
of the localization functor at `Q.trW`.

## Main results

* `CategoryTheory.ObjectProperty.isZero_obj_iff_retractClosure`,
  `CategoryTheory.ObjectProperty.isZero_obj_iff`: the kernel of a Verdier localization.
* `CategoryTheory.ObjectProperty.trW_isInvertedBy_iff`: a triangle functor inverts `P.trW` if
  and only if it kills `P`.
* `CategoryTheory.ObjectProperty.triangEnvelope_trW_isInvertedBy_iff`: a triangle functor
  inverts the morphisms with cone in the thick closure of `P` if and only if it kills `P`.
* `CategoryTheory.ObjectProperty.trWLift`: the triangle functor out of a Verdier localization
  induced by a triangle functor killing `P`, with `trWLiftFactors` and its `IsTriangulated`
  instance.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque **239** (1996),
  Chapitre II, §2.
* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Chapter 2.
-/

public section

namespace CategoryTheory

open Limits Pretriangulated
open scoped ZeroObject

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {E : Type*} [Category* E] [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-! ### Zero objects and kernels of triangle functors -/

/-- The zero objects of a category are closed under isomorphisms. -/
instance {D : Type*} [Category* D] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := D)) where
  of_iso e hX := hX.of_iso e.symm

/-- The zero objects of a pretriangulated category form a triangulated subcategory. -/
instance : ObjectProperty.IsTriangulated (IsZero (C := E)) where
  exists_zero := ⟨0, isZero_zero E, isZero_zero E⟩
  isStableUnderShiftBy n := ⟨fun _ hX ↦ (shiftFunctor E n).map_isZero hX⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦ Triangle.isZero₂_of_isZero₁₃ T hT h₁ h₃

/-- The kernel of any functor to a category with zero morphisms is stable under retracts. -/
instance {B D : Type*} [Category* B] [Category* D] [HasZeroMorphisms D] (F : B ⥤ D) :
    F.kernel.IsStableUnderRetracts where
  of_retract h hY := IsZero.of_mono (h.map F).i hY

/-! ### Triangle functors inverting `P.trW` -/

namespace ObjectProperty

variable (P : ObjectProperty C) (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]

/-- **The universal property of the Verdier quotient.** A triangle functor inverts the morphisms
whose cone satisfies `P` if and only if it sends every object satisfying `P` to zero. -/
theorem trW_isInvertedBy_iff : P.trW.IsInvertedBy F ↔ P ≤ F.kernel := by
  refine ⟨fun hF X hX ↦ ?_, fun hF X Y f ⟨Z, g, h, hT, hZ⟩ ↦ ?_⟩
  · have : IsIso (F.map (0 : 0 ⟶ X)) := hF _ (trW.mk P (contractible_distinguished₁ X) hX)
    exact (F.map_isZero (isZero_zero C)).of_iso (asIso (F.map (0 : 0 ⟶ X))).symm
  · exact (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).1 (hF Z hZ)

/-- A triangle functor inverts the morphisms whose cone lies in the thick closure of `P` if and
only if it sends every object satisfying `P` to zero. -/
theorem triangEnvelope_trW_isInvertedBy_iff :
    P.triangEnvelope.trW.IsInvertedBy F ↔ P ≤ F.kernel := by
  rw [trW_isInvertedBy_iff, triangEnvelope_le_iff]

/-! ### The kernel of a Verdier localization -/

variable [IsTriangulated C] [P.IsTriangulated]
  {D : Type*} [Category* D] [HasZeroMorphisms D] (L : C ⥤ D) [L.IsLocalization P.trW]
  [L.PreservesZeroMorphisms]

/-- **The kernel of a Verdier localization.** An object becomes zero in a localization at
`P.trW` exactly when it is a retract of an object satisfying `P`. -/
theorem isZero_obj_iff_retractClosure (X : C) : IsZero (L.obj X) ↔ P.retractClosure X := by
  constructor
  · intro hX
    obtain ⟨Z, s, ⟨W, g, h, hT, hW⟩, hs⟩ := (MorphismProperty.map_eq_iff_postcomp L P.trW
      (𝟙 X) 0).1 (by rw [L.map_id, L.map_zero]; exact hX.eq_of_src _ _)
    rw [Category.id_comp, zero_comp] at hs
    subst hs
    -- The cone `W` of the zero map `X ⟶ Z` is `Z ⊞ X⟦1⟧`, so `X⟦1⟧` is a retract of `W`, and
    -- `X` is a retract of `W⟦-1⟧`.
    obtain ⟨e, -⟩ := exists_iso_binaryBiproduct_of_distTriang
      (Triangle.mk (0 : X ⟶ Z) g h).rotate (rot_of_distTriang _ hT)
      (neg_eq_zero.2 (Functor.map_zero _ _ _))
    have r : Retract (X⟦(1 : ℤ)⟧) W :=
      (BinaryBiproduct.bicone Z (X⟦(1 : ℤ)⟧)).retract_right.trans (Retract.ofIso e.symm)
    exact ⟨_, P.le_shift (-1) W hW,
      ⟨(Retract.ofIso ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by simp)).app X).symm).trans
        (r.map (shiftFunctor C (-1)))⟩⟩
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have : IsIso (L.map (0 : Y ⟶ 0)) :=
      Localization.inverts L P.trW _ (trW.mk' P (contractible_distinguished Y) hY)
    exact IsZero.of_mono (r.map L).i
      ((L.map_isZero (isZero_zero C)).of_iso (asIso (L.map (0 : Y ⟶ 0))))

/-- When `P` is thick, an object becomes zero in a localization at `P.trW` exactly when it
satisfies `P`. -/
theorem isZero_obj_iff [P.IsStableUnderRetracts] (X : C) : IsZero (L.obj X) ↔ P X := by
  rw [isZero_obj_iff_retractClosure P L, retractClosure_eq_self]

/-! ### Descending triangle functors -/

/-- The triangle functor out of a Verdier localization `P.trW.Localization` induced by a
triangle functor killing `P`. -/
noncomputable def trWLift (hF : P ≤ F.kernel) : P.trW.Localization ⥤ E :=
  Localization.lift F ((P.trW_isInvertedBy_iff F).2 hF) P.trW.Q

/-- The functor `trWLift` restricts to the original triangle functor along the localization
functor. -/
noncomputable def trWLiftFactors (hF : P ≤ F.kernel) : P.trW.Q ⋙ P.trWLift F hF ≅ F :=
  Localization.fac _ _ _

noncomputable instance (hF : P ≤ F.kernel) :
    Localization.Lifting P.trW.Q P.trW F (P.trWLift F hF) :=
  ⟨P.trWLiftFactors F hF⟩

noncomputable instance (hF : P ≤ F.kernel) : (P.trWLift F hF).CommShift ℤ :=
  Functor.commShiftOfLocalization P.trW.Q P.trW ℤ F (P.trWLift F hF)

instance (hF : P ≤ F.kernel) : NatTrans.CommShift (P.trWLiftFactors F hF).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Localization.Lifting.iso P.trW.Q P.trW F (P.trWLift F hF)).hom ℤ)

/-- The functor induced on the Verdier quotient by a triangle functor killing `P` is a triangle
functor. -/
instance (hF : P ≤ F.kernel) : (P.trWLift F hF).IsTriangulated :=
  have := Localization.essSurj_mapArrow P.trW.Q P.trW
  Functor.isTriangulated_of_precomp_iso (P.trWLiftFactors F hF)

end ObjectProperty

end CategoryTheory
