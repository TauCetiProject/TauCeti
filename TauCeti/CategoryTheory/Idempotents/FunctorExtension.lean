/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Extending fully faithful functors across the Karoubi envelope

A fully faithful functor to an idempotent-complete category extends to a fully faithful functor
on the Karoubi envelope. Its essential image consists of retracts of objects in the original
essential image.
-/

public section

namespace CategoryTheory

open Idempotents CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}

namespace Idempotents

/-- Restriction of the extension to the original category recovers the original functor. -/
noncomputable def toKaroubiCompFunctorExtensionIso [IsIdempotentComplete D] (F : C ⥤ D) :
    toKaroubi C ⋙ (functorExtension C D).obj F ≅ F :=
  let E := toKaroubiEquivalence D
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F) E.inverse ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F E.unitIso.symm ≪≫ F.rightUnitor

end Idempotents

namespace Functor.FullyFaithful

/-- Extending a fully faithful functor to a functor between Karoubi envelopes preserves full
faithfulness. The preimage of a morphism between formal summands is obtained by taking the
preimage of its underlying morphism. -/
def functorExtension₂ (hF : F.FullyFaithful) :
    ((Idempotents.functorExtension₂ C D).obj F).FullyFaithful where
  preimage f := ⟨hF.preimage f.f, hF.map_injective (by simpa using f.comm)⟩
  map_preimage f := Karoubi.hom_ext _ _ (by simp)
  preimage_map f := Karoubi.hom_ext _ _ (by simp)

/-- The extension of a fully faithful functor across the Karoubi envelope is fully faithful. -/
noncomputable def functorExtension [IsIdempotentComplete D] (hF : F.FullyFaithful) :
    ((Idempotents.functorExtension C D).obj F).FullyFaithful :=
  hF.functorExtension₂.comp (ofFullyFaithful (toKaroubiEquivalence D).inverse)

/-- The essential image of the extended functor is the retract closure of the original essential
image. -/
theorem essImage_functorExtension [IsIdempotentComplete D] (hF : F.FullyFaithful) :
    ((Idempotents.functorExtension C D).obj F).essImage = F.essImage.retractClosure := by
  let G := (Idempotents.functorExtension C D).obj F
  let e := toKaroubiCompFunctorExtensionIso F
  let : G.Full := hF.functorExtension.full
  let : G.Faithful := hF.functorExtension.faithful
  refine le_antisymm (fun Y hY ↦ ?_) ?_
  · obtain ⟨P, ⟨i⟩⟩ := hY
    exact ⟨F.obj P.X, F.obj_mem_essImage P.X,
      ⟨i.symm.retract.trans (((Karoubi.retract P).map G).trans (e.app P.X).retract)⟩⟩
  · apply (F.essImage.retractClosure_le_iff G.essImage).2
    rintro Y ⟨X, ⟨i⟩⟩
    exact ⟨(toKaroubi C).obj X, ⟨e.app X ≪≫ i⟩⟩

end Functor.FullyFaithful

end CategoryTheory
