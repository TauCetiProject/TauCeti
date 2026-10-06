/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Colimits along cokernel presentations

`TauCeti.isColimitπ₃MapCoconeOfIsCokernel` transfers a colimit on the first two terms of a
cocone of short complexes to its third terms, assuming stagewise epimorphisms and a cokernel
presentation at the apex. It requires only zero morphisms, with no abelian or exactness assumptions.

The criterion generalizes the coproduct argument of `TauCeti.isColimitCofanMkCokernelCofork`
in `TauCeti/CategoryTheory/Limits/Shapes/Products` to arbitrary diagrams, using Mathlib's
`ShortComplex` projections and cokernel universal properties. The coproduct result is its
discrete-diagram specialization.
-/

public section

namespace TauCeti

open CategoryTheory Limits

variable {D : Type*} [Category* D] [HasZeroMorphisms D]
  {I : Type*} [Category I] {F : I ⥤ ShortComplex D}

/-- A cocone of short complexes is a colimit on the third terms if it is a colimit on the
first two terms, its stagewise second maps are epimorphisms, and its apex is a cokernel
sequence. No exactness of colimits or stagewise cokernel presentations are needed. -/
noncomputable def isColimitπ₃MapCoconeOfIsCokernel (c : Cocone F)
    (h₁ : IsColimit (ShortComplex.π₁.mapCocone c))
    (h₂ : IsColimit (ShortComplex.π₂.mapCocone c))
    (h : ∀ i, Epi (F.obj i).g)
    (hpt : IsColimit (CokernelCofork.ofπ c.pt.g c.pt.zero)) :
    IsColimit (ShortComplex.π₃.mapCocone c) := by
  let t (s : Cocone (F ⋙ ShortComplex.π₃)) : Cocone (F ⋙ ShortComplex.π₂) :=
    (Cocone.precompose (Functor.whiskerLeft F ShortComplex.π₂Toπ₃)).obj s
  have hz (s : Cocone (F ⋙ ShortComplex.π₃)) : c.pt.f ≫ h₂.desc (t s) = 0 := by
    apply h₁.hom_ext
    intro i
    calc
      _ = (F.obj i).f ≫ (c.ι.app i).τ₂ ≫ h₂.desc (t s) :=
        (reassoc_of% (c.ι.app i).comm₁₂) _
      _ = (F.obj i).f ≫ (t s).ι.app i := congrArg ((F.obj i).f ≫ ·) (h₂.fac (t s) i)
      _ = 0 := ((reassoc_of% (F.obj i).zero) _).trans zero_comp
      _ = _ := comp_zero.symm
  -- The projection components are recorded by `ShortComplex.π₂_map` and
  -- `ShortComplex.π₃_map`; `ShortComplex.π₂Toπ₃_app` identifies the legs of `t s`
  -- with `(F.obj i).g ≫ s.ι.app i`. These identifications are definitional.
  have hd (s : Cocone (F ⋙ ShortComplex.π₃)) :
      c.pt.g ≫ hpt.desc (CokernelCofork.ofπ (h₂.desc (t s)) (hz s)) =
        h₂.desc (t s) := Cofork.IsColimit.π_desc hpt
  have ht (s : Cocone (F ⋙ ShortComplex.π₃)) (i : I) :
      (c.ι.app i).τ₂ ≫ h₂.desc (t s) = (F.obj i).g ≫ s.ι.app i := h₂.fac (t s) i
  refine
    { desc := fun s ↦ hpt.desc (CokernelCofork.ofπ (h₂.desc (t s)) (hz s))
      fac := ?_
      uniq := ?_ }
  · intro s i
    have := h i
    apply (cancel_epi (F.obj i).g).1
    calc
      _ = (c.ι.app i).τ₂ ≫ c.pt.g ≫
          hpt.desc (CokernelCofork.ofπ (h₂.desc (t s)) (hz s)) :=
        ((reassoc_of% (c.ι.app i).comm₂₃) _).symm
      _ = (c.ι.app i).τ₂ ≫ h₂.desc (t s) :=
        congrArg ((c.ι.app i).τ₂ ≫ ·) (hd s)
      _ = _ := ht s i
  · intro s m hm
    apply Cofork.IsColimit.hom_ext hpt
    refine (h₂.hom_ext (fun i ↦ ?_)).trans (hd s).symm
    calc
      _ = (F.obj i).g ≫ (c.ι.app i).τ₃ ≫ m :=
        (reassoc_of% (c.ι.app i).comm₂₃) _
      _ = (F.obj i).g ≫ s.ι.app i := congrArg ((F.obj i).g ≫ ·) (hm i)
      _ = _ := (ht s i).symm

end TauCeti
