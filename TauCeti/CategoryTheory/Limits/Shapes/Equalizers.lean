/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Colimits commute with coequalizers

Let `α β : F ⟶ G` and `π : G ⟶ H` be natural transformations of diagrams `J ⥤ D` such that each
component `π j` is a coequalizer of `α j` and `β j`.  If `F` and `G` have colimit cocones, then a
cocone on `H` whose apex is the coequalizer of the maps induced by `α` and `β` on the colimits is
itself a colimit cocone (`TauCeti.isColimitOfIsColimitCofork`).  No existence of colimits or
coequalizers in `D` is assumed: all the relevant cocones and coforks are given.

The special case of cokernels is `TauCeti.isColimitOfIsColimitCokernelCofork`.
-/

public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace TauCeti

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D]
  {F G H : J ⥤ D} {α β : F ⟶ G} {π : G ⟶ H} {w : ∀ j, α.app j ≫ π.app j = β.app j ≫ π.app j}
  {cF : Cocone F} {cG : Cocone G} {cH : Cocone H} {f g : cF.pt ⟶ cG.pt} {p : cG.pt ⟶ cH.pt}
  {wp : f ≫ p = g ≫ p}

/-- **Colimits commute with coequalizers.**  Let `π j` be a coequalizer of `α j` and `β j` for
every `j`, let `cF` and `cG` be colimit cocones, and let `f`, `g` and `p` be maps of apexes
compatible with `α`, `β` and `π`.  If `p` is a coequalizer of `f` and `g`, then `cH` is a colimit
cocone. -/
def isColimitOfIsColimitCofork (hπ : ∀ j, IsColimit (Cofork.ofπ _ (w j)))
    (hF : IsColimit cF) (hG : IsColimit cG)
    (hf : ∀ j, cF.ι.app j ≫ f = α.app j ≫ cG.ι.app j)
    (hg : ∀ j, cF.ι.app j ≫ g = β.app j ≫ cG.ι.app j)
    (hp : ∀ j, cG.ι.app j ≫ p = π.app j ≫ cH.ι.app j)
    (hcoeq : IsColimit (Cofork.ofπ p wp)) : IsColimit cH :=
  -- A cocone `s` on `H` gives a cocone on `G` by precomposition with `π`, whose descent `φ s`
  -- coequalizes `f` and `g` because each `π j` coequalizes `α j` and `β j`; so `φ s` descends to
  -- the coequalizer of `f` and `g`.
  let φ (s : Cocone H) : cG.pt ⟶ s.pt := hG.desc
    { pt := s.pt
      ι :=
        { app j := π.app j ≫ s.ι.app j
          naturality j j' u := by simp } }
  have hφ (s : Cocone H) (j : J) : cG.ι.app j ≫ φ s = π.app j ≫ s.ι.app j := hG.fac _ j
  let desc (s : Cocone H) : cH.pt ⟶ s.pt :=
    Cofork.IsColimit.desc hcoeq (φ s) <| hF.hom_ext fun j ↦ by
      rw [reassoc_of% (hf j), reassoc_of% (hg j), hφ, reassoc_of% (w j)]
  have hdesc (s : Cocone H) : p ≫ desc s = φ s := Cofork.IsColimit.π_desc' hcoeq _ _
  { desc
    fac s j := Cofork.IsColimit.hom_ext (hπ j) <| by
      rw [Cofork.π_ofπ, ← reassoc_of% (hp j), hdesc, hφ]
    uniq s m hm := Cofork.IsColimit.hom_ext hcoeq <| hG.hom_ext fun j ↦ by
      rw [Cofork.π_ofπ, hdesc, reassoc_of% (hp j), hm, hφ] }

end TauCeti
