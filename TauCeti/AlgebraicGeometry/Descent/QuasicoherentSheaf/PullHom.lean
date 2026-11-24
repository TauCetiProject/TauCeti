/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Restricting morphisms of pullbacks of modules

The restriction maps of Mathlib's presheaves of morphisms `Pseudofunctor.presheafHom` of the
pullback pseudofunctor of modules `TauCeti.AlgebraicGeometry.Descent.modulesPseudofunctor` are
`Pseudofunctor.LocallyDiscreteOpToCat.pullHom`: a morphism `φ : f^* M ⟶ f'^* N` restricts along
`g` to `g^* φ`, read through the composition isomorphisms of pullback. This file records how
`pullHom` interacts with multiplication by global functions (`Scheme.Modules.globalSectionsSmul`)
and with pullbacks of morphisms of the modules themselves.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pullHom_globalSectionsSmul`: restricting multiplication by
  `r` along `g` gives multiplication by `g^♯ r`.
* `AlgebraicGeometry.Scheme.Modules.pullHom_globalSectionsSmul_comp`: the same, composed with a
  morphism `φ`.
* `AlgebraicGeometry.Scheme.Modules.pullHom_comp_pullback_map`: restricting `φ ≫ f'^* ψ` gives the
  restriction of `φ` followed by the pullback of `ψ`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Pseudofunctor.LocallyDiscreteOpToCat TauCeti.AlgebraicGeometry.Descent

/-- Multiplication by a global function commutes with the restriction maps `pullHom` of the
presheaves of morphisms of the pullback pseudofunctor of modules: restricting multiplication by
`r` on `f^* M` along `g` gives multiplication by `g^♯ r` on `(g ≫ f)^* M`. -/
lemma pullHom_globalSectionsSmul {X Y Y' : Scheme.{u}} {M : X.Modules} (f : Y ⟶ X)
    (r : Γ(Y, ⊤)) (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M) (f₁ := f) (f₂ := f)
        (globalSectionsSmul ((pullback f).obj M) r) g gf gf hgf hgf =
      globalSectionsSmul ((pullback gf).obj M) (g.appTop r) := by
  rw [modulesPseudofunctor_pullHom, pullback_map_globalSectionsSmul]
  have key {A B C : Y'.Modules} (e₁ : A ≅ B) (e₂ : B ≅ C) (r' : Γ(Y', ⊤)) :
      e₂.inv ≫ e₁.inv ≫ globalSectionsSmul A r' ≫ e₁.hom ≫ e₂.hom = globalSectionsSmul C r' := by
    rw [globalSectionsSmul_naturality_assoc, globalSectionsSmul_naturality, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id_assoc]
  exact key ((pullbackComp g f).app M) ((pullbackCongr hgf).app M) _

/-- Restricting a morphism `φ` composed with multiplication by a global function `r` gives the
restriction of `φ` composed with multiplication by the pullback of `r`. -/
lemma pullHom_globalSectionsSmul_comp {X X' Y Y' : Scheme.{u}} {M : X.Modules} {N : X'.Modules}
    {f : Y ⟶ X} {f' : Y ⟶ X'} (r : Γ(Y, ⊤)) (φ : (pullback f).obj M ⟶ (pullback f').obj N)
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (gf' : Y' ⟶ X') (hgf : g ≫ f = gf) (hgf' : g ≫ f' = gf') :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N) (f₁ := f) (f₂ := f')
        (globalSectionsSmul ((pullback f).obj M) r ≫ φ) g gf gf' hgf hgf' =
      globalSectionsSmul ((pullback gf).obj M) (g.appTop r) ≫
        pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N) (f₁ := f) (f₂ := f') φ g gf gf'
          hgf hgf' :=
  (Pseudofunctor.pullHom_comp _ _ g gf gf gf' hgf hgf hgf').trans
    (congrArg (· ≫ _) (pullHom_globalSectionsSmul f r g gf hgf))

/-- Restricting a morphism `φ` followed by the pullback of a morphism `ψ` gives the restriction of
`φ` followed by the pullback of `ψ`. -/
lemma pullHom_comp_pullback_map {X X' Y Y' : Scheme.{u}} {M : X.Modules} {N N' : X'.Modules}
    {f : Y ⟶ X} {f' : Y ⟶ X'} (φ : (pullback f).obj M ⟶ (pullback f').obj N) (ψ : N ⟶ N')
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (gf' : Y' ⟶ X') (hgf : g ≫ f = gf) (hgf' : g ≫ f' = gf') :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N') (f₁ := f) (f₂ := f')
        (φ ≫ (pullback f').map ψ) g gf gf' hgf hgf' =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N) (f₁ := f) (f₂ := f') φ g gf gf'
          hgf hgf' ≫ (pullback gf').map ψ :=
  (Pseudofunctor.pullHom_comp (F := modulesPseudofunctor) (M₁ := M) (M₂ := N) (M₃ := N')
    (f₁ := f) (f₂ := f') (f₃ := f') φ ((pullback f').map ψ) g gf gf' gf' hgf hgf' hgf').trans
      (congrArg (_ ≫ ·) (Pseudofunctor.pullHom_map (F := modulesPseudofunctor) ψ f' g gf' hgf'))

end AlgebraicGeometry.Scheme.Modules
