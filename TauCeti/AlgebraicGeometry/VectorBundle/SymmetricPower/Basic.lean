/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.LocallyFree
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank

/-!
# Symmetric powers of finite locally free sheaves on a scheme

Symmetric powers preserve finite local freeness, so they restrict to endofunctors on finite
locally free sheaves. A basis with `r` elements induces the monomial basis indexed by exponent
vectors of total degree `n`; hence the rank of `Symⁿ E` is `r.multichoose n`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.symmetricPower`: symmetric power as an
  endofunctor of finite locally free sheaves;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_symmetricPower_apply`: its rank formula.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable (X : Scheme.{u})

/-- The `n`-th symmetric power endofunctor on finite locally free sheaves over `X`. -/
def symmetricPower (n : ℕ) : FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ SheafOfModules.symmetricPower X.sheaf n)
    fun E ↦ SheafOfModules.isFiniteLocallyFree_symmetricPower E.obj n E.property

variable {X}

/-- The underlying sheaf of a symmetric power is the symmetric power of the underlying
`𝒪_X`-module. -/
@[simp]
lemma symmetricPower_obj_obj (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    ((symmetricPower X n).obj E).obj = (SheafOfModules.symmetricPower X.sheaf n).obj E.obj :=
  (rfl)

/-- Symmetric powers act on morphisms through the symmetric power of the underlying morphism. -/
@[simp]
lemma symmetricPower_map_hom (n : ℕ) {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((symmetricPower X n).map φ).hom =
      eqToHom (symmetricPower_obj_obj n E) ≫
        (SheafOfModules.symmetricPower X.sheaf n).map φ.hom ≫
          eqToHom (symmetricPower_obj_obj n F).symm := by
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The rank of `Symⁿ E` at `x` is the number of monomials of degree `n` in `E.rank x`
variables. -/
@[simp]
theorem rank_symmetricPower_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X) (x : X) :
    ((symmetricPower X n).obj E).rank x = (E.rank x).multichoose n := by
  classical
  obtain ⟨U, hx, σ, hσ, hI⟩ := E.exists_generatingSections x
  rw [@rank_apply_eq_natCard _ ((symmetricPower X n).obj E) _ _ hx (σ.symmetricPower n)
      (SheafOfModules.GeneratingSections.isIso_symmetricPower_π (R := X.sheaf) σ n)
      (SheafOfModules.GeneratingSections.finite_symmetricPower_I (R := X.sheaf) σ n),
    E.rank_apply_eq_natCard hx σ]
  refine (congrArg Nat.card
    (SheafOfModules.GeneratingSections.symmetricPower_I (R := X.sheaf) σ n)).trans ?_
  exact Sym.natCard_sym_eq_multichoose σ.I n

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
