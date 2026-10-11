/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.LocallyFree
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank

/-!
# Exterior powers of finite locally free sheaves on a scheme

The `n`-th exterior power of `𝒪_X`-modules (`SheafOfModules.exteriorPower X.sheaf n`) preserves
finite local freeness (`SheafOfModules.isFiniteLocallyFree_exteriorPower`), so it restricts to an
endofunctor `FiniteLocallyFreeSheaf.exteriorPower X n` of the category of finite locally free
sheaves on `X`. A basis of `E` with `r` elements over an open `U` induces a basis of `⋀ⁿ E` over
`U` indexed by the `n`-element subsets of the basis, so the rank of `⋀ⁿ E` at `x` is
`(E.rank x).choose n`. In particular, if `E` has constant rank `r`, then `⋀ʳ E` has rank one
at every point.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.exteriorPower X n`: the `n`-th exterior power
  of finite locally free sheaves on `X`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_exteriorPower_apply`: the rank of
  `⋀ⁿ E` at `x` is `(E.rank x).choose n`.

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

/-- The `n`-th exterior power of finite locally free sheaves on a scheme `X`, computed as the
exterior power of the underlying `𝒪_X`-modules. -/
def exteriorPower (n : ℕ) : FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ SheafOfModules.exteriorPower X.sheaf n)
    fun E ↦ SheafOfModules.isFiniteLocallyFree_exteriorPower E.obj n E.property

variable {X}

/-- The underlying sheaf of the `n`-th exterior power of a finite locally free sheaf is the `n`-th
exterior power of its underlying `𝒪_X`-module. -/
@[simp]
lemma exteriorPower_obj_obj (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    ((exteriorPower X n).obj E).obj = (SheafOfModules.exteriorPower X.sheaf n).obj E.obj :=
  (rfl)

/-- The `n`-th exterior power acts on morphisms of finite locally free sheaves through the `n`-th
exterior power of the underlying morphisms of `𝒪_X`-modules. -/
@[simp]
lemma exteriorPower_map_hom (n : ℕ) {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((exteriorPower X n).map φ).hom =
      eqToHom (exteriorPower_obj_obj n E) ≫ (SheafOfModules.exteriorPower X.sheaf n).map φ.hom ≫
        eqToHom (exteriorPower_obj_obj n F).symm := by
  -- Both `eqToHom`s are identities, but `simp` cannot remove them: the module category of
  -- `X.sheaf` is that of `X.Modules` only after unfolding `Scheme.sheaf`.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The rank of the `n`-th exterior power of a finite locally free sheaf `E` at `x` is
`(E.rank x).choose n`. -/
@[simp]
theorem rank_exteriorPower_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X) (x : X) :
    ((exteriorPower X n).obj E).rank x = (E.rank x).choose n := by
  classical
  obtain ⟨U, hx, σ, hσ, hI⟩ := E.exists_generatingSections x
  let _ : LinearOrder σ.I := linearOrderOfSTO WellOrderingRel
  -- A basis of `E` over `U` induces a basis of `⋀ⁿ E` over `U` indexed by its `n`-element subsets.
  -- Its instance arguments are passed explicitly: instance search does not see through
  -- `exteriorPower_obj_obj` to recognize the restriction of `⋀ⁿ E` they are stated for.
  rw [@rank_apply_eq_natCard _ ((exteriorPower X n).obj E) _ _ hx (σ.exteriorPower n)
      (SheafOfModules.GeneratingSections.isIso_exteriorPower_π (R := X.sheaf) σ n)
      (SheafOfModules.GeneratingSections.finite_exteriorPower_I (R := X.sheaf) σ n),
    E.rank_apply_eq_natCard hx σ]
  exact (congrArg Nat.card
    (SheafOfModules.GeneratingSections.exteriorPower_I (R := X.sheaf) σ n)).trans
      (Set.powersetCard.card _ _)

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
