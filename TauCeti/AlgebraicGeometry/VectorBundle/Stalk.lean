/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.AlgebraicGeometry.Modules.Stalk
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# Stalks of finite locally free sheaves

The stalk `E_x` of a finite locally free sheaf `E` at a point `x` is a finite free module over the
local ring `𝒪_{X,x}`, of rank the rank of `E` at `x`.

On an affine open `V ∋ x`, the sections `Γ(E, V)` form a finitely generated projective
`Γ(X, V)`-module, and the germ map exhibits `E_x` as its base change to `𝒪_{X,x}`
(`AlgebraicGeometry.Scheme.Modules.isBaseChange_germₗ`). So `E_x` is finitely generated and
projective over a local ring, hence free, and its rank is the rank of `Γ(E, V)` at the prime of
`x`, which is the rank of `E` at `x`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rankAtStalk_sections`: for an affine open
  `V`, the rank of `Γ(E, V)` at a prime `p` of `Γ(X, V)` is the rank of `E` at the corresponding
  point of `X`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finite_stalk` and
  `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.free_stalk`: `E_x` is finite and free over
  `𝒪_{X,x}`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.finrank_stalk`: its rank is `E.rank x`.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

namespace FiniteLocallyFreeSheaf

variable {X : Scheme.{u}} (E : FiniteLocallyFreeSheaf X)

/-- For an affine open `V` of `X`, the rank at a prime `p` of `Γ(X, V)` of the module of sections
`Γ(E, V)` is the rank of `E` at the image of `p` in `X`. -/
theorem rankAtStalk_sections {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    Module.rankAtStalk Γ(E.obj, V) p = E.rank (hV.fromSpec p) := by
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  refine Eq.trans ?_ ((rank_apply_eq_rankAtStalk ((pullback hV.fromSpec).obj E) p).symm.trans
    (rank_pullback_apply hV.fromSpec E p))
  rw [pullback_obj_obj]
  exact congrFun (Module.rankAtStalk_eq_of_equiv ((E.obj.fromSpecSectionsEquiv hV).trans
    (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec).app E.obj)).toLinearEquiv)) p

variable (x : X)

/-- Some affine open `V ∋ x` has finitely generated projective sections `Γ(E, V)`, and the germ
map `Γ(E, V) → E_x` exhibits `E_x` as their base change to `𝒪_{X,x}`. -/
private lemma exists_isBaseChange_germₗ :
    ∃ (V : X.Opens) (y : V), IsAffineOpen V ∧ (y : X) = x ∧
      Module.Finite Γ(X, V) Γ(E.obj, V) ∧ Module.Projective Γ(X, V) Γ(E.obj, V) ∧
      IsBaseChange (X.presheaf.stalk y) (E.obj.germₗ y) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨_, _⟩ := E.obj.isFiniteLocallyFree_iff_forall_isAffineOpen.mp E.property V hV
  exact ⟨V, ⟨x, hxV⟩, hV, rfl, ‹_›, ‹_›, E.obj.isBaseChange_germₗ ⟨x, hxV⟩ hV⟩

/-- The stalk of a finite locally free sheaf is a finitely generated module over the local
ring. -/
instance finite_stalk : Module.Finite (X.presheaf.stalk x) (E.obj.presheaf.stalk x) := by
  obtain ⟨V, y, -, rfl, _, _, hb⟩ := E.exists_isBaseChange_germₗ x
  exact Module.Finite.equiv hb.equiv

/-- The stalk of a finite locally free sheaf is a projective module over the local ring. -/
instance projective_stalk : Module.Projective (X.presheaf.stalk x) (E.obj.presheaf.stalk x) := by
  obtain ⟨V, y, -, rfl, _, _, hb⟩ := E.exists_isBaseChange_germₗ x
  exact Module.Projective.of_equiv hb.equiv

/-- The stalk of a finite locally free sheaf is a free module over the local ring. -/
instance free_stalk : Module.Free (X.presheaf.stalk x) (E.obj.presheaf.stalk x) :=
  Module.free_of_flat_of_isLocalRing

/-- The stalk of a finite locally free sheaf `E` at `x` is free of rank `E.rank x` over the local
ring. -/
@[simp]
theorem finrank_stalk :
    Module.finrank (X.presheaf.stalk x) (E.obj.presheaf.stalk x) = E.rank x := by
  obtain ⟨V, y, hV, rfl, _, _, hb⟩ := E.exists_isBaseChange_germₗ x
  have hp : (IsLocalRing.closedPoint (X.presheaf.stalk y)).comap
      (algebraMap Γ(X, V) (X.presheaf.stalk y)) = hV.primeIdealOf y :=
    (hV.primeIdealOf_eq_map_closedPoint y).symm
  have := Module.rankAtStalk_isBaseChange hb (IsLocalRing.closedPoint _)
  rw [Module.rankAtStalk_eq_finrank_of_free, hp, rankAtStalk_sections E hV,
    hV.fromSpec_primeIdealOf] at this
  exact this

end FiniteLocallyFreeSheaf

end TauCeti.AlgebraicGeometry
