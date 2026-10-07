/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Free sheaves on finitely many generators

This file records the canonical identification between the free sheaf of modules on one
generator and the tensor unit, and that the free sheaf on no generators is a zero object. It is
stated over an arbitrary site and without tying the universe of the coefficient modules to either
universe of the site.

For a finite index type, the free sheaf is also a finite biproduct of copies of the sheaf of
rings, so each of its sections is a linear combination of the tautological sections
`SheafOfModules.freeSection`, with coefficients in the ring of sections over the same object.
The morphism out of a free sheaf determined by a family of sections sends such a combination to
the corresponding combination of those sections. These are the sectionwise computations by
which generators and relations of a finitely presented sheaf are handled locally.

## Main declarations

* `TauCeti.SheafOfModules.freePUnitIsoUnit` identifies the free sheaf on `PUnit` with the sheaf
  of rings itself, regarded as a sheaf of modules;
* `TauCeti.SheafOfModules.isZero_free`: the free sheaf on an empty type is a zero object;
* `TauCeti.SheafOfModules.exists_eq_sum_smul_freeSection`: every section of a finite free sheaf
  is a linear combination of the tautological sections;
* `TauCeti.SheafOfModules.freeHomEquiv_symm_val_app_sum_smul`: evaluation of the morphism out
  of a free sheaf on such a linear combination;
* `TauCeti.SheafOfModules.isIso_unitHomEquiv_symm`: the morphism `unit R ⟶ M` attached to a
  global section `s` is an isomorphism when scalar multiplication on `s` is bijective over every
  object, that is, when `s` is a global basis of `M`.

The first comparison is used both by tensor-unit computations and when restricting a rank-one
local trivialization. No formalization is vendored; it is Mathlib's canonical isomorphism from a
coproduct indexed by a unique type to its unique summand.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf on one generator is canonically isomorphic to the tensor unit. -/
def freePUnitIsoUnit (S : Sheaf J RingCat.{u}) :
    _root_.SheafOfModules.free.{u, v₁, u₁} (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit.{v₁, u₁, u} S :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

/-- The inverse of `freePUnitIsoUnit` is the unique basis inclusion. -/
@[simp]
lemma freePUnitIsoUnit_inv (S : Sheaf J RingCat.{u}) :
    (freePUnitIsoUnit S).inv =
      _root_.SheafOfModules.ιFree (R := S) PUnit.unit := by
  exact coproductUniqueIso_inv (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

/-- The free sheaf of modules on an empty type is a zero object: it is the coproduct of the empty
family. -/
theorem isZero_free {S : Sheaf J RingCat.{u}} (I : Type u) [IsEmpty I] :
    IsZero (_root_.SheafOfModules.free (R := S) I) :=
  (isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit _)).isZero

section Sections

variable {R : Sheaf J RingCat.{u}} {I : Type u} [Fintype I]

/-- Every section of a free sheaf on a finite type is a linear combination of the tautological
sections, with coefficients in the ring of sections over the same object. -/
theorem exists_eq_sum_smul_freeSection {Y : Cᵒᵖ}
    (c : (_root_.SheafOfModules.free (R := R) I).val.obj Y) :
    ∃ a : I → R.obj.obj Y,
      c = ∑ k, a k • (_root_.SheafOfModules.freeSection (R := R) k).eval Y := by
  classical
  -- The coordinate projections of the finite coproduct `free I` onto its summands.
  let p : I → (_root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.unit R) :=
    fun k ↦ Cofan.IsColimit.desc (_root_.SheafOfModules.isColimitFreeCofan I)
      (fun j ↦ if j = k then 𝟙 _ else 0)
  have htot : ∑ k, p k ≫ _root_.SheafOfModules.ιFree k = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext (_root_.SheafOfModules.isColimitFreeCofan I) _ _ fun j ↦ ?_
    have hp (k : I) : _root_.SheafOfModules.ιFree j ≫ p k = if j = k then 𝟙 _ else 0 :=
      Cofan.IsColimit.fac (_root_.SheafOfModules.isColimitFreeCofan I) _ j
    -- The injections of `freeCofan I` are the `ιFree j`, but its cone point is only
    -- definitionally `free I`, so the goal is restated with that point.
    change _root_.SheafOfModules.ιFree j ≫ _ = _root_.SheafOfModules.ιFree j ≫ _
    rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
    · rw [← Category.assoc, hp]
      simp
    · intro k _ hk
      rw [← Category.assoc, hp]
      simp [Ne.symm hk]
    · simp
  refine ⟨fun k ↦ (p k).val.app Y c, ?_⟩
  let ev : (_root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.free I) →+
      (_root_.SheafOfModules.free (R := R) I).val.obj Y :=
    { toFun f := f.val.app Y c, map_zero' := rfl, map_add' _ _ := rfl }
  calc c = ev (∑ k, p k ≫ _root_.SheafOfModules.ιFree k) := by rw [htot]; rfl
    _ = _ := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      -- The tautological section is the image of `1` under the basis inclusion.
      have h1 : (_root_.SheafOfModules.freeSection (R := R) k).eval Y =
          (_root_.SheafOfModules.ιFree k).val.app Y (1 : R.obj.obj Y) := rfl
      have h2 : ev (p k ≫ _root_.SheafOfModules.ιFree k) =
          (_root_.SheafOfModules.ιFree k).val.app Y ((p k).val.app Y c) := rfl
      rw [h1, h2]
      -- The unit module has `R.obj.obj Y` itself as carrier, so `r = r • 1` there.
      exact (congrArg ((_root_.SheafOfModules.ιFree k).val.app Y)
        (@mul_one (R.obj.obj Y) _ ((p k).val.app Y c)).symm).trans
          (((_root_.SheafOfModules.ιFree k).val.app Y).hom.map_smul ((p k).val.app Y c)
            (1 : R.obj.obj Y))

/-- The morphism out of a finite free sheaf determined by a family of sections `s` sends a
linear combination of the tautological sections to the same linear combination of the `s k`. -/
theorem freeHomEquiv_symm_val_app_sum_smul {M : _root_.SheafOfModules.{u} R}
    (s : I → M.sections) (Y : Cᵒᵖ) (a : I → R.obj.obj Y) :
    ((_root_.SheafOfModules.freeHomEquiv M).symm s).val.app Y
        (∑ k, a k • (_root_.SheafOfModules.freeSection (R := R) k).eval Y) =
      ∑ k, a k • (s k).eval Y := by
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  refine (((_root_.SheafOfModules.freeHomEquiv M).symm s).val.app Y).hom.map_smul _ _ |>.trans ?_
  exact congrArg (a k • ·) (congrArg (fun t : M.sections ↦ t.eval Y)
    (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s k))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The morphism `unit R ⟶ M` attached to a global section `s` sends a scalar `r` over `Y` to
`r • s`. -/
@[simp]
lemma unitHomEquiv_symm_val_app {M : _root_.SheafOfModules.{u} R} (s : M.sections) (Y : Cᵒᵖ)
    (r : R.obj.obj Y) :
    (M.unitHomEquiv.symm s).val.app Y r = r • s.eval Y :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The morphism `unit R ⟶ M` attached to a global section `s` is an isomorphism as soon as, over
every object `Y`, multiplying `s` by scalars is a bijection `R(Y) ⟶ M(Y)`: `s` is then a global
basis of `M`. -/
theorem isIso_unitHomEquiv_symm {M : _root_.SheafOfModules.{u} R} (s : M.sections)
    (hs : ∀ Y : Cᵒᵖ, Function.Bijective fun r : R.obj.obj Y ↦ r • s.eval Y) :
    IsIso (M.unitHomEquiv.symm s) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget _)]
  have (Y : Cᵒᵖ) : IsIso ((M.unitHomEquiv.symm s).val.app Y) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hs Y
  exact (_root_.PresheafOfModules.isoMk (fun Y ↦ asIso ((M.unitHomEquiv.symm s).val.app Y))
    fun _ _ f ↦ (M.unitHomEquiv.symm s).val.naturality f).isIso_hom

end Sections

end SheafOfModules

end


end TauCeti
