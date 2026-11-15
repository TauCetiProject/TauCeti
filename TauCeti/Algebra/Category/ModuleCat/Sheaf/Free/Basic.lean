/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-!
# Free sheaves on finitely many generators

This file records basic properties of free sheaves of modules. It gives the canonical
identification between the free sheaf on one generator and the tensor unit, shows that the free
sheaf on no generators is a zero object, and identifies the sections of a finite free sheaf with
tuples of sections of the coefficient sheaf.

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
* `TauCeti.SheafOfModules.biproductIsoFree`: a finite free sheaf is the biproduct of copies of
  the unit;
* `TauCeti.SheafOfModules.evaluationFreeIso`: the sections of a finite free sheaf are tuples of
  sections of the coefficient sheaf;
* `TauCeti.SheafOfModules.freeBasis`: the corresponding basis of sections, consisting of the
  tautological sections `freeSection i`;
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

open CategoryTheory Limits MonoidalCategory

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

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {R : Sheaf J CommRingCat.{u}} (I : Type u) [Finite I]

/-- The free sheaf of modules on a finite type `I` is the biproduct of `I` copies of the unit. -/
def biproductIsoFree :
    ⨁ (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅ free (R := ringCatSheaf R) I :=
  (biproduct.isColimit _).coconePointUniqueUpToIso (isColimitFreeCofan I)

variable {I}

/-- `biproductIsoFree` sends the `i`-th summand to the `i`-th basis section. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biproductIsoFree_hom (i : I) :
    biproduct.ι (fun _ : I ↦ unit (ringCatSheaf R)) i ≫
      (biproductIsoFree (R := R) I).hom = ιFree i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitFreeCofan I) ⟨i⟩

/-- The inverse of `biproductIsoFree` sends the `i`-th basis section to the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem ιFree_biproductIsoFree_inv (i : I) :
    ιFree i ≫ (biproductIsoFree (R := R) I).inv =
      biproduct.ι (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimitFreeCofan I) ⟨i⟩

variable (I)

/-- The sections over `W` of the free sheaf of modules on a finite type `I` are the `I`-indexed
tuples of sections of the sheaf of rings over `W`: `free I` is the product of `I` copies of the
unit, and evaluation at `W` preserves products. -/
def evaluationFreeIso (W : Cᵒᵖ) :
    (evaluation (ringCatSheaf R) W).obj (free I) ≅
      ModuleCat.of ((ringCatSheaf R).obj.obj W) (I → (ringCatSheaf R).obj.obj W) :=
  (evaluation (ringCatSheaf R) W).mapIso
      ((biproductIsoFree (R := R) I).symm ≪≫ biproduct.isoProduct _) ≪≫
    PreservesProduct.iso (evaluation (ringCatSheaf R) W) _ ≪≫ ModuleCat.piIsoPi _

/-- The `i`-th coordinate of a section of `free I` under `evaluationFreeIso` is its image under
the `i`-th projection `free I ⟶ R` of the biproduct decomposition of `free I`. -/
@[reassoc (attr := simp)]
theorem evaluationFreeIso_hom_comp_proj (W : Cᵒᵖ) (i : I) :
    (evaluationFreeIso (R := R) I W).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (evaluation (ringCatSheaf R) W).map
        ((biproductIsoFree (R := R) I).inv ≫ biproduct.π _ i) := by
  -- The last factor of `evaluationFreeIso` lands in the module of `I`-tuples of sections of the
  -- unit over `W`, which is the module of `I`-tuples of sections of `R` only after unfolding
  -- `evaluation`; the composite is therefore spelled out in the former form before simplifying.
  change ((evaluation (ringCatSheaf R) W).map
      ((biproductIsoFree (R := R) I).inv ≫ (biproduct.isoProduct _).hom) ≫
    (PreservesProduct.iso (evaluation (ringCatSheaf R) W) _).hom ≫
    (ModuleCat.piIsoPi fun _ : I ↦ (evaluation (ringCatSheaf R) W).obj (𝟙_ _)).hom) ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
  simp

/-- The basis of the sections over `W` of the free sheaf of modules on a finite type `I`, obtained
from the standard basis of `I`-tuples through `evaluationFreeIso`. Its `i`-th member is the basis
section `freeSection i` over `W` (`freeBasis_apply`). -/
def freeBasis (W : Cᵒᵖ) :
    Module.Basis I (R.obj.obj W)
      (PresheafOfModulesOfCommRing.obj (R := R.obj) (free (R := ringCatSheaf R) I).val W) :=
  (Pi.basisFun _ I).map (evaluationFreeIso (R := R) I W).toLinearEquiv.symm

/-- The `i`-th member of `freeBasis I W` is the basis section `freeSection i` over `W`. -/
@[simp]
theorem freeBasis_apply (W : Cᵒᵖ) (i : I) :
    freeBasis (R := R) I W i = (freeSection (R := ringCatSheaf R) i).eval W := by
  classical
  refine (Module.Basis.map_apply _ _ _).trans ((LinearEquiv.symm_apply_eq _).2 ?_)
  funext j
  -- The `j`-th coordinate is computed by `evaluationFreeIso_hom_comp_proj`, and
  -- `freeSection i` over `W` is the image of `1` under `ιFree i`.
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (evaluationFreeIso_hom_comp_proj (R := R) I W j)
    ((ιFree (R := ringCatSheaf R) i).val.app W (1 : R.obj.obj W))).symm
  have h := ιFree_biproductIsoFree_inv_assoc (R := R) i (biproduct.π _ j)
  rw [biproduct.ι_π] at h
  -- `rw` cannot apply `h` to the goal: the coefficient ring is `(ringCatSheaf R).obj.obj W` on
  -- one side and `R.obj.obj W` on the other, which agree only after unfolding `ringCatSheaf`.
  refine Eq.trans ?_ (congrArg (fun g ↦ (g.val.app W) (1 : R.obj.obj W)) h).symm
  split_ifs with hij
  · subst hij
    simp
    -- the identity morphism of sheaves of modules is the identity on sections
    rfl
  · simp [Ne.symm hij]
    -- the zero morphism of sheaves of modules is zero on sections
    rfl

/-- The restriction maps of a finite free sheaf preserve the members of `freeBasis`. -/
theorem freeBasis_map {W W' : Cᵒᵖ} (f : W ⟶ W') (i : I) :
    (free (R := ringCatSheaf R) I).val.map f (freeBasis (R := R) I W i) =
      freeBasis (R := R) I W' i := by
  rw [freeBasis_apply, freeBasis_apply]
  exact PresheafOfModules.sections_property _ f

end SheafOfModules

end


end TauCeti
