/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Hom
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Mon
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Base change of abelian schemes

Pulling back an abelian scheme `A` over `S` along a morphism of base schemes `f : T ⟶ S` yields
an abelian scheme `A.baseChange f` over `T`: properness, smoothness, and geometric connectedness
are stable under base change, and the cartesian monoidal functor `Over.pullback f` transports the
group-object structure.

This file defines:

* `AbelianScheme.baseChange`, `AbelianScheme.Hom.baseChange`, and
  `AbelianScheme.baseChangeFunctor`: the base-change functor `AbelianScheme S ⥤ AbelianScheme T`;
* `AbelianScheme.baseChangeIdIso`, `AbelianScheme.baseChangeCompIso`, and
  `AbelianScheme.baseChangeIdentityIso`: canonical isomorphisms for identity base change, iterated
  base change, and base change of `AbelianScheme.identity`;
* `AbelianScheme.baseChangePointMulEquiv`: the multiplicative equivalence between `U`-points of
  `A.baseChange f` and `((Over.map f).obj U)`-points of `A`, with naturality in `U` and in
  homomorphisms of abelian schemes, and compatibility with identity and iterated base change.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T U : Scheme.{u}}

noncomputable section

/-- The base change of an abelian scheme `A` over `S` along a morphism of schemes `f : T ⟶ S`,
obtained by pulling back the group scheme along `f`. -/
def baseChange (A : AbelianScheme S) (f : T ⟶ S) : AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs (IsProper (Limits.pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (Limits.pullback.snd A.toOver.hom f))
  geometricallyConnected :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd A.toOver.hom f))

@[simp]
lemma baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toOver = (Over.pullback f).obj A.toOver :=
  (rfl)

@[simp]
lemma baseChange_toScheme (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toScheme = Limits.pullback A.toOver.hom f := by
  simp only [toScheme, baseChange_toOver, Over.pullback_obj_left]

/-- Bundling the underlying `Over T` object of a base change with `Grp.mk` gives the group object
obtained by applying `(Over.pullback f).mapGrp`. -/
lemma grpMk_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    Grp.mk (A.baseChange f).toOver = (Over.pullback f).mapGrp.obj (Grp.mk A.toOver) := by
  unfold baseChange
  rfl

/-- The unit of a base-changed abelian scheme is the pullback of the original unit. -/
@[simp]
lemma baseChange_one (A : AbelianScheme S) (f : T ⟶ S) :
    η[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A.toOver] :=
  Category.comp_id _

/-- The multiplication of a base-changed abelian scheme is the pullback of the original
multiplication. -/
@[simp]
lemma baseChange_mul (A : AbelianScheme S) (f : T ⟶ S) :
    μ[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      (eqToHom (baseChange_toOver A f) ⊗ₘ eqToHom (baseChange_toOver A f)) ≫
        Functor.LaxMonoidal.μ (Over.pullback f) A.toOver A.toOver ≫
        (Over.pullback f).map μ[A.toOver] :=
  (Category.comp_id μ[(A.baseChange f).toOver]).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _).symm))

/-- The inversion of a base-changed abelian scheme is the pullback of the original inversion. -/
@[simp]
lemma baseChange_inv (A : AbelianScheme S) (f : T ⟶ S) :
    ι[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      eqToHom (baseChange_toOver A f) ≫ (Over.pullback f).map ι[A.toOver] :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The transport isomorphism identifying `(A.baseChange f).toOver` with
`(Over.pullback f).obj A.toOver` is a homomorphism of monoid objects. -/
instance isMonHom_eqToHom_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    IsMonHom (eqToHom (baseChange_toOver A f)) where
  one_hom := by rw [baseChange_one, Functor.obj.η_def]
  mul_hom := by rw [baseChange_mul, Functor.obj.μ_def]

/-- The inverse transport isomorphism for `baseChange_toOver` is a homomorphism of monoid
objects. -/
instance isMonHom_eqToHom_baseChange_toOver_symm (A : AbelianScheme S) (f : T ⟶ S) :
    IsMonHom (eqToHom (baseChange_toOver A f).symm) :=
  haveI : IsMonHom (eqToIso (baseChange_toOver A f)).hom :=
    isMonHom_eqToHom_baseChange_toOver A f
  inferInstanceAs (IsMonHom (eqToIso (baseChange_toOver A f)).inv)

/-- Base change of a homomorphism of abelian schemes along a base morphism `f : T ⟶ S`. -/
def Hom.baseChange {A B : AbelianScheme S} (φ : A ⟶ B) (f : T ⟶ S) :
    A.baseChange f ⟶ B.baseChange f :=
  InducedCategory.homMk
    (eqToHom (grpMk_baseChange_toOver A f) ≫ (Over.pullback f).mapGrp.map φ.hom ≫
      eqToHom (grpMk_baseChange_toOver B f).symm)

@[simp]
lemma Hom.toOverHom_baseChange {A B : AbelianScheme S} (φ : A ⟶ B) (f : T ⟶ S) :
    Hom.toOverHom (Hom.baseChange φ f) =
      eqToHom (baseChange_toOver A f) ≫ (Over.pullback f).map (Hom.toOverHom φ) ≫
        eqToHom (baseChange_toOver B f).symm := by
  -- Exposes the morphism passed to `InducedCategory.homMk` under `Grp.forget`.
  change (Grp.forget _).map
      (eqToHom (grpMk_baseChange_toOver A f) ≫ (Over.pullback f).mapGrp.map φ.hom ≫
        eqToHom (grpMk_baseChange_toOver B f).symm) = _
  simp only [Functor.map_comp, eqToHom_map]
  rfl

@[simp]
lemma Hom.toSchemeHom_baseChange {A B : AbelianScheme S} (φ : A ⟶ B) (f : T ⟶ S) :
    Hom.toSchemeHom (Hom.baseChange φ f) =
      (eqToHom (baseChange_toOver A f) ≫ (Over.pullback f).map (Hom.toOverHom φ) ≫
        eqToHom (baseChange_toOver B f).symm).left :=
  congrArg Over.Hom.left (Hom.toOverHom_baseChange φ f)

@[simp]
lemma Hom.baseChange_id (A : AbelianScheme S) (f : T ⟶ S) :
    Hom.baseChange (𝟙 A) f = 𝟙 (A.baseChange f) :=
  Hom.toOverHom_injective (by
    rw [Hom.toOverHom_baseChange, Hom.toOverHom_id, Hom.toOverHom_id]; simp)

@[simp]
lemma Hom.baseChange_comp {A B C : AbelianScheme S} (φ : A ⟶ B) (ψ : B ⟶ C) (f : T ⟶ S) :
    Hom.baseChange (φ ≫ ψ) f = Hom.baseChange φ f ≫ Hom.baseChange ψ f :=
  Hom.toOverHom_injective (by
    rw [Hom.toOverHom_baseChange, Hom.toOverHom_comp, Hom.toOverHom_comp,
      Hom.toOverHom_baseChange, Hom.toOverHom_baseChange]; simp)

/-- Base change along `f : T ⟶ S`, as a functor `AbelianScheme S ⥤ AbelianScheme T`. -/
def baseChangeFunctor (f : T ⟶ S) : AbelianScheme S ⥤ AbelianScheme T where
  obj A := A.baseChange f
  map φ := Hom.baseChange φ f
  map_id A := Hom.baseChange_id A f
  map_comp φ ψ := Hom.baseChange_comp φ ψ f

@[simp]
lemma baseChangeFunctor_obj (f : T ⟶ S) (A : AbelianScheme S) :
    (baseChangeFunctor f).obj A = A.baseChange f :=
  (rfl)

@[simp]
lemma baseChangeFunctor_map {A B : AbelianScheme S} (f : T ⟶ S) (φ : A ⟶ B) :
    (baseChangeFunctor f).map φ =
      eqToHom (baseChangeFunctor_obj f A) ≫ Hom.baseChange φ f ≫
        eqToHom (baseChangeFunctor_obj f B).symm :=
  (rfl)

/-! ### Points of a base-changed abelian scheme -/

/-- Points of a base-changed abelian scheme `A.baseChange f` over a test scheme `V : Over T` are
canonically isomorphic, as a group, to `((Over.map f).obj V)`-points of `A`. -/
def baseChangePointMulEquiv (A : AbelianScheme S) (f : T ⟶ S) (V : Over T) :
    (V ⟶ (A.baseChange f).toOver) ≃* ((Over.map f).obj V ⟶ A.toOver) :=
  let : IsMonHom (eqToIso (baseChange_toOver A f)).hom :=
    isMonHom_eqToHom_baseChange_toOver A f
  (CategoryTheory.Hom.mulEquivCongrRight (eqToIso (baseChange_toOver A f)) V).trans
    (GroupScheme.baseChangePointMulEquiv f (Grp.mk A.toOver) V)

lemma baseChangePointMulEquiv_apply (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv A f V p =
      ((Over.mapPullbackAdj f).homEquiv V A.toOver).symm (p ≫ eqToHom (baseChange_toOver A f)) := by
  -- Opens `MulEquiv.trans` and `Hom.mulEquivCongrRight` once; later proofs rewrite by this lemma.
  change GroupScheme.baseChangePointMulEquiv f (Grp.mk A.toOver) V
    (p ≫ eqToHom (baseChange_toOver A f)) = _
  exact GroupScheme.baseChangePointMulEquiv_apply f (Grp.mk A.toOver) V _

@[simp]
lemma baseChangePointMulEquiv_symm_apply (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : (Over.map f).obj V ⟶ A.toOver) :
    (baseChangePointMulEquiv A f V).symm p =
      (Over.mapPullbackAdj f).homEquiv V A.toOver p ≫ eqToHom (baseChange_toOver A f).symm := by
  apply (baseChangePointMulEquiv A f V).injective
  rw [MulEquiv.apply_symm_apply, baseChangePointMulEquiv_apply]
  simp

/-- The underlying scheme morphism of the point comparison is postcomposition with the first
pullback projection. -/
@[simp]
lemma baseChangePointMulEquiv_apply_left (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : V ⟶ (A.baseChange f).toOver) :
    (baseChangePointMulEquiv A f V p).left =
      (p ≫ eqToHom (baseChange_toOver A f)).left ≫ Limits.pullback.fst A.toOver.hom f := by
  rw [baseChangePointMulEquiv_apply]
  rfl

/-- The underlying scheme morphism of the inverse point comparison is the pullback lift with
second component `V.hom`. -/
lemma baseChangePointMulEquiv_symm_apply_left (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : (Over.map f).obj V ⟶ A.toOver) :
    ((baseChangePointMulEquiv A f V).symm p ≫ eqToHom (baseChange_toOver A f)).left =
      Limits.pullback.lift p.left V.hom (by simp) := by
  rw [baseChangePointMulEquiv_symm_apply, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, ← GroupScheme.baseChangePointMulEquiv_symm_apply f (Grp.mk A.toOver) V p]
  exact GroupScheme.baseChangePointMulEquiv_symm_apply_left f (Grp.mk A.toOver) V p

/-- The point comparison commutes with restriction along morphisms of test schemes. -/
lemma baseChangePointMulEquiv_naturality_left (A : AbelianScheme S) (f : T ⟶ S)
    {V W : Over T} (h : W ⟶ V) (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv A f W (h ≫ p) =
      (Over.map f).map h ≫ baseChangePointMulEquiv A f V p := by
  rw [baseChangePointMulEquiv_apply, baseChangePointMulEquiv_apply, Category.assoc]
  exact (Over.mapPullbackAdj f).homEquiv_naturality_left_symm h
    (p ≫ eqToHom (baseChange_toOver A f))

/-- The point comparison commutes with homomorphisms of abelian schemes. -/
lemma baseChangePointMulEquiv_naturality_right {A B : AbelianScheme S} (φ : A ⟶ B) (f : T ⟶ S)
    (V : Over T) (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv B f V (p ≫ Hom.toOverHom (Hom.baseChange φ f)) =
      baseChangePointMulEquiv A f V p ≫ Hom.toOverHom φ := by
  rw [baseChangePointMulEquiv_apply B f V, baseChangePointMulEquiv_apply A f V,
    Hom.toOverHom_baseChange]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simpa only [Category.assoc] using
    (Over.mapPullbackAdj f).homEquiv_naturality_right_symm
      (p ≫ eqToHom (baseChange_toOver A f)) (Hom.toOverHom φ)

/-! ### Identity, composition, and trivial base-change isomorphisms -/

/-- Base change along the identity morphism is canonically isomorphic to the original abelian
scheme. -/
def baseChangeIdIso (A : AbelianScheme S) : A.baseChange (𝟙 S) ≅ A :=
  let e : (A.baseChange (𝟙 S)).toOver ≅ A.toOver :=
    (eqToIso (baseChange_toOver A (𝟙 S))).trans ((Over.pullbackId (X := S)).app A.toOver)
  have : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (eqToHom (baseChange_toOver A (𝟙 S)) ≫
      (Over.pullbackId (X := S)).hom.app A.toOver))
  isoMk e

@[simp]
lemma toOverHom_baseChangeIdIso_hom (A : AbelianScheme S) :
    Hom.toOverHom (baseChangeIdIso A).hom =
      eqToHom (baseChange_toOver A (𝟙 S)) ≫ (Over.pullbackId (X := S)).hom.app A.toOver := by
  simp [baseChangeIdIso]

/-- For identity base change, the point comparison agrees with `baseChangeIdIso`. -/
lemma baseChangePointMulEquiv_id (A : AbelianScheme S) (V : Over S)
    (p : V ⟶ (A.baseChange (𝟙 S)).toOver) :
    (Over.mapId S).inv.app V ≫ baseChangePointMulEquiv A (𝟙 S) V p =
      p ≫ Hom.toOverHom (baseChangeIdIso A).hom := by
  have h := GroupScheme.baseChangePointMulEquiv_id (Grp.mk A.toOver) V
    (p ≫ eqToHom (baseChange_toOver A (𝟙 S)))
  rw [GroupScheme.baseChangePointMulEquiv_apply] at h
  rw [baseChangePointMulEquiv_apply, toOverHom_baseChangeIdIso_hom, ← Category.assoc]
  exact h

/-- The underlying `Over U` isomorphism comparing base change along `g ≫ f` with iterated base
change. -/
private def baseChangeCompOverIso (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    (A.baseChange (g ≫ f)).toOver ≅ ((A.baseChange f).baseChange g).toOver :=
  (eqToIso (baseChange_toOver A (g ≫ f))).trans
    (((Over.pullbackComp g f).app A.toOver).trans
      (((Over.pullback g).mapIso (eqToIso (baseChange_toOver A f)).symm).trans
        (eqToIso (baseChange_toOver (A.baseChange f) g)).symm))

/-- Pointwise compatibility of `baseChangeCompOverIso` with `baseChangePointMulEquiv`. -/
private lemma baseChangePointMulEquiv_comp_over (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S)
    (V : Over U) (p : V ⟶ (A.baseChange (g ≫ f)).toOver) :
    baseChangePointMulEquiv A f ((Over.map g).obj V)
        (baseChangePointMulEquiv (A.baseChange f) g V
          (p ≫ (baseChangeCompOverIso A g f).hom)) =
      (Over.mapComp g f).inv.app V ≫ baseChangePointMulEquiv A (g ≫ f) V p := by
  rw [baseChangePointMulEquiv_apply A f, baseChangePointMulEquiv_apply (A.baseChange f) g,
    baseChangePointMulEquiv_apply A (g ≫ f)]
  simp only [baseChangeCompOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  have hnat := (Over.mapPullbackAdj g).homEquiv_naturality_right_symm
    (p ≫ eqToHom (baseChange_toOver A (g ≫ f)) ≫ (Over.pullbackComp g f).hom.app A.toOver)
    (eqToHom (baseChange_toOver A f).symm)
  simp only [Category.assoc] at hnat
  rw [hnat, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, ← Category.assoc p]
  have hcomp := GroupScheme.baseChangePointMulEquiv_comp g f (Grp.mk A.toOver) V
    (p ≫ eqToHom (baseChange_toOver A (g ≫ f)))
  rw [GroupScheme.baseChangePointMulEquiv_apply, GroupScheme.baseChangePointMulEquiv_apply,
    GroupScheme.baseChangePointMulEquiv_apply] at hcomp
  exact hcomp

/-- Base change along a composite `g ≫ f` is canonically isomorphic to iterated base change. -/
def baseChangeCompIso (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    A.baseChange (g ≫ f) ≅ (A.baseChange f).baseChange g :=
  have : IsMonHom (baseChangeCompOverIso A g f).hom := by
    rw [GrpObj.isMonHom_iff_mul_comp]
    intro V x y
    apply (baseChangePointMulEquiv (A.baseChange f) g V).injective
    apply (baseChangePointMulEquiv A f ((Over.map g).obj V)).injective
    rw [baseChangePointMulEquiv_comp_over, map_mul, MonObj.comp_mul,
      ← baseChangePointMulEquiv_comp_over, ← baseChangePointMulEquiv_comp_over,
      ← map_mul, ← map_mul]
  isoMk (baseChangeCompOverIso A g f)

@[simp]
lemma toOverHom_baseChangeCompIso_hom (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    Hom.toOverHom (baseChangeCompIso A g f).hom =
      eqToHom (baseChange_toOver A (g ≫ f)) ≫
        (Over.pullbackComp g f).hom.app A.toOver ≫
        (Over.pullback g).map (eqToHom (baseChange_toOver A f).symm) ≫
        eqToHom (baseChange_toOver (A.baseChange f) g).symm := by
  simp [baseChangeCompIso, baseChangeCompOverIso]

/-- For iterated base change along `g ≫ f`, the point comparison agrees with `baseChangeCompIso`. -/
lemma baseChangePointMulEquiv_comp (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) (V : Over U)
    (p : V ⟶ (A.baseChange (g ≫ f)).toOver) :
    baseChangePointMulEquiv A f ((Over.map g).obj V)
        (baseChangePointMulEquiv (A.baseChange f) g V
          (p ≫ Hom.toOverHom (baseChangeCompIso A g f).hom)) =
      (Over.mapComp g f).inv.app V ≫ baseChangePointMulEquiv A (g ≫ f) V p := by
  simpa [baseChangeCompIso] using baseChangePointMulEquiv_comp_over A g f V p

/-- The base change of `identity S` along `f : T ⟶ S` is terminal in `AbelianScheme T`. -/
def isTerminalBaseChangeIdentity (f : T ⟶ S) : IsTerminal ((identity S).baseChange f) :=
  let hterm : IsTerminal ((identity S).baseChange f).toOver :=
    IsTerminal.ofIso ((isTerminalIdentityToOver S).isTerminalObj (Over.pullback f))
      (eqToIso (baseChange_toOver (identity S) f).symm)
  IsTerminal.ofUniqueHom
    (fun B ↦ Hom.mk' (hterm.from B.toOver) (hterm.hom_ext _ _) (hterm.hom_ext _ _))
    fun _ _ ↦ Hom.ext (congrArg Over.Hom.left (hterm.hom_ext _ _))

/-- Base change carries the identity abelian scheme over `S` to the identity abelian scheme over
`T`. -/
def baseChangeIdentityIso (f : T ⟶ S) : (identity S).baseChange f ≅ identity T :=
  (isTerminalBaseChangeIdentity f).uniqueUpToIso (isTerminalIdentity T)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
