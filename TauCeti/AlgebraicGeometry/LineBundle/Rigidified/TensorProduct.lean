/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Dual
public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Basic

/-!
# The group of rigidified line bundles

Let `s : T ⟶ Y` be a morphism of schemes. The tensor product of two line bundles `L`, `K` on `Y`
rigidified along `s`, by `α : s^* L ≅ 𝒪_T` and `β : s^* K ≅ 𝒪_T`, is rigidified by
```
s^* (L ⊗ K) ≅ s^* L ⊗ s^* K ≅ 𝒪_T ⊗ 𝒪_T ≅ 𝒪_T,
```
using the tensor comparison of pullback, which is invertible because line bundles are
quasicoherent. The dual of `L` is rigidified so that the canonical isomorphism `L ⊗ L^∨ ≅ 𝒪_Y`
respects the rigidifications. On isomorphism classes this makes the classes of line bundles
rigidified along `s` a commutative group, with the canonically rigidified structure sheaf as
identity. Forgetting the rigidification is a group homomorphism to the Picard group of `Y`, and
pullback along a commutative square is a group homomorphism.

When `s` is the base change of a section of a morphism `X ⟶ S`, this is the group law of the
rigidified Picard functor.

## Main declarations

* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.tensorProduct`: the tensor product of two
  rigidified line bundles;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.dual`: the dual of a rigidified line bundle;
* `RigidifiedLineBundleClass.mk_tensorProduct_comm`,
  `RigidifiedLineBundleClass.mk_tensorProduct_assoc`,
  `RigidifiedLineBundleClass.mk_tensorProduct_trivial_left` and
  `RigidifiedLineBundleClass.mk_tensorProduct_dual`: the group laws up to isomorphism of
  rigidified line bundles;
* the `CommGroup` instance on `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass s`, with
  `RigidifiedLineBundleClass.mk_mul_mk`, `RigidifiedLineBundleClass.one_def` and
  `RigidifiedLineBundleClass.inv_mk`;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass.toLineBundleClassHom`: forgetting the
  rigidification, as a group homomorphism;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass.pullbackHom`: pullback along a commutative
  square, as a group homomorphism, from `RigidifiedLineBundleClass.mk_pullback_tensorProduct`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {T Y : Scheme.{u}} {s : T ⟶ Y}

namespace RigidifiedLineBundle

/-- The tensor product of two line bundles rigidified along `s`: the rigidification of `L ⊗ K` is
`s^* (L ⊗ K) ≅ s^* L ⊗ s^* K ≅ 𝒪_T ⊗ 𝒪_T ≅ 𝒪_T`. -/
-- Reducible, so that morphisms out of the line bundle of a tensor product typecheck against the
-- rigidification at reducible transparency, as `simp` and `rw` require.
abbrev tensorProduct (P Q : RigidifiedLineBundle s) : RigidifiedLineBundle s where
  lineBundle := InvertibleSheaf.tensorProduct P.lineBundle Q.lineBundle
  rigidification := (Scheme.Modules.pullback s).mapIso (InvertibleSheaf.tensorProductObjIso _ _) ≪≫
    asIso (δ (Scheme.Modules.pullback s) P.lineBundle.obj Q.lineBundle.obj) ≪≫
    (P.rigidification ⊗ᵢ Q.rigidification) ≪≫ λ_ (𝟙_ T.Modules)

/-- The line bundle of a tensor product of rigidified line bundles is the tensor product of their
line bundles. -/
@[simp]
lemma tensorProduct_lineBundle (P Q : RigidifiedLineBundle s) :
    (tensorProduct P Q).lineBundle = InvertibleSheaf.tensorProduct P.lineBundle Q.lineBundle :=
  (rfl)

/-- The dual of a line bundle rigidified along `s`, rigidified so that the canonical isomorphism
`L ⊗ L^∨ ≅ 𝒪_Y` respects the rigidifications: `s^* L^∨` is identified with
`𝒪_T ⊗ s^* L^∨ ≅ s^* L ⊗ s^* L^∨ ≅ s^* (L ⊗ L^∨) ≅ s^* 𝒪_Y ≅ 𝒪_T`. -/
-- Reducible for the same reason as `RigidifiedLineBundle.tensorProduct`.
abbrev dual (P : RigidifiedLineBundle s) : RigidifiedLineBundle s where
  lineBundle := InvertibleSheaf.dual P.lineBundle
  rigidification := (λ_ _).symm ≪≫ whiskerRightIso P.rigidification.symm _ ≪≫
    (asIso (δ (Scheme.Modules.pullback s) P.lineBundle.obj
      (InvertibleSheaf.dual P.lineBundle).obj)).symm ≪≫
    (Scheme.Modules.pullback s).mapIso
      ((InvertibleSheaf.tensorProductObjIso _ _).symm ≪≫
        InvertibleSheaf.tensorDualIsoSheaf P.lineBundle ≪≫ InvertibleSheaf.trivialObjIsoUnit Y) ≪≫
    Scheme.Modules.pullbackObjUnitIso s

/-- The line bundle of the dual of a rigidified line bundle is the dual line bundle. -/
@[simp]
lemma dual_lineBundle (P : RigidifiedLineBundle s) :
    (dual P).lineBundle = InvertibleSheaf.dual P.lineBundle :=
  (rfl)

end RigidifiedLineBundle

namespace RigidifiedLineBundleClass

open RigidifiedLineBundle

/-- Tensor product of rigidified line bundles respects isomorphism of rigidified line bundles. -/
lemma mk_tensorProduct_eq_mk_tensorProduct {P P' Q Q' : RigidifiedLineBundle s}
    (hP : mk P = mk P') (hQ : mk Q = mk Q') :
    mk (tensorProduct P Q) = mk (tensorProduct P' Q') := by
  obtain ⟨e, he⟩ := mk_eq_mk_iff.mp hP
  obtain ⟨e', he'⟩ := mk_eq_mk_iff.mp hQ
  refine mk_eq_mk_iff.mpr ⟨InvertibleSheaf.tensorProductObjIso _ _ ≪≫ (e ⊗ᵢ e') ≪≫
    (InvertibleSheaf.tensorProductObjIso _ _).symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom, asIso_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [← δ_natural_assoc, tensorHom_comp_tensorHom_assoc, he, he']

/-- Tensor product of rigidified line bundles is commutative up to isomorphism. -/
lemma mk_tensorProduct_comm (P Q : RigidifiedLineBundle s) :
    mk (tensorProduct P Q) = mk (tensorProduct Q P) := by
  refine mk_eq_mk_iff.mpr ⟨InvertibleSheaf.tensorProductObjIso _ _ ≪≫ β_ _ _ ≪≫
    (InvertibleSheaf.tensorProductObjIso _ _).symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom, asIso_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [Scheme.Modules.pullback_map_braiding_hom_comp_δ_assoc,
    ← BraidedCategory.braiding_naturality_assoc, braiding_tensorUnit_left, unitors_equal]
  simp

/-- Tensor product of rigidified line bundles is associative up to isomorphism. -/
lemma mk_tensorProduct_assoc (P Q R : RigidifiedLineBundle s) :
    mk (tensorProduct (tensorProduct P Q) R) = mk (tensorProduct P (tensorProduct Q R)) := by
  refine mk_eq_mk_iff.mpr ⟨InvertibleSheaf.tensorProductObjIso _ _ ≪≫
    whiskerRightIso (InvertibleSheaf.tensorProductObjIso _ _) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (InvertibleSheaf.tensorProductObjIso _ _).symm ≪≫
    (InvertibleSheaf.tensorProductObjIso _ _).symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom, asIso_hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc, whiskerRightIso_hom,
    whiskerLeftIso_hom]
  -- Move the identifications of the tensor products past the tensor comparisons of pullback,
  -- use the associativity of these comparisons, and conclude by monoidal coherence on `𝒪_T`.
  rw [← δ_natural_right_assoc, whiskerLeft_comp_tensorHom_assoc, Iso.inv_hom_id_map_assoc,
    ← whiskerRight_comp_tensorHom, Category.assoc, δ_natural_left_assoc,
    ← whiskerLeft_comp_tensorHom_assoc, ← whiskerRight_comp_tensorHom_assoc,
    ← associativity_assoc]
  monoidal

/-- The canonically rigidified trivial line bundle, with its line bundle written as the monoidal
unit, so that morphisms to and from it typecheck at reducible transparency. -/
private lemma trivial_eq : RigidifiedLineBundle.trivial s =
    ⟨⟨𝟙_ Y.Modules, (RigidifiedLineBundle.trivial s).lineBundle.property⟩,
      Scheme.Modules.pullbackObjUnitIso s⟩ :=
  rfl

/-- The canonically rigidified trivial line bundle is a unit for the tensor product of rigidified
line bundles, up to isomorphism. -/
lemma mk_tensorProduct_trivial_left (P : RigidifiedLineBundle s) :
    mk (tensorProduct (RigidifiedLineBundle.trivial s) P) = mk P := by
  rw [trivial_eq, mk_eq_mk_iff]
  refine ⟨InvertibleSheaf.tensorProductObjIso _ _ ≪≫ λ_ P.lineBundle.obj, ?_⟩
  simp only [Iso.trans_hom, tensorIso_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp,
    Category.assoc, ← Scheme.Modules.pullback_η]
  rw [δ_comp_η_tensorHom_assoc, ← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The tensor product of a rigidified line bundle with its dual is isomorphic to the canonically
rigidified trivial line bundle. -/
lemma mk_tensorProduct_dual (P : RigidifiedLineBundle s) :
    mk (tensorProduct P (dual P)) = mk (RigidifiedLineBundle.trivial s) := by
  rw [trivial_eq, mk_eq_mk_iff]
  refine ⟨InvertibleSheaf.tensorDualIsoSheaf P.lineBundle ≪≫ InvertibleSheaf.trivialObjIsoUnit Y,
    ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv,
    whiskerRightIso_hom, tensorIso_hom, Category.assoc, tensorHom_def]
  rw [leftUnitor_naturality]
  simp only [Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, IsIso.hom_inv_id_assoc,
    ← Functor.map_comp_assoc]

instance : Mul (RigidifiedLineBundleClass s) where
  mul a b := lift (fun P ↦ lift (fun Q ↦ mk (tensorProduct P Q))
      fun _ _ hQ ↦ mk_tensorProduct_eq_mk_tensorProduct rfl (mk_eq_mk_iff.mpr hQ))
    (fun _ _ hP ↦ funext fun b ↦ by
      obtain ⟨Q, rfl⟩ := mk_surjective b
      simp only [lift_mk]
      exact mk_tensorProduct_eq_mk_tensorProduct (mk_eq_mk_iff.mpr hP) rfl) a b

instance : One (RigidifiedLineBundleClass s) where
  one := mk (RigidifiedLineBundle.trivial s)

/-- The product of the classes of two rigidified line bundles is the class of their tensor
product. -/
@[simp]
lemma mk_mul_mk (P Q : RigidifiedLineBundle s) : mk P * mk Q = mk (tensorProduct P Q) :=
  (congrFun (lift_mk P) (mk Q)).trans (lift_mk Q)

/-- The identity class is the class of the canonically rigidified structure sheaf. -/
lemma one_def : (1 : RigidifiedLineBundleClass s) = mk (RigidifiedLineBundle.trivial s) :=
  (rfl)

instance : CommMonoid (RigidifiedLineBundleClass s) where
  mul_assoc a b c := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    obtain ⟨Q, rfl⟩ := mk_surjective b
    obtain ⟨R, rfl⟩ := mk_surjective c
    simp only [mk_mul_mk, mk_tensorProduct_assoc]
  one_mul a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    rw [one_def, mk_mul_mk, mk_tensorProduct_trivial_left]
  mul_one a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    rw [one_def, mk_mul_mk, mk_tensorProduct_comm, mk_tensorProduct_trivial_left]
  mul_comm a b := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    obtain ⟨Q, rfl⟩ := mk_surjective b
    rw [mk_mul_mk, mk_mul_mk, mk_tensorProduct_comm]

instance : CommGroup (RigidifiedLineBundleClass s) :=
  commGroupOfIsUnit fun a ↦ by
    obtain ⟨P, rfl⟩ := mk_surjective a
    exact isUnit_iff_exists_inv.mpr
      ⟨mk (dual P), by rw [mk_mul_mk, mk_tensorProduct_dual, one_def]⟩

/-- The inverse of the class of a rigidified line bundle is the class of its dual. -/
@[simp]
lemma inv_mk (P : RigidifiedLineBundle s) : (mk P)⁻¹ = mk (dual P) :=
  inv_eq_of_mul_eq_one_right (by rw [mk_mul_mk, mk_tensorProduct_dual, one_def])

/-- Forgetting the rigidification carries the product of classes to the product of line-bundle
classes. -/
@[simp]
lemma toLineBundleClass_mul (a b : RigidifiedLineBundleClass s) :
    toLineBundleClass (a * b) = toLineBundleClass a * toLineBundleClass b := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  obtain ⟨Q, rfl⟩ := mk_surjective b
  rw [mk_mul_mk, toLineBundleClass_mk, toLineBundleClass_mk, toLineBundleClass_mk,
    tensorProduct_lineBundle, LineBundleClass.mk_tensorProduct]

/-- Forgetting the rigidification carries the identity class to the identity line-bundle class. -/
@[simp]
lemma toLineBundleClass_one : toLineBundleClass (1 : RigidifiedLineBundleClass s) = 1 :=
  toLineBundleClass_trivial

/-- Forgetting the rigidification, as a homomorphism to the Picard group of `Y`. -/
-- Exposed so that homomorphisms built from it apply to a class by forgetting its rigidification.
@[expose]
def toLineBundleClassHom : RigidifiedLineBundleClass s →* LineBundleClass Y :=
  MonoidHom.mk' toLineBundleClass toLineBundleClass_mul

/-- The homomorphism `toLineBundleClassHom` forgets the rigidification. -/
@[simp]
lemma toLineBundleClassHom_apply (a : RigidifiedLineBundleClass s) :
    toLineBundleClassHom a = toLineBundleClass a :=
  (rfl)

variable {T' Y' : Scheme.{u}} {s' : T' ⟶ Y'} {h : Y' ⟶ Y} {g : T' ⟶ T}

/-- Pulling back the rigidification of a tensor product along a commutative square agrees with
the tensor product of the pulled-back rigidifications, through the tensor comparison of the
pullback along `h`. -/
private lemma pullbackRigidification_tensorProduct (w : s' ≫ h = g ≫ s)
    (P Q : RigidifiedLineBundle s) :
    (pullbackRigidification w _ (tensorProduct P Q).rigidification).hom =
      (Scheme.Modules.pullback s').map ((Scheme.Modules.pullback h).map
          (InvertibleSheaf.tensorProductObjIso P.lineBundle Q.lineBundle).hom ≫
        δ (Scheme.Modules.pullback h) P.lineBundle.obj Q.lineBundle.obj) ≫
        δ (Scheme.Modules.pullback s') _ _ ≫
        ((pullbackRigidification w _ P.rigidification).hom ⊗ₘ
          (pullbackRigidification w _ Q.rigidification).hom) ≫ (λ_ (𝟙_ T'.Modules)).hom := by
  -- Expand both sides, then move the tensor comparisons of the pullbacks along `s'`, `h`, `g`
  -- and `s` past the composition isomorphisms `(s' ≫ h)^* ≅ s'^* h^*`, `(g ≫ s)^* ≅ g^* s^*` and
  -- the identification `(s' ≫ h)^* ≅ (g ≫ s)^*`, and finally past the unit of `g^*`.
  simp only [pullbackRigidification_hom, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    tensorIso_hom, Functor.map_comp, Category.assoc]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [← pullbackComp_hom_app_comp_δ_assoc, ← Scheme.Modules.pullbackCongr_hom_app_comp_δ_assoc,
    Scheme.Modules.pullback_comp_δ g s]
  simp only [Category.assoc]
  -- The composition isomorphisms of pullback along `g ≫ s` cancel on both tensor factors.
  have hc {Z : T'.Modules} (k : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj
      P.lineBundle.obj) ⊗ (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj
        Q.lineBundle.obj) ⟶ Z) :
      ((Scheme.Modules.pullbackComp g s).hom.app P.lineBundle.obj ⊗ₘ
          (Scheme.Modules.pullbackComp g s).hom.app Q.lineBundle.obj) ≫
        ((Scheme.Modules.pullbackComp g s).inv.app P.lineBundle.obj ⊗ₘ
          (Scheme.Modules.pullbackComp g s).inv.app Q.lineBundle.obj) ≫ k = k := by
    rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      id_tensorHom_id, Category.id_comp]
  rw [hc, δ_natural_assoc, ← Scheme.Modules.pullback_η, δ_comp_η_tensorHom_assoc,
    leftUnitor_naturality, Iso.inv_hom_id_assoc]
  have h₁ := (Scheme.Modules.pullbackComp s' h).hom.naturality
    (InvertibleSheaf.tensorProductObjIso P.lineBundle Q.lineBundle).hom
  have h₂ := (Scheme.Modules.pullbackCongr w).hom.naturality
    (InvertibleSheaf.tensorProductObjIso P.lineBundle Q.lineBundle).hom
  have h₃ := (Scheme.Modules.pullbackComp g s).inv.naturality
    (InvertibleSheaf.tensorProductObjIso P.lineBundle Q.lineBundle).hom
  simp only [Functor.comp_map] at h₁ h₃
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]

/-- Pullback along a commutative square carries the tensor product of two rigidified line bundles
to the tensor product of their pullbacks, up to isomorphism. -/
lemma mk_pullback_tensorProduct (w : s' ≫ h = g ≫ s) (P Q : RigidifiedLineBundle s) :
    mk (RigidifiedLineBundle.pullback w (tensorProduct P Q)) =
      mk (tensorProduct (RigidifiedLineBundle.pullback w P)
        (RigidifiedLineBundle.pullback w Q)) := by
  refine mk_eq_mk_iff.mpr ⟨((Scheme.Modules.pullback h).mapIso
      (InvertibleSheaf.tensorProductObjIso P.lineBundle Q.lineBundle) ≪≫
    asIso (δ (Scheme.Modules.pullback h) P.lineBundle.obj Q.lineBundle.obj)) ≪≫
    (InvertibleSheaf.tensorProductObjIso ((InvertibleSheaf.pullback h).obj P.lineBundle)
      ((InvertibleSheaf.pullback h).obj Q.lineBundle)).symm, ?_⟩
  rw [RigidifiedLineBundle.pullback_rigidification, pullbackRigidification_tensorProduct]
  -- The line bundles of the pulled-back rigidified line bundles are the pulled-back line bundles
  -- only after unfolding `RigidifiedLineBundle.pullback`, which `simp` does not do. So the
  -- identification of the tensor product with the monoidal one is cancelled by a lemma applied up
  -- to that unfolding, and the two sides then agree after unfolding the composite isomorphisms and
  -- the pulled-back rigidifications (`RigidifiedLineBundle.pullback_rigidification`).
  have hcancel {A B C : Y'.Modules} {Z : T'.Modules} (e : A ≅ B) (i : C ≅ B)
      (R : (Scheme.Modules.pullback s').obj B ⟶ Z) :
      (Scheme.Modules.pullback s').map (e ≪≫ i.symm).hom ≫
        (Scheme.Modules.pullback s').map i.hom ≫ R =
          (Scheme.Modules.pullback s').map e.hom ≫ R := by
    simp
  exact (hcancel _ _ _).trans rfl

/-- Pullback of classes of rigidified line bundles along a commutative square is compatible with
products. -/
@[simp]
lemma pullback_mul (w : s' ≫ h = g ≫ s) (a b : RigidifiedLineBundleClass s) :
    pullback w (a * b) = pullback w a * pullback w b := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  obtain ⟨Q, rfl⟩ := mk_surjective b
  rw [mk_mul_mk, pullback_mk, pullback_mk, pullback_mk, mk_mul_mk, mk_pullback_tensorProduct]

/-- Pullback of classes of rigidified line bundles along a commutative square, as a group
homomorphism. -/
-- Exposed so that a functor whose action is `pullbackHom` acts definitionally by pullback.
@[expose]
def pullbackHom (w : s' ≫ h = g ≫ s) :
    RigidifiedLineBundleClass s →* RigidifiedLineBundleClass s' :=
  MonoidHom.mk' (pullback w) (pullback_mul w)

/-- The homomorphism `pullbackHom w` is pullback of classes. -/
@[simp]
lemma pullbackHom_apply (w : s' ≫ h = g ≫ s) (a : RigidifiedLineBundleClass s) :
    pullbackHom w a = pullback w a :=
  (rfl)

end RigidifiedLineBundleClass

end

end AlgebraicGeometry

end TauCeti
