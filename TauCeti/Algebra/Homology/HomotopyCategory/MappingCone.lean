/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Basic

/-!
# Mapping cones and homotopy equivalences

The standard null-homotopy of `f ≫ mappingCone.inr f` has components given by
`mappingCone.inl f`. This file exposes that homotopy and the component formulas relating
Mathlib's mapping-cone API to its underlying homotopy-cofiber construction.

A morphism of cochain complexes `f : K ⟶ L` sits in the distinguished triangle
`K ⟶ L ⟶ cone f ⟶ K⟦1⟧` of the homotopy category. In a pretriangulated category the third
object of a distinguished triangle is zero exactly when its first morphism is an isomorphism, so
the mapping cone of `f` is zero in the homotopy category as soon as `f` becomes an isomorphism
there, in particular when `f` is a homotopy equivalence. Being zero in the homotopy category means
that the identity is null-homotopic, which is the form in which this file records the statement.

## Main results

* `CochainComplex.mappingCone.inrCompHomotopy`: the standard null-homotopy of the composite of
  `f` with the right inclusion into its mapping cone.
* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_isIso_quotient_map`: the mapping cone
  of a morphism inverted by the homotopy category is contractible.
* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_homotopyEquiv`: the mapping cone of a
  homotopy equivalence is contractible.

## Mapping cones of natural transformations and shifts

Mathlib's `CochainComplex.mappingCone.shiftIso φ n : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧')`
multiplies the first component by `(-1)^n`. This file proves that it is natural in commutative
squares and compatible with the isomorphisms `shiftFunctorZero` and `shiftFunctorAdd`. For a
natural transformation `τ : F ⟶ G` of functors `D ⥤ CochainComplex C ℤ`, the mapping cones
`X ↦ mappingCone (τ.app X)` form a functor `TauCeti.mappingConeFunctor τ`. When `F`, `G` and
`τ` commute with the shifts of `D` and of cochain complexes, so does this functor: its
commutation isomorphism at `X` is the map of mapping cones induced by those of `F` and `G`,
followed by the inverse of `shiftIso`. For instance, the homotopy limit `Cone(δ)[-1]` of a
complex of towers of modules is built from such a functor.

* `CochainComplex.mappingCone.shiftIso_hom_naturality`,
  `CochainComplex.mappingCone.shiftFunctorZero_inv_app_shiftIso_hom` and
  `CochainComplex.mappingCone.shiftFunctorAdd_inv_app_shiftIso_hom`: naturality and coherence
  of `shiftIso`.
* `CochainComplex.mappingCone.mapIso`: the isomorphism of mapping cones induced by an
  isomorphism of arrows.
* `TauCeti.mappingConeFunctor`: the mapping cone of a natural transformation, as a functor, which
  commutes with the shifts when `τ` does.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- The components of `mappingCone.inl` are the left inclusions of the underlying homotopy
cofiber. -/
lemma inl_v_eq_inlX (i j : ℤ) (hij : j + 1 = i) :
    (inl f).v i j (by omega) = homotopyCofiber.inlX f i j hij :=
  rfl

/-- The standard null-homotopy of `f ≫ mappingCone.inr f`, whose components are those of
`mappingCone.inl f`. -/
noncomputable def inrCompHomotopy : Homotopy (f ≫ inr f) 0 :=
  homotopyCofiber.inrCompHomotopy f fun j ↦ ⟨j - 1, by simp⟩

/-- The components of the standard null-homotopy of `f ≫ mappingCone.inr f`. -/
lemma inrCompHomotopy_hom (i j : ℤ) (hij : j + 1 = i) :
    (inrCompHomotopy f).hom i j = (inl f).v i j (by omega) := by
  rw [inl_v_eq_inlX f i j hij]
  exact homotopyCofiber.inrCompHomotopy_hom f _ i j hij

section

variable [HasZeroObject C]

/-- The mapping cone of a morphism which becomes an isomorphism in the homotopy category is
contractible. -/
theorem nonempty_homotopy_id_zero_of_isIso_quotient_map
    [IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)] :
    Nonempty (Homotopy (𝟙 (mappingCone f)) 0) :=
  (HomotopyCategory.isZero_quotient_obj_iff _).1
    (Triangle.isZero₃_of_isIso₁ _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (inferInstanceAs (IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f))))

/-- The mapping cone of a homotopy equivalence is contractible. -/
theorem nonempty_homotopy_id_zero_of_homotopyEquiv (e : HomotopyEquiv K L) :
    Nonempty (Homotopy (𝟙 (mappingCone e.hom)) 0) :=
  have : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map e.hom) :=
    inferInstanceAs (IsIso (HomotopyCategory.isoOfHomotopyEquiv e).hom)
  nonempty_homotopy_id_zero_of_isIso_quotient_map e.hom

end

section Shift

open HomComplex

variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The components of `mappingCone.map` on the left inclusion. -/
@[reassoc (attr := simp)]
lemma inl_v_map_f (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ₁).v p q hpq ≫ (map φ₁ φ₂ a b comm).f q = a.f p ≫ (inl φ₂).v p q hpq := by
  simp [map]

@[reassoc (attr := simp)]
lemma inr_f_map_f (p : ℤ) : (inr φ₁).f p ≫ (map φ₁ φ₂ a b comm).f p = b.f p ≫ (inr φ₂).f p := by
  simp [map]

@[reassoc (attr := simp)]
lemma map_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (map φ₁ φ₂ a b comm).f p ≫ (fst φ₂).1.v p q hpq = (fst φ₁).1.v p q hpq ≫ a.f q := by
  apply ext_from φ₁ q p hpq <;> simp

@[reassoc (attr := simp)]
lemma map_f_snd_v (p : ℤ) :
    (map φ₁ φ₂ a b comm).f p ≫ (snd φ₂).v p p (add_zero p) =
      (snd φ₁).v p p (add_zero p) ≫ b.f p := by
  apply ext_from φ₁ (p + 1) p rfl <;> simp

/-- The isomorphism of mapping cones induced by an isomorphism of arrows. -/
@[expose, simps]
noncomputable def mapIso {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} (e₁ : K₁ ≅ K₂) (e₂ : L₁ ≅ L₂)
    (comm : φ₁ ≫ e₂.hom = e₁.hom ≫ φ₂) :
    mappingCone φ₁ ≅ mappingCone φ₂ where
  hom := map φ₁ φ₂ e₁.hom e₂.hom comm
  inv := map φ₂ φ₁ e₁.inv e₂.inv (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc,
    ← reassoc_of% comm, e₂.hom_inv_id, Category.comp_id])
  hom_inv_id := by rw [← map_comp]; simp [map_id]
  inv_hom_id := by rw [← map_comp]; simp [map_id]

/-- A variant of `inl_v_fst_v` with an arbitrary target degree. -/
@[reassoc]
lemma inl_v_fst_v' (p q r : ℤ) (h₁ : p + -1 = q) (h₂ : q + 1 = r) :
    (inl f).v p q h₁ ≫ (fst f).1.v q r h₂ = (K.XIsoOfEq (show p = r by lia)).hom := by
  obtain rfl : r = p := by lia
  simp

/-- A variant of `inl_v_snd_v` with an arbitrary target degree. -/
@[reassoc]
lemma inl_v_snd_v' (p q r : ℤ) (h₁ : p + -1 = q) (h₂ : q + 0 = r) :
    (inl f).v p q h₁ ≫ (snd f).v q r h₂ = 0 := by
  obtain rfl : r = q := by lia
  simp

/-- A variant of `inr_f_snd_v` with an arbitrary target degree. -/
@[reassoc]
lemma inr_f_snd_v' (p q : ℤ) (h : p + 0 = q) :
    (inr f).f p ≫ (snd f).v p q h = (L.XIsoOfEq (show p = q by lia)).hom := by
  obtain rfl : q = p := by lia
  simp

/-- The first component of `mappingCone.shiftIso` carries the sign `(-1)^n`. -/
@[reassoc (attr := simp)]
lemma shiftIso_hom_f_fst_v (n p q : ℤ) (hpq : p + 1 = q) :
    (shiftIso f n).hom.f p ≫ (fst (f⟦n⟧')).1.v p q hpq =
      n.negOnePow • (fst f).1.v (p + n) (q + n) (by lia) := by
  simp [shiftIso, Cochain.shift_v']

@[reassoc (attr := simp)]
lemma shiftIso_hom_f_snd_v (n p : ℤ) :
    (shiftIso f n).hom.f p ≫ (snd (f⟦n⟧')).v p p (add_zero p) =
      (snd f).v (p + n) (p + n) (add_zero _) := by
  simp [shiftIso, Cochain.shift_v']

/-- The inverse of `mappingCone.shiftIso` also carries the sign `(-1)^n` on the first component. -/
@[reassoc (attr := simp)]
lemma shiftIso_inv_f_fst_v (n p q : ℤ) (hpq : p + 1 = q) :
    (shiftIso f n).inv.f p ≫ (fst f).1.v (p + n) (q + n) (by lia) =
      n.negOnePow • (fst (f⟦n⟧')).1.v p q hpq := by
  rw [← cancel_epi ((shiftIso f n).hom.f p), ← HomologicalComplex.comp_f_assoc,
    Iso.hom_inv_id, HomologicalComplex.id_f, Category.id_comp, Linear.comp_units_smul,
    shiftIso_hom_f_fst_v, smul_smul, Int.units_mul_self, one_smul]

/-- `shiftIso` is natural in commutative squares. -/
@[reassoc]
lemma shiftIso_hom_naturality (n : ℤ) :
    (map φ₁ φ₂ a b comm)⟦n⟧' ≫ (shiftIso φ₂ n).hom =
      (shiftIso φ₁ n).hom ≫ map (φ₁⟦n⟧') (φ₂⟦n⟧') (a⟦n⟧') (b⟦n⟧')
        (by simp only [← Functor.map_comp, comm]) := by
  ext p
  rw [ext_to_iff _ p (p + 1) rfl]
  constructor <;> simp

/-- `shiftIso` for the shift by `0` is induced by `shiftFunctorZero`. -/
@[reassoc]
lemma shiftFunctorZero_inv_app_shiftIso_hom :
    (shiftFunctorZero _ ℤ).inv.app (mappingCone f) ≫ (shiftIso f 0).hom =
      map f (f⟦0⟧') ((shiftFunctorZero _ ℤ).inv.app K) ((shiftFunctorZero _ ℤ).inv.app L)
        ((shiftFunctorZero _ ℤ).inv.naturality f) := by
  ext p
  rw [ext_to_iff _ p (p + 1) rfl]
  constructor <;> apply ext_from f (p + 1) p rfl <;>
    simp [shiftFunctorZero_inv_app_f, TauCeti.XIsoOfEq_hom_comp_v, inl_v_snd_v', inr_f_snd_v',
      inl_v_fst_v']

/-- `shiftIso` for the shift by `a + b` is obtained from those for `a` and `b`, through
`shiftFunctorAdd`. -/
@[reassoc]
lemma shiftFunctorAdd_inv_app_shiftIso_hom (a b : ℤ) :
    (shiftFunctorAdd _ a b).inv.app (mappingCone f) ≫ (shiftIso f (a + b)).hom =
      (shiftIso f a).hom⟦b⟧' ≫ (shiftIso (f⟦a⟧') b).hom ≫
        map (f⟦a⟧'⟦b⟧') (f⟦a + b⟧') ((shiftFunctorAdd _ a b).inv.app K)
          ((shiftFunctorAdd _ a b).inv.app L) ((shiftFunctorAdd _ a b).inv.naturality f) := by
  ext p
  rw [ext_to_iff _ p (p + 1) rfl]
  constructor <;> apply ext_from f (p + b + a + 1) (p + b + a) rfl <;>
    simp [shiftFunctorAdd_inv_app_f, TauCeti.XIsoOfEq_hom_comp_v, inl_v_snd_v', inr_f_snd_v',
      inl_v_fst_v', inl_v_fst_v'_assoc, Int.negOnePow_add, smul_smul, mul_comm]

end Shift

end CochainComplex.mappingCone

namespace TauCeti

open CategoryTheory CochainComplex CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type*} [Category* D] {F G : D ⥤ CochainComplex C ℤ} (τ : F ⟶ G)

/-- The mapping cone of a natural transformation `τ : F ⟶ G` of functors with values in
cochain complexes, as the functor `X ↦ mappingCone (τ.app X)`. -/
@[expose, simps]
noncomputable def mappingConeFunctor : D ⥤ CochainComplex C ℤ where
  obj X := mappingCone (τ.app X)
  map f := map _ _ (F.map f) (G.map f) (τ.naturality f).symm
  map_id X := by
    ext p
    apply ext_from (τ.app X) (p + 1) p rfl <;> simp
  map_comp f g := by
    ext p
    apply ext_from _ (p + 1) p rfl <;> simp

variable [HasShift D ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [NatTrans.CommShift τ ℤ]

/-- The isomorphism `mappingCone (τ.app (X⟦a⟧)) ≅ (mappingCone (τ.app X))⟦a⟧`: the map of
mapping cones induced by the commutation isomorphisms of `F` and `G`, followed by the inverse
of `CochainComplex.mappingCone.shiftIso`. -/
noncomputable def mappingConeFunctorShiftIso (a : ℤ) (X : D) :
    mappingCone (τ.app (X⟦a⟧)) ≅ (mappingCone (τ.app X))⟦a⟧ :=
  mapIso ((F.commShiftIso a).app X) ((G.commShiftIso a).app X)
    (NatTrans.shift_app_comm τ a X).symm ≪≫ (shiftIso (τ.app X) a).symm

lemma mappingConeFunctorShiftIso_hom (a : ℤ) (X : D) :
    (mappingConeFunctorShiftIso τ a X).hom =
      map _ _ ((F.commShiftIso a).hom.app X) ((G.commShiftIso a).hom.app X)
        (NatTrans.shift_app_comm τ a X).symm ≫ (shiftIso (τ.app X) a).inv :=
  (rfl)

/-- Followed by `shiftIso`, `TauCeti.mappingConeFunctorShiftIso` is the map of mapping cones
induced by the commutation isomorphisms of `F` and `G`. -/
@[reassoc (attr := simp)]
lemma mappingConeFunctorShiftIso_hom_comp_shiftIso_hom (a : ℤ) (X : D) :
    (mappingConeFunctorShiftIso τ a X).hom ≫ (shiftIso (τ.app X) a).hom =
      map _ _ ((F.commShiftIso a).hom.app X) ((G.commShiftIso a).hom.app X)
        (NatTrans.shift_app_comm τ a X).symm := by
  simp [mappingConeFunctorShiftIso]

/-- The isomorphisms `TauCeti.mappingConeFunctorShiftIso` are natural. -/
lemma mappingConeFunctorShiftIso_hom_naturality (a : ℤ) {X Y : D} (f : X ⟶ Y) :
    map _ _ (F.map (f⟦a⟧')) (G.map (f⟦a⟧')) (τ.naturality _).symm ≫
        (mappingConeFunctorShiftIso τ a Y).hom =
      (mappingConeFunctorShiftIso τ a X).hom ≫
        (map _ _ (F.map f) (G.map f) (τ.naturality f).symm)⟦a⟧' := by
  rw [← cancel_mono (shiftIso (τ.app Y) a).hom, Category.assoc, Category.assoc,
    mappingConeFunctorShiftIso_hom_comp_shiftIso_hom, shiftIso_hom_naturality,
    mappingConeFunctorShiftIso_hom_comp_shiftIso_hom_assoc, ← map_comp, ← map_comp]
  congr 1 <;> simp

private lemma mappingConeFunctorShiftIso_zero (X : D) :
    (mappingConeFunctorShiftIso τ 0 X).hom =
      map (τ.app (X⟦0⟧)) (τ.app X) (F.map ((shiftFunctorZero D ℤ).hom.app X))
        (G.map ((shiftFunctorZero D ℤ).hom.app X)) (τ.naturality _).symm ≫
          (shiftFunctorZero _ ℤ).inv.app (mappingCone (τ.app X)) := by
  rw [← cancel_mono (shiftIso (τ.app X) 0).hom, Category.assoc,
    mappingConeFunctorShiftIso_hom_comp_shiftIso_hom, shiftFunctorZero_inv_app_shiftIso_hom,
    ← map_comp]
  congr 1 <;> simp [Functor.commShiftIso_zero]

private lemma mappingConeFunctorShiftIso_add (a b : ℤ) (X : D) :
    (mappingConeFunctorShiftIso τ (a + b) X).hom =
      map (τ.app (X⟦a + b⟧)) (τ.app (X⟦a⟧⟦b⟧)) (F.map ((shiftFunctorAdd D a b).hom.app X))
        (G.map ((shiftFunctorAdd D a b).hom.app X)) (τ.naturality _).symm ≫
          (mappingConeFunctorShiftIso τ b (X⟦a⟧)).hom ≫
            (mappingConeFunctorShiftIso τ a X).hom⟦b⟧' ≫
              (shiftFunctorAdd _ a b).inv.app (mappingCone (τ.app X)) := by
  rw [← cancel_mono (shiftIso (τ.app X) (a + b)).hom, Category.assoc, Category.assoc,
    Category.assoc, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom,
    shiftFunctorAdd_inv_app_shiftIso_hom, ← Functor.map_comp_assoc,
    mappingConeFunctorShiftIso_hom_comp_shiftIso_hom, shiftIso_hom_naturality_assoc,
    mappingConeFunctorShiftIso_hom_comp_shiftIso_hom_assoc, ← map_comp, ← map_comp, ← map_comp]
  congr 1 <;> simp [Functor.commShiftIso_add]

/-- The mapping cone of a natural transformation compatible with the shifts commutes with the
shifts, through `TauCeti.mappingConeFunctorShiftIso`. -/
noncomputable instance : (mappingConeFunctor τ).CommShift ℤ where
  commShiftIso a := NatIso.ofComponents (mappingConeFunctorShiftIso τ a)
    (fun f ↦ mappingConeFunctorShiftIso_hom_naturality τ a f)
  commShiftIso_zero := by
    refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
    simp only [Functor.CommShift.isoZero_hom_app]
    exact mappingConeFunctorShiftIso_zero τ X
  commShiftIso_add a b := by
    refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
    simp only [Functor.CommShift.isoAdd_hom_app]
    exact mappingConeFunctorShiftIso_add τ a b X

lemma mappingConeFunctor_commShiftIso_hom_app (a : ℤ) (X : D) :
    ((mappingConeFunctor τ).commShiftIso a).hom.app X = (mappingConeFunctorShiftIso τ a X).hom :=
  (rfl)

end TauCeti
