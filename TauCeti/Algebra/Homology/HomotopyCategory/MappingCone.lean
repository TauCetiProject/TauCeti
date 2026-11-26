/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Basic
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Mapping cones and homotopy equivalences

The standard null-homotopy of `f ≫ mappingCone.inr f` has components given by
`mappingCone.inl f`. This file exposes that homotopy and the component formulas relating
Mathlib's mapping-cone API to its underlying homotopy-cofiber construction.

For Mathlib's `mappingCone.mapOfHomotopy`, the component formulas retain the specified square
homotopy. These maps compose using `Homotopy.compSquare`, and a specified degree-minus-two
cochain whose differential is the difference of two square homotopies induces a homotopy
of the cone maps (`mapOfHomotopyHomotopy`). This uses Joël Riou's `mappingCone.descHomotopy`.

A morphism of cochain complexes `f : K ⟶ L` sits in the distinguished triangle
`K ⟶ L ⟶ cone f ⟶ K⟦1⟧` of the homotopy category. In a pretriangulated category the third
object of a distinguished triangle is zero exactly when its first morphism is an isomorphism, so
the mapping cone of `f` is zero in the homotopy category as soon as `f` becomes an isomorphism
there, in particular when `f` is a homotopy equivalence. Being zero in the homotopy category means
that the identity is null-homotopic, which is the form in which this file records the statement.
In an abelian category the same triangle shows that `f` is a quasi-isomorphism exactly when its
mapping cone is acyclic, since the quasi-isomorphisms of the homotopy category are the morphisms
whose cones are acyclic.

## Main results

* `CochainComplex.mappingCone.inrCompHomotopy`: the standard null-homotopy of the composite of
  `f` with the right inclusion into its mapping cone.
* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_isIso_quotient_map`: the mapping cone
  of a morphism inverted by the homotopy category is contractible.
* `CochainComplex.mappingCone.nonempty_homotopy_id_zero_of_homotopyEquiv`: the mapping cone of a
  homotopy equivalence is contractible.
* `CochainComplex.quasiIso_iff_acyclic_mappingCone`: in an abelian category, a morphism is a
  quasi-isomorphism exactly when its mapping cone is acyclic.
* `CochainComplex.mappingCone.isIso_map_f`: the map of mapping cones induced by a commutative
  square is an isomorphism in each degree where the vertical maps are.
* `CochainComplex.mappingCone.mapHomotopy`: homotopies of the vertical maps of a commutative
  square, compatible with its horizontal maps, induce a homotopy of the maps of mapping cones.
* `CategoryTheory.ShortComplex.Splitting.mappingConeGHomotopyEquiv`: for a short complex of
  cochain complexes split by chain maps, the mapping cone of the split epimorphism `S.g` is
  homotopy equivalent to `S.X₁⟦1⟧`.
* `HomotopyEquiv.shift`: the shift of a homotopy equivalence of cochain complexes.

## Mapping cones of natural transformations and shifts

Mathlib's `CochainComplex.mappingCone.shiftIso φ n : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧')`
multiplies the first component by `(-1)^n`. This file proves that it is natural in commutative
squares and compatible with the isomorphisms `shiftFunctorZero` and `shiftFunctorAdd`. For a
natural transformation `τ : F ⟶ G` of functors `D ⥤ CochainComplex C ℤ`, the mapping cones
`X ↦ mappingCone (τ.app X)` form a functor `NatTrans.mappingConeFunctor τ`. When `F`, `G` and
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
* `NatTrans.mappingConeFunctor`: the mapping cone of a natural transformation, as a functor, which
  commutes with the shifts when `τ` does.

## Mapping cones of maps of mapping cones

A commutative square `a ≫ v = u ≫ b` of cochain complexes, with `a : X₁ ⟶ X₂`, `b : Y₁ ⟶ Y₂`,
`u : X₁ ⟶ Y₁` and `v : X₂ ⟶ Y₂`, induces maps of mapping cones `cone a ⟶ cone b` and
`cone u ⟶ cone v`. Their mapping cones are isomorphic: in degree `n` both are
`X₁ⁿ⁺² ⊕ X₂ⁿ⁺¹ ⊕ Y₁ⁿ⁺¹ ⊕ Y₂ⁿ`, and the isomorphism changes the sign of the first summand. It is
compatible with the right inclusions of `cone v` and with the third morphisms of the mapping cone
triangles. It is built with Joël Riou's `mappingCone.lift` and `mappingCone.descCocycle`.

For a natural transformation `α : F ⟶ G` of additive functors, the mapping cone of the induced
natural transformation of functors on cochain complexes, evaluated at the mapping cone of `φ`,
is such a mapping cone of a map of mapping cones, after Mathlib's identification
`mappingCone.mapHomologicalComplexIso` of `F (cone φ)` with `cone (F φ)`. Hence the functor
`NatTrans.mappingConeFunctor` sends mapping cone triangles to mapping cone triangles, compatibly
with its commutation with the shifts, as Mathlib's `CochainComplex.mappingCone.mapTriangleIso`
does for a single additive functor.

* `CochainComplex.mappingCone.transposeIso`: the isomorphism between the mapping cones of
  `cone a ⟶ cone b` and of `cone u ⟶ cone v`.
* `CochainComplex.mappingCone.map_inr_inr_comp_transposeHom` and
  `CochainComplex.mappingCone.map_triangle_mor₃_comp_shiftIso_inv`: its compatibility with the
  mapping cone triangles.
* `CochainComplex.mappingCone.mapHomologicalComplexIso_hom_naturality`: naturality of
  `mapHomologicalComplexIso` in the additive functor.
* `NatTrans.mappingConeFunctorMapTriangleIso`: the image of a mapping cone triangle by the mapping
  cone functor of a natural transformation of additive functors.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] {K L : CochainComplex C ℤ} (f : K ⟶ L)

section HasHomotopyCofiber

variable [HasHomotopyCofiber f]

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

/-- A variant of `inl_v_fst_v` with an arbitrary target degree. -/
@[reassoc]
lemma inl_v_fst_v' (p q r : ℤ) (h₁ : p + -1 = q) (h₂ : q + 1 = r) :
    (inl f).v p q h₁ ≫ (fst f).val.v q r h₂ = (K.XIsoOfEq (show p = r by lia)).hom := by
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

/-- The inclusion `mappingCone.inr f` of `L` into the mapping cone of `f : K ⟶ L` is a
monomorphism: it is the inclusion `homotopyCofiber.inr f`. -/
instance mono_inr : Mono (inr f) :=
  inferInstanceAs (Mono (homotopyCofiber.inr f))

end HasHomotopyCofiber

variable [HasBinaryBiproducts C]

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

section DescHomotopy

open HomComplex

variable {M : CochainComplex C ℤ} (f₁ f₂ : mappingCone f ⟶ M) (γ₁ : Cochain K M (-2))
  (γ₂ : Cochain L M (-1))

/-- The components of `descHomotopy f f₁ f₂ γ₁ γ₂ h₁ h₂` are those of the cochain
`descCochain f γ₁ γ₂`. -/
lemma descHomotopy_hom
    (h₁ : (inl f).comp (Cochain.ofHom f₁) (add_zero (-1)) =
      δ (-2) (-1) γ₁ + (Cochain.ofHom f).comp γ₂ (zero_add (-1)) +
      (inl f).comp (Cochain.ofHom f₂) (add_zero (-1)))
    (h₂ : Cochain.ofHom (inr f ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr f ≫ f₂))
    (p q : ℤ) (hpq : p + -1 = q) :
    (descHomotopy f f₁ f₂ γ₁ γ₂ h₁ h₂).hom p q = (descCochain f γ₁ γ₂ (by simp)).v p q hpq := by
  -- Mathlib defines `descHomotopy` through the inverse of `Cochain.equivHomotopy`, whose
  -- components are those of the cochain in degrees `p + -1 = q` and zero otherwise.
  simp only [descHomotopy, Cochain.equivHomotopy, Equiv.coe_fn_symm_mk, hpq, ↓reduceDIte]

end DescHomotopy

section HomotopySquares

open HomComplex

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ}
  {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {φ₃ : K₃ ⟶ L₃}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
  (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/-- A cone map from a specified square homotopy acts on the shifted source by the source map
and the chosen homotopy. -/
@[reassoc (attr := simp)]
lemma inl_v_mapOfHomotopy_f (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ₁).v p q hpq ≫ (mapOfHomotopy H).f q =
      a.f p ≫ (inl φ₂).v p q hpq + H.hom p q ≫ (inr φ₂).f q := by
  simp [mapOfHomotopy, Cochain.equivHomotopy, Cochain.ofHomotopy]

/-- A cone map from a specified square homotopy acts on the target by the target map. -/
@[reassoc (attr := simp)]
lemma inr_f_mapOfHomotopy_f (p : ℤ) :
    (inr φ₁).f p ≫ (mapOfHomotopy H).f p = b.f p ≫ (inr φ₂).f p :=
  HomologicalComplex.congr_hom (triangleMapOfHomotopy_comm₂ H) p

/-- The first projection of a cone map does not depend on the square homotopy. -/
@[reassoc (attr := simp)]
lemma mapOfHomotopy_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (mapOfHomotopy H).f p ≫ (fst φ₂).val.v p q hpq =
      (fst φ₁).val.v p q hpq ≫ a.f q := by
  apply ext_from φ₁ q p hpq <;> simp

/-- The second projection retains the specified square homotopy. -/
@[reassoc (attr := simp)]
lemma mapOfHomotopy_f_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (mapOfHomotopy H).f p ≫ (snd φ₂).v p p (add_zero p) =
      (fst φ₁).val.v p q hpq ≫ H.hom q p +
        (snd φ₁).v p p (add_zero p) ≫ b.f p := by
  apply ext_from φ₁ q p hpq <;> simp

variable {a' : K₂ ⟶ K₃} {b' : L₂ ⟶ L₃}
  (H' : Homotopy (φ₂ ≫ b') (a' ≫ φ₃))

/-- Cone maps compose with the composed square homotopy, not with an independently chosen
homotopy for the outer square. -/
@[reassoc]
lemma mapOfHomotopy_comp :
    mapOfHomotopy (H.compSquare H') = mapOfHomotopy H ≫ mapOfHomotopy H' := by
  ext p
  apply ext_from φ₁ (p + 1) p rfl <;>
    simp [Preadditive.add_comp, Preadditive.comp_add, add_assoc, add_comm]

/-- A specified second homotopy between square homotopies gives a homotopy of their cone maps.
No independence from an arbitrary choice of square homotopy is asserted. -/
noncomputable def mapOfHomotopyHomotopy
    (H₂ : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (s : Cochain K₁ L₂ (-2))
    (hs : δ (-2) (-1) s = Cochain.ofHomotopy H - Cochain.ofHomotopy H₂) :
    Homotopy (mapOfHomotopy H) (mapOfHomotopy H₂) :=
  descHomotopy φ₁ _ _ (s.comp (Cochain.ofHom (inr φ₂)) (add_zero _)) 0
    (by
      rw [δ_comp_zero_cochain _ _ (-1) (by omega), δ_ofHom, Cochain.comp_zero,
        zero_add, hs, Cochain.sub_comp]
      simp only [mapOfHomotopy, inl_desc, Cochain.comp_zero, add_zero]
      ext p q hpq
      simp only [Cochain.add_v, Cochain.sub_v, Cochain.zero_cochain_comp_v,
        Cochain.ofHom_v, Cochain.comp_zero_cochain_v]
      simp [Cochain.equivHomotopy, Cochain.ofHomotopy]
      abel)
    (by simp [mapOfHomotopy])

/-- The second homotopy of cone maps factors through the first projection of the source
and the right inclusion of the target. -/
@[simp]
lemma mapOfHomotopyHomotopy_hom
    (H₂ : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (s : Cochain K₁ L₂ (-2))
    (hs : δ (-2) (-1) s = Cochain.ofHomotopy H - Cochain.ofHomotopy H₂)
    (p q : ℤ) (hpq : p + -1 = q) :
    (mapOfHomotopyHomotopy H H₂ s hs).hom p q =
      (fst φ₁ : Cochain _ _ 1).v p (p + 1) rfl ≫
        s.v (p + 1) q (by omega) ≫ (inr φ₂).f q := by
  rw [mapOfHomotopyHomotopy, descHomotopy_hom _ _ _ _ _ _ _ p q hpq]
  simp only [descCochain, Cochain.comp_zero, add_zero]
  rw [Cochain.comp_v _ _ _ p (p + 1) q rfl (by omega),
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

end HomotopySquares

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
    (map φ₁ φ₂ a b comm).f p ≫ (fst φ₂).val.v p q hpq = (fst φ₁).val.v p q hpq ≫ a.f q := by
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
  inv := map φ₂ φ₁ e₁.inv e₂.inv (by simp [Iso.comp_inv_eq, comm])
  hom_inv_id := by rw [← map_comp]; simp [map_id]
  inv_hom_id := by rw [← map_comp]; simp [map_id]

section MapHomotopy

/-- **Homotopic squares induce homotopic maps of mapping cones.** Homotopies `ha` from `a` to `a'`
and `hb` from `b` to `b'` which commute with `φ₁` and `φ₂`, in the sense that
`φ₁ ≫ hb = ha ≫ φ₂` in every pair of degrees, induce a homotopy from the map of mapping cones of
the square `(a, b)` to that of the square `(a', b')`. On the shifted source it is `-ha` followed
by the left inclusion, and on the target it is `hb` followed by the right inclusion
(`inl_v_mapHomotopy_hom`, `inr_f_mapHomotopy_hom`). -/
noncomputable def mapHomotopy {a' : K₁ ⟶ K₂} {b' : L₁ ⟶ L₂} (comm' : φ₁ ≫ b' = a' ≫ φ₂)
    (ha : Homotopy a a') (hb : Homotopy b b')
    (h : ∀ p q, φ₁.f p ≫ hb.hom p q = ha.hom p q ≫ φ₂.f q) :
    Homotopy (map φ₁ φ₂ a b comm) (map φ₁ φ₂ a' b' comm') :=
  descHomotopy φ₁ _ _ (-(Cochain.ofHomotopy ha).comp (inl φ₂) (by lia))
    ((Cochain.ofHomotopy hb).comp (Cochain.ofHom (inr φ₂)) (add_zero _))
    (by
      have hc : (Cochain.ofHom φ₁).comp (Cochain.ofHomotopy hb) (zero_add _) =
          (Cochain.ofHomotopy ha).comp (Cochain.ofHom φ₂) (add_zero _) := by
        ext p q hpq
        simp [Cochain.ofHomotopy, h]
      rw [δ_neg, δ_comp _ _ _ 0 0 (-1) (by lia) (by lia) (by lia), δ_inl, δ_ofHomotopy,
        ← Cochain.comp_assoc_of_first_is_zero_cochain, hc]
      simp only [map, inl_desc, Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one,
        Units.neg_smul, one_smul, Cochain.sub_comp, neg_add_rev, neg_neg, Cochain.ofHom_comp]
      rw [Cochain.comp_assoc _ _ _ (add_zero _) (add_zero _) (by lia)]
      abel)
    (by
      rw [δ_comp_zero_cochain _ _ _ (by lia), δ_ofHom, Cochain.comp_zero, zero_add,
        δ_ofHomotopy, Cochain.sub_comp]
      simp [map])

variable {a' : K₁ ⟶ K₂} {b' : L₁ ⟶ L₂} (comm' : φ₁ ≫ b' = a' ≫ φ₂)
  (ha : Homotopy a a') (hb : Homotopy b b')
  (h : ∀ p q, φ₁.f p ≫ hb.hom p q = ha.hom p q ≫ φ₂.f q)

/-- On the shifted source, the homotopy of maps of mapping cones is `-ha` followed by the left
inclusion. -/
@[reassoc (attr := simp)]
lemma inl_v_mapHomotopy_hom (p q r : ℤ) (hpq : p + -1 = q) (hqr : q + -1 = r) :
    (inl φ₁).v p q hpq ≫ (mapHomotopy φ₁ φ₂ a b comm comm' ha hb h).hom q r =
      -(ha.hom p q ≫ (inl φ₂).v q r hqr) := by
  rw [mapHomotopy, descHomotopy_hom _ _ _ _ _ _ _ q r hqr, inl_v_descCochain_v]
  simp [Cochain.comp_v _ _ _ p q r hpq hqr, Cochain.ofHomotopy]

/-- On the target, the homotopy of maps of mapping cones is `hb` followed by the right
inclusion. -/
@[reassoc (attr := simp)]
lemma inr_f_mapHomotopy_hom (p q : ℤ) :
    (inr φ₁).f p ≫ (mapHomotopy φ₁ φ₂ a b comm comm' ha hb h).hom p q =
      hb.hom p q ≫ (inr φ₂).f q := by
  by_cases hpq : p + -1 = q
  · rw [mapHomotopy, descHomotopy_hom _ _ _ _ _ _ _ p q hpq, inr_f_descCochain_v]
    simp [Cochain.ofHomotopy]
  · rw [Homotopy.zero _ p q (by simp; lia), hb.zero p q (by simp; lia), comp_zero, zero_comp]

end MapHomotopy

/-- The first component of `mappingCone.shiftIso` carries the sign `(-1)^n`. -/
@[reassoc (attr := simp)]
lemma shiftIso_hom_f_fst_v (n p q : ℤ) (hpq : p + 1 = q) :
    (shiftIso f n).hom.f p ≫ (fst (f⟦n⟧')).val.v p q hpq =
      n.negOnePow • (fst f).val.v (p + n) (q + n) (by lia) := by
  simp [shiftIso, Cochain.shift_v']

@[reassoc (attr := simp)]
lemma shiftIso_hom_f_snd_v (n p : ℤ) :
    (shiftIso f n).hom.f p ≫ (snd (f⟦n⟧')).v p p (add_zero p) =
      (snd f).v (p + n) (p + n) (add_zero _) := by
  simp [shiftIso, Cochain.shift_v']

/-- The inverse of `mappingCone.shiftIso` also carries the sign `(-1)^n` on the first component. -/
@[reassoc (attr := simp)]
lemma shiftIso_inv_f_fst_v (n p q : ℤ) (hpq : p + 1 = q) :
    (shiftIso f n).inv.f p ≫ (fst f).val.v (p + n) (q + n) (by lia) =
      n.negOnePow • (fst (f⟦n⟧')).val.v p q hpq := by
  rw [← cancel_epi ((shiftIso f n).hom.f p)]
  simp [← HomologicalComplex.comp_f_assoc, smul_smul]

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
    simp [shiftFunctorZero_inv_app_f, Cochain.XIsoOfEq_hom_comp_v, inl_v_snd_v', inr_f_snd_v',
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
    simp [shiftFunctorAdd_inv_app_f, Cochain.XIsoOfEq_hom_comp_v, inl_v_snd_v', inr_f_snd_v',
      inl_v_fst_v', inl_v_fst_v'_assoc, Int.negOnePow_add, smul_smul, mul_comm]

end Shift

section Transpose

open HomComplex

variable {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (u : X₁ ⟶ Y₁)
  (v : X₂ ⟶ Y₂) (comm : a ≫ v = u ≫ b)

/-- For a commutative square `a ≫ v = u ≫ b` of cochain complexes, the comparison morphism
between the mapping cones of the maps `cone a ⟶ cone b` and `cone u ⟶ cone v` induced by the
square. In degree `n` both mapping cones are `X₁ⁿ⁺² ⊕ X₂ⁿ⁺¹ ⊕ Y₁ⁿ⁺¹ ⊕ Y₂ⁿ`, and the comparison
is the identity on these summands except for the sign `-1` on `X₁ⁿ⁺²`. It is an isomorphism,
`mappingCone.transposeIso`, whose inverse is the comparison for the transposed square. -/
noncomputable def transposeHom :
    mappingCone (map a b u v comm) ⟶ mappingCone (map u v a b comm.symm) :=
  lift _ (descCocycle _ (-(fst a).val.comp (inl u) (add_neg_cancel 1))
      (Cocycle.mk ((fst b).val.comp (Cochain.ofHom (inr u)) (add_zero 1)) 2 (by lia) (by
        simp [δ_comp_zero_cochain])) (zero_add 1) (by
        rw [δ_neg, δ_comp (fst a).val (inl u) _ 2 0 1 (by lia) rfl (by lia)]
        ext p q hpq
        simp))
    (descCochain _ ((snd a).comp (inl v) (zero_add _))
      ((snd b).comp (Cochain.ofHom (inr v)) (zero_add 0)) (neg_add_cancel 1)) (by
      ext p _ rfl
      simp [ext_from_iff _ (p + 1) p rfl, ext_from_iff _ (p + 2) (p + 1) (by lia),
        inl_v_d_assoc _ (p + 1) p (p + 2) (by lia) (by lia),
        inl_v_d _ (p + 1) p (p + 2) (by lia) (by lia),
        inl_v_d_assoc _ (p + 2) (p + 1) (p + 3) (by lia) (by lia),
        Cochain.comp_v _ _ (add_neg_cancel 1) (p + 1) (p + 2) (p + 1) (by lia) (by lia)])

/-- The comparison for the transposed square is inverse to `mappingCone.transposeHom`. -/
@[reassoc (attr := simp)]
lemma transposeHom_comp_transposeHom :
    transposeHom a b u v comm ≫ transposeHom u v a b comm.symm = 𝟙 _ := by
  ext n
  simp [transposeHom, lift_f _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) n rfl,
    Cochain.comp_v _ _ (add_neg_cancel 1) (n + 1) (n + 2) (n + 1) (by lia) (by lia),
    ext_from_iff _ (n + 2) (n + 1) (by lia)]

/-- The mapping cone of the map `cone a ⟶ cone b` of mapping cones induced by a commutative
square `a ≫ v = u ≫ b` is isomorphic to the mapping cone of the map `cone u ⟶ cone v`. -/
noncomputable def transposeIso :
    mappingCone (map a b u v comm) ≅ mappingCone (map u v a b comm.symm) where
  hom := transposeHom a b u v comm
  inv := transposeHom u v a b comm.symm
  hom_inv_id := transposeHom_comp_transposeHom a b u v comm
  inv_hom_id := transposeHom_comp_transposeHom u v a b comm.symm

@[simp]
lemma transposeIso_hom : (transposeIso a b u v comm).hom = transposeHom a b u v comm :=
  (rfl)

@[simp]
lemma transposeIso_inv : (transposeIso a b u v comm).inv = transposeHom u v a b comm.symm :=
  (rfl)

/-- Under `mappingCone.transposeHom`, the map `cone v ⟶ cone (cone a ⟶ cone b)` induced by the
right inclusions becomes the right inclusion of `cone v` in the mapping cone of
`cone u ⟶ cone v`. -/
@[reassoc (attr := simp)]
lemma map_inr_inr_comp_transposeHom :
    map v (map a b u v comm) (inr a) (inr b) (by ext; simp) ≫
        transposeHom a b u v comm =
      inr (map u v a b comm.symm) := by
  ext n
  simp [transposeHom, ext_from_iff _ (n + 1) n rfl, ext_to_iff _ n (n + 1) rfl,
    Cochain.comp_v _ _ (add_neg_cancel 1) (n + 1) (n + 2) (n + 1) (by lia) (by lia)]

/-- Under `mappingCone.transposeHom`, the map `cone (cone a ⟶ cone b) ⟶ cone (u⟦1⟧')` induced
by the third morphisms of the mapping cone triangles of `a` and `b`, followed by
`mappingCone.shiftIso`, becomes the third morphism of the mapping cone triangle of
`cone u ⟶ cone v`. -/
@[reassoc]
lemma map_triangle_mor₃_comp_shiftIso_inv :
    map (map a b u v comm) (u⟦(1 : ℤ)⟧') (triangle a).mor₃ (triangle b).mor₃
        (by ext n; simp [ext_from_iff _ (n + 1) n rfl]) ≫ (shiftIso u 1).inv =
      transposeHom a b u v comm ≫ (triangle (map u v a b comm.symm)).mor₃ := by
  ext n
  simp [transposeHom, lift_f _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) n rfl,
    ext_to_iff _ (n + 1) (n + 2) (by lia), shiftIso, Cochain.shift_v',
    ext_from_iff _ (n + 2) (n + 1) (by lia),
    inl_v_fst_v' u (n + 1 + 1) (n + 1) (n + 2) (by lia) (by lia),
    Cochain.comp_v _ _ (add_neg_cancel 1) (n + 1) (n + 2) (n + 1) (by lia) (by lia)]

end Transpose

section Map

/-! ### Components of the map of mapping cones induced by a commutative square -/

variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂)
  (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

/-- The map of mapping cones induced by a commutative square is an isomorphism in degree `p` when
the vertical maps are isomorphisms in degrees `p + 1` (on the sources) and `p` (on the
targets). -/
lemma isIso_map_f (p q : ℤ) (hpq : p + 1 = q) [IsIso (a.f q)] [IsIso (b.f p)] :
    IsIso ((map φ₁ φ₂ a b comm).f p) := by
  refine ⟨(fst φ₂).val.v p q hpq ≫ inv (a.f q) ≫ (inl φ₁).v q p (by lia) +
      (snd φ₂).v p p (add_zero p) ≫ inv (b.f p) ≫ (inr φ₁).f p, ?_, ?_⟩
  · apply ext_from φ₁ q p (by lia) <;> simp
  · simp only [Preadditive.add_comp, Category.assoc, inl_v_map_f, inr_f_map_f,
      IsIso.inv_hom_id_assoc]
    exact id_X φ₂ p q hpq

end Map

section MapHomologicalComplex

variable {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D] {F G : C ⥤ D}
  [F.Additive] [G.Additive] (α : F ⟶ G)

/-- The identification `mappingCone.mapHomologicalComplexIso` of the image of a mapping cone by
an additive functor with the mapping cone of the image is natural in the additive functor. -/
@[reassoc]
lemma mapHomologicalComplexIso_hom_naturality :
    (NatTrans.mapHomologicalComplex α _).app (mappingCone f) ≫
        (mapHomologicalComplexIso f G).hom =
      (mapHomologicalComplexIso f F).hom ≫
        map _ _ ((NatTrans.mapHomologicalComplex α _).app K)
          ((NatTrans.mapHomologicalComplex α _).app L)
          ((NatTrans.mapHomologicalComplex α _).naturality f) := by
  ext n
  simp [mapHomologicalComplexIso, mapHomologicalComplexXIso_eq f _ n (n + 1) rfl]

end MapHomologicalComplex

end CochainComplex.mappingCone

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism of cochain complexes in an abelian category is a quasi-isomorphism exactly when its
mapping cone is acyclic. -/
theorem quasiIso_iff_acyclic_mappingCone {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    QuasiIso φ ↔ (mappingCone φ).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)

end CochainComplex

namespace CategoryTheory.NatTrans

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
    rw [← map_id (τ.app X)]
    congr 1 <;> simp
  map_comp f g := by
    rw [← map_comp]
    congr 1 <;> simp

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

/-- Followed by `shiftIso`, `NatTrans.mappingConeFunctorShiftIso` is the map of mapping cones
induced by the commutation isomorphisms of `F` and `G`. -/
@[reassoc (attr := simp)]
lemma mappingConeFunctorShiftIso_hom_comp_shiftIso_hom (a : ℤ) (X : D) :
    (mappingConeFunctorShiftIso τ a X).hom ≫ (shiftIso (τ.app X) a).hom =
      map _ _ ((F.commShiftIso a).hom.app X) ((G.commShiftIso a).hom.app X)
        (NatTrans.shift_app_comm τ a X).symm := by
  simp [mappingConeFunctorShiftIso]

/-- The isomorphisms `NatTrans.mappingConeFunctorShiftIso` are natural. -/
lemma mappingConeFunctorShiftIso_hom_naturality (a : ℤ) {X Y : D} (f : X ⟶ Y) :
    map _ _ (F.map (f⟦a⟧')) (G.map (f⟦a⟧')) (τ.naturality _).symm ≫
        (mappingConeFunctorShiftIso τ a Y).hom =
      (mappingConeFunctorShiftIso τ a X).hom ≫
        (map _ _ (F.map f) (G.map f) (τ.naturality f).symm)⟦a⟧' := by
  rw [← cancel_mono (shiftIso (τ.app Y) a).hom]
  simp only [Category.assoc, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom,
    shiftIso_hom_naturality, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom_assoc, ← map_comp]
  congr 1 <;> simp

private lemma mappingConeFunctorShiftIso_zero (X : D) :
    (mappingConeFunctorShiftIso τ 0 X).hom =
      map (τ.app (X⟦0⟧)) (τ.app X) (F.map ((shiftFunctorZero D ℤ).hom.app X))
        (G.map ((shiftFunctorZero D ℤ).hom.app X)) (τ.naturality _).symm ≫
          (shiftFunctorZero _ ℤ).inv.app (mappingCone (τ.app X)) := by
  rw [← cancel_mono (shiftIso (τ.app X) 0).hom]
  simp only [Category.assoc, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom,
    shiftFunctorZero_inv_app_shiftIso_hom, ← map_comp]
  congr 1 <;> simp [Functor.commShiftIso_zero]

private lemma mappingConeFunctorShiftIso_add (a b : ℤ) (X : D) :
    (mappingConeFunctorShiftIso τ (a + b) X).hom =
      map (τ.app (X⟦a + b⟧)) (τ.app (X⟦a⟧⟦b⟧)) (F.map ((shiftFunctorAdd D a b).hom.app X))
        (G.map ((shiftFunctorAdd D a b).hom.app X)) (τ.naturality _).symm ≫
          (mappingConeFunctorShiftIso τ b (X⟦a⟧)).hom ≫
            (mappingConeFunctorShiftIso τ a X).hom⟦b⟧' ≫
              (shiftFunctorAdd _ a b).inv.app (mappingCone (τ.app X)) := by
  rw [← cancel_mono (shiftIso (τ.app X) (a + b)).hom]
  simp only [Category.assoc, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom,
    shiftFunctorAdd_inv_app_shiftIso_hom, ← Functor.map_comp_assoc,
    shiftIso_hom_naturality_assoc, mappingConeFunctorShiftIso_hom_comp_shiftIso_hom_assoc,
    ← map_comp]
  congr 1 <;> simp [Functor.commShiftIso_add]

/-- The mapping cone of a natural transformation compatible with the shifts commutes with the
shifts, through `NatTrans.mappingConeFunctorShiftIso`. -/
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

end CategoryTheory.NatTrans

namespace CategoryTheory.NatTrans

open CategoryTheory CochainComplex CochainComplex.mappingCone

variable {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
  {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C] {F G : A ⥤ C}
  [F.Additive] [G.Additive] (α : F ⟶ G) {K L : CochainComplex A ℤ} (φ : K ⟶ L)

private lemma mappingConeFunctorMapTriangleIso_comm₂ :
    map _ _ ((F.mapHomologicalComplex _).map (inr φ)) ((G.mapHomologicalComplex _).map (inr φ))
        ((NatTrans.mapHomologicalComplex α _).naturality (inr φ)).symm ≫
      map _ _ (mapHomologicalComplexIso φ F).hom (mapHomologicalComplexIso φ G).hom
        (mapHomologicalComplexIso_hom_naturality φ α) ≫
      transposeHom _ _ _ _ ((NatTrans.mapHomologicalComplex α _).naturality φ) =
    inr (map _ _ ((F.mapHomologicalComplex _).map φ) ((G.mapHomologicalComplex _).map φ)
      ((NatTrans.mapHomologicalComplex α _).naturality φ).symm) := by
  rw [← Category.assoc, ← map_comp]
  simp only [map_inr, map_inr_inr_comp_transposeHom]

private lemma mappingConeFunctorMapTriangleIso_comm₃ :
    map _ _ ((F.mapHomologicalComplex _).map (triangle φ).mor₃)
        ((G.mapHomologicalComplex _).map (triangle φ).mor₃)
        ((NatTrans.mapHomologicalComplex α _).naturality _).symm ≫
      map _ _ (((F.mapHomologicalComplex _).commShiftIso (1 : ℤ)).hom.app K)
        (((G.mapHomologicalComplex _).commShiftIso (1 : ℤ)).hom.app K)
        (NatTrans.shift_app_comm (NatTrans.mapHomologicalComplex α _) 1 K).symm ≫
      (shiftIso ((NatTrans.mapHomologicalComplex α _).app K) 1).inv =
    (map _ _ (mapHomologicalComplexIso φ F).hom (mapHomologicalComplexIso φ G).hom
        (mapHomologicalComplexIso_hom_naturality φ α) ≫
      transposeHom _ _ _ _ ((NatTrans.mapHomologicalComplex α _).naturality φ)) ≫
      (triangle (map _ _ ((F.mapHomologicalComplex _).map φ) ((G.mapHomologicalComplex _).map φ)
        ((NatTrans.mapHomologicalComplex α _).naturality φ).symm)).mor₃ := by
  rw [Category.assoc, ← map_triangle_mor₃_comp_shiftIso_inv, ← Category.assoc,
    ← Category.assoc, ← map_comp, ← map_comp]
  simp only [map_δ]
  -- The two sides differ only by `(triangle φ).obj₃ = mappingCone φ`, which holds by definition.
  rfl

/-- For a natural transformation `α : F ⟶ G` of additive functors, the mapping cone functor
`K ↦ mappingCone (α.app K)` of the induced natural transformation of functors on cochain
complexes sends the mapping cone triangle of `φ` to the mapping cone triangle of its image,
compatibly with its commutation with the shifts. This extends Mathlib's
`CochainComplex.mappingCone.mapTriangleIso`, the case of a single additive functor. -/
noncomputable def mappingConeFunctorMapTriangleIso :
    (mappingConeFunctor (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))).mapTriangle.obj
        (triangle φ) ≅
      triangle
        ((mappingConeFunctor (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))).map φ) :=
  Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (mapIso (mapHomologicalComplexIso φ F) (mapHomologicalComplexIso φ G)
        (mapHomologicalComplexIso_hom_naturality φ α) ≪≫
      transposeIso _ _ _ _ ((NatTrans.mapHomologicalComplex α _).naturality φ))
    (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      dsimp
      exact (mappingConeFunctorMapTriangleIso_comm₂ α φ).trans (Category.id_comp _).symm)
    (by dsimp; exact (Category.comp_id _).trans (mappingConeFunctorMapTriangleIso_comm₃ α φ))

@[simp]
lemma mappingConeFunctorMapTriangleIso_hom_hom₁ :
    (mappingConeFunctorMapTriangleIso α φ).hom.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
lemma mappingConeFunctorMapTriangleIso_hom_hom₂ :
    (mappingConeFunctorMapTriangleIso α φ).hom.hom₂ = 𝟙 _ :=
  (rfl)

@[simp]
lemma mappingConeFunctorMapTriangleIso_hom_hom₃ :
    (mappingConeFunctorMapTriangleIso α φ).hom.hom₃ =
      map _ _ (mapHomologicalComplexIso φ F).hom (mapHomologicalComplexIso φ G).hom
          (mapHomologicalComplexIso_hom_naturality φ α) ≫
        transposeHom _ _ _ _ ((NatTrans.mapHomologicalComplex α _).naturality φ) :=
  (rfl)

@[simp]
lemma mappingConeFunctorMapTriangleIso_inv_hom₁ :
    (mappingConeFunctorMapTriangleIso α φ).inv.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
lemma mappingConeFunctorMapTriangleIso_inv_hom₂ :
    (mappingConeFunctorMapTriangleIso α φ).inv.hom₂ = 𝟙 _ :=
  (rfl)

@[simp]
lemma mappingConeFunctorMapTriangleIso_inv_hom₃ :
    (mappingConeFunctorMapTriangleIso α φ).inv.hom₃ =
      transposeHom _ _ _ _ ((NatTrans.mapHomologicalComplex α _).naturality φ).symm ≫
        (mapIso (mapHomologicalComplexIso φ F) (mapHomologicalComplexIso φ G)
          (mapHomologicalComplexIso_hom_naturality φ α)).inv :=
  (rfl)

end CategoryTheory.NatTrans

namespace HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C] {K L : CochainComplex C ℤ}

/-- The shift `K⟦n⟧ ≃ L⟦n⟧` of a homotopy equivalence `K ≃ L` of cochain complexes, with the
homotopies shifted by Mathlib's `Homotopy.shift`. -/
noncomputable def shift (e : HomotopyEquiv K L) (n : ℤ) : HomotopyEquiv (K⟦n⟧) (L⟦n⟧) where
  hom := e.hom⟦n⟧'
  inv := e.inv⟦n⟧'
  homotopyHomInvId := (Homotopy.ofEq (CategoryTheory.Functor.map_comp _ _ _).symm).trans
    ((e.homotopyHomInvId.shift n).trans (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (CategoryTheory.Functor.map_comp _ _ _).symm).trans
    ((e.homotopyInvHomId.shift n).trans (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))

/-- The map of the shift of a homotopy equivalence is the shifted map. -/
@[simp]
theorem shift_hom (e : HomotopyEquiv K L) (n : ℤ) : (e.shift n).hom = e.hom⟦n⟧' :=
  (rfl)

/-- The homotopy inverse of the shift of a homotopy equivalence is the shifted homotopy
inverse. -/
@[simp]
theorem shift_inv (e : HomotopyEquiv K L) (n : ℤ) : (e.shift n).inv = e.inv⟦n⟧' :=
  (rfl)

end HomotopyEquiv

namespace CategoryTheory.ShortComplex.Splitting

open CochainComplex HomComplex CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {S : ShortComplex (CochainComplex C ℤ)} (σ : S.Splitting)

/-- For a short complex of cochain complexes `S` split by chain maps, the mapping cone of the split
epimorphism `S.g` is homotopy equivalent to `S.X₁⟦1⟧`. This is dual to
`CategoryTheory.ShortComplex.Splitting.homotopyCofiberHomotopyEquiv`, which identifies the mapping
cone of `S.f` with `S.X₃`. The map from the cone is the third morphism of the mapping cone triangle
followed by the shifted retraction, and its homotopy inverse is `S.f` shifted into the first
summand of the cone. One composite is the identity, and the other is homotopic to the identity
through the homotopy which sends the `S.X₃`-summand of the cone to its `S.X₂`-summand by `-σ.s`. -/
noncomputable def mappingConeGHomotopyEquiv :
    _root_.HomotopyEquiv (mappingCone S.g) (S.X₁⟦(1 : ℤ)⟧) where
  hom := (mappingCone.triangle S.g).mor₃ ≫ σ.r⟦(1 : ℤ)⟧'
  inv := lift S.g ((Cocycle.ofHom S.f).leftShift 1 1 (zero_add 1)) 0
    (by simp [← Cochain.leftShift_comp_zero_cochain, ← Cochain.ofHom_comp])
  homotopyInvHomId := _root_.Homotopy.ofEq (by
    have hfr (k : ℤ) : S.f.f k ≫ σ.r.f k = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, σ.f_r, HomologicalComplex.id_f]
    ext n
    simp [lift_f _ _ _ _ _ (n + 1) rfl,
      (Cochain.ofHom S.f).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by lia), hfr])
  homotopyHomInvId := (Cochain.equivHomotopy _ _).symm
    ⟨-(snd S.g).comp ((Cochain.ofHom σ.s).comp (inl S.g) (zero_add (-1))) (zero_add (-1)), by
      have hrf (k : ℤ) : σ.r.f k ≫ S.f.f k = 𝟙 _ - S.g.f k ≫ σ.s.f k := by
        rw [← HomologicalComplex.comp_f, σ.r_f, HomologicalComplex.sub_f_apply,
          HomologicalComplex.id_f, HomologicalComplex.comp_f]
      have hsg (k : ℤ) : σ.s.f k ≫ S.g.f k = 𝟙 _ := by
        rw [← HomologicalComplex.comp_f, σ.s_g, HomologicalComplex.id_f]
      ext n
      simp [ext_to_iff _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl,
        (Cochain.ofHom S.f).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by lia),
        Cochain.comp_v _ _ (add_neg_cancel 1) n (n + 1) n rfl (by lia),
        δ_zero_cochain_comp _ _ _ (neg_add_cancel 1), hrf, hsg]⟩

/-- The map from the mapping cone in `mappingConeGHomotopyEquiv` is the third morphism of the
mapping cone triangle followed by the shifted retraction. -/
@[simp]
theorem mappingConeGHomotopyEquiv_hom :
    (σ.mappingConeGHomotopyEquiv).hom = (mappingCone.triangle S.g).mor₃ ≫ σ.r⟦(1 : ℤ)⟧' :=
  (rfl)

/-- The homotopy inverse in `mappingConeGHomotopyEquiv` is `S.f` shifted into the first summand of
the mapping cone. -/
@[simp]
theorem mappingConeGHomotopyEquiv_inv :
    (σ.mappingConeGHomotopyEquiv).inv =
      lift S.g ((Cocycle.ofHom S.f).leftShift 1 1 (zero_add 1)) 0
        (by simp [← Cochain.leftShift_comp_zero_cochain, ← Cochain.ofHom_comp]) :=
  (rfl)

end CategoryTheory.ShortComplex.Splitting
