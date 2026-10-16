/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.CategoryTheory.DG.Functor
public import TauCeti.CategoryTheory.DG.HomComplexData

/-!
# The shift closure of a differential graded category

For a differential graded category `C`, the shift closure `TauCeti.DGShiftClosure C` adjoins a
formal shift `X[r]` of every object `X` by every integer `r`.  Its Hom complexes are shifts of
those of `C`:

`Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`,

with Mathlib's cochain-shift convention `K[a]^p = K^(p + a)` and differential `(-1)^a d_K`.  So a
morphism `X[r] ⟶ Y[s]` of degree `p` is a morphism `X ⟶ Y` of degree `p + s - r`
(`TauCeti.DGShiftClosure.dgHomEquiv`), and the differential of the shift closure is
`(-1)^(s - r)` times the differential of `C`.

Composition carries a sign.  In Mathlib's enriched factor order, a degree-`p` morphism
`f : X[r] ⟶ Y[s]` followed by `g : Y[s] ⟶ Z[t]` composes to
`(-1)^((t - s) * (p + s - r)) • dgComp f g`.  In Keller's order, where
`g ∘ f = (-1)^(p * q) • dgComp f g` for `g` of degree `q`, the sign becomes `(-1)^((s - r) * q)`.
These are the signs for which the formal shifts of cochain complexes are Mathlib's shifted
complexes `K⟦r⟧`, with `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)` multiplying the underlying cochain
by `(-1)^(r * p)`: see `TauCeti/CategoryTheory/DG/ShiftClosure/CochainComplex.lean`.

The shift closure is the home of the matrix entries of one-sided twisted complexes, the objects
`(⊕ᵢ Xᵢ[rᵢ], δ)` of the pretriangulated envelope of Bondal and Kapranov.

## Main definitions

* `TauCeti.DGShiftClosure`: the objects `X[r]` of the shift closure.
* `TauCeti.DGShiftClosure.homComplexData`: its explicit Hom-complex data.
* `TauCeti.DGShiftClosure.dgHomEquiv`: degree-`n` morphisms `X[r] ⟶ Y[s]` are degree-`n + s - r`
  morphisms `X ⟶ Y`.
* `TauCeti.DGShiftClosure.ι`: the DG functor `X ↦ X[0]`.

## Main results

* `TauCeti.DGShiftClosure.dgHomEquiv_dgDifferential`: the differential is `(-1)^(s - r) d`.
* `TauCeti.DGShiftClosure.dgHomEquiv_dgComp`: composition carries the sign
  `(-1)^((t - s) * (p + s - r))`.
* `TauCeti.DGShiftClosure.dgHomEquiv_negOnePow_smul_dgComp`: in Keller's order the sign is
  `(-1)^((s - r) * q)`.
* `TauCeti.DGShiftClosure.dgHomEquiv_dgId`: the identity of `X[r]` is the identity of `X`.
* `TauCeti.DGShiftClosure.isIso_ι_map`: `X ↦ X[0]` is an isomorphism on Hom complexes.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u

/-- The objects of the **shift closure** of a differential graded category on the objects `C`:
an object `X` of `C` together with an integer `r`, standing for the formal shift `X[r]`.  The
Hom complexes are `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`; see
`TauCeti.DGShiftClosure.homComplexData`. -/
@[ext]
structure DGShiftClosure (C : Type u) where
  /-- The underlying object `X` of the shifted object `X[r]`. -/
  obj : C
  /-- The shift `r` of the shifted object `X[r]`. -/
  shift : ℤ

namespace DGShiftClosure

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Degree transport -/

/-- Transport of a homogeneous morphism of `C` along an equality of degrees. -/
private noncomputable def castDeg {X Y : C} {p p' : ℤ} (hp : p = p') :
    DGHom R p X Y →ₗ[R] DGHom R p' X Y :=
  ((dgHomComplex R X Y).XIsoOfEq hp).hom.hom

private theorem castDeg_self {X Y : C} {p : ℤ} (hp : p = p) (f : DGHom R p X Y) :
    castDeg R hp f = f := by
  simp [castDeg]

private theorem castDeg_dgComp {X Y Z : C} {p p' q n n' : ℤ} (hp : p = p') (hn : n = n')
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p' + q = n') :
    dgComp R (castDeg R hp f) g h = castDeg R hn (dgComp R f g (by omega)) := by
  subst hp hn
  simp [castDeg]

private theorem dgComp_castDeg {X Y Z : C} {p q q' n n' : ℤ} (hq : q = q') (hn : n = n')
    (f : DGHom R p X Y) (g : DGHom R q Y Z) (h : p + q' = n') :
    dgComp R f (castDeg R hq g) h = castDeg R hn (dgComp R f g (by omega)) := by
  subst hq hn
  simp [castDeg]

private theorem d_castDeg {X Y : C} {a b a' b' : ℤ} (h : a = b) (h' : a' = b')
    (f : DGHom R a X Y) :
    ((dgHomComplex R X Y).d b b').hom (castDeg R h f) =
      castDeg R h' (((dgHomComplex R X Y).d a a').hom f) := by
  subst h h'
  simp [castDeg]

/-! ### The Hom-complex data -/

/-- The Hom complex `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]` of the shift closure. -/
private abbrev homComplex (X Y : DGShiftClosure C) : CochainComplex (ModuleCat.{v} R) ℤ :=
  (dgHomComplex R X.obj Y.obj)⟦Y.shift - X.shift⟧

/-- The sign `(-1)^((t - s) * (p + s - r))` of the composite of a degree-`p` morphism
`X[r] ⟶ Y[s]` followed by a morphism `Y[s] ⟶ Z[t]`. -/
private abbrev compSign (X Y Z : DGShiftClosure C) (p : ℤ) : ℤˣ :=
  ((Z.shift - Y.shift) * (p + (Y.shift - X.shift))).negOnePow

/-- Composition in the shift closure: the composition of `C` on the underlying morphisms, with
the sign `TauCeti.DGShiftClosure.compSign`. -/
private noncomputable def comp {X Y Z : DGShiftClosure C} (p q n : ℤ) (h : p + q = n) :
    (homComplex R X Y).X p →ₗ[R] (homComplex R Y Z).X q →ₗ[R] (homComplex R X Z).X n :=
  compSign X Y Z p • TensorProduct.curry
    (dgCompMap R X.obj Y.obj Z.obj (p + (Y.shift - X.shift)) (q + (Z.shift - Y.shift))
      (n + (Z.shift - X.shift)) (by omega)).hom

private theorem comp_apply {X Y Z : DGShiftClosure C} (p q n : ℤ) (h : p + q = n)
    (f : (homComplex R X Y).X p) (g : (homComplex R Y Z).X q) :
    comp R p q n h f g = compSign X Y Z p • dgComp R (n := n + (Z.shift - X.shift))
      (p := p + (Y.shift - X.shift)) (q := q + (Z.shift - Y.shift)) f g (by omega) := by
  rw [comp, LinearMap.smul_apply, LinearMap.smul_apply, TensorProduct.curry_apply,
    dgCompMap_tmul]

/-- The **explicit Hom-complex data of the shift closure**: `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`,
whose differential is `(-1)^(s - r) d`, with composition the composition of `C` multiplied by
`(-1)^((t - s) * (p + s - r))` and identity the identity of `C`. -/
noncomputable def homComplexData : DGCategoryData R (DGShiftClosure C) where
  hom := homComplex R
  comp := comp R
  id X := castDeg R (p' := 0 + (X.shift - X.shift)) (by rw [sub_self, add_zero]) (dgId R X.obj)
  d_comp {X Y Z p q n} h f g := by
    simp only [comp_apply, CochainComplex.shiftFunctor_obj_d', ModuleCat.hom_smul,
      LinearMap.smul_apply, map_zsmul_unit]
    rw [dgHomComplex_d_dgComp R (p' := p + 1 + (Y.shift - X.shift))
      (q' := q + 1 + (Z.shift - Y.shift)) (by omega) (by omega) (by omega)]
    simp only [smul_add, smul_smul]
    congr 2 <;> simp only [compSign, ← Int.negOnePow_add] <;> rw [Int.negOnePow_eq_iff]
    · exact ⟨0, by ring⟩
    · exact ⟨Y.shift - X.shift, by ring⟩
  comp_assoc {W X Y Z p q r pq qr n} hpq hqr h f g k := by
    simp only [comp_apply, units_smul_dgComp, dgComp_units_smul, smul_smul]
    rw [dgComp_assoc R (p := p + (X.shift - W.shift)) (q := q + (Y.shift - X.shift))
      (r := r + (Z.shift - Y.shift)) (pq := pq + (Y.shift - W.shift))
      (qr := qr + (Z.shift - X.shift)) f g k (by omega) (by omega) (by omega)]
    congr 1
    simp only [compSign, ← Int.negOnePow_add]
    congr 1
    subst hpq
    ring
  id_comp {X Y q} g := by
    rw [comp_apply, castDeg_dgComp R (p := 0) (q := q + (Y.shift - X.shift))
      (n := q + (Y.shift - X.shift)) (by rw [sub_self, add_zero]) rfl, dgId_dgComp, castDeg_self]
    simp [compSign]
  comp_id {X Y p} f := by
    rw [comp_apply, dgComp_castDeg R (p := p + (Y.shift - X.shift)) (q := 0)
      (n := p + (Y.shift - X.shift)) (by rw [sub_self, add_zero]) rfl, dgComp_dgId, castDeg_self]
    simp [compSign]

/-- The **shift closure** of a differential graded category: the objects `X[r]`, with Hom
complexes `Hom(X[r], Y[s]) = Hom(X, Y)[s - r]`. -/
noncomputable instance : DGCategory R (DGShiftClosure C) :=
  (homComplexData R).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- The Hom complex `Hom(X[r], Y[s])` of the shift closure is the shifted Hom complex
`Hom(X, Y)[s - r]`. -/
theorem dgHomComplex_eq (X Y : DGShiftClosure C) :
    dgHomComplex R X Y = (dgHomComplex R X.obj Y.obj)⟦Y.shift - X.shift⟧ :=
  (rfl)

/-- A morphism `X[r] ⟶ Y[s]` of degree `n` in the shift closure is a morphism `X ⟶ Y` of degree
`n + (s - r)` in `C`. -/
noncomputable def dgHomEquiv (X Y : DGShiftClosure C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R (n + (Y.shift - X.shift)) X.obj Y.obj :=
  LinearEquiv.refl R _

/-- The differential of the shift closure is `(-1)^(s - r)` times the differential of `C`. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {X Y : DGShiftClosure C} (n : ℤ) (f : DGHom R n X Y) :
    dgHomEquiv R X Y (n + 1) (dgDifferential R n f) =
      (Y.shift - X.shift).negOnePow • ((dgHomComplex R X.obj Y.obj).d (n + (Y.shift - X.shift))
        (n + 1 + (Y.shift - X.shift))).hom (dgHomEquiv R X Y n f) := by
  refine ((homComplexData R).dgDifferential_toDGCategory n f).trans ?_
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (CochainComplex.shiftFunctor_obj_d' (dgHomComplex R X.obj Y.obj) (Y.shift - X.shift) n
      (n + 1))) f

/-- Composition in the shift closure: a degree-`p` morphism `f : X[r] ⟶ Y[s]` followed by
`g : Y[s] ⟶ Z[t]` is the composite of the underlying morphisms of `C`, with the sign
`(-1)^((t - s) * (p + s - r))`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {X Y Z : DGShiftClosure C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgHomEquiv R X Z n (dgComp R f g h) =
      ((Z.shift - Y.shift) * (p + (Y.shift - X.shift))).negOnePow •
        dgComp R (dgHomEquiv R X Y p f) (dgHomEquiv R Y Z q g) (by omega) :=
  ((homComplexData R).dgComp_toDGCategory f g h).trans (comp_apply R p q n h f g)

/-- **The shift-closure composition sign in Keller's order**: for `f : X[r] ⟶ Y[s]` of degree
`p` and `g : Y[s] ⟶ Z[t]` of degree `q`, the Keller-ordered composite
`g ∘ f = (-1)^(p * q) • dgComp f g` is the Keller-ordered composite of the underlying morphisms
of `C`, of degrees `p + s - r` and `q + t - s`, multiplied by `(-1)^((s - r) * q)`. -/
theorem dgHomEquiv_negOnePow_smul_dgComp {X Y Z : DGShiftClosure C} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (h : p + q = n) :
    dgHomEquiv R X Z n ((p * q).negOnePow • dgComp R f g h) =
      ((Y.shift - X.shift) * q).negOnePow •
        ((p + (Y.shift - X.shift)) * (q + (Z.shift - Y.shift))).negOnePow •
          dgComp R (dgHomEquiv R X Y p f) (dgHomEquiv R Y Z q g) (by omega) := by
  rw [map_zsmul_unit, dgHomEquiv_dgComp, smul_smul, smul_smul, ← Int.negOnePow_add,
    ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨-((Y.shift - X.shift) * q), by ring⟩

/-- The identity of `X[r]` in the shift closure is the identity of `X`. -/
@[simp↓]
theorem dgHomEquiv_dgId (X : DGShiftClosure C) :
    dgHomEquiv R X X 0 (dgId R X) =
      ((dgHomComplex R X.obj X.obj).XIsoOfEq (by rw [sub_self, add_zero])).hom (dgId R X.obj) :=
  (homComplexData R).dgId_toDGCategory X

/-! ### The inclusion `X ↦ X[0]` -/

/-- The action of the inclusion `X ↦ X[0]` on morphisms of degree `n`: a degree-`n` morphism
`X ⟶ Y` of `C` is a degree-`n` morphism `X[0] ⟶ Y[0]` of the shift closure. -/
noncomputable def ιHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (⟨X, 0⟩ : DGShiftClosure C) ⟨Y, 0⟩ :=
  ((dgHomComplex R X Y).XIsoOfEq (by rw [sub_self, add_zero])).toLinearEquiv.trans
    (dgHomEquiv R ⟨X, 0⟩ ⟨Y, 0⟩ n).symm

/-- The inclusion `X ↦ X[0]` does not change the underlying morphism. -/
@[simp]
theorem dgHomEquiv_ιHomEquiv {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgHomEquiv R ⟨X, 0⟩ ⟨Y, 0⟩ n (ιHomEquiv R X Y n f) =
      ((dgHomComplex R X Y).XIsoOfEq (by rw [sub_self, add_zero])).hom f := by
  simp [ιHomEquiv]

/-- The DG functor `X ↦ X[0]` from a differential graded category to its shift closure. -/
-- The body is exposed so that `(ι R).obj X` is definitionally `⟨X, 0⟩`, as for
-- `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def ι : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C (DGShiftClosure C) :=
  EnrichedFunctor.ofDGMap (fun X ↦ ⟨X, 0⟩) (fun {X Y} n ↦ (ιHomEquiv R X Y n).toLinearMap)
    (fun {X Y} n f ↦ (dgHomEquiv R _ _ (n + 1)).injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgHomEquiv_dgDifferential,
        dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv]
      simp only [sub_self, Int.negOnePow_zero, one_smul]
      exact (d_castDeg R _ _ f).symm)
    (fun X ↦ (dgHomEquiv R _ _ 0).injective <| by
      rw [LinearEquiv.coe_coe, dgHomEquiv_ιHomEquiv, dgHomEquiv_dgId])
    (fun {X Y Z p q n} f g h ↦ (dgHomEquiv R _ _ n).injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgHomEquiv_dgComp,
        dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv, dgHomEquiv_ιHomEquiv]
      simp only [sub_self, zero_mul, Int.negOnePow_zero, one_smul]
      exact ((castDeg_dgComp R _ (by rw [sub_self, add_zero]) f _ _).trans
        (congrArg _ ((dgComp_castDeg R _ rfl f g _).trans (castDeg_self R _ _)))).symm)

/-- The inclusion sends `X` to `X[0]`. -/
@[simp]
theorem ι_obj (X : C) : (ι R).obj X = ⟨X, 0⟩ :=
  rfl

/-- The inclusion acts on morphisms by `TauCeti.DGShiftClosure.ιHomEquiv`. -/
theorem dgMap_ι {X Y : C} {n : ℤ} (f : DGHom R n X Y) : (ι R).dgMap n f = ιHomEquiv R X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- The inclusion `X ↦ X[0]` is an isomorphism on Hom complexes: `C` is a full DG subcategory of
its shift closure. -/
instance isIso_ι_map (X Y : C) : IsIso ((ι R).map X Y) :=
  have (n : ℤ) : IsIso (((ι R).map X Y).f n) := (ιHomEquiv R X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

end DGShiftClosure

end TauCeti
