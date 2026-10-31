/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# The ordered Čech complex

Let `C` be a category with finite products, let `U : ι → C` be a family of objects indexed by a
preordered type `ι`, and let `P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category
with products. Mathlib's Čech complex `Č(U, P)` (`CategoryTheory.cechComplexFunctor`) has in
degree `n` the product, over all tuples `a : Fin (n + 1) → ι`, of `P(U (a 0) × ⋯ × U (a n))`,
including tuples with repeated indices. The *ordered* Čech complex `Čₒ(U, P)` keeps only the
strictly increasing tuples `a 0 < ⋯ < a n`, with the same alternating differential: the factor
indexed by `k` of the differential of a cochain `s` is
`∑ m, (-1) ^ m • s (k ∘ m.succAbove)`, restricted from `∏ⱼ U (k (m.succAbove j))` to
`∏ⱼ U (k j)`. Deleting an entry of a strictly increasing tuple leaves a strictly increasing tuple,
so this differential only involves factors of `Čₒ(U, P)`.

For a linear order on `ι`, for instance a well-ordering of the index set of an open cover, this is
the ordered Čech complex of the Stacks Project. It is much smaller than `Č(U, P)`: when `ι` has
`N` elements its terms vanish in degrees `n ≥ N` (`isZero_orderedCechComplexFunctor_obj_X`), and
for the empty family it is zero in every degree. For a cover by two opens indexed by `0 < 1` it is
`P(U 0) × P(U 1) ⟶ P(U 0 × U 1)`, `(a, b) ↦ b - a` (suitably restricted), and nothing else.

Restricting a Čech cochain to the strictly increasing tuples is a map of complexes
`Č(U, P) ⟶ Čₒ(U, P)`, natural in `P` (`toOrderedCechComplex`), which is split surjective in every
degree. That the differential of `Čₒ(U, P)` squares to zero is deduced from this: precomposed with
the surjection from `Č(U, P)`, it is the image of the square of the differential of `Č(U, P)`.

## Main definitions

* `TauCeti.CategoryTheory.orderedCechComplexFunctor U`: the ordered Čech complex functor
  `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` of the family `U`.
* `TauCeti.CategoryTheory.toOrderedCechComplex U`: the natural map `Č(U, P) ⟶ Čₒ(U, P)` which
  restricts a cochain to the strictly increasing tuples.

## Main results

* `TauCeti.CategoryTheory.orderedCechComplexFunctor_obj_d_comp_π`: the differential of the
  ordered Čech complex is the alternating sum of the restrictions along the coface maps.
* `TauCeti.CategoryTheory.toOrderedCechComplex_app_f_π`: the factor of `toOrderedCechComplex`
  indexed by a strictly increasing tuple is the projection onto that factor of `Č(U, P)`.
* `TauCeti.CategoryTheory.isZero_orderedCechComplexFunctor_obj_X`: for a family indexed by a
  finite type with at most `n` elements, the ordered Čech complex vanishes in degree `n`.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.23 (alternating Čech complexes),
  Definitions 20.23.1–20.23.2.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} [Preorder ι] (U : ι → C)

/-! ### The terms and the differential -/

/-- The restriction of a degree `n` cochain of the Čech complex to the strictly increasing tuples:
the degree `n` component of `toOrderedCechComplex`. -/
private def toOrderedCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) ⟶
      ∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.lift fun a ↦ Pi.π _ a.1

omit [Preadditive A] in
@[reassoc]
private lemma toOrderedCechX_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    toOrderedCechX U P n ≫ Pi.π _ a = Pi.π _ a.1 :=
  Pi.lift_comp_π _ _

/-- A section of `toOrderedCechX`: it extends a cochain on the strictly increasing tuples by
zero. -/
private lemma isSplitEpi_toOrderedCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    IsSplitEpi (toOrderedCechX U P n) := by
  classical
  refine IsSplitEpi.mk' ⟨Pi.lift (f := fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))))
    fun a ↦ if h : StrictMono a then
      Pi.π (fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))))
        ⟨a, h⟩
    else 0, Pi.hom_ext _ _ fun a ↦ ?_⟩
  rw [Category.assoc, toOrderedCechX_π, Pi.lift_comp_π, dite_eq_left a.2, Category.id_comp]

/-- The differential of the Čech complex, with source and target the products which define its
terms. -/
private abbrev cechD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) ⟶
      ∏ᶜ fun a : Fin (n + 2) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  ((cechComplexFunctor U).obj P).d n (n + 1)

omit [Preorder ι] in
/-- `cechComplexFunctor_obj_d_comp_π`, stated through `cechD`. -/
private lemma cechD_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (k : Fin (n + 2) → ι) :
    cechD U P n ≫ Pi.π _ k = ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
      (Pi.π _ (k ∘ m.succAbove) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op) :=
  cechComplexFunctor_obj_d_comp_π U P n k

omit [Preorder ι] in
@[reassoc]
private lemma cechD_comp_cechD (P : Cᵒᵖ ⥤ A) (n : ℕ) : cechD U P n ≫ cechD U P (n + 1) = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _

/-- The differential of the ordered Čech complex `Čₒ(U, P)` from degree `n` to degree `n + 1`.
Its factor indexed by a strictly increasing tuple `k` is the alternating sum, over the entries `m`
of `k`, of the factor indexed by `k ∘ m.succAbove`, restricted along the projection
`U (k 0) × ⋯ × U (k (n + 1)) ⟶ ∏ⱼ U (k (m.succAbove j))` (`orderedCechComplexD_π`). -/
def orderedCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) ⟶
      ∏ᶜ fun a : {a : Fin (n + 2) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.lift fun k ↦ ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
    (Pi.π _ (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
        {a : Fin (n + 1) → ι // StrictMono a}) ≫
      P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op)

/-- The factor indexed by `k` of the differential of the ordered Čech complex. -/
@[reassoc]
theorem orderedCechComplexD_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (k : {a : Fin (n + 2) → ι // StrictMono a}) :
    orderedCechComplexD U P n ≫ Pi.π _ k = ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
      (Pi.π _ (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
          {a : Fin (n + 1) → ι // StrictMono a}) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op) :=
  Pi.lift_comp_π _ _

/-- Restriction to the strictly increasing tuples commutes with the differentials. -/
@[reassoc]
private lemma toOrderedCechX_comp_orderedCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    toOrderedCechX U P n ≫ orderedCechComplexD U P n =
      cechD U P n ≫ toOrderedCechX U P (n + 1) := by
  refine Pi.hom_ext _ _ fun k ↦ ?_
  rw [Category.assoc, Category.assoc, toOrderedCechX_π, orderedCechComplexD_π,
    Preadditive.comp_sum, cechD_π]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Preadditive.comp_zsmul, toOrderedCechX_π_assoc]

/-- The differential of the ordered Čech complex squares to zero. -/
@[reassoc (attr := simp)]
theorem orderedCechComplexD_comp_orderedCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    orderedCechComplexD U P n ≫ orderedCechComplexD U P (n + 1) = 0 := by
  have := isSplitEpi_toOrderedCechX U P n
  rw [← cancel_epi (toOrderedCechX U P n), comp_zero,
    toOrderedCechX_comp_orderedCechComplexD_assoc, toOrderedCechX_comp_orderedCechComplexD,
    cechD_comp_cechD_assoc, zero_comp]

/-- The map of products induced by a morphism of presheaves commutes with the differentials of
the ordered Čech complexes. -/
private lemma pi_map_comp_orderedCechComplexD {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    Limits.Pi.map (fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
        α.app (op (∏ᶜ fun j ↦ U (a.1 j)))) ≫ orderedCechComplexD U Q n =
      orderedCechComplexD U P n ≫ Limits.Pi.map fun a : {a : Fin (n + 2) → ι // StrictMono a} ↦
        α.app (op (∏ᶜ fun j ↦ U (a.1 j))) := by
  refine Pi.hom_ext _ _ fun k ↦ ?_
  rw [Category.assoc, orderedCechComplexD_π, Preadditive.comp_sum, Category.assoc, Pi.map_π,
    orderedCechComplexD_π_assoc, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Pi.map_π_assoc]
  simp only [Category.assoc, NatTrans.naturality]
  rfl

omit [Preadditive A] in
/-- Restriction to the strictly increasing tuples is natural in the presheaf. -/
private lemma pi_map_comp_toOrderedCechX {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    Limits.Pi.map (fun a : Fin (n + 1) → ι ↦ α.app (op (∏ᶜ fun j ↦ U (a j)))) ≫
        toOrderedCechX U Q n =
      toOrderedCechX U P n ≫ Limits.Pi.map fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
        α.app (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.hom_ext _ _ fun a ↦ by
    rw [Category.assoc, Category.assoc, toOrderedCechX_π, Pi.map_π, Pi.map_π,
      toOrderedCechX_π_assoc]

/-! ### The ordered Čech complex functor -/

/-- The ordered Čech complex functor of a family `U : ι → C` indexed by a preordered type. It sends
a presheaf `P` to the cochain complex `Čₒ(U, P)` whose degree `n` term is the product, over the
strictly increasing tuples `a : Fin (n + 1) → ι`, of `P(U (a 0) × ⋯ × U (a n))`, with the
alternating differential `orderedCechComplexD` (`orderedCechComplexFunctor_obj_d_comp_π`). A
morphism of presheaves acts factorwise (`orderedCechComplexFunctor_map_f_π`).

The body is exposed, as for Mathlib's `CategoryTheory.cechComplexFunctor`, so that the terms of the
complex are seen to be products and `Pi.π` and `Pi.lift` apply to them. -/
@[expose]
def orderedCechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ where
  obj P := CochainComplex.of
    (fun n ↦ ∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))))
    (orderedCechComplexD U P) (orderedCechComplexD_comp_orderedCechComplexD U P)
  map α := CochainComplex.ofHom
    (fun n ↦ Limits.Pi.map fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
      α.app (op (∏ᶜ fun j ↦ U (a.1 j))))
    fun n ↦ by
      simp only [CochainComplex.of_d]
      exact pi_map_comp_orderedCechComplexD U α n
  map_id P := by
    ext n : 2
    simp
  map_comp α β := by
    ext n : 2
    simp

/-- The differential of the ordered Čech complex from degree `n` to degree `n + 1` is
`orderedCechComplexD`. -/
@[simp]
theorem orderedCechComplexFunctor_obj_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((orderedCechComplexFunctor U).obj P).d n (n + 1) = orderedCechComplexD U P n := by
  dsimp only [orderedCechComplexFunctor]
  exact CochainComplex.of_d _ _ n

/-- The differential of the ordered Čech complex is the alternating sum of the restrictions along
the coface maps: the factor of `((orderedCechComplexFunctor U).obj P).d n (n + 1)` indexed by a
strictly increasing tuple `k` is the alternating sum over `m` of the factor indexed by
`k ∘ m.succAbove`, restricted along the projection
`U (k 0) × ⋯ × U (k (n + 1)) ⟶ ∏ⱼ U (k (m.succAbove j))`. -/
@[reassoc]
theorem orderedCechComplexFunctor_obj_d_comp_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : {a : Fin (n + 2) → ι // StrictMono a}) :
    ((orderedCechComplexFunctor U).obj P).d n (n + 1) ≫ Pi.π _ k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        (Pi.π _ (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
            {a : Fin (n + 1) → ι // StrictMono a}) ≫
          P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op) :=
  by rw [orderedCechComplexFunctor_obj_d]; exact orderedCechComplexD_π U P n k

/-- A morphism of presheaves `α : P ⟶ Q` acts on the ordered Čech complexes factorwise: the factor
of `((orderedCechComplexFunctor U).map α).f n` indexed by `a` is the component of `α` at
`U (a 0) × ⋯ × U (a n)`. -/
@[reassoc]
theorem orderedCechComplexFunctor_map_f_π {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    ((orderedCechComplexFunctor U).map α).f n ≫ Pi.π _ a =
      Pi.π _ a ≫ α.app (op (∏ᶜ fun j ↦ U (a.1 j))) := by
  dsimp only [orderedCechComplexFunctor]
  exact Pi.map_π _ a

/-- Two morphisms into a term of the ordered Čech complex are equal as soon as their factors
indexed by all strictly increasing tuples are. -/
theorem orderedCechComplexFunctor_obj_X_hom_ext (P : Cᵒᵖ ⥤ A) (n : ℕ) {W : A}
    {f g : W ⟶ ((orderedCechComplexFunctor U).obj P).X n}
    (h : ∀ a : {a : Fin (n + 1) → ι // StrictMono a}, f ≫ Pi.π _ a = g ≫ Pi.π _ a) : f = g :=
  Pi.hom_ext _ _ h

/-- For a family indexed by a finite type with at most `n` elements, the ordered Čech complex
vanishes in degree `n`: there is no strictly increasing tuple `Fin (n + 1) → ι`. In particular,
for the empty family the ordered Čech complex is zero in every degree. -/
theorem isZero_orderedCechComplexFunctor_obj_X [Finite ι] {n : ℕ} (hn : Nat.card ι ≤ n)
    (P : Cᵒᵖ ⥤ A) : IsZero (((orderedCechComplexFunctor U).obj P).X n) := by
  have (a : {a : Fin (n + 1) → ι // StrictMono a}) : False := by
    have := Nat.card_le_card_of_injective a.1 a.2.injective
    rw [Nat.card_fin] at this
    omega
  exact (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun a ↦ (this a).elim)

/-! ### Restriction to the strictly increasing tuples -/

/-- The component at `P` of `toOrderedCechComplex`. -/
private def toOrderedCechComplexApp (P : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj P ⟶ (orderedCechComplexFunctor U).obj P :=
  CochainComplex.ofHom (toOrderedCechX U P) fun n ↦ by
    rw [orderedCechComplexFunctor_obj_d]
    exact toOrderedCechX_comp_orderedCechComplexD U P n

@[reassoc]
private lemma toOrderedCechComplexApp_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    (toOrderedCechComplexApp U P).f n ≫ Pi.π _ a = Pi.π _ a.1 :=
  toOrderedCechX_π U P n a

/-- The map of complexes `Č(U, P) ⟶ Čₒ(U, P)` from the Čech complex to the ordered Čech complex,
natural in the presheaf `P`. It restricts a cochain to the strictly increasing tuples: its factor
indexed by such a tuple `a` is the projection of `Č(U, P)` onto the factor indexed by `a`
(`toOrderedCechComplex_app_f_π`). It is split surjective in every degree. -/
def toOrderedCechComplex : cechComplexFunctor U ⟶ orderedCechComplexFunctor (A := A) U where
  app := toOrderedCechComplexApp U
  naturality P Q α := by
    ext n : 1
    -- in degree `n`, both maps of presheaves act factorwise by `Limits.Pi.map`
    exact pi_map_comp_toOrderedCechX U α n

/-- The factor of `toOrderedCechComplex` indexed by a strictly increasing tuple `a` is the
projection of the Čech complex onto the factor indexed by `a`. -/
@[simp, reassoc]
theorem toOrderedCechComplex_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    ((toOrderedCechComplex U).app P).f n ≫ Pi.π _ a = Pi.π _ a.1 :=
  toOrderedCechComplexApp_f_π U P n a

/-- Restriction to the strictly increasing tuples is split surjective in every degree: a cochain on
the strictly increasing tuples extends by zero to a Čech cochain. -/
instance (P : Cᵒᵖ ⥤ A) (n : ℕ) : IsSplitEpi (((toOrderedCechComplex U).app P).f n) :=
  isSplitEpi_toOrderedCechX U P n

end TauCeti.CategoryTheory
