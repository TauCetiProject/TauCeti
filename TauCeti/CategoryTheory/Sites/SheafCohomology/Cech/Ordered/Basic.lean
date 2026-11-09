/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.Homology.OrderedCech
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
import Mathlib.Order.Hom.PowersetCard
import TauCeti.CategoryTheory.Limits.Shapes.Products
import TauCeti.Data.Finset.Sort
import TauCeti.Order.Hom.Basic

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
`N` elements its terms vanish in degrees `n ≥ N` (`isZero_strictMonoCechComplexFunctor_obj_X`), and
for the empty family it is zero in every degree. For a cover by two opens indexed by `0 < 1` it is
`P(U 0) × P(U 1) ⟶ P(U 0 × U 1)`, `(a, b) ↦ b - a` (suitably restricted), and nothing else.

Strictly increasing tuples are then the same as finite sets of indices, and `Čₒ(U, P)` is
isomorphic (`strictMonoCechComplexIso`) to the ordered Čech complex
`CategoryTheory.Functor.orderedCechComplex` of the functor `s ↦ P(∏_{i ∈ s} U i)` on finite sets of
indices (`presheafCechFunctor`), formed in `Aᵒᵖ` and brought back to `A`; the description of the
two-index case above is `CategoryTheory.Functor.ι_orderedCechComplex_d_pair` on that side. The
tuple indexing of `Čₒ(U, P)` is what makes it a quotient of `Č(U, P)` and lets it be defined for a
preorder.

Restricting a Čech cochain to the strictly increasing tuples is a map of complexes
`Č(U, P) ⟶ Čₒ(U, P)`, natural in `P` (`toStrictMonoCechComplex`), which is split surjective in every
degree. That the differential of `Čₒ(U, P)` squares to zero is deduced from this: precomposed with
the surjection from `Č(U, P)`, it is the image of the square of the differential of `Č(U, P)`.

## Main definitions

* `TauCeti.CategoryTheory.strictMonoCechComplexFunctor U`: the ordered Čech complex functor
  `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` of the family `U`.
* `TauCeti.CategoryTheory.toStrictMonoCechComplex U`: the natural map `Č(U, P) ⟶ Čₒ(U, P)` which
  restricts a cochain to the strictly increasing tuples.
* `TauCeti.CategoryTheory.strictMonoCechComplexIso U P`: for a linear order on `ι`, the isomorphism
  of `Čₒ(U, P)` with the ordered Čech complex of `presheafCechFunctor U P` indexed by finite sets.

## Main results

* `TauCeti.CategoryTheory.isLimitStrictMonoCechComplexFan`: the degree `n` term of the ordered
  Čech complex is the product of its factors, with projections `strictMonoCechComplexπ`.
* `TauCeti.CategoryTheory.strictMonoCechComplexFunctor_obj_d_comp_π`: the differential of the
  ordered Čech complex is the alternating sum of the restrictions along the coface maps.
* `TauCeti.CategoryTheory.toStrictMonoCechComplex_app_f_π`: the factor of
  `toStrictMonoCechComplex` indexed by a strictly increasing tuple is the projection onto that
  factor of `Č(U, P)`.
* `TauCeti.CategoryTheory.isZero_strictMonoCechComplexFunctor_obj_X`: for a family indexed by a
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
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)

section Preorder

variable [Preorder ι]

/-! ### The terms and the differential -/

/-- The restriction of a degree `n` cochain of the Čech complex to the strictly increasing tuples:
the degree `n` component of `toStrictMonoCechComplex`. -/
private def toStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) ⟶
      ∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.map' Subtype.val fun _ ↦ 𝟙 _

/-- `toStrictMonoCechX` is split surjective, as the reindexing of a product along the injection
`Subtype.val` (`isSplitEpi_piMap'`): a cochain on the strictly increasing tuples extends by zero. -/
private lemma isSplitEpi_toStrictMonoCechX (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    IsSplitEpi (toStrictMonoCechX U P n) :=
  have : Mono (TypeCat.ofHom (Subtype.val : {a : Fin (n + 1) → ι // StrictMono a} → _)) :=
    (mono_iff_injective _).2 Subtype.val_injective
  isSplitEpi_piMap' (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))))
    (TypeCat.ofHom Subtype.val)

/-- The differential of the Čech complex, with source and target the products which define its
terms. -/
private abbrev cechD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) ⟶
      ∏ᶜ fun a : Fin (n + 2) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  ((cechComplexFunctor U).obj P).d n (n + 1)

/-- The differential of the ordered Čech complex `Čₒ(U, P)` from degree `n` to degree `n + 1`.
Its factor indexed by a strictly increasing tuple `k` is the alternating sum, over the entries `m`
of `k`, of the factor indexed by `k ∘ m.succAbove`, restricted along the projection
`U (k 0) × ⋯ × U (k (n + 1)) ⟶ ∏ⱼ U (k (m.succAbove j))` (`strictMonoCechComplexD_π`). -/
private def strictMonoCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) ⟶
      ∏ᶜ fun a : {a : Fin (n + 2) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.lift fun k ↦ ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
    (Pi.π _ (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
        {a : Fin (n + 1) → ι // StrictMono a}) ≫
      P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op)

/-- The factor indexed by `k` of the differential of the ordered Čech complex. -/
@[reassoc]
private lemma strictMonoCechComplexD_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : {a : Fin (n + 2) → ι // StrictMono a}) :
    strictMonoCechComplexD U P n ≫ Pi.π _ k = ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
      (Pi.π _ (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
          {a : Fin (n + 1) → ι // StrictMono a}) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op) :=
  Pi.lift_comp_π _ _

/-- Restriction to the strictly increasing tuples commutes with the differentials. -/
@[reassoc]
private lemma toStrictMonoCechX_comp_strictMonoCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    toStrictMonoCechX U P n ≫ strictMonoCechComplexD U P n =
      cechD U P n ≫ toStrictMonoCechX U P (n + 1) := by
  refine Pi.hom_ext _ _ fun k ↦ ?_
  simp only [toStrictMonoCechX, Category.assoc, Pi.map'_comp_π, Category.comp_id,
    strictMonoCechComplexD_π, Preadditive.comp_sum, Preadditive.comp_zsmul, Pi.map'_comp_π_assoc,
    Category.id_comp]
  exact (cechComplexFunctor_obj_d_comp_π U P n k.1).symm

/-- The differential of the ordered Čech complex squares to zero. -/
private lemma strictMonoCechComplexD_comp_strictMonoCechComplexD (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    strictMonoCechComplexD U P n ≫ strictMonoCechComplexD U P (n + 1) = 0 := by
  have := isSplitEpi_toStrictMonoCechX U P n
  rw [← cancel_epi (toStrictMonoCechX U P n), comp_zero,
    toStrictMonoCechX_comp_strictMonoCechComplexD_assoc,
    toStrictMonoCechX_comp_strictMonoCechComplexD]
  exact (HomologicalComplex.d_comp_d_assoc _ _ _ _ _).trans zero_comp

/-- The map of products induced by a morphism of presheaves commutes with the differentials of
the ordered Čech complexes. -/
private lemma pi_map_comp_strictMonoCechComplexD {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    Limits.Pi.map (fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
        α.app (op (∏ᶜ fun j ↦ U (a.1 j)))) ≫ strictMonoCechComplexD U Q n =
      strictMonoCechComplexD U P n ≫ Limits.Pi.map fun a : {a : Fin (n + 2) → ι // StrictMono a} ↦
        α.app (op (∏ᶜ fun j ↦ U (a.1 j))) := by
  refine Pi.hom_ext _ _ fun k ↦ ?_
  simp only [Category.assoc, strictMonoCechComplexD_π, Preadditive.comp_sum, Pi.map_π,
    strictMonoCechComplexD_π_assoc, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Pi.map_π_assoc, NatTrans.naturality]
  -- the components of `α` on both sides are taken at the same product, written once through the
  -- subtype `⟨k.1 ∘ m.succAbove, _⟩` and once through `k.1 (m.succAbove x)`
  dsimp only [Function.comp_apply]

/-! ### The ordered Čech complex functor -/

/-- The ordered Čech complex functor of a family `U : ι → C` indexed by a preordered type. It sends
a presheaf `P` to the cochain complex `Čₒ(U, P)` whose degree `n` term is the product, over the
strictly increasing tuples `a : Fin (n + 1) → ι`, of `P(U (a 0) × ⋯ × U (a n))`
(`isLimitStrictMonoCechComplexFan`, with projections `strictMonoCechComplexπ`), with the
alternating differential (`strictMonoCechComplexFunctor_obj_d_comp_π`). A morphism of presheaves
acts factorwise (`strictMonoCechComplexFunctor_map_f_π`). -/
def strictMonoCechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ where
  obj P := CochainComplex.of
    (fun n ↦ ∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))))
    (strictMonoCechComplexD U P) (strictMonoCechComplexD_comp_strictMonoCechComplexD U P)
  map α := CochainComplex.ofHom
    (fun n ↦ Limits.Pi.map fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦
      α.app (op (∏ᶜ fun j ↦ U (a.1 j))))
    fun n ↦ by
      simp only [CochainComplex.of_d]
      exact pi_map_comp_strictMonoCechComplexD U α n
  map_id P := by
    ext n : 2
    simp
  map_comp α β := by
    ext n : 2
    simp

/-- The projection of the degree `n` term of the ordered Čech complex `Čₒ(U, P)` onto the factor
`P(U (a 0) × ⋯ × U (a n))` of a strictly increasing tuple `a`. -/
def strictMonoCechComplexπ (P : Cᵒᵖ ⥤ A) {n : ℕ} (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    ((strictMonoCechComplexFunctor U).obj P).X n ⟶ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))) :=
  Pi.π _ a

/-- The morphism into the degree `n` term of the ordered Čech complex `Čₒ(U, P)` with the given
factors. -/
def strictMonoCechComplexLift (P : Cᵒᵖ ⥤ A) {n : ℕ} {W : A}
    (f : ∀ a : {a : Fin (n + 1) → ι // StrictMono a}, W ⟶ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) :
    W ⟶ ((strictMonoCechComplexFunctor U).obj P).X n :=
  Pi.lift f

/-- The morphism `strictMonoCechComplexLift U P f` has factor `f a` at the strictly increasing
tuple `a`. -/
@[reassoc (attr := simp)]
theorem strictMonoCechComplexLift_π (P : Cᵒᵖ ⥤ A) {n : ℕ} {W : A}
    (f : ∀ a : {a : Fin (n + 1) → ι // StrictMono a}, W ⟶ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))))
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    strictMonoCechComplexLift U P f ≫ strictMonoCechComplexπ U P a = f a :=
  Pi.lift_comp_π f a

/-- The projections `strictMonoCechComplexπ` exhibit the degree `n` term of the ordered Čech complex
as the product of the `P(U (a 0) × ⋯ × U (a n))` over the strictly increasing tuples `a`. -/
def isLimitStrictMonoCechComplexFan (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    IsLimit (Fan.mk (((strictMonoCechComplexFunctor U).obj P).X n)
      (strictMonoCechComplexπ U P (n := n))) :=
  productIsProduct _

/-- Two morphisms into a term of the ordered Čech complex are equal as soon as their factors
indexed by all strictly increasing tuples are. -/
@[ext]
theorem strictMonoCechComplexFunctor_obj_X_hom_ext (P : Cᵒᵖ ⥤ A) {n : ℕ} {W : A}
    {f g : W ⟶ ((strictMonoCechComplexFunctor U).obj P).X n}
    (h : ∀ a, f ≫ strictMonoCechComplexπ U P a = g ≫ strictMonoCechComplexπ U P a) : f = g :=
  Pi.hom_ext _ _ h

private lemma strictMonoCechComplexFunctor_obj_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((strictMonoCechComplexFunctor U).obj P).d n (n + 1) = strictMonoCechComplexD U P n := by
  dsimp only [strictMonoCechComplexFunctor]
  exact CochainComplex.of_d _ _ n

/-- The differential of the ordered Čech complex is the alternating sum of the restrictions along
the coface maps: the factor of `((strictMonoCechComplexFunctor U).obj P).d n (n + 1)` indexed by a
strictly increasing tuple `k` is the alternating sum over `m` of the factor indexed by
`k ∘ m.succAbove`, restricted along the projection
`U (k 0) × ⋯ × U (k (n + 1)) ⟶ ∏ⱼ U (k (m.succAbove j))`. -/
@[reassoc]
theorem strictMonoCechComplexFunctor_obj_d_comp_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : {a : Fin (n + 2) → ι // StrictMono a}) :
    ((strictMonoCechComplexFunctor U).obj P).d n (n + 1) ≫ strictMonoCechComplexπ U P k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        (strictMonoCechComplexπ U P
            (⟨k.1 ∘ m.succAbove, k.2.comp (Fin.strictMono_succAbove m)⟩ :
              {a : Fin (n + 1) → ι // StrictMono a}) ≫
          P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k.1 j)) (m.succAbove x)).op) := by
  rw [strictMonoCechComplexFunctor_obj_d]
  exact strictMonoCechComplexD_π U P n k

/-- A morphism of presheaves `α : P ⟶ Q` acts on the ordered Čech complexes factorwise: the factor
of `((strictMonoCechComplexFunctor U).map α).f n` indexed by `a` is the component of `α` at
`U (a 0) × ⋯ × U (a n)`. -/
@[reassoc (attr := simp)]
theorem strictMonoCechComplexFunctor_map_f_π {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    ((strictMonoCechComplexFunctor U).map α).f n ≫ strictMonoCechComplexπ U Q a =
      strictMonoCechComplexπ U P a ≫ α.app (op (∏ᶜ fun j ↦ U (a.1 j))) := by
  dsimp only [strictMonoCechComplexFunctor, strictMonoCechComplexπ]
  exact Pi.map_π _ a

/-- For a family indexed by a finite type with at most `n` elements, the ordered Čech complex
vanishes in degree `n`: there is no strictly increasing tuple `Fin (n + 1) → ι`. In particular,
for the empty family the ordered Čech complex is zero in every degree. -/
theorem isZero_strictMonoCechComplexFunctor_obj_X [Finite ι] {n : ℕ} (hn : Nat.card ι ≤ n)
    (P : Cᵒᵖ ⥤ A) : IsZero (((strictMonoCechComplexFunctor U).obj P).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext a
  have := Nat.card_le_card_of_injective a.1 a.2.injective
  rw [Nat.card_fin] at this
  omega

/-! ### Restriction to the strictly increasing tuples -/

/-- The component at `P` of `toStrictMonoCechComplex`. -/
private def toStrictMonoCechComplexApp (P : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor U).obj P ⟶ (strictMonoCechComplexFunctor U).obj P :=
  CochainComplex.ofHom (toStrictMonoCechX U P) fun n ↦ by
    rw [strictMonoCechComplexFunctor_obj_d]
    exact toStrictMonoCechX_comp_strictMonoCechComplexD U P n

@[reassoc]
private lemma toStrictMonoCechComplexApp_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    (toStrictMonoCechComplexApp U P).f n ≫ strictMonoCechComplexπ U P a = Pi.π _ a.1 :=
  -- the component `(toStrictMonoCechComplexApp U P).f n` is by definition the `Pi.map'`
  -- `toStrictMonoCechX U P n`, and `strictMonoCechComplexπ U P a` is `Pi.π _ a`
  (Pi.map'_comp_π _ _ a).trans (Category.comp_id _)

/-- The map of complexes `Č(U, P) ⟶ Čₒ(U, P)` from the Čech complex to the ordered Čech complex,
natural in the presheaf `P`. It restricts a cochain to the strictly increasing tuples: its factor
indexed by such a tuple `a` is the projection of `Č(U, P)` onto the factor indexed by `a`
(`toStrictMonoCechComplex_app_f_π`). It is split surjective in every degree. -/
def toStrictMonoCechComplex : cechComplexFunctor U ⟶ strictMonoCechComplexFunctor (A := A) U where
  app := toStrictMonoCechComplexApp U
  naturality P Q α := by
    ext n a : 2
    -- both sides are the projection onto the factor of `a`, followed by the component of `α`
    simp only [HomologicalComplex.comp_f, Category.assoc, toStrictMonoCechComplexApp_f_π,
      strictMonoCechComplexFunctor_map_f_π, toStrictMonoCechComplexApp_f_π_assoc]
    exact cechComplexFunctor_map_f_π U P α n a.1

/-- The factor of `toStrictMonoCechComplex` indexed by a strictly increasing tuple `a` is the
projection of the Čech complex onto the factor indexed by `a`. -/
@[simp, reassoc]
theorem toStrictMonoCechComplex_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (a : {a : Fin (n + 1) → ι // StrictMono a}) :
    ((toStrictMonoCechComplex U).app P).f n ≫ strictMonoCechComplexπ U P a = Pi.π _ a.1 :=
  toStrictMonoCechComplexApp_f_π U P n a

/-- Restriction to the strictly increasing tuples is split surjective in every degree: a cochain on
the strictly increasing tuples extends by zero to a Čech cochain. -/
instance (P : Cᵒᵖ ⥤ A) (n : ℕ) : IsSplitEpi (((toStrictMonoCechComplex U).app P).f n) :=
  isSplitEpi_toStrictMonoCechX U P n

end Preorder

/-! ### Comparison with the ordered Čech complex of a functor on finite sets

For a linear order on `ι`, strictly increasing tuples `Fin (n + 1) → ι` are the same as finite
sets of `n + 1` indices, so `Čₒ(U, P)` is the ordered Čech complex
`CategoryTheory.Functor.orderedCechComplex` of the functor `s ↦ P(∏_{i ∈ s} U i)` on finite sets of
indices, taken in `Aᵒᵖ` and brought back to `A` by `HomologicalComplex.unop`
(`strictMonoCechComplexIso`). -/

section LinearOrder

open Finset

variable [LinearOrder ι]

/-- The functor on finite sets of indices, with values in `Aᵒᵖ`, whose ordered Čech complex is
`Čₒ(U, P)`: a finite set `s` goes to `P(∏_{i ∈ s} U i)` and an inclusion `t ⊆ s` to the restriction
along the projection `∏_{i ∈ s} U i ⟶ ∏_{i ∈ t} U i` (`presheafCechFunctor_obj`,
`presheafCechFunctor_map`). It is reducible, so that its values are seen to be the objects
`op (P.obj _)`. -/
@[simps]
abbrev presheafCechFunctor (P : Cᵒᵖ ⥤ A) : (Finset ι)ᵒᵖ ⥤ Aᵒᵖ where
  obj s := op (P.obj (op (∏ᶜ fun i : s.unop ↦ U i)))
  map {s t} f := (P.map (Pi.lift fun i : t.unop ↦
    Pi.π (fun i : s.unop ↦ U i) ⟨i.1, leOfHom f.unop i.2⟩).op).op
  map_id s := Quiver.Hom.unop_inj <| by simp
  map_comp f g := Quiver.Hom.unop_inj <| by
    simp only [unop_comp, Quiver.Hom.unop_op]
    rw [← P.map_comp, ← op_comp]
    congr 2
    exact Pi.hom_ext _ _ fun i ↦ by simp

variable (P : Cᵒᵖ ⥤ A)

/-- The degree `n` term of `Čₒ(U, P)` is the product of the `P(∏_{i ∈ s} U i)` over the sets `s`
of `n + 1` indices, the factor of `s` being reached through its increasing enumeration. The sets of
`n + 1` indices are matched with the strictly increasing tuples by
`Set.powersetCard.ofFinEmbEquiv` and `OrderEmbedding.equivSubtypeStrictMono`, and
`∏_{i ∈ s} U i` is reindexed along the increasing enumeration of `s` by `Pi.reindex`. -/
private def isLimitFan (n : ℕ) : IsLimit (Fan.mk
    (∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j))))
    fun s : {s : Finset ι // #s = n + 1} ↦
      Pi.π _ (⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩ :
        {a : Fin (n + 1) → ι // StrictMono a}) ≫
      P.map (Pi.lift fun j ↦
        Pi.π (fun i : s.1 ↦ U i) ⟨s.1.orderEmbOfFin s.2 j, orderEmbOfFin_mem _ _ j⟩).op) :=
  (productIsProduct _).ofIsoLimit <| Iso.symm <| Fan.ext (Pi.whiskerEquiv
    (((Equiv.subtypeEquivRight fun _ ↦ Set.powersetCard.mem_iff.symm).trans
      Set.powersetCard.ofFinEmbEquiv.symm).trans OrderEmbedding.equivSubtypeStrictMono)
    fun s ↦ P.mapIso (Pi.reindex (s.1.orderIsoOfFin s.2).toEquiv fun i : s.1 ↦ U i).symm.op).symm
      fun s ↦ by
        have h : Pi.lift (f := fun j ↦ U (s.1.orderEmbOfFin s.2 j)) (fun j ↦
              Pi.π (fun i : s.1 ↦ U i) ⟨s.1.orderEmbOfFin s.2 j, orderEmbOfFin_mem _ _ j⟩) =
            (Pi.reindex (s.1.orderIsoOfFin s.2).toEquiv fun i : s.1 ↦ U i).inv :=
          Pi.hom_ext _ _ fun j ↦ by
            rw [Pi.lift_comp_π]
            -- the factor `⟨s.orderEmbOfFin h j, _⟩` is `(s.orderIsoOfFin h).toEquiv j`, as
            -- `Finset.coe_orderIsoOfFin_apply` holds by definition
            exact (Pi.reindex_inv_π (s.1.orderIsoOfFin s.2).toEquiv (fun i : s.1 ↦ U i) j).symm
        rw [fan_mk_proj, fan_mk_proj, Iso.symm_hom, h]
        dsimp only [Pi.whiskerEquiv]
        rw [Pi.map'_comp_π, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom]
        -- the index is `⟨s.orderEmbOfFin h, _⟩` by `Set.powersetCard.ofFinEmbEquiv_symm_apply`,
        -- which is `rfl`; it cannot be rewritten, as the type of the factor depends on it
        rfl

/-- The degree `n` component of `strictMonoCechComplexIso`. -/
private def strictMonoCechXIso (n : ℕ) :
    (∏ᶜ fun a : {a : Fin (n + 1) → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) ≅
      unop ((presheafCechFunctor U P).orderedCechComplex.X n) :=
  (((presheafCechFunctor U P).isColimitOrderedCechComplexCofan n).coconePointUniqueUpToIso
    (Fan.IsLimit.op (isLimitFan U P n))).unop

@[reassoc]
private lemma orderedCechComplexι_strictMonoCechXIso_hom_op (n : ℕ)
    (s : {s : Finset ι // #s = n + 1}) :
    (presheafCechFunctor U P).orderedCechComplexι s ≫ (strictMonoCechXIso U P n).hom.op =
      (Pi.π _ (⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩ :
          {a : Fin (n + 1) → ι // StrictMono a}) ≫
        P.map (Pi.lift fun j ↦
          Pi.π (fun i : s.1 ↦ U i) ⟨s.1.orderEmbOfFin s.2 j, orderEmbOfFin_mem _ _ j⟩).op).op :=
  ((presheafCechFunctor U P).isColimitOrderedCechComplexCofan n).comp_coconePointUniqueUpToIso_hom
    _ ⟨s⟩

omit [Preadditive A] in
/-- Restricting the factor of a strictly increasing tuple `b` along a map determined by its
factors depends only on `b`. -/
private lemma pi_π_comp_map_congr (s : Finset ι) {k : ℕ} {b b' : {a : Fin k → ι // StrictMono a}}
    (h : b = b') (hb : ∀ j, b.1 j ∈ s) (f : (∏ᶜ fun i : s ↦ U i) ⟶ ∏ᶜ fun j ↦ U (b.1 j))
    (f' : (∏ᶜ fun i : s ↦ U i) ⟶ ∏ᶜ fun j ↦ U (b'.1 j))
    (hf : ∀ j, f ≫ Pi.π _ j = Pi.π (fun i : s ↦ U i) ⟨b.1 j, hb j⟩)
    (hf' : ∀ j, f' ≫ Pi.π _ j = Pi.π (fun i : s ↦ U i) ⟨b'.1 j, h ▸ hb j⟩) :
    Pi.π (fun a : {a : Fin k → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) b ≫
        P.map f.op =
      Pi.π (fun a : {a : Fin k → ι // StrictMono a} ↦ P.obj (op (∏ᶜ fun j ↦ U (a.1 j)))) b' ≫
        P.map f'.op := by
  subst h
  rw [Pi.hom_ext f f' fun j ↦ (hf j).trans (hf' j).symm]

/-- The components `strictMonoCechXIso` commute with the differentials: the ordered Čech
differential deleting the `m`-th smallest index carries the sign `(-1) ^ m`. -/
private lemma strictMonoCechXIso_hom_comp_d (n : ℕ) :
    (strictMonoCechXIso U P n).hom ≫
        ((presheafCechFunctor U P).orderedCechComplex.d (n + 1) n).unop =
      strictMonoCechComplexD U P n ≫ (strictMonoCechXIso U P (n + 1)).hom := by
  apply Quiver.Hom.op_inj
  refine (presheafCechFunctor U P).orderedCechComplex_hom_ext fun s ↦ ?_
  simp only [op_comp, Quiver.Hom.op_unop, Functor.ι_orderedCechComplex_d_assoc,
    orderedCechComplexι_strictMonoCechXIso_hom_op_assoc]
  simp only [← op_comp, strictMonoCechComplexD_π_assoc, Preadditive.sum_comp,
    CategoryTheory.op_sum]
  -- match the summand of `s.orderIsoOfFin h m`, the `m`-th smallest element of `s`, with the
  -- coface `m`
  refine (Fintype.sum_equiv (s.1.orderIsoOfFin s.2).toEquiv _ _ fun m ↦ ?_).symm
  simp only [Preadditive.zsmul_comp, CategoryTheory.op_zsmul, Category.assoc]
  have hc : #{j ∈ s.1 | j < (s.1.orderIsoOfFin s.2 m : ι)} = m := by
    rw [coe_orderIsoOfFin_apply]
    exact card_filter_lt_orderEmbOfFin _ _ m
  rw [orderedCechComplexι_strictMonoCechXIso_hom_op, OrderIso.coe_toEquiv, hc]
  simp only [← op_comp, Category.assoc, ← P.map_comp]
  congr 2
  have hm (x : Fin (n + 1)) : s.1.orderEmbOfFin s.2 (m.succAbove x) ∈
      s.1.erase (s.1.orderIsoOfFin s.2 m) :=
    mem_erase.2 ⟨fun h ↦ m.succAbove_ne x ((s.1.orderEmbOfFin s.2).injective h),
      orderEmbOfFin_mem _ _ _⟩
  refine pi_π_comp_map_congr U P s.1 (Subtype.ext (orderEmbOfFin_unique _ hm
    ((s.1.orderEmbOfFin s.2).strictMono.comp (Fin.strictMono_succAbove m)))) (fun x ↦
      orderEmbOfFin_mem _ _ _) _ _ (fun x ↦ by simp) fun j ↦ by
    simp only [Category.assoc, Pi.lift_comp_π]

/-- For a linearly ordered index type, the ordered Čech complex `Čₒ(U, P)`, indexed by strictly
increasing tuples, is isomorphic to the ordered Čech complex
`CategoryTheory.Functor.orderedCechComplex` of `presheafCechFunctor U P`, indexed by finite sets of
indices, brought back from `Aᵒᵖ` to `A`. The factor of a set `s` is the factor of its increasing
enumeration (`strictMonoCechComplexIso_hom_f_comp_unop_orderedCechComplexι`). -/
def strictMonoCechComplexIso :
    (strictMonoCechComplexFunctor U).obj P ≅
      ((presheafCechFunctor U P).orderedCechComplex.unop : CochainComplex A ℕ) :=
  HomologicalComplex.Hom.isoOfComponents (strictMonoCechXIso U P) fun i j h ↦ by
    obtain rfl : i + 1 = j := h
    rw [strictMonoCechComplexFunctor_obj_d]
    exact strictMonoCechXIso_hom_comp_d U P i

/-- The factor indexed by a set `s = {i₀ < ⋯ < iₙ}` of `strictMonoCechComplexIso` is the projection
onto the factor of the increasing enumeration `a` of `s`, followed by the restriction along the
isomorphism `∏_{i ∈ s} U i ≅ U (a 0) × ⋯ × U (a n)`. -/
@[reassoc]
theorem strictMonoCechComplexIso_hom_f_comp_unop_orderedCechComplexι (n : ℕ)
    (s : {s : Finset ι // #s = n + 1}) :
    (strictMonoCechComplexIso U P).hom.f n ≫
        ((presheafCechFunctor U P).orderedCechComplexι s).unop =
      strictMonoCechComplexπ U P (⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩ :
          {a : Fin (n + 1) → ι // StrictMono a}) ≫
        P.map (Pi.lift fun j ↦
          Pi.π (fun i : s.1 ↦ U i) ⟨s.1.orderEmbOfFin s.2 j, orderEmbOfFin_mem _ _ j⟩).op := by
  dsimp only [strictMonoCechComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  -- `strictMonoCechComplexπ U P a` is `Pi.π _ a` by definition
  exact Quiver.Hom.op_inj (orderedCechComplexι_strictMonoCechXIso_hom_op U P n s)

end LinearOrder

end TauCeti.CategoryTheory
