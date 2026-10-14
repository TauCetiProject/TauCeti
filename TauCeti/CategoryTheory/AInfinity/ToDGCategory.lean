/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.HomComplex
public import TauCeti.CategoryTheory.DG.HomComplexData

/-!
# The differential graded category of a unital `A∞` category with `m₃ = 0`

An `A∞` category `𝒞` on a graded linear quiver `C` over a commutative ring `R` has Hom complexes
`TauCeti.AInfinityCategory.homComplex 𝒞 X Y`, whose differential is `m₁`.  The composition
`m₂(g, f) = g ∘ f` satisfies the Leibniz rule `d (g ∘ f) = d g ∘ f + (-1) ^ |g| g ∘ d f`, and
when the ternary operation vanishes the arity-three Stasheff identity says that it is associative
(`TauCeti.AInfinityCategory.comp_assoc_of_m_three_eq_zero`).  A family `e` of degree-zero
two-sided identities for `m₂` makes it unital.  These are exactly the axioms of a differential
graded category in Keller's factor order, so such an `A∞` category with `m₃ = 0` determines the
differential graded category `TauCeti.AInfinityCategory.toDGCategory` on the same objects.  A
strict unit (`TauCeti.AInfinityCategory.StrictUnit`) supplies such a family; its conditions on the
operations of arity other than two are not needed.

Composition in a `TauCeti.DGCategory` is in Mathlib's enriched factor order, `dgComp f g` being
`f` followed by `g`.  The two orders differ by the Koszul sign: for `f` of degree `p` and `g` of
degree `q`, `dgComp f g = (-1) ^ (p * q) • (g ∘ f)`.

This is the converse construction to `TauCeti.DGCategory.toAInfinityCategory`, which views a
differential graded category as a strictly unital `A∞` category whose operations of arity at least
three vanish (`TauCeti.DGCategory.strictUnit_toAInfinityCategory`).  The hypothesis used here is
only `m₃ = 0`: the operations of arity at least four play no role in a differential graded
category.

## Main definitions

* `TauCeti.AInfinityCategory.toDGCategoryData`: the explicit Hom-complex data of an `A∞` category
  with `m₃ = 0` and degree-zero identities for `m₂`.
* `TauCeti.AInfinityCategory.toDGCategory`: the differential graded category it determines.
* `TauCeti.AInfinityCategory.dgHomEquiv`: its morphisms of degree `n` are the morphisms of degree
  `n` of the `A∞` category.

## Main results

* `TauCeti.AInfinityCategory.dgHomEquiv_dgDifferential`: the differential is `m₁`.
* `TauCeti.AInfinityCategory.dgHomEquiv_dgComp`: composition is `m₂` in the reversed order, with
  the Koszul sign `(-1) ^ (p * q)`.
* `TauCeti.AInfinityCategory.dgHomEquiv_dgId`: the identities are the given identities `e`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

/-! ### Hom complexes -/

section HomComplex

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The inclusion of the degree-`n` term of the Hom complex into the hom module. -/
private noncomputable abbrev homComplexι (X Y : C) (n : ℤ) :
    (𝒞.homComplex X Y).X n →ₗ[R] homModule (R := R) X Y :=
  ((grading (R := R) X Y).piece n).subtype ∘ₗ (𝒞.homComplexXEquiv X Y n).toLinearMap

private theorem homComplexι_mem (X Y : C) (n : ℤ) (f : (𝒞.homComplex X Y).X n) :
    𝒞.homComplexι X Y n f ∈ (grading (R := R) X Y).piece n :=
  (𝒞.homComplexXEquiv X Y n f).2

private theorem homComplexι_injective (X Y : C) (n : ℤ) :
    Function.Injective (𝒞.homComplexι X Y n) :=
  Subtype.val_injective.comp (𝒞.homComplexXEquiv X Y n).injective

/-- Keller-ordered composition `g ∘ f` of homogeneous morphisms, between the terms of the Hom
complexes. -/
private noncomputable def kellerComp {X Y Z : C} (q p n : ℤ) (hn : q + p = n) :
    (𝒞.homComplex Y Z).X q →ₗ[R] (𝒞.homComplex X Y).X p →ₗ[R] (𝒞.homComplex X Z).X n :=
  LinearMap.codRestrict₂ ((𝒞.comp X Y Z).compl₁₂ (𝒞.homComplexι Y Z q) (𝒞.homComplexι X Y p))
    (𝒞.homComplexι X Z n) (𝒞.homComplexι_injective X Z n) fun g f ↦
      ⟨(𝒞.homComplexXEquiv X Z n).symm ⟨_, hn ▸ 𝒞.comp_mem_piece
        (𝒞.homComplexXEquiv Y Z q g).2 (𝒞.homComplexXEquiv X Y p f).2⟩, by simp⟩

private theorem homComplexι_kellerComp {X Y Z : C} (q p n : ℤ) (hn : q + p = n)
    (g : (𝒞.homComplex Y Z).X q) (f : (𝒞.homComplex X Y).X p) :
    𝒞.homComplexι X Z n (𝒞.kellerComp q p n hn g f) =
      𝒞.comp X Y Z (𝒞.homComplexι Y Z q g) (𝒞.homComplexι X Y p f) :=
  LinearMap.codRestrict₂_apply _ _ _ _ g f

private theorem homComplexι_d (X Y : C) (n : ℤ) (f : (𝒞.homComplex X Y).X n) :
    𝒞.homComplexι X Y (n + 1) (((𝒞.homComplex X Y).d n (n + 1)).hom f) =
      𝒞.homDifferential X Y (𝒞.homComplexι X Y n f) :=
  𝒞.homComplexXEquiv_d X Y n f

end HomComplex

/-! ### The differential graded category -/

variable {R : Type v} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, v} R C]
  {𝒞 : AInfinityCategory R C} {e : ∀ X : C, homModule (R := R) X X}

/-- The **explicit Hom-complex data** of an `A∞` category with `m₃ = 0` and a family `e` of
degree-zero two-sided identities for `m₂`: the Hom complexes
`TauCeti.AInfinityCategory.homComplex`, Keller-ordered composition `m₂`, and the identities `e`. -/
noncomputable def toDGCategoryData (h₃ : 𝒞.m 3 = 0)
    (he₀ : ∀ X, e X ∈ (grading (R := R) X X).piece 0)
    (hel : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X Y Y (e Y) f = f)
    (her : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X X Y f (e X) = f) :
    DGCategoryData R C :=
  DGCategoryData.ofKeller 𝒞.homComplex (fun q p n hn ↦ 𝒞.kellerComp q p n hn)
    (fun X ↦ (𝒞.homComplexXEquiv X X 0).symm ⟨e X, he₀ X⟩)
    (fun {X Y Z q p n} hn g f ↦ 𝒞.homComplexι_injective X Z (n + 1) <| by
      rw [map_add, map_zsmul_unit, homComplexι_d, homComplexι_kellerComp, homComplexι_kellerComp,
        homComplexι_kellerComp, homComplexι_d, homComplexι_d,
        𝒞.homDifferential_comp (𝒞.homComplexι_mem Y Z q g),
        negOnePow_smul_eq_negOnePowCast_smul (R := R)])
    (fun {W X Y Z r q p rq qp n} hrq hqp hn k g f ↦ 𝒞.homComplexι_injective W Z n <| by
      simp only [homComplexι_kellerComp]
      exact 𝒞.comp_assoc_of_m_three_eq_zero h₃ _ _ _)
    (fun {X Y q} g ↦ 𝒞.homComplexι_injective X Y q <| by
      simp only [homComplexι_kellerComp, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.coe_subtype, her])
    (fun {X Y p} f ↦ 𝒞.homComplexι_injective X Y p <| by
      simp only [homComplexι_kellerComp, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.coe_subtype, hel])

/-- The **differential graded category of an `A∞` category with `m₃ = 0`** and a family `e` of
degree-zero two-sided identities for `m₂`: its Hom complexes are
`TauCeti.AInfinityCategory.homComplex`, with differential `m₁`, its composition is `m₂` converted
to Mathlib's enriched factor order with the Koszul sign, and its identities are `e`.  For a
strict unit `he : 𝒞.StrictUnit e` this is
`toDGCategory h₃ he.degree_zero he.binary_left he.binary_right`. -/
@[instance_reducible]
noncomputable def toDGCategory (h₃ : 𝒞.m 3 = 0)
    (he₀ : ∀ X, e X ∈ (grading (R := R) X X).piece 0)
    (hel : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X Y Y (e Y) f = f)
    (her : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X X Y f (e X) = f) :
    DGCategory R C :=
  (toDGCategoryData h₃ he₀ hel her).toDGCategory

variable (h₃ : 𝒞.m 3 = 0) (he₀ : ∀ X, e X ∈ (grading (R := R) X X).piece 0)
  (hel : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X Y Y (e Y) f = f)
  (her : ∀ X Y (f : homModule (R := R) X Y), 𝒞.comp X X Y f (e X) = f)

/-- The Hom complexes of the differential graded category are the Hom complexes of the `A∞`
category. -/
@[simp↓]
theorem dgHomComplex_toDGCategory (X Y : C) :
    letI := toDGCategory h₃ he₀ hel her
    dgHomComplex R X Y = 𝒞.homComplex X Y :=
  (rfl)

/-- The morphisms of degree `n` of the differential graded category are the morphisms of degree
`n` of the `A∞` category. -/
noncomputable def dgHomEquiv (X Y : C) (n : ℤ) :
    letI := toDGCategory h₃ he₀ hel her
    DGHom R n X Y ≃ₗ[R] grHom R X Y n :=
  𝒞.homComplexXEquiv X Y n

/-- **The differential of the differential graded category** is `m₁`. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {X Y : C} (n : ℤ)
    (f : letI := toDGCategory h₃ he₀ hel her; DGHom R n X Y) :
    letI := toDGCategory h₃ he₀ hel her
    (dgHomEquiv h₃ he₀ hel her X Y (n + 1) (dgDifferential R n f) : homModule (R := R) X Y) =
      𝒞.homDifferential X Y (dgHomEquiv h₃ he₀ hel her X Y n f) := by
  rw [(toDGCategoryData h₃ he₀ hel her).dgDifferential_toDGCategory n f]
  exact 𝒞.homComplexXEquiv_d X Y n f

/-- **The composition of the differential graded category** is `m₂` in the reversed order: for
`f : X ⟶ Y` of degree `p` and `g : Y ⟶ Z` of degree `q`, the enriched composite `dgComp f g` is
`g ∘ f` up to the Koszul sign `(-1) ^ (p * q)`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {X Y Z : C} {p q n : ℤ}
    (f : letI := toDGCategory h₃ he₀ hel her; DGHom R p X Y)
    (g : letI := toDGCategory h₃ he₀ hel her; DGHom R q Y Z) (h : p + q = n) :
    letI := toDGCategory h₃ he₀ hel her
    (dgHomEquiv h₃ he₀ hel her X Z n (dgComp R f g h) : homModule (R := R) X Z) =
      (p * q).negOnePow • 𝒞.comp X Y Z (dgHomEquiv h₃ he₀ hel her Y Z q g)
        (dgHomEquiv h₃ he₀ hel her X Y p f) := by
  let := toDGCategory h₃ he₀ hel her
  -- `toDGCategoryData` is built by `DGCategoryData.ofKeller`, whose enriched-order composition
  -- is the signed reversed Keller composition by definition (`DGCategoryData.ofKeller_comp`).
  have hcomp : dgComp R f g h = (p * q).negOnePow • 𝒞.kellerComp q p n (by omega) g f :=
    DGCategoryData.dgComp_toDGCategory _ f g h
  rw [hcomp]
  exact (map_zsmul_unit (𝒞.homComplexι X Z n) _ _).trans
    (congrArg _ (𝒞.homComplexι_kellerComp q p n _ g f))

/-- **The identities of the differential graded category** are the given identities `e`. -/
@[simp↓]
theorem dgHomEquiv_dgId (X : C) :
    letI := toDGCategory h₃ he₀ hel her
    (dgHomEquiv h₃ he₀ hel her X X 0 (dgId R X) : homModule (R := R) X X) = e X := by
  let := toDGCategory h₃ he₀ hel her
  -- As for composition, the identity of `ofKeller` data is the given one by definition
  -- (`DGCategoryData.ofKeller_id`).
  have hid : dgId R X = (𝒞.homComplexXEquiv X X 0).symm ⟨e X, he₀ X⟩ :=
    DGCategoryData.dgId_toDGCategory _ X
  rw [hid]
  exact congrArg Subtype.val ((𝒞.homComplexXEquiv X X 0).apply_symm_apply _)

end AInfinityCategory

end TauCeti
