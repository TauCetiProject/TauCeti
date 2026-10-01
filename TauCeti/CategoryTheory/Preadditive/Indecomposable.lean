/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Recognizing indecomposable objects from their endomorphisms

Mathlib defines `CategoryTheory.Indecomposable X` as the conjunction "`X` is not a zero object,
and in every decomposition `X ≅ Y ⊞ Z` one of `Y`, `Z` is zero", and proves exactly one criterion
for it: a simple object is indecomposable (`CategoryTheory.indecomposable_of_simple`). That
criterion is too strong for the objects that carry the theory of a finite-dimensional algebra: an
indecomposable projective module is almost never simple. The criterion that does apply is the one
this file supplies — an object all of whose idempotent endomorphisms are trivial is
indecomposable — together with the two forms in which it is used in practice. An object whose
endomorphisms are recorded faithfully in a *local* ring, by a map preserving zero, the identity and
squares, is indecomposable; this is the criterion behind the Krull–Schmidt theorem, and the one
the quiver Jordan blocks need, their endomorphism algebra `k[X]/(Xⁿ⁺¹)` being local but not a
field. And over a division ring, an object whose endomorphism space is one-dimensional (a
*brick*) is indecomposable.

The converse holds as soon as idempotents split, that is, over an idempotent-complete category
(`CategoryTheory.IsIdempotentComplete`, which every abelian category is): splitting `e` and `𝟙 - e`
produces two retracts of `X` whose idempotents add up to the identity, and any such pair realizes
`X` as their biproduct. So over such a category an object is indecomposable exactly when it is
nonzero and carries no idempotent endomorphism other than `0` and the identity, which is the form
in which indecomposability is *used*: it turns a decomposition of a vertex space into a
decomposition of the whole object.

## Main results

* `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`: a nonzero object whose only idempotent
  endomorphisms are `0` and the identity is indecomposable.
* `TauCeti.indecomposable_of_injective_of_isLocalRing`: **an object whose endomorphisms are
  recorded faithfully in a local ring, by a map preserving zero, the identity and squares, is
  indecomposable.**
* `TauCeti.indecomposable_of_finrank_end_eq_one`: in a `k`-linear category over a division ring,
  **a brick is indecomposable**.
* `TauCeti.isoBiprodOfRetracts`: two retracts of `X` whose idempotents sum to the identity exhibit
  `X` as their biproduct.
* `TauCeti.idempotent_eq_zero_or_id_of_indecomposable`: the converse of the first criterion, over
  an idempotent-complete category, packaged with it as
  `TauCeti.indecomposable_iff_idempotent_eq_zero_or_id`.
* `TauCeti.isIso_of_isIso_comp`: an invertible composite `f ≫ g` through an object with only
  trivial idempotent endomorphisms has `f` invertible.
* `CategoryTheory.Functor.indecomposable_obj_of_map_bijective`: a functor preserving zero morphisms
  and bijective on the endomorphisms of an indecomposable object carries it to an indecomposable
  object; in particular a fully faithful one does.

## Implementation notes

The idempotent hypothesis is phrased with composition, `e ≫ e = e`, rather than through the ring
`CategoryTheory.End X`, whose multiplication is composition in the opposite order; for an
idempotent the two agree, but the hypothesis is easier to discharge as stated.

`indecomposable_of_injective_of_isLocalRing` records the endomorphisms in an unbundled map `φ`,
asked to be injective, to send `0` to `0` and `𝟙 X` to `1`, and to carry squares to squares,
`φ (e ≫ e) = φ e * φ e`. On a square the two orders of multiplication agree, so no use site has to
choose between `≫` and the multiplication of `End X`; bundling `φ` as a ring homomorphism would
settle the order and demand additivity besides. The ring is not asked to be commutative because
the endomorphism ring of an indecomposable object, the intended source of `φ`, is not.

Two neighbours state the same idea in narrower settings.
`TauCeti.indecomposable_iff_isLocalRing_end` asks `CategoryTheory.End` itself to be local but is
confined to `ModuleCat A` and to modules of finite length;
`TauCeti.isIndecomposableModule_of_isLocalRing_end` is the statement for bare modules. A quiver
representation is a functor `Paths Q ⥤ ModuleCat k`, not an object of `ModuleCat A`, and recording
its endomorphisms in a ring already known to be local is what makes the criterion cheap to apply.

The criteria that only produce or consume idempotents and zero objects are stated over
`CategoryTheory.Limits.HasZeroMorphisms`, the setting of `CategoryTheory.Indecomposable` itself;
only the converse direction, which forms `𝟙 X - e`, and the biproduct decomposition from retracts
need a preadditive category. The brick criterion is stated over a division ring.

`isoBiprodOfRetracts` asks only for the two retractions and the identity `r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X`;
the orthogonality relations `i₁ ≫ r₂ = 0` and `i₂ ≫ r₁ = 0` follow. Stating it this way keeps it
usable from any source of complementary idempotents, not only from
`CategoryTheory.IsIdempotentComplete.idempotents_split`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- **An object with no nontrivial idempotent endomorphism is indecomposable.** -/
theorem indecomposable_of_idempotent_eq_zero_or_id [HasBinaryBiproducts C] {X : C} (hX : ¬ IsZero X)
    (h : ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X) : Indecomposable X := by
  refine ⟨hX, fun Y Z i ↦ ?_⟩
  rcases h (i.hom ≫ biprod.fst ≫ biprod.inl ≫ i.inv) (by simp) with h0 | h1
  · refine Or.inl ((IsZero.iff_id_eq_zero Y).mpr ?_)
    simpa using congrArg (fun f : X ⟶ X ↦ biprod.inl ≫ i.inv ≫ f ≫ i.hom ≫ biprod.fst) h0
  · refine Or.inr ((IsZero.iff_id_eq_zero Z).mpr ?_)
    simpa using (congrArg (fun f : X ⟶ X ↦ biprod.inr ≫ i.inv ≫ f ≫ i.hom ≫ biprod.snd) h1).symm

/-- **An object whose endomorphisms are recorded faithfully in a local ring is indecomposable.**
The record `φ` is asked to be injective and to preserve zero, the identity and squares. This is
the criterion behind the Krull–Schmidt theorem: an object whose endomorphism ring is local is
indecomposable. -/
theorem indecomposable_of_injective_of_isLocalRing [HasBinaryBiproducts C] {X : C} (hX : ¬ IsZero X)
    {R : Type*} [Ring R] [IsLocalRing R] (φ : (X ⟶ X) → R) (hφ : Function.Injective φ)
    (hzero : φ 0 = 0) (hid : φ (𝟙 X) = 1) (hsq : ∀ e : X ⟶ X, φ (e ≫ e) = φ e * φ e) :
    Indecomposable X := by
  refine indecomposable_of_idempotent_eq_zero_or_id hX fun e he ↦ ?_
  have hidem : IsIdempotentElem (φ e) := (hsq e).symm.trans (congrArg φ he)
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · exact Or.inl (hφ (h0.trans hzero.symm))
  · exact Or.inr (hφ (h1.trans hid.symm))

/-- **A composite that is invertible has an invertible first factor**, when the object it passes
through has only the trivial idempotent endomorphisms and the identity of the source is nonzero.
Both hypotheses hold when the source is nonzero and the middle object is indecomposable in a
category where idempotents split (`TauCeti.idempotent_eq_zero_or_id_of_indecomposable`). -/
theorem isIso_of_isIso_comp {X Y : C} (hX : 𝟙 X ≠ 0)
    (hY : ∀ e : Y ⟶ Y, e ≫ e = e → e = 0 ∨ e = 𝟙 Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsIso (f ≫ g)) : IsIso f := by
  have hfp : f ≫ g ≫ inv (f ≫ g) = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]
  rcases hY ((g ≫ inv (f ≫ g)) ≫ f) (by simp only [Category.assoc, reassoc_of% hfp])
    with h0 | h1
  · refine absurd ?_ hX
    calc 𝟙 X = f ≫ ((g ≫ inv (f ≫ g)) ≫ f) ≫ g ≫ inv (f ≫ g) := by
          simp only [Category.assoc, reassoc_of% hfp, hfp]
      _ = 0 := by rw [h0, zero_comp, comp_zero]
  · exact ⟨⟨g ≫ inv (f ≫ g), hfp, h1⟩⟩

end HasZeroMorphisms

variable [Preadditive C]

/-- **Two retracts whose idempotents sum to the identity split an object as a biproduct.** Its
comparison map and inverse are read off by `TauCeti.isoBiprodOfRetracts_hom` and
`TauCeti.isoBiprodOfRetracts_inv`. -/
noncomputable def isoBiprodOfRetracts [HasBinaryBiproducts C] {X Y Z : C} (i₁ : Y ⟶ X) (r₁ : X ⟶ Y)
    (i₂ : Z ⟶ X) (r₂ : X ⟶ Z) (h₁ : i₁ ≫ r₁ = 𝟙 Y) (h₂ : i₂ ≫ r₂ = 𝟙 Z)
    (h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X) : X ≅ Y ⊞ Z := by
  -- `i₁` and `i₂` are split monomorphisms, so orthogonality can be checked after composing with
  -- them, where `h` and the two retraction identities settle it.
  haveI : IsSplitMono i₁ := ⟨⟨r₁, h₁⟩⟩
  haveI : IsSplitMono i₂ := ⟨⟨r₂, h₂⟩⟩
  have key₁ : i₁ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₁ := by rw [h, Category.comp_id]
  have key₂ : i₂ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₂ := by rw [h, Category.comp_id]
  simp only [Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂, add_eq_left,
    add_eq_right] at key₁ key₂
  have horth₁ : i₁ ≫ r₂ = 0 := by rw [← cancel_mono i₂, Category.assoc, key₁, zero_comp]
  have horth₂ : i₂ ≫ r₁ = 0 := by rw [← cancel_mono i₁, Category.assoc, key₂, zero_comp]
  exact
    { hom := biprod.lift r₁ r₂
      inv := biprod.desc i₁ i₂
      hom_inv_id := by rw [biprod.lift_desc, h]
      inv_hom_id := by
        refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
          simp [h₁, h₂, horth₁, horth₂] }

/-- The comparison map of `TauCeti.isoBiprodOfRetracts` is the pair of the two retractions. -/
@[simp]
theorem isoBiprodOfRetracts_hom [HasBinaryBiproducts C] {X Y Z : C} {i₁ : Y ⟶ X} {r₁ : X ⟶ Y}
    {i₂ : Z ⟶ X} {r₂ : X ⟶ Z} {h₁ : i₁ ≫ r₁ = 𝟙 Y} {h₂ : i₂ ≫ r₂ = 𝟙 Z}
    {h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X} :
    (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ h).hom = biprod.lift r₁ r₂ :=
  -- The parentheses are load-bearing: `isoBiprodOfRetracts` does not expose its body, and the
  -- bare-`rfl` elaborator refuses to unfold a sealed definition, even in the defining module.
  (rfl)

/-- The inverse of `TauCeti.isoBiprodOfRetracts` is the pair of the two sections. -/
@[simp]
theorem isoBiprodOfRetracts_inv [HasBinaryBiproducts C] {X Y Z : C} {i₁ : Y ⟶ X} {r₁ : X ⟶ Y}
    {i₂ : Z ⟶ X} {r₂ : X ⟶ Z} {h₁ : i₁ ≫ r₁ = 𝟙 Y} {h₂ : i₂ ≫ r₂ = 𝟙 Z}
    {h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X} :
    (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ h).inv = biprod.desc i₁ i₂ :=
  (rfl)

/-- **An indecomposable object has no nontrivial idempotent endomorphism**, as soon as idempotents
split. This is the converse of `TauCeti.indecomposable_of_idempotent_eq_zero_or_id`. -/
theorem idempotent_eq_zero_or_id_of_indecomposable [HasBinaryBiproducts C] [IsIdempotentComplete C]
    {X : C} (hX : Indecomposable X) {e : X ⟶ X} (he : e ≫ e = e) : e = 0 ∨ e = 𝟙 X := by
  obtain ⟨Y, i₁, r₁, h₁, hr₁⟩ := IsIdempotentComplete.idempotents_split X e he
  obtain ⟨Z, i₂, r₂, h₂, hr₂⟩ := IsIdempotentComplete.idempotents_split X (𝟙 X - e) (by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, he])
  have hsum : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X := by rw [hr₁, hr₂]; abel
  rcases hX.2 Y Z (isoBiprodOfRetracts i₁ r₁ i₂ r₂ h₁ h₂ hsum) with hY | hZ
  · exact Or.inl (by rw [← hr₁, hY.eq_of_tgt r₁ 0, Limits.zero_comp])
  · refine Or.inr (sub_eq_zero.mp ?_).symm
    rw [← hr₂, hZ.eq_of_tgt r₂ 0, Limits.zero_comp]

/-- **Indecomposability is the triviality of the idempotent endomorphisms**, over a category in
which idempotents split. -/
theorem indecomposable_iff_idempotent_eq_zero_or_id [HasBinaryBiproducts C]
    [IsIdempotentComplete C] {X : C} :
    Indecomposable X ↔ ¬ IsZero X ∧ ∀ e : X ⟶ X, e ≫ e = e → e = 0 ∨ e = 𝟙 X :=
  ⟨fun hX ↦ ⟨hX.1, fun _ he ↦ idempotent_eq_zero_or_id_of_indecomposable hX he⟩,
    fun hX ↦ indecomposable_of_idempotent_eq_zero_or_id hX.1 hX.2⟩

section Linear

variable {k : Type*} [Semiring k] [Nontrivial k] [Linear k C]

/-- An object whose endomorphism space is one-dimensional is not a zero object. -/
theorem not_isZero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    ¬ IsZero X := fun hX ↦ by
  have : Subsingleton (X ⟶ X) := ⟨hX.eq_of_src⟩
  rw [Module.finrank_zero_of_subsingleton] at h
  exact zero_ne_one h

/-- An object whose endomorphism space is one-dimensional has a nonzero identity. -/
theorem id_ne_zero_of_finrank_end_eq_one {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    𝟙 X ≠ 0 := fun hid ↦
  not_isZero_of_finrank_end_eq_one h ((IsZero.iff_id_eq_zero X).mpr hid)

end Linear

/-- **A brick is indecomposable**: an object whose endomorphism space over a division ring is
one-dimensional is indecomposable. -/
theorem indecomposable_of_finrank_end_eq_one {k : Type*} [DivisionRing k] [Linear k C]
    [HasBinaryBiproducts C] {X : C} (h : Module.finrank k (X ⟶ X) = 1) :
    Indecomposable X := by
  have hid := id_ne_zero_of_finrank_end_eq_one h
  refine indecomposable_of_idempotent_eq_zero_or_id (not_isZero_of_finrank_end_eq_one h)
    fun e he ↦ ?_
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 X) hid).mp h e
  rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul] at he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (smul_left_injective k hid he) with rfl | rfl
  · exact Or.inl (zero_smul k (𝟙 X))
  · exact Or.inr (one_smul k (𝟙 X))

end TauCeti

namespace CategoryTheory.Functor

open Limits

variable {C : Type*} [Category* C] [Preadditive C] {D : Type*} [Category* D] [HasZeroMorphisms D]

/-- **A functor bijective on the endomorphisms of an indecomposable object carries it to an
indecomposable object**, when idempotents split in the source. A fully faithful functor
qualifies, by `CategoryTheory.Functor.FullyFaithful.map_bijective`. -/
theorem indecomposable_obj_of_map_bijective [HasBinaryBiproducts C] [IsIdempotentComplete C]
    [HasBinaryBiproducts D] (F : C ⥤ D) {X : C}
    (hX : Indecomposable X) (hF : Function.Bijective (F.map : (X ⟶ X) → (F.obj X ⟶ F.obj X))) :
    Indecomposable (F.obj X) := by
  obtain ⟨g, hg⟩ := hF.2 (0 : F.obj X ⟶ F.obj X)
  have hzero : F.map (0 : X ⟶ X) = 0 := by
    calc
      F.map (0 : X ⟶ X) = F.map (g ≫ (0 : X ⟶ X)) := by rw [comp_zero]
      _ = 0 := by rw [F.map_comp, hg, zero_comp]
  refine TauCeti.indecomposable_of_idempotent_eq_zero_or_id (fun h0 ↦ hX.1 ?_) fun e he ↦ ?_
  · rw [IsZero.iff_id_eq_zero] at h0 ⊢
    exact hF.1 (by rw [F.map_id, h0, hzero])
  · obtain ⟨η, rfl⟩ := hF.2 e
    rcases TauCeti.idempotent_eq_zero_or_id_of_indecomposable hX
        (hF.1 (by rw [F.map_comp, he])) with h | h
    · exact Or.inl (by rw [h, hzero])
    · exact Or.inr (by rw [h, F.map_id])

end CategoryTheory.Functor
