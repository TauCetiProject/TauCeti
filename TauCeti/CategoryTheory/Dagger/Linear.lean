/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.Conj

/-!
# Endomorphism star-algebra homomorphisms in linear dagger categories

In a dagger category, unitary endomorphisms of `X` correspond to elements of the unitary group
`unitary (End X)` under Mathlib's operator-order multiplication.

When `C` and `D` are `R`-linear dagger categories, an additive `R`-linear dagger-preserving
functor `F : C ⥤ D` induces a unital star-algebra homomorphism
`CategoryTheory.Functor.mapEndStarAlgHom : End X →⋆ₐ[R] End (F.obj X)`, upgrading
`CategoryTheory.Functor.mapEndAlgHom`. A fully faithful such functor induces a star-algebra
equivalence `CategoryTheory.Functor.FullyFaithful.starAlgEquivEnd`, and conjugation by a unitary
isomorphism `e : X ≅ Y` upgrades `CategoryTheory.Iso.conjAlgEquiv` to a star-algebra equivalence
`CategoryTheory.Iso.conjStarAlgEquiv : End X ≃⋆ₐ[R] End Y`.
-/

public section

open CategoryTheory TauCeti

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.End

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] {X : C}

/-- An endomorphism belongs to `unitary (End X)` precisely when its underlying arrow is unitary. -/
theorem mem_unitary_iff (f : End X) : f ∈ unitary (End X) ↔ IsUnitary f.asHom := by
  simp [Unitary.mem_iff, End.ext_iff, isUnitary_iff]

/-- Constructing an endomorphism from an arrow gives a unitary element precisely when the arrow
is unitary. -/
@[simp] theorem of_mem_unitary_iff (f : X ⟶ X) :
    End.of f ∈ unitary (End X) ↔ IsUnitary f :=
  mem_unitary_iff (End.of f)

/-- Unitary elements of `End X` correspond to unitary endomorphism arrows of `X`. -/
def unitaryEquiv (X : C) : unitary (End X) ≃ { f : X ⟶ X // IsUnitary f } where
  toFun u := ⟨u.1.asHom, (mem_unitary_iff u.1).mp u.2⟩
  invFun f := ⟨End.of f.1, (of_mem_unitary_iff f.1).mpr f.2⟩
  left_inv u := by ext; rfl
  right_inv f := by ext; rfl

/-- The forward map of `End.unitaryEquiv` extracts the underlying endomorphism arrow. -/
@[simp] theorem unitaryEquiv_apply_val (u : unitary (End X)) :
    (unitaryEquiv X u).1 = u.1.asHom := (rfl)

/-- The inverse of `End.unitaryEquiv` wraps a unitary arrow as an element of `End X`. -/
@[simp] theorem unitaryEquiv_symm_apply_coe (f : { f : X ⟶ X // IsUnitary f }) :
    ((unitaryEquiv X).symm f : End X) = End.of f.1 := (rfl)

end CategoryTheory.End

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [Preadditive D]
variable {E : Type u₃} [Category.{v₃} E] [DaggerCategory E] [Preadditive E]
variable (F : C ⥤ D) (R : Type w) [CommSemiring R]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An additive `R`-linear dagger-preserving functor induces a unital star-algebra homomorphism on
endomorphism algebras. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) where
  __ := F.mapEndAlgHom R X
  map_star' f := by ext; simp

/-- Forgetting star preservation recovers `Functor.mapEndAlgHom`. -/
@[simp] theorem mapEndStarAlgHom_toAlgHom (X : C) :
    (F.mapEndStarAlgHom R X).toAlgHom = F.mapEndAlgHom R X := (rfl)

/-- The induced star-algebra homomorphism acts by `F.map` on underlying arrows. -/
@[simp] theorem mapEndStarAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgHom R X f).asHom = F.map f.asHom :=
  F.mapEndAlgHom_asHom R X f

/-- Evaluating `mapEndStarAlgHom` on `End.of f` wraps `F.map f`. -/
@[simp] theorem mapEndStarAlgHom_of (X : C) (f : X ⟶ X) :
    F.mapEndStarAlgHom R X (End.of f) = End.of (F.map f) := by
  ext
  exact F.mapEndAlgHom_asHom R X (End.of f)

/-- The identity functor induces the identity star-algebra homomorphism on endomorphisms. -/
@[simp] theorem mapEndStarAlgHom_id (X : C) :
    (𝟭 C).mapEndStarAlgHom R X = StarAlgHom.id R (End X) := by
  ext x
  exact mapEndStarAlgHom_asHom (𝟭 C) R X x

/-- Composition of functors induces composition of endomorphism star-algebra homomorphisms. -/
@[simp] theorem mapEndStarAlgHom_comp [CategoryTheory.Linear R E]
    (G : D ⥤ E) [G.Additive] [G.Linear R] [G.PreservesDagger] (X : C) :
    (F ⋙ G).mapEndStarAlgHom R X =
      (G.mapEndStarAlgHom R (F.obj X)).comp (F.mapEndStarAlgHom R X) := by
  ext; simp

/-- A faithful additive linear dagger-preserving functor embeds each endomorphism star-algebra. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_injective R X

/-- An additive linear dagger-preserving functor bijective on `X ⟶ X` induces a bijective
star-algebra homomorphism on `End X`. -/
theorem mapEndStarAlgHom_bijective (X : C)
    (h : Function.Bijective (F.map : (X ⟶ X) → (F.obj X ⟶ F.obj X))) :
    Function.Bijective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_bijective R X h

namespace FullyFaithful

variable {F}

/-- A fully faithful additive `R`-linear dagger-preserving functor induces a star-algebra
equivalence on endomorphism algebras. -/
noncomputable def starAlgEquivEnd (hf : F.FullyFaithful) (X : C) :
    End X ≃⋆ₐ[R] End (F.obj X) where
  __ := hf.mulEquivEnd X
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp
  map_star' f := by ext; simp

/-- Applying `FullyFaithful.starAlgEquivEnd` acts by `F.map` on underlying arrows. -/
@[simp] theorem starAlgEquivEnd_asHom (hf : F.FullyFaithful) (X : C) (f : End X) :
    (hf.starAlgEquivEnd R X f).asHom = F.map f.asHom := (rfl)

/-- Applying `(FullyFaithful.starAlgEquivEnd).symm` acts by `hf.preimage` on underlying arrows. -/
@[simp] theorem starAlgEquivEnd_symm_asHom (hf : F.FullyFaithful) (X : C)
    (g : End (F.obj X)) :
    ((hf.starAlgEquivEnd R X).symm g).asHom = hf.preimage g.asHom := (rfl)

/-- Viewing `FullyFaithful.starAlgEquivEnd` as a `StarAlgHom` recovers `mapEndStarAlgHom`. -/
@[simp] theorem ofClass_starAlgEquivEnd (hf : F.FullyFaithful) (X : C) :
    StarAlgHom.ofClass (hf.starAlgEquivEnd R X) = F.mapEndStarAlgHom R X := by
  ext; simp

end FullyFaithful

end CategoryTheory.Functor

namespace CategoryTheory.Iso

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] [Preadditive C]
variable (R : Type w) [CommSemiring R] [Linear R C] {X Y Z : C}

/-- Conjugation by a unitary isomorphism identifies the endomorphism star-algebras of its source
and target. -/
def conjStarAlgEquiv (e : X ≅ Y) (he : IsUnitary e.hom) : End X ≃⋆ₐ[R] End Y where
  __ := e.conjAlgEquiv R
  map_smul' r f := map_smul (e.conjAlgEquiv R) r f
  map_star' f := by
    have hinv : dagger e.inv = e.hom := by
      rw [← e.dagger_hom_eq_inv_of_isUnitary he, dagger_dagger]
    ext
    simp [e.dagger_hom_eq_inv_of_isUnitary he, hinv, Category.assoc]

/-- Applying `Iso.conjStarAlgEquiv` agrees with `Iso.conj`. -/
@[simp] theorem conjStarAlgEquiv_apply (e : X ≅ Y) (he : IsUnitary e.hom) (f : End X) :
    e.conjStarAlgEquiv R he f = e.conj f :=
  e.conjAlgEquiv_apply (R := R) f

/-- Unitary conjugation acts on underlying arrows as `dagger e.hom ≫ f ≫ e.hom`. -/
theorem conjStarAlgEquiv_asHom (e : X ≅ Y) (he : IsUnitary e.hom) (f : End X) :
    (e.conjStarAlgEquiv R he f).asHom = dagger e.hom ≫ f.asHom ≫ e.hom := by
  simp [e.dagger_hom_eq_inv_of_isUnitary he]

/-- Conjugation by the identity isomorphism is the identity star-algebra equivalence. -/
@[simp] theorem refl_conjStarAlgEquiv :
    (Iso.refl X).conjStarAlgEquiv R (IsUnitary.id X) = StarAlgEquiv.refl (R := R) (A := End X) := by
  ext; simp

/-- Unitary conjugation respects composition of unitary isomorphisms. -/
@[simp] theorem trans_conjStarAlgEquiv (e₁ : X ≅ Y) (e₂ : Y ≅ Z)
    (he₁ : IsUnitary e₁.hom) (he₂ : IsUnitary e₂.hom) :
    (e₁ ≪≫ e₂).conjStarAlgEquiv R (he₁.comp he₂) =
      (e₁.conjStarAlgEquiv R he₁).trans (e₂.conjStarAlgEquiv R he₂) := by
  ext; simp

/-- Reversing a unitary isomorphism inverts the induced star-algebra equivalence. -/
@[simp] theorem symm_conjStarAlgEquiv (e : X ≅ Y) (he : IsUnitary e.hom) :
    e.symm.conjStarAlgEquiv R (by simpa [← e.dagger_hom_eq_inv_of_isUnitary he] using he.dagger) =
      (e.conjStarAlgEquiv R he).symm := by
  refine StarAlgEquiv.ext fun f => Eq.symm ?_
  rw [StarAlgEquiv.symm_apply_eq]
  simp

end CategoryTheory.Iso

namespace CategoryTheory.InducedCategory

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] [Preadditive C]
variable (R : Type w) [CommSemiring R] [Linear R C]
variable {S : Type u₂} {F : S → C}

/-- Endomorphisms in an induced category are star-algebra equivalent to endomorphisms of the
underlying object. -/
def endStarAlgEquiv (X : InducedCategory C F) : End X ≃⋆ₐ[R] End (F X) where
  __ := InducedCategory.endEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  map_star' _ := by ext; rfl

/-- Applying `InducedCategory.endStarAlgEquiv` extracts the underlying endomorphism arrow. -/
@[simp] theorem endStarAlgEquiv_asHom (X : InducedCategory C F) (f : End X) :
    (endStarAlgEquiv R X f).asHom = f.asHom.hom := (rfl)

/-- Applying `(InducedCategory.endStarAlgEquiv).symm` wraps an endomorphism arrow via `homMk`. -/
@[simp] theorem endStarAlgEquiv_symm_asHom (X : InducedCategory C F) (g : End (F X)) :
    ((endStarAlgEquiv R X).symm g).asHom = InducedCategory.homMk g.asHom := (rfl)

end CategoryTheory.InducedCategory
