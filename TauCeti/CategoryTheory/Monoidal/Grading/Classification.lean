/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Character
public import TauCeti.CategoryTheory.Monoidal.Grading.MonoidalAut
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor

/-!
# Monoidal automorphisms of the identity are characters of the universal grading group

Let `C` be a finite semisimple `k`-linear monoidal category with simple tensor unit, over an
algebraically closed field `k`, whose simple objects have finite-dimensional endomorphism
algebras. A monoidal natural automorphism of the identity functor acts on each simple object by
a scalar, and these scalars form a character of the universal grading group
(`TauCeti.monoidalAutCharacter`); conversely a character determines such an automorphism
(`TauCeti.characterMonoidalAut`). The two constructions are mutually inverse, so
`Aut_⊗(𝟭_C) ≃* Hom(U(C), kˣ)` as groups (Drinfeld–Gelaki–Nikshych–Ostrik).

Combined with the torsor of pivotal structures over `Aut_⊗(𝟭_C)`, this classifies the pivotal
structures of a rigid such category relative to any one of them: for pivotal structures `P` and
`Q` there is exactly one character `χ` with `P = χ • Q`, and `P` is then obtained from `Q` by
multiplying its component at each simple object `X` by `χ (degree [X])`. Whether a pivotal
structure exists at all is a separate question, so these statements start from given ones.

Neither rigidity (for the group isomorphism), finiteness of the set of simple classes, nor a
characteristic assumption is needed.

## Main declarations

* `TauCeti.monoidalAutCharacterEquiv`: the group isomorphism `Aut_⊗(𝟭_C) ≃* Hom(U(C), kˣ)`, given
  by `TauCeti.monoidalAutCharacter` with inverse `TauCeti.characterMonoidalAut`;
* `TauCeti.PivotalCategory.existsUnique_eq_characterMonoidalAut_smul`: two pivotal structures
  differ by exactly one character of the universal grading group;
* `TauCeti.PivotalCategory.characterMonoidalAut_smul_pivotalIso_hom_app_of_simple`: the twist of
  a pivotal structure by a character `χ` multiplies its component at a simple object `X` by
  `χ (degree [X])`.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace TauCeti

section Classification

variable (k : Type w) [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)]

/-- The character of the monoidal automorphism given by a character `χ` is `χ`. -/
@[simp]
theorem monoidalAutCharacter_characterMonoidalAut (χ : universalGradingGroup C →* kˣ) :
    monoidalAutCharacter (hfin := hfin) k (characterMonoidalAut k χ) = χ := by
  ext S
  apply smul_left_injective k (CategoryTheory.id_ne_zero S.repr)
  have h := monoidalAutCharacter_degree_smul_id (hfin := hfin) k (characterMonoidalAut k χ) S.repr
  rwa [characterMonoidalAut_app_of_simple, SimpleClasses.classOf_repr] at h

/-- The monoidal automorphism given by the character of a monoidal automorphism `a` is `a`. -/
@[simp]
theorem characterMonoidalAut_monoidalAutCharacter (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    characterMonoidalAut k (monoidalAutCharacter (hfin := hfin) k a) = a :=
  monoidalAutCharacter_injective (hfin := hfin) k
    (monoidalAutCharacter_characterMonoidalAut (hfin := hfin) k _)

/-- **The classification of monoidal automorphisms of the identity.** The monoidal natural
automorphisms of the identity functor of a finite semisimple linear monoidal category with
simple unit, over an algebraically closed field, are exactly the characters of its universal
grading group: `Aut_⊗(𝟭_C) ≃* Hom(U(C), kˣ)`. An automorphism corresponds to the character whose
value on the degree of a simple object is the scalar by which the automorphism acts on it. -/
def monoidalAutCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroup C →* kˣ) where
  toFun := monoidalAutCharacter (hfin := hfin) k
  invFun := characterMonoidalAut k
  left_inv := characterMonoidalAut_monoidalAutCharacter (hfin := hfin) k
  right_inv := monoidalAutCharacter_characterMonoidalAut (hfin := hfin) k
  map_mul' := (monoidalAutCharacter (hfin := hfin) k).map_mul

/-- The classification isomorphism sends a monoidal automorphism to its character. -/
@[simp]
theorem monoidalAutCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutCharacterEquiv (hfin := hfin) k a = monoidalAutCharacter (hfin := hfin) k a :=
  (rfl)

/-- The inverse of the classification isomorphism sends a character to the monoidal automorphism
acting on each simple object by the value of the character on its degree. -/
@[simp]
theorem monoidalAutCharacterEquiv_symm_apply (χ : universalGradingGroup C →* kˣ) :
    (monoidalAutCharacterEquiv (hfin := hfin) k).symm χ = characterMonoidalAut k χ :=
  (rfl)

end Classification

namespace PivotalCategory

section Twist

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [RigidCategory C]

/-- Twisting a pivotal structure by a character `χ` of the universal grading group multiplies
its component at a simple object `X` by `χ (degree [X])`. -/
theorem characterMonoidalAut_smul_pivotalIso_hom_app_of_simple
    (χ : universalGradingGroup C →* Rˣ) (P : PivotalCategory C) (X : C) [Simple X] :
    (characterMonoidalAut R χ • P).pivotalIso.hom.app X =
      (χ (universalGradingGroup.degree (SimpleClasses.classOf X)) : R) •
        P.pivotalIso.hom.app X := by
  rw [smul_pivotalIso, Iso.trans_hom, NatTrans.comp_app, characterMonoidalAut_app_of_simple,
    Linear.smul_comp]
  -- The identity sits on `(LaxMonoidalFunctor.of (𝟭 C)).obj X`, which is `X` only up to
  -- unfolding, so `Category.id_comp` is applied up to definitional equality.
  exact congrArg _ (Category.id_comp _)

end Twist

section Classification

variable (k : Type w) [Field k] [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)] [RigidCategory C]

include hfin in
/-- **The pivotal structures of a fusion category form a torsor over the characters of its
universal grading group.** Any two pivotal structures `P` and `Q` differ by exactly one
character `χ` of the universal grading group, in the sense that `P` is the twist of `Q` by the
monoidal automorphism of the identity given by `χ`. -/
theorem existsUnique_eq_characterMonoidalAut_smul (P Q : PivotalCategory C) :
    ∃! χ : universalGradingGroup C →* kˣ, P = characterMonoidalAut k χ • Q := by
  have : Nonempty (PivotalCategory C) := ⟨Q⟩
  refine ⟨monoidalAutCharacter (hfin := hfin) k (P /ₛ Q), by simp, fun χ hχ ↦ ?_⟩
  rw [hχ, smul_sdiv, monoidalAutCharacter_characterMonoidalAut (hfin := hfin)]

end Classification

end PivotalCategory

end TauCeti
