/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Action.FullSubcategory
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Objectwise congruence invariance of categorical group actions

For a group `H` acting on `C` and a family of subgroups `K : ℕ → Subgroup H`,
`congruenceInvariant K` is the object property that some `K N`, with `0 < N`, fixes the
object up to isomorphism. `IsObjectwiseCongruenceInvariant K C` requires this for every
object, allowing the bound to depend on the object.

Equivariant functors preserve this property, and fully faithful equivariant functors
reflect it. Consequently it is invariant under equivariant equivalence and restricts
to invariant full subcategories. Equivariance uses Mathlib's `Functor.LeftLinear`;
restriction uses the native full-subcategory action.

The fixing isomorphisms are only required to exist separately for each group element.
They carry no multiplication coherence or rational integration data. No normality or
monotonicity of `K` is needed for these comparisons.

## References

`congruenceInvariant` follows the objectwise `K_N`-invariance condition in Frenkel's
local-category discussion:

* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  §1.3.4 (congruence subgroups and stability under twisting).
* Edward Frenkel and Dennis Gaitsgory,
  [Local geometric Langlands correspondence and affine Kac–Moody algebras](https://arxiv.org/abs/math/0508382).
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory MonoidalLeftAction

variable {H : Type*} [Group H] (K : ℕ → Subgroup H)
variable {C : Type*} [Category* C] [MonoidalLeftAction (Discrete H) C]

/-- Objects fixed up to isomorphism by some positive-indexed congruence subgroup.
The isomorphisms need not satisfy any coherence condition. -/
def congruenceInvariant : ObjectProperty C := fun X =>
  ∃ N : ℕ, 0 < N ∧ ∀ g ∈ K N, Nonempty ((Discrete.mk g) ⊙ₗ X ≅ X)

lemma congruenceInvariant_iff (X : C) :
    congruenceInvariant K X ↔
      ∃ N : ℕ, 0 < N ∧ ∀ g ∈ K N, Nonempty ((Discrete.mk g) ⊙ₗ X ≅ X) := by
  rfl

/-- Every object is fixed up to isomorphism by a positive-indexed congruence subgroup;
the subgroup may depend on the object. -/
def IsObjectwiseCongruenceInvariant (C : Type*) [Category* C]
    [MonoidalLeftAction (Discrete H) C] : Prop :=
  ∀ X : C, congruenceInvariant K X

lemma isObjectwiseCongruenceInvariant_iff :
    IsObjectwiseCongruenceInvariant K C ↔ ∀ X : C, congruenceInvariant K X := by
  rfl

instance : (congruenceInvariant K (C := C)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e := by
    rintro ⟨N, hN, hX⟩
    refine ⟨N, hN, fun g hg => ?_⟩
    obtain ⟨i⟩ := hX g hg
    exact ⟨(actionLeft C (Discrete.mk g)).mapIso e.symm ≪≫ i ≪≫ e⟩

variable {K}
variable {D : Type*} [Category* D] [MonoidalLeftAction (Discrete H) D]

/-- An equivariant functor preserves the fixing subgroup of each object. -/
lemma congruenceInvariant_map (F : C ⥤ D) [F.LeftLinear (Discrete H)] {X : C}
    (hX : congruenceInvariant K X) : congruenceInvariant K (F.obj X) := by
  obtain ⟨N, hN, hX⟩ := hX
  refine ⟨N, hN, fun g hg => ?_⟩
  obtain ⟨i⟩ := hX g hg
  exact ⟨Functor.LeftLinear.μₗIso F (Discrete.mk g) X ≪≫ F.mapIso i⟩

/-- A fully faithful equivariant functor reflects the fixing subgroup of each object. -/
lemma congruenceInvariant_of_map (F : C ⥤ D) [F.LeftLinear (Discrete H)]
    [F.Full] [F.Faithful] {X : C} (hX : congruenceInvariant K (F.obj X)) :
    congruenceInvariant K X := by
  obtain ⟨N, hN, hX⟩ := hX
  refine ⟨N, hN, fun g hg => ?_⟩
  obtain ⟨i⟩ := hX g hg
  exact ⟨F.preimageIso ((Functor.LeftLinear.μₗIso F (Discrete.mk g) X).symm ≪≫ i)⟩

@[simp]
lemma congruenceInvariant_map_iff (F : C ⥤ D) [F.LeftLinear (Discrete H)]
    [F.Full] [F.Faithful] (X : C) :
    congruenceInvariant K (F.obj X) ↔ congruenceInvariant K X :=
  ⟨congruenceInvariant_of_map F, congruenceInvariant_map F⟩

/-- Essential surjectivity lets an equivariant functor transfer objectwise congruence
invariance to its entire target category. -/
lemma IsObjectwiseCongruenceInvariant.of_essSurj (h : IsObjectwiseCongruenceInvariant K C)
    (F : C ⥤ D) [F.LeftLinear (Discrete H)] [F.EssSurj] :
    IsObjectwiseCongruenceInvariant K D := by
  intro Y
  exact (congruenceInvariant K).prop_of_iso (F.objObjPreimageIso Y)
    (congruenceInvariant_map F (h (F.objPreimage Y)))

/-- Objectwise congruence invariance pulls back along a fully faithful equivariant functor. -/
lemma IsObjectwiseCongruenceInvariant.of_fullyFaithful
    (h : IsObjectwiseCongruenceInvariant K D) (F : C ⥤ D)
    [F.LeftLinear (Discrete H)] [F.Full] [F.Faithful] :
    IsObjectwiseCongruenceInvariant K C := by
  intro X
  exact congruenceInvariant_of_map F (h (F.obj X))

/-- Objectwise congruence invariance is independent of an equivariant presentation of
the category. Only the forward functor of the equivalence needs a specified lineator. -/
lemma isObjectwiseCongruenceInvariant_iff_of_equivalence (e : C ≌ D)
    [e.functor.LeftLinear (Discrete H)] :
    IsObjectwiseCongruenceInvariant K C ↔ IsObjectwiseCongruenceInvariant K D :=
  ⟨fun h => h.of_essSurj e.functor, fun h => h.of_fullyFaithful e.functor⟩

variable (K) (P : ObjectProperty C) [P.IsStableUnderLeftAction (Discrete H)]

/-- For a stable full subcategory, congruence invariance of an object is equivalent to
congruence invariance of its underlying ambient object, with the same fixing subgroup. -/
@[simp]
lemma congruenceInvariant_fullSubcategory_iff (X : P.FullSubcategory) :
    congruenceInvariant K X ↔ congruenceInvariant K X.obj := by
  exact (congruenceInvariant_map_iff P.ι X).symm

/-- A stable full subcategory is objectwise congruence invariant exactly when all objects
satisfying its defining property are congruence invariant in the ambient category. -/
@[simp]
lemma isObjectwiseCongruenceInvariant_fullSubcategory_iff :
    IsObjectwiseCongruenceInvariant K P.FullSubcategory ↔ P ≤ congruenceInvariant K := by
  constructor
  · intro h X hX
    exact (congruenceInvariant_fullSubcategory_iff K P ⟨X, hX⟩).mp (h ⟨X, hX⟩)
  · intro h X
    exact (congruenceInvariant_fullSubcategory_iff K P X).mpr (h X.obj X.property)

/-- Restricting an objectwise congruence invariant action to a stable full subcategory
preserves objectwise congruence invariance. -/
lemma IsObjectwiseCongruenceInvariant.fullSubcategory
    (h : IsObjectwiseCongruenceInvariant K C) :
    IsObjectwiseCongruenceInvariant K P.FullSubcategory :=
  h.of_fullyFaithful P.ι

end TauCeti
