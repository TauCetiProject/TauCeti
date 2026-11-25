/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Groupoid
public import TauCeti.CategoryTheory.FiberedCategory.Fiber

/-!
# Categories fibred in groupoids

A functor `p : 𝒳 ⥤ 𝒮` makes `𝒳` a category fibred in groupoids over `𝒮` if every morphism of `𝒮`
has a lift with any prescribed target lying over its codomain, and every morphism of `𝒳` is
strongly Cartesian over its image (Stacks, Definition 4.35.1 (003T)).
Equivalently, `p` is a fibered category whose fibers are groupoids (Stacks, Lemma 4.35.2 (003V)).

The Grothendieck construction of a pseudofunctor with groupoid fibers is fibred in groupoids
(`TauCeti.CategoryTheory.FiberedCategory.Grothendieck`).

## Main declarations

* `CategoryTheory.Functor.IsFiberedInGroupoids`: the functor `p` makes its source a category
  fibred in groupoids.
* `CategoryTheory.Functor.IsFiberedInGroupoids.isFibered`: a category fibred in groupoids is
  fibered.
* `CategoryTheory.Functor.IsFiberedInGroupoids.isGroupoid_fiber`: the fibers of a category fibred
  in groupoids are groupoids.
* `CategoryTheory.Functor.IsFiberedInGroupoids.of_isGroupoid_fiber`: a fibered category whose
  fibers are groupoids is fibred in groupoids.
* `CategoryTheory.Functor.isFiberedInGroupoids_iff`: the two descriptions agree.
* `CategoryTheory.Functor.IsFiberedInGroupoids.reflectsIsomorphisms`: the projection of a category
  fibred in groupoids reflects isomorphisms.

## References

* [Stacks Project, Section 003S](https://stacks.math.columbia.edu/tag/003S)
* [A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent
  theory*][vistoli2004]
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Functor Opposite

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The functor `p : 𝒳 ⥤ 𝒮` makes `𝒳` a category fibred in groupoids over `𝒮`: every morphism of
`𝒮` has a Cartesian lift with any prescribed target lying over its codomain, and every
morphism of `𝒳` is strongly Cartesian over every morphism of `𝒮` it lies over (Stacks,
Definition 4.35.1 (003T)). -/
@[stacks 003T]
class Functor.IsFiberedInGroupoids (p : 𝒳 ⥤ 𝒮) : Prop extends p.IsPreFibered where
  isStronglyCartesian {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] :
    p.IsStronglyCartesian f φ

namespace Functor.IsFiberedInGroupoids

attribute [instance] IsFiberedInGroupoids.isStronglyCartesian

/-- A fibered category whose fibers are groupoids is fibred in groupoids (Stacks, Lemma 4.35.2
(003V)). -/
@[stacks 003V]
lemma of_isGroupoid_fiber (p : 𝒳 ⥤ 𝒮) [p.IsFibered] [∀ S, IsGroupoid (Fiber p S)] :
    p.IsFiberedInGroupoids where
  isStronglyCartesian {R _ _ b} f φ _ := by
    -- Factor `φ` as a vertical morphism `χ` followed by a Cartesian lift `ψ` of `f`.
    let ψ := IsPreFibered.pullbackMap (IsHomLift.codomain_eq p f φ) f
    let χ := IsStronglyCartesian.map p f ψ (Category.id_comp f).symm φ
    -- The vertical morphism `χ` is a morphism of the fiber over `R`, hence an isomorphism.
    have : IsIso χ := by
      rw [← Fiber.fiberInclusion_homMk p R χ]
      exact Functor.map_isIso Fiber.fiberInclusion (Fiber.homMk p R χ)
    have h : χ ≫ ψ = φ := IsStronglyCartesian.fac p f ψ (Category.id_comp f).symm φ
    have : p.IsStronglyCartesian (𝟙 R ≫ f) (χ ≫ ψ) := inferInstance
    rw [Category.id_comp, h] at this
    exact this

variable (p : 𝒳 ⥤ 𝒮) [p.IsFiberedInGroupoids]

/-- A category fibred in groupoids is a fibered category. -/
instance isFibered : p.IsFibered where
  comp := by intros; infer_instance

/-- In a category fibred in groupoids, `p` reflects isomorphisms: a morphism lying over an
isomorphism is strongly Cartesian, hence an isomorphism
(Mathlib's `Functor.IsStronglyCartesian.isIso_of_base_isIso`). -/
instance reflectsIsomorphisms : p.ReflectsIsomorphisms where
  reflects φ _ := IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ

/-- The fibers of a category fibred in groupoids are groupoids. -/
instance isGroupoid_fiber (S : 𝒮) : IsGroupoid (Fiber p S) where
  all_isIso φ := by
    have : IsIso (Fiber.fiberInclusion.map φ) :=
      IsStronglyCartesian.isIso_of_base_isIso p (𝟙 S) _
    exact isIso_of_reflects_iso φ Fiber.fiberInclusion

end Functor.IsFiberedInGroupoids

/-- A functor makes its source a category fibred in groupoids exactly when it is a fibered
category whose fibers are groupoids (Stacks, Lemma 4.35.2 (003V)). -/
lemma Functor.isFiberedInGroupoids_iff (p : 𝒳 ⥤ 𝒮) :
    p.IsFiberedInGroupoids ↔ p.IsFibered ∧ ∀ S, IsGroupoid (Fiber p S) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ .of_isGroupoid_fiber p⟩

end CategoryTheory
