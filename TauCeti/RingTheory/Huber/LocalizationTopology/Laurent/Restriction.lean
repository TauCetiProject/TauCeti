/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Canonical transition maps for simple Laurent covers

This file constructs the unique continuous `A`-algebra transition homomorphisms from models of the
two pieces `A⟨{f, 1}/1⟩` and `A⟨{1}/f⟩` of a simple Laurent cover to a model of their overlap
`A⟨{f², 1}/f⟩` (`IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft` and
`IsRationalCompletion.existsUnique_continuous_algHom_laurentRight`), together with the canonical
`ratLoc` maps `laurentLeftAlgHom` and `laurentRightAlgHom`, their computation rules on dense
images of the uncompleted localisations, and the induced overlap algebra structures and scalar
towers.

## Main definitions

* `TauCeti.Huber.laurentLeftAlgHom` and `TauCeti.Huber.laurentRightAlgHom`: the canonical
  continuous `A`-algebra transition maps `A⟨{f, 1}/1⟩ →ₐ[A] A⟨{f², 1}/f⟩` and
  `A⟨{1}/f⟩ →ₐ[A] A⟨{f², 1}/f⟩`.
* `TauCeti.Huber.laurentLeftAlgebra` and `TauCeti.Huber.laurentRightAlgebra`: the overlap algebra
  structures on `A⟨{f², 1}/f⟩` induced by `laurentLeftAlgHom` and `laurentRightAlgHom`
  (registered as `scoped[TauCeti.Huber.Laurent]` instances).

## Main results

* `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft` and
  `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom_laurentRight`: unique
  continuous transition maps from models of `A⟨{f, 1}/1⟩` and `A⟨{1}/f⟩` to a model of
  `A⟨{f², 1}/f⟩`.
* `TauCeti.Huber.continuous_laurentLeftAlgHom` and `TauCeti.Huber.continuous_laurentRightAlgHom`:
  continuity of the canonical transition maps.
* `TauCeti.Huber.laurentLeftAlgHom_coe` and `TauCeti.Huber.laurentRightAlgHom_coe`: computation
  rules for the canonical transition maps on the dense images of the uncompleted localisations.
* `TauCeti.Huber.isScalarTower_laurentLeft` and `TauCeti.Huber.isScalarTower_laurentRight`:
  scalar tower compatibility of `laurentLeftAlgebra` and `laurentRightAlgebra` over `A`.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section LaurentTransition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DecidableEq A]
  {P : PairOfDefinition A} {f : A} {B₁₂ : Type*} [CommRing B₁₂] [TopologicalSpace B₁₂]
  [Algebra A B₁₂] {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}

/-- There is a unique continuous `A`-algebra transition map `B₁ →ₐ[A] B₁₂` from any model `B₁` of
`A⟨{f, 1}/1⟩` to any model `B₁₂` of `A⟨{f², 1}/f⟩`: in `B₁₂`, `f = f² / f` is a distinguished
fraction and `1 / 1 = 1`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft {B₁ : Type*} [CommRing B₁]
    [TopologicalSpace B₁] [Algebra A B₁]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₁ : B₁ →ₐ[A] B₁₂, Continuous ρ₁ :=
  h₁.existsUnique_continuous_algHom_of_refines h₁₂ (one_mul f).symm fun t ht ↦
    (Finset.mem_insert.mp ht).elim (fun h ↦ Or.inr (by simp [h]))
      (fun h ↦ Or.inl (Finset.mem_singleton.mp h))

/-- There is a unique continuous `A`-algebra transition map `B₂ →ₐ[A] B₁₂` from any model `B₂` of
`A⟨{1}/f⟩` to any model `B₁₂` of `A⟨{f², 1}/f⟩`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom_laurentRight {B₂ : Type*} [CommRing B₂]
    [TopologicalSpace B₂] [Algebra A B₂]
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₂ : B₂ →ₐ[A] B₁₂, Continuous ρ₂ :=
  h₂.existsUnique_continuous_algHom_of_refines h₁₂ (mul_one f).symm fun t ht ↦
    Or.inr (by rw [Finset.mem_singleton.mp ht]; simp)

/-- The canonical continuous `A`-algebra transition map `A⟨{f, 1}/1⟩ →ₐ[A] A⟨{f², 1}/f⟩` between
the canonical `ratLoc` models of the first Laurent piece and the overlap. -/
noncomputable def laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {f, 1} 1 hden₁ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  ((isRationalCompletion_ratLoc P {f, 1} 1
      (isOpen_span_of_one_mem (by simp))).existsUnique_continuous_algHom_laurentLeft
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose

/-- `laurentLeftAlgHom` is continuous. -/
theorem continuous_laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)) :=
  ((isRationalCompletion_ratLoc P {f, 1} 1
      (isOpen_span_of_one_mem (by simp))).existsUnique_continuous_algHom_laurentLeft
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose_spec.1

/-- On the dense image of `A₁`, `laurentLeftAlgHom` acts by the localisation map sending `1` to
`f / f`. -/
@[simp]
theorem laurentLeftAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away (1 : A)) :
    laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)
        (@UniformSpace.Completion.coe' (Localization.Away (1 : A))
          (P.locUniformSpace ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁) x) =
      @UniformSpace.Completion.coe' (Localization.Away f)
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂)
        (IsLocalization.Away.lift (1 : A)
          (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩) x) := by
  let _ := P.locUniformSpace _ 1 _ hden₁
  have _ := P.isUniformAddGroup_locUniformSpace _ 1 _ hden₁
  have _ := P.isTopologicalRing_locUniformSpace _ 1 _ hden₁
  let _ := P.locUniformSpace _ f _ hden₁₂
  have _ := P.isUniformAddGroup_locUniformSpace _ f _ hden₁₂
  have _ := P.isTopologicalRing_locUniformSpace _ f _ hden₁₂
  have h : (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)).toRingHom.comp
      UniformSpace.Completion.coeRingHom = UniformSpace.Completion.coeRingHom.comp
      (IsLocalization.Away.lift (1 : A)
        (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (1 : A)) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, UniformSpace.Completion.coe_coeRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IsLocalization.Away.lift_eq]
    rw [← P.toCompletionLoc_apply ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁ a,
      ← algebraMap_ratLoc, (laurentLeftAlgHom P f).commutes a, algebraMap_ratLoc,
      P.toCompletionLoc_apply]
  exact RingHom.congr_fun h x

/-- The canonical continuous `A`-algebra transition map `A⟨{1}/f⟩ →ₐ[A] A⟨{f², 1}/f⟩` between
the canonical `ratLoc` models of the second Laurent piece and the overlap. -/
noncomputable def laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {1} f hden₂ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  ((isRationalCompletion_ratLoc P {1} f
      (isOpen_span_of_one_mem (by simp))).existsUnique_continuous_algHom_laurentRight
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose

/-- `laurentRightAlgHom` is continuous. -/
theorem continuous_laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)) :=
  ((isRationalCompletion_ratLoc P {1} f
      (isOpen_span_of_one_mem (by simp))).existsUnique_continuous_algHom_laurentRight
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose_spec.1

/-- On the dense image of `A_f`, `laurentRightAlgHom` fixes each fraction elementwise. -/
@[simp]
theorem laurentRightAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away f) :
    laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)
        (@UniformSpace.Completion.coe' (Localization.Away f)
          (P.locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂) x) =
      @UniformSpace.Completion.coe' (Localization.Away f)
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂) x := by
  let c₂ : Localization.Away f →+* ratLoc P {1} f hden₂ :=
    let _ := P.locUniformSpace _ f _ hden₂
    have _ := P.isUniformAddGroup_locUniformSpace _ f _ hden₂
    have _ := P.isTopologicalRing_locUniformSpace _ f _ hden₂
    UniformSpace.Completion.coeRingHom
  let c₁₂ : Localization.Away f →+* ratLoc P {f * f, 1} f hden₁₂ :=
    let _ := P.locUniformSpace _ f _ hden₁₂
    have _ := P.isUniformAddGroup_locUniformSpace _ f _ hden₁₂
    have _ := P.isTopologicalRing_locUniformSpace _ f _ hden₁₂
    UniformSpace.Completion.coeRingHom
  have h : (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)).toRingHom.comp c₂ =
      c₁₂ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a ↦ ?_)
    have hc₂ : c₂ (algebraMap A (Localization.Away f) a) = algebraMap A (ratLoc P {1} f hden₂) a :=
      (P.toCompletionLoc_apply _ f _ hden₂ a).symm.trans
        (RingHom.congr_fun (algebraMap_ratLoc P {1} f hden₂) a).symm
    have hc₁₂ : c₁₂ (algebraMap A (Localization.Away f) a) =
        algebraMap A (ratLoc P {f * f, 1} f hden₁₂) a :=
      (P.toCompletionLoc_apply _ f _ hden₁₂ a).symm.trans
        (RingHom.congr_fun (algebraMap_ratLoc P {f * f, 1} f hden₁₂) a).symm
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      hc₂, hc₁₂, (laurentRightAlgHom P f).commutes]
  exact RingHom.congr_fun h x

/-- The canonical `A⟨{f, 1}/1⟩`-algebra structure on the overlap `A⟨{f², 1}/f⟩` induced by
`laurentLeftAlgHom`. -/
@[instance_reducible]
noncomputable def laurentLeftAlgebra (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Algebra (ratLoc P {f, 1} 1 hden₁) (ratLoc P {f * f, 1} f hden₁₂) :=
  (laurentLeftAlgHom P f).toRingHom.toAlgebra

scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.laurentLeftAlgebra

/-- The canonical `A⟨{1}/f⟩`-algebra structure on the overlap `A⟨{f², 1}/f⟩` induced by
`laurentRightAlgHom`. -/
@[instance_reducible]
noncomputable def laurentRightAlgebra (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Algebra (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) :=
  (laurentRightAlgHom P f).toRingHom.toAlgebra

scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.laurentRightAlgebra

section ScopedAPI

open scoped TauCeti.Huber.Laurent

/-- The structure map of `laurentLeftAlgebra` is `laurentLeftAlgHom`. -/
@[simp] theorem algebraMap_laurentLeftAlgebra (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    algebraMap (ratLoc P {f, 1} 1 hden₁) (ratLoc P {f * f, 1} f hden₁₂) =
      (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)).toRingHom := by rfl

/-- The structure map of `laurentRightAlgebra` is `laurentRightAlgHom`. -/
@[simp] theorem algebraMap_laurentRightAlgebra (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    algebraMap (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) =
      (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)).toRingHom := by rfl

/-- The structure map of `laurentLeftAlgebra` is continuous. -/
theorem continuous_algebraMap_laurentLeftAlgebra (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (algebraMap (ratLoc P {f, 1} 1 hden₁) (ratLoc P {f * f, 1} f hden₁₂)) :=
  continuous_laurentLeftAlgHom P f

/-- The structure map of `laurentRightAlgebra` is continuous. -/
theorem continuous_algebraMap_laurentRightAlgebra (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (algebraMap (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂)) :=
  continuous_laurentRightAlgHom P f

/-- `laurentLeftAlgebra` makes `A → A⟨{f, 1}/1⟩ → A⟨{f², 1}/f⟩` a scalar tower. -/
theorem isScalarTower_laurentLeft (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    IsScalarTower A (ratLoc P {f, 1} 1 hden₁) (ratLoc P {f * f, 1} f hden₁₂) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ ((laurentLeftAlgHom P f).commutes r).symm

scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.isScalarTower_laurentLeft

/-- `laurentRightAlgebra` makes `A → A⟨{1}/f⟩ → A⟨{f², 1}/f⟩` a scalar tower. -/
theorem isScalarTower_laurentRight (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    IsScalarTower A (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ ((laurentRightAlgHom P f).commutes r).symm

scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.isScalarTower_laurentRight

end ScopedAPI

end LaurentTransition

end TauCeti.Huber

end
