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

This file constructs the unique continuous `A`-algebra transition homomorphisms from models of
`A⟨{f, 1}/1⟩` and `A⟨{1}/f⟩` to a model of `A⟨{f², 1}/f⟩`
(`IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft` and
`IsRationalCompletion.existsUnique_continuous_algHom_laurentRight`), exposes the named transition
maps `IsRationalCompletion.laurentLeftAlgHom` and `laurentRightAlgHom` with their continuity,
algebra, and scalar-tower API, and specializes them to the canonical `ratLoc` models.

## Main definitions

* `TauCeti.Huber.IsRationalCompletion.laurentLeftAlgHom`, `laurentRightAlgHom`,
  `laurentLeftAlgebra`, and `laurentRightAlgebra`: model transition maps and overlap algebras.
* `TauCeti.Huber.laurentLeftAlgHom`, `laurentRightAlgHom`, `laurentLeftAlgebra`, and
  `laurentRightAlgebra`: specializations to `ratLoc` (with `scoped[TauCeti.Huber.Laurent]`
  instances).

## Main results

* `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft`,
  `existsUnique_continuous_algHom_laurentRight`, `continuous_laurentLeftAlgHom`,
  `continuous_laurentRightAlgHom`, `isScalarTower_laurentLeft`, and `isScalarTower_laurentRight`.
* `TauCeti.Huber.continuous_laurentLeftAlgHom`, `continuous_laurentRightAlgHom`,
  `laurentLeftAlgHom_coe`, `laurentRightAlgHom_coe`, `isScalarTower_laurentLeft`, and
  `isScalarTower_laurentRight`.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section LaurentTransition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DecidableEq A]
  {P : PairOfDefinition A} {f : A} {B₁₂ : Type*} [CommRing B₁₂] [TopologicalSpace B₁₂]
  [Algebra A B₁₂] {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}

section Models

variable {B₁ B₂ : Type*} [CommRing B₁] [TopologicalSpace B₁] [Algebra A B₁]
  [CommRing B₂] [TopologicalSpace B₂] [Algebra A B₂]
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}

/-- Unique continuous `A`-algebra map `B₁ →ₐ[A] B₁₂` from a model of `A⟨{f, 1}/1⟩` to a model of
`A⟨{f², 1}/f⟩`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom_laurentLeft
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : ∃! ρ₁ : B₁ →ₐ[A] B₁₂, Continuous ρ₁ :=
  h₁.existsUnique_continuous_algHom_of_refines h₁₂ (one_mul f).symm fun t ht ↦
    (Finset.mem_insert.mp ht).elim (fun h ↦ Or.inr (by simp [h]))
      (fun h ↦ Or.inl (Finset.mem_singleton.mp h))

/-- Unique continuous `A`-algebra map `B₂ →ₐ[A] B₁₂` from a model of `A⟨{1}/f⟩` to a model of
`A⟨{f², 1}/f⟩`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom_laurentRight
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : ∃! ρ₂ : B₂ →ₐ[A] B₁₂, Continuous ρ₂ :=
  h₂.existsUnique_continuous_algHom_of_refines h₁₂ (mul_one f).symm fun t ht ↦
    Or.inr (by rw [Finset.mem_singleton.mp ht]; simp)

/-- Canonical continuous `A`-algebra map `B₁ →ₐ[A] B₁₂` from a model of `A⟨{f, 1}/1⟩` to a model
of `A⟨{f², 1}/f⟩`. -/
noncomputable def IsRationalCompletion.laurentLeftAlgHom
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : B₁ →ₐ[A] B₁₂ :=
  (h₁.existsUnique_continuous_algHom_laurentLeft h₁₂).choose
/-- `IsRationalCompletion.laurentLeftAlgHom` is continuous. -/
theorem IsRationalCompletion.continuous_laurentLeftAlgHom
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : Continuous (h₁.laurentLeftAlgHom h₁₂) :=
  (h₁.existsUnique_continuous_algHom_laurentLeft h₁₂).choose_spec.1
/-- Canonical `B₁`-algebra structure on `B₁₂` induced by
`IsRationalCompletion.laurentLeftAlgHom`. -/
@[instance_reducible] noncomputable def IsRationalCompletion.laurentLeftAlgebra
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : Algebra B₁ B₁₂ :=
  (h₁.laurentLeftAlgHom h₁₂).toRingHom.toAlgebra
/-- The structure map of `IsRationalCompletion.laurentLeftAlgebra` is `laurentLeftAlgHom`. -/
theorem IsRationalCompletion.algebraMap_laurentLeftAlgebra
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    letI := h₁.laurentLeftAlgebra h₁₂
    algebraMap B₁ B₁₂ = (h₁.laurentLeftAlgHom h₁₂).toRingHom := by rfl
/-- `IsRationalCompletion.laurentLeftAlgebra` makes `A → B₁ → B₁₂` a scalar tower. -/
theorem IsRationalCompletion.isScalarTower_laurentLeft
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    letI := h₁.laurentLeftAlgebra h₁₂; IsScalarTower A B₁ B₁₂ :=
  let _ := h₁.laurentLeftAlgebra h₁₂
  IsScalarTower.of_algebraMap_eq fun r ↦ ((h₁.laurentLeftAlgHom h₁₂).commutes r).symm
/-- On the dense image of `Localization.Away (1 : A)`, `IsRationalCompletion.laurentLeftAlgHom`
intertwines `localizationAlgHom` with the canonical lift `Away 1 →+* Away f`. -/
@[simp] theorem IsRationalCompletion.laurentLeftAlgHom_localizationAlgHom
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) (x : Localization.Away (1 : A)) :
    h₁.laurentLeftAlgHom h₁₂ (h₁.localizationAlgHom x) =
      h₁₂.localizationAlgHom (IsLocalization.Away.lift (1 : A)
        (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩) x) :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (1 : A))
    (j := (h₁.laurentLeftAlgHom h₁₂).toRingHom.comp h₁.localizationAlgHom.toRingHom)
    (k := h₁₂.localizationAlgHom.toRingHom.comp (IsLocalization.Away.lift (1 : A)
      (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩))) (RingHom.ext fun a ↦ by
        simp)) x

/-- Canonical continuous `A`-algebra map `B₂ →ₐ[A] B₁₂` from a model of `A⟨{1}/f⟩` to a model of
`A⟨{f², 1}/f⟩`. -/
noncomputable def IsRationalCompletion.laurentRightAlgHom
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : B₂ →ₐ[A] B₁₂ :=
  (h₂.existsUnique_continuous_algHom_laurentRight h₁₂).choose
/-- `IsRationalCompletion.laurentRightAlgHom` is continuous. -/
theorem IsRationalCompletion.continuous_laurentRightAlgHom
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    Continuous (h₂.laurentRightAlgHom h₁₂) :=
  (h₂.existsUnique_continuous_algHom_laurentRight h₁₂).choose_spec.1
/-- Canonical `B₂`-algebra structure on `B₁₂` induced by
`IsRationalCompletion.laurentRightAlgHom`. -/
@[instance_reducible] noncomputable def IsRationalCompletion.laurentRightAlgebra
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) : Algebra B₂ B₁₂ :=
  (h₂.laurentRightAlgHom h₁₂).toRingHom.toAlgebra
/-- The structure map of `IsRationalCompletion.laurentRightAlgebra` is `laurentRightAlgHom`. -/
theorem IsRationalCompletion.algebraMap_laurentRightAlgebra
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    letI := h₂.laurentRightAlgebra h₁₂
    algebraMap B₂ B₁₂ = (h₂.laurentRightAlgHom h₁₂).toRingHom := by rfl
/-- `IsRationalCompletion.laurentRightAlgebra` makes `A → B₂ → B₁₂` a scalar tower. -/
theorem IsRationalCompletion.isScalarTower_laurentRight
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    letI := h₂.laurentRightAlgebra h₁₂; IsScalarTower A B₂ B₁₂ :=
  let _ := h₂.laurentRightAlgebra h₁₂
  IsScalarTower.of_algebraMap_eq fun r ↦ ((h₂.laurentRightAlgHom h₁₂).commutes r).symm
/-- On the dense image of `Localization.Away f`, `IsRationalCompletion.laurentRightAlgHom`
intertwines the two canonical maps from `Localization.Away f`. -/
@[simp] theorem IsRationalCompletion.laurentRightAlgHom_localizationAlgHom
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) (x : Localization.Away f) :
    h₂.laurentRightAlgHom h₁₂ (h₂.localizationAlgHom x) = h₁₂.localizationAlgHom x :=
  h₂.map_localizationAlgHom h₁₂ (RingHom.ext (h₂.laurentRightAlgHom h₁₂).commutes) x

end Models

/-- Canonical continuous `A`-algebra transition map `A⟨{f, 1}/1⟩ →ₐ[A] A⟨{f², 1}/f⟩` between
`ratLoc` models. -/
noncomputable def laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {f, 1} 1 hden₁ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  (isRationalCompletion_ratLoc P {f, 1} 1 (isOpen_span_of_one_mem (by simp))).laurentLeftAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
/-- `laurentLeftAlgHom` is continuous. -/
theorem continuous_laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)) :=
  (isRationalCompletion_ratLoc P {f, 1} 1
    (isOpen_span_of_one_mem (by simp))).continuous_laurentLeftAlgHom _
/-- On the dense image of `A₁`, `laurentLeftAlgHom` sends `1` to `f / f`. -/
@[simp] theorem laurentLeftAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away (1 : A)) :
    laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂) (@Completion.coe' _
        (P.locUniformSpace ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁) x) =
      @Completion.coe' _
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂)
        (IsLocalization.Away.lift (1 : A)
          (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩) x) := by
  simpa only [laurentLeftAlgHom, localizationAlgHom_ratLoc] using
    (isRationalCompletion_ratLoc P {f, 1} 1
      (isOpen_span_of_one_mem (by simp))).laurentLeftAlgHom_localizationAlgHom
      (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp))) x

/-- Canonical continuous `A`-algebra transition map `A⟨{1}/f⟩ →ₐ[A] A⟨{f², 1}/f⟩` between `ratLoc`
models. -/
noncomputable def laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {1} f hden₂ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  (isRationalCompletion_ratLoc P {1} f (isOpen_span_of_one_mem (by simp))).laurentRightAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
/-- `laurentRightAlgHom` is continuous. -/
theorem continuous_laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)) :=
  (isRationalCompletion_ratLoc P {1} f
    (isOpen_span_of_one_mem (by simp))).continuous_laurentRightAlgHom _
/-- On the dense image of `A_f`, `laurentRightAlgHom` fixes each fraction elementwise. -/
@[simp] theorem laurentRightAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away f) :
    laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)
        (@Completion.coe' _ (P.locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂) x) =
      @Completion.coe' _
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂) x := by
  simpa only [laurentRightAlgHom, localizationAlgHom_ratLoc] using
    (isRationalCompletion_ratLoc P {1} f
      (isOpen_span_of_one_mem (by simp))).laurentRightAlgHom_localizationAlgHom
      (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp))) x

/-- Canonical `A⟨{f, 1}/1⟩`-algebra structure on `A⟨{f², 1}/f⟩` induced by `laurentLeftAlgHom`. -/
@[instance_reducible] noncomputable def laurentLeftAlgebra (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Algebra (ratLoc P {f, 1} 1 hden₁) (ratLoc P {f * f, 1} f hden₁₂) :=
  (isRationalCompletion_ratLoc P {f, 1} 1 (isOpen_span_of_one_mem (by simp))).laurentLeftAlgebra
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.laurentLeftAlgebra
/-- Canonical `A⟨{1}/f⟩`-algebra structure on `A⟨{f², 1}/f⟩` induced by `laurentRightAlgHom`. -/
@[instance_reducible] noncomputable def laurentRightAlgebra (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Algebra (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) :=
  (isRationalCompletion_ratLoc P {1} f (isOpen_span_of_one_mem (by simp))).laurentRightAlgebra
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
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
  (isRationalCompletion_ratLoc P {f, 1} 1
    (isOpen_span_of_one_mem (by simp))).isScalarTower_laurentLeft
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.isScalarTower_laurentLeft
/-- `laurentRightAlgebra` makes `A → A⟨{1}/f⟩ → A⟨{f², 1}/f⟩` a scalar tower. -/
theorem isScalarTower_laurentRight (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    IsScalarTower A (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) :=
  (isRationalCompletion_ratLoc P {1} f
    (isOpen_span_of_one_mem (by simp))).isScalarTower_laurentRight
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
scoped[TauCeti.Huber.Laurent] attribute [instance] TauCeti.Huber.isScalarTower_laurentRight

end ScopedAPI
end LaurentTransition

end TauCeti.Huber

end
