/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Bounded Borel symbols

Bounded measurable complex functions form a pointwise star algebra. Equality is pointwise;
no measure or almost-everywhere quotient is involved. On a topological space equipped with
its Borel measurable space these are bounded Borel functions. The domain may be empty.

This is the source algebra requested by `SA-B01` of the self-adjoint spectral theory roadmap.
It does not construct a functional calculus or a spectral measure.
-/

@[expose] public section

noncomputable section

namespace TauCeti

variable (X : Type*) [MeasurableSpace X]

/-- The star subalgebra of measurable functions with an everywhere uniform norm bound. -/
def boundedBorelSubalgebra : StarSubalgebra ℂ (X → ℂ) where
  carrier := {f | Measurable f ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M}
  zero_mem' := ⟨measurable_const, 0, le_rfl, fun _ => by simp⟩
  one_mem' := ⟨measurable_const, 1, zero_le_one, fun _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, M, hM, hfM⟩ ⟨hg, N, hN, hgN⟩
    refine ⟨hf.add hg, M + N, add_nonneg hM hN, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hfM x) (hgN x))
  mul_mem' := by
    rintro f g ⟨hf, M, hM, hfM⟩ ⟨hg, N, hN, hgN⟩
    refine ⟨hf.mul hg, M * N, mul_nonneg hM hN, fun x => ?_⟩
    exact (norm_mul_le _ _).trans (mul_le_mul (hfM x) (hgN x) (norm_nonneg _) hM)
  algebraMap_mem' c := ⟨measurable_const, ‖c‖, norm_nonneg c, fun _ => le_rfl⟩
  star_mem' := by
    rintro f ⟨hf, M, hM, hfM⟩
    refine ⟨?_, M, hM, fun x => ?_⟩
    · exact Complex.continuous_conj.measurable.comp hf
    · simpa using hfM x

/-- Bounded Borel symbols, with the pointwise algebra inherited from functions. -/
abbrev BoundedBorelFunction : Type _ := ↥(boundedBorelSubalgebra X)

namespace BoundedBorelFunction

variable {X}

instance : FunLike (BoundedBorelFunction X) X ℂ where
  coe f := f.val
  coe_injective := Subtype.val_injective

/-- Two symbols are equal when they agree at every point. -/
@[ext] theorem ext {f g : BoundedBorelFunction X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Evaluation of a bounded Borel symbol is measurable. -/
@[fun_prop] theorem measurable (f : BoundedBorelFunction X) : Measurable f := f.property.1

/-- Every symbol has a nonnegative bound valid at every point, including on an empty domain. -/
theorem exists_bound (f : BoundedBorelFunction X) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := f.property.2

/-- Bundle a measurable function with its everywhere bound. -/
def ofFunction (f : X → ℂ) (hf : Measurable f)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) : BoundedBorelFunction X :=
  ⟨f, hf, hbound⟩

/-- Bundling preserves evaluation. -/
@[simp] theorem ofFunction_apply (f : X → ℂ) (hf : Measurable f) (hbound) (x : X) :
    ofFunction f hf hbound x = f x := rfl

/-- The constant bounded Borel symbol. -/
def const (c : ℂ) : BoundedBorelFunction X := algebraMap ℂ _ c

/-- Evaluation of a constant symbol. -/
@[simp] theorem const_apply (c : ℂ) (x : X) : const c x = c := rfl

/-- Evaluation of zero. -/
@[simp] theorem zero_apply (x : X) : (0 : BoundedBorelFunction X) x = 0 := rfl

/-- Evaluation of one. -/
@[simp] theorem one_apply (x : X) : (1 : BoundedBorelFunction X) x = 1 := rfl

/-- Evaluation of addition. -/
@[simp] theorem add_apply (f g : BoundedBorelFunction X) (x : X) :
    (f + g) x = f x + g x := rfl

/-- Evaluation of negation. -/
@[simp] theorem neg_apply (f : BoundedBorelFunction X) (x : X) : (-f) x = -f x := rfl

/-- Evaluation of subtraction. -/
@[simp] theorem sub_apply (f g : BoundedBorelFunction X) (x : X) :
    (f - g) x = f x - g x := rfl

/-- Evaluation of multiplication. -/
@[simp] theorem mul_apply (f g : BoundedBorelFunction X) (x : X) :
    (f * g) x = f x * g x := rfl

/-- Evaluation of scalar multiplication. -/
@[simp] theorem smul_apply (c : ℂ) (f : BoundedBorelFunction X) (x : X) :
    (c • f) x = c * f x := rfl

/-- Evaluation of the star operation is complex conjugation. -/
@[simp] theorem star_apply (f : BoundedBorelFunction X) (x : X) :
    (star f) x = star (f x) := rfl

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- Pullback of symbols along a measurable map, as a star algebra homomorphism. -/
def compHom (g : X → Y) (hg : Measurable g) :
    BoundedBorelFunction Y →⋆ₐ[ℂ] BoundedBorelFunction X where
  toFun f := ⟨f ∘ g, f.measurable.comp hg, by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    exact ⟨M, hM, fun x => hfM (g x)⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- Pullback evaluates by composition. -/
@[simp] theorem compHom_apply (g : X → Y) (hg : Measurable g)
    (f : BoundedBorelFunction Y) (x : X) : compHom g hg f x = f (g x) := rfl

/-- Pullback by the identity does not change a symbol. -/
@[simp] theorem compHom_id (f : BoundedBorelFunction X) :
    compHom id measurable_id f = f := rfl

/-- Successive pullbacks agree with pullback along the composite map. -/
theorem compHom_comp (g : X → Y) (hg : Measurable g) (h : Y → Z) (hh : Measurable h)
    (f : BoundedBorelFunction Z) :
    compHom g hg (compHom h hh f) = compHom (h ∘ g) (hh.comp hg) f := rfl

/-- Restrict a symbol to a measurable set and extend it by zero. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) : BoundedBorelFunction X :=
  ⟨s.indicator f, f.measurable.indicator hs, by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    refine ⟨M, hM, fun x => ?_⟩
    by_cases hx : x ∈ s
    · simpa [Set.indicator_of_mem hx] using hfM x
    · simp [Set.indicator_of_notMem hx, hM]⟩

/-- Indicator evaluation is the usual set indicator. -/
@[simp] theorem indicator_apply (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) (x : X) : indicator s hs f x = s.indicator f x := rfl

/-- The indicator of the empty set vanishes. -/
@[simp] theorem indicator_empty (f : BoundedBorelFunction X) :
    indicator ∅ MeasurableSet.empty f = 0 := by ext; simp

/-- The indicator of the whole domain is the original symbol. -/
@[simp] theorem indicator_univ (f : BoundedBorelFunction X) :
    indicator Set.univ MeasurableSet.univ f = f := by ext; simp

/-- Products of indicator symbols correspond to intersections. -/
theorem indicator_mul_indicator (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f g : BoundedBorelFunction X) :
    indicator s hs f * indicator t ht g = indicator (s ∩ t) (hs.inter ht) (f * g) := by
  ext x
  by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]

/-- Pullback commutes with restriction and extension by zero. -/
theorem compHom_indicator (g : X → Y) (hg : Measurable g) (s : Set Y)
    (hs : MeasurableSet s) (f : BoundedBorelFunction Y) :
    compHom g hg (indicator s hs f) =
      indicator (g ⁻¹' s) (hs.preimage hg) (compHom g hg f) := by
  ext x
  by_cases hx : g x ∈ s <;> simp [hx]

/-- Every measurable complex simple function is an everywhere bounded symbol. -/
noncomputable def ofSimpleFunc (f : MeasureTheory.SimpleFunc X ℂ) : BoundedBorelFunction X :=
  ⟨f, f.measurable, by
    obtain ⟨M, hM⟩ := (f.map norm).exists_forall_le
    exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩⟩

/-- Bundling a simple function preserves its values. -/
@[simp] theorem ofSimpleFunc_apply (f : MeasureTheory.SimpleFunc X ℂ) (x : X) :
    ofSimpleFunc f x = f x := rfl

/-- A constant-one indicator is measurable exactly when its set is measurable.
Thus measurability is a necessary boundary of the indicator constructor. -/
theorem measurable_indicator_one_iff (s : Set X) :
    Measurable (s.indicator (fun _ => (1 : ℂ))) ↔ MeasurableSet s := by
  classical
  refine ⟨fun h => ?_, fun hs => measurable_const.indicator hs⟩
  have hpre := h (measurableSet_singleton (1 : ℂ))
  convert hpre using 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

end BoundedBorelFunction
end TauCeti
