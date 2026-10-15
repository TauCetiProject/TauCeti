/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Bounded Borel symbols

Bounded measurable complex functions form a pointwise star algebra. Equality is pointwise;
no measure or almost-everywhere quotient is involved. On a topological space equipped with
its Borel measurable space these are bounded Borel functions. The domain may be empty.

These symbols form the source algebra for bounded Borel functional calculus: constants,
measurable simple functions and restrictions to measurable sets are bounded symbols, and
pullback along a measurable map preserves their pointwise star algebra structure.
-/

public section

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

/-- Membership in the bounded-symbol algebra means measurability and an everywhere uniform
nonnegative norm bound. -/
@[simp] theorem mem_boundedBorelSubalgebra (f : X → ℂ) :
    f ∈ boundedBorelSubalgebra X ↔
      Measurable f ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := (Iff.rfl)

/-- Bounded Borel symbols, with the pointwise algebra inherited from functions. -/
abbrev BoundedBorelFunction : Type _ := ↥(boundedBorelSubalgebra X)

namespace BoundedBorelFunction

variable {X}

instance : FunLike (BoundedBorelFunction X) X ℂ where
  coe f := f.val
  coe_injective := Subtype.val_injective

/-- The subtype and function coercions have the same values. -/
@[simp] theorem val_eq_coe (f : BoundedBorelFunction X) : f.val = ⇑f := (rfl)

/-- Function coercion determines a bounded Borel symbol. -/
theorem coe_injective : Function.Injective
    (DFunLike.coe : BoundedBorelFunction X → X → ℂ) := DFunLike.coe_injective

/-- The zero symbol coerces to the zero function. -/
@[simp] theorem coe_zero : ⇑(0 : BoundedBorelFunction X) = 0 := (rfl)

/-- The unit symbol coerces to the constant unit function. -/
@[simp] theorem coe_one : ⇑(1 : BoundedBorelFunction X) = 1 := (rfl)

/-- Function coercion preserves addition. -/
@[simp] theorem coe_add (f g : BoundedBorelFunction X) : ⇑(f + g) = ⇑f + ⇑g := (rfl)

/-- Function coercion preserves negation. -/
@[simp] theorem coe_neg (f : BoundedBorelFunction X) : ⇑(-f) = -⇑f := (rfl)

/-- Function coercion preserves subtraction. -/
@[simp] theorem coe_sub (f g : BoundedBorelFunction X) : ⇑(f - g) = ⇑f - ⇑g := (rfl)

/-- Function coercion preserves multiplication. -/
@[simp] theorem coe_mul (f g : BoundedBorelFunction X) : ⇑(f * g) = ⇑f * ⇑g := (rfl)

/-- Function coercion preserves scalar multiplication. -/
@[simp] theorem coe_smul (c : ℂ) (f : BoundedBorelFunction X) : ⇑(c • f) = c • ⇑f := (rfl)

/-- Function coercion preserves the star operation. -/
@[simp] theorem coe_star (f : BoundedBorelFunction X) : ⇑(star f) = star ⇑f := (rfl)

/-- Function coercion preserves natural powers. -/
@[simp] theorem coe_pow (f : BoundedBorelFunction X) (n : ℕ) : ⇑(f ^ n) = ⇑f ^ n := (rfl)

/-- Algebra scalars coerce to constant functions. -/
@[simp] theorem coe_algebraMap (c : ℂ) :
    ⇑(algebraMap ℂ (BoundedBorelFunction X) c) = fun _ => c := (rfl)

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
    ofFunction f hf hbound x = f x := (rfl)

/-- Evaluation of an algebra scalar is the constant scalar. -/
@[simp] theorem algebraMap_apply (c : ℂ) (x : X) :
    algebraMap ℂ (BoundedBorelFunction X) c x = c := (rfl)

/-- Evaluation of zero. -/
@[simp] theorem zero_apply (x : X) : (0 : BoundedBorelFunction X) x = 0 := (rfl)

/-- Evaluation of one. -/
@[simp] theorem one_apply (x : X) : (1 : BoundedBorelFunction X) x = 1 := (rfl)

/-- Evaluation of addition. -/
@[simp] theorem add_apply (f g : BoundedBorelFunction X) (x : X) :
    (f + g) x = f x + g x := (rfl)

/-- Evaluation of negation. -/
@[simp] theorem neg_apply (f : BoundedBorelFunction X) (x : X) : (-f) x = -f x := (rfl)

/-- Evaluation of subtraction. -/
@[simp] theorem sub_apply (f g : BoundedBorelFunction X) (x : X) :
    (f - g) x = f x - g x := (rfl)

/-- Evaluation of multiplication. -/
@[simp] theorem mul_apply (f g : BoundedBorelFunction X) (x : X) :
    (f * g) x = f x * g x := (rfl)

/-- Evaluation of scalar multiplication. -/
@[simp] theorem smul_apply (c : ℂ) (f : BoundedBorelFunction X) (x : X) :
    (c • f) x = c * f x := (rfl)

/-- Evaluation of the star operation is complex conjugation. -/
@[simp] theorem star_apply (f : BoundedBorelFunction X) (x : X) :
    (star f) x = star (f x) := (rfl)

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- Pullback of symbols along a measurable map, as a star algebra homomorphism. -/
def compStarAlgHom' (g : X → Y) (hg : Measurable g) :
    BoundedBorelFunction Y →⋆ₐ[ℂ] BoundedBorelFunction X where
  toFun f := ⟨f ∘ g, f.measurable.comp hg, by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    exact ⟨M, hM, fun x => hfM (g x)⟩⟩
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

/-- Pullback evaluates by composition. -/
@[simp] theorem compStarAlgHom'_apply (g : X → Y) (hg : Measurable g)
    (f : BoundedBorelFunction Y) (x : X) : compStarAlgHom' g hg f x = f (g x) := (rfl)

/-- Pullback by the identity is the identity star algebra homomorphism. -/
@[simp] theorem compStarAlgHom'_id :
    compStarAlgHom' (X := X) id measurable_id = StarAlgHom.id ℂ (BoundedBorelFunction X) :=
  (rfl)

/-- Pullback along a composite is composition of the star algebra homomorphisms. -/
theorem compStarAlgHom'_comp (g : X → Y) (hg : Measurable g) (h : Y → Z) (hh : Measurable h) :
    compStarAlgHom' (h ∘ g) (hh.comp hg) = (compStarAlgHom' g hg).comp (compStarAlgHom' h hh) :=
  (rfl)

/-- Restriction to a measurable set and extension by zero, as a non-unital star algebra
homomorphism. It need not preserve the unit because the unit restricts to the set indicator. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) :
    BoundedBorelFunction X →⋆ₙₐ[ℂ] BoundedBorelFunction X where
  toFun f := ⟨s.indicator f, f.measurable.indicator hs, by
    obtain ⟨M, hM, hfM⟩ := f.exists_bound
    exact ⟨M, hM, fun x ↦ (norm_indicator_le_norm_self f x).trans (hfM x)⟩⟩
  map_zero' := by ext x; exact congrFun (Set.indicator_zero ℂ s) x
  map_add' f g := by ext x; exact congrFun (Set.indicator_add s f g) x
  map_mul' f g := by ext x; exact congrFun (Set.indicator_mul s f g) x
  map_smul' c f := by ext x; exact Set.indicator_const_smul_apply s c f x
  map_star' f := by
    ext x
    exact (map_indicator (starAddEquiv : ℂ ≃+ ℂ) s f x).symm

/-- Restriction coerces to the usual set indicator function. -/
@[simp] theorem coe_indicator (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) : ⇑(indicator s hs f) = s.indicator f := (rfl)

/-- Indicator evaluation is the usual set indicator. -/
@[simp] theorem indicator_apply (s : Set X) (hs : MeasurableSet s)
    (f : BoundedBorelFunction X) (x : X) : indicator s hs f x = s.indicator f x := (rfl)

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
  simp only [mul_apply, indicator_apply]
  exact (Set.inter_indicator_mul _ _ x).symm

/-- Pullback commutes with restriction and extension by zero. -/
theorem compStarAlgHom'_indicator (g : X → Y) (hg : Measurable g) (s : Set Y)
    (hs : MeasurableSet s) (f : BoundedBorelFunction Y) :
    compStarAlgHom' g hg (indicator s hs f) =
      indicator (g ⁻¹' s) (hs.preimage hg) (compStarAlgHom' g hg f) := by
  ext x
  simp only [compStarAlgHom'_apply, indicator_apply]
  exact (Set.indicator_comp_right g (g := (f : Y → ℂ)) (s := s) (x := x)).symm

/-- Every measurable complex simple function is an everywhere bounded symbol. -/
noncomputable def ofSimpleFunc (f : MeasureTheory.SimpleFunc X ℂ) : BoundedBorelFunction X :=
  ⟨f, f.measurable, by
    obtain ⟨M, hM⟩ := (f.map norm).exists_forall_le
    exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩⟩

/-- Bundling a simple function preserves its values. -/
@[simp] theorem ofSimpleFunc_apply (f : MeasureTheory.SimpleFunc X ℂ) (x : X) :
    ofSimpleFunc f x = f x := (rfl)

end BoundedBorelFunction
end TauCeti
