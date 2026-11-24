/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Order.Filter.TendstoCofinite
public import TauCeti.Order.Filter.ZeroAndBoundedAtFilter
public import TauCeti.Order.Northcott.Comparison

/-!
# Height classes: real functions modulo bounded functions

A height attached to a line bundle is only well defined up to a bounded function: different
projective embeddings, metrics or choices of generating sections change it by `O(1)`. This file
introduces the real vector space in which such heights live,

  `HeightClass X = (X → ℝ) ⧸ {uniformly bounded functions}`,

for an arbitrary type `X`, together with the operations Weil's height machine needs.

`HeightClass X` is the native quotient by Mathlib's `Filter.boundedFilterSubmodule ℝ ⊤`, and its
projection `HeightClass.mk` is the native `Submodule.Quotient.mk`. So the native quotient API
applies directly: `Submodule.Quotient.mk_add` and its relatives give linearity of `mk`,
`Submodule.Quotient.mk_surjective` gives surjectivity, `Submodule.liftQ` descends exactly the
linear maps that kill bounded functions, and `Submodule.quot_hom_ext` tests linear maps on
representatives.

The class has neither point evaluation nor an induced multiplication: `[1] = [0]`, but on `ℕ`
the classes of `n * 1` and `n * 0` differ.

## Main definitions

* `TauCeti.HeightClass X`: real functions on `X` modulo uniformly bounded ones.
* `TauCeti.HeightClass.mk h`: the class `[h]` of `h : X → ℝ`.
* `TauCeti.HeightClass.pullback f`: the linear map `[h] ↦ [h ∘ f]` along `f : X → Y`.

## Main results

* `TauCeti.HeightClass.mk_eq_mk_iff`: `[h] = [g]` exactly when `h - g` is uniformly bounded.
* `TauCeti.HeightClass.pullback_comp`: pullback reverses composition.
* `TauCeti.HeightClass.pullback_injective_of_surjective`: surjective maps detect height classes.
* `TauCeti.HeightClass.northcott_congr`: functions with the same class are Northcott together.
* `TauCeti.HeightClass.northcott_of_pullback_eq`: a function whose class is the pullback, along a
  map with finite fibres, of the class of a Northcott function is Northcott.

## References

* A. J. de Jong, *Notes on Heights*, §14 (footnote 1 and Steps 1–7) and §17,
  <https://www.math.columbia.edu/~dejong/courses/heights.pdf>.
-/

public section

open Filter

namespace TauCeti

/-- **Height classes on `X`.** Real-valued functions on `X` modulo the uniformly bounded ones:
the native quotient of `X → ℝ` by `Filter.boundedFilterSubmodule ℝ ⊤`. A height attached to a
line bundle is well defined only as an element of such a space. -/
abbrev HeightClass (X : Type*) : Type _ :=
  (X → ℝ) ⧸ (boundedFilterSubmodule ℝ ⊤ : Submodule ℝ (X → ℝ))

namespace HeightClass

variable {X Y Z : Type*}

/-- The height class `[h]` of a real function `h` on `X`. It is the native quotient map
`Submodule.Quotient.mk`, so the native lemmas about it apply. -/
abbrev mk (h : X → ℝ) : HeightClass X :=
  Submodule.Quotient.mk h

/-- A function has zero class exactly when it is uniformly bounded. -/
theorem mk_eq_zero_iff {h : X → ℝ} : mk h = 0 ↔ ∃ C, ∀ x, |h x| ≤ C := by
  simp

/-- **The bounded-error criterion.** Two functions have the same class exactly when their
difference is uniformly bounded. -/
theorem mk_eq_mk_iff {h g : X → ℝ} : mk h = mk g ↔ ∃ C, ∀ x, |h x - g x| ≤ C := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_iff]
  simp

/-- Two functions have the same class exactly when the range of their difference is a bounded
set of reals. -/
theorem mk_eq_mk_iff_isBounded {h g : X → ℝ} :
    mk h = mk g ↔ Bornology.IsBounded (Set.range (h - g)) := by
  simp [mk_eq_mk_iff, isBounded_iff_forall_norm_le]

/-- Constant functions have zero class. -/
@[simp]
theorem mk_const (c : ℝ) : mk (fun _ : X ↦ c) = 0 :=
  mk_eq_zero_iff.2 ⟨|c|, fun _ ↦ le_rfl⟩

/-- On a finite type every function is bounded, so it has zero class. -/
theorem mk_eq_zero_of_finite [Finite X] (h : X → ℝ) : mk h = 0 := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun x ↦ |h x|).bddAbove
  exact mk_eq_zero_iff.2 ⟨C, fun x ↦ hC ⟨x, rfl⟩⟩

/-- On a finite type the space of height classes is zero. -/
instance [Finite X] : Subsingleton (HeightClass X) where
  allEq a b := by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    exact (mk_eq_zero_of_finite _).trans (mk_eq_zero_of_finite _).symm

/-- **Pullback of height classes** along `f : X → Y`: the linear map `[h] ↦ [h ∘ f]`. It is
well defined because a bound for `h` on all of `Y` bounds `h ∘ f` on all of `X`. -/
noncomputable def pullback (f : X → Y) : HeightClass Y →ₗ[ℝ] HeightClass X :=
  Submodule.mapQ _ _ (LinearMap.funLeft ℝ ℝ f) fun h hh ↦ by
    obtain ⟨C, hC⟩ := boundedAtFilter_top_iff.1 hh
    exact boundedAtFilter_top_iff.2 ⟨C, fun x ↦ hC (f x)⟩

@[simp]
theorem pullback_mk (f : X → Y) (h : Y → ℝ) : pullback f (mk h) = mk (h ∘ f) :=
  (rfl)

@[simp]
theorem pullback_id : pullback (id : X → X) = LinearMap.id :=
  Submodule.quot_hom_ext _ _ _ fun _ ↦ (rfl)

/-- Pullback reverses composition: pulling back along `g ∘ f` is pulling back along `g`, then
along `f`. -/
theorem pullback_comp (g : Y → Z) (f : X → Y) : pullback (g ∘ f) = pullback f ∘ₗ pullback g :=
  Submodule.quot_hom_ext _ _ _ fun _ ↦ (rfl)

/-- Pullback along a constant map is zero: it sends every function to a constant. -/
@[simp]
theorem pullback_const (y : Y) : pullback (fun _ : X ↦ y) = 0 :=
  Submodule.quot_hom_ext _ _ _ fun h ↦ by simp [Function.comp_def]

/-- **Surjective maps detect height classes.** If `f` is surjective, then `[h ∘ f] = [g ∘ f]`
forces `[h] = [g]`: a bound on all of `X` is a bound at every point of `Y = f(X)`.
Surjectivity cannot be dropped: the inclusion of `{0}` into `ℕ` kills the nonzero class `[n]`. -/
theorem pullback_injective_of_surjective {f : X → Y} (hf : f.Surjective) :
    Function.Injective (pullback f) := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with | H h => ?_
  induction b using Submodule.Quotient.induction_on with | H g => ?_
  obtain ⟨C, hC⟩ := mk_eq_mk_iff.1 (by simpa using hab)
  refine mk_eq_mk_iff.2 ⟨C, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  exact hC x

/-- **Northcott depends only on the height class.** Two real functions with the same class are
Northcott together. -/
theorem northcott_congr {h g : X → ℝ} (hhg : mk h = mk g) : Northcott h ↔ Northcott g := by
  obtain ⟨C, hC⟩ := mk_eq_mk_iff.1 hhg
  exact northcott_iff_of_abs_sub_le C hC

/-- **Northcott for a boundedly equal pullback.** If `f : X → Y` has finite fibres, `h` is
Northcott on `Y` and `[g] = f^*[h]`, then `g` is Northcott on `X`. Finite fibres cannot be
dropped: `[n]` pulled back along the first projection `ℕ × ℕ → ℕ` has an infinite zero
sublevel set. -/
theorem northcott_of_pullback_eq {f : X → Y} [TendstoCofinite f] {h : Y → ℝ} [Northcott h]
    {g : X → ℝ} (hg : mk g = pullback f (mk h)) : Northcott g := by
  rw [pullback_mk] at hg
  exact (northcott_congr hg).2 (Northcott.comp_of_finite_fibers f h)

end HeightClass

end TauCeti

end
