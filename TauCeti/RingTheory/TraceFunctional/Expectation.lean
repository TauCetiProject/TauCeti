/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Trace-preserving conditional expectations

Let `f : B →ₐ[K] A` be an algebra map over a field, with `B` finite-dimensional, and let
`σ : B →ₗ[K] K` and `τ : A →ₗ[K] K` be linear functionals. If the multiplication pairing
`(x, y) ↦ σ (x * y)` of `σ` is nondegenerate, then for each `a : A` there is a unique `b : B` with
`σ (b * y) = τ (a * f y)` for every `y : B`. This defines a linear map
`LinearMap.traceExpectation σ hσ τ f : A →ₗ[K] B`, the adjoint of `f` for the two trace pairings.

This is the algebraic form of the trace-preserving conditional expectation onto a subalgebra:

* it is right `B`-linear, `E (a * f y) = E a * y`, with no further assumption;
* it carries `τ` to `σ`, `σ (E a) = τ a`;
* when `f` carries `τ` to `σ`, it is unital and retracts `f`, `E (f x) = x`;
* when both functionals are tracial, it is also left `B`-linear, `E (f x * a) = x * E a`;
* when both functionals are tracial and, together with `f`, preserve stars, so does `E`;
* it is the only right `B`-linear map carrying `τ` to `σ`.

No positivity is assumed. The construction applies, for instance, to the quotients of the
Temperley–Lieb tower by the radicals of its Markov trace, whose trace pairings are nondegenerate.

## Main definitions

* `LinearMap.traceExpectation`: the trace-preserving conditional expectation `A → B`.

## Main results

* `LinearMap.apply_traceExpectation_mul`: the defining identity `σ (E a * y) = τ (a * f y)`.
* `LinearMap.traceExpectation_eq_iff`: the defining identity characterizes `E a`.
* `LinearMap.traceExpectation_mul_algHom`, `LinearMap.traceExpectation_algHom_mul`: the bimodule
  identities.
* `LinearMap.apply_traceExpectation`, `LinearMap.traceExpectation_algHom`: trace preservation and
  the retraction property.
* `LinearMap.eq_traceExpectation`: uniqueness among right `B`-linear trace-preserving maps.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25, §3.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989, §2.6.
-/

public section

namespace LinearMap

variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [FiniteDimensional K B]
  (σ : B →ₗ[K] K) (hσ : ∀ x, (∀ y, σ (x * y) = 0) → x = 0) (τ : A →ₗ[K] K) (f : B →ₐ[K] A)

/-- The trace-preserving conditional expectation `A → B` along `f`: the element `E a` is
determined by `σ (E a * y) = τ (a * f y)` for every `y : B`. -/
noncomputable def traceExpectation : A →ₗ[K] B :=
  -- The nondegenerate pairing `x ↦ (y ↦ σ (x * y))` identifies `B` with its dual.
  (BilinForm.toDual ((LinearMap.mul K B).compr₂ σ) (.ofSeparatingLeft hσ)).symm.toLinearMap ∘ₗ
    ((LinearMap.mul K A).compr₂ τ).compl₂ f.toLinearMap

/-- The defining identity of the trace-preserving conditional expectation. -/
@[simp]
theorem apply_traceExpectation_mul (a : A) (y : B) :
    σ (σ.traceExpectation hσ τ f a * y) = τ (a * f y) :=
  BilinForm.apply_toDual_symm_apply (B := (LinearMap.mul K B).compr₂ σ)
    (hB := .ofSeparatingLeft hσ) (((LinearMap.mul K A).compr₂ τ).compl₂ f.toLinearMap a) y

/-- The defining identity characterizes the value of the conditional expectation. -/
theorem traceExpectation_eq_iff {a : A} {b : B} :
    σ.traceExpectation hσ τ f a = b ↔ ∀ y, σ (b * y) = τ (a * f y) := by
  refine ⟨fun h y ↦ h ▸ apply_traceExpectation_mul σ hσ τ f a y, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  refine hσ _ fun y ↦ ?_
  rw [sub_mul, map_sub, apply_traceExpectation_mul, h, sub_self]

/-- The conditional expectation is right `B`-linear. -/
@[simp]
theorem traceExpectation_mul_algHom (a : A) (y : B) :
    σ.traceExpectation hσ τ f (a * f y) = σ.traceExpectation hσ τ f a * y := by
  refine (traceExpectation_eq_iff σ hσ τ f).mpr fun z ↦ ?_
  rw [mul_assoc, apply_traceExpectation_mul, map_mul f, mul_assoc]

/-- The conditional expectation carries `τ` to `σ`. -/
@[simp]
theorem apply_traceExpectation (a : A) : σ (σ.traceExpectation hσ τ f a) = τ a := by
  simpa using apply_traceExpectation_mul σ hσ τ f a 1

/-- A right `B`-linear map carrying `τ` to `σ` is the conditional expectation. -/
theorem eq_traceExpectation (g : A →ₗ[K] B) (hg : ∀ a y, g (a * f y) = g a * y)
    (hgσ : ∀ a, σ (g a) = τ a) : g = σ.traceExpectation hσ τ f := by
  ext a
  exact ((traceExpectation_eq_iff σ hσ τ f).mpr fun y ↦ by rw [← hg, hgσ]).symm

variable {σ τ f}

/-- If `f` carries `τ` to `σ`, the conditional expectation is unital. -/
@[simp]
theorem traceExpectation_one (hf : τ ∘ₗ f.toLinearMap = σ) :
    σ.traceExpectation hσ τ f 1 = 1 :=
  (traceExpectation_eq_iff σ hσ τ f).mpr fun y ↦ by
    simpa using (LinearMap.congr_fun hf y).symm

/-- If `f` carries `τ` to `σ`, the conditional expectation retracts `f`. -/
@[simp]
theorem traceExpectation_algHom (hf : τ ∘ₗ f.toLinearMap = σ) (x : B) :
    σ.traceExpectation hσ τ f (f x) = x := by
  simpa [traceExpectation_one hσ hf] using traceExpectation_mul_algHom σ hσ τ f 1 x

/-- For tracial functionals the conditional expectation is also left `B`-linear. -/
theorem traceExpectation_algHom_mul (hσc : ∀ x y, σ (x * y) = σ (y * x))
    (hτc : ∀ a b, τ (a * b) = τ (b * a)) (x : B) (a : A) :
    σ.traceExpectation hσ τ f (f x * a) = x * σ.traceExpectation hσ τ f a := by
  refine (traceExpectation_eq_iff σ hσ τ f).mpr fun z ↦ ?_
  rw [mul_assoc, hσc, mul_assoc, apply_traceExpectation_mul, map_mul f, hτc (f x * a), hτc a,
    mul_assoc]

/-- For tracial functionals, a product `f x * a * f y` has conditional expectation
`x * E a * y`. -/
theorem traceExpectation_algHom_mul_mul_algHom (hσc : ∀ x y, σ (x * y) = σ (y * x))
    (hτc : ∀ a b, τ (a * b) = τ (b * a)) (x : B) (a : A) (y : B) :
    σ.traceExpectation hσ τ f (f x * a * f y) = x * σ.traceExpectation hσ τ f a * y := by
  rw [traceExpectation_mul_algHom, traceExpectation_algHom_mul hσ hσc hτc]

/-- For star-preserving tracial functionals and a star-preserving `f`, the conditional expectation
preserves stars. -/
theorem traceExpectation_star [StarRing K] [StarRing A] [StarRing B]
    (hσc : ∀ x y, σ (x * y) = σ (y * x)) (hτc : ∀ a b, τ (a * b) = τ (b * a))
    (hσs : ∀ x, σ (star x) = star (σ x)) (hτs : ∀ a, τ (star a) = star (τ a))
    (hfs : ∀ x, f (star x) = star (f x)) (a : A) :
    σ.traceExpectation hσ τ f (star a) = star (σ.traceExpectation hσ τ f a) := by
  refine (traceExpectation_eq_iff σ hσ τ f).mpr fun y ↦ ?_
  calc σ (star (σ.traceExpectation hσ τ f a) * y)
      = star (σ (σ.traceExpectation hσ τ f a * star y)) := by
        rw [← hσs, star_mul, star_star, hσc]
    _ = star (τ (a * star (f y))) := by rw [apply_traceExpectation_mul, hfs]
    _ = τ (star a * f y) := by rw [← hτs, star_mul, star_star, hτc]

end LinearMap
