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

For a subalgebra `C` of `A`, `Subalgebra.traceExpectation C τ : A →ₗ[K] A` is the same
construction along the inclusion of `C`, followed by that inclusion. When `C` is finite-dimensional
and the trace pairing of `τ` is nondegenerate on `C`, it is the idempotent with image `C` whose
kernel is the orthogonal complement of `C` for the trace pairing. For a tracial `τ` it is
self-adjoint for that pairing, and expectations onto nested subalgebras satisfy the tower property.
These are the expectations compared in commuting squares.

## Main definitions

* `LinearMap.traceExpectation`: the trace-preserving conditional expectation `A → B`.
* `Subalgebra.traceExpectation`: the trace-preserving conditional expectation onto a subalgebra,
  as an endomorphism of the ambient algebra.

## Main results

* `LinearMap.apply_traceExpectation_mul`: the defining identity `σ (E a * y) = τ (a * f y)`.
* `LinearMap.traceExpectation_eq_iff`: the defining identity characterizes `E a`.
* `LinearMap.traceExpectation_mul_algHom`, `LinearMap.traceExpectation_algHom_mul`: the bimodule
  identities.
* `LinearMap.apply_traceExpectation`, `LinearMap.traceExpectation_algHom`: trace preservation and
  the retraction property.
* `LinearMap.eq_traceExpectation`: uniqueness among right `B`-linear trace-preserving maps.
* `Subalgebra.traceExpectation_eq_iff`: the expectation onto `C` is characterized by pairing
  against `C`.
* `Subalgebra.apply_mul_traceExpectation`: self-adjointness for a tracial functional.
* `Subalgebra.traceExpectation_traceExpectation_of_le`: the tower property.
* `Subalgebra.traceExpectation_map`: transport along trace-preserving algebra isomorphisms.

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

/-! ### Expectations onto subalgebras -/

namespace Subalgebra

variable {K A A' : Type*} [Field K] [Ring A] [Algebra K A] [Ring A'] [Algebra K A']

open scoped Classical in
/-- The trace-preserving conditional expectation of `A` onto a subalgebra `C`, as an endomorphism
of `A`. When `C` is finite-dimensional and the trace pairing `(x, y) ↦ τ (x * y)` is nondegenerate
on `C`, the value `C.traceExpectation τ a` is the unique `c ∈ C` with `τ (c * y) = τ (a * y)` for
every `y ∈ C` (`Subalgebra.traceExpectation_eq_iff`). It is then `LinearMap.traceExpectation`
along the inclusion of `C`, followed by that inclusion. Otherwise it is `0`. -/
noncomputable def traceExpectation (C : Subalgebra K A) (τ : A →ₗ[K] K) : A →ₗ[K] A :=
  if h : FiniteDimensional K C ∧ ∀ x ∈ C, (∀ y ∈ C, τ (x * y) = 0) → x = 0 then
    haveI := h.1
    C.val.toLinearMap ∘ₗ (τ ∘ₗ C.val.toLinearMap).traceExpectation
      (fun x hx ↦ Subtype.ext <| h.2 x x.property fun y hy ↦ hx ⟨y, hy⟩) τ C.val
  else 0

variable {C D : Subalgebra K A} {τ : A →ₗ[K] K}

/-- The expectation onto `C` takes values in `C`. -/
@[simp]
theorem traceExpectation_mem (a : A) : C.traceExpectation τ a ∈ C := by
  unfold traceExpectation
  split_ifs <;> simp

/-- Outside the finite-dimensional, nondegenerate case the expectation onto `C` is `0`. -/
theorem traceExpectation_of_not
    (h : ¬ (FiniteDimensional K C ∧ ∀ x ∈ C, (∀ y ∈ C, τ (x * y) = 0) → x = 0)) :
    C.traceExpectation τ = 0 := by
  rw [traceExpectation, dite_eq_right h]

section Nondegenerate

variable [FiniteDimensional K C] (hC : ∀ x ∈ C, (∀ y ∈ C, τ (x * y) = 0) → x = 0)
include hC

/-- On a finite-dimensional subalgebra with nondegenerate trace pairing, the expectation is
`LinearMap.traceExpectation` along the inclusion. -/
theorem traceExpectation_apply (a : A) :
    C.traceExpectation τ a = (τ ∘ₗ C.val.toLinearMap).traceExpectation
      (fun x hx ↦ Subtype.ext <| hC x x.property fun y hy ↦ hx ⟨y, hy⟩) τ C.val a := by
  rw [traceExpectation, dite_eq_left ⟨inferInstance, hC⟩, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val]

/-- The defining identity of the expectation onto `C`: pairing against elements of `C` does not
see the difference between `a` and its expectation. -/
theorem apply_traceExpectation_mul (a : A) {y : A} (hy : y ∈ C) :
    τ (C.traceExpectation τ a * y) = τ (a * y) := by
  rw [traceExpectation_apply hC]
  simpa using LinearMap.apply_traceExpectation_mul (τ ∘ₗ C.val.toLinearMap) _ τ C.val a ⟨y, hy⟩

/-- The defining identity characterizes the expectation onto `C`. -/
theorem traceExpectation_eq_iff {a c : A} (hc : c ∈ C) :
    C.traceExpectation τ a = c ↔ ∀ y ∈ C, τ (c * y) = τ (a * y) := by
  refine ⟨fun h y hy ↦ h ▸ apply_traceExpectation_mul hC a hy, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  refine hC _ (sub_mem (traceExpectation_mem a) hc) fun y hy ↦ ?_
  rw [sub_mul, map_sub, apply_traceExpectation_mul hC a hy, h y hy, sub_self]

/-- The expectation onto `C` vanishes exactly on the elements orthogonal to `C` for the trace
pairing. -/
theorem traceExpectation_eq_zero_iff {a : A} :
    C.traceExpectation τ a = 0 ↔ ∀ y ∈ C, τ (a * y) = 0 := by
  simp [traceExpectation_eq_iff hC (zero_mem C), eq_comm]

/-- The expectation onto `C` fixes `C`. -/
theorem traceExpectation_of_mem {a : A} (ha : a ∈ C) : C.traceExpectation τ a = a :=
  (traceExpectation_eq_iff hC ha).mpr fun _ _ ↦ rfl

/-- The expectation onto `C` is idempotent. -/
theorem traceExpectation_traceExpectation (a : A) :
    C.traceExpectation τ (C.traceExpectation τ a) = C.traceExpectation τ a :=
  traceExpectation_of_mem hC (traceExpectation_mem a)

/-- The expectation onto `C` is unital. -/
theorem traceExpectation_one : C.traceExpectation τ 1 = 1 :=
  traceExpectation_of_mem hC C.one_mem

/-- The expectation onto `C` preserves `τ`. -/
theorem apply_traceExpectation (a : A) : τ (C.traceExpectation τ a) = τ a := by
  simpa using apply_traceExpectation_mul hC a C.one_mem

/-- The expectation onto `C` is right `C`-linear. -/
theorem traceExpectation_mul_of_mem_right (a : A) {y : A} (hy : y ∈ C) :
    C.traceExpectation τ (a * y) = C.traceExpectation τ a * y :=
  (traceExpectation_eq_iff hC (mul_mem (traceExpectation_mem a) hy)).mpr fun z hz ↦ by
    rw [mul_assoc, apply_traceExpectation_mul hC a (mul_mem hy hz), mul_assoc]

/-- For a tracial functional, the expectation onto `C` is left `C`-linear. -/
theorem traceExpectation_mul_of_mem_left (hτ : ∀ a b, τ (a * b) = τ (b * a)) {x : A}
    (hx : x ∈ C) (a : A) : C.traceExpectation τ (x * a) = x * C.traceExpectation τ a :=
  (traceExpectation_eq_iff hC (mul_mem hx (traceExpectation_mem a))).mpr fun z hz ↦
    calc τ (x * C.traceExpectation τ a * z) = τ (C.traceExpectation τ a * (z * x)) := by
          rw [mul_assoc, hτ, mul_assoc]
      _ = τ (a * (z * x)) := apply_traceExpectation_mul hC a (mul_mem hz hx)
      _ = τ (x * a * z) := by rw [hτ, mul_assoc, hτ]

/-- For a tracial functional, the expectation onto `C` is self-adjoint for the trace pairing. -/
theorem apply_mul_traceExpectation (hτ : ∀ a b, τ (a * b) = τ (b * a)) (a b : A) :
    τ (a * C.traceExpectation τ b) = τ (C.traceExpectation τ a * b) := by
  rw [← apply_traceExpectation_mul hC a (traceExpectation_mem b), hτ,
    apply_traceExpectation_mul hC b (traceExpectation_mem a), hτ]

omit [FiniteDimensional K C] in
/-- The tower property: expecting onto a larger subalgebra `D` first does not change the
expectation onto `C`. -/
theorem traceExpectation_traceExpectation_of_le [FiniteDimensional K C] [FiniteDimensional K D]
    (hD : ∀ x ∈ D, (∀ y ∈ D, τ (x * y) = 0) → x = 0) (hCD : C ≤ D) (a : A) :
    C.traceExpectation τ (D.traceExpectation τ a) = C.traceExpectation τ a :=
  (traceExpectation_eq_iff hC (traceExpectation_mem a)).mpr fun y hy ↦ by
    rw [apply_traceExpectation_mul hC a hy, apply_traceExpectation_mul hD a (hCD hy)]

omit [FiniteDimensional K C] in
/-- The tower property as an identity of linear maps. -/
theorem traceExpectation_comp_traceExpectation_of_le [FiniteDimensional K C]
    [FiniteDimensional K D] (hD : ∀ x ∈ D, (∀ y ∈ D, τ (x * y) = 0) → x = 0) (hCD : C ≤ D) :
    C.traceExpectation τ ∘ₗ D.traceExpectation τ = C.traceExpectation τ :=
  LinearMap.ext <| traceExpectation_traceExpectation_of_le hC hD hCD

end Nondegenerate

/-- A trace-preserving algebra isomorphism `e` carries the expectation onto `C` to the
expectation onto the image of `C`. -/
theorem traceExpectation_map (e : A ≃ₐ[K] A') {τ' : A' →ₗ[K] K} (he : ∀ a, τ' (e a) = τ a)
    (a : A) :
    (C.map (e : A →ₐ[K] A')).traceExpectation τ' (e a) = e (C.traceExpectation τ a) := by
  have hfd : FiniteDimensional K (C.map (e : A →ₐ[K] A')) ↔ FiniteDimensional K C :=
    ⟨fun _ ↦ (e.subalgebraMap C).toLinearEquiv.symm.finiteDimensional,
      fun _ ↦ (e.subalgebraMap C).toLinearEquiv.finiteDimensional⟩
  have hnd : (∀ x ∈ C.map (e : A →ₐ[K] A'), (∀ y ∈ C.map (e : A →ₐ[K] A'), τ' (x * y) = 0) →
      x = 0) ↔ ∀ x ∈ C, (∀ y ∈ C, τ (x * y) = 0) → x = 0 := by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      AlgEquiv.coe_toAlgHom, ← map_mul, he, EmbeddingLike.map_eq_zero_iff]
  by_cases hC : FiniteDimensional K C ∧ ∀ x ∈ C, (∀ y ∈ C, τ (x * y) = 0) → x = 0
  · obtain ⟨_, hC⟩ := hC
    have : FiniteDimensional K (C.map (e : A →ₐ[K] A')) := hfd.mpr inferInstance
    refine (traceExpectation_eq_iff (hnd.mpr hC) ⟨_, traceExpectation_mem a, rfl⟩).mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp [← map_mul, he, apply_traceExpectation_mul hC a hy]
  · rw [traceExpectation_of_not hC, traceExpectation_of_not (by rwa [hfd, hnd]),
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end Subalgebra
