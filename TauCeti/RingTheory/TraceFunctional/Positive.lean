/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Star
public import TauCeti.RingTheory.TraceFunctional.Star

/-!
# Positive trace quotients

For a positive tracial functional on a complex star algebra, the trace radical is exactly
the null space of its positive semidefinite form. The quotient by this radical is therefore
a star algebra with a faithful positive trace, without any norm or finite-dimensionality
assumption. A trace-preserving star representation into an algebra with a faithful positive
functional has kernel exactly this radical; surjectivity is not required. These are the
algebraic steps preceding the C*-norm on positive Jones quotients.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.4–4.5,
  for the positive trace quotients of Temperley–Lieb algebras.
-/

public section

open scoped ComplexOrder

namespace TauCeti.StarPositiveFunctional

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  (φ : StarPositiveFunctional A) (hφ : ∀ x y, φ (x * y) = φ (y * x))

/-- For a positive trace, radical membership can be tested on a single square. -/
theorem mem_traceRadical_iff_apply_star_mul_self_eq_zero (a : A) :
    a ∈ φ.toLinearMap.traceRadical hφ ↔ φ (star a * a) = 0 := by
  rw [φ.toLinearMap.mem_traceRadical_iff_left hφ,
    φ.apply_star_mul_self_eq_zero_iff]
  exact ⟨fun h b ↦ h (star b), fun h b ↦ by simpa using h (star b)⟩

/-- The GNS null space of a positive trace is the coefficient submodule of its trace radical. -/
theorem nullSubmodule_eq_traceRadical :
    φ.nullSubmodule = (φ.toLinearMap.traceRadical hφ).restrictScalars ℂ := by
  ext a
  simp only [φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    Submodule.restrictScalars_mem, φ.mem_traceRadical_iff_apply_star_mul_self_eq_zero hφ]

/-- A positive trace has a star-stable radical. Install this instance explicitly when the
underlying linear map does not determine the bundled positive functional during inference. -/
instance instIsStarTraceRadical : (φ.toLinearMap.traceRadical hφ).IsStar where
  star_mem ha := (φ.toLinearMap.star_mem_traceRadical_iff hφ φ.map_star).mpr ha

/-- The positive functional induced on the trace-radical quotient. It is tracial and faithful. -/
def quotientTrace : StarPositiveFunctional (A ⧸ φ.toLinearMap.traceRadical hφ) where
  toLinearMap := φ.toLinearMap.quotientTrace hφ
  square_nonneg x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [Ideal.Quotient.star_mk, ← map_mul, LinearMap.quotientTrace_mk] using
      φ.square_nonneg a

/-- Forgetting positivity recovers the algebraic quotient trace. -/
@[simp]
theorem toLinearMap_quotientTrace :
    (φ.quotientTrace hφ).toLinearMap = φ.toLinearMap.quotientTrace hφ := (rfl)

/-- The positive quotient trace has the prescribed value on each representative. -/
@[simp]
theorem quotientTrace_mk (a : A) :
    φ.quotientTrace hφ (Ideal.Quotient.mk (φ.toLinearMap.traceRadical hφ) a) = φ a :=
  φ.toLinearMap.quotientTrace_mk hφ a

/-- The induced positive trace retains the value at the identity. -/
@[simp]
theorem quotientTrace_one : φ.quotientTrace hφ 1 = φ 1 :=
  φ.toLinearMap.quotientTrace_one hφ

/-- The induced positive functional is tracial. -/
theorem quotientTrace_mul_comm (x y : A ⧸ φ.toLinearMap.traceRadical hφ) :
    φ.quotientTrace hφ (x * y) = φ.quotientTrace hφ (y * x) :=
  φ.toLinearMap.quotientTrace_mul_comm hφ x y

/-- A square has zero quotient trace exactly when its argument vanishes. -/
@[simp]
theorem quotientTrace_star_mul_self_eq_zero_iff (x : A ⧸ φ.toLinearMap.traceRadical hφ) :
    φ.quotientTrace hφ (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.star_mk, ← map_mul, φ.quotientTrace_mk,
    Ideal.Quotient.eq_zero_iff_mem, φ.mem_traceRadical_iff_apply_star_mul_self_eq_zero]

/-- The positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_quotientTrace : (φ.quotientTrace hφ).nullSubmodule = ⊥ := by
  ext x
  simp only [mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    φ.quotientTrace_star_mul_self_eq_zero_iff hφ, Submodule.mem_bot]

end TauCeti.StarPositiveFunctional

namespace LinearMap

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- A trace pulled back from a positive functional with trivial GNS null space has radical
equal to the representation kernel. Neither surjectivity nor traciality on the target is
required. -/
theorem traceRadical_eq_ker_of_nullSubmodule_eq_bot (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (ψ : TauCeti.StarPositiveFunctional B) (hψ : ψ.nullSubmodule = ⊥)
    (f : A →⋆ₐ[ℂ] B) (hf : ∀ a, ψ (f a) = τ a) :
    τ.traceRadical hτ = RingHom.ker f := by
  ext a
  simp only [mem_traceRadical, RingHom.mem_ker]
  constructor
  · intro ha
    apply (ψ.apply_star_mul_self_eq_zero_iff_of_nullSubmodule_eq_bot hψ (f a)).mp
    rw [← map_star, ← map_mul, hf, hτ]
    exact ha (star a)
  · intro ha b
    rw [← hf, map_mul, ha, zero_mul, map_zero]

end LinearMap
