/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Finite trace radicals of Hecke traces

Restrict a tracial functional on the infinite Hecke algebra to the independently presented
finite algebra through `TypeAHeckeAlgebra.toInfinite`. Its multiplication pairing has a two-sided
radical `finiteRadical`. Membership can be checked against the standard basis `T_w`
(`TypeAHeckeAlgebra.basisTw`). The quotient functional `finiteQuotientTrace` is tracial and
algebraically nondegenerate, and is normalized for a Markov trace; this makes no positivity
assertion.

Under a tower map, the preimage of the later radical is contained in the earlier radical.
The opposite inclusion, needed to induce forward maps of these quotients, is not asserted
here: trace compatibility alone would not imply it. At the two scalar-character parameters,
the finite radicals are exactly the kernels of the corresponding characters.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5.
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- The two-sided trace radical on the finite `n`-strand presentation. -/
def finiteRadical (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    Ideal (TypeAHeckeAlgebra R q n) :=
  (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n))

/-- Identify the finite radical with the general trace radical. -/
theorem finiteRadical_def (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    finiteRadical hτ n = (τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical
      (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) := (rfl)

/-- An element belongs to the finite radical exactly when it pairs to zero with all elements
of that finite presentation, not with all elements of the infinite algebra. -/
@[simp]
theorem mem_finiteRadical (hτ : ∀ x y, τ (x * y) = τ (y * x)) {n : ℕ}
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ finiteRadical hτ n ↔ ∀ y, τ (toInfinite R q n (x * y)) = 0 := by
  simp only [finiteRadical_def, LinearMap.mem_traceRadical, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]

instance (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    (finiteRadical hτ n).IsTwoSided :=
  inferInstanceAs ((τ ∘ₗ (toInfinite R q n).toLinearMap).traceRadical _).IsTwoSided

/-- It suffices to test the finite trace pairing on the standard basis `T_w`. -/
theorem mem_finiteRadical_iff_Tw (hτ : ∀ x y, τ (x * y) = τ (y * x)) {n : ℕ}
    {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
    {x : TypeAHeckeAlgebra R q n} :
    x ∈ finiteRadical hτ n ↔ ∀ w, τ (toInfinite R q n (x * Tw q cs w)) = 0 := by
  simpa only [finiteRadical_def, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coe_basisTw] using
    (τ ∘ₗ (toInfinite R q n).toLinearMap).mem_traceRadical_iff_basis
      (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) (basisTw q cs) (x := x)

/-- Pulling back a later finite radical along a tower map lands in the earlier radical. -/
theorem comap_finiteRadical_strandIncl_le (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    Ideal.comap (strandIncl R q n) (finiteRadical hτ (n + 1)) ≤ finiteRadical hτ n := by
  rw [finiteRadical_def, finiteRadical_def]
  exact LinearMap.comap_traceRadical_le _ _ (strandIncl R q n)
    (LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      toInfinite_strandIncl])

/-- The tracial functional induced on the finite trace-radical quotient. -/
def finiteQuotientTrace (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n →ₗ[R] R :=
  (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n))

/-- The finite quotient trace agrees with the original trace on representatives. -/
@[simp]
theorem finiteQuotientTrace_mk (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) :
    finiteQuotientTrace hτ n (Ideal.Quotient.mk (finiteRadical hτ n) x) =
      τ (toInfinite R q n x) := by
  calc
    _ = (τ ∘ₗ (toInfinite R q n).toLinearMap) x :=
      (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_mk
        (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x
    _ = _ := by rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]

/-- The finite quotient preserves the value at the identity. -/
@[simp]
theorem finiteQuotientTrace_one (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ) :
    finiteQuotientTrace hτ n 1 = τ 1 := by
  simpa only [map_one] using finiteQuotientTrace_mk hτ n 1

/-- The finite quotient of a Markov trace is normalized. -/
theorem IsMarkovTrace.finiteQuotientTrace_one (hτ : IsMarkovTrace z τ) (n : ℕ) :
    finiteQuotientTrace hτ.map_mul_comm n 1 = 1 := by
  rw [InfiniteTypeAHeckeAlgebra.finiteQuotientTrace_one, hτ.map_one]

/-- The finite quotient functional is tracial. -/
theorem finiteQuotientTrace_mul_comm (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x y : TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n) :
    finiteQuotientTrace hτ n (x * y) = finiteQuotientTrace hτ n (y * x) := by
  exact (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_mul_comm
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x y

/-- The finite quotient multiplication pairing is algebraically nondegenerate. -/
theorem finiteQuotientTrace_nondegenerate (hτ : ∀ x y, τ (x * y) = τ (y * x)) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n ⧸ finiteRadical hτ n)
    (hx : ∀ y, finiteQuotientTrace hτ n (x * y) = 0) : x = 0 := by
  exact (τ ∘ₗ (toInfinite R q n).toLinearMap).quotientTrace_nondegenerate
    (τ.comp_algHom_mul_comm hτ (toInfinite R q n)) x hx

/-- At the index-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_indexCharacter (n : ℕ) :
    finiteRadical (isMarkovTrace_indexCharacter (R := R) (q := q)).map_mul_comm n =
      RingHom.ker ((indexCharacter R q).comp (toInfinite R q n)) := by
  rw [finiteRadical_def]
  exact AlgHom.traceRadical_eq_ker ((indexCharacter R q).comp (toInfinite R q n))

/-- At the sign-character parameter, the finite radical is the kernel of that character
pulled back to the finite presentation. -/
theorem finiteRadical_signCharacter (n : ℕ) :
    finiteRadical (isMarkovTrace_signCharacter (R := R) (q := q)).map_mul_comm n =
      RingHom.ker ((signCharacter R q).comp (toInfinite R q n)) := by
  rw [finiteRadical_def]
  exact AlgHom.traceRadical_eq_ker ((signCharacter R q).comp (toInfinite R q n))

end TauCeti.InfiniteTypeAHeckeAlgebra
