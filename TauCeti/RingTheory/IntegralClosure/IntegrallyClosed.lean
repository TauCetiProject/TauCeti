/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integrally closed algebras and subrings

For a field `k` and a nontrivial commutative `k`-algebra `A`, being integrally closed in `A`
means every element of `A` algebraic over `k` is a constant. An algebraically closed field is
integrally closed in every domain algebra.

If a subring `S` of `B` is integrally closed in `B`, then its preimage under a ring homomorphism
`f : A → B` is integrally closed in `A`: an element of `A` integral over the preimage is sent by
`f` to an element integral over `S`, which therefore lies in `S`.

Mathlib's `IsIntegrallyClosed.pow_dvd_pow_iff` says that in an integrally closed domain
`a ^ n ∣ b ^ n` implies `a ∣ b` for `n ≠ 0`. The same holds in a ring `R` integrally closed in an
algebra `A`, with no domain hypothesis, provided `a` becomes invertible in `A`: then `b / a ∈ A` is
a root of `X ^ n - c` with `c ∈ R`, hence comes from `R`. For the ring `R°` of power-bounded
elements of a Tate ring and a pseudouniformiser `a`, this is why Frobenius `R° ⧸ a →+* R° ⧸ a ^ p`
is injective.

## Main results

* `TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic`: the elementwise criterion for a field
  to be integrally closed in a nontrivial commutative algebra.
* `TauCeti.isIntegrallyClosedIn_of_isAlgClosed`: an algebraically closed field is integrally
  closed in every domain algebra.
* `Subring.isIntegrallyClosedIn_comap`: the preimage of an integrally closed subring is integrally
  closed.
* `IsIntegrallyClosedIn.pow_dvd_pow_iff`: if `R` is integrally closed in `A` and `a ∈ R` becomes a
  unit in `A`, then `a ^ n ∣ b ^ n` in `R` with `n ≠ 0` exactly when `a ∣ b` in `R`.
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- A field `k` is integrally closed in a nontrivial commutative `k`-algebra `A` exactly when
every element of `A` algebraic over `k` lies in the image of `k`. -/
theorem isIntegrallyClosedIn_iff_forall_isAlgebraic [Nontrivial A] :
    IsIntegrallyClosedIn k A ↔ ∀ x : A, IsAlgebraic k x → ∃ c : k, algebraMap k A c = x := by
  constructor
  · intro h x hx
    exact (isIntegrallyClosedIn_iff.mp h).2 hx.isIntegral
  · intro h
    exact isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k A).injective, fun hx ↦ h _ hx.isAlgebraic⟩

/-- An algebraically closed field is integrally closed in every domain algebra. -/
theorem isIntegrallyClosedIn_of_isAlgClosed [IsAlgClosed k] [IsDomain A] :
    IsIntegrallyClosedIn k A :=
  isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k A).injective, fun {z} hz ↦
    minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz))⟩

end TauCeti

namespace Subring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The preimage of an integrally closed subring is integrally closed**: if `S` is integrally
closed in `B`, then `S.comap f` is integrally closed in `A` for every ring homomorphism
`f : A →+* B`. -/
instance isIntegrallyClosedIn_comap (f : A →+* B) (S : Subring B) [IsIntegrallyClosedIn S B] :
    IsIntegrallyClosedIn (S.comap f) A :=
  Subring.isIntegrallyClosedIn_iff.mpr fun _ hx ↦ (Subring.isIntegrallyClosedIn_iff (S := S)).mp
    inferInstance (hx.map_of_comp_eq (f.restrict _ S fun _ hy ↦ hy) f rfl)

end Subring

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]

/-- **Roots of divisibility in an integrally closed subring.** If `R` is integrally closed in `A`
and `a ∈ R` is a unit of `A`, then for `n ≠ 0`, `a ^ n ∣ b ^ n` in `R` exactly when `a ∣ b` in
`R`. Compare `IsIntegrallyClosed.pow_dvd_pow_iff`, which instead asks `R` to be an integrally
closed domain. -/
theorem pow_dvd_pow_iff {n : ℕ} (hn : n ≠ 0) {a b : R} (ha : IsUnit (algebraMap R A a)) :
    a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  obtain ⟨u, hu⟩ := ha
  -- `x = b / a` satisfies `x ^ n = c`, so it is integral over `R` and comes from `R`.
  have hx : (algebraMap R A b * ↑u⁻¹) ^ n = algebraMap R A c := by
    rw [mul_pow, ← map_pow, hc, map_mul, map_pow, ← hu]
    simp [mul_right_comm, ← mul_pow]
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_isIntegral_pow (Nat.pos_of_ne_zero hn)
    (hx ▸ isIntegral_algebraMap)
  refine ⟨y, IsIntegralClosure.algebraMap_injective R R A ?_⟩
  rw [map_mul, hy, ← hu, mul_left_comm, Units.mul_inv, mul_one]

end IsIntegrallyClosedIn
