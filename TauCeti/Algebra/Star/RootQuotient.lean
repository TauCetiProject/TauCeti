/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.Group.Hom.TwistedNorm
import TauCeti.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Tactic.Group

/-!
# Root quotients of polynomials at an element of a star algebra

Let `A` be a star algebra over a commutative semiring `R`, `x : A` and `z : R[X]`. An element
`a : A` is a **root quotient** of `z` at `x` if `a * star (aeval x z) = aeval x z`. For a square
matrix `x` over a commutative star ring, `star` is the conjugate transpose, and this is the
relation `a * z(x)ᴴ = z(x)` of base change for definite unitary groups.

## Main results

* `Polynomial.IsRootQuotient`: the relation `a * star (aeval x z) = aeval x z`.
* `Polynomial.commute_star_aeval_aeval`: if `x` is normal, `star (aeval x z)` commutes with
  `aeval x w`.
* `Polynomial.IsRootQuotient.mul`: at a normal `x`, root quotients of `z` and `w` multiply to a
  root quotient of `z * w`.
* `Polynomial.IsRootQuotient.eq_of_isUnit`: if `aeval x z` is a unit, root quotients of `z` at `x`
  are unique.
* `Polynomial.IsRootQuotient.conj` and `Polynomial.IsRootQuotient.map`: root quotients are
  carried along conjugation by a unitary and along ring homomorphisms commuting with `star`.
* `Polynomial.existsUnique_isRootQuotient`: if `x` is normal and `aeval x z` is a unit, `z` has
  exactly one unitary root quotient at `x`.
* `Polynomial.IsRootQuotient.twistedNorm_eq_mul`: let `τ` be a ring endomorphism of `A` commuting
  with `star` and acting on scalars by `σ`. If `a` is a root quotient of `z` at a unitary `γ`, `γ`
  is a root quotient at `γ` of the twisted norm of `z` under `σ`, `aeval γ z` is a unit and
  `γ * c = c * τ γ` for a unitary `c`, then `N_τ(c) = γ * N_τ(a⁻¹ * c)`.

## Provenance

The statements follow `New.IsRootQuotient`, `New.U.existsUnique_isRootQuotient`,
`New.IsRootQuotient.mul` and `New.IsRootQuotient.twistedNorm_eq_mul` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC), stated there for
unitary matrices over a commutative star ring; here they are stated for a star algebra. The proof
of `twistedNorm_eq_mul` follows the grh-lean proof: by induction on the length, the quotient of the
two twisted norms of `c` and `a⁻¹ * c` is a root quotient of the twisted norm of `z`, and root
quotients at an element with unit value are unique.
-/

public section

open Polynomial

namespace Polynomial

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [StarRing A]

/-- An element `a` is a **root quotient** of the polynomial `z` at `x` if
`a * star (aeval x z) = aeval x z`. -/
def IsRootQuotient (z : R[X]) (x a : A) : Prop :=
  a * star (aeval x z) = aeval x z

/-- At a normal element `x`, the adjoint of `aeval x z` commutes with `aeval x w`. -/
theorem commute_star_aeval_aeval (x : A) [IsStarNormal x] (z w : R[X]) :
    Commute (star (aeval x z)) (aeval x w) := by
  have h : Commute (star x) (aeval x z) := Algebra.commute_of_mem_adjoin_singleton_of_commute
    (aeval_mem_adjoin_singleton R x) (star_comm_self' x)
  have h' : Commute (star (aeval x z)) x := by simpa using h.star_star.symm
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton R x) h'

namespace IsRootQuotient

variable {x a b : A} {z w : R[X]}

/-- At a normal element, root quotients multiply: if `a` is a root quotient of `z` and `b` one of
`w`, then `a * b` is a root quotient of `z * w`. -/
theorem mul [IsStarNormal x] (ha : IsRootQuotient z x a) (hb : IsRootQuotient w x b) :
    IsRootQuotient (z * w) x (a * b) := by
  unfold IsRootQuotient at *
  rw [map_mul, star_mul, ← mul_assoc, mul_assoc a, hb, mul_assoc,
    ← (commute_star_aeval_aeval x z w).eq, ← mul_assoc, ha]

/-- If `aeval x z` is a unit, `z` has at most one root quotient at `x`. -/
theorem eq_of_isUnit (hz : IsUnit (aeval x z)) (ha : IsRootQuotient z x a)
    (hb : IsRootQuotient z x b) : a = b :=
  hz.star.mul_left_inj.mp (ha.trans hb.symm)

end IsRootQuotient

/-- If `x` is normal and `aeval x z` is a unit, then `z` has exactly one unitary root quotient
at `x`. -/
theorem existsUnique_isRootQuotient {x : A} [IsStarNormal x] {z : R[X]}
    (hz : IsUnit (aeval x z)) : ∃! a : unitary A, IsRootQuotient z x (a : A) := by
  obtain ⟨u, hu⟩ := hz
  have hcomm : Commute (star (u : A)) u := hu ▸ commute_star_aeval_aeval x z z
  have hmem : ((u * (star u)⁻¹ : Aˣ) : A) ∈ unitary A := by
    refine Units.mem_unitary_iff_star_eq_inv.mpr ?_
    have h : star (u : A) * ↑u⁻¹ = ↑u⁻¹ * star (u : A) := hcomm.units_inv_right.eq
    simpa [mul_inv_rev] using h.symm
  refine ⟨⟨_, hmem⟩, ?_, fun b hb ↦ Subtype.ext ?_⟩
  · simp only [IsRootQuotient, ← hu]
    simp [mul_assoc, ← star_mul]
  · refine IsRootQuotient.eq_of_isUnit (hu ▸ u.isUnit) hb ?_
    simp only [IsRootQuotient, ← hu]
    simp [mul_assoc, ← star_mul]

/-- If `x * c = c * y` for a unitary `c`, then `aeval x z = c * aeval y z * star c`. -/
theorem aeval_eq_mul_mul_star_of_mul_eq_mul {x y : A} {c : unitary A} (hc : x * c = c * y)
    (z : R[X]) : aeval x z = c * aeval y z * star (c : A) := by
  have hx : x = Unitary.conjStarAlgAut R A c y := by
    simp [← hc, mul_assoc]
  rw [hx, aeval_algHom_apply (Unitary.conjStarAlgAut R A c)]
  rfl

namespace IsRootQuotient

variable {x y a : A} {z : R[X]}

/-- Conjugation by a unitary `c` with `x * c = c * y` carries root quotients of `z` at `y` to root
quotients of `z` at `x`. -/
theorem conj {c : unitary A} (hc : x * c = c * y) (ha : IsRootQuotient z y a) :
    IsRootQuotient z x (c * a * star (c : A)) := by
  unfold IsRootQuotient at *
  rw [aeval_eq_mul_mul_star_of_mul_eq_mul hc]
  simp only [star_mul, star_star, ← mul_assoc]
  rw [mul_assoc (_ * a), Unitary.coe_star_mul_self, mul_one, mul_assoc _ a, ha]

variable {T B : Type*} [CommSemiring T] [Semiring B] [Algebra T B] [StarRing B]

/-- Let `τ : A →+* B` commute with `star` and act on scalars through `φ : R →+* T`. Then `τ`
carries root quotients of `z` at `x` to root quotients of `z.map φ` at `τ x`. -/
theorem map {φ : R →+* T} {τ : A →+* B} (hτ : (algebraMap T B).comp φ = τ.comp (algebraMap R A))
    (hτ_star : ∀ y, τ (star y) = star (τ y)) (ha : IsRootQuotient z x a) :
    IsRootQuotient (z.map φ) (τ x) (τ a) := by
  unfold IsRootQuotient at *
  rw [← map_aeval_eq_aeval_map hτ, ← hτ_star, ← map_mul, ha]

end IsRootQuotient

section TwistedNorm

variable {σ : R →+* R} {τ : A →+* A} (hτ : (algebraMap R A).comp σ = τ.comp (algebraMap R A))
  (hτ_star : ∀ y, τ (star y) = star (τ y))

include hτ in
/-- Let `τ` be a ring endomorphism of `A` commuting with `star` and acting on scalars through
`σ`, and `N_q` the twisted norms of length `q` under `σ` and under `τ`. Let `a`, `γ`, `c` be
unitary, with `a` a root quotient of `z` at `γ`, `aeval γ z` a unit and `γ * c = c * τ γ`. Then
`aeval γ (N_q(z))` is a unit and `N_q(c) * N_q(a⁻¹ * c)⁻¹` is a root quotient of `N_q(z)` at
`γ`. -/
theorem IsRootQuotient.isUnit_and_isRootQuotient_twistedNorm {z : R[X]} {γ a c : unitary A}
    (hc : (γ : A) * c = c * τ γ) (ha : IsRootQuotient z (γ : A) a) (hz : IsUnit (aeval (γ : A) z))
    (q : ℕ) :
    IsUnit (aeval (γ : A) (MonoidHom.twistedNorm (mapRingHom σ : R[X] →* R[X]) q z)) ∧
      IsRootQuotient (MonoidHom.twistedNorm (mapRingHom σ : R[X] →* R[X]) q z) (γ : A)
        ((MonoidHom.twistedNorm (Unitary.map ⟨τ, hτ_star⟩).toMonoidHom q c *
          (MonoidHom.twistedNorm (Unitary.map ⟨τ, hτ_star⟩).toMonoidHom q (a⁻¹ * c))⁻¹ :
            unitary A) : A) := by
  induction q with
  | zero => simp [IsRootQuotient]
  | succ q ih =>
    obtain ⟨ih_unit, ih_root⟩ := ih
    set w := MonoidHom.twistedNorm (mapRingHom σ : R[X] →* R[X]) q z
    have hw : aeval (γ : A) (w.map σ) = c * τ (aeval (γ : A) w) * star (c : A) := by
      rw [aeval_eq_mul_mul_star_of_mul_eq_mul hc, map_aeval_eq_aeval_map hτ]
    have h_succ : MonoidHom.twistedNorm (mapRingHom σ : R[X] →* R[X]) (q + 1) z =
        w.map σ * z := by
      rw [MonoidHom.twistedNorm_succ, mul_comm]
      rfl
    rw [h_succ, map_mul, hw]
    refine ⟨((Unitary.isUnit_coe.mul (ih_unit.map τ)).mul ?_).mul hz, ?_⟩
    · exact (Unitary.isUnit_coe (U := star c))
    have h := ((ih_root.map hτ hτ_star).conj hc).mul ha
    convert h using 1
    set T := (Unitary.map (⟨τ, hτ_star⟩ : A →⋆* A)).toMonoidHom
    have hg : T.twistedNorm (q + 1) c * (T.twistedNorm (q + 1) (a⁻¹ * c))⁻¹ =
        c * T (T.twistedNorm q c * (T.twistedNorm q (a⁻¹ * c))⁻¹) * star c * a := by
      simp only [MonoidHom.twistedNorm_succ, map_mul, map_inv, Unitary.star_eq_inv]
      group
    rw [hg]
    rfl

include hτ in
/-- Let `τ` be a ring endomorphism of `A` commuting with `star` and acting on scalars through
`σ`, and `N` the twisted norms of length `p` under `σ` and under `τ`. Let `a`, `γ`, `c` be unitary,
with `a` a root quotient of `z` at `γ`, `γ` a root quotient of `N(z)` at `γ`, `aeval γ z` a unit
and `γ * c = c * τ γ`. Then `N(c) = γ * N(a⁻¹ * c)`. -/
theorem IsRootQuotient.twistedNorm_eq_mul {p : ℕ} {z : R[X]} {γ a c : unitary A}
    (hγ : IsRootQuotient (MonoidHom.twistedNorm (mapRingHom σ : R[X] →* R[X]) p z) (γ : A) γ)
    (hc : (γ : A) * c = c * τ γ) (ha : IsRootQuotient z (γ : A) a)
    (hz : IsUnit (aeval (γ : A) z)) :
    MonoidHom.twistedNorm (Unitary.map ⟨τ, hτ_star⟩).toMonoidHom p c =
      γ * MonoidHom.twistedNorm (Unitary.map ⟨τ, hτ_star⟩).toMonoidHom p (a⁻¹ * c) := by
  obtain ⟨h_unit, h_root⟩ := isUnit_and_isRootQuotient_twistedNorm hτ hτ_star hc ha hz p
  exact eq_mul_of_mul_inv_eq (Subtype.ext (eq_of_isUnit h_unit h_root hγ))

end TwistedNorm

end Polynomial
