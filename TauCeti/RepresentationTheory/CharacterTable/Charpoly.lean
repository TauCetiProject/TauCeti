/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Characters determine characteristic polynomials

For a finite-dimensional representation `ρ` of a monoid and an element `g`, the traces of the
powers of `ρ g` are character values: `tr (ρ g ^ j) = χ_ρ (g ^ j)`. Newton's identities for the
traces of the powers of an endomorphism therefore express the coefficients of `det (1 - X ρ g)`
through the character values `χ_ρ (g), χ_ρ (g ^ 2), …`. In characteristic zero the recurrence can
be solved, so the dimension of `ρ` together with the values `χ_ρ (g ^ j)` for `0 < j ≤ dim ρ`
determines the characteristic polynomial of `ρ g`.

The characteristic polynomial of `ρ g` is also invariant under isomorphism of representations,
multiplicative on products and compatible with scalar extension.

## Main results

* `Representation.trace_pow_eq_character_pow`: `tr (ρ g ^ j) = χ_ρ (g ^ j)`.
* `Representation.mul_coeff_reverse_charpoly_eq_neg_sum`: **Newton's identities** in character
  form, `r c_r = -(c_(r-1) χ(g) + c_(r-2) χ(g ^ 2) + ⋯ + c_0 χ(g ^ r))` for the coefficients `c_r`
  of `det (1 - X ρ g)`, in every characteristic.
* `Representation.charpoly_eq_of_character_pow_eq`,
  `Representation.charpoly_eq_iff_character_pow_eq`: in characteristic zero, the dimension and the
  character values on `g, g ^ 2, …, g ^ d` determine the characteristic polynomial of `ρ g`. The
  two representations may be of different monoids.
* `Representation.charpoly_apply_eq_of_sq_eq_one`: if `g ^ 2 = 1`, then
  `charpoly (ρ g) = (X - 1) ^ a * (X + 1) ^ b` whenever `a + b = dim ρ` and `a - b = χ_ρ (g)`.
* `Representation.Equiv.charpoly_apply_eq`, `Representation.charpoly_prod_apply`,
  `Representation.charpoly_baseChange_apply`: invariance under isomorphism, multiplicativity on
  products, and compatibility with scalar extension.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2, (2.11′) and (2.14′).
-/

public section

open Finset Module Polynomial

namespace Representation

section CommRing

variable {R G V W : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Free R W]
  [Module.Finite R W] {ρ : Representation R G V} {σ : Representation R G W}

/-- Isomorphic representations have the same characteristic polynomials. -/
theorem Equiv.charpoly_apply_eq (φ : ρ.Equiv σ) (g : G) : (ρ g).charpoly = (σ g).charpoly := by
  rw [← φ.conj_apply_self g, LinearEquiv.charpoly_conj]

variable (ρ σ) in
/-- The characteristic polynomial is multiplicative on products of representations. -/
@[simp]
theorem charpoly_prod_apply (g : G) :
    (ρ.prod σ g).charpoly = (ρ g).charpoly * (σ g).charpoly :=
  LinearMap.charpoly_prodMap (ρ g) (σ g)

variable (ρ) in
/-- The characteristic polynomials of a base-changed representation are those of the original
representation, read in the larger ring of scalars. -/
theorem charpoly_baseChange_apply (A : Type*) [CommRing A] [Algebra R A] (g : G) :
    (baseChange A ρ g).charpoly = (ρ g).charpoly.map (algebraMap R A) := by
  rw [baseChange_apply, LinearMap.charpoly_baseChange]

end CommRing

section Field

variable {k G H V W : Type*} [Field k] [Monoid G] [Monoid H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] (ρ : Representation k G V) {σ : Representation k H W}

/-- The traces of the powers of `ρ g` are the character values at the powers of `g`. -/
theorem trace_pow_eq_character_pow (g : G) (j : ℕ) :
    LinearMap.trace k V (ρ g ^ j) = ρ.character (g ^ j) := by
  rw [character, map_pow ρ]

variable [FiniteDimensional k V] [FiniteDimensional k W]

/-- **Newton's identities** in character form: the coefficients `c_r` of `det (1 - X ρ g)`, the
reverse of the characteristic polynomial of `ρ g`, satisfy
`r c_r = -(c_(r-1) χ(g) + c_(r-2) χ(g ^ 2) + ⋯ + c_0 χ(g ^ r))`, in every characteristic. -/
theorem mul_coeff_reverse_charpoly_eq_neg_sum (g : G) (r : ℕ) :
    (r : k) * (ρ g).charpoly.reverse.coeff r =
      -∑ j ∈ range r, (ρ g).charpoly.reverse.coeff (r - (j + 1)) * ρ.character (g ^ (j + 1)) := by
  simp only [← trace_pow_eq_character_pow]
  exact (ρ g).mul_coeff_reverse_charpoly_eq_neg_sum r

/-- In every characteristic, the characteristic polynomial of `ρ g` determines the character values
at all positive powers of `g`. -/
theorem character_pow_eq_of_charpoly_eq {g : G} {h : H} (hgh : (ρ g).charpoly = (σ h).charpoly)
    {j : ℕ} (hj : 0 < j) : ρ.character (g ^ j) = σ.character (h ^ j) := by
  rw [← trace_pow_eq_character_pow, ← trace_pow_eq_character_pow,
    LinearMap.trace_pow_eq_of_charpoly_eq hgh hj]

variable [CharZero k]

/-- In characteristic zero, the dimension of `ρ` and the character values `χ_ρ (g ^ j)` for
`0 < j ≤ dim ρ` determine the characteristic polynomial of `ρ g`. The two representations may be
of different monoids. -/
theorem charpoly_eq_of_character_pow_eq {g : G} {h : H} (hVW : finrank k V = finrank k W)
    (hgh : ∀ j, 0 < j → j ≤ finrank k V → ρ.character (g ^ j) = σ.character (h ^ j)) :
    (ρ g).charpoly = (σ h).charpoly :=
  LinearMap.charpoly_eq_of_trace_pow_eq hVW fun j hj hjV ↦ by
    rw [trace_pow_eq_character_pow, trace_pow_eq_character_pow, hgh j hj hjV]

/-- In characteristic zero, for representations of the same dimension, `ρ g` and `σ h` have the
same characteristic polynomial if and only if `χ_ρ (g ^ j) = χ_σ (h ^ j)` for every `j > 0`. -/
theorem charpoly_eq_iff_character_pow_eq {g : G} {h : H} (hVW : finrank k V = finrank k W) :
    (ρ g).charpoly = (σ h).charpoly ↔ ∀ j, 0 < j → ρ.character (g ^ j) = σ.character (h ^ j) :=
  ⟨fun hgh _ ↦ ρ.character_pow_eq_of_charpoly_eq hgh, fun hgh ↦
    ρ.charpoly_eq_of_character_pow_eq hVW fun j hj _ ↦ hgh j hj⟩

/-- In characteristic zero, if `g ^ 2 = 1`, then the characteristic polynomial of `ρ g` is
`(X - 1) ^ a * (X + 1) ^ b` for any `a` and `b` with `a + b = dim ρ` and `a - b = χ_ρ (g)`. -/
theorem charpoly_apply_eq_of_sq_eq_one {g : G} (hg : g ^ 2 = 1) {a b : ℕ}
    (hab : a + b = finrank k V) (hχ : (a : k) - b = ρ.character g) :
    (ρ g).charpoly = (X - 1) ^ a * (X + 1) ^ b := by
  -- Compare `ρ g` with the diagonal matrix with `a` entries `1` and `b` entries `-1`.
  let D : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) k :=
    Matrix.diagonal (Sum.elim (fun _ ↦ 1) fun _ ↦ -1)
  have hD : D.charpoly = (X - 1) ^ a * (X + 1) ^ b := by
    simp [D, Matrix.charpoly_diagonal, Fintype.prod_sum_type, sub_eq_add_neg]
  have hDtrace (j : ℕ) : (D ^ j).trace = a + (-1) ^ j * b := by
    simp [D, Matrix.diagonal_pow, Matrix.trace_diagonal, Fintype.sum_sum_type, mul_comm]
  have hpow (j : ℕ) : g ^ j = if Even j then 1 else g := by
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
    · simp [pow_mul, hg]
    · simp [pow_succ, pow_mul, hg]
  rw [← hD, ← LinearMap.charpoly_toMatrix (ρ g) (Module.finBasis k V)]
  refine Matrix.charpoly_eq_of_trace_pow_eq (by simp [hab]) fun j _ _ ↦ ?_
  rw [hDtrace, LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace,
    trace_pow_eq_character_pow, hpow]
  rcases Nat.even_or_odd j with hj | hj
  · simp [hj, hj.neg_one_pow, ← hab]
  · simp [Nat.not_even_iff_odd.2 hj, hj.neg_one_pow, ← hχ, sub_eq_add_neg]

end Field

end Representation
