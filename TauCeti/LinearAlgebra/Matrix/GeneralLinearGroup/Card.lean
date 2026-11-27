/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `qPochhammer` occurs in the statement of the density identity.
public import TauCeti.Algebra.Ring.QPochhammer.Basic
-- Non-public: `Matrix.card_GL_field` is what the two factorizations below are read off, in the
-- proofs only.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- Non-public: the determinant surjection transfers vanishing cardinality for infinite fields.
import Mathlib.SetTheory.Cardinal.NatCard
-- Non-public: the density identity reverses its product and clears denominators.
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.BigOperators.Finset.Range
-- Non-public: the count along a local surjection is the unit count of the matrix rings.
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.RingTheory.LocalRing.RingHom
-- Non-public: `Finset.prod_range_add_sub_eq` reverses the factors `q ^ i - 1`.
import TauCeti.Algebra.BigOperators.Finset.Range
-- Non-public: `Nat.pow_sub_pow_eq_pow_mul_pow_sub_one` factors each difference `q ^ n - q ^ i`.
import TauCeti.Data.Nat.Pow

/-!
# The order of general linear groups

## Over a field

Mathlib's `Matrix.card_GL_field` gives `|GL n 𝔽_q| = ∏ i, (qⁿ - qⁱ)`, a product of differences.
Writing each difference as `qⁱ (qⁿ⁻ⁱ - 1)` gives the closed form of `TauCeti.natCard_GL_fin`,
`|GLₙ(𝔽)| = q ^ (n.choose 2) · ∏_{i = 1}^{n} (q ^ i - 1)`: the order of the upper-unitriangular
group times its index. In size two the product reads `(q² - 1)(q² - q)`, and every index
computation in `GL₂` divides it by the order of a subgroup, so what is wanted there is the
factored form `(q - 1)² · q · (q + 1)`, where the natural subtraction has already been carried
out. It is recorded here in the two associations the two maximal tori call for: the split torus
has order `(q - 1)²` and the non-split one `q² - 1`.

The formulas use `q = Nat.card F` and require no chosen enumeration or finiteness assumption.
For an infinite field, both the field and its general linear group have `Nat.card` equal to zero,
so the same identities hold.

Dividing `Matrix.card_GL_field` by the `q^{n²}` matrices gives the proportion of invertible
matrices, `∏_{i=0}^{n-1} (q^n - q^i) / q^{n²} = ∏_{i=1}^n (1 - q^{-i})`, the q-Pochhammer product
`(q⁻¹; q⁻¹)_n`; the identity behind this holds for any nonzero `q` in a field.

## Along a local surjection

A surjective ring homomorphism `f : R →+* S` that reflects units (`IsLocalHom f`), such as the
reduction `ℤ/pᵏ → 𝔽_p`, multiplies the order of `GL n` by `|ker f| ^ (n²)`: an `n × n` matrix is
invertible exactly when its image is, and the entrywise map on matrices is a surjective local
homomorphism whose kernel is the matrices with entries in `ker f`.

## Main results

* `Matrix.natCard_GL_eq_natCard_ker_pow_mul`: `|GL n R| = |ker f| ^ (n²) · |GL n S|` for a
  surjective local homomorphism `f : R →+* S`.
* `TauCeti.natCard_GL_fin`: `|GLₙ(𝔽_q)| = q ^ (n.choose 2) · ∏_{i = 1}^{n} (q ^ i - 1)`.
* `TauCeti.natCard_GL_fin_two`: `|GL₂(𝔽_q)| = (q - 1)² · q(q + 1)`.
* `TauCeti.natCard_GL_fin_two_eq_sq_sub_one_mul`: `|GL₂(𝔽_q)| = (q² - 1) · q(q - 1)`.
* `TauCeti.natCard_GL_fin_two_of_card_eq_two`: `|GL₂(𝔽₂)| = 6`.
* `TauCeti.prod_range_pow_sub_pow_div_pow`: `∏_{i=0}^{n-1} (q^n - q^i) / q^{n²} = (q⁻¹; q⁻¹)_n`
  in a field, the proportion of invertible matrices over `𝔽_q`.
-/

public section

namespace TauCeti

variable (F : Type*) [Field F]

/-- **The order of `GLₙ` over a field**: for a field `𝔽` with `q` elements,
`|GLₙ(𝔽)| = q ^ (n.choose 2) · ∏_{i = 1}^{n} (q ^ i - 1)`, the order of the upper-unitriangular
group times its index. For an infinite field both sides are `1` when `n = 0` and `0` otherwise. -/
theorem natCard_GL_fin (n : ℕ) :
    Nat.card (GL (Fin n) F) = Nat.card F ^ n.choose 2 *
      ∏ i ∈ Finset.range n, (Nat.card F ^ (i + 1) - 1) := by
  rcases finite_or_infinite F with _ | hF
  · let := Fintype.ofFinite F
    rw [Matrix.card_GL_field, Fin.prod_univ_eq_prod_range
      (fun i => (Fintype.card F ^ n - Fintype.card F ^ i : ℕ)) n, ← Nat.card_eq_fintype_card]
    have hfactor : ∀ i ∈ Finset.range n, Nat.card F ^ n - Nat.card F ^ i =
        Nat.card F ^ i * (Nat.card F ^ (n - i) - 1) := fun i hi =>
      Nat.pow_sub_pow_eq_pow_mul_pow_sub_one (Finset.mem_range_le hi)
    have hsum : ∏ i ∈ Finset.range n, Nat.card F ^ i = Nat.card F ^ n.choose 2 := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id n, Nat.choose_two_right]
    have hreflect : ∏ i ∈ Finset.range n, (Nat.card F ^ (n - i) - 1) =
        ∏ i ∈ Finset.range n, (Nat.card F ^ (i + 1) - 1) := by
      simpa using Finset.prod_range_add_sub_eq (fun j => Nat.card F ^ j - 1) 0 n
    rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, hsum, hreflect]
  · cases n with
    | zero => simp
    | succ n =>
      have hcard : Nat.card (GL (Fin (n + 1)) F) = 0 :=
        Finite.card_eq_zero_of_surjective Matrix.GeneralLinearGroup.det_surjective
          (by simp [Nat.card_units])
      rw [hcard, Nat.card_eq_zero_of_infinite (α := F)]
      simp

/-- **The order of `GL₂` over a field**, in the factored form `(q - 1)² · q(q + 1)`: the
first factor is the order of the split torus and the second its index. -/
theorem natCard_GL_fin_two :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F - 1) ^ 2 * (Nat.card F * (Nat.card F + 1)) := by
  rw [natCard_GL_fin F 2]
  simp only [Nat.choose_two_right, Finset.prod_range_succ, Finset.prod_range_zero, pow_one,
    Nat.zero_add, Nat.reduceAdd]
  simp_rw [pow_two, mul_self_tsub_one]
  ring

/-- **The order of `GL₂` over a field**, in the factored form `(q² - 1) · q(q - 1)`: the
first factor is the order of the non-split torus and the second its index. -/
theorem natCard_GL_fin_two_eq_sq_sub_one_mul :
    Nat.card (GL (Fin 2) F) =
      (Nat.card F ^ 2 - 1) * (Nat.card F * (Nat.card F - 1)) := by
  rw [natCard_GL_fin_two F]
  simp_rw [pow_two, mul_self_tsub_one]
  ring

variable {F} in
/-- **`GL₂` over a field with two elements has order `6`.** This is `(q - 1)² · q(q + 1)` at
`q = 2`. -/
theorem natCard_GL_fin_two_of_card_eq_two (hF : Nat.card F = 2) :
    Nat.card (GL (Fin 2) F) = 6 := by
  rw [natCard_GL_fin_two F, hF]
  norm_num

variable {F} in
/-- **The proportion of invertible matrices**, as a q-Pochhammer product: in a field,
`∏_{i=0}^{n-1} (q^n - q^i) / q^{n²} = (q⁻¹; q⁻¹)_n = ∏_{i=1}^n (1 - q^{-i})` for `q ≠ 0`. With
`q = Nat.card F` for a finite field `F`, the left side is `|GL n F| / |M_n(F)|` by
`Matrix.card_GL_field`. -/
theorem prod_range_pow_sub_pow_div_pow {q : F} (hq : q ≠ 0) (n : ℕ) :
    (∏ i ∈ Finset.range n, (q ^ n - q ^ i)) / q ^ (n * n) = qPochhammer q⁻¹ q⁻¹ n := calc
  _ = ∏ i ∈ Finset.range n, (q ^ n - q ^ i) / q ^ n := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  _ = ∏ i ∈ Finset.range n, (1 - q⁻¹ ^ (n - i)) := Finset.prod_congr rfl fun i hi => by
    rw [inv_pow, ← pow_sub_mul_pow q (Finset.mem_range.1 hi).le]
    field_simp
  _ = qPochhammer q⁻¹ q⁻¹ n := by
    simpa [qPochhammer_self] using Finset.prod_range_add_sub_eq (fun j => 1 - q⁻¹ ^ j) 0 n

end TauCeti

namespace Matrix

/-- **The order of `GL n` along a surjective local homomorphism.** If `f : R →+* S` is surjective
and reflects units, then `|GL n R| = |ker f| ^ (n²) · |GL n S|`: this is the unit count of
`RingHom.natCard_units_eq_natCard_ker_mul` for the entrywise map on matrices. -/
theorem natCard_GL_eq_natCard_ker_pow_mul {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Nat.card (GL n R) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n * Fintype.card n) * Nat.card (GL n S) := by
  rw [← f.natCard_ker_mapMatrix]
  exact (f.mapMatrix (m := n)).natCard_units_eq_natCard_ker_mul fun M ↦
    ⟨of fun i j ↦ (hf (M i j)).choose, ext fun i j ↦ (hf (M i j)).choose_spec⟩

end Matrix
