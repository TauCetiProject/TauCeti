/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import TauCeti.LinearAlgebra.End.Exp
import Mathlib.Tactic.FieldSimp

/-!
# The exponential of a locally nilpotent Lie derivation

Mathlib's `LieDerivation.exp` exponentiates a derivation `D` of a Lie algebra `L` in characteristic
zero when `D` is nilpotent. This file only asks that `D` be *locally* nilpotent: every element of
`L` is killed by some power of `D`, with no bound uniform in the element. The exponential
`Module.End.locallyNilpotentExp` of the underlying endomorphism is then an automorphism of the Lie
algebra, `LieDerivation.locallyNilpotentExp D hD`, agreeing with `LieDerivation.exp` when `D` is
nilpotent.

The bracket is preserved by the Leibniz rule `Dⁿ ⁅x, y⁆ = ∑ (n choose i) ⁅Dⁱ x, Dⁿ⁻ⁱ y⁆`
(`LieDerivation.iterate_apply_lie`): if `D ^ N` kills both `x` and `y`, then `D ^ (2 N)` kills
`⁅x, y⁆`, and the exponential series of `⁅x, y⁆` truncated at `2 N` is the bracket of the two
series truncated at `N`.

The local version is needed for Lie algebras that are not known to be finite-dimensional, such as
an algebra presented by Serre's relations: there the adjoint action of each Chevalley generator is
locally nilpotent, but no single power of it is known to vanish.

## Main definitions

* `LieDerivation.locallyNilpotentExp`: the exponential of a locally nilpotent derivation, as a Lie
  algebra automorphism.

## Main results

* `LieDerivation.locallyNilpotentExp_apply_eq_sum`: the exponential at an element killed by
  `D ^ k` is the exponential series truncated at length `k`.
* `LieDerivation.locallyNilpotentExp_eq_exp`: for nilpotent `D` it is `LieDerivation.exp`.

## References

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972],
  §18.3, where the exponentials of the locally nilpotent `ad xᵢ` and `ad yᵢ` on the algebra
  presented by Serre's relations are used in the proof of Serre's theorem.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, 3rd ed., Chapter 3.
-/

public section

open Finset

namespace LieDerivation

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [Module ℚ L]
  (D : LieDerivation R L L) (hD : ∀ x, ∃ n, (D.toLinearMap ^ n) x = 0)

/-- Rational scalars pass through the bracket: the bracket is biadditive, hence `ℚ`-bilinear. -/
private theorem rat_smul_lie_rat_smul (p q : ℚ) (x y : L) :
    ⁅p • x, q • y⁆ = (p * q) • ⁅x, y⁆ := by
  have h₁ : ∀ (a b : L) (c : ℚ), ⁅a, c • b⁆ = c • ⁅a, b⁆ := fun a b c ↦
    map_rat_smul (AddMonoidHom.mk' (fun b ↦ ⁅a, b⁆) (lie_add a)) c b
  rw [h₁, ← lie_skew, h₁, ← lie_skew y x]
  module

/-- The exponential of a locally nilpotent derivation preserves the bracket. -/
private theorem locallyNilpotentExp_lie (x y : L) :
    Module.End.locallyNilpotentExp D.toLinearMap hD ⁅x, y⁆ =
      ⁅Module.End.locallyNilpotentExp D.toLinearMap hD x,
        Module.End.locallyNilpotentExp D.toLinearMap hD y⁆ := by
  obtain ⟨k, hx⟩ := hD x
  obtain ⟨l, hy⟩ := hD y
  set N := max k l
  have hxN : ∀ i, N ≤ i → (D.toLinearMap ^ i) x = 0 := fun i hi ↦
    Module.End.pow_map_zero_of_le ((le_max_left k l).trans hi) hx
  have hyN : ∀ i, N ≤ i → (D.toLinearMap ^ i) y = 0 := fun i hi ↦
    Module.End.pow_map_zero_of_le ((le_max_right k l).trans hi) hy
  have hvan : ∀ i j, N ≤ i ∨ N ≤ j → ⁅(D.toLinearMap ^ i) x, (D.toLinearMap ^ j) y⁆ = 0 := by
    rintro i j (h | h)
    · rw [hxN i h, zero_lie]
    · rw [hyN j h, lie_zero]
  have hxy : (D.toLinearMap ^ (N + N)) ⁅x, y⁆ = 0 := by
    rw [Module.End.pow_apply, coeFn_coe, D.iterate_apply_lie]
    simp only [← coeFn_coe, ← Module.End.pow_apply]
    refine sum_eq_zero fun ij hij ↦ ?_
    rw [mem_antidiagonal] at hij
    rw [hvan ij.1 ij.2 (by omega), smul_zero]
  rw [Module.End.locallyNilpotentExp_apply_eq_sum _ hD hxy,
    Module.End.locallyNilpotentExp_apply_eq_sum _ hD (hxN N le_rfl),
    Module.End.locallyNilpotentExp_apply_eq_sum _ hD (hyN N le_rfl), sum_lie]
  simp_rw [lie_sum, rat_smul_lie_rat_smul]
  rw [← TauCeti.sum_range_add_antidiagonal_of_support N N
    (fun p ↦ ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) •
      ⁅(D.toLinearMap ^ p.1) x, (D.toLinearMap ^ p.2) y⁆)
    (fun i j h ↦ by rw [hvan i j h, smul_zero])]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [Module.End.pow_apply, coeFn_coe, D.iterate_apply_lie, smul_sum]
  simp only [← coeFn_coe, ← Module.End.pow_apply]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  subst hp
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  field_simp
  exact_mod_cast (by
    simpa [Nat.add_comm, Nat.mul_right_comm] using
      Nat.add_choose_mul_factorial_mul_factorial p.2 p.1)

/-- **The exponential of a locally nilpotent derivation.** If every element of `L` is killed by
some power of the derivation `D`, the exponential series `∑ (Dⁱ x) / i!` is a finite sum at every
`x`, and it defines an automorphism of the Lie algebra `L`. -/
noncomputable def locallyNilpotentExp : L ≃ₗ⁅R⁆ L :=
  { Module.End.locallyNilpotentExp D.toLinearMap hD with
    map_lie' := fun {x y} ↦ locallyNilpotentExp_lie D hD x y }

/-- The linear automorphism underlying the exponential of a locally nilpotent derivation is the
exponential of its underlying endomorphism. -/
@[simp]
theorem toLinearEquiv_locallyNilpotentExp :
    (D.locallyNilpotentExp hD).toLinearEquiv = Module.End.locallyNilpotentExp D.toLinearMap hD :=
  (rfl)

/-- **The exponential as a truncated series.** At an element killed by `D ^ k`, the exponential of
`D` is its exponential series truncated at length `k`. -/
theorem locallyNilpotentExp_apply_eq_sum {x : L} {k : ℕ} (hk : (D.toLinearMap ^ k) x = 0) :
    D.locallyNilpotentExp hD x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (D.toLinearMap ^ i) x :=
  Module.End.locallyNilpotentExp_apply_eq_sum _ hD hk

/-- **The inverse of the exponential.** At an element killed by `D ^ k`, the inverse of the
exponential of `D` is the exponential series of `-D` truncated at length `k`. -/
theorem locallyNilpotentExp_symm_apply_eq_sum {x : L} {k : ℕ} (hk : (D.toLinearMap ^ k) x = 0) :
    (D.locallyNilpotentExp hD).symm x =
      ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • ((-D.toLinearMap) ^ i) x :=
  Module.End.locallyNilpotentExp_symm_apply_eq_sum _ hD hk

/-- For a nilpotent derivation, the exponential is Mathlib's `LieDerivation.exp`. -/
theorem locallyNilpotentExp_eq_exp (h : IsNilpotent D.toLinearMap) :
    D.locallyNilpotentExp hD = LieDerivation.exp D h := by
  ext x
  rw [exp_map_apply, ← Module.End.locallyNilpotentExp_eq_exp _ hD h]
  rfl

end LieDerivation
