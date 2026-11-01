/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Derivation.LocallyNilpotent
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Tactic.FieldSimp

/-!
# Local nilpotence and exponentials of derivations

For a derivation of a possibly noncommutative algebra, the elements annihilated by some power
are closed under multiplication. Consequently, local nilpotence can be checked on algebra
generators. Both facts specialise the corresponding results for linear endomorphisms satisfying
the Leibniz rule in `TauCeti.RingTheory.Derivation.LocallyNilpotent`.

These facts allow nilpotent Lie derivations to act nilpotently on finite stable quotients of
universal enveloping algebras, even though the lifted derivations on the enveloping algebras
need not have a uniform nilpotence bound.

A locally nilpotent derivation `D` of a Lie algebra over a `ℚ`-algebra has an exponential
`exp D x = ∑ Dᵏ x / k!`, and the divided-power Leibniz rule
`Dᵐ ⁅x, y⁆ / m! = ∑ ⁅Dⁱ x / i!, Dʲ y / j!⁆` makes it a Lie algebra automorphism
(`LieDerivation.locallyNilpotentExp`). Mathlib's `LieDerivation.exp` needs a global nilpotence
bound, which the adjoint action of a generator of an infinite-dimensional Lie algebra presented by
generators and relations does not have.

## Main declarations

* `TauCeti.derivationLieAlgebra.exists_pow_apply_eq_zero_of_mem_adjoin`: local nilpotence of an
  algebra derivation can be checked on generators.
* `LieDerivation.locallyNilpotentExp`: the exponential of a locally nilpotent Lie derivation, as a
  Lie algebra automorphism, with inverse `LieDerivation.symm_locallyNilpotentExp`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5, for the use of nilpotent derivations on finite enveloping quotients.
-/

public section

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- If powers `n` and `m` of a derivation kill the two factors, power `n + m` kills their
product. Neither associativity nor commutativity of multiplication is required. -/
theorem pow_apply_mul_eq_zero (D : derivationLieAlgebra R A) {x y : A} {n m : ℕ}
    (hx : ((D : Module.End R A) ^ n) x = 0)
    (hy : ((D : Module.End R A) ^ m) y = 0) :
    ((D : Module.End R A) ^ (n + m)) (x * y) = 0 :=
  Module.End.pow_apply_mul_eq_zero_of_leibniz (leibniz D) hx hy

end TauCeti.derivationLieAlgebra

namespace TauCeti.derivationLieAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Local nilpotence on a set of generators extends to the algebra they generate. -/
theorem exists_pow_apply_eq_zero_of_mem_adjoin (D : derivationLieAlgebra R A) {s : Set A}
    (hs : ∀ x ∈ s, ∃ n : ℕ, ((D : Module.End R A) ^ n) x = 0)
    {a : A} (ha : a ∈ Algebra.adjoin R s) :
    ∃ n : ℕ, ((D : Module.End R A) ^ n) a = 0 :=
  Module.End.exists_pow_apply_eq_zero_of_mem_adjoin_of_leibniz (leibniz D)
    (apply_one_eq_zero D) hs ha

end TauCeti.derivationLieAlgebra

/-! ### The exponential of a locally nilpotent Lie derivation -/

section Exp

open Finset

namespace LieDerivation

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

/-- The divided-power Leibniz rule `Dᵐ ⁅x, y⁆ / m! = ∑ ⁅Dⁱ x / i!, Dʲ y / j!⁆` over `i + j = m`,
with the inverse factorials taken in a `ℚ`-algebra `R` acting on `L`. -/
private theorem inv_factorial_smul_pow_apply_lie (D : LieDerivation R L L) (m : ℕ) (x y : L) :
    algebraMap ℚ R (m.factorial : ℚ)⁻¹ • (D.toLinearMap ^ m) ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal m,
        ⁅algebraMap ℚ R (ij.1.factorial : ℚ)⁻¹ • (D.toLinearMap ^ ij.1) x,
          algebraMap ℚ R (ij.2.factorial : ℚ)⁻¹ • (D.toLinearMap ^ ij.2) y⁆ := by
  -- `Module.End.pow_apply` presents iteration through the underlying linear-map function,
  -- whereas `LieDerivation.iterate_apply_lie` uses the derivation's function coercion.
  have hpow : ∀ (k : ℕ) (z : L), (D.toLinearMap ^ k) z = D^[k] z := fun k z => by
    rw [Module.End.pow_apply]
    rfl
  rw [hpow, iterate_apply_lie, smul_sum]
  refine sum_congr rfl fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  subst m
  have hcoeff : ((ij.1 + ij.2).factorial : ℚ)⁻¹ * ((ij.1 + ij.2).choose ij.1 : ℚ) =
      (ij.2.factorial : ℚ)⁻¹ * (ij.1.factorial : ℚ)⁻¹ := by
    have hfac := Nat.add_choose_mul_factorial_mul_factorial ij.2 ij.1
    rw [Nat.add_comm ij.2] at hfac
    field_simp
    exact_mod_cast hfac
  rw [hpow, hpow, lie_smul, smul_lie, smul_smul, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    ← map_natCast (algebraMap ℚ R), ← map_mul, ← map_mul, hcoeff]

/-- The exponential of a locally nilpotent Lie derivation preserves the bracket. -/
private theorem locallyNilpotentExp_lie (D : LieDerivation R L L)
    (hD : ∀ x, ∃ n, (D.toLinearMap ^ n) x = 0) (x y : L) :
    Module.End.locallyNilpotentExp D.toLinearMap hD ⁅x, y⁆ =
      ⁅Module.End.locallyNilpotentExp D.toLinearMap hD x,
        Module.End.locallyNilpotentExp D.toLinearMap hD y⁆ := by
  obtain ⟨n, hn⟩ := hD x
  obtain ⟨m, hm⟩ := hD y
  let c : ℕ → R := fun k => algebraMap ℚ R (k.factorial : ℚ)⁻¹
  let g : ℕ × ℕ → L := fun ij =>
    ⁅c ij.1 • (D.toLinearMap ^ ij.1) x, c ij.2 • (D.toLinearMap ^ ij.2) y⁆
  have hg : ∀ i j, n ≤ i ∨ m ≤ j → g (i, j) = 0 := fun i j hij => by
    rcases hij with hi | hj
    · simp only [g, Module.End.pow_map_zero_of_le hi hn, smul_zero, zero_lie]
    · simp only [g, Module.End.pow_map_zero_of_le hj hm, smul_zero, lie_zero]
  -- the bracket of the two truncated series is the double series truncated at `n + m`
  have hsum : ∑ k ∈ range (n + m), c k • (D.toLinearMap ^ k) ⁅x, y⁆ =
      ∑ i ∈ range n, ∑ j ∈ range m, g (i, j) := by
    rw [← TauCeti.sum_range_add_antidiagonal_of_support n m g hg]
    exact sum_congr rfl fun k _ => inv_factorial_smul_pow_apply_lie D k x y
  have hxy : (D.toLinearMap ^ (n + m)) ⁅x, y⁆ = 0 := by
    -- as above, pass from powers of the linear map to iterates of the derivation
    rw [Module.End.pow_apply, show (⇑D.toLinearMap)^[n + m] ⁅x, y⁆ = D^[n + m] ⁅x, y⁆ from rfl,
      iterate_apply_lie]
    refine sum_eq_zero fun ij hij => ?_
    rw [mem_antidiagonal] at hij
    rcases le_or_gt n ij.1 with hi | hi
    · rw [show D^[ij.1] x = (D.toLinearMap ^ ij.1) x by rw [Module.End.pow_apply]; rfl,
        Module.End.pow_map_zero_of_le hi hn, zero_lie, smul_zero]
    · rw [show D^[ij.2] y = (D.toLinearMap ^ ij.2) y by rw [Module.End.pow_apply]; rfl,
        Module.End.pow_map_zero_of_le (by omega) hm, lie_zero, smul_zero]
  rw [Module.End.locallyNilpotentExp_apply_eq_sum _ hD hn,
    Module.End.locallyNilpotentExp_apply_eq_sum _ hD hm,
    Module.End.locallyNilpotentExp_apply_eq_sum _ hD hxy, hsum, sum_lie]
  simp only [g, c, lie_sum]

/-- **The exponential of a locally nilpotent Lie derivation.** If every element of `L` is killed by
some power of the derivation `D`, then over a `ℚ`-algebra the exponential series
`exp D x = ∑ Dᵏ x / k!` is a Lie algebra automorphism of `L`, with inverse `exp (-D)`. Unlike
`LieDerivation.exp`, no global nilpotence bound is required, so this applies to the locally
nilpotent inner derivations of an infinite-dimensional Lie algebra. -/
noncomputable def locallyNilpotentExp (D : LieDerivation R L L)
    (hD : ∀ x, ∃ n, (D.toLinearMap ^ n) x = 0) : L ≃ₗ⁅R⁆ L :=
  { Module.End.locallyNilpotentExp D.toLinearMap hD with
    map_lie' := fun {x y} => locallyNilpotentExp_lie D hD x y }

/-- The Lie exponential of a locally nilpotent derivation is the linear exponential of its
underlying endomorphism. -/
@[simp]
theorem locallyNilpotentExp_apply (D : LieDerivation R L L)
    (hD : ∀ x, ∃ n, (D.toLinearMap ^ n) x = 0) (x : L) :
    D.locallyNilpotentExp hD x = Module.End.locallyNilpotentExp D.toLinearMap hD x :=
  (rfl)

/-- The inverse of `exp D` is `exp (-D)`. -/
theorem symm_locallyNilpotentExp (D : LieDerivation R L L)
    (hD : ∀ x, ∃ n, (D.toLinearMap ^ n) x = 0) :
    (D.locallyNilpotentExp hD).symm =
      (-D).locallyNilpotentExp fun x => (hD x).imp fun _ hn => by
        rw [coe_neg_linearMap, neg_pow, Module.End.mul_apply, hn, map_zero] := by
  ext x
  -- the inverse of the Lie equivalence is, as a function, the inverse of its linear equivalence
  change (Module.End.locallyNilpotentExp D.toLinearMap hD).symm x = _
  rw [Module.End.symm_locallyNilpotentExp, locallyNilpotentExp_apply]
  congr 1

end LieDerivation

end Exp
