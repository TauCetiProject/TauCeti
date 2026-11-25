/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import TauCeti.Algebra.MvPolynomial.Fin.Three

/-!
# Additive 2-cocycles given by power series in characteristic zero

A power series `f(Y, Z) = ∑ b_{i,j} Yⁱ Zʲ` is an *additive 2-cocycle* if

  `f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`,

the cocycle identity of the additive formal group with trivial coefficients. The *coboundary* of a
one-variable series `u(X) = ∑ a_k Xᵏ` is the additivity defect `u(Y + Z) - u(Y) - u(Z)`. This file
works with the coefficient families `b : ℕ × ℕ → M` and `a : ℕ → M` directly, with coefficients in
an arbitrary additive commutative group `M`. Both identities compare coefficients of finitely many
monomials of each degree, so they make sense for formal, restricted or convergent series alike, and
for vector-valued coefficients, where substitution of `X + Y` into a series over a ring is not
available.

* `TauCeti.IsAddCocycleCoeff b`: the cocycle identity at every monomial `XⁱYʲZᵏ`. It is the
  coefficient form of `MvPolynomial.IsAddCocycle₂`
  (`MvPolynomial.isAddCocycle₂_iff_isAddCocycleCoeff`).
* `TauCeti.addCoboundaryCoeff a`: the coefficients of `u(Y + Z) - u(Y) - u(Z)`. For a power
  series over a commutative ring they are the coefficients of its homomorphism defect
  `u(X₀ + X₁) - u(X₀) - u(X₁)` from the additive formal group law to itself
  (`FormalGroup.coeff_homDefect_𝔾ₐ_𝔾ₐ`).

Over a characteristic-zero field every additive 2-cocycle is a coboundary, with no symmetry
assumption: the cocycle identity at `XⁱY⁰Z⁰` and `X⁰Y⁰Zᵏ` kills the coefficients of `Yⁱ` and `Zᵏ`,
and the identity at `XYʲZᵏ` expresses every mixed coefficient through those of `YZᵐ`. The constant
coefficient of a primitive is minus the constant term of the cocycle, and its linear coefficient is
arbitrary, since `u = X` is additive. Thus `a ↦ addCoboundaryCoeff a` has kernel exactly the
sequences supported in degree one, and every cocycle has a primitive with `a₁ = 0`.

The `p`-adic size of such primitives, which have bounded denominators, is in
`TauCeti.RingTheory.FormalGroup.AddCocycle.Padic`.

## Main results

* `TauCeti.isAddCocycleCoeff_addCoboundaryCoeff`: every coboundary is a cocycle.
* `TauCeti.addCoboundaryCoeff_eq_zero_iff`: in a torsion-free group, `addCoboundaryCoeff a = 0`
  exactly when `a k = 0` for all `k ≠ 1`.
* `TauCeti.IsAddCocycleCoeff.exists_addCoboundaryCoeff_eq`: over a characteristic-zero division
  ring, every cocycle `b` is the coboundary of some `a` with `a 0 = -b (0, 0)` and `a 1 = 0`.
* `TauCeti.isAddCocycleCoeff_iff_exists_addCoboundaryCoeff_eq`: cocycles are exactly coboundaries.

## References

* P. Colmez and W. Nizioł, *On the cohomology of p-adic analytic spaces, II: The
  C_st-conjecture* (2025), Lemma 4.13 and its proof.
* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955),
  for additive 2-cocycles of polynomials.
-/

public section

namespace TauCeti

section Monoid

variable {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]

/-- The coefficient family `b`, with `b (i, j)` the coefficient of `YⁱZʲ` in a two-variable
series `f(Y, Z)`, satisfies the **additive 2-cocycle identity**
`f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`: comparing coefficients of `XⁱYʲZᵏ`,
`[k = 0] b_{i,j} + (i + j).choose i • b_{i+j,k} = (j + k).choose j • b_{i,j+k} + [i = 0] b_{j,k}`.
Only `ℕ`-multiples enter, so the identity makes sense in an additive commutative monoid. -/
def IsAddCocycleCoeff (b : ℕ × ℕ → M) : Prop :=
  ∀ i j k : ℕ, (if k = 0 then b (i, j) else 0) + (i + j).choose i • b (i + j, k) =
    (j + k).choose j • b (i, j + k) + if i = 0 then b (j, k) else 0

/-- Unfolding `TauCeti.IsAddCocycleCoeff`. -/
theorem isAddCocycleCoeff_iff {b : ℕ × ℕ → M} :
    IsAddCocycleCoeff b ↔ ∀ i j k : ℕ,
      (if k = 0 then b (i, j) else 0) + (i + j).choose i • b (i + j, k) =
        (j + k).choose j • b (i, j + k) + if i = 0 then b (j, k) else 0 :=
  Iff.rfl

namespace IsAddCocycleCoeff

variable {b : ℕ × ℕ → M}

/-- The zero family is an additive 2-cocycle. -/
theorem zero : IsAddCocycleCoeff (0 : ℕ × ℕ → M) := by
  intro i j k
  simp

/-- The sum of two additive 2-cocycles is an additive 2-cocycle. -/
theorem add {b' : ℕ × ℕ → M} (h : IsAddCocycleCoeff b) (h' : IsAddCocycleCoeff b') :
    IsAddCocycleCoeff (b + b') := by
  intro i j k
  convert congrArg₂ (· + ·) (h i j k) (h' i j k) using 1 <;>
    split_ifs <;> simp only [Pi.add_apply, nsmul_add, add_zero, zero_add] <;> abel

/-- Additive 2-cocycles are preserved by additive monoid homomorphisms of the coefficients. -/
theorem map (h : IsAddCocycleCoeff b) (φ : M →+ N) : IsAddCocycleCoeff fun ij => φ (b ij) := by
  intro i j k
  have := congrArg φ (h i j k)
  simpa only [map_add, map_nsmul, apply_ite φ, map_zero] using this

/-- A scalar multiple of an additive 2-cocycle is an additive 2-cocycle. -/
theorem smul {S : Type*} [DistribSMul S M] (c : S) (h : IsAddCocycleCoeff b) :
    IsAddCocycleCoeff (c • b) :=
  h.map (DistribSMul.toAddMonoidHom M c)

/-- The negative of an additive 2-cocycle is an additive 2-cocycle, in an additive group. -/
theorem neg {M : Type*} [AddCommGroup M] {b : ℕ × ℕ → M} (h : IsAddCocycleCoeff b) :
    IsAddCocycleCoeff (-b) :=
  h.map (-AddMonoidHom.id M)

/-- The difference of two additive 2-cocycles is an additive 2-cocycle, in an additive group. -/
theorem sub {M : Type*} [AddCommGroup M] {b b' : ℕ × ℕ → M} (h : IsAddCocycleCoeff b)
    (h' : IsAddCocycleCoeff b') : IsAddCocycleCoeff (b - b') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/-- The coefficient of `Yⁱ` in an additive 2-cocycle vanishes for `i ≠ 0`, in an additive group. -/
theorem apply_zero_right {M : Type*} [AddCommGroup M] {b : ℕ × ℕ → M}
    (h : IsAddCocycleCoeff b) {i : ℕ} (hi : i ≠ 0) : b (i, 0) = 0 := by
  simpa [hi] using h i 0 0

/-- The coefficient of `Zᵏ` in an additive 2-cocycle vanishes for `k ≠ 0`, in an additive group. -/
theorem apply_zero_left {M : Type*} [AddCommGroup M] {b : ℕ × ℕ → M}
    (h : IsAddCocycleCoeff b) {k : ℕ} (hk : k ≠ 0) : b (0, k) = 0 := by
  simpa [hk] using h 0 0 k

end IsAddCocycleCoeff

end Monoid

end TauCeti

namespace MvPolynomial

open TauCeti

variable {R : Type*} [CommRing R] {f : MvPolynomial (Fin 2) R}

/-- A polynomial is an additive 2-cocycle exactly when its coefficients satisfy the coefficient
form of the cocycle identity. -/
theorem isAddCocycle₂_iff_isAddCocycleCoeff :
    f.IsAddCocycle₂ ↔
      IsAddCocycleCoeff fun ij : ℕ × ℕ =>
        f.coeff (Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2) := by
  refine ⟨fun hf i j k => by simpa only [nsmul_eq_mul] using hf.coeff_eq i j k, fun h => ?_⟩
  -- Compare the coefficients of `X₀^(d 0) X₁^(d 1) X₂^(d 2)`.
  rw [isAddCocycle₂_iff]
  ext d
  simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_aeval_X_zero_X_one,
    coeff_aeval_X_add_X_X, coeff_aeval_X_X_add_X, coeff_aeval_X_one_X_two, nsmul_eq_mul] using
    h (d 0) (d 1) (d 2)

/-- The coefficients of a polynomial additive 2-cocycle satisfy the coefficient form of the
cocycle identity. -/
theorem IsAddCocycle₂.isAddCocycleCoeff (hf : f.IsAddCocycle₂) :
    IsAddCocycleCoeff fun ij : ℕ × ℕ =>
      f.coeff (Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2) :=
  isAddCocycle₂_iff_isAddCocycleCoeff.1 hf

end MvPolynomial

namespace TauCeti

section Group

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The coefficients of the additivity defect `u(Y + Z) - u(Y) - u(Z)` of a one-variable series
`u(X) = ∑ a_k Xᵏ`: the coefficient of `YⁱZʲ` is
`(i + j).choose i • a_{i+j} - [j = 0] a_i - [i = 0] a_j`. Up to sign it is the coboundary of `u`
in the cochain complex of the additive formal group with trivial coefficients. It is additive in
`u`. -/
def addCoboundaryCoeff : (ℕ → M) →+ ℕ × ℕ → M where
  toFun a ij := (ij.1 + ij.2).choose ij.1 • a (ij.1 + ij.2) - (if ij.2 = 0 then a ij.1 else 0) -
    if ij.1 = 0 then a ij.2 else 0
  map_zero' := by
    ext ij
    simp
  map_add' a a' := by
    ext ij
    simp only [Pi.add_apply, nsmul_add]
    split_ifs <;> abel

/-- Unfolding `TauCeti.addCoboundaryCoeff`. -/
theorem addCoboundaryCoeff_apply (a : ℕ → M) (i j : ℕ) :
    addCoboundaryCoeff a (i, j) = (i + j).choose i • a (i + j) - (if j = 0 then a i else 0) -
      if i = 0 then a j else 0 :=
  (rfl)

/-- The constant coefficient of `u(Y + Z) - u(Y) - u(Z)` is `-u(0)`. -/
@[simp]
theorem addCoboundaryCoeff_apply_zero_zero (a : ℕ → M) :
    addCoboundaryCoeff a (0, 0) = -a 0 := by
  simp [addCoboundaryCoeff_apply]

/-- The coefficient of `Yⁱ`, `i ≠ 0`, in `u(Y + Z) - u(Y) - u(Z)` vanishes. -/
@[simp]
theorem addCoboundaryCoeff_apply_zero_right (a : ℕ → M) {i : ℕ} (hi : i ≠ 0) :
    addCoboundaryCoeff a (i, 0) = 0 := by
  simp [addCoboundaryCoeff_apply, hi]

/-- The coefficient of `Zʲ`, `j ≠ 0`, in `u(Y + Z) - u(Y) - u(Z)` vanishes. -/
@[simp]
theorem addCoboundaryCoeff_apply_zero_left (a : ℕ → M) {j : ℕ} (hj : j ≠ 0) :
    addCoboundaryCoeff a (0, j) = 0 := by
  simp [addCoboundaryCoeff_apply, hj]

/-- The coefficient of a mixed monomial `YⁱZʲ`, `i, j ≠ 0`, in `u(Y + Z) - u(Y) - u(Z)` is
`(i + j).choose i • a_{i+j}`. -/
@[simp]
theorem addCoboundaryCoeff_apply_of_ne_zero (a : ℕ → M) {i j : ℕ} (hi : i ≠ 0)
    (hj : j ≠ 0) :
    addCoboundaryCoeff a (i, j) = (i + j).choose i • a (i + j) := by
  simp [addCoboundaryCoeff_apply, hi, hj]

/-- `addCoboundaryCoeff` commutes with additive group homomorphisms of the coefficients. -/
theorem addCoboundaryCoeff_comp (a : ℕ → M) (φ : M →+ N) :
    addCoboundaryCoeff (fun k => φ (a k)) = fun ij => φ (addCoboundaryCoeff a ij) := by
  ext ⟨i, j⟩
  simp only [addCoboundaryCoeff_apply, map_sub, map_nsmul, apply_ite φ, map_zero]

end Group

end TauCeti

namespace FormalGroup

open TauCeti

/-- The coefficients of the homomorphism defect `g(X₀ + X₁) - g(X₀) - g(X₁)` of a power series `g`
from the additive formal group law to itself are given by `TauCeti.addCoboundaryCoeff`. -/
theorem coeff_homDefect_𝔾ₐ_𝔾ₐ {R : Type*} [CommRing R] (g : PowerSeries R) (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        ((𝔾ₐ : FormalGroup R).homDefect 𝔾ₐ g) =
      addCoboundaryCoeff (fun k => PowerSeries.coeff k g) (i, j) := by
  classical
  rw [homDefect_𝔾ₐ, 𝔾ₐ_toPowerSeries, map_sub, map_sub, PowerSeries.coeff_subst_X_zero_add_X_one,
    PowerSeries.coeff_subst_single, PowerSeries.coeff_subst_single, addCoboundaryCoeff_apply]
  simp [nsmul_eq_mul]

end FormalGroup

namespace TauCeti

section Group

variable {M : Type*} [AddCommGroup M]

/-- **Every coboundary is a cocycle**: `u(Y + Z) - u(Y) - u(Z)` satisfies the additive 2-cocycle
identity. -/
@[simp]
theorem isAddCocycleCoeff_addCoboundaryCoeff (a : ℕ → M) :
    IsAddCocycleCoeff (addCoboundaryCoeff a) := by
  intro i j k
  -- The terms in `a_{i+j+k}` agree by the binomial identity `hc` (choose `i + j`, then `i`, or
  -- `i`, then `j`); the remaining terms, in `a_i`, `a_j`, `a_k`, `a_{i+j}` and `a_{j+k}`, cancel
  -- case by case.
  have hc : (i + j + k).choose (i + j) * (i + j).choose i =
      (i + j + k).choose i * (j + k).choose j := by
    rw [Nat.choose_mul (Nat.le_add_right i j)]
    congr 2 <;> omega
  have key : (i + j).choose i • (i + j + k).choose (i + j) • a (i + j + k) =
      (j + k).choose j • (i + (j + k)).choose i • a (i + (j + k)) := by
    rw [← add_assoc, smul_smul, smul_smul, mul_comm, hc, mul_comm]
  simp only [addCoboundaryCoeff_apply, nsmul_sub, smul_ite, nsmul_zero]
  rcases Nat.eq_zero_or_pos i with rfl | hi <;> rcases Nat.eq_zero_or_pos j with rfl | hj <;>
    rcases Nat.eq_zero_or_pos k with rfl | hk <;>
    simp_all [Nat.pos_iff_ne_zero, Nat.add_eq_zero_iff]

/-- In a torsion-free group, `u(Y + Z) - u(Y) - u(Z) = 0` exactly when `u` is linear: all
coefficients of `u` other than the linear one vanish. -/
theorem addCoboundaryCoeff_eq_zero_iff [HasUniqueDiv M] {a : ℕ → M} :
    addCoboundaryCoeff a = 0 ↔ ∀ k, k ≠ 1 → a k = 0 := by
  refine ⟨fun h k hk => ?_, fun h => ?_⟩
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 0 := by omega
      simpa using congrFun h (0, 0)
    · have h' := congrFun h (1, k - 1)
      rw [addCoboundaryCoeff_apply_of_ne_zero a one_ne_zero (by omega),
        Nat.add_sub_cancel' (by omega), Nat.choose_one_right, Pi.zero_apply, ← nsmul_zero k] at h'
      exact (nsmul_right_inj (by omega)).1 h'
  · ext ⟨i, j⟩
    rw [Pi.zero_apply, addCoboundaryCoeff_apply]
    rcases Nat.eq_zero_or_pos i with rfl | hi <;> rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [h 0 zero_ne_one]
    · simp [hj.ne']
    · simp [hi.ne']
    · simp [hi.ne', hj.ne', h (i + j) (by omega)]

/-- In a torsion-free group, two series have the same additivity defect exactly when they agree
outside the linear coefficient. -/
theorem addCoboundaryCoeff_eq_addCoboundaryCoeff_iff [HasUniqueDiv M] {a a' : ℕ → M} :
    addCoboundaryCoeff a = addCoboundaryCoeff a' ↔ ∀ k, k ≠ 1 → a k = a' k := by
  rw [← sub_eq_zero, ← map_sub, addCoboundaryCoeff_eq_zero_iff]
  simp only [Pi.sub_apply, sub_eq_zero]

namespace IsAddCocycleCoeff

variable {b : ℕ × ℕ → M}

/-- The cocycle identity at `XYʲZᵏ`: `(j + 1) • b_{j+1,k} = (j + k).choose j • b_{1,j+k}` for
`k ≠ 0`. -/
private theorem succ_nsmul_apply (h : IsAddCocycleCoeff b) (j : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (j + 1) • b (j + 1, k) = (j + k).choose j • b (1, j + k) := by
  simpa [hk, add_comm 1 j] using h 1 j k

/-- **Additive 2-cocycles are coboundaries in characteristic zero.** If `b` satisfies the
additive 2-cocycle identity, with coefficients in a module over a characteristic-zero division
ring `𝕜`, then `b` is the coefficient family of `u(Y + Z) - u(Y) - u(Z)` for a series `u` with
constant coefficient `-b (0, 0)` and linear coefficient `0`. No symmetry of `b` is assumed. -/
theorem exists_addCoboundaryCoeff_eq (𝕜 : Type*) [DivisionRing 𝕜] [CharZero 𝕜] [Module 𝕜 M]
    (h : IsAddCocycleCoeff b) :
    ∃ a : ℕ → M, addCoboundaryCoeff a = b ∧ a 0 = -b (0, 0) ∧ a 1 = 0 := by
  classical
  -- `a_0 = -b_{0,0}`, `a_1 = 0` and `a_m = m⁻¹ • b_{1,m-1}` for `m ≥ 2`.
  let a : ℕ → M := fun m => if m = 0 then -b (0, 0) else if m = 1 then 0 else
    ((m : 𝕜)⁻¹ • b (1, m - 1))
  refine ⟨a, ?_, by simp [a], by simp [a]⟩
  ext ⟨i, j⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [a]
    · rw [addCoboundaryCoeff_apply_zero_left a hj.ne', h.apply_zero_left hj.ne']
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [addCoboundaryCoeff_apply_zero_right a hi.ne', h.apply_zero_right hi.ne']
  -- For `i + 1, j ≥ 1`, the identity at `XYⁱZʲ` gives
  -- `b_{i+1,j} = (i + 1)⁻¹ • C(i+j, i) • b_{1,i+j}`, and
  -- `(i + 1) • C(i+1+j, i+1) = C(i+j, i) • (i + 1 + j)`.
  rw [addCoboundaryCoeff_apply_of_ne_zero a hi.ne' hj.ne']
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [zero_add]
  have hm : i + 1 + j ≠ 0 := by omega
  have hm1 : i + 1 + j ≠ 1 := by omega
  have hb : b (i + 1, j) = ((i + 1 : ℕ) : 𝕜)⁻¹ • (((i + j).choose i : ℕ) : 𝕜) • b (1, i + j) := by
    rw [eq_inv_smul_iff₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero i))]
    simpa only [Nat.cast_smul_eq_nsmul] using h.succ_nsmul_apply i hj.ne'
  have hchoose : (i + 1) * (i + 1 + j).choose (i + 1) = (i + j).choose i * (i + 1 + j) := by
    rw [mul_comm, show i + 1 + j = i + j + 1 by omega, ← Nat.add_one_mul_choose_eq, mul_comm]
  simp only [a, ite_eq_right hm, ite_eq_right hm1, show i + 1 + j - 1 = i + j by omega]
  rw [hb, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, smul_smul]
  congr 1
  -- `𝕜` need not be commutative, so prove the scalar identity in `ℚ` and cast it to `𝕜`.
  have key : (((i + 1 + j).choose (i + 1) : ℕ) : ℚ) * ((i + 1 + j : ℕ) : ℚ)⁻¹ =
      ((i + 1 : ℕ) : ℚ)⁻¹ * ((i + j).choose i : ℕ) := by
    -- Clearing the denominators leaves the cast of `hchoose`.
    rw [mul_inv_eq_iff_eq_mul₀ (by positivity), mul_assoc,
      eq_inv_mul_iff_mul_eq₀ (by positivity)]
    exact_mod_cast hchoose
  simpa only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast] using congrArg (Rat.cast : ℚ → 𝕜) key

end IsAddCocycleCoeff

/-- **Additive 2-cocycles are exactly coboundaries in characteristic zero.** With coefficients in
a module over a characteristic-zero division ring, a coefficient family satisfies the additive
2-cocycle identity exactly when it is the family of `u(Y + Z) - u(Y) - u(Z)` for some series `u`. -/
theorem isAddCocycleCoeff_iff_exists_addCoboundaryCoeff_eq (𝕜 : Type*) [DivisionRing 𝕜]
    [CharZero 𝕜] [Module 𝕜 M] {b : ℕ × ℕ → M} :
    IsAddCocycleCoeff b ↔ ∃ a : ℕ → M, addCoboundaryCoeff a = b := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := h.exists_addCoboundaryCoeff_eq 𝕜
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact isAddCocycleCoeff_addCoboundaryCoeff a

end Group

end TauCeti
