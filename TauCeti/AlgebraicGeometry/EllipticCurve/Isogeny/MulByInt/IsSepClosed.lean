/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.DivisionPolynomialSeparable
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.TorsionRank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.TorsionSurjective
-- Proof-only: the `y`-coordinate of a solution with rational `x` is rational.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsSepClosed
-- Proof-only: the abscissa of a torsion point is integral over the base field.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
-- Proof-only: an even index with nonzero cast keeps `2` nonzero.
import TauCeti.Data.Int.CastNeZero
-- Proof-only: an integral element whose minimal polynomial splits lies in the base field.
import Mathlib.RingTheory.Adjoin.Field

/-!
# Torsion over a separably closed field

An `n`-torsion point of `W` with coordinates in an extension of a separably closed `F` already has
them in `F`, provided `n` is invertible in `F`. Its abscissa is integral over `F` with separable
minimal polynomial, and the ordinate then solves a quadratic whose other root is its negative.

Invertibility of `n` is what the separability rests on, and it cannot be dropped. Over the
separable closure `K` of `𝔽₂(t)` the curve `y² + xy = x³ + t` has discriminant `t`, so it is
elliptic, and its nonzero `2`-torsion point is `(0, √t)`: the geometric `2`-torsion is
nontrivial while the `2`-torsion over `K` itself is not.

Rationality of the geometric torsion is the hypothesis the counts of `MulByInt/` take of the base
field, so each of them holds here, and the algebraically closed hypothesis they carried weakens to
a separably closed one. The exception is the fibre count `Isogeny.card_zsmul_fiber`: it is what the
separability of the division polynomials is counted against, and that separability is what the
rationality below rests on, so it stays where it is.

## Main results

* `WeierstrassCurve.mem_range_x_of_zsmul_eq_zero_of_isSepClosed` and
  `WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed`: an `n`-torsion point
  over an extension of a separably closed field, with `n` invertible, is already rational.
* `TauCeti.Isogeny.card_ker_mulByIntIsogeny` and `WeierstrassCurve.Affine.natCard_torsionBy`:
  `#E[n] = n ²`, in the kernel and the torsion-subgroup forms.
* `TauCeti.Isogeny.card_ker_mulByPrimeIsogeny`,
  `TauCeti.Isogeny.finrank_ker_mulByPrimeIsogeny` and
  `TauCeti.Isogeny.nonempty_linearEquiv_ker_mulByPrimeIsogeny`: `E[ℓ] ≅ (ZMod ℓ) ²` at a prime.
* `WeierstrassCurve.Affine.zsmulTorsionSqHom_surjective` and
  `WeierstrassCurve.Affine.exists_zsmul_eq_of_zsmul_eq_zero`: `[n]` carries `E[n ²]` onto `E[n]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] [IsSepClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
  {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- **The abscissa of a torsion point is rational** over a separably closed field in which the
index is invertible: it is integral over the base field and its minimal polynomial is separable,
so a separably closed field already contains it. -/
theorem mem_range_x_of_zsmul_eq_zero_of_isSepClosed {n : ℤ} (hchar : (n : F) ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    x ∈ Set.range (algebraMap F Ω) := by
  have hn : n ≠ 0 := by rintro rfl; exact hchar (by simp)
  refine (isIntegral_x_of_zsmul_eq_zero W hn hns htors).mem_range_algebraMap_of_minpoly_splits ?_
  simpa using IsSepClosed.splits_of_separable _
    (separable_minpoly_of_zsmul_eq_zero W hchar hns htors)

variable [DecidableEq F] [DecidableEq Ω]

omit [IsSepClosed F] [W.IsElliptic] [DecidableEq F] in
/-- A torsion point of invertible index satisfies the side condition that makes its ordinate
rational: in characteristic `2` it would otherwise be its own negative, hence killed by `2` as
well as by an odd index, hence zero. -/
private theorem two_ne_zero_or_add_ne_zero_of_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0)
    {x y : Ω} (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (h : n • Affine.Point.some x y hns = 0) {x₀ : F} (hx₀ : algebraMap F Ω x₀ = x) :
    (2 : F) ≠ 0 ∨ W.a₁ * x₀ + W.a₃ ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h2, hb⟩ := hcon
  have hzero : (2 : Ω) = 0 := by rw [← map_ofNat (algebraMap F Ω) 2, h2, map_zero]
  have hab : (W.baseChange Ω).a₁ * x + (W.baseChange Ω).a₃ = 0 := by
    rw [← hx₀]
    simp only [baseChange, map_a₁, map_a₃]
    rw [← map_mul, ← map_add, hb, map_zero]
  -- The point is its own negative, so it is killed by `2`.
  have hself : -Affine.Point.some x y hns = Affine.Point.some x y hns := by
    rw [Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq, Affine.negY, true_and]
    linear_combination -hab - y * hzero
  have htwo : (2 : ℤ) • Affine.Point.some x y hns = 0 := by
    rw [two_zsmul]
    calc Affine.Point.some x y hns + Affine.Point.some x y hns
        = Affine.Point.some x y hns + -Affine.Point.some x y hns := by rw [hself]
      _ = 0 := add_neg_cancel _
  -- An invertible index in characteristic `2` is odd, so the point itself vanishes.
  obtain ⟨k, hk⟩ : Odd n := Int.not_even_iff_odd.mp fun heven ↦
    Int.two_ne_zero_of_even_of_cast_ne_zero heven hchar (by exact_mod_cast h2)
  refine Affine.Point.some_ne_zero hns ?_
  rwa [hk, add_smul, one_smul, mul_comm (2 : ℤ) k, mul_smul, htwo, smul_zero, zero_add] at h

/-- **A torsion point over an extension of a separably closed field is already rational** when its
index is invertible there: both of its coordinates are separable over the base field. -/
theorem mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed {n : ℤ} (hchar : (n : F) ≠ 0)
    {P : (W.baseChange Ω).toAffine.Point} (h : n • P = 0) :
    P ∈ Set.range (Affine.Point.baseChange (W' := W) F Ω) := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact ⟨0, Affine.Point.map_zero _⟩
  · have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
      have h' := congrArg (Jacobian.Point.toAffineAddEquiv (W.baseChange Ω)).symm h
      rw [map_zsmul, map_zero] at h'
      simpa using h'
    obtain ⟨x₀, hx₀⟩ := W.mem_range_x_of_zsmul_eq_zero_of_isSepClosed hchar hns hJac
    obtain ⟨y₀, hy₀⟩ := W.mem_range_y_of_equation_of_mem_range_x_of_isSepClosed hns.left hx₀
      (W.two_ne_zero_or_add_ne_zero_of_zsmul_eq_zero hchar hns h hx₀)
    subst hx₀
    subst hy₀
    refine ⟨Affine.Point.some x₀ y₀ ((W.toAffine.baseChange_nonsingular
      (f := Algebra.ofId F Ω) (FaithfulSMul.algebraMap_injective F Ω) x₀ y₀).mp hns), ?_⟩
    rw [Affine.Point.map_some]
    simp only [Algebra.ofId_apply]

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

open scoped Classical in
/-- **`#ker [n] = n ²`** over a separably closed field, for `n` invertible there: the geometric
`n`-torsion is then rational, which is the only thing the count asks of the base field. -/
theorem card_ker_mulByIntIsogeny {n : ℤ} {hn : psiFunctionField W n ≠ 0} (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2 :=
  card_ker_mulByIntIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed hchar hP) hchar

-- Not `@[simp]`: `mulByPrimeIsogeny` is an `abbrev`, so `simp` sees through it to
-- `card_ker_mulByIntIsogeny` and `simpNF` rejects the pair as duplicates.
/-- **`#E[ℓ] = ℓ ²`**, for a prime `ℓ` invertible in a separably closed base field. -/
theorem card_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime] (hchar : (l : F) ≠ 0) :
    Nat.card (mulByPrimeIsogeny W l).ker = l ^ 2 := by
  rw [card_ker_mulByIntIsogeny W (by simpa using hchar), Int.natAbs_natCast]

open scoped Classical in
/-- **`E[ℓ]` is two-dimensional over `ZMod ℓ`** for a prime `ℓ` invertible in a separably closed
base field, where the geometric `ℓ`-torsion is rational. -/
@[simp]
theorem finrank_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime] (hchar : (l : F) ≠ 0) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 :=
  finrank_ker_mulByPrimeIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by simpa using hchar) hP) hchar

open scoped Classical in
/-- **`E[ℓ] ≅ (ZMod ℓ)²`** for a prime `ℓ` invertible in a separably closed base field. -/
theorem nonempty_linearEquiv_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime]
    (hchar : (l : F) ≠ 0) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) :=
  nonempty_linearEquiv_ker_mulByPrimeIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by simpa using hchar) hP) hchar

end TauCeti.Isogeny

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : Affine F) [W.IsElliptic]

open scoped Classical in
/-- **`#E[n] = n ²`** over a separably closed field in which `n` is invertible, read on Mathlib's
intrinsic torsion subgroup. -/
theorem natCard_torsionBy {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) = n.natAbs ^ 2 :=
  natCard_torsionBy_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed hchar hP) hchar

open scoped Classical in
/-- **`[n]` carries `E[n ²]` onto `E[n]`** over a separably closed field in which `n` is
invertible. -/
theorem zsmulTorsionSqHom_surjective {n : ℤ} (hchar : (n : F) ≠ 0) :
    Function.Surjective (zsmulTorsionSqHom W n) :=
  zsmulTorsionSqHom_surjective_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by push_cast; exact pow_ne_zero 2 hchar) hP) hchar

open scoped Classical in
/-- **Every `n`-torsion point is `n` times an `n ²`-torsion point**, over a separably closed field
in which `n` is invertible. -/
theorem exists_zsmul_eq_of_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0)
    {T : (W⁄F).toAffine.Point} (hT : n • T = 0) :
    ∃ P : (W⁄F).toAffine.Point, n • P = T ∧ (n ^ 2 : ℤ) • P = 0 :=
  exists_zsmul_eq_of_zsmul_eq_zero_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by push_cast; exact pow_ne_zero 2 hchar) hP) hchar hT

end WeierstrassCurve.Affine

end
