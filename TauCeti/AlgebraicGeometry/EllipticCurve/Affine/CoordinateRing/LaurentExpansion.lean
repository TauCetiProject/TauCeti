/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.Basis
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
-- Body-only: evaluation of the coordinate ring at a solution of the Weierstrass equation.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# The Laurent expansion of the coordinate ring at the point at infinity

Let `W` be a Weierstrass curve over a commutative ring `R`, with affine coordinate ring
`R[W] = R[X, Y] ⧸ (W(X, Y))` and coordinate functions `x` and `y`. Near the point at infinity
`[0 : 1 : 0]`, the parameter is `z = -x / y`, and `w = -1 / y` is the power series
`w(z) = z³ u(z)` of `WeierstrassCurve.formalW`, with `u(0) = 1`. Inverting these relations gives
the Laurent series

`x = z / w(z) = z⁻² u(z)⁻¹` and `y = -1 / w(z) = -z⁻³ u(z)⁻¹`

in `R⸨X⸩`, the variable of the Laurent series ring standing for `z`. They satisfy the Weierstrass
equation of `W`, so they define an `R`-algebra homomorphism `R[W] →ₐ[R] R⸨X⸩`, the Laurent
expansion of a function on the affine curve at the point at infinity.

The order of the Laurent expansion is the order of the pole at infinity. The coordinate ring is
free over `R` on the monomials `xⁱyʲ` with `j ≤ 1`
(`WeierstrassCurve.Affine.CoordinateRing.basisMonomials`), and the expansion of `xⁱyʲ` is
`(-1)ʲ z^(-(2i + 3j))` times a power series with constant coefficient `1`. The weights `2i + 3j`
of distinct monomials are distinct, so the expansion of an element vanishes below `z^(-n)` exactly
when the element is an `R`-linear combination of the monomials of weight at most `n`. For
`n = 0, 2, 3, 4, 5, 6` these are the bases `1`; `1, x`; `1, x, y`; `1, x, y, x²`;
`1, x, y, x², xy`; `1, x, y, x², xy, x³` of the functions with a pole of order at most `n` at
infinity. No hypothesis on `W` or on `R` is needed: the leading coefficients are `±1`, so the
argument does not use that `R` is reduced. Over a field, the bounds for `n = 2, 3` are also proved
with the valuation at the place at infinity, in
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/InfinityPlace/PoleOrder.lean`; over a
general ring there is no such valuation, and the Laurent expansion takes its place.

## Main definitions

* `WeierstrassCurve.laurentExpansion`: the Laurent expansion `R[W] →ₐ[R] R⸨X⸩` at the point at
  infinity.

## Main results

* `WeierstrassCurve.laurentExpansion_of_X` and `WeierstrassCurve.laurentExpansion_root`: the
  expansions of `x` and `y` are `z⁻² u(z)⁻¹` and `-z⁻³ u(z)⁻¹`.
* `WeierstrassCurve.laurentExpansion_root_mul_formalW` and
  `WeierstrassCurve.laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root`: the expansion of
  `y` is `-1 / w(z)`, and that of `x` is `-z` times that of `y`.
* `WeierstrassCurve.mem_span_basisMonomials_iff_forall_coeff_laurentExpansion_eq_zero`: the
  expansion of `g` vanishes below `z^(-n)` exactly when `g` is a linear combination of the
  monomials `xⁱyʲ` with `2i + 3j ≤ n`.
* `WeierstrassCurve.laurentExpansion_injective`: the Laurent expansion is injective.
* `WeierstrassCurve.exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_two` and
  `WeierstrassCurve.exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_three`: a function with
  a pole of order at most `2` (resp. `3`) at infinity is `αx + β` (resp. `γy + δx + β`), where
  `α` (resp. `-γ`) is the coefficient of `z⁻²` (resp. `z⁻³`) of its expansion.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 (the expansions of
  `x` and `y` in the parameter `z`) and II.5.8 (the bases of the spaces `L(n(O))`).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
-/

public section

open Polynomial LaurentSeries HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

-- The inverse `u(z)⁻¹` of `u(z) = w(z) / z³` is a two-sided inverse, with constant coefficient
-- `1`.
private theorem formalU_mul_invOfUnit : formalU W * (formalU W).invOfUnit 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_formalU, Units.val_one])

private theorem constantCoeff_invOfUnit_formalU :
    PowerSeries.constantCoeff ((formalU W).invOfUnit 1) = 1 := by
  rw [PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]

-- In `R⸨X⸩`, the expansion `w(z)` is `z³ u(z)`, and `z⁻³ u(z)⁻¹` is its inverse.
private theorem formalW_mul_single_mul_invOfUnit_formalU :
    ofPowerSeries ℤ R (formalW W) *
      (single (-3) 1 * ofPowerSeries ℤ R ((formalU W).invOfUnit 1)) = 1 := by
  rw [formalW_eq_X_pow_mul_formalU, map_mul, map_pow, ofPowerSeries_X, single_pow,
    mul_mul_mul_comm, single_mul_single, ← map_mul, formalU_mul_invOfUnit]
  simp

-- The Laurent series `x = z⁻² u(z)⁻¹` and `y = -z⁻³ u(z)⁻¹` satisfy the Weierstrass equation.
private theorem equation_laurent :
    (W.toAffine⁄R⸨X⸩).toAffine.Equation
      (single (-2) 1 * ofPowerSeries ℤ R ((formalU W).invOfUnit 1))
      (single (-3) (-1) * ofPowerSeries ℤ R ((formalU W).invOfUnit 1)) := by
  set ω : R⸨X⸩ := ofPowerSeries ℤ R (formalW W)
  set ι : R⸨X⸩ := single (-3) 1 * ofPowerSeries ℤ R ((formalU W).invOfUnit 1)
  set T : R⸨X⸩ := single 1 1
  have hι : ω * ι = 1 := W.formalW_mul_single_mul_invOfUnit_formalU
  have hx : single (-2) 1 * ofPowerSeries ℤ R ((formalU W).invOfUnit 1) = T * ι := by
    rw [← mul_assoc, single_mul_single]
    norm_num
  have hy : single (-3) (-1) * ofPowerSeries ℤ R ((formalU W).invOfUnit 1) = -ι := by
    rw [single_neg, neg_mul]
  -- the `w`-equation, read in `R⸨X⸩`
  have hw : ω = wEquationRHS W T ω := by
    have := congrArg (ofPowerSeries ℤ R) (formalW_wEquation W)
    rw [wEquationRHS_powerSeries] at this
    simpa only [wEquationRHS_def, map_add, map_mul, map_pow, ofPowerSeries_X,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] using this
  rw [hx, hy, Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  rw [wEquationRHS_def] at hw
  -- clear the denominators `ι = 1 / ω` with `ω * ι = 1`
  linear_combination ι ^ 3 * hw - (ι ^ 2 - algebraMap R R⸨X⸩ W.a₁ * T * ι ^ 2 -
    algebraMap R R⸨X⸩ W.a₂ * T ^ 2 * ι ^ 2 - algebraMap R R⸨X⸩ W.a₃ * ι * (1 + ω * ι) -
    algebraMap R R⸨X⸩ W.a₄ * T * ι * (1 + ω * ι) -
    algebraMap R R⸨X⸩ W.a₆ * (1 + ω * ι + (ω * ι) ^ 2)) * hι

/-- The **Laurent expansion at the point at infinity** of a function on the affine Weierstrass
curve: the `R`-algebra homomorphism `R[W] →ₐ[R] R⸨X⸩` sending `x` to `z⁻² u(z)⁻¹ = z / w(z)` and
`y` to `-z⁻³ u(z)⁻¹ = -1 / w(z)`, where `z` is the variable of the Laurent series ring and
`w(z) = z³ u(z)` is the `w`-expansion `WeierstrassCurve.formalW` of `W`. -/
noncomputable def laurentExpansion : W.toAffine.CoordinateRing →ₐ[R] R⸨X⸩ :=
  Affine.CoordinateRing.evalAlgHom W.equation_laurent

/-- The Laurent expansion of the coordinate function `x` is `z⁻² u(z)⁻¹`. -/
@[simp]
theorem laurentExpansion_of_X :
    W.laurentExpansion (AdjoinRoot.of W.toAffine.polynomial X) =
      single (-2) 1 * ofPowerSeries ℤ R ((formalU W).invOfUnit 1) :=
  Affine.CoordinateRing.evalAlgHom_of_X _

/-- The Laurent expansion of the coordinate function `y` is `-z⁻³ u(z)⁻¹`. -/
@[simp]
theorem laurentExpansion_root :
    W.laurentExpansion (AdjoinRoot.root W.toAffine.polynomial) =
      single (-3) (-1) * ofPowerSeries ℤ R ((formalU W).invOfUnit 1) :=
  Affine.CoordinateRing.evalAlgHom_root _

/-- The Laurent expansion of the coordinate function `y` is `-1 / w(z)`: its product with the
`w`-expansion is `-1`. -/
theorem laurentExpansion_root_mul_formalW :
    W.laurentExpansion (AdjoinRoot.root W.toAffine.polynomial) *
      ofPowerSeries ℤ R (formalW W) = -1 := by
  rw [laurentExpansion_root, single_neg, neg_mul, neg_mul, mul_comm,
    formalW_mul_single_mul_invOfUnit_formalU]

/-- The Laurent expansion of the coordinate function `x` is `-z` times that of `y`, that is,
`x = -z y`. -/
theorem laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root :
    W.laurentExpansion (AdjoinRoot.of W.toAffine.polynomial X) =
      -(ofPowerSeries ℤ R PowerSeries.X *
        W.laurentExpansion (AdjoinRoot.root W.toAffine.polynomial)) := by
  rw [laurentExpansion_of_X, laurentExpansion_root, ofPowerSeries_X, ← mul_assoc,
    single_mul_single, ← neg_mul, ← single_neg]
  norm_num

/-! ### The order of the pole at infinity -/

open Affine.CoordinateRing

/-- The weight `2i + 3j` of the monomial `xⁱyʲ`, the order of its pole at infinity. -/
private abbrev weight (p : ℕ × Fin 2) : ℕ := 2 * p.1 + 3 * (p.2 : ℕ)

-- Distinct monomials `xⁱyʲ` with `j ≤ 1` have distinct weights.
private theorem weight_injective : Function.Injective weight := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [weight] at h
  have hj : (j : ℕ) = j' := by omega
  have hi : i = i' := by omega
  rw [hi, Fin.ext hj]

-- The Laurent expansion of the monomial `xⁱyʲ` is `(-1)ʲ z^(-(2i + 3j)) u(z)^(-(i + j))`.
private theorem laurentExpansion_basisMonomials (p : ℕ × Fin 2) :
    W.laurentExpansion (Affine.CoordinateRing.basisMonomials W.toAffine p) =
      single (-(weight p : ℤ)) ((-1) ^ (p.2 : ℕ)) *
        ofPowerSeries ℤ R ((formalU W).invOfUnit 1 ^ (p.1 + p.2)) := by
  obtain ⟨i, j⟩ := p
  rw [basisMonomials_apply, map_mul, map_pow, map_pow, laurentExpansion_of_X,
    laurentExpansion_root, mul_pow, mul_pow, single_pow, single_pow, mul_mul_mul_comm,
    single_mul_single, ← map_pow, ← map_pow, ← map_mul, ← pow_add, one_pow, one_mul,
    show i • (-2 : ℤ) + (j : ℕ) • (-3 : ℤ) = -(weight (i, j) : ℤ) by
      push_cast [weight, nsmul_eq_mul]; ring]

-- The Laurent expansion of `xⁱyʲ` has no terms below `z^(-(2i + 3j))`.
private theorem coeff_laurentExpansion_basisMonomials_of_lt (p : ℕ × Fin 2) {m : ℤ}
    (hm : m < -(weight p : ℤ)) :
    (W.laurentExpansion (Affine.CoordinateRing.basisMonomials W.toAffine p)).coeff m = 0 := by
  rw [laurentExpansion_basisMonomials, coeff_single_mul, PowerSeries.coeff_coe]
  simp only [show m - -(weight p : ℤ) < 0 by omega, ↓reduceIte, mul_zero]

-- The coefficient of `z^(-(2i + 3j))` in the Laurent expansion of `xⁱyʲ` is `(-1)ʲ`.
private theorem coeff_laurentExpansion_basisMonomials_self (p : ℕ × Fin 2) :
    (W.laurentExpansion (Affine.CoordinateRing.basisMonomials W.toAffine p)).coeff
      (-(weight p : ℤ)) = (-1) ^ (p.2 : ℕ) := by
  rw [laurentExpansion_basisMonomials, coeff_single_mul, sub_self, PowerSeries.coeff_coe]
  simp only [lt_irrefl, ↓reduceIte]
  rw [Int.natAbs_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_invOfUnit_formalU, one_pow, mul_one]

-- The coefficients of the Laurent expansion of `g` are the combinations, with the coordinates of
-- `g` in the monomial basis, of those of the monomials.
private theorem coeff_laurentExpansion (g : W.toAffine.CoordinateRing) (m : ℤ) :
    (W.laurentExpansion g).coeff m =
      ∑ p ∈ ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support,
        (Affine.CoordinateRing.basisMonomials W.toAffine).repr g p *
          (W.laurentExpansion (Affine.CoordinateRing.basisMonomials W.toAffine p)).coeff m := by
  conv_lhs => rw [← (Affine.CoordinateRing.basisMonomials W.toAffine).linearCombination_repr g]
  rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- the scalar action of `R` on `R⸨X⸩` through its algebra structure is multiplication by a
  -- constant series
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

-- If the Laurent expansion of `g` vanishes below `z^(-N)`, then every monomial occurring in `g`
-- has weight at most `N`: otherwise, at the occurring monomial of largest weight `M > N`, the
-- coefficient of `z^(-M)` is `±` its coordinate, since the other occurring monomials have smaller
-- weight.
private theorem weight_le_of_coeff_laurentExpansion_eq_zero {g : W.toAffine.CoordinateRing}
    {N : ℤ} (h : ∀ m : ℤ, m < -N → (W.laurentExpansion g).coeff m = 0)
    {p : ℕ × Fin 2} (hp : p ∈ ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support) :
    (weight p : ℤ) ≤ N := by
  set c := (Affine.CoordinateRing.basisMonomials W.toAffine).repr g
  by_contra! hpN
  -- the occurring monomial of largest weight
  obtain ⟨q, hq, hqmax⟩ := c.support.exists_max_image weight ⟨p, hp⟩
  have hqN : N < weight q := hpN.trans_le (by exact_mod_cast hqmax p hp)
  have hcoeff := coeff_laurentExpansion W g (-(weight q : ℤ))
  rw [h _ (by omega), Finset.sum_eq_single q (fun p' hp' hne ↦ ?_) (fun h ↦ (h hq).elim),
    coeff_laurentExpansion_basisMonomials_self] at hcoeff
  · -- the coordinate of `q` is `±` the vanishing coefficient
    exact Finsupp.mem_support_iff.mp hq
      (((isUnit_neg_one (α := R)).pow _).mul_left_eq_zero.mp hcoeff.symm)
  · -- the other occurring monomials have smaller weight
    have hlt : weight p' < weight q :=
      (hqmax p' hp').lt_of_ne fun heq ↦ hne (weight_injective heq)
    rw [coeff_laurentExpansion_basisMonomials_of_lt W p' (by omega), mul_zero]

/-- **The pole order at infinity.** The Laurent expansion of a function `g` on the affine
Weierstrass curve vanishes below `z^(-n)` exactly when `g` is an `R`-linear combination of the
monomials `xⁱyʲ`, `j ≤ 1`, of weight `2i + 3j ≤ n`. -/
theorem mem_span_basisMonomials_iff_forall_coeff_laurentExpansion_eq_zero
    {g : W.toAffine.CoordinateRing} {n : ℕ} :
    g ∈ Submodule.span R (Affine.CoordinateRing.basisMonomials W.toAffine ''
        {p | 2 * p.1 + 3 * (p.2 : ℕ) ≤ n}) ↔
      ∀ m : ℤ, m < -n → (W.laurentExpansion g).coeff m = 0 := by
  rw [Module.Basis.mem_span_image]
  refine ⟨fun hg m hm ↦ ?_, fun h p hp ↦ ?_⟩
  · rw [coeff_laurentExpansion, Finset.sum_eq_zero fun p hp ↦ ?_]
    have hpn : weight p ≤ n := hg hp
    rw [coeff_laurentExpansion_basisMonomials_of_lt W p (by omega), mul_zero]
  · exact_mod_cast weight_le_of_coeff_laurentExpansion_eq_zero W h hp

/-- The Laurent expansion at the point at infinity is injective. -/
theorem laurentExpansion_injective : Function.Injective W.laurentExpansion := by
  refine (injective_iff_map_eq_zero _).mpr fun g hg ↦ ?_
  -- no monomial has weight at most `-1`, so no monomial occurs in `g`
  rw [← (Affine.CoordinateRing.basisMonomials W.toAffine).repr.map_eq_zero_iff,
    ← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have := weight_le_of_coeff_laurentExpansion_eq_zero W (N := -1)
    (fun m _ ↦ by rw [hg, HahnSeries.coeff_zero]) hp
  omega

-- If no monomial of weight above that of `p₀` occurs in `g`, the coefficient of `z^(-(2i + 3j))`,
-- for `p₀ = (i, j)`, in the Laurent expansion of `g` is `(-1)ʲ` times the coordinate of `xⁱyʲ`.
private theorem coeff_laurentExpansion_neg_weight {g : W.toAffine.CoordinateRing}
    {p₀ : ℕ × Fin 2}
    (hg : ∀ p ∈ ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support,
      weight p ≤ weight p₀) :
    (W.laurentExpansion g).coeff (-(weight p₀ : ℤ)) =
      (Affine.CoordinateRing.basisMonomials W.toAffine).repr g p₀ * (-1) ^ (p₀.2 : ℕ) := by
  rw [coeff_laurentExpansion, Finset.sum_eq_single p₀ (fun p hp hne ↦ ?_) (fun h ↦ ?_),
    coeff_laurentExpansion_basisMonomials_self]
  · have hlt : weight p < weight p₀ :=
      (hg p hp).lt_of_ne fun heq ↦ hne (weight_injective heq)
    rw [coeff_laurentExpansion_basisMonomials_of_lt W p (by omega), mul_zero]
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

-- An element whose coordinates in the monomial basis vanish off a finite set `s` is the
-- combination over `s` of the monomials.
private theorem eq_sum_basisMonomials {g : W.toAffine.CoordinateRing} {s : Finset (ℕ × Fin 2)}
    (hs : ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support ⊆ s) :
    g = ∑ p ∈ s, (Affine.CoordinateRing.basisMonomials W.toAffine).repr g p •
      Affine.CoordinateRing.basisMonomials W.toAffine p := by
  conv_lhs => rw [← (Affine.CoordinateRing.basisMonomials W.toAffine).linearCombination_repr g]
  exact Finsupp.sum_of_support_subset _ hs (fun p a ↦ a • _) fun _ _ ↦ zero_smul ..

/-- **A function with a pole of order at most `2` at infinity is `αx + β`.** If the Laurent
expansion of `g` vanishes below `z⁻²`, then `g = αx + β` for some `β`, where `α` is the
coefficient of `z⁻²` of the expansion. -/
theorem exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_two
    {g : W.toAffine.CoordinateRing} (h : ∀ m : ℤ, m < -2 → (W.laurentExpansion g).coeff m = 0) :
    ∃ β : R, g = algebraMap R _ ((W.laurentExpansion g).coeff (-2)) *
      AdjoinRoot.of W.toAffine.polynomial X + algebraMap R _ β := by
  have hg := (mem_span_basisMonomials_iff_forall_coeff_laurentExpansion_eq_zero W (n := 2)).mpr
    (by exact_mod_cast h)
  rw [Module.Basis.mem_span_image] at hg
  have hw : ∀ p ∈ ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support,
      weight p ≤ weight (1, 0) := fun p hp ↦ hg hp
  -- the occurring monomials are `1` and `x`
  have hs : ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support ⊆
      {(0, 0), (1, 0)} := by
    rintro ⟨i, j⟩ hp
    have hij : 2 * i + 3 * (j : ℕ) ≤ 2 := hg hp
    fin_cases j <;> simp at hij ⊢
    omega
  refine ⟨(Affine.CoordinateRing.basisMonomials W.toAffine).repr g (0, 0), ?_⟩
  have hc := coeff_laurentExpansion_neg_weight W hw
  norm_num [weight] at hc
  conv_lhs => rw [eq_sum_basisMonomials W hs]
  rw [hc, Finset.sum_pair (by decide)]
  simp [Algebra.smul_def, add_comm]

/-- **A function with a pole of order at most `3` at infinity is `γy + δx + β`.** If the Laurent
expansion of `g` vanishes below `z⁻³`, then `g = γy + δx + β` for some `δ` and `β`, where `-γ` is
the coefficient of `z⁻³` of the expansion. -/
theorem exists_eq_of_coeff_laurentExpansion_eq_zero_of_lt_neg_three
    {g : W.toAffine.CoordinateRing} (h : ∀ m : ℤ, m < -3 → (W.laurentExpansion g).coeff m = 0) :
    ∃ δ β : R, g = algebraMap R _ (-(W.laurentExpansion g).coeff (-3)) *
      AdjoinRoot.root W.toAffine.polynomial + algebraMap R _ δ *
        AdjoinRoot.of W.toAffine.polynomial X + algebraMap R _ β := by
  have hg := (mem_span_basisMonomials_iff_forall_coeff_laurentExpansion_eq_zero W (n := 3)).mpr
    (by exact_mod_cast h)
  rw [Module.Basis.mem_span_image] at hg
  have hw : ∀ p ∈ ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support,
      weight p ≤ weight (0, 1) := fun p hp ↦ hg hp
  -- the occurring monomials are `1`, `x` and `y`
  have hs : ((Affine.CoordinateRing.basisMonomials W.toAffine).repr g).support ⊆
      {(0, 0), (1, 0), (0, 1)} := by
    rintro ⟨i, j⟩ hp
    have hij : 2 * i + 3 * (j : ℕ) ≤ 3 := hg hp
    fin_cases j <;> simp at hij ⊢ <;> omega
  refine ⟨(Affine.CoordinateRing.basisMonomials W.toAffine).repr g (1, 0),
    (Affine.CoordinateRing.basisMonomials W.toAffine).repr g (0, 0), ?_⟩
  have hc := coeff_laurentExpansion_neg_weight W hw
  norm_num [weight] at hc
  conv_lhs => rw [eq_sum_basisMonomials W hs]
  rw [hc, Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp [Algebra.smul_def]
  ring

end WeierstrassCurve
