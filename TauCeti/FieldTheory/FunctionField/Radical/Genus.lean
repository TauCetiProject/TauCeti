/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The genus formula for radical extensions `y ^ n = u`

Let `F' = F(y)` with `y ^ n = u` for a nonzero `u ∈ F`, where `n` is invertible in the constant
field `k` of `F`. At a place `P` of `F` write `r_P = gcd(n, ord_P u)`. Every place `P'` of `F'`
above `P` has `e(P' ∣ P) = n / r_P` and `d(P' ∣ P) = n / r_P - 1`
(`TauCeti.Place.ramificationIdx_eq_of_pow_eq` and
`TauCeti.Place.differentExponent_add_one_eq_of_pow_eq`), so the different is a rational multiple
of a conorm:

`n • Diff(F'/F) = Con (∑_P (n - r_P) P)`.

The sum runs over any finite set `S` of places of `F` outside which `n` divides `ord_P u`, for
instance the zeros and poles of `u`; the places outside `S` contribute nothing because
`r_P = n` there. Taking degrees gives `[k' : k] deg Diff(F'/F) = ∑_{P ∈ S} (n - r_P) deg P` once
`[F' : F] = n`, and the Hurwitz genus formula turns this into Stichtenoth's closed genus formula

`[k' : k] (2g' - 2) = n (2g - 2) + ∑_{P ∈ S} (n - r_P) deg P`.

Neither a root of unity in the constants nor the irreducibility of `X ^ n - u` is assumed: the
local data does not need them, and the genus formula only uses the degree `[F' : F] = n`, which
is what the irreducibility of `X ^ n - u` would supply. The genus formula inherits the hypotheses
of the Hurwitz genus formula: the constant fields `k` of `F` and `k'` of `F'` are exact, and
`k' / k` is separable.

When some place `P` of `F` has `gcd(n, ord_P u) = 1`, the hypotheses on `F'` are consequences
(Stichtenoth, Corollary 3.7.4): `X ^ n - u` is irreducible, so `[F' : F] = n`, the extension is
separable, and the places above `P` are totally ramified, so `k` stays the exact constant field of
`F'`. The genus formula then holds with no hypothesis on `F'`:

`2g' - 2 = n (2g - 2) + ∑_{P ∈ S} (n - r_P) deg P`.

## Main results

* `TauCeti.Divisor.nsmul_different_eq_conorm_of_pow_eq`: `n • Diff(F'/F) = Con (∑ (n - r_P) P)`.
* `TauCeti.Divisor.natCast_mul_finrank_mul_degree_different_of_pow_eq`: its degree,
  `n [k' : k] deg Diff(F'/F) = [F' : F] ∑ (n - r_P) deg P`.
* `TauCeti.genus_formula_of_pow_eq`: the genus formula
  `[k' : k] (2g' - 2) = n (2g - 2) + ∑ (n - r_P) deg P`.
* `TauCeti.isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one`: a place with `gcd(n, ord_P u) = 1`
  keeps the constant field exact.
* `TauCeti.two_mul_genus_sub_two_eq_of_pow_eq_of_gcd_ord_eq_one`: the genus formula
  `2g' - 2 = n (2g - 2) + ∑ (n - r_P) deg P` in that case, and
  `TauCeti.two_mul_genus_eq_of_pow_eq_of_gcd_ord_eq_one_ratFunc` its form over `k(x)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.3, Corollary 3.7.4 and Theorem 3.4.13.

The divisor, degree and Hurwitz assembly follows the Artin–Schreier genus formula in
`TauCeti.FieldTheory.FunctionField.ArtinSchreier.Genus`.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

section Radical

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (hF : IsFunctionField k F)
variable {y : F'} {n : ℕ} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u)
variable (hn : (n : k) ≠ 0) (hu : u ≠ 0)
variable (S : Finset (Place k F)) (hS : ∀ P ∉ S, (n : ℤ) ∣ P.ord u)

include hF hgen hy hn hu hS

/-- **The different of a radical extension** (Stichtenoth, Proposition 3.7.3(b)): for
`F' = F(y)` with `y ^ n = u`, the different multiplied by `n` is the conorm of the divisor
`∑_{P ∈ S} (n - r_P) P`, where `r_P = gcd(n, ord_P u)` and `S` is any finite set of places outside
which `n` divides `ord_P u`. -/
theorem Divisor.nsmul_different_eq_conorm_of_pow_eq :
    n • Divisor.different k' F' hF = Divisor.conorm k' F'
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ n - Int.gcd n (P.ord u)) := by
  classical
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  refine WeilDivisor.ext fun P' ↦ ?_
  rw [WeilDivisor.coeff_nsmul, Divisor.coeff_different, Divisor.coeff_conorm,
    WeilDivisor.coeff_ofFinsetWithMultiplicity,
    Place.ramificationIdx_eq_of_pow_eq k F (P' := P') hgen hy hn hu]
  have hd := Place.differentExponent_add_one_eq_of_pow_eq k F (P' := P') hgen hy hn hu
  set r := Int.gcd n ((P'.restrict k F).ord u)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have hrn : r ∣ n := by exact_mod_cast Int.gcd_dvd_left (n : ℤ) ((P'.restrict k F).ord u)
  obtain ⟨s, hs⟩ := hrn
  have hr0 : r ≠ 0 := by
    rintro h
    exact hn0 (by rw [hs, h, zero_mul])
  rw [hs, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0)] at hd ⊢
  split_ifs with hP
  · -- `n (s - 1) = s (n - r)` for `n = r s`, read in `ℤ`.
    have hrle : r ≤ r * s := Nat.le_mul_of_pos_right r (Nat.pos_of_ne_zero fun h ↦ by
      simp [h] at hd)
    rw [Nat.cast_sub hrle]
    have hd' : (Place.differentExponent k F P' : ℤ) = s - 1 := by omega
    rw [hd']
    push_cast
    ring
  · -- Outside `S`, `r_P = n`, so the place is unramified and the different exponent vanishes.
    have hrs : r * 1 = r * s := by
      rw [mul_one, ← hs]
      exact Int.gcd_eq_natAbs_left (hS _ hP) |>.trans (Int.natAbs_natCast n)
    have hs1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) hrs
    have : Place.differentExponent k F P' = 0 := by omega
    simp [this]

/-- **The degree of the different of a radical extension**, cross-multiplied: for `F' = F(y)` with
`y ^ n = u`, `n · [k' : k] · deg Diff(F'/F) = [F' : F] · ∑_{P ∈ S} (n - r_P) deg P`, where
`r_P = gcd(n, ord_P u)` and `S` is any finite set of places outside which `n` divides `ord_P u`.
When `[F' : F] = n` the factor `n` cancels; see `TauCeti.genus_formula_of_pow_eq`. -/
theorem Divisor.natCast_mul_finrank_mul_degree_different_of_pow_eq (hF' : IsFunctionField k' F') :
    (n : ℤ) * ((Module.finrank k k' : ℤ) * Divisor.degree (Divisor.different k' F' hF)) =
      Module.finrank F F' * ∑ P ∈ S, ((n : ℤ) - Int.gcd n (P.ord u)) * P.degree := by
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  have h := congrArg Divisor.degree
    (Divisor.nsmul_different_eq_conorm_of_pow_eq (k' := k') (F' := F') hF hgen hy hn hu S hS)
  rw [map_nsmul, nsmul_eq_mul] at h
  have hcon := Divisor.finrank_mul_degree_conorm_of_isSeparable (k' := k') (F' := F')
    (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ n - Int.gcd n (P.ord u))
  rw [Divisor.degree_eq_weightedDegree
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ n - Int.gcd n (P.ord u)),
    WeilDivisor.weightedDegree_ofFinsetWithMultiplicity] at hcon
  have hle (P : Place k F) : Int.gcd n (P.ord u) ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero fun h ↦ hn (by rw [h, Nat.cast_zero]))
      (by exact_mod_cast Int.gcd_dvd_left (n : ℤ) (P.ord u))
  simp_rw [Nat.cast_sub (hle _)] at hcon
  rw [mul_left_comm, h, hcon]

/-- **The genus formula for radical extensions** (Stichtenoth, Proposition 3.7.3(b) with
Theorem 3.4.13): for `F' = F(y)` of degree `n` over `F` with `y ^ n = u`, `n` invertible in `k`,
exact constant fields `k` of `F` and `k'` of `F'`, and `k' / k` separable,
`[k' : k] (2g' - 2) = n (2g - 2) + ∑_{P ∈ S} (n - r_P) deg P`, where `r_P = gcd(n, ord_P u)` and
`S` is any finite set of places outside which `n` divides `ord_P u`. -/
theorem genus_formula_of_pow_eq [Algebra.IsSeparable k k'] (hF' : IsFunctionField k' F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F')
    (hfin : Module.finrank F F' = n) :
    (Module.finrank k k' : ℤ) * (2 * genus k' F' - 2) =
      n * (2 * genus k F - 2) + ∑ P ∈ S, ((n : ℤ) - Int.gcd n (P.ord u)) * P.degree := by
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  have hn0 : (n : ℤ) ≠ 0 := by
    rintro h
    exact hn (by exact_mod_cast congrArg (Int.cast : ℤ → k) h)
  have h := Divisor.natCast_mul_finrank_mul_degree_different_of_pow_eq hF hgen hy hn hu S hS hF'
  rw [hfin] at h
  rw [hurwitz_genus_formula hF hF' hex hex', hfin, mul_left_cancel₀ hn0 h]

end Radical

/-! ### Kummer extensions with a place of coprime order -/

section Coprime

variable {k : Type u} {F : Type v} {F' : Type v'} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable {y : F'} {n : ℕ} {u : F}

omit [Algebra k F'] [IsScalarTower k F F'] in
/-- A radical extension `F(y) / F`, `y ^ n = u`, with a place at which `n` is coprime to the order
of `u`, has degree `n` and is finite and separable when `n` is invertible in `k` and `u ≠ 0`. -/
private theorem finrank_eq_and_isSeparable_of_pow_eq_of_gcd_ord_eq_one (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ n = algebraMap F F' u) (hn : (n : k) ≠ 0) (hu : u ≠ 0) (P : Place k F)
    (hP : Int.gcd n (P.ord u) = 1) :
    Module.finrank F F' = n ∧ FiniteDimensional F F' ∧ Algebra.IsSeparable F F' := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have hfin : Module.finrank F F' = n :=
    P.valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one hgen hy hn0
      (by rwa [Valuation.ord_def, ← Place.ord_def])
  have hnF : (n : F) ≠ 0 := by
    rwa [← map_natCast (algebraMap k F), ne_eq, map_eq_zero]
  exact ⟨hfin, Module.finite_of_finrank_pos (hfin ▸ Nat.pos_of_ne_zero hn0),
    isSeparable_of_pow_eq_of_adjoin_eq_top hnF hu hy hgen⟩

/-- **A Kummer extension with a place of coprime order acquires no new constants** (Stichtenoth,
Corollary 3.7.4): if `F' = F(y)` with `y ^ n = u` for a nonzero `u ∈ F`, `n` is invertible in
the exact constant field `k` of `F`, and `gcd(n, ord_P u) = 1` at some place `P` of `F`, then `k`
is also the exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hgen : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u)
    (hn : (n : k) ≠ 0) (hu : u ≠ 0) (P : Place k F) (hP : Int.gcd n (P.ord u) = 1) :
    IsIntegrallyClosedIn k F' := by
  obtain ⟨hfin, _, _⟩ :=
    finrank_eq_and_isSeparable_of_pow_eq_of_gcd_ord_eq_one hgen hy hn hu P hP
  obtain ⟨P', hP'⟩ :=
    Place.restrict_surjective_of_finiteDimensional (k' := k) (F' := F') hF hF.finite_extension P
  refine isIntegrallyClosedIn_of_isTotallyRamified (F := F) hex (P' := P') ?_
  refine Place.isTotallyRamified_of_pow_eq_of_gcd_ord_eq_one k F hfin hy
    (fun h ↦ hn (by rw [h, Nat.cast_zero])) ?_
  simpa only [hP'] using hP

/-- **The genus formula for Kummer extensions** (Stichtenoth, Corollary 3.7.4): let `F' = F(y)`
with `y ^ n = u` for a nonzero `u ∈ F`, where `n` is invertible in the exact constant field `k`
of `F`, and suppose `gcd(n, ord_P u) = 1` at some place `P` of `F`. Then

`2g' - 2 = n (2g - 2) + ∑_{Q ∈ S} (n - r_Q) deg Q`,

where `r_Q = gcd(n, ord_Q u)` and `S` is any finite set of places outside which `n` divides
`ord_Q u`. The degree `[F' : F] = n`, separability, and exactness of the constants of `F'` all
follow from the place `P`. No root of unity in `k` is needed. -/
theorem two_mul_genus_sub_two_eq_of_pow_eq_of_gcd_ord_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hgen : F⟮y⟯ = ⊤) (hy : y ^ n = algebraMap F F' u)
    (hn : (n : k) ≠ 0) (hu : u ≠ 0) (S : Finset (Place k F))
    (hS : ∀ Q ∉ S, (n : ℤ) ∣ Q.ord u) (P : Place k F) (hP : Int.gcd n (P.ord u) = 1) :
    2 * (genus k F' : ℤ) - 2 =
      n * (2 * genus k F - 2) + ∑ Q ∈ S, ((n : ℤ) - Int.gcd n (Q.ord u)) * Q.degree := by
  obtain ⟨hfin, _, _⟩ :=
    finrank_eq_and_isSeparable_of_pow_eq_of_gcd_ord_eq_one hgen hy hn hu P hP
  have hex' := isIntegrallyClosedIn_of_pow_eq_of_gcd_ord_eq_one hF hex hgen hy hn hu P hP
  simpa only [Module.finrank_self, Nat.cast_one, one_mul] using
    genus_formula_of_pow_eq (k' := k) hF hgen hy hn hu S hS hF.finite_extension hex hex' hfin

end Coprime

section RatFunc

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- **The genus formula for Kummer extensions of `k(x)`**: if `F = k(x)(y)` with `y ^ n = u` for
a nonzero `u ∈ k(x)`, `n` is invertible in `k`, and `gcd(n, ord_P u) = 1` at some place `P` of
`k(x)`, then

`2g = ∑_{Q ∈ S} (n - r_Q) deg Q - 2 (n - 1)`,

where `r_Q = gcd(n, ord_Q u)` and `S` is any finite set of places of `k(x)` outside which `n`
divides `ord_Q u`. -/
theorem two_mul_genus_eq_of_pow_eq_of_gcd_ord_eq_one_ratFunc {y : F} {n : ℕ}
    {u : RatFunc k} (hgen : (RatFunc k)⟮y⟯ = ⊤) (hy : y ^ n = algebraMap (RatFunc k) F u)
    (hn : (n : k) ≠ 0) (hu : u ≠ 0) (S : Finset (Place k (RatFunc k)))
    (hS : ∀ Q ∉ S, (n : ℤ) ∣ Q.ord u) (P : Place k (RatFunc k))
    (hP : Int.gcd n (P.ord u) = 1) :
    2 * (genus k F : ℤ) = ∑ Q ∈ S, ((n : ℤ) - Int.gcd n (Q.ord u)) * Q.degree - 2 * (n - 1) := by
  have hg := two_mul_genus_sub_two_eq_of_pow_eq_of_gcd_ord_eq_one (IsFunctionField.ratFunc k)
    inferInstance hgen hy hn hu S hS P hP
  rw [genus_ratFunc, Nat.cast_zero] at hg
  linear_combination hg

end RatFunc

end TauCeti
