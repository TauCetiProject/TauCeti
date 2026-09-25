/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Different.Radical
public import TauCeti.FieldTheory.Separable.Quadratic
-- Proof-only: the places of `k(x)`, their degrees, and the orders of polynomials there.
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
-- Proof-only: `Valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one`, the degree of `F / k(x)`.
import TauCeti.FieldTheory.KummerExtension

/-!
# Hyperelliptic function fields

An algebraic function field `F / k` is *hyperelliptic* when it has genus at least two and
contains a rational subfield `k(x)` of index two over which it is separable.  Separability is
part of the definition rather than a consequence of it: over a constant field of characteristic
two an index-two subfield can be inseparable, and no standing hypothesis of this development
rules that out.  Away from characteristic two it is automatic, by
`TauCeti.Algebra.isSeparable_of_finrank_eq_two`.

The first part of this file is the *intrinsic* description of that subfield, which mentions no
element of `F` at all: `F` is hyperelliptic exactly when its genus is at least two and some
divisor of degree two has `ℓ(A) ≥ 2`.  One direction is the pole divisor `(x)_∞` of the
index-two generator, whose Riemann--Roch space contains `1` and `x`.  The other moves `A` inside
its class to an effective divisor `B`, picks a function `x ∈ L(B)` outside the constants — which
positivity of `ℓ(B)` over the line of constants provides — and reads `[F : k(x)] = deg (x)_∞`
off the product formula: the pole divisor of `x` is dominated by `B`, so the degree is at most
two, and it is not one because a rational function field has genus zero.

In genus two the canonical divisor is such an `A`, since `deg W = 2g - 2 = 2` and `ℓ(W) = g = 2`;
so every function field of genus two has an index-two rational subfield, and away from
characteristic two every function field of genus two is hyperelliptic.

The models `y² = f(x)` go the other way. Away from characteristic two, if `F = k(x)(y)` with
`y² = f(x)` for a squarefree polynomial `f` of degree `m`, and `k` is the exact constant field,
then `F` has genus `⌊(m - 1) / 2⌋`. The ramified places of `F / k(x)` lie over the irreducible
factors of `f`, and over the place at infinity when `m` is odd. Each has different exponent one,
so `deg Diff(F / k(x)) = m + m % 2`, and the Hurwitz genus formula gives the genus.

## Main definitions

* `TauCeti.IsHyperellipticFunctionField`: genus at least two together with a separable rational
  subfield of index two.

## Main results

* `TauCeti.exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two`: a divisor of degree two
  with `ℓ ≥ 2` produces a rational subfield of index two; no hypothesis on the characteristic.
* `TauCeti.isHyperellipticFunctionField_iff_two_le_genus_and_exists_degree_eq_two_and_two_le_dim`:
  the intrinsic characterization, away from characteristic two.
* `TauCeti.exists_transcendental_finrank_adjoin_eq_two_of_genus_eq_two` and
  `TauCeti.isHyperellipticFunctionField_of_genus_eq_two`: genus two gives an index-two rational
  subfield, and away from characteristic two makes `F` hyperelliptic.
* `TauCeti.finrank_eq_two_of_sq_eq_of_squarefree`: `[F : k(x)] = 2` for `y² = f(x)` with `f`
  squarefree and nonconstant.
* `TauCeti.genus_eq_natDegree_sub_one_div_two_of_sq_eq`: `y² = f(x)` with `f` squarefree has genus
  `⌊(deg f - 1) / 2⌋`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section VI.2: Definition 6.2.1, Lemma 6.2.2 and Proposition 6.2.3.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A **hyperelliptic function field** (Stichtenoth, Definition 6.2.1, with separability of the
index-two subextension made part of the definition): genus at least two together with an element
`x` transcendental over `k` such that `F / k(x)` is separable of degree two.

Being an algebraic function field is *not* part of the predicate: the hypothesis
`TauCeti.IsFunctionField`, like the exactness of the constant field, is kept as a separate
hypothesis on the statements that need it, as everywhere in this development.

In characteristic two an index-two subextension can be purely inseparable, and such an `F` is
deliberately outside this model class; away from characteristic two the separability clause is
automatic, so there the predicate agrees with Stichtenoth's index-two definition. -/
structure IsHyperellipticFunctionField (k F : Type*) [Field k] [Field F] [Algebra k F] :
    Prop where
  /-- A hyperelliptic function field has genus at least two. -/
  two_le_genus : 2 ≤ genus k F
  /-- A hyperelliptic function field has a separable rational subfield of index two. -/
  exists_separable_finrank_adjoin_eq_two : ∃ x : F, Transcendental k x ∧
    Module.finrank k⟮x⟯ F = 2 ∧ Algebra.IsSeparable k⟮x⟯ F

/-! ### From the index-two subfield to a divisor of degree two -/

/-- **A hyperelliptic function field has a divisor of degree two whose Riemann--Roch space has
dimension at least two.**  This is the forward half of the intrinsic characterization
`TauCeti.isHyperellipticFunctionField_iff_two_le_genus_and_exists_degree_eq_two_and_two_le_dim`,
and it needs no hypothesis on the characteristic. -/
theorem IsHyperellipticFunctionField.exists_degree_eq_two_and_two_le_dim
    (hhyp : IsHyperellipticFunctionField k F) :
    ∃ A : Divisor k F, Divisor.degree A = 2 ∧ 2 ≤ Divisor.dim A := by
  -- The pole divisor of an index-two generator `x` has degree `[F : k(x)]` by the product
  -- formula, and its Riemann--Roch space contains the two independent functions `1` and `x`.
  obtain ⟨x, hx, hrank, -⟩ := hhyp.exists_separable_finrank_adjoin_eq_two
  have _ : FiniteDimensional k⟮x⟯ F := Module.finite_of_finrank_pos (by omega)
  have hF : IsFunctionField k F := hx.isFunctionField_adjoin.finite_extension
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  refine ⟨Divisor.poles hF (Units.mk0 x hx0), ?_, ?_⟩
  · rw [Divisor.degree_poles hF (Units.mk0 x hx0) hx, Units.val_mk0, hrank]
    norm_num
  · simpa using Divisor.succ_le_dim_nsmul_poles hF (Units.mk0 x hx0) hx 1

/-! ### From a divisor of degree two to the index-two subfield -/

/-- **A divisor of degree two whose Riemann--Roch space has dimension at least two produces a
rational subfield of index two**, as soon as the genus is positive.

No hypothesis on the characteristic is made, and no separability is claimed: this is the part of
Stichtenoth's Section VI.2 dictionary that holds over an arbitrary constant field.  The genus
hypothesis cannot be dropped: over a rational function field the subfield produced would be all
of `F`. -/
theorem exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hg : genus k F ≠ 0)
    {A : Divisor k F} (hA : Divisor.degree A = 2) (hdim : 2 ≤ Divisor.dim A) :
    ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = 2 := by
  -- Move `A` inside its class to an effective divisor `B`, which has the same degree and `ℓ`.
  obtain ⟨z, hzA, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF A).mp (by omega))
  set B : Divisor k F := Divisor.principal hF (Units.mk0 z hz0) + A with hB
  have hBrw : B = A - Divisor.principal hF (Units.mk0 z hz0)⁻¹ := by
    rw [hB, Divisor.principal_inv]; abel
  have hBeff : 0 ≤ B := (mem_riemannRochSpace_units_iff hF).mp hzA
  have hBdeg : Divisor.degree B = 2 := by rw [hB]; simp [hA]
  have hBdim : 2 ≤ Divisor.dim B := by rwa [hBrw, Divisor.dim_sub_principal]
  -- The constants form a line inside `L(B)`, which has dimension at least two, so `L(B)` holds a
  -- function `x` outside the constants.
  have hlt : (k ∙ (1 : F)) < riemannRochSpace B := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (one_mem_riemannRochSpace_iff.mpr hBeff)) fun hEq ↦ ?_
    rw [Divisor.dim_def, ← hEq, finrank_span_singleton (one_ne_zero : (1 : F) ≠ 0)] at hBdim
    omega
  obtain ⟨x, hxB, hxspan⟩ := SetLike.exists_of_lt hlt
  have hxconst : ∀ c : k, algebraMap k F c ≠ x := fun c hc ↦
    hxspan (hc ▸ Submodule.mem_span_singleton.mpr ⟨c, by simp [Algebra.smul_def]⟩)
  have hx : Transcendental k x := fun halg ↦
    let ⟨c, hc⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex x halg
    hxconst c hc
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isAlgebraic_zero)
  -- The poles of `x` are bounded by `B`, so `[F : k(x)] = deg (x)_∞ ≤ deg B = 2`.
  have hle : Divisor.poles hF (Units.mk0 x hx0) ≤ B := by
    rw [WeilDivisor.le_iff]
    intro P
    have hBP : (0 : ℤ) ≤ B.coeff P := by simpa using WeilDivisor.le_iff.mp hBeff P
    have hord := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp hxB P
    rw [Divisor.coeff_poles, Units.val_mk0, sup_le_iff]
    exact ⟨by omega, hBP⟩
  have hdegle : Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) ≤ 2 := by
    rw [← hBdeg]
    exact Divisor.degree_le_of_le hle
  have _ : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  have hrank : (Module.finrank k⟮x⟯ F : ℤ) =
      Divisor.degree (Divisor.poles hF (Units.mk0 x hx0)) :=
    (Divisor.degree_poles hF (Units.mk0 x hx0) hx).symm
  have hpos : 0 < Module.finrank k⟮x⟯ F := Module.finrank_pos
  have hne : Module.finrank k⟮x⟯ F ≠ 1 := fun h1 ↦ hg (genus_eq_zero_of_adjoin_eq_top hx
    (IntermediateField.finrank_eq_one_iff_eq_top.mp h1))
  exact ⟨x, hx, by omega⟩

/-- **The intrinsic characterization of hyperelliptic function fields** away from characteristic
two (Stichtenoth, Section VI.2): `F` is hyperelliptic exactly when its genus is at least two and
some divisor of degree two has a Riemann--Roch space of dimension at least two.

The characteristic hypothesis is used only to make the index-two subextension separable, so the
forward implication `TauCeti.IsHyperellipticFunctionField.exists_degree_eq_two_and_two_le_dim`
and the subfield half of the converse hold without it. -/
theorem isHyperellipticFunctionField_iff_two_le_genus_and_exists_degree_eq_two_and_two_le_dim
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (h2 : (2 : k) ≠ 0) :
    IsHyperellipticFunctionField k F ↔
      2 ≤ genus k F ∧ ∃ A : Divisor k F, Divisor.degree A = 2 ∧ 2 ≤ Divisor.dim A := by
  refine ⟨fun hhyp ↦ ⟨hhyp.two_le_genus, hhyp.exists_degree_eq_two_and_two_le_dim⟩, ?_⟩
  rintro ⟨hgen, A, hA, hdim⟩
  obtain ⟨x, hx, hrank⟩ :=
    exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two hF hex (by omega) hA hdim
  have h2' : (2 : k⟮x⟯) ≠ 0 := by
    intro h
    have hmap : algebraMap k k⟮x⟯ (2 : k) = 0 := by rw [map_ofNat]; exact h
    exact h2 (by simpa using hmap)
  exact ⟨hgen, x, hx, hrank, Algebra.isSeparable_of_finrank_eq_two h2' hrank⟩

/-! ### Genus two -/

/-- **A function field of genus two has a divisor of degree two whose Riemann--Roch space has
dimension exactly two.**  It supplies the divisor hypotheses of
`TauCeti.exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two` in genus two. -/
theorem exists_degree_eq_two_and_dim_eq_two_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 2) :
    ∃ A : Divisor k F, Divisor.degree A = 2 ∧ Divisor.dim A = 2 := by
  -- A Riemann--Roch divisor `W` is one: `deg W = 2g - 2 = 2` and `ℓ(W) = g = 2`.
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  refine ⟨W, ?_, ?_⟩
  · rw [hW.degree_eq hF hex, hg]; norm_num
  · rw [hW.dim_eq hF hex, hg]

/-- **Every function field of genus two has a rational subfield of index two** (Stichtenoth,
Lemma 6.2.2), over an arbitrary constant field.  Separability of that subextension is *not*
claimed here; away from characteristic two it is automatic, see
`TauCeti.isHyperellipticFunctionField_of_genus_eq_two`. -/
theorem exists_transcendental_finrank_adjoin_eq_two_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 2) :
    ∃ x : F, Transcendental k x ∧ Module.finrank k⟮x⟯ F = 2 := by
  obtain ⟨A, hA, hdim⟩ := exists_degree_eq_two_and_dim_eq_two_of_genus_eq_two hF hex hg
  exact exists_transcendental_finrank_adjoin_eq_two_of_degree_eq_two hF hex (by omega) hA hdim.ge

/-- **Every function field of genus two away from characteristic two is hyperelliptic**
(Stichtenoth, Lemma 6.2.2). -/
theorem isHyperellipticFunctionField_of_genus_eq_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (h2 : (2 : k) ≠ 0) (hg : genus k F = 2) :
    IsHyperellipticFunctionField k F := by
  obtain ⟨A, hA, hdim⟩ := exists_degree_eq_two_and_dim_eq_two_of_genus_eq_two hF hex hg
  exact (isHyperellipticFunctionField_iff_two_le_genus_and_exists_degree_eq_two_and_two_le_dim
    hF hex h2).mpr ⟨by omega, A, hA, hdim.ge⟩

/-! ### The genus of `y² = f(x)` -/

section SquareRoot

open _root_.Polynomial

/-- The places of `k(x)` at which a squarefree polynomial `f` has odd order are those of the
irreducible factors of `f`, each a simple zero, and the place at infinity exactly when `deg f` is
odd.  As divisors: they sum to `div f + (deg f + deg f % 2) · P_∞`. -/
private theorem ofFinset_not_dvd_ord_eq {f : k[X]} (hf : Squarefree f) :
    WeilDivisor.ofFinset {P ∈ (Divisor.principal (IsFunctionField.ratFunc k) (Units.mk0
        (algebraMap k[X] (RatFunc k) f) (RatFunc.algebraMap_ne_zero hf.ne_zero))).support |
        ¬ ((2 : ℕ) : ℤ) ∣ P.ord (algebraMap k[X] (RatFunc k) f)} =
      Divisor.principal (IsFunctionField.ratFunc k)
          (Units.mk0 (algebraMap k[X] (RatFunc k) f) (RatFunc.algebraMap_ne_zero hf.ne_zero)) +
        (f.natDegree + f.natDegree % 2) • WeilDivisor.ofPoint (Place.infty k) := by
  classical
  refine WeilDivisor.ext fun P ↦ ?_
  simp only [WeilDivisor.coeff_ofFinset, Finset.mem_filter, Divisor.mem_support_principal_iff,
    Units.val_mk0, WeilDivisor.coeff_add, Divisor.coeff_principal, WeilDivisor.coeff_nsmul]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · rw [Place.ord_infty, RatFunc.intDegree_polynomial, WeilDivisor.coeff_ofPoint_self]
    split_ifs <;> omega
  · rw [Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf,
      WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq)]
    split_ifs <;> omega

variable [Algebra (RatFunc k) F]

omit [Algebra k F] in
/-- **`y² = f(x)` has degree two over `k(x)`**: if `F = k(x)(y)` with `y² = f(x)` for a squarefree
nonconstant polynomial `f`, then `[F : k(x)] = 2`.  The order of `f` at the place of any
irreducible factor is one, so `f` is not a square in `k(x)`.  No hypothesis on the characteristic
is needed. -/
theorem finrank_eq_two_of_sq_eq_of_squarefree {f : k[X]} (hf : Squarefree f)
    (hm : 0 < f.natDegree) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) :
    Module.finrank (RatFunc k) F = 2 := by
  obtain ⟨q, hq, hqf⟩ := exists_irreducible_of_degree_pos (natDegree_pos_iff_degree_pos.mp hm)
  refine Valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one
    (Place.adicOfIrreducible hq).valuation hgen hy two_ne_zero ?_
  rw [Valuation.ord_def, ← Place.ord_def,
    Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq hf]
  simp [hqf]

variable [IsScalarTower k (RatFunc k) F]

/-- **The genus of `y² = f(x)`** (Stichtenoth, Proposition 6.2.3(b)): away from characteristic
two, if `F = k(x)(y)` with `y² = f(x)` for a squarefree polynomial `f`, and `k` is the exact field
of constants of `F`, then `F` has genus `⌊(deg f - 1) / 2⌋`, that is `(m - 1) / 2` for `m = deg f`
odd and `(m - 2) / 2` for `m` even.  In particular `F` has genus at least two once `deg f ≥ 5`.

For constant `f` the hypotheses force `F = k(x)`, of genus `0`, in accordance with the formula. -/
theorem genus_eq_natDegree_sub_one_div_two_of_sq_eq (h2 : (2 : k) ≠ 0)
    (hex : IsIntegrallyClosedIn k F) {f : k[X]} (hf : Squarefree f) {y : F}
    (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) :
    genus k F = (f.natDegree - 1) / 2 := by
  have hu : algebraMap k[X] (RatFunc k) f ≠ 0 := RatFunc.algebraMap_ne_zero hf.ne_zero
  -- `[F : k(x)]` is `2` for nonconstant `f`; for constant `f`, exactness of the constants puts
  -- the square root `y` of a constant into `k`, so `F = k(x)`.
  have hN : Module.finrank (RatFunc k) F = if f.natDegree = 0 then 1 else 2 := by
    split_ifs with hm
    · obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hm
      have halg : IsAlgebraic k y := ⟨X ^ 2 - C c, X_pow_sub_C_ne_zero two_pos c, by
        rw [map_sub, map_pow, aeval_X, aeval_C, hy, ← hc, RatFunc.algebraMap_C,
          ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply, sub_self]⟩
      obtain ⟨c', hc'⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex y halg
      have hbot : (RatFunc k)⟮y⟯ = ⊥ := IntermediateField.adjoin_simple_eq_bot_iff.mpr
        (IntermediateField.mem_bot.mpr
          ⟨algebraMap k (RatFunc k) c', by rw [← IsScalarTower.algebraMap_apply, hc']⟩)
      exact IntermediateField.bot_eq_top_iff_finrank_eq_one.mp (hbot ▸ hgen)
    · exact finrank_eq_two_of_sq_eq_of_squarefree hf (Nat.pos_of_ne_zero hm) hgen hy
  have : FiniteDimensional (RatFunc k) F :=
    Module.finite_of_finrank_pos (by split_ifs at hN <;> omega)
  -- `y` is a root of the separable `X² - f`, so `F = k(x)(y)` is separable over `k(x)`.
  have : Algebra.IsSeparable (RatFunc k) F := by
    have h2' : ((2 : ℕ) : RatFunc k) ≠ 0 := by
      rw [← map_natCast (algebraMap k (RatFunc k))]
      exact (_root_.map_ne_zero _).mpr (by exact_mod_cast h2)
    have hsep : IsSeparable (RatFunc k) y :=
      (separable_X_pow_sub_C _ h2' hu).of_dvd (minpoly.dvd _ _ (by simp [hy]))
    have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hsep
    exact AlgEquiv.Algebra.isSeparable
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  -- Hurwitz: `2g - 2 = [F : k(x)] · (0 - 2) + deg f + deg f % 2`.
  have h := hurwitz_genus_formula_of_pow_eq_of_prime (IsFunctionField.ratFunc k)
    (isFunctionField_iff_functionField.mpr inferInstance) isIntegrallyClosedIn_ratFunc hex
    Nat.prime_two hgen hy (by exact_mod_cast h2) hu
  rw [ofFinset_not_dvd_ord_eq hf, Divisor.degree_add, Divisor.degree_principal,
    map_nsmul, Divisor.degree_ofPoint, Place.degree_infty, genus_ratFunc, Module.finrank_self,
    hN] at h
  by_cases hm : f.natDegree = 0 <;>
    simp only [hm, ↓reduceIte, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one] at h <;> omega

end SquareRoot

end TauCeti
