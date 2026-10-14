/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# The places over a place in an algebraic constant field extension

Let `F' = F · k'` be the compositum of an algebraic function field `F / k` with an algebraic
extension `k' / k` of the constants, finite or not (an algebraic closure of `k`, for instance).
Then `F' / F` is algebraic but in general infinite, so the finiteness of the fibres of
`TauCeti.Place.restrict` cannot be read off the fundamental inequality. It still holds: every
place `P` of `F / k` has only finitely many places of `F' / k'` above it. Indeed `P` is the only
pole of some function `z ∈ F`, and the places of `F'` over `P` are exactly the poles of `z` in
`F'`.

When `k' / k` is separable and `k` is the exact constant field of `F`, the degrees of these
places add up to the degree of `P`:

`∑_{P' ∣ P} deg P' = deg P`.

This is Stichtenoth's Theorem 3.6.3(c), `deg (Con A) = deg A`, for the divisor `A = P`, and it
holds for infinite `k' / k` as well. The same function `z` proves it. Every place over `P` has
ramification index one, so the pole divisor of `z` in `F'` is `m` times the sum of the places over
`P`, where `m = -ord_P z`, while in `F` it is `m P`. The degree of a pole divisor is the degree
`[F : k(z)]`, which does not change when the constants are extended. So the number of places over
`P` is at most `deg P`, with equality when every place over `P` is rational. This is the case
when `k' / k` is normal and the residue field of `P` embeds into `k'`, for example when `k'` is a
separable closure of `k` and the residue field of `P` is separable over `k`: then `P` splits into
exactly `deg P` rational places.

These fibres are the supports of the conorms `Con P` along an algebraic constant field extension,
so their finiteness is what makes the conorm of a divisor finitely supported when `k' / k` is
infinite.

## Main results

* `TauCeti.Place.finite_setOf_restrict_eq_of_isIntegral`: a place of `F / k` has only finitely
  many places above it in an integral extension of function fields, in particular in an
  algebraic constant field extension.
* `TauCeti.Place.finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top`: **the degrees of
  the places over `P` add up to `deg P`** in a separable algebraic constant field extension.
* `TauCeti.Place.ncard_setOf_restrict_eq_le_degree_of_constantCompositum_eq_top`: there are at
  most `deg P` places over `P`.
* `TauCeti.Place.ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top`: there are exactly
  `deg P` places over `P` when `k' / k` is normal and the residue field of `P` embeds into `k'`.

## Reference

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.6.3(a), (c) and (g).
-/

public section

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **A place has only finitely many extensions to an integral extension of function fields**:
if `F' / F` is integral, finite or not, and `F' / k'` is again an algebraic function field, then
every place of `F / k` has only finitely many places of `F' / k'` above it. This covers an
algebraic constant field extension `F' = F · k'` with `k' / k` infinite, where the fundamental
inequality bounds nothing. -/
theorem finite_setOf_restrict_eq_of_isIntegral [Algebra.IsIntegral F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (P : Place k F) :
    {P' : Place k' F' | P'.restrict k F = P}.Finite := by
  -- The places over `P` are the poles in `F'` of a function whose only pole is at `P`.
  obtain ⟨z, hP, hQ⟩ := exists_ord_neg_and_forall_ne_ord_nonneg hF P
  have hz : algebraMap F F' z ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F F').injective]
    rintro rfl
    simp at hP
  refine (Divisor.poles hF' (Units.mk0 _ hz)).support.finite_toSet.subset fun P' hP' ↦ ?_
  rw [Finset.mem_coe, Divisor.mem_support_poles_iff, Units.val_mk0]
  exact (ord_algebraMap_neg_iff_restrict_eq k F P' hP hQ).2 hP'

variable [Algebra.IsSeparable k k']

/-- **The degrees of the places over a place add up to its degree** (Stichtenoth,
Theorem 3.6.3(c), for a single place): if `k` is the exact constant field of `F` and
`F' = F · k'` for a separable algebraic extension `k' / k`, finite or not, then for every place
`P` of `F / k`,

`∑_{P' ∣ P} deg P' = deg P`,

where `deg P'` is the degree of `P'` over `k'`. -/
theorem finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    ∑ᶠ P' ∈ {P' : Place k' F' | P'.restrict k F = P}, P'.degree = P.degree := by
  classical
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hfin := finite_setOf_restrict_eq_of_isIntegral hF hF' P
  obtain ⟨z, hP, hQ⟩ := exists_ord_neg_and_forall_ne_ord_nonneg hF P
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.ord z = -(n : ℤ) := ⟨(-P.ord z).toNat, by omega⟩
  have hn0 : n ≠ 0 := by omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hP
  have hz : algebraMap F F' z ≠ 0 := (map_ne_zero _).2 hz0
  have hzk : ¬IsAlgebraic k z := P.transcendental_of_ord_ne_zero hP.ne
  have hzk' : ¬IsAlgebraic k' (algebraMap F F' z) :=
    (Algebra.IsAlgebraic.transcendental_iff k k').1
      ((transcendental_algebraMap_iff (algebraMap F F').injective).2 hzk)
  -- In `F'`, every place over `P` is unramified, so the pole divisor of `z` is `m` times the sum
  -- of the places over `P`.
  have hpoles' : Divisor.poles hF' (Units.mk0 _ hz) =
      (n : ℤ) • AlgebraicGeometry.WeilDivisor.ofFinset hfin.toFinset := by
    ext P'
    rw [Divisor.coeff_poles, Units.val_mk0, AlgebraicGeometry.WeilDivisor.coeff_zsmul,
      AlgebraicGeometry.WeilDivisor.coeff_ofFinset, ord_algebraMap_restrict k F P' z,
      ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h P', Nat.cast_one, one_mul]
    by_cases hP' : P'.restrict k F = P
    · simp only [hP', Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ite_true, mul_one]
      omega
    · have := hQ _ hP'
      simp only [hP', Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ite_false, mul_zero]
      omega
  -- The degree of the pole divisor of `z` is `[F' : k'(z)] = [F : k(z)] = n deg P`.
  have hdeg := Divisor.degree_poles hF' (Units.mk0 _ hz) (by simpa using hzk')
  rw [hpoles', Divisor.degree_zsmul, AlgebraicGeometry.WeilDivisor.ofFinset_eq_sum, map_sum,
    Units.val_mk0, finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top hex h z,
    finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF hn0 hn hQ] at hdeg
  simp only [Divisor.degree_ofPoint] at hdeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast at hdeg
  exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hn0 : (n : ℤ) ≠ 0) hdeg

/-- **At most `deg P` places lie over `P`**: if `k` is the exact constant field of `F` and
`F' = F · k'` for a separable algebraic extension `k' / k`, finite or not, then a place `P` of
`F / k` has at most `deg P` places of `F' / k'` above it. -/
theorem ncard_setOf_restrict_eq_le_degree_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    {P' : Place k' F' | P'.restrict k F = P}.ncard ≤ P.degree := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hfin := finite_setOf_restrict_eq_of_isIntegral hF hF' P
  rw [← finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top hF hex h P,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun P' _ ↦ P'.one_le_degree_of_isFunctionField hF'

/-- **A place splits into `deg P` rational places once its residue field embeds into the
constants**: if `k` is the exact constant field of `F`, `F' = F · k'` for a separable normal
algebraic extension `k' / k`, finite or not, and the residue field of a place `P` of `F / k`
admits a `k`-embedding into `k'`, then exactly `deg P` places of `F' / k'` lie over `P`. This
applies to every place with residue field separable over `k` when `k'` is a separable closure of
`k`. -/
theorem ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top [Normal k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) (φ : P.ResidueField →ₐ[k] k') :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    {P' : Place k' F' | P'.restrict k F = P}.ncard = P.degree := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hfin := finite_setOf_restrict_eq_of_isIntegral hF hF' P
  rw [← finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top hF hex h P,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P' hP' ↦ ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP'
  subst hP'
  exact (degree_eq_one_of_constantCompositum_eq_top hF hex h P' φ).symm

end Place

end TauCeti
