/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.KummerPolynomial
public import TauCeti.FieldTheory.FunctionField.Different.Derivative
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# A quadratic extension with inseparable residue field extension

Let `P` be a place of an algebraic function field `F / k`, let `t ∈ F` vanish at `P`, and let
`s ∈ 𝒪_P` have a residue `s(P)` that is not a square in the residue field `F_P`. Suppose
`F' = F(y)` with

`y ^ 2 + t y = s`.

In every characteristic, `X ^ 2 + t X - s` is the minimal polynomial of `y`, so `[F' : F] = 2`,
and `F' / F` is separable, since the derivative `2 X + t` is a nonzero polynomial. The residue
of `y` at a place `P'` above `P` is a square root of `s(P)`, so `f(P' ∣ P) ≥ 2`, and the
fundamental inequality `e f ≤ [F' : F]` forces `e(P' ∣ P) = 1`, `f(P' ∣ P) = 2` and the
uniqueness of `P'`.

In characteristic two the residue extension `F'_{P'} = F_P(√s(P))` is purely inseparable, so
`P'` is not tame although `e(P' ∣ P) = 1`. By Dedekind's different theorem the different
exponent is then positive, while the derivative of the equation, `2 y + t = t`, bounds it by
`ord_P t`. When `t` is a uniformizer at `P`, the different exponent is exactly `1`: the place is
*fiercely ramified*, with positive different and ramification index one in a separable
quadratic extension.

Two such steps, `y ^ 2 + t y = s` and then `z ^ 2 + t z = u`, with `s(P), u(P)` independent over
the squares of `F_P`, build the classical fiercely ramified extension of degree four in
characteristic two. Its different exponent `2` differs from the sum `3` of
`|G_i(P')| - 1` over the lower ramification groups: Hilbert's different formula
`TauCeti.Place.differentExponent_eq_finsum_card_ramificationGroup_sub_one` needs a separable
residue extension.

## Main results

* `TauCeti.Place.minpoly_eq_of_sq_add_mul_eq` and `TauCeti.Place.finrank_eq_two_of_sq_add_mul_eq`:
  `X ^ 2 + t X - s` is the minimal polynomial of `y`, and `[F' : F] = 2`.
* `TauCeti.Place.isSeparable_of_sq_add_mul_eq`: `F' / F` is separable.
* `TauCeti.Place.mem_integers_of_sq_add_mul_eq`: `y` is regular at every place above `P`.
* `TauCeti.Place.ramificationIdx_eq_one_of_sq_add_mul_eq` and
  `TauCeti.Place.relativeDegree_eq_two_of_sq_add_mul_eq`: every place above `P` has `e = 1` and
  `f = 2`.
* `TauCeti.Place.subsingleton_setOf_restrict_eq_of_sq_add_mul_eq`: at most one place of `F'` lies
  above `P`.
* `TauCeti.Place.not_isSeparable_residueField_of_sq_add_mul_eq`: in characteristic two the
  residue field extension is not separable.
* `TauCeti.Place.differentExponent_pos_of_sq_add_mul_eq` and
  `TauCeti.Place.differentExponent_le_ord_of_sq_add_mul_eq`: in characteristic two,
  `0 < d(P' ∣ P) ≤ ord_P t`.
* `TauCeti.Place.differentExponent_eq_one_of_sq_add_mul_eq`: in characteristic two, when `t` is a
  uniformizer at `P`, `d(P' ∣ P) = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.1.11, Theorem 3.5.1, Corollary 3.5.5 and Theorem 3.5.10.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F']

section Field

variable {P : Place k F} {t : F} {s : P.integers}

/-- The equation `X ^ 2 + t X - s`, with coefficients in the valuation ring of `P`. -/
private noncomputable def integralEquation (ht : 0 < P.ord t) (s : P.integers) :
    P.integers[X] :=
  X ^ 2 + C ⟨t, P.mem_integers_iff_ord_nonneg.mpr ht.le⟩ * X - C s

private theorem monic_integralEquation (ht : 0 < P.ord t) : (integralEquation ht s).Monic := by
  unfold integralEquation
  monicity!

private theorem map_integralEquation (ht : 0 < P.ord t) :
    (integralEquation ht s).map (algebraMap P.integers F) = X ^ 2 + C t * X - C (s : F) := by
  simp [integralEquation, ValuationSubring.algebraMap_apply]

/-- The reduction of `X ^ 2 + t X - s` at `P` is `X ^ 2 - s(P)`, since `t` vanishes at `P`. -/
private theorem map_residue_integralEquation (ht : 0 < P.ord t) :
    (integralEquation ht s).map (IsLocalRing.residue P.integers) =
      X ^ 2 - C (IsLocalRing.residue P.integers s) := by
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  have hres : IsLocalRing.residue P.integers ⟨t, P.mem_integers_iff_ord_nonneg.mpr ht.le⟩ = 0 :=
    (P.residue_eq_zero_iff_ord_pos (f := ⟨t, _⟩) ht0).mpr ht
  simp [integralEquation, hres]

/-- If `s(P)` is not a square, then `X ^ 2 + t X - s` has no root in `F`: a root would be
integral at `P`, and its residue would be a square root of `s(P)`. -/
private theorem irreducible_X_pow_two_add_C_mul_X_sub_C (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s) :
    Irreducible (X ^ 2 + C t * X - C (s : F)) := by
  have hdeg : (X ^ 2 + C t * X - C (s : F)).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun c hc ↦ ?_
  have hroot : aeval c (integralEquation ht s) = 0 := by
    rw [← aeval_map_algebraMap F, map_integralEquation ht]
    simpa using hc
  have hc' : c ∈ P.integers := P.mem_integers_of_isIntegral (R := P.integers) (fun r ↦ r.2)
    ⟨_, monic_integralEquation ht, by rwa [← aeval_def]⟩
  apply hs (IsLocalRing.residue P.integers ⟨c, hc'⟩)
  have h0 : aeval (⟨c, hc'⟩ : P.integers) (integralEquation ht s) = 0 := by
    apply Subtype.ext
    rw [← ValuationSubring.algebraMap_apply, ← aeval_algebraMap_apply,
      ValuationSubring.algebraMap_apply]
    exact hroot
  have h1 : aeval (IsLocalRing.residue P.integers ⟨c, hc'⟩) (integralEquation ht s) = 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, h0, map_zero]
  rw [aeval_def, eval₂_eq_eval_map, IsLocalRing.ResidueField.algebraMap_eq,
    map_residue_integralEquation ht] at h1
  simpa [sub_eq_zero] using h1

/-- A root of `X ^ 2 + t X - s` is integral over `F`. -/
private theorem isIntegral_of_sq_add_mul_eq {y : F'} (ht : 0 < P.ord t)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) : IsIntegral F y := by
  refine ⟨X ^ 2 + C t * X - C (s : F), ?_, by simp [hy]⟩
  rw [← map_integralEquation ht]
  exact (monic_integralEquation ht).map _

end Field

section Extension

variable {P : Place k F} {y : F'} {t : F} {s : P.integers}

/-- **The minimal equation of `y`**: if `y ^ 2 + t y = s`, where `t` vanishes at `P` and the
residue of `s` at `P` is not a square, then the minimal polynomial of `y` over `F` is
`X ^ 2 + t X - s`. -/
theorem minpoly_eq_of_sq_add_mul_eq (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) :
    minpoly F y = X ^ 2 + C t * X - C (s : F) := by
  refine (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_two_add_C_mul_X_sub_C ht hs)
    ?_ ?_).symm
  · simp [hy]
  · rw [← map_integralEquation ht]
    exact (monic_integralEquation ht).map _

/-- **The degree of the quadratic extension**: if `F' = F(y)` with `y ^ 2 + t y = s`, where `t`
vanishes at `P` and the residue of `s` at `P` is not a square, then `[F' : F] = 2`. -/
theorem finrank_eq_two_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) :
    Module.finrank F F' = 2 := by
  rw [← IntermediateField.finrank_top', ← hgen,
    IntermediateField.adjoin.finrank (isIntegral_of_sq_add_mul_eq ht hy),
    minpoly_eq_of_sq_add_mul_eq ht hs hy]
  compute_degree!

/-- **The quadratic extension is separable**, in every characteristic: if `F' = F(y)` with
`y ^ 2 + t y = s`, where `t` vanishes at `P` and the residue of `s` at `P` is not a square, then
`F' / F` is separable. -/
theorem isSeparable_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) :
    Algebra.IsSeparable F F' := by
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  have hsep : IsSeparable F y := by
    rw [IsSeparable, minpoly_eq_of_sq_add_mul_eq ht hs hy, separable_iff_derivative_ne_zero
      (irreducible_X_pow_two_add_C_mul_X_sub_C ht hs)]
    intro h
    have := congrArg (coeff · 0) h
    simp [ht0] at this
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F F').mpr hsep
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)

end Extension

section Places

variable [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable {y : F'} {t : F} {P : Place k F} {s : P.integers} {P' : Place k' F'}

/-- **`y` is regular above `P`**: a root of `y ^ 2 + t y = s`, where `t` vanishes at `P` and `s`
is regular at `P`, is regular at every place `P'` of `F'` above `P`. -/
theorem mem_integers_of_sq_add_mul_eq (ht : 0 < P.ord t)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    y ∈ P'.integers := by
  subst hP'
  refine P'.mem_integers_of_isIntegral (fun a : (P'.restrict k F).integers ↦ ?_)
    ⟨integralEquation ht s, monic_integralEquation ht, ?_⟩
  · rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F']
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  · rw [← aeval_def, ← aeval_map_algebraMap F, map_integralEquation ht]
    simp [hy]

/-- The residue of a root of `y ^ 2 + t y = s` at a place above `P` is a square root of `s(P)`:
its minimal polynomial over the residue field of `P` is `X ^ 2 - s(P)`. -/
private theorem minpoly_residue_of_sq_add_mul_eq (ht : 0 < (P'.restrict k F).ord t)
    {s : (P'.restrict k F).integers}
    (hs : ∀ a : (P'.restrict k F).ResidueField,
      a ^ 2 ≠ IsLocalRing.residue (P'.restrict k F).integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) :
    minpoly (P'.restrict k F).ResidueField
        (IsLocalRing.residue P'.integers ⟨y, mem_integers_of_sq_add_mul_eq ht hy rfl⟩) =
      X ^ 2 - C (IsLocalRing.residue (P'.restrict k F).integers s) := by
  let yP : P'.integers := ⟨y, mem_integers_of_sq_add_mul_eq ht hy rfl⟩
  let tP : (P'.restrict k F).integers :=
    ⟨t, (P'.restrict k F).mem_integers_iff_ord_nonneg.mpr ht.le⟩
  have ht0 : t ≠ 0 := fun h ↦ by simp [h] at ht
  have htP : IsLocalRing.residue (P'.restrict k F).integers tP = 0 :=
    ((P'.restrict k F).residue_eq_zero_iff_ord_pos (f := tP) ht0).mpr ht
  have heq : yP ^ 2 + algebraMap (P'.restrict k F).integers P'.integers tP * yP =
      algebraMap (P'.restrict k F).integers P'.integers s :=
    Subtype.ext (by simpa [yP, tP] using hy)
  have hroot := congrArg (IsLocalRing.residue P'.integers) heq
  rw [map_add, map_mul, map_pow, ← IsLocalRing.ResidueField.algebraMap_residue, htP, map_zero,
    zero_mul, add_zero, ← IsLocalRing.ResidueField.algebraMap_residue] at hroot
  refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime Nat.prime_two hs)
    ?_ ?_).symm
  · rw [map_sub, map_pow, aeval_X, aeval_C, hroot, sub_self]
  · monicity!

/-- The residue extension at a place above `P` has degree at least two. -/
private theorem two_le_relativeDegree_of_sq_add_mul_eq (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    2 ≤ relativeDegree k F P' := by
  subst hP'
  rw [relativeDegree_def]
  have h := minpoly.natDegree_le (A := (P'.restrict k F).ResidueField)
    (IsLocalRing.residue P'.integers ⟨y, mem_integers_of_sq_add_mul_eq ht hy rfl⟩)
  rwa [minpoly_residue_of_sq_add_mul_eq ht hs hy, natDegree_sub_C, natDegree_X_pow] at h

/-- **The quadratic step is unramified**: if `F' = F(y)` with `y ^ 2 + t y = s`, where `t`
vanishes at `P` and the residue of `s` at `P` is not a square, then every place `P'` of `F'`
above `P` has `e(P' ∣ P) = 1`. -/
theorem ramificationIdx_eq_one_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    ramificationIdx F P' = 1 := by
  have h := ramificationIdx_mul_relativeDegree_le_finrank (k := k) F P'
  rw [finrank_eq_two_of_sq_add_mul_eq hgen ht hs hy] at h
  have := two_le_relativeDegree_of_sq_add_mul_eq ht hs hy hP'
  have := ramificationIdx_pos F P'
  nlinarith

/-- **The quadratic step is inert**: if `F' = F(y)` with `y ^ 2 + t y = s`, where `t` vanishes
at `P` and the residue of `s` at `P` is not a square, then every place `P'` of `F'` above `P`
has `f(P' ∣ P) = 2 = [F' : F]`. -/
theorem relativeDegree_eq_two_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    relativeDegree k F P' = 2 := by
  have h := ramificationIdx_mul_relativeDegree_le_finrank (k := k) F P'
  rw [finrank_eq_two_of_sq_add_mul_eq hgen ht hs hy,
    ramificationIdx_eq_one_of_sq_add_mul_eq hgen ht hs hy hP', one_mul] at h
  exact le_antisymm h (two_le_relativeDegree_of_sq_add_mul_eq ht hs hy hP')

/-- **At most one place lies above `P`**: if `F' = F(y)` with `y ^ 2 + t y = s`, where `t`
vanishes at `P` and the residue of `s` at `P` is not a square, then two places of `F'` above
`P` are equal. -/
theorem subsingleton_setOf_restrict_eq_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) :
    {Q : Place k' F' | Q.restrict k F = P}.Subsingleton := by
  classical
  intro Q hQ Q' hQ'
  by_contra hne
  have h := sum_ramificationIdx_mul_relativeDegree_le_finrank k F P {Q, Q'} (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro P' (rfl | rfl)
    exacts [hQ, hQ'])
  rw [Finset.sum_pair hne, finrank_eq_two_of_sq_add_mul_eq hgen ht hs hy,
    relativeDegree_eq_two_of_sq_add_mul_eq hgen ht hs hy hQ,
    relativeDegree_eq_two_of_sq_add_mul_eq hgen ht hs hy hQ',
    ramificationIdx_eq_one_of_sq_add_mul_eq hgen ht hs hy hQ,
    ramificationIdx_eq_one_of_sq_add_mul_eq hgen ht hs hy hQ'] at h
  omega

section CharTwo

variable [CharP F 2]

/-- **The residue extension is inseparable in characteristic two**: if `y ^ 2 + t y = s`, where
`t` vanishes at `P` and the residue of `s` at `P` is not a square, then at every place `P'`
above `P` the residue field `F'_{P'}` contains the square root of `s(P)`, which is purely
inseparable of degree two over `F_P`. -/
theorem not_isSeparable_residueField_of_sq_add_mul_eq (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    ¬ Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField := by
  subst hP'
  intro hsep
  have : CharP k 2 := (Algebra.charP_iff k F 2).mpr inferInstance
  have : CharP (P'.restrict k F).ResidueField 2 := (Algebra.charP_iff k _ 2).mp inferInstance
  have h := Algebra.IsSeparable.isSeparable (P'.restrict k F).ResidueField
    (IsLocalRing.residue P'.integers ⟨y, mem_integers_of_sq_add_mul_eq ht hy rfl⟩)
  rw [IsSeparable, minpoly_residue_of_sq_add_mul_eq ht hs hy,
    separable_iff_derivative_ne_zero (X_pow_sub_C_irreducible_of_prime Nat.prime_two hs)] at h
  apply h
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, Nat.cast_ofNat,
    CharTwo.two_eq_zero, map_zero, zero_mul]

variable [Algebra.IsSeparable F F']

/-- **The quadratic step has positive different in characteristic two**: if `F' = F(y)` with
`y ^ 2 + t y = s`, where `t` vanishes at `P` and the residue of `s` at `P` is not a square, then
every place `P'` above `P` has `d(P' ∣ P) > 0`, although `e(P' ∣ P) = 1`. -/
theorem differentExponent_pos_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    0 < differentExponent k F P' := by
  have he := ramificationIdx_eq_one_of_sq_add_mul_eq hgen ht hs hy hP'
  refine Nat.pos_of_ne_zero fun hd ↦ not_isSeparable_residueField_of_sq_add_mul_eq ht hs hy hP' ?_
  exact ((isTame_iff_isSeparable_residueField k F P').mp
    ((ramificationIdx_eq_differentExponent_add_one_iff k F P').mp (by rw [he, hd]))).1

/-- **The different of the quadratic step is bounded by the order of `t`** in characteristic
two: if `F' = F(y)` with `y ^ 2 + t y = s`, where `t` vanishes at `P` and the residue of `s` at
`P` is not a square, then every place `P'` above `P` has `d(P' ∣ P) ≤ ord_P t`. -/
theorem differentExponent_le_ord_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : 0 < P.ord t)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    (differentExponent k F P' : ℤ) ≤ P.ord t := by
  have he := ramificationIdx_eq_one_of_sq_add_mul_eq hgen ht hs hy hP'
  have : CharP F' 2 := charP_of_injective_algebraMap (algebraMap F F').injective 2
  subst hP'
  have hord : P'.ord (algebraMap F F' t) = (P'.restrict k F).ord t := by
    rw [ord_algebraMap_restrict k F P', he, Nat.cast_one, one_mul]
  have h2 : (2 : F') * y + algebraMap F F' t = algebraMap F F' t := by
    rw [CharTwo.two_eq_zero, zero_mul, zero_add]
  have hup := differentExponent_le_ord_two_mul_add k F (P' := P') (u := t) (v := s)
    (P'.mem_integers_iff_ord_nonneg.mpr (by omega))
    ((mem_integers_restrict_iff k F P' (s : F)).mp s.2) hgen (by rw [← hy]; ring)
    (by rw [h2]; intro h; simp [h] at hord; omega)
  rwa [h2, hord] at hup

/-- **The different exponent of the quadratic step in characteristic two**: if `F' = F(y)` with
`y ^ 2 + t y = s`, where `t` is a uniformizer at `P` and the residue of `s` at `P` is not a
square, then every place `P'` above `P` has `d(P' ∣ P) = 1`, although `e(P' ∣ P) = 1`. -/
theorem differentExponent_eq_one_of_sq_add_mul_eq (hgen : F⟮y⟯ = ⊤) (ht : P.ord t = 1)
    (hs : ∀ a : P.ResidueField, a ^ 2 ≠ IsLocalRing.residue P.integers s)
    (hy : y ^ 2 + algebraMap F F' t * y = algebraMap F F' s) (hP' : P'.restrict k F = P) :
    differentExponent k F P' = 1 := by
  have hpos := differentExponent_pos_of_sq_add_mul_eq hgen (by omega) hs hy hP'
  have hle := differentExponent_le_ord_of_sq_add_mul_eq hgen (by omega) hs hy hP'
  omega

end CharTwo

end Places

end TauCeti.Place
