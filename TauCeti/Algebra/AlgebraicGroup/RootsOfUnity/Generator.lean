/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Generator.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.AdjoinRoot
import TauCeti.Algebra.Polynomial.XPowSubC
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Norm.FullSetOfSections.AdjoinRoot

/-!
# Generators of `μ_N`

The coordinate ring of `μ_N = D(ℤ/N)` over a commutative ring `R` is the group algebra
`R[Multiplicative (ZMod N)]`. For `N ≠ 0` it is also the classical `R[X]/(X ^ N - 1)`, the standard
generator corresponding to the class of `X` (`TauCeti.RootsOfUnityGroup.adjoinRootEquiv`). Through
this presentation, the criterion for full sets of sections of `R[X]/(g)`
(`TauCeti.isFullSetOfSections_iff_eq_prod_X_sub_C`) describes the Katz–Mazur generators of `μ_N`
(`TauCeti.IsAGenerator`): for a finite monoid `A`, a homomorphism `φ : A → μ_N(R)` is an
`A`-generator if and only if

  `X ^ N - 1 = ∏ a, (X - φ(a))`

in `R[X]`, the points of `μ_N` being read as `N`th roots of unity in `R`.

In characteristic `p` this gives generators which are not injective. The trivial homomorphism
from any monoid of order `p ^ k` is a generator of `μ_{p ^ k}`, since `X ^ (p ^ k) - 1` is
`(X - 1) ^ (p ^ k)`.

The file also proves the generator statements in the example by which Katz and Mazur show that
the converse of their transitivity theorem for generators in an exact sequence
`0 → G₁ → G → G₂ → 0` fails. Over an `𝔽_p`-algebra, let `ζ` be a point of `μ_{p²}` with
`ζ ^ p = 1`. The homomorphism `ℤ/p × ℤ/p → μ_{p²}`, `(a, b) ↦ ζ ^ a`, is a generator of `μ_{p²}`.
In the exact sequence `0 → μ_p → μ_{p²} → μ_p → 0`, whose second map is the `p`th power, it
restricts on `ℤ/p × 0` to `a ↦ ζ ^ a` into `μ_p`, and induces the trivial homomorphism on the
quotient `ℤ/p`. The trivial homomorphism is a generator of `μ_p`, but `a ↦ ζ ^ a` need not be:
over `𝔽_p[X]/(X ^ p - 1)` with `ζ` the class of `X`, it is not, because the sum
`1 + ζ + ⋯ + ζ ^ (p - 1)` of its values is nonzero, while the values of a generator of `μ_p` sum
to `0`, minus the coefficient of `X ^ (p - 1)` in `X ^ p - 1`. Only the three generator statements
are proved here; the exact sequence and the maps relating the three homomorphisms are not
formalized.

## Main results

* `TauCeti.RootsOfUnityGroup.isAGenerator_iff_X_pow_sub_one_eq_prod`: a homomorphism to the points
  of `μ_N` is a generator if and only if `X ^ N - 1` is the product of the `X - φ(a)`.
* `TauCeti.RootsOfUnityGroup.isAGenerator_one_of_card_eq`: in characteristic `p`, the trivial
  homomorphism from a monoid of order `p ^ k` is a generator of `μ_{p ^ k}`.
* `TauCeti.RootsOfUnityGroup.isAGenerator_comp_fst`: over an `𝔽_p`-algebra, for every
  homomorphism `χ : ℤ/p → μ_{p²}(R)`, the homomorphism `(a, b) ↦ χ(a)` from `ℤ/p × ℤ/p` is a
  generator of `μ_{p²}`.
* `TauCeti.RootsOfUnityGroup.not_isAGenerator_of_eq_root`: over `𝔽_p[X]/(X ^ p - 1)`, the
  homomorphism `ℤ/p → μ_p` taking `1` to the class of `X` is not a generator of `μ_p`, and
  `TauCeti.RootsOfUnityGroup.exists_not_isAGenerator` exhibits it.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §1.10 (generators) and §1.11 (generators in exact
  sequences, and the examples 1.11.4–1.11.5).
-/

public section

open Polynomial WithConv

namespace TauCeti.RootsOfUnityGroup

section Generator

variable {R : Type*} [CommRing R] {A : Type*} [Monoid A] [Fintype A]

/-- **Generators of `μ_n`.** For `n ≠ 0`, a homomorphism `φ` from a finite monoid `A` to the points
of `μ_n` is an `A`-generator if and only if `X ^ n - 1 = ∏ a, (X - φ(a))`, where `φ(a)` is read as
an `n`th root of unity through its value on the standard generator. -/
theorem isAGenerator_iff_X_pow_sub_one_eq_prod (n : ℕ) [NeZero n]
    {φ : A →* WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] R)} :
    IsAGenerator φ ↔
      (X ^ n - 1 : R[X]) = ∏ a, (X - C ((φ a).ofConv (MonoidAlgebra.single (generator n) 1))) := by
  rw [isAGenerator_iff, ← isFullSetOfSections_comp_algEquiv_iff (adjoinRootEquiv n),
    isFullSetOfSections_iff_eq_prod_X_sub_C (monic_X_pow_sub_one (NeZero.ne n))]
  simp

/-- **Trivial generators in characteristic `p`.** If `R` has exponential characteristic `p` and the
finite monoid `A` has order `p ^ k`, the trivial homomorphism from `A` is an `A`-generator of
`μ_{p ^ k}`: its values are all `1`, and `X ^ (p ^ k) - 1 = (X - 1) ^ (p ^ k)`. -/
theorem isAGenerator_one_of_card_eq (p : ℕ) [ExpChar R p] {k : ℕ} (hA : Fintype.card A = p ^ k) :
    IsAGenerator (1 : A →* WithConv (MonoidAlgebra R (Multiplicative (ZMod (p ^ k))) →ₐ[R] R)) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (expChar_pos R p).ne'⟩
  rw [isAGenerator_iff_X_pow_sub_one_eq_prod]
  simp [hA, sub_pow_expChar_pow]

/-- **A generator of `μ_{p²}` whose restriction can fail to be a generator** (Katz–Mazur 1.11.4).
Over a ring of characteristic `p`, for every homomorphism `χ : ℤ/p → μ_{p²}(R)`, the homomorphism
`(a, b) ↦ χ(a)` from `ℤ/p × ℤ/p` is a generator of `μ_{p²}`. Writing `ζ = χ(1)`, a point of
`μ_{p²}` with `ζ ^ p = 1`, this is `(a, b) ↦ ζ ^ a`; it is a generator because
`∏ a, (X - ζ ^ a) ^ p = ∏ a, (X ^ p - 1) = X ^ (p²) - 1` in characteristic `p`. Its restriction
`a ↦ ζ ^ a` to `ℤ/p × 0`, into `μ_p`, need not be a generator: `not_isAGenerator_of_eq_root` gives
an example. -/
theorem isAGenerator_comp_fst (p : ℕ) [Fact p.Prime] [CharP R p]
    (χ : Multiplicative (ZMod p) →*
      WithConv (MonoidAlgebra R (Multiplicative (ZMod (p ^ 2))) →ₐ[R] R)) :
    IsAGenerator (χ.comp (MonoidHom.fst (Multiplicative (ZMod p)) (Multiplicative (ZMod p)))) := by
  rw [isAGenerator_iff_X_pow_sub_one_eq_prod, Fintype.prod_prod_type]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, Finset.prod_const, Finset.card_univ,
    Fintype.card_multiplicative, ZMod.card, sub_pow_char, ← C_pow]
  -- every value of `χ` is a `p`th root of unity, since `ℤ/p` is killed by `p`
  have hp (a : Multiplicative (ZMod p)) :
      (χ a).ofConv (MonoidAlgebra.single (generator (p ^ 2)) 1) ^ p = 1 := by
    have ha : a ^ p = 1 := by
      simpa [Fintype.card_multiplicative, ZMod.card] using pow_card_eq_one (x := a)
    rw [← ofConv_pow_apply_single_generator, ← map_pow, ha, map_one]
    simp
  simp only [hp, map_one, Finset.prod_const, Finset.card_univ, Fintype.card_multiplicative,
    ZMod.card, sub_pow_char, one_pow, ← pow_mul, sq]

/-- **A non-generator of `μ_p`** (Katz–Mazur 1.11.4–1.11.5). Over `R = 𝔽_p[X]/(X ^ p - 1)`, let
`χ : ℤ/p → μ_p(R)` take `1` to the class `θ` of `X`, so that `χ(a) = θ ^ a`. Then `χ` is not a
generator of `μ_p`: a generator would give `X ^ p - 1 = ∏ a, (X - θ ^ a)`, but the coefficients of
`X ^ (p - 1)` differ, the right-hand one being `-(1 + θ + ⋯ + θ ^ (p - 1)) ≠ 0`. For `ζ = θ`, the
homomorphism `(a, b) ↦ ζ ^ a` into `μ_{p²}` is a generator by `isAGenerator_comp_fst`; this is
the half of Katz and Mazur's example in which the subgroup term fails to be a generator. -/
theorem not_isAGenerator_of_eq_root (p : ℕ) [Fact p.Prime]
    {χ : Multiplicative (ZMod p) →* WithConv (MonoidAlgebra (AdjoinRoot (X ^ p - 1 : (ZMod p)[X]))
      (Multiplicative (ZMod p)) →ₐ[AdjoinRoot (X ^ p - 1 : (ZMod p)[X])]
        AdjoinRoot (X ^ p - 1 : (ZMod p)[X]))}
    (hχ : (χ (generator p)).ofConv (MonoidAlgebra.single (generator p) 1) = AdjoinRoot.root _) :
    ¬ IsAGenerator χ := by
  have hp : p.Prime := Fact.out
  -- the value of `χ` at `a` is the `a`th power of the class `θ` of `X`
  have hval (a : Multiplicative (ZMod p)) : (χ a).ofConv (MonoidAlgebra.single (generator p) 1) =
      AdjoinRoot.root _ ^ (Multiplicative.toAdd a).val := by
    rw [← generator_pow_val p a, map_pow, ofConv_pow_apply_single_generator, hχ,
      generator_pow_val]
  rw [isAGenerator_iff_X_pow_sub_one_eq_prod]
  intro h
  simp only [hval] at h
  -- the coefficient of `X ^ (p - 1)` is `0` on the left and `-(1 + θ + ⋯ + θ ^ (p - 1))` on the
  -- right
  have hcard : (Finset.univ : Finset (Multiplicative (ZMod p))).card = p := by simp
  have hcoeff := prod_X_sub_C_coeff_card_pred Finset.univ
    (fun a : Multiplicative (ZMod p) ↦ AdjoinRoot.root (X ^ p - 1 : (ZMod p)[X]) ^
      (Multiplicative.toAdd a).val) (by rw [hcard]; exact hp.pos)
  have h₁ : p - 1 ≠ p := by have := hp.pos; lia
  have h₂ : p - 1 ≠ 0 := by have := hp.two_le; lia
  rw [hcard, ← h] at hcoeff
  simp only [coeff_sub, coeff_X_pow, coeff_one, h₁, h₂, ite_false, sub_zero, zero_eq_neg] at hcoeff
  -- reindexed by `ZMod.val`, the sum is the class of `1 + X + ⋯ + X ^ (p - 1)`
  rw [Finset.sum_nbij' (fun a ↦ (Multiplicative.toAdd a).val)
    (fun k ↦ Multiplicative.ofAdd (k : ZMod p))
    (g := fun k ↦ AdjoinRoot.root (X ^ p - 1 : (ZMod p)[X]) ^ k) (t := Finset.range p)
    (by simp [ZMod.val_lt]) (by simp) (by simp) (by simp +contextual [Nat.mod_eq_of_lt])
    (by simp)] at hcoeff
  have hndvd := not_X_pow_sub_C_dvd_geom_sum (1 : ZMod p) hp.ne_zero
  rw [C_1] at hndvd
  refine hndvd ?_
  rw [← AdjoinRoot.mk_eq_zero, map_sum]
  simpa using hcoeff

/-- The homomorphism `ℤ/p → μ_p` of `not_isAGenerator_of_eq_root` exists: over
`𝔽_p[X]/(X ^ p - 1)` there is a homomorphism `a ↦ θ ^ a` from `ℤ/p` to the points of `μ_p`, where
`θ` is the class of `X`, and it is not a generator of `μ_p`. -/
theorem exists_not_isAGenerator (p : ℕ) [Fact p.Prime] :
    ∃ χ : Multiplicative (ZMod p) →* WithConv (MonoidAlgebra (AdjoinRoot (X ^ p - 1 : (ZMod p)[X]))
      (Multiplicative (ZMod p)) →ₐ[AdjoinRoot (X ^ p - 1 : (ZMod p)[X])]
        AdjoinRoot (X ^ p - 1 : (ZMod p)[X])),
      (χ (generator p)).ofConv (MonoidAlgebra.single (generator p) 1) = AdjoinRoot.root _ ∧
        ¬ IsAGenerator χ := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ζ : rootsOfUnity p (AdjoinRoot (X ^ p - 1 : (ZMod p)[X])) :=
    rootsOfUnity.mkOfPowEq _ (AdjoinRoot.root_X_pow_sub_one_pow p)
  -- the character `a ↦ ζ ^ a` of `ℤ/p`, whose values are `p`th roots of unity since `ℤ/p` is
  -- killed by `p`
  let ψ := ((characterMulEquivRootsOfUnity p).symm ζ).codRestrict (rootsOfUnity p _) fun a ↦ by
    have ha : a ^ p = 1 := by
      simpa [Fintype.card_multiplicative, ZMod.card] using pow_card_eq_one (x := a)
    rw [mem_rootsOfUnity, ← map_pow, ha, map_one]
  let χ := (pointsMulEquiv (R := AdjoinRoot (X ^ p - 1 : (ZMod p)[X])) p).symm.toMonoidHom.comp ψ
  have hχ : (χ (generator p)).ofConv (MonoidAlgebra.single (generator p) 1) =
      AdjoinRoot.root _ := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, pointsMulEquiv_symm_apply_single_generator,
      MonoidHom.codRestrict_apply, Subgroup.coe_mk,
      characterMulEquivRootsOfUnity_symm_apply_generator, rootsOfUnity.coe_mkOfPowEq]
  exact ⟨χ, hχ, not_isAGenerator_of_eq_root p hχ⟩

end Generator

end TauCeti.RootsOfUnityGroup
