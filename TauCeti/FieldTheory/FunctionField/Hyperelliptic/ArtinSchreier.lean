/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ArtinSchreier.Genus
-- Proof-only: a separable quadratic extension in characteristic two is Artin–Schreier.
import TauCeti.FieldTheory.IntermediateField.Quadratic
-- Proof-only: the different of a separable quadratic extension of `k(x)` has degree `2g + 2`.
import TauCeti.FieldTheory.FunctionField.Hyperelliptic.BranchPlaces

/-!
# Hyperelliptic function fields in characteristic two

Let `F / k` be an algebraic function field with exact constants, `k` of characteristic two, and
`x ∈ F` transcendental with `F / k(x)` separable of degree two, as for a hyperelliptic function
field (`TauCeti.IsHyperellipticFunctionField`). Away from characteristic two such a field is
`k(x, y)` with `y ^ 2 = f(x)`, and its genus and ramified places are read off `f`
(`TauCeti.genus_eq_of_sq_eq`, `TauCeti.Place.one_lt_ramificationIdx_iff_of_sq_eq`). In
characteristic two square roots generate only inseparable extensions, and the model is an
Artin–Schreier one instead: `F = k(x, y)` with `y ^ 2 + y = u` for some `u ∈ k(x)`, by
`IntermediateField.exists_sq_sub_self_eq_algebraMap_adjoin_simple_eq_top_of_finrank_eq_two`.
Since `y ^ 2 + y = y ^ 2 - y` in characteristic two, the statements below use the form
`y ^ 2 - y = u` of the general Artin–Schreier theory.

The ramification of `F / k(x)` is then wild, and it is read off *reduced* representatives of the
class of `u` modulo `{w ^ 2 - w}`. Let `S` be a set of places of `k(x)` such that at each
`P ∈ S` some `u - (w ^ 2 - w)` has a pole of odd order `m_P`, while at every place outside `S`
some `u - (w ^ 2 - w)` is regular. Then the places of `F` ramified over `k(x)` are exactly those
over `S` (`TauCeti.Place.one_lt_ramificationIdx_iff_restrict_mem_of_pow_sub_self_eq`), each with
ramification index two and different exponent `m_P + 1`, and the Hurwitz genus formula over the
genus-zero field `k(x)` becomes

`2g + 2 = ∑_{P ∈ S} (m_P + 1) deg P`.

A reduced representative is guaranteed only at a place with perfect residue field, so the
general statements take the representatives as hypotheses. Over a perfect constant field every
residue field is perfect, and the model, the representatives and the genus formula exist
unconditionally.

## Main results

* `TauCeti.two_mul_genus_add_two_eq_sum_of_sq_sub_self_eq`: `2g + 2 = ∑_{P ∈ S} (m_P + 1) deg P`.
* `TauCeti.exists_sq_sub_self_eq_and_two_mul_genus_add_two_eq_sum`: over a perfect constant
  field, `F = k(x, y)` with `y ^ 2 - y = u ∈ k(x)`, reduced representatives of `u` exist at every
  place, and the genus formula holds.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8, Theorem 3.4.13 and Section VI.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharP k 2] {x : F}

/-- **The genus of `y ^ 2 + y = u` over `k(x)`** in characteristic two: for `F / k` with exact
constants and `[F : k(x)] = 2`, if `S` is a finite set of places of `k(x)` at each of which some
`u - (w ^ 2 - w)` has a pole of odd order `m P`, while at every other place some
`u - (w ^ 2 - w)` is regular, then `2g + 2 = ∑_{P ∈ S} (m P + 1) deg P`.

This is the Hurwitz genus formula over `k(x)`, of genus zero, with the Artin–Schreier different
exponents `m P + 1`. -/
theorem two_mul_genus_add_two_eq_sum_of_sq_sub_self_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) {y : F} {u : k⟮x⟯} (hgen : k⟮x⟯⟮y⟯ = ⊤)
    (hy : y ^ 2 - y = algebraMap k⟮x⟯ F u) (S : Finset (Place k k⟮x⟯)) (m : Place k k⟮x⟯ → ℕ)
    (hpole : ∀ P ∈ S, ∃ w : k⟮x⟯, P.ord (u - (w ^ 2 - w)) = -(m P : ℤ) ∧
      ¬ (2 : ℤ) ∣ P.ord (u - (w ^ 2 - w)))
    (hreg : ∀ P ∉ S, ∃ w : k⟮x⟯, u - (w ^ 2 - w) ∈ P.integers) :
    2 * (genus k F : ℤ) + 2 = ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  have : CharP k⟮x⟯ 2 := charP_of_injective_algebraMap' k 2
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F
    (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  -- The different has degree `2g + 2` by Hurwitz, and `∑ (m P + 1) deg P` by its local
  -- Artin–Schreier exponents.
  have hHurwitz := degree_different_adjoin hF hex hx hdeg
  have hlocal := Divisor.finrank_mul_degree_different_of_pow_sub_self_eq
    hx.isFunctionField_adjoin hF 2 hgen hy S m hpole hreg
  rw [Module.finrank_self, hHurwitz] at hlocal
  push_cast at hlocal
  linarith

/-- **The Artin–Schreier model of a separable quadratic extension of `k(x)`** over a perfect
field of characteristic two (the characteristic-two counterpart of Stichtenoth,
Proposition 6.2.3): if `F / k` has exact constants and `F / k(x)` is separable of degree two,
then `F = k(x, y)` with `y ^ 2 - y = u ∈ k(x)`, there is a finite set `S` of places of `k(x)` at
each of which some `u - (w ^ 2 - w)` has a pole of odd order `m P`, while at every other place
some `u - (w ^ 2 - w)` is regular, and `2g + 2 = ∑_{P ∈ S} (m P + 1) deg P`. The places of `F`
ramified over `k(x)` are those over `S`
(`TauCeti.Place.one_lt_ramificationIdx_iff_restrict_mem_of_pow_sub_self_eq`). -/
theorem exists_sq_sub_self_eq_and_two_mul_genus_add_two_eq_sum [PerfectField k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    (hdeg : Module.finrank k⟮x⟯ F = 2) [Algebra.IsSeparable k⟮x⟯ F] :
    ∃ (y : F) (u : k⟮x⟯), k⟮x⟯⟮y⟯ = ⊤ ∧ y ^ 2 - y = algebraMap k⟮x⟯ F u ∧
      ∃ (S : Finset (Place k k⟮x⟯)) (m : Place k k⟮x⟯ → ℕ),
        (∀ P ∈ S, ∃ w : k⟮x⟯, P.ord (u - (w ^ 2 - w)) = -(m P : ℤ) ∧
          ¬ (2 : ℤ) ∣ P.ord (u - (w ^ 2 - w))) ∧
        (∀ P ∉ S, ∃ w : k⟮x⟯, u - (w ^ 2 - w) ∈ P.integers) ∧
        2 * (genus k F : ℤ) + 2 = ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  have : CharP k⟮x⟯ 2 := charP_of_injective_algebraMap' k 2
  obtain ⟨y, ⟨u, hy⟩, hgen⟩ :=
    IntermediateField.exists_sq_sub_self_eq_algebraMap_adjoin_simple_eq_top_of_finrank_eq_two
      (K := k⟮x⟯) hdeg
  obtain ⟨S, m, hpole, hreg⟩ :=
    exists_reduced_artinSchreier_representatives hx.isFunctionField_adjoin 2 u
  exact ⟨y, u, hgen, hy, S, m, hpole, hreg,
    two_mul_genus_add_two_eq_sum_of_sq_sub_self_eq hF hex hx hdeg hgen hy S m hpole hreg⟩

end TauCeti
