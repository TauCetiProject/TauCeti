/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Signature
public import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.Degree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Signature
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Cofinite
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Count
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Gamma1
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.Basic
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.One
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.Zero

/-!
# The genus formula for modular curves

For a finite-index subgroup `H ≤ SL(2, ℤ)`, let `X(H)` be the compactified quotient of the upper
half-plane by the effective image of `H` in `PSL(2, ℝ)`, a compact Riemann surface. Write
`d = [SL(2, ℤ) : ±H]` for the degree of `X(H) → X(1)`, `ε₂` and `ε₃` for the numbers of elliptic
points of orders `2` and `3`, and `ε∞` for the number of cusps. The topological genus `g` of
`X(H)` is then given by

`g = 1 + d / 12 - ε₂ / 4 - ε₃ / 3 - ε∞ / 2`

(Diamond–Shurman, Theorem 3.1.1). These are the invariants entering the dimension formulas for
spaces of modular forms on `H`.

The formula is Riemann–Hurwitz for `X(H) → X(1)`
(`TauCeti.Fuchsian.two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_ramificationDegree`),
with the ramification expressed through elliptic orders and cusp counts
(`TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub`). The level-one
curve has genus `0`, one cusp, and elliptic orbits of orders `2` and `3`. The remaining input is
that every elliptic point of `H` has order `2` or `3`, being a translate of `i` or `ρ`, so that
the elliptic defect `∑ (1 - 1 / m)` of `H` is `ε₂ / 2 + 2 ε₃ / 3`.

Specializing the counts already computed gives the genus of `X₀(N)`, `X₁(N)` and `X(N)`. For
example `X₀(11)` has genus `1`, and `X₁(13)` has genus `2`.

## Main results

* `Subgroup.mem_ellipticOrbits_map_sl2zToPSL2R_iff`: the elliptic orbits of `H` are those of
  order `2` or `3`.
* `Subgroup.finsum_mem_ellipticOrbits_map_sl2zToPSL2R`: the elliptic defect of `H` is
  `ε₂ / 2 + 2 ε₃ / 3`.
* `Subgroup.twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add`: the genus formula in the
  integral form `12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + d`.
* `Subgroup.genus_compactifiedQuotient_map_sl2zToPSL2R_eq`: the genus formula
  `g = 1 + d / 12 - ε₂ / 4 - ε₃ / 3 - ε∞ / 2`.
* `CongruenceSubgroup.twelve_mul_genus_compactifiedQuotient_Gamma0_add`: the genus of `X₀(N)`.
* `CongruenceSubgroup.twenty_four_mul_genus_compactifiedQuotient_Gamma1_add`: the genus of
  `X₁(N)` for `N ≥ 4`.
* `CongruenceSubgroup.twelve_mul_genus_compactifiedQuotient_Gamma_add`: the genus of `X(N)` for
  `N ≥ 2`.
* `CongruenceSubgroup.genus_compactifiedQuotient_Gamma0_eleven` and
  `CongruenceSubgroup.genus_compactifiedQuotient_Gamma1_thirteen`: `X₀(11)` has genus `1` and
  `X₁(13)` has genus `2`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, Theorem 3.1.1 and §§3.7–3.9.
-/

public noncomputable section

open MulAction UpperHalfPlane TauCeti TauCeti.RiemannSurface
open scoped MatrixGroups

namespace Subgroup

variable (H : Subgroup SL(2, ℤ))

/-- **The elliptic orbits of a subgroup of `SL(2, ℤ)`** are its orbits with stabilizer of order
`2` or `3` in the effective image: every elliptic point is a translate of `i` or of `ρ`. -/
theorem mem_ellipticOrbits_map_sl2zToPSL2R_iff (q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ) :
    q ∈ (H.map sl2zToPSL2R).ellipticOrbits ↔
      cardStabilizerOnOrbit q = 2 ∨ cardStabilizerOnOrbit q = 3 := by
  induction q using Quotient.inductionOn with
  | h z =>
    rw [quotientMk_mem_ellipticOrbits_iff, cardStabilizerOnOrbit_mk, mem_freeLocus,
      ← card_eq_one]
    refine ⟨fun h ↦ ?_, fun h h1 ↦ by omega⟩
    rcases H.exists_smul_eq_of_card_stabilizer_ne_one h with ⟨_, _, h2⟩ | ⟨_, _, h3⟩
    exacts [Or.inl h2, Or.inr h3]

variable [H.FiniteIndex]

/-- For a finite-index subgroup, there are finitely many orbits of stabilizer order `2` or `3`. -/
private theorem finite_setOf_cardStabilizerOnOrbit_eq {m : ℕ} (hm : m = 2 ∨ m = 3) :
    {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ | cardStabilizerOnOrbit q = m}.Finite :=
  H.isCofinite_map_sl2zToPSL2R.finite_ellipticOrbits.subset fun q hq ↦
    (H.mem_ellipticOrbits_map_sl2zToPSL2R_iff q).mpr (hq ▸ hm)

/-- **The elliptic defect of a finite-index subgroup of `SL(2, ℤ)`.** Summing `1 - 1 / m` over the
elliptic orbits, of orders `m = 2` and `m = 3`, gives `ε₂ / 2 + 2 ε₃ / 3`. -/
theorem finsum_mem_ellipticOrbits_map_sl2zToPSL2R :
    ∑ᶠ q ∈ (H.map sl2zToPSL2R).ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} / 2 +
      2 * Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} /
        3 := by
  have h2 := H.finite_setOf_cardStabilizerOnOrbit_eq (Or.inl rfl)
  have h3 := H.finite_setOf_cardStabilizerOnOrbit_eq (Or.inr rfl)
  have hdisj : Disjoint {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ | cardStabilizerOnOrbit q = 2}
      {q | cardStabilizerOnOrbit q = 3} :=
    Set.disjoint_left.mpr fun q h2 h3 ↦ by simp_all
  -- on the orbits of order `m` the summand is the constant `1 - 1 / m`
  have hconst (m : ℕ) : ∑ᶠ q ∈ {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ |
      cardStabilizerOnOrbit q = m}, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      ∑ᶠ q ∈ {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ | cardStabilizerOnOrbit q = m},
        (1 - (m : ℝ)⁻¹) :=
    finsum_mem_congr rfl fun q hq ↦ by rw [show cardStabilizerOnOrbit q = m from hq]
  rw [show (H.map sl2zToPSL2R).ellipticOrbits =
      {q | cardStabilizerOnOrbit q = 2} ∪ {q | cardStabilizerOnOrbit q = 3} from
      Set.ext H.mem_ellipticOrbits_map_sl2zToPSL2R_iff, finsum_mem_union hdisj h2 h3, hconst,
    hconst, finsum_mem_eq_finite_toFinset_sum _ h2, finsum_mem_eq_finite_toFinset_sum _ h3,
    Finset.sum_const, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ h2,
    ← Set.ncard_eq_toFinset_card _ h3, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  simp only [nsmul_eq_mul, Set.coe_ofPred]
  ring

/-- The modular curve `X(H)` of a finite-index subgroup `H ≤ SL(2, ℤ)` has finite CW type, so its
Euler characteristic and topological genus are defined. -/
instance finiteCWType_compactifiedQuotient_map_sl2zToPSL2R :
    FiniteCWType (H.map sl2zToPSL2R).CompactifiedQuotient :=
  H.isCofinite_map_sl2zToPSL2R.finiteCWType_compactifiedQuotient

/-- **The genus formula for modular curves** (Diamond–Shurman, Theorem 3.1.1), in integral form.
For a finite-index subgroup `H ≤ SL(2, ℤ)`, the genus `g` of `X(H)`, its numbers `ε₂`, `ε₃` of
elliptic points of orders `2` and `3`, and its number `ε∞` of cusps satisfy
`12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + d`, where `d = [SL(2, ℤ) : ±H]` is the degree of
`X(H) → X(1)`. -/
theorem twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add :
    12 * genus (H.map sl2zToPSL2R).CompactifiedQuotient +
        3 * Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} +
        4 * Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} +
        6 * Nat.card (H.map sl2zToPSL2R).CuspOrbit =
      12 + H.withCenter.index := by
  have h := H.map_sl2zToPSL2R_le_range_psl2zToPSL2R
  have hΓ := ModularGroup.isCofinite_psl2zToPSL2RRange
  -- Riemann–Hurwitz for `X(H) → X(1)`, with `X(1)` of genus `0`
  have hRH : (2 * genus (H.map sl2zToPSL2R).CompactifiedQuotient - 2 : ℝ) =
      H.withCenter.index * (2 * 0 - 2) + ramificationDegree (compactifiedQuotientMap h) := by
    have := Fuchsian.two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_ramificationDegree
      h hΓ
    rw [ModularGroup.genus_compactifiedQuotient, ← relIndex, H.relIndex_map_sl2zToPSL2R] at this
    exact_mod_cast this
  -- the ramification through cusps and elliptic orders, `X(1)` having one cusp and defect `7 / 6`
  have hR := Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub h hΓ
  rw [ModularGroup.finsum_mem_ellipticOrbits_psl2zToPSL2RRange,
    H.finsum_mem_ellipticOrbits_map_sl2zToPSL2R, Nat.card_unique, ← relIndex,
    H.relIndex_map_sl2zToPSL2R] at hR
  rw [hR] at hRH
  have : (12 * genus (H.map sl2zToPSL2R).CompactifiedQuotient +
        3 * Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} +
        4 * Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} +
        6 * Nat.card (H.map sl2zToPSL2R).CuspOrbit : ℝ) = 12 + H.withCenter.index := by
    push_cast at hRH
    linarith
  exact_mod_cast this

/-- **The genus formula for modular curves** (Diamond–Shurman, Theorem 3.1.1). For a finite-index
subgroup `H ≤ SL(2, ℤ)`, the genus of `X(H)` is `1 + d / 12 - ε₂ / 4 - ε₃ / 3 - ε∞ / 2`, where
`d = [SL(2, ℤ) : ±H]` is the degree of `X(H) → X(1)`, `ε₂` and `ε₃` count the elliptic points of
orders `2` and `3`, and `ε∞` counts the cusps. -/
theorem genus_compactifiedQuotient_map_sl2zToPSL2R_eq :
    (genus (H.map sl2zToPSL2R).CompactifiedQuotient : ℚ) =
      1 + H.withCenter.index / 12 -
        Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} /
          4 -
        Nat.card {q : orbitRel.Quotient (H.map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} /
          3 -
        Nat.card (H.map sl2zToPSL2R).CuspOrbit / 2 := by
  have h : (_ : ℚ) = _ := congrArg (Nat.cast : ℕ → ℚ)
    H.twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add
  push_cast at h
  linarith

end Subgroup

namespace CongruenceSubgroup

variable (N : ℕ) [NeZero N]

/-- **The genus of `X₀(N)`** (Diamond–Shurman, §3.9): `12 g + 3 ε₂ + 4 ε₃ + 6 ε∞` equals
`12 + [SL(2, ℤ) : Γ₀(N)]`, where `ε₂` and `ε₃` count the roots of `x² + 1` and of `x² - x + 1`
modulo `N`, and `ε∞ = ∑_{g ∣ N} φ(gcd(g, N / g))`. -/
theorem twelve_mul_genus_compactifiedQuotient_Gamma0_add :
    12 * genus ((Gamma0 N).map sl2zToPSL2R).CompactifiedQuotient +
        3 * Nat.card {x : ZMod N // x ^ 2 + 1 = 0} +
        4 * Nat.card {x : ZMod N // x ^ 2 - x + 1 = 0} +
        6 * ∑ g ∈ N.divisors, Nat.totient (Nat.gcd g (N / g)) =
      12 + (Gamma0 N).index := by
  rw [← card_orderTwoElliptic_Gamma0, ← card_orderThreeElliptic_Gamma0, ← card_cuspOrbit_Gamma0,
    (Gamma0 N).twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add,
    le_antisymm (withCenter_le_Gamma0 le_rfl) (Gamma0 N).le_withCenter]

/-- **The genus of `X₁(N)` for `N ≥ 4`**: then `X₁(N)` has no elliptic points and
`-I ∉ Γ₁(N)`, so `24 g + 12 ε∞ = 24 + [SL(2, ℤ) : Γ₁(N)]`. -/
theorem twenty_four_mul_genus_compactifiedQuotient_Gamma1_add (hN : 4 ≤ N) :
    24 * genus ((Gamma1 N).map sl2zToPSL2R).CompactifiedQuotient +
        12 * Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit =
      24 + (Gamma1 N).index := by
  have h := (Gamma1 N).twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add
  have hneg : (-1 : SL(2, ℤ)) ∉ Gamma1 N := fun h ↦ by
    have := Nat.le_of_dvd two_pos (neg_one_mem_Gamma1_iff.mp h)
    omega
  rw [card_orderTwoElliptic_Gamma1, card_orderThreeElliptic_Gamma1] at h
  simp only [show ¬(N = 1 ∨ N = 2) by omega, show ¬(N = 1 ∨ N = 3) by omega, ↓reduceIte] at h
  rw [Matrix.SpecialLinearGroup.index_eq_two_mul_index_withCenter_of_neg_one_notMem hneg]
  omega

/-- **The genus of `X(N)` for `N ≥ 2`**: then `X(N)` has no elliptic points and all its cusps have
width `N`, so `12 g + 6 ε∞ = 12 + N ε∞`, that is, `g = 1 + (N - 6) ε∞ / 12`. -/
theorem twelve_mul_genus_compactifiedQuotient_Gamma_add (hN : 2 ≤ N) :
    12 * genus ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient +
        6 * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit =
      12 + N * Nat.card ((Gamma N).map sl2zToPSL2R).CuspOrbit := by
  have h := (Gamma N).twelve_mul_genus_compactifiedQuotient_map_sl2zToPSL2R_add
  rw [card_orderTwoElliptic_Gamma, card_orderThreeElliptic_Gamma, ← mul_card_cuspOrbit_Gamma] at h
  simp only [show N ≠ 1 by omega, ↓reduceIte] at h
  omega

/-- **`X₀(11)` has genus `1`**: `d = 12`, `ε₂ = ε₃ = 0` and `ε∞ = 2`, so `g = 1 + 1 - 1`. -/
theorem genus_compactifiedQuotient_Gamma0_eleven :
    genus ((Gamma0 11).map sl2zToPSL2R).CompactifiedQuotient = 1 := by
  have h := twelve_mul_genus_compactifiedQuotient_Gamma0_add 11
  have hidx := Gamma0_index_mul_prod_primeFactors (N := 11)
  rw [Nat.Prime.primeFactors (by decide : Nat.Prime 11), Finset.prod_singleton,
    Finset.prod_singleton] at hidx
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have h2 : Fintype.card {x : ZMod 11 // x ^ 2 + 1 = 0} = 0 := by decide
  have h3 : Fintype.card {x : ZMod 11 // x ^ 2 - x + 1 = 0} = 0 := by decide
  have hc : ∑ g ∈ Nat.divisors 11, Nat.totient (Nat.gcd g (11 / g)) = 2 := by decide
  rw [h2, h3, hc] at h
  omega

/-- **`X₁(13)` has genus `2`**: `[SL(2, ℤ) : Γ₁(13)] = 168`, there are `12` cusps and no elliptic
points, so `g = 1 + 7 - 6`. Using the index `168` in place of the degree `84` would give `9`. -/
theorem genus_compactifiedQuotient_Gamma1_thirteen :
    genus ((Gamma1 13).map sl2zToPSL2R).CompactifiedQuotient = 2 := by
  have h := twenty_four_mul_genus_compactifiedQuotient_Gamma1_add 13 (by norm_num)
  have hc := card_cuspOrbit_Gamma1 (N := 13) (by norm_num) (by norm_num)
  have hidx0 := Gamma0_index_mul_prod_primeFactors (N := 13)
  rw [Nat.Prime.primeFactors (by decide : Nat.Prime 13), Finset.prod_singleton,
    Finset.prod_singleton] at hidx0
  have hsum : ∑ g ∈ Nat.divisors 13, Nat.totient g * Nat.totient (13 / g) = 24 := by decide
  have hunits : Nat.card (ZMod 13)ˣ = 12 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (by decide : Nat.Prime 13)]
  rw [Gamma1_index, hunits] at h
  omega

end CongruenceSubgroup
