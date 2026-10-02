/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

import Mathlib.RingTheory.LocalRing.Basic
import TauCeti.Algebra.Ring.TwoPowMulThreePow
import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
import TauCeti.NumberTheory.DedekindDomain.FiniteApproximation

/-!
# Kraus's criterion: which pairs of invariants come from an integral equation

A pair `(c₄, c₆)` in a field `K` where `2` and `3` are invertible, with `c₄³ ≠ c₆²`, is the
pair of `c`-invariants of exactly one Weierstrass equation up to a change of variables with
`u = 1`, namely `ofCInvariants c₄ c₆ : y² = x³ - (c₄/48)x - c₆/864`. Given a commutative ring
`R` with an algebra map to `K` — a localisation `𝒪_{K,v}` of a ring of integers, in the
application — the question
Kraus answers is a different one: is there an equation whose coefficients come from `R` and whose
invariants are `c₄` and `c₆` **on the nose**? Integrality of `c₄`, `c₆` and `Δ` is necessary but
not sufficient, and what is missing is visible only at the residue characteristics `2` and `3`,
where the coefficients `a₁`, `a₂`, `a₃` of the sought equation have to absorb the denominators of
`ofCInvariants c₄ c₆`.

This file states that obstruction as Kraus's local condition and proves it exact: over a local
ring the condition holds precisely when an integral equation with those invariants exists. Over a
Dedekind domain `O` with fraction field `K` the local conditions at all height-one primes are
then shown to patch: they hold everywhere exactly when a single equation with coefficients in `O`
has invariants `c₄` and `c₆`.
Because every equation is the `(b₂/12, a₁/2, a₃/2)`-transform of the canonical one
(`WeierstrassCurve.smul_ofCInvariants`), the auxiliary data of the criterion is a candidate for
those coefficients — a single `b₂` above `3`, where completing the square is free, and a pair
`(a₁, a₃)` above `2`, where completing the cube is free.

## Main definitions

* `TauCeti.HasKrausThreeWitness`: some `b₂ ∈ R` makes the `(b₂/12, 0, 0)`-transform of
  `ofCInvariants c₄ c₆` integral.
* `TauCeti.HasKrausTwoWitness`: some `a₁, a₃ ∈ R` make the `(a₁²/12, a₁/2, a₃/2)`-transform of
  `ofCInvariants c₄ c₆` integral. Each triple specialises the general prescription
  `(b₂/12, a₁/2, a₃/2)`: the three-witness sets `a₁ = a₃ = 0`, while the two-witness sets
  `a₂ = 0`, so `b₂ = a₁²`.
* `TauCeti.KrausLocalCondition`: integrality of `c₄`, `c₆` and `Δ`, nonvanishing of `Δ`, and the
  two witness conditions, each imposed only when the corresponding numeral is a nonunit.
* `TauCeti.KrausGlobalCondition`: Kraus's local condition at the localisation of a Dedekind
  domain at every height-one prime.

## Main results

* `TauCeti.krausLocalCondition_iff_exists_integralModel`: over a local ring the condition holds
  exactly when some Weierstrass equation with coefficients in `R` has `c`-invariants `c₄` and
  `c₆` and nonzero discriminant.
* `TauCeti.isIntegral_ofCInvariants`: where `6` is a unit and `c₄`, `c₆` lie in the image of `R`,
  the canonical equation is itself integral, so no auxiliary data is needed;
* `TauCeti.krausLocalCondition_of_isUnit_six`: consequently the condition is automatic there,
  given only the integrality and nonvanishing of the invariants.
* `TauCeti.krausGlobalCondition_iff_exists_integralModel`: over a Dedekind domain with at least
  one height-one prime, the global condition holds exactly when some Weierstrass equation with
  coefficients in `O` has `c`-invariants `c₄` and `c₆` and nonzero discriminant.

## Patching the local witnesses

Every witness is a change of variables `(B/12, A/2, G/2)` with `u = 1` and `A, B, G` in the local
ring. Two such triples give the same integrality as soon as the second is congruent to the first
modulo `12`, after the correction `G ↦ G + A·(b - B)/12` of the last entry. The change of
variables between the two transforms is then `((b - B)/12, (a - A)/2, (g - G - A(b - B)/12)/2)`,
which has coefficients in the local ring. A single modulus therefore serves the primes above `2`
and above `3` alike, and at the remaining primes `12` is a unit. Approximating the local
`A`, `B` and the corrected `G` modulo `12` by elements of `O`
(`TauCeti.DedekindDomain.exists_forall_sub_mem_span_singleton_localizationAtPrime`) produces
one global change of variables.

## Provenance

Not ported. The criterion and its local auxiliary conditions follow Kraus's paper below; the
reduction to a single change of variables off the canonical equation is this file's own.

## References

* A. Kraus, *Quelques remarques à propos des invariants `c₄`, `c₆` et `Δ` d'une courbe
  elliptique*, Acta Arith. 54 (1989), 75–80.
-/

public section

namespace TauCeti

open WeierstrassCurve

variable (R : Type*) [CommRing R] {K : Type*} [Field K] [Algebra R K] (c₄ c₆ : K)

/-- **Kraus's witness above `3`**: some `b₂ ∈ R` for which the `(b₂/12, 0, 0)`-transform of the
canonical equation `ofCInvariants c₄ c₆` has all its coefficients in `R`. This is the auxiliary
datum the criterion requires at a residue characteristic `3`, where a change of variables over
`R` can make `a₁` and `a₃` vanish and `b₂ = 4a₂` is the only remaining coefficient. -/
def HasKrausThreeWitness : Prop :=
  ∃ b₂ : R,
    ((⟨1, algebraMap R K b₂ / 12, 0, 0⟩ : VariableChange K) • ofCInvariants c₄ c₆).IsIntegral R

/-- **Kraus's witness above `2`**: some `a₁, a₃ ∈ R` for which the `(a₁²/12, a₁/2, a₃/2)`-transform
of the canonical equation `ofCInvariants c₄ c₆` has all its coefficients in `R`. This is the
auxiliary datum the criterion requires at a residue characteristic `2`, where a change of
variables over `R` can make `a₂` vanish, so that `b₂ = a₁²`; the triple is the case `b₂ = a₁²` of
the general prescription `(b₂/12, a₁/2, a₃/2)`. -/
def HasKrausTwoWitness : Prop :=
  ∃ a₁ a₃ : R, ((⟨1, algebraMap R K a₁ ^ 2 / 12, algebraMap R K a₁ / 2,
    algebraMap R K a₃ / 2⟩ : VariableChange K) • ofCInvariants c₄ c₆).IsIntegral R

/-- **Kraus's local condition on a pair of invariants.** The first four fields ask that `c₄`, `c₆`
and the discriminant of the canonical equation lie in `R` and that this discriminant is nonzero;
the last two are the auxiliary data, each demanded only at the residue characteristic it concerns.

The structure is stated over any `R` and `K`. Where `2` and `3` are invertible in `K` the first
four fields are exactly what an integral equation with these invariants forces: that is how the
`←` direction of `TauCeti.krausLocalCondition_iff_exists_integralModel` obtains them, and it is
why that direction needs the hypothesis, since without it a pair of `c`-invariants need not
determine the discriminant (`WeierstrassCurve.Δ_eq_of_c₄_eq_of_c₆_eq` asks for `1728` to be
regular). Where `2` and `3` are both units in `R` the last two fields are vacuous, which is
`TauCeti.krausLocalCondition_of_isUnit_six`. -/
structure KrausLocalCondition : Prop where
  /-- `c₄` lies in `R`. -/
  exists_c₄ : ∃ x : R, algebraMap R K x = c₄
  /-- `c₆` lies in `R`. -/
  exists_c₆ : ∃ x : R, algebraMap R K x = c₆
  /-- the discriminant `(c₄³ - c₆²)/1728` lies in `R`. -/
  exists_Δ : ∃ x : R, algebraMap R K x = (ofCInvariants c₄ c₆).Δ
  /-- the pair is nonsingular. -/
  Δ_ne_zero : (ofCInvariants c₄ c₆).Δ ≠ 0
  /-- above `2`, a witness. -/
  hasKrausTwoWitness : ¬IsUnit (2 : R) → HasKrausTwoWitness R c₄ c₆
  /-- above `3`, a witness. -/
  hasKrausThreeWitness : ¬IsUnit (3 : R) → HasKrausThreeWitness R c₄ c₆

variable {R c₄ c₆}

/-- **Where `6` is a unit an integral pair of invariants already gives an integral canonical
equation.** Its two coefficients are `-c₄/48` and `-c₆/864`, so once `c₄` and `c₆` lie in the
image of `R` so do these, because `48` and `864` are units as soon as `6` is. -/
theorem isIntegral_ofCInvariants (h6 : IsUnit (6 : R)) (h₄ : ∃ x : R, algebraMap R K x = c₄)
    (h₆ : ∃ x : R, algebraMap R K x = c₆) : (ofCInvariants c₄ c₆).IsIntegral R := by
  obtain ⟨u₄, hu₄⟩ : IsUnit (48 : R) := isUnit_of_dvd_unit ⟨27, by norm_num⟩ (h6.pow 4)
  obtain ⟨u₆, hu₆⟩ : IsUnit (864 : R) := isUnit_of_dvd_unit ⟨9, by norm_num⟩ (h6.pow 5)
  obtain ⟨x₄, hx₄⟩ := h₄
  obtain ⟨x₆, hx₆⟩ := h₆
  refine isIntegral_of_exists_lift R ⟨0, by simp⟩ ⟨0, by simp⟩ ⟨0, by simp⟩
    ⟨-x₄ * ↑u₄⁻¹, ?_⟩ ⟨-x₆ * ↑u₆⁻¹, ?_⟩
  · rw [ofCInvariants_a₄, map_mul, map_neg, hx₄, map_units_inv, hu₄, map_ofNat, div_eq_mul_inv]
  · rw [ofCInvariants_a₆, map_mul, map_neg, hx₆, map_units_inv, hu₆, map_ofNat, div_eq_mul_inv]

/-- **Away from the residue characteristics `2` and `3` Kraus's condition carries no auxiliary
content**: an integral, nonsingular pair of invariants satisfies it outright, because the
canonical equation is then already integral and both witness fields are vacuous. -/
theorem krausLocalCondition_of_isUnit_six (h6 : IsUnit (6 : R))
    (h₄ : ∃ x : R, algebraMap R K x = c₄) (h₆ : ∃ x : R, algebraMap R K x = c₆)
    (hΔ : (ofCInvariants c₄ c₆).Δ ≠ 0) : KrausLocalCondition R c₄ c₆ := by
  have h2 : IsUnit (2 : R) := isUnit_of_dvd_unit ⟨3, by norm_num⟩ h6
  have h3 : IsUnit (3 : R) := isUnit_of_dvd_unit ⟨2, by norm_num⟩ h6
  have := isIntegral_ofCInvariants h6 h₄ h₆
  exact ⟨h₄, h₆, Δ_integral_of_isIntegral R _, hΔ, fun h ↦ absurd h2 h, fun h ↦ absurd h3 h⟩

/-! ### Kraus's global condition over a Dedekind domain -/

variable (O : Type*) [CommRing O] [IsDedekindDomain O] [Algebra O K] [IsFractionRing O K]

open IsDedekindDomain

/-- **Kraus's global condition on a pair of invariants**: Kraus's local condition holds over the
localisation of the Dedekind domain `O` at every height-one prime. -/
def KrausGlobalCondition (c₄ c₆ : K) : Prop :=
  ∀ v : HeightOneSpectrum O, KrausLocalCondition (Localization.AtPrime v.asIdeal) c₄ c₆

variable {O}

/-- Kraus's global condition, unfolded: the local condition at every height-one prime. -/
@[simp]
theorem krausGlobalCondition_iff : KrausGlobalCondition O c₄ c₆ ↔
    ∀ v : HeightOneSpectrum O, KrausLocalCondition (Localization.AtPrime v.asIdeal) c₄ c₆ :=
  Iff.rfl

/-- Kraus's global condition gives the local condition at each height-one prime. -/
theorem KrausGlobalCondition.krausLocalCondition (h : KrausGlobalCondition O c₄ c₆)
    (v : HeightOneSpectrum O) : KrausLocalCondition (Localization.AtPrime v.asIdeal) c₄ c₆ :=
  h v

variable [Invertible (2 : K)] [Invertible (3 : K)]

/-- A pair realised by an integral equation with `a₂ = 0` has a two-witness: the equation is the
`(a₁²/12, a₁/2, a₃/2)`-transform of the canonical one. -/
private theorem hasKrausTwoWitness_of_baseChange (V : WeierstrassCurve R) (ha₂ : V.a₂ = 0)
    (h₄ : (V⁄K).c₄ = c₄) (h₆ : (V⁄K).c₆ = c₆) : HasKrausTwoWitness R c₄ c₆ := by
  subst h₄; subst h₆
  refine ⟨V.a₁, V.a₃, ?_⟩
  have ha₁' : (V⁄K).a₁ = algebraMap R K V.a₁ := by rw [baseChange, map_a₁]
  have ha₃' : (V⁄K).a₃ = algebraMap R K V.a₃ := by rw [baseChange, map_a₃]
  have hb : (V⁄K).b₂ = algebraMap R K V.a₁ ^ 2 := by
    rw [baseChange, map_b₂, b₂, ha₂]; simp
  have hC : (⟨1, algebraMap R K V.a₁ ^ 2 / 12, algebraMap R K V.a₁ / 2,
      algebraMap R K V.a₃ / 2⟩ : VariableChange K) =
      ⟨1, (V⁄K).b₂ / 12, (V⁄K).a₁ / 2, (V⁄K).a₃ / 2⟩ := by
    rw [hb, ha₁', ha₃']
  rw [hC, smul_ofCInvariants]
  exact ⟨V, rfl⟩

/-- A pair realised by an integral equation with `a₁ = a₃ = 0` has a three-witness: the equation
is the `(b₂/12, 0, 0)`-transform of the canonical one. -/
private theorem hasKrausThreeWitness_of_baseChange (V : WeierstrassCurve R) (ha₁ : V.a₁ = 0)
    (ha₃ : V.a₃ = 0) (h₄ : (V⁄K).c₄ = c₄) (h₆ : (V⁄K).c₆ = c₆) : HasKrausThreeWitness R c₄ c₆ := by
  subst h₄; subst h₆
  refine ⟨V.b₂, ?_⟩
  have ha₁' : (V⁄K).a₁ = 0 := by rw [baseChange, map_a₁, ha₁, map_zero]
  have ha₃' : (V⁄K).a₃ = 0 := by rw [baseChange, map_a₃, ha₃, map_zero]
  have hb : (V⁄K).b₂ = algebraMap R K V.b₂ := by rw [baseChange, map_b₂]
  have hC : (⟨1, algebraMap R K V.b₂ / 12, 0, 0⟩ : VariableChange K) =
      ⟨1, (V⁄K).b₂ / 12, (V⁄K).a₁ / 2, (V⁄K).a₃ / 2⟩ := by
    rw [hb, ha₁', ha₃']; norm_num
  rw [hC, smul_ofCInvariants]
  exact ⟨V, rfl⟩

/-- Reading the conclusion of the criterion off a witness: a transform of the canonical equation
with `u = 1` keeps its invariants. -/
private theorem exists_integralModel_of_isIntegral_smul {r s t : K}
    (h : ((⟨1, r, s, t⟩ : VariableChange K) • ofCInvariants c₄ c₆).IsIntegral R)
    (hΔ : (ofCInvariants c₄ c₆).Δ ≠ 0) :
    ∃ W : WeierstrassCurve K, W.IsIntegral R ∧ W.c₄ = c₄ ∧ W.c₆ = c₆ ∧ W.Δ ≠ 0 :=
  ⟨_, h, by simp [variableChange_c₄], by simp [variableChange_c₆], by
    simpa [variableChange_Δ] using hΔ⟩

/-- **Kraus's local criterion.** For a local ring `R` with an algebra map to a field `K` in which
`2` and `3` are invertible, the pair `(c₄, c₆)` is the pair of `c`-invariants of a nonsingular
Weierstrass equation with coefficients in `R` exactly when Kraus's local condition holds.

The correspondence is concrete in both directions: a witness of `KrausLocalCondition` is a change
of variables carrying `ofCInvariants c₄ c₆` to an equation with coefficients in `R`, and that
transform is the model the equivalence produces. -/
theorem krausLocalCondition_iff_exists_integralModel [IsLocalRing R] :
    KrausLocalCondition R c₄ c₆ ↔
      ∃ W : WeierstrassCurve K, W.IsIntegral R ∧ W.c₄ = c₄ ∧ W.c₆ = c₆ ∧ W.Δ ≠ 0 := by
  constructor
  · intro h
    by_cases h2 : IsUnit (2 : R)
    · by_cases h3 : IsUnit (3 : R)
      · refine ⟨ofCInvariants c₄ c₆, ?_, by simp, by simp, h.Δ_ne_zero⟩
        have h6 : IsUnit (6 : R) :=
          isUnit_of_eq_two_pow_mul_three_pow h2 h3 (m := 1) (n := 1) (by norm_num)
        exact isIntegral_ofCInvariants h6 h.exists_c₄ h.exists_c₆
      · obtain ⟨b₂, hb₂⟩ := h.hasKrausThreeWitness h3
        exact exists_integralModel_of_isIntegral_smul hb₂ h.Δ_ne_zero
    · obtain ⟨a₁, a₃, ha⟩ := h.hasKrausTwoWitness h2
      exact exists_integralModel_of_isIntegral_smul ha h.Δ_ne_zero
  · rintro ⟨W, hW, rfl, rfl, hΔ⟩
    obtain ⟨V, rfl⟩ := hW.integral
    have hc₄ : ∃ x : R, algebraMap R K x = (V⁄K).c₄ := ⟨V.c₄, by rw [baseChange, map_c₄]⟩
    have hc₆ : ∃ x : R, algebraMap R K x = (V⁄K).c₆ := ⟨V.c₆, by rw [baseChange, map_c₆]⟩
    -- `1728 = 2⁶3³` is regular, which is the cancellation `Δ_eq_of_c₄_eq_of_c₆_eq` asks for
    have hΔ' : (ofCInvariants (V⁄K).c₄ (V⁄K).c₆).Δ = (V⁄K).Δ :=
      Δ_eq_of_c₄_eq_of_c₆_eq (isUnit_of_eq_two_pow_mul_three_pow (isUnit_of_invertible 2)
        (isUnit_of_invertible 3) (m := 6) (n := 3) (by norm_num)).isRegular (by simp) (by simp)
    refine ⟨hc₄, hc₆, ⟨V.Δ, by rw [hΔ', baseChange, map_Δ]⟩, hΔ' ▸ hΔ, ?_, ?_⟩
    · intro h2
      have hsum : IsUnit ((-2 : R) + 3) := by norm_num
      have h3 : IsUnit (3 : R) :=
        (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left (by simpa using h2)
      have := h3.invertible
      have hcancel : (3 : R) * (⅟(3 : R) * V.a₂) = V.a₂ := by
        rw [← mul_assoc, mul_invOf_self, one_mul]
      refine hasKrausTwoWitness_of_baseChange
        ((⟨1, -(⅟(3 : R) * V.a₂), 0, 0⟩ : VariableChange R) • V) ?_
        (baseChange_smul_c₄ K rfl V) (baseChange_smul_c₆ K rfl V)
      simp [variableChange_a₂, mul_neg, hcancel]
    · intro h3
      have hsum : IsUnit ((3 : R) + -2) := by norm_num
      have h2 : IsUnit (2 : R) := by
        have := (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).resolve_left h3
        simpa using this
      have := h2.invertible
      exact hasKrausThreeWitness_of_baseChange (V.toCharNeTwoNF • V)
        (a₁_of_isCharNeTwoNF _) (a₃_of_isCharNeTwoNF _)
        (baseChange_smul_c₄ K rfl V) (baseChange_smul_c₆ K rfl V)

/-! ### Kraus's global criterion -/

/-- **Every local witness is a change of variables `(B/12, A/2, G/2)`.** Under Kraus's local
condition over a local ring, some such triple, with `A`, `B`, `G` in `R`, carries the canonical
equation to an integral one. These entries can be taken to be the coefficients `a₁`, `b₂`,
`a₃` of an integral model supplied by the local criterion. -/
private theorem KrausLocalCondition.exists_isIntegral_smul [IsLocalRing R]
    (h : KrausLocalCondition R c₄ c₆) :
    ∃ A B G : R, ((⟨1, algebraMap R K B / 12, algebraMap R K A / 2, algebraMap R K G / 2⟩ :
      VariableChange K) • ofCInvariants c₄ c₆).IsIntegral R := by
  obtain ⟨W, hW, h₄, h₆, _⟩ := krausLocalCondition_iff_exists_integralModel.mp h
  obtain ⟨V, rfl⟩ := hW.integral
  refine ⟨V.a₁, V.b₂, V.a₃, ?_⟩
  rw [← h₄, ← h₆, ← map_b₂, ← map_a₁, ← map_a₃, ← baseChange, smul_ofCInvariants]
  exact ⟨V, rfl⟩

/-- `12 = 2² · 3` is nonzero where `2` and `3` are invertible. -/
private theorem twelve_ne_zero : (12 : K) ≠ 0 := by
  have h12 : (12 : K) = 2 * 2 * 3 := by norm_num
  rw [h12]
  exact mul_ne_zero (mul_ne_zero (Invertible.ne_zero 2) (Invertible.ne_zero 2))
    (Invertible.ne_zero 3)

/-- **Witnesses congruent modulo `12` are equally good.** If the `(B/12, A/2, G/2)`-transform of
`W` is integral, so is the `(b/12, a/2, g/2)`-transform whenever `a = A + 12x`, `b = B + 12y` and
`g = G + Ay + 12z` in `R`: the second is the `(y, 6x, 6z)`-transform of the first. -/
private theorem isIntegral_smul_of_eq_add {W : WeierstrassCurve K} {A B G a b g x y z : R}
    (h : ((⟨1, algebraMap R K B / 12, algebraMap R K A / 2, algebraMap R K G / 2⟩ :
      VariableChange K) • W).IsIntegral R)
    (ha : a = A + 12 * x) (hb : b = B + 12 * y) (hg : g = G + A * y + 12 * z) :
    ((⟨1, algebraMap R K b / 12, algebraMap R K a / 2, algebraMap R K g / 2⟩ :
      VariableChange K) • W).IsIntegral R := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have h12 : (12 : K) ≠ 0 := twelve_ne_zero
  obtain ⟨V, hV⟩ := h.integral
  have hC : (⟨1, algebraMap R K b / 12, algebraMap R K a / 2, algebraMap R K g / 2⟩ :
      VariableChange K) = (⟨1, y, 6 * x, 6 * z⟩ : VariableChange R).baseChange K *
        ⟨1, algebraMap R K B / 12, algebraMap R K A / 2, algebraMap R K G / 2⟩ := by
    subst ha hb hg
    ext <;> simp [VariableChange.mul_def, VariableChange.baseChange, map_ofNat] <;> field_simp <;>
      ring
  rw [hC, mul_smul, hV, baseChange_smul_baseChange]
  exact ⟨_, rfl⟩

/-- **Kraus's global criterion.** Let `O` be a Dedekind domain with fraction field `K`, in which
`2` and `3` are invertible, and assume `O` has a height-one prime, as the ring of integers of a
number field does. Then the pair `(c₄, c₆)` is the pair of `c`-invariants of a nonsingular
Weierstrass equation with coefficients in `O` exactly when Kraus's local condition holds at every
height-one prime.

The equation produced is the `(b₂/12, a₁/2, a₃/2)`-transform of `ofCInvariants c₄ c₆` for elements
`a₁`, `b₂`, `a₃` of `O` approximating the local witnesses modulo `12`. Without a height-one prime
the condition is vacuous and the statement fails, since nothing then forces `c₄³ ≠ c₆²`. -/
theorem krausGlobalCondition_iff_exists_integralModel [Nonempty (HeightOneSpectrum O)] :
    KrausGlobalCondition O c₄ c₆ ↔
      ∃ W : WeierstrassCurve K, W.IsIntegral O ∧ W.c₄ = c₄ ∧ W.c₆ = c₆ ∧ W.Δ ≠ 0 := by
  constructor
  · intro h
    have hΔ := (h (Classical.arbitrary _)).Δ_ne_zero
    have h12 : (12 : O) ≠ 0 := fun h0 ↦
      twelve_ne_zero (K := K) (by rw [← map_ofNat (algebraMap O K) 12, h0, map_zero])
    -- Local witnesses `(A v, B v, G v)`, then `a₁`, `b₂` approximating `A`, `B` modulo `12`,
    -- and `a₃` approximating `G v + A v · (b₂ - B v)/12` modulo `12`.
    choose A B G hABG using fun v : HeightOneSpectrum O ↦ (h v).exists_isIntegral_smul
    obtain ⟨a₁, ha₁⟩ :=
      DedekindDomain.exists_forall_sub_mem_span_singleton_localizationAtPrime h12 A
    obtain ⟨b₂, hb₂⟩ :=
      DedekindDomain.exists_forall_sub_mem_span_singleton_localizationAtPrime h12 B
    choose y hy using fun v ↦ Ideal.mem_span_singleton'.1 (hb₂ v)
    obtain ⟨a₃, ha₃⟩ :=
      DedekindDomain.exists_forall_sub_mem_span_singleton_localizationAtPrime h12
        fun v ↦ G v + A v * y v
    refine exists_integralModel_of_isIntegral_smul (r := algebraMap O K b₂ / 12)
      (s := algebraMap O K a₁ / 2) (t := algebraMap O K a₃ / 2) ?_ hΔ
    refine isIntegral_of_forall_isIntegral_localizationAtPrime fun v ↦ ?_
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 (ha₁ v)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (ha₃ v)
    have hyv := hy v
    simp only [map_ofNat] at hx hyv hz
    simp only [IsScalarTower.algebraMap_apply O (Localization.AtPrime v.asIdeal) K]
    refine isIntegral_smul_of_eq_add (hABG v) (x := x) (y := y v) (z := z) ?_ ?_ ?_
    · linear_combination -hx
    · linear_combination -hyv
    · linear_combination -hz
  · rintro ⟨W, hW, rfl, rfl, hΔ⟩ v
    have : W.IsIntegral (Localization.AtPrime v.asIdeal) := IsIntegral.of_isScalarTower (R := O) W
    exact krausLocalCondition_iff_exists_integralModel.2 ⟨W, this, rfl, rfl, hΔ⟩

end TauCeti
