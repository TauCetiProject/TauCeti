/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve
import Mathlib.Tactic.ComputeDegree
import TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Potential good reduction

Let `R` be a discrete valuation ring with fraction field `K`. An elliptic curve over `K` has
**potential good reduction** when it acquires good reduction after a finite extension of `K`:
there are a finite extension `L / K` and a discrete valuation ring `S` with fraction field `L`
dominating `R`, such that a minimal equation of the curve over `S` has good reduction.

The minimal model is taken *after* the base change. An equation that is minimal over `R` need not
stay minimal over `S`, and Mathlib's `HasGoodReduction` holds only for minimal equations, so
asking `HasGoodReduction S (W.baseChange L)` would make the predicate depend on the chosen model
over `K`.

Over a complete `R` the valuation of `K` extends uniquely to `L` (Neukirch, *Algebraic Number
Theory*, II.4.8), so the integral closure of `R` in `L` is the only discrete valuation ring
with fraction field `L` dominating `R`; then `S` is forced and the definition is the usual one.
For a general `R` the place of `L` above `R` is part of the data being quantified over.

The main result is the `j`-invariant criterion (Silverman VII.5.5): an elliptic curve has
potential good reduction exactly when its `j`-invariant is **integral**. The necessary direction
holds in every residue characteristic. Its proof reads `j = c₄ ³ / Δ` on a minimal model with good
reduction over `S`, where `Δ` is a unit, and descends integrality from `S` to `R` because `R`, a
valuation ring, is integrally closed against every ring dominating it. In particular a curve with
multiplicative reduction, whose `j`-invariant has a pole, never has potential good reduction.

The sufficient direction is proved when `2` is a unit in `R`. Over a finite separable extension the
curve takes the Legendre form `y² = x (x - 1) (x + B)`, whose `j`-invariant is
`256 (B² + B + 1)³ / (B² (B + 1)²)`. If it is integral then so are `B`, `1 / B` and `-1 / (B + 1)`,
being roots of a monic polynomial with integral coefficients, so the discriminant
`16 B² (B + 1)²` is a unit at any discrete valuation ring of the extension dominating `R`. In
residue characteristic `2` the Legendre form is not available and this direction is not proved
here.

## Main definitions

* `WeierstrassCurve.HasPotentialGoodReduction`: good reduction after some finite extension.

## Main results

* `WeierstrassCurve.HasGoodReduction.hasPotentialGoodReduction`: good reduction is potentially
  good.
* `WeierstrassCurve.hasPotentialGoodReduction_smul`: potential good reduction is invariant under
  a change of variables.
* `WeierstrassCurve.HasGoodReduction.isInteger_j`: a minimal equation with good reduction has
  integral `j`-invariant.
* `WeierstrassCurve.HasPotentialGoodReduction.isInteger_j`: a curve with potential good reduction
  has integral `j`-invariant.
* `WeierstrassCurve.HasMultiplicativeReduction.not_isInteger_j` and
  `WeierstrassCurve.HasMultiplicativeReduction.not_hasPotentialGoodReduction`: multiplicative
  reduction gives a nonintegral `j`-invariant, so it is not potentially good.
* `WeierstrassCurve.hasGoodReduction_freyCurve_one`: a curve `y² = x (x - 1) (x + B)` in Legendre
  form with integral `j`-invariant has good reduction where `2` is a unit.
* `WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j` and
  `WeierstrassCurve.hasPotentialGoodReduction_iff_isInteger_j`: when `2` is a unit in `R`, a curve
  with integral `j`-invariant has potential good reduction, so the criterion is an equivalence.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4 and VII.5.5.
* J. Neukirch, *Algebraic Number Theory*, II.4.8.
-/

public section

universe u v

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum TauCeti

section

variable (R : Type v) [CommRing R] {K : Type u} [Field K] [Algebra R K]

/-- **Potential good reduction**: after some finite extension `L` of `K`, at some discrete
valuation ring `S` with fraction field `L` dominating `R`, a minimal equation of `W` has good
reduction. The maps `R → S → L` and `R → K → L` are required to agree, so that `S` lies over `R`.
The field `L` and the ring `S` are taken in the universe of `K`.

Over a complete `R`, the integral closure of `R` in `L` is the only such ring `S`, so this is the
usual notion of good reduction over the ring of integers of a finite extension. -/
def HasPotentialGoodReduction (W : WeierstrassCurve K) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
    (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
    (_ : Algebra S L) (_ : IsFractionRing S L) (_ : Algebra R S) (_ : IsLocalHom (algebraMap R S)),
    (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K) ∧
      ((W.baseChange L).minimal S).HasGoodReduction S

variable {R} in
/-- Potential good reduction unfolded: good reduction of a minimal equation after a finite
extension, at a discrete valuation ring dominating `R`. -/
theorem hasPotentialGoodReduction_iff {W : WeierstrassCurve K} :
    W.HasPotentialGoodReduction R ↔
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
        (_ : Algebra S L) (_ : IsFractionRing S L) (_ : Algebra R S)
        (_ : IsLocalHom (algebraMap R S)),
        (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K) ∧
          ((W.baseChange L).minimal S).HasGoodReduction S :=
  Iff.rfl

/-- **Introducing potential good reduction** from a finite extension `L / K` and a discrete
valuation ring `S` with fraction field `L`, dominating `R`, over which a minimal equation of `W`
has good reduction. -/
theorem HasPotentialGoodReduction.intro {W : WeierstrassCurve K} (L : Type u) [Field L]
    [Algebra K L] [FiniteDimensional K L] (S : Type u) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Algebra S L] [IsFractionRing S L] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (h : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (hW : ((W.baseChange L).minimal S).HasGoodReduction S) :
    W.HasPotentialGoodReduction R :=
  ⟨L, ‹_›, ‹_›, ‹_›, S, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, h, hW⟩

/-- **Potential good reduction is invariant under a change of variables**, so it is a property
of the curve rather than of the equation presenting it. -/
@[simp]
theorem hasPotentialGoodReduction_smul (D : VariableChange K) (W : WeierstrassCurve K) :
    (D • W).HasPotentialGoodReduction R ↔ W.HasPotentialGoodReduction R := by
  -- one direction for every change of variables, applied to `D` and to `D⁻¹`
  suffices h : ∀ (D : VariableChange K) (W : WeierstrassCurve K),
      W.HasPotentialGoodReduction R → (D • W).HasPotentialGoodReduction R from
    ⟨fun hW ↦ by simpa using h D⁻¹ _ hW, h D W⟩
  rintro D W ⟨L, _, _, _, S, _, _, _, _, _, _, _, hRS, hW⟩
  refine .intro R L S hRS ?_
  rwa [baseChange, ← map_variableChange, hasGoodReduction_minimal_smul_iff]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-! ### The `j`-invariant -/

/-- **A minimal equation with good reduction has integral `j`-invariant**: its `c₄` is integral
and its discriminant is a unit, so `j = c₄ ³ / Δ` is integral. -/
theorem HasGoodReduction.isInteger_j {W : WeierstrassCurve K} [W.IsElliptic]
    (h : W.HasGoodReduction R) : IsLocalization.IsInteger R W.j := by
  have := h.toIsMinimal
  -- the discriminant of the integral model is not in the maximal ideal, hence a unit
  have hΔ : IsUnit (W.integralModel R).Δ := by
    have hv : valuation K (maximalIdeal R) (algebraMap R K (W.integralModel R).Δ) = 1 := by
      rw [integralModel_Δ_eq]
      exact h.goodReduction
    exact IsLocalRing.notMem_maximalIdeal.mp fun hmem ↦
      ((valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr hmem).ne hv
  refine ⟨(W.integralModel R).c₄ ^ 3 * ↑hΔ.unit⁻¹, ?_⟩
  rw [j_eq, mul_comm, map_mul, map_pow, integralModel_c₄_eq, ← integralModel_Δ_eq R W]
  rw [map_units_inv, IsUnit.unit_spec]

/-- **A curve with potential good reduction has integral `j`-invariant** (Silverman VII.5.5,
the necessary direction): `j` lies in the image of `R`. -/
theorem HasPotentialGoodReduction.isInteger_j {W : WeierstrassCurve K} [W.IsElliptic]
    (h : W.HasPotentialGoodReduction R) : IsLocalization.IsInteger R W.j := by
  obtain ⟨L, _, _, _, S, _, _, _, _, _, _, _, hRS, hgood⟩ := h
  refine TauCeti.ValuationRing.isInteger_of_isInteger_algebraMap (IsFractionRing.injective S L)
    hRS ?_
  -- over `S`, the chosen minimal equation has good reduction and the same `j`-invariant
  obtain ⟨C, hC⟩ := (W.baseChange L).exists_smul_eq_minimal S
  have : (W.baseChange L).IsElliptic := by rw [baseChange]; infer_instance
  have : ((W.baseChange L).minimal S).IsElliptic := hC ▸ inferInstance
  have hj (W' : WeierstrassCurve L) [W'.IsElliptic] (hW' : C • W.baseChange L = W') :
      W'.j = algebraMap K L W.j := by
    subst hW'
    rw [variableChange_j]
    exact map_j W (algebraMap K L)
  exact hj _ hC ▸ hgood.isInteger_j S

/-- **Multiplicative reduction gives a nonintegral `j`-invariant**: on a minimal equation with
multiplicative reduction, `c₄` is a unit while `Δ` is not, so `j = c₄ ³ / Δ` has a pole. -/
theorem HasMultiplicativeReduction.not_isInteger_j {W : WeierstrassCurve K} [W.IsElliptic]
    (h : W.HasMultiplicativeReduction R) : ¬ IsLocalization.IsInteger R W.j := by
  rintro ⟨r, hr⟩
  have hc :
      valuation K (maximalIdeal R) (W.c₄ ^ 3) = valuation K (maximalIdeal R) (W.j * W.Δ) := by
    rw [j_eq, mul_comm, ← mul_assoc, mul_inv_cancel₀ W.isUnit_Δ.ne_zero, one_mul]
  rw [map_pow, h.multiplicativeReduction, one_pow, map_mul, ← hr] at hc
  exact ((mul_le_of_le_one_left' (valuation_le_one _ r)).trans_lt h.badReduction).ne' hc

/-- **Multiplicative reduction is not potentially good.** -/
theorem HasMultiplicativeReduction.not_hasPotentialGoodReduction {W : WeierstrassCurve K}
    [W.IsElliptic] (h : W.HasMultiplicativeReduction R) : ¬ W.HasPotentialGoodReduction R :=
  fun hW ↦ h.not_isInteger_j R hW.isInteger_j

/-! ### The Legendre form -/

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A root of `(X² + X + 1)³ - c X² (X + 1)²`, for `c ∈ R`, is integral over `R`: the polynomial is
monic. -/
private theorem isIntegral_of_sq_add_add_one_pow_three_eq {c : R} {x : K}
    (h : (x ^ 2 + x + 1) ^ 3 = algebraMap R K c * (x ^ 2 * (x + 1) ^ 2)) :
    _root_.IsIntegral R x := by
  open Polynomial in
  refine ⟨(X ^ 2 + X + 1) ^ 3 - C c * (X ^ 2 * (X + 1) ^ 2), ?_, ?_⟩
  · monicity!
  · simp only [eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_one]
    rw [h, sub_self]

/-- **A curve in Legendre form with integral `j`-invariant has good reduction** over a discrete
valuation ring in which `2` is a unit. The curve is `y² = x (x - 1) (x + B)`, that is
`TauCeti.freyCurve 1 B`.

The `j`-invariant `256 (B² + B + 1)³ / (B² (B + 1)²)` forces `B`, `1 / B` and `-1 / (B + 1)` to be
roots of the monic polynomial `(X² + X + 1)³ - (j / 256) X² (X + 1)²`, so `B` and `B + 1` are units
of `R`. The discriminant `16 B² (B + 1)²` of the integral equation is then a unit too (Silverman,
*AEC*, VII.5.5). -/
theorem hasGoodReduction_freyCurve_one (h2 : IsUnit (2 : R)) {B : K}
    [(freyCurve 1 B).IsElliptic] (hj : IsLocalization.IsInteger R (freyCurve 1 B).j) :
    (freyCurve 1 B).HasGoodReduction R := by
  obtain ⟨h2K, -, hB, hB1⟩ := (isElliptic_freyCurve_iff 1 B).mp ‹_›
  have hB0 : B ≠ 0 := hB.ne_zero
  have hB1' : 1 + B ≠ 0 := hB1.ne_zero
  -- `j = 256 c` for some `c ∈ R`, since `256 = 2⁸` is a unit
  obtain ⟨J, hJ⟩ := hj
  have h256 : IsUnit (256 : R) := by
    rw [show (256 : R) = 2 ^ 8 by norm_num]
    exact h2.pow 8
  set c : R := J * ↑h256.unit⁻¹
  have hc : algebraMap R K c * 256 = algebraMap R K J := by
    rw [← map_ofNat (algebraMap R K) 256, ← map_mul, mul_assoc, h256.val_inv_mul, mul_one]
  have key : (B ^ 2 + B + 1) ^ 3 = algebraMap R K c * (B ^ 2 * (B + 1) ^ 2) := by
    have hden : (1 : K) ^ 2 * B ^ 2 * (1 + B) ^ 2 ≠ 0 := by
      rw [one_pow, one_mul]
      exact mul_ne_zero (pow_ne_zero 2 hB0) (pow_ne_zero 2 hB1')
    rw [freyCurve_j, ← hc, eq_div_iff hden] at hJ
    have h256K : (256 : K) ≠ 0 := by
      rw [show (256 : K) = 2 ^ 8 by norm_num]
      exact pow_ne_zero 8 h2K.ne_zero
    exact mul_left_cancel₀ h256K (by linear_combination -hJ)
  -- `B`, `1 / B` and `-1 / (1 + B)` are integral over `R`, hence in `R`
  obtain ⟨β, hβ⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_add_one_pow_three_eq R key)
  obtain ⟨σ, hσ⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_add_one_pow_three_eq R (x := B⁻¹) (c := c) (by
      field_simp
      linear_combination key))
  obtain ⟨ρ, hρ⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_add_one_pow_three_eq R (x := -(1 + B)⁻¹) (c := c) (by
      field_simp
      linear_combination key))
  have hinj := IsFractionRing.injective R K
  have hβu : IsUnit β := .of_mul_eq_one σ (hinj (by
    rw [map_mul, hβ, hσ, mul_inv_cancel₀ hB0, map_one]))
  have hβ1 : IsUnit (1 + β) := .of_mul_eq_one (-ρ) (hinj (by
    rw [map_mul, map_add, map_neg, map_one, hβ, hρ, neg_neg, mul_inv_cancel₀ hB1']))
  -- the integral equation `y² = x (x - 1) (x + β)` has unit discriminant
  have hbase : (freyCurve 1 β).baseChange K = freyCurve 1 B := by
    rw [baseChange, map_freyCurve, map_one, hβ]
  have : IsIntegral R (freyCurve 1 B) := ⟨⟨freyCurve 1 β, hbase.symm⟩⟩
  rw [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_eq_of_baseChange_eq hbase]
  exact ((isElliptic_freyCurve_iff 1 β).mpr ⟨h2, isUnit_one, hβu, hβ1⟩).isUnit

end

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type u} [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- **Good reduction is potentially good**, taking the trivial extension `L = K`, `S = R`. Here `R`
lives in the universe of `K`, since `HasPotentialGoodReduction` takes `S` there. -/
theorem HasGoodReduction.hasPotentialGoodReduction {W : WeierstrassCurve K}
    (h : W.HasGoodReduction R) : W.HasPotentialGoodReduction R := by
  refine .intro R K R (by ext; simp) ?_
  rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, map_id]
  exact h.hasGoodReduction_minimal R

/-- **Integral `j`-invariant gives potential good reduction** (Silverman VII.5.5, the sufficient
direction) when `2` is a unit in `R`, that is away from residue characteristic `2`.

Over a finite separable extension `L` of `K` the curve takes the Legendre form
`y² = x (x - 1) (x + B)`
(`WeierstrassCurve.exists_variableChange_smul_baseChange_eq_freyCurve_one`). Its `j`-invariant is
still integral at a discrete valuation ring of `L` dominating `R`, and a curve in Legendre form with
integral `j`-invariant has good reduction there (`WeierstrassCurve.hasGoodReduction_freyCurve_one`).
Here `R` lives in the universe of `K`, as in
`WeierstrassCurve.HasGoodReduction.hasPotentialGoodReduction`, since that discrete valuation ring
is built in the universe of `L`. -/
theorem hasPotentialGoodReduction_of_isInteger_j {W : WeierstrassCurve K} [W.IsElliptic]
    (h2 : IsUnit (2 : R)) (hj : IsLocalization.IsInteger R W.j) :
    W.HasPotentialGoodReduction R := by
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap R K) 2]
    exact (h2.map _).ne_zero
  obtain ⟨L, _, _, _, _, C, B, hC⟩ := W.exists_variableChange_smul_baseChange_eq_freyCurve_one h2K
  -- a discrete valuation ring `S` dominating `R`, with fraction field `K`-isomorphic to `L`
  let _ : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq' rfl
  obtain ⟨E, ⟨e⟩⟩ := TauCeti.FiniteDVRExtension.exists_algEquiv_extensionField R K L
  set L' := E.extensionField
  set S := E.localRing
  set f : L →ₐ[K] L' := e.symm.toAlgHom
  have hRS : (algebraMap S L').comp (algebraMap R S) = (algebraMap K L').comp (algebraMap R K) :=
    RingHom.ext fun r ↦ by simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  -- transport the Legendre form along `f`
  have hE : C.map (f : L →+* L') • W.baseChange L' = freyCurve 1 (f B) := by
    rw [← map_baseChange W f, map_variableChange, hC, map_freyCurve, map_one, RingHom.coe_coe]
  have : (W.baseChange L').IsElliptic := by rw [baseChange]; infer_instance
  have : (freyCurve 1 (f B)).IsElliptic := hE ▸ inferInstance
  have hjE (W' : WeierstrassCurve L') [W'.IsElliptic]
      (hW' : C.map (f : L →+* L') • W.baseChange L' = W') : W'.j = algebraMap K L' W.j := by
    subst hW'
    rw [variableChange_j]
    exact map_j W (algebraMap K L')
  -- the `j`-invariant stays integral at `S`, so the Legendre curve has good reduction there
  have hjS : IsLocalization.IsInteger S (freyCurve 1 (f B)).j := by
    obtain ⟨r, hr⟩ := hj
    refine ⟨algebraMap R S r, ?_⟩
    rw [hjE _ hE, ← hr, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L']
  have h2S : IsUnit (2 : S) := by
    rw [← map_ofNat (algebraMap R S) 2]
    exact h2.map _
  have hgood := hasGoodReduction_freyCurve_one S h2S hjS
  refine .intro R L' S hRS ?_
  rw [← hasGoodReduction_minimal_smul_iff S (C.map (f : L →+* L')), hE]
  exact hgood.hasGoodReduction_minimal S

/-- **The `j`-invariant criterion for potential good reduction** (Silverman VII.5.5) away from
residue characteristic `2`: an elliptic curve has potential good reduction exactly when its
`j`-invariant is integral. -/
theorem hasPotentialGoodReduction_iff_isInteger_j {W : WeierstrassCurve K} [W.IsElliptic]
    (h2 : IsUnit (2 : R)) : W.HasPotentialGoodReduction R ↔ IsLocalization.IsInteger R W.j :=
  ⟨(·.isInteger_j), hasPotentialGoodReduction_of_isInteger_j R h2⟩

end WeierstrassCurve

end
