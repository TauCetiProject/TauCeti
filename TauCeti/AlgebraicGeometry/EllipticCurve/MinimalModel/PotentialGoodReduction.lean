/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

The main result is the necessary direction of the `j`-invariant criterion (Silverman VII.5.5):
an elliptic curve with potential good reduction has **integral** `j`-invariant. The proof reads
`j = c₄ ³ / Δ` on a minimal model with good reduction over `S`, where `Δ` is a unit, and descends
integrality from `S` to `R` because `R`, a valuation ring, is integrally closed against every ring
dominating it. In particular a curve with multiplicative reduction, whose `j`-invariant has a pole,
never has potential good reduction.

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

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.4 and VII.5.5.
* J. Neukirch, *Algebraic Number Theory*, II.4.8.
-/

public section

universe u v

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

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

end

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type u} [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- **Good reduction is potentially good**, taking the trivial extension `L = K`, `S = R`. Here `R`
lives in the universe of `K`, since `HasPotentialGoodReduction` takes `S` there. -/
theorem HasGoodReduction.hasPotentialGoodReduction {W : WeierstrassCurve K}
    (h : W.HasGoodReduction R) : W.HasPotentialGoodReduction R := by
  refine .intro R K R (by ext; simp) ?_
  rw [baseChange, Algebra.algebraMap_self, map_id]
  exact h.hasGoodReduction_minimal R

end WeierstrassCurve

end
