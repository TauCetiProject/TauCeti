/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.RamificationGroup
public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity

/-!
# The global different exponent

The coefficient of the different ideal of a number-field extension at a prime `w` equals the
coefficient of the different ideal of the completed integer-ring extension at its maximal ideal.
The global different extends to the completed different, and completion preserves the
multiplicity of an ideal at the selected prime. This is the coefficient comparison needed to
transport local different-exponent theorems to number fields.

For a Galois extension, Hilbert's local different formula and the comparison between global and
local ramification groups then express this coefficient as
`\sum_{i \ge 0} (\# G_i - 1)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, Proposition 2.2 and Theorem 2.6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 4.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Polynomial ValuativeRel
open scoped AdicCompletionExtension NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

private theorem integerEquivAdicCompletionIntegers_comp :
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)).comp
        (v.integerEquivAdicCompletionIntegers (K := K)).toRingHom =
      (w.integerEquivAdicCompletionIntegers (K := L)).toRingHom.comp
        (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
          (ValuativeRel.valuation (w.adicCompletion L)).integer) :=
  RingHom.ext fun x ↦ (integerEquivAdicCompletionIntegers_algebraMap K L v w x).symm

/-- A generator of the abstract valuation integer ring remains a generator after identifying it
with the concrete adic-completion integer ring. -/
theorem adjoin_integerEquivAdicCompletionIntegers_eq_top
    (x : (ValuativeRel.valuation (w.adicCompletion L)).integer)
    (hx : Algebra.adjoin (ValuativeRel.valuation (v.adicCompletion K)).integer {x} = ⊤) :
    Algebra.adjoin (v.adicCompletionIntegers K)
        {w.integerEquivAdicCompletionIntegers (K := L) x} = ⊤ := by
  let eK := v.integerEquivAdicCompletionIntegers (K := K)
  let eL := w.integerEquivAdicCompletionIntegers (K := L)
  have hcomp :
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)).comp eK.toRingHom =
        eL.toRingHom.comp
          (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
            (ValuativeRel.valuation (w.adicCompletion L)).integer) :=
    integerEquivAdicCompletionIntegers_comp v w
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
  intro y
  have hmem : eL.symm y ∈
      (aeval x : Polynomial (ValuativeRel.valuation (v.adicCompletion K)).integer →ₐ[
        (ValuativeRel.valuation (v.adicCompletion K)).integer]
        (ValuativeRel.valuation (w.adicCompletion L)).integer).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]
    simp
  obtain ⟨p, hp⟩ := hmem
  -- The integer-ring equivalences are deliberately opaque; expose their `RingHom` coercions
  -- so the polynomial base map is visible to `map_aeval_eq_aeval_map`.
  change aeval x p = eL.symm y at hp
  refine ⟨p.map eK.toRingHom, ?_⟩
  change aeval (eL.toRingHom x) (p.map eK.toRingHom) = y
  calc
    aeval (eL.toRingHom x) (p.map eK.toRingHom) = eL.toRingHom (aeval x p) :=
      (map_aeval_eq_aeval_map hcomp p x).symm
    _ = y := by
      rw [hp]
      change eL (eL.symm y) = y
      exact eL.apply_symm_apply y

/-- Minimal polynomials are carried across the canonical identifications between abstract
valuation integer rings and concrete adic-completion integer rings. -/
theorem map_minpoly_integerEquivAdicCompletionIntegers
    (x : (ValuativeRel.valuation (w.adicCompletion L)).integer) :
    (minpoly (ValuativeRel.valuation (v.adicCompletion K)).integer x).map
        (v.integerEquivAdicCompletionIntegers (K := K)).toRingHom =
      minpoly (v.adicCompletionIntegers K)
        (w.integerEquivAdicCompletionIntegers (K := L) x) := by
  let eK := v.integerEquivAdicCompletionIntegers (K := K)
  let eL := w.integerEquivAdicCompletionIntegers (K := L)
  -- Expose the opaque integer-ring equivalences as ring homomorphisms so the two minimal
  -- polynomials have visibly corresponding coefficient and element maps.
  change (minpoly (ValuativeRel.valuation (v.adicCompletion K)).integer x).map
      eK.toRingHom = minpoly (v.adicCompletionIntegers K) (eL.toRingHom x)
  have hcomp :
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)).comp eK.toRingHom =
        eL.toRingHom.comp
          (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
            (ValuativeRel.valuation (w.adicCompletion L)).integer) :=
    integerEquivAdicCompletionIntegers_comp v w
  have hcomp_symm :
      (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
        (ValuativeRel.valuation (w.adicCompletion L)).integer).comp eK.symm.toRingHom =
        eL.symm.toRingHom.comp
          (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
    apply RingHom.ext
    intro z
    apply eL.injective
    simp only [RingHom.coe_comp, Function.comp_apply]
    -- Normalize the opaque equivalences to their underlying functions before using their
    -- inverse laws and the public naturality theorem.
    change eL (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
      (ValuativeRel.valuation (w.adicCompletion L)).integer (eK.symm z)) =
        eL (eL.symm
          (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) z))
    rw [eL.apply_symm_apply]
    have hn := integerEquivAdicCompletionIntegers_algebraMap K L v w (eK.symm z)
    rw [eK.apply_symm_apply] at hn
    exact hn
  have hxint : IsIntegral (ValuativeRel.valuation (v.adicCompletion K)).integer x :=
    Algebra.IsIntegral.isIntegral x
  refine IsIntegrallyClosed.minpoly.unique (R := v.adicCompletionIntegers K)
    ((minpoly.monic hxint).map eK.toRingHom) ?_ ?_
  · have he := map_aeval_eq_aeval_map hcomp
      (minpoly (ValuativeRel.valuation (v.adicCompletion K)).integer x) x
    exact (by simpa only [minpoly.aeval, map_zero] using he.symm)
  · intro q hqmonic hq
    have he := map_aeval_eq_aeval_map hcomp_symm q (eL.toRingHom x)
    have hq' : aeval x (q.map eK.symm.toRingHom) = 0 := by
      rw [hq, map_zero] at he
      have hsx : eL.symm.toRingHom (eL.toRingHom x) = x := by
        -- Reveal the underlying equivalence application so its inverse law applies.
        change eL.symm (eL x) = x
        exact eL.symm_apply_apply x
      rw [hsx] at he
      exact he.symm
    have hdegree := minpoly.min
      (ValuativeRel.valuation (v.adicCompletion K)).integer x
      (hqmonic.map eK.symm.toRingHom) hq'
    rw [degree_map_eq_of_injective (f := eK.toRingHom) eK.injective]
    rw [degree_map_eq_of_injective (f := eK.symm.toRingHom) eK.symm.injective] at hdegree
    exact hdegree

/-- The identification of the abstract valuation rings of `K_v ⊆ L_w` with the concrete
completed integer rings carries the local different ideal to the completed different ideal. -/
@[simp]
theorem map_differentIdeal_integerEquivAdicCompletionIntegers :
    (differentIdeal (ValuativeRel.valuation (v.adicCompletion K)).integer
        (ValuativeRel.valuation (w.adicCompletion L)).integer).map
        (w.integerEquivAdicCompletionIntegers (K := L)) =
      differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  let eK := v.integerEquivAdicCompletionIntegers (K := K)
  let eL := w.integerEquivAdicCompletionIntegers (K := L)
  have hcomp :
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)).comp eK.toRingHom =
        eL.toRingHom.comp
          (algebraMap (ValuativeRel.valuation (v.adicCompletion K)).integer
            (ValuativeRel.valuation (w.adicCompletion L)).integer) :=
    integerEquivAdicCompletionIntegers_comp v w
  obtain ⟨x, hx⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top
    (R := (ValuativeRel.valuation (v.adicCompletion K)).integer)
    (S := (ValuativeRel.valuation (w.adicCompletion L)).integer)
  have hy : Algebra.adjoin (v.adicCompletionIntegers K) {eL x} = ⊤ :=
    adjoin_integerEquivAdicCompletionIntegers_eq_top v w x hx
  rw [TauCeti.differentIdeal_eq_span_aeval_derivative_minpoly
      (ValuativeRel.valuation (v.adicCompletion K)).integer (v.adicCompletion K)
      (w.adicCompletion L) (ValuativeRel.valuation (w.adicCompletion L)).integer x hx,
    TauCeti.differentIdeal_eq_span_aeval_derivative_minpoly
      (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
      (w.adicCompletionIntegers L) (eL x) hy,
    Ideal.map_span, Set.image_singleton]
  congr 2
  have hmin : (minpoly (ValuativeRel.valuation (v.adicCompletion K)).integer x).map
      eK.toRingHom = minpoly (v.adicCompletionIntegers K) (eL.toRingHom x) :=
    map_minpoly_integerEquivAdicCompletionIntegers v w x
  calc
    eL.toRingHom (aeval x (derivative (minpoly
        (ValuativeRel.valuation (v.adicCompletion K)).integer x))) =
        aeval (eL.toRingHom x) ((derivative (minpoly
          (ValuativeRel.valuation (v.adicCompletion K)).integer x)).map eK.toRingHom) :=
      map_aeval_eq_aeval_map hcomp _ _
    _ = aeval (eL.toRingHom x)
        (derivative (minpoly (v.adicCompletionIntegers K) (eL.toRingHom x))) := by
      rw [← derivative_map, hmin]

/-- The local different exponent of `L_w/K_v` is the multiplicity of the completed different
ideal in the maximal ideal of the concrete completed integer ring. -/
theorem differentExponent_adicCompletion_eq_multiplicity_differentIdeal :
    TauCeti.differentExponent (v.adicCompletion K) (w.adicCompletion L) =
      multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
  let e := w.integerEquivAdicCompletionIntegers (K := L)
  let E : Ideal (ValuativeRel.valuation (w.adicCompletion L)).integer ≃*
      Ideal (w.adicCompletionIntegers L) :=
    { e.idealComapOrderIso.symm.toEquiv with
      map_mul' := Ideal.map_mul e }
  rw [TauCeti.differentExponent_def, ← multiplicity_map_eq E]
  -- `E` is the ideal equivalence induced by `e`; exposing its applications turns the two
  -- remaining goals into the characteristic map lemmas for the maximal ideal and the different.
  change multiplicity
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation (w.adicCompletion L)).integer).map e)
    ((differentIdeal (ValuativeRel.valuation (v.adicCompletion K)).integer
      (ValuativeRel.valuation (w.adicCompletion L)).integer).map e) = _
  rw [IsLocalRing.map_ringEquiv_maximalIdeal,
    map_differentIdeal_integerEquivAdicCompletionIntegers v w]

/-- The exponent of the completed different at the maximal ideal is the exponent of the global
different at `w`. -/
@[simp]
theorem multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal :
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  calc
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        ((differentIdeal (𝓞 K) (𝓞 L)).map
          (algebraMap (𝓞 L) (w.adicCompletionIntegers L))) := by
        rw [map_differentIdeal_eq_differentIdeal_adicCompletionIntegers v w]
    _ = _ := w.multiplicity_map_adicCompletionIntegers (K := L)
      (differentIdeal (𝓞 K) (𝓞 L)) differentIdeal_ne_bot

variable [IsGalois K L]

/-- **Hilbert's formula for a number-field different exponent.** For a finite Galois extension
`L/K`, the multiplicity of a prime `w` in the global different is the sum of the orders of the
nonnegative-index lower ramification groups, minus one in each degree. -/
theorem multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one :
    multiplicity w.asIdeal
        (differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) =
      ∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) - 1) := by
  let v := w.under (NumberField.RingOfIntegers K)
  rw [← multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal v w]
  rw [← differentExponent_adicCompletion_eq_multiplicity_differentIdeal v w,
    TauCeti.differentExponent_eq_finsum_lowerRamificationGroup]
  apply finsum_congr
  intro i
  rw [card_ramificationGroup_eq_card_lowerRamificationGroup v w]

end IsDedekindDomain.HeightOneSpectrum

end
