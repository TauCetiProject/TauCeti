/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.Henselian.Strict

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.Integral

/-!
# Integrally closed local domains with separably closed fraction field

Let `R` be an integrally closed local domain whose fraction field `K` is separably closed. Then
`R` is a strictly henselian local ring. Every monic polynomial over `R` is a product of monic
polynomials that are irreducible over `K`, and over the separably closed field `K` an irreducible
polynomial is either linear or has zero derivative. A simple root of the reduction of a monic
polynomial is therefore the reduction of a root of a linear factor over `R`, and an irreducible
separable polynomial over the residue field lifts to a monic polynomial that is irreducible and
separable over `K`, hence linear. If `K` is algebraically closed, so is the residue field: every
root in `K` of a monic polynomial over `R` lies in `R`.

The main application is to valuation rings: a valuation ring with separably closed fraction field
is strictly henselian, and a valuation ring with algebraically closed fraction field is strictly
henselian with algebraically closed residue field. The same local statement shows that the local
rings of a normal integral scheme with separably closed function field are strictly henselian.

## Main results

* `TauCeti.HenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed`: an integrally closed local
  domain with separably closed fraction field is henselian.
* `TauCeti.isSepClosed_residueField_of_isIntegrallyClosed`: its residue field is separably closed.
* `TauCeti.IsStrictlyHenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed`: it is strictly
  henselian.
* `TauCeti.isAlgClosed_residueField_of_isIntegrallyClosed`: if the fraction field is algebraically
  closed, so is the residue field.
* `TauCeti.ValuationRing.isStrictlyHenselianLocalRing`,
  `TauCeti.ValuationRing.isAlgClosed_residueField`: the specialisations to valuation rings.

## References

* [Stacks Project, Lemma 15.14.5 (Tag 0DCQ)](https://stacks.math.columbia.edu/tag/0DCQ)
* [Stacks Project, Lemma 15.14.7 (Tag 0DCS)](https://stacks.math.columbia.edu/tag/0DCS)
* R. Huber, *Étale cohomology of henselian rings and cohomology of abstract Riemann surfaces of
  fields*, Math. Ann. 295 (1993), §2, proof of Lemma 2.4.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 16.3.
-/

public section

open _root_.IsLocalRing Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] [IsIntegrallyClosed R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A monic polynomial of positive degree over an integrally closed domain `R` has a monic factor
over `R` that is irreducible over the fraction field `K`, with monic cofactor. -/
private theorem exists_monic_mul_eq_of_irreducible_map {f : R[X]} (hf : f.Monic)
    (hdeg : f.natDegree ≠ 0) :
    ∃ g q : R[X], g.Monic ∧ q.Monic ∧ g * q = f ∧ Irreducible (g.map (algebraMap R K)) := by
  have hinj := IsFractionRing.injective R K
  have hu : ¬IsUnit (f.map (algebraMap R K)) := fun h ↦
    hdeg <| by rw [← hf.natDegree_map (algebraMap R K), natDegree_eq_zero_of_isUnit h]
  obtain ⟨G, hGm, hGirr, hGdvd⟩ := exists_monic_irreducible_factor _ hu
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hf hGdvd
  rw [hGm.leadingCoeff, C_1, mul_one] at hg
  have hgm : g.Monic :=
    hinj <| by rw [← leadingCoeff_map_of_injective hinj, hg, hGm.leadingCoeff, map_one]
  obtain ⟨q, rfl⟩ := hf.dvd_of_fraction_map_dvd_fraction_map hgm (hg ▸ hGdvd)
  exact ⟨g, q, hgm, hgm.of_mul_monic_left hf, rfl, hg ▸ hGirr⟩

omit [IsIntegrallyClosed R] in
/-- A monic polynomial over `R` with nonzero derivative that is irreducible over the separably
closed fraction field `K` is linear. -/
private theorem natDegree_eq_one_of_irreducible_map [IsSepClosed K] {g : R[X]} (hg : g.Monic)
    (hirr : Irreducible (g.map (algebraMap R K))) (hder : derivative g ≠ 0) :
    g.natDegree = 1 := by
  have hsep : (g.map (algebraMap R K)).Separable := by
    rw [separable_iff_derivative_ne_zero hirr, derivative_map]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hder
  rw [← hg.natDegree_map (algebraMap R K)]
  exact natDegree_eq_of_degree_eq_some (IsSepClosed.degree_eq_one_of_irreducible K hirr hsep)

variable [IsLocalRing R]

/-- **Integrally closed local domains with separably closed fraction field are henselian.**
A simple root of the reduction of a monic polynomial is the reduction of a root of one of its
linear factors. -/
theorem HenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed [IsSepClosed K] :
    HenselianLocalRing R := by
  refine ⟨fun f hf a₀ h₁ h₂ ↦ ?_⟩
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  have hdeg : f.natDegree ≠ 0 := fun h0 ↦ by
    rw [hf.natDegree_eq_zero.mp h0, eval_one] at h₁
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h₁)
  obtain ⟨g, q, hg, hq, rfl, hirr⟩ := exists_monic_mul_eq_of_irreducible_map K hf hdeg
  rw [derivative_mul, eval_add, eval_mul, eval_mul] at h₂
  rw [eval_mul] at h₁
  rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h₁ with hg₁ | hq₁
  · -- The root lifts along the factor `g`, which is linear since `g'(a₀)` is a unit.
    have hg₂ : IsUnit (eval a₀ (derivative g)) := by
      by_contra hnu
      refine (mem_maximalIdeal _).mp (add_mem ?_ ?_) h₂
      · exact (maximalIdeal R).mul_mem_right _ ((mem_maximalIdeal _).mpr hnu)
      · exact (maximalIdeal R).mul_mem_right _ hg₁
    have hder : derivative g ≠ 0 := fun h0 ↦ by
      rw [h0, eval_zero] at hg₂; exact not_isUnit_zero hg₂
    have h1 := natDegree_eq_one_of_irreducible_map K hg hirr hder
    have hgX : g = X + C (g.coeff 0) := hg.eq_X_add_C h1
    refine ⟨-g.coeff 0, ?_, ?_⟩
    · rw [IsRoot, eval_mul, hgX]; simp
    · rw [hgX, eval_add, eval_X, eval_C] at hg₁
      rw [show -g.coeff 0 - a₀ = -(a₀ + g.coeff 0) by ring]
      exact (maximalIdeal R).neg_mem_iff.mpr hg₁
  · -- Otherwise `a₀` is a simple root of the reduction of the cofactor `q`.
    have hq₂ : IsUnit (eval a₀ (derivative q)) := by
      by_contra hnu
      refine (mem_maximalIdeal _).mp (add_mem ?_ ?_) h₂
      · exact (maximalIdeal R).mul_mem_left _ hq₁
      · exact (maximalIdeal R).mul_mem_left _ ((mem_maximalIdeal _).mpr hnu)
    have hgdeg : g.natDegree ≠ 0 := fun h0 ↦ hirr.not_isUnit <| by
      rw [hg.natDegree_eq_zero.mp h0, Polynomial.map_one]; exact isUnit_one
    have hlt : q.natDegree < n := by
      rw [← hn, hg.natDegree_mul hq]; omega
    obtain ⟨a, ha, ha₀⟩ := ih _ hlt q hq hq₁ hq₂ rfl
    exact ⟨a, by rw [IsRoot, eval_mul, ha.eq_zero, mul_zero], ha₀⟩

/-- The residue field of an integrally closed local domain with separably closed fraction field is
separably closed: a monic lift of an irreducible separable polynomial over the residue field is
irreducible and separable over the fraction field, hence linear. -/
theorem isSepClosed_residueField_of_isIntegrallyClosed [IsSepClosed K] :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun p hpm hirr hsep ↦ ?_
  obtain ⟨f, hfp, -, hf⟩ :=
    lifts_and_natDegree_eq_and_monic (map_surjective _ residue_surjective p) hpm
  have hpdeg : p.natDegree ≠ 0 := fun h0 ↦ hirr.not_isUnit <| by
    rw [hpm.natDegree_eq_zero.mp h0]; exact isUnit_one
  have hdeg : f.natDegree ≠ 0 := by
    rwa [← hf.natDegree_map (residue R), hfp]
  obtain ⟨g, q, hg, hq, rfl, hgirr⟩ := exists_monic_mul_eq_of_irreducible_map K hf hdeg
  rw [Polynomial.map_mul] at hfp
  -- The reduction of `q` is a monic unit, so `p` is the reduction of `g`.
  have hqu : IsUnit (q.map (residue R)) := by
    refine (hirr.isUnit_or_isUnit hfp.symm).resolve_left fun hu ↦ ?_
    have := natDegree_eq_zero_of_isUnit hu
    rw [hg.natDegree_map] at this
    exact hgirr.not_isUnit <| by
      rw [hg.natDegree_eq_zero.mp this, Polynomial.map_one]; exact isUnit_one
  have hq1 : q.map (residue R) = 1 :=
    (hq.map _).natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hqu)
  rw [hq1, mul_one] at hfp
  have hder : derivative g ≠ 0 := fun h0 ↦ (separable_iff_derivative_ne_zero hirr).mp hsep <| by
    rw [← hfp, derivative_map, h0, Polynomial.map_zero]
  have h1 := natDegree_eq_one_of_irreducible_map K hg hgirr hder
  rw [← hfp] at hpm ⊢
  exact ⟨-(g.map (residue R)).coeff 0, by
    rw [(hg.map (residue R)).eq_X_add_C (by rw [hg.natDegree_map, h1])]; simp⟩

/-- **Integrally closed local domains with separably closed fraction field are strictly
henselian.** -/
theorem IsStrictlyHenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed [IsSepClosed K] :
    IsStrictlyHenselianLocalRing R :=
  have := HenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed (R := R) K
  have := isSepClosed_residueField_of_isIntegrallyClosed (R := R) K
  inferInstance

/-- The residue field of an integrally closed local domain with algebraically closed fraction
field is algebraically closed: a root in the fraction field of a monic lift lies in the ring. -/
theorem isAlgClosed_residueField_of_isIntegrallyClosed [IsAlgClosed K] :
    IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hpm hirr ↦ ?_
  obtain ⟨f, rfl, -, hf⟩ :=
    lifts_and_natDegree_eq_and_monic (map_surjective _ residue_surjective p) hpm
  have hdeg : (f.map (algebraMap R K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (IsFractionRing.injective R K)]
    intro h0
    refine hirr.not_isUnit ?_
    rw [hf.natDegree_eq_zero.mp (natDegree_eq_of_degree_eq_some h0), Polynomial.map_one]
    exact isUnit_one
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    ⟨f, hf, by rwa [IsRoot, eval_map] at hx⟩
  have ha : f.eval a = 0 := IsFractionRing.injective R K <| by
    rw [map_zero, ← eval₂_at_apply, ← eval_map]; exact hx
  exact ⟨residue R a, by rw [eval_map, eval₂_at_apply, ha, map_zero]⟩

end TauCeti

namespace TauCeti.ValuationRing

variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

/-- **A valuation ring with separably closed fraction field is strictly henselian.** -/
theorem isStrictlyHenselianLocalRing [IsSepClosed K] : IsStrictlyHenselianLocalRing V :=
  have := (_root_.ValuationRing.integers V K).isIntegrallyClosed
  IsStrictlyHenselianLocalRing.of_isIntegrallyClosed_of_isSepClosed K

/-- **A valuation ring with algebraically closed fraction field has algebraically closed residue
field.** -/
theorem isAlgClosed_residueField [IsAlgClosed K] : IsAlgClosed (ResidueField V) :=
  have := (_root_.ValuationRing.integers V K).isIntegrallyClosed
  isAlgClosed_residueField_of_isIntegrallyClosed K

end TauCeti.ValuationRing
