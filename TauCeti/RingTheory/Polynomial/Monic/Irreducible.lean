/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.Polynomial.SpecificDegree

/-!
# Monic irreducible polynomials of a fixed degree

The monic irreducible polynomials of a given degree over a semiring `R` form a set depending
only on `R` and the degree. When `R` is finite that set is finite, because a monic polynomial of
degree `d` is determined by its lower coefficients: `Polynomial.monicEquivDegreeLT` matches such
polynomials with `Polynomial.degreeLT`, which `Polynomial.degreeLTEquiv` identifies with the
finite function space `Fin d → R`.

The file also records irreducibility criteria for monic cubics and quartics over an integrally
closed domain: irreducibility over the fraction field reduces to the absence of roots, and of
monic quadratic factors, in the domain itself.

## Main definitions

* `Polynomial.monicIrreduciblesOfDegree`: the monic irreducible polynomials of degree `d`.

## Main results

* `Polynomial.mem_monicIrreduciblesOfDegree_iff`: the defining membership condition.
* `Polynomial.finite_monicIrreduciblesOfDegree`: over a finite coefficient ring there are
  finitely many.
* `Polynomial.ncard_monicIrreduciblesOfDegree_one`: over a domain the monic irreducibles of degree
  one are the `X - C a`, as many as the elements of the coefficient ring.
* `Polynomial.Monic.irreducible_map_of_natDegree_eq_three`: a monic cubic over an integrally
  closed domain with no root in it is irreducible over the fraction field.
* `Polynomial.Monic.irreducible_map_of_natDegree_eq_four`: a monic quartic over an integrally
  closed domain with no root and no monic quadratic factor is irreducible over the fraction field.
* `Polynomial.Monic.exists_monic_mul_eq_irreducible_map`: a monic polynomial of positive degree
  over an integrally closed domain has a monic factor, with monic cofactor, that is irreducible
  over the fraction field.
-/

public section

namespace Polynomial

section Semiring

variable (R : Type*) [Semiring R]

/-- The monic irreducible polynomials of degree `d` over `R`.

The set depends only on `R` and `d`, which is what lets a counting argument compare it with an
unrelated family without assuming a bound on either. -/
def monicIrreduciblesOfDegree (d : ℕ) : Set R[X] :=
  {g | g.Monic ∧ Irreducible g ∧ g.natDegree = d}

variable {R} in
/-- Membership in `monicIrreduciblesOfDegree` is the conjunction defining it. -/
@[simp]
theorem mem_monicIrreduciblesOfDegree_iff {d : ℕ} {g : R[X]} :
    g ∈ monicIrreduciblesOfDegree R d ↔ g.Monic ∧ Irreducible g ∧ g.natDegree = d :=
  Iff.rfl

/-- **Over a finite coefficient ring there are finitely many monic irreducibles of each
degree.** -/
theorem finite_monicIrreduciblesOfDegree [Finite R] (d : ℕ) :
    (monicIrreduciblesOfDegree R d).Finite := by
  nontriviality R
  have : Finite (degreeLT R d) := .of_equiv _ (degreeLTEquiv R d).toEquiv.symm
  have hmon : {g : R[X] | g.Monic ∧ g.natDegree = d}.Finite :=
    Set.finite_coe_iff.mp (.of_equiv _ (monicEquivDegreeLT d).symm)
  exact hmon.subset fun g hg => ⟨hg.1, hg.2.2⟩

end Semiring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Over a domain, the monic irreducible polynomials of degree one are exactly the `X - C a`. -/
theorem monicIrreduciblesOfDegree_one :
    monicIrreduciblesOfDegree R 1 = Set.range fun a : R => X - C a := by
  ext g
  rw [mem_monicIrreduciblesOfDegree_iff, Set.mem_range]
  constructor
  · rintro ⟨hmon, -, hdeg⟩
    exact ⟨-g.coeff 0, by rw [C_neg, sub_neg_eq_add, ← hmon.eq_X_add_C hdeg]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩

variable (R) in
/-- Over a domain there are as many monic irreducible polynomials of degree one as elements of
the coefficient ring. -/
@[simp] theorem ncard_monicIrreduciblesOfDegree_one :
    (monicIrreduciblesOfDegree R 1).ncard = Nat.card R := by
  rw [monicIrreduciblesOfDegree_one]
  exact Set.ncard_range_of_injective (sub_right_injective.comp C_injective)

end Domain

end Polynomial

namespace Polynomial.Monic

variable {R K : Type*} [CommRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
  [IsFractionRing R K] {g : R[X]}

/-- A monic cubic over an integrally closed domain `R` with no root in `R` is irreducible over
the fraction field `K` of `R`. -/
theorem irreducible_map_of_natDegree_eq_three (hg : g.Monic) (hdeg : g.natDegree = 3)
    (hroot : ∀ m : R, g.eval m ≠ 0) : Irreducible (g.map (algebraMap R K)) := by
  refine irreducible_of_degree_le_three_of_not_isRoot
    (by rw [natDegree_map_eq_of_injective (IsFractionRing.injective R K), hdeg]; decide)
    fun x hx => ?_
  -- A root in `K` of the monic `g` is integral over `R`, hence lies in `R`.
  obtain ⟨m, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).mp
    ⟨g, hg, by rwa [← eval_map]⟩
  exact hroot m ((isRoot_map_iff (IsFractionRing.injective R K)).mp hx)

/-- A monic quartic over an integrally closed domain `R` with no root in `R` and no monic
quadratic factor over `R` is irreducible over the fraction field `K` of `R`. -/
theorem irreducible_map_of_natDegree_eq_four (hg : g.Monic) (hdeg : g.natDegree = 4)
    (hroot : ∀ m : R, g.eval m ≠ 0) (hquad : ∀ a b : R, ¬ X ^ 2 + C a * X + C b ∣ g) :
    Irreducible (g.map (algebraMap R K)) := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R K) (IsFractionRing.injective R K)
  rw [← hg.irreducible_iff_irreducible_map_fraction_map]
  exact hg.irreducible_of_degree_le_five_of_not_isRoot_of_not_quadratic_dvd (by rw [hdeg]; decide)
    hroot hquad

variable (K) in
/-- A monic polynomial of positive degree over an integrally closed domain `R` has a monic factor
over `R` that is irreducible over the fraction field `K`, with monic cofactor. -/
theorem exists_monic_mul_eq_irreducible_map {f : R[X]} (hf : f.Monic) (hdeg : f.natDegree ≠ 0) :
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

end Polynomial.Monic

end
