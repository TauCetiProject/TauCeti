/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic

import Mathlib.RingTheory.Valuation.ExtendToLocalization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Rational domains seen by continuous valuations

Let `A` be a normed ring with an ultrametric norm, and let `g, f₁, …, fₘ ∈ A`. A continuous
valuation `v` on `A` with `v(g) ≠ 0` and `v(fᵢ) ≤ v(g)` for every `i` lies in the rational subset
`R(f/g)` of the space of continuous valuations. This file shows that such a valuation forces the
rational fraction algebra `A⟨f/g⟩ = A⟨X₁, …, Xₘ⟩ ⧸ (g Xᵢ - fᵢ)` to be nonzero. For an affinoid
algebra `A` over a complete nonarchimedean field `K` with `(g, f₁, …, fₘ) = A`, the classical
rational domain `R(f/g) ⊆ Sp A` is then nonempty, since `A⟨f/g⟩` represents it.

So a rational subset of the adic spectrum that has a point at all has a classical point. This is
the input for the density of the classical points in `Spa (A, A°)`.

The proof is by contradiction. If `A⟨f/g⟩ = 0`, then `1 = ∑ᵢ hᵢ (g Xᵢ - fᵢ)` for restricted
series `hᵢ`. Approximating the `hᵢ` by polynomials `pᵢ` in the Gauss norm gives a polynomial
`P = 1 - ∑ᵢ pᵢ (g Xᵢ - fᵢ)` all of whose coefficients have norm less than one. Extend `v` to the
localization `A[1/g]` and evaluate `P` at `Xᵢ = fᵢ/g`. The relations vanish there, so `P`
evaluates to `1`. But each coefficient of `P` is topologically nilpotent, so has value less
than one under the continuous valuation `v`, while each `fᵢ/g` has value at most one. The
ultrametric inequality then bounds the value of `P(f/g)` strictly below one.

## Main results

* `TauCeti.RationalFraction.nontrivial_of_isContinuous`: a continuous valuation with
  `v(fᵢ) ≤ v(g) ≠ 0` makes `A⟨f/g⟩` nonzero.
* `TauCeti.IsAffinoidAlgebra.rationalDomain_nonempty_of_isContinuous`: for an affinoid algebra
  and `(g, f₁, …, fₘ) = A`, such a valuation makes the rational domain `R(f/g)` nonempty.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §7.2.2.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), §4.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries

namespace RationalFraction

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] {m : ℕ} {g : A} {f : Fin m → A}

/-- If `1` lies in the ideal of relations `(g Xᵢ - fᵢ)`, polynomials `pᵢ` make every coefficient of
`1 - ∑ᵢ pᵢ (g Xᵢ - fᵢ)` have norm less than one: approximate the coefficients of a relation
`1 = ∑ᵢ hᵢ (g Xᵢ - fᵢ)` by polynomials in the Gauss norm. -/
private theorem exists_norm_coeff_lt_one (h : (1 : IsRestricted.subring (R := A)
      (fun _ : Fin m ↦ 1)) ∈ rationalIdeal g f) :
    ∃ p : Fin m → MvPolynomial (Fin m) A, ∀ t, ‖(1 - ∑ i,
      p i * (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))).coeff t‖ < 1 := by
  set r : Fin m → IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) := fun i ↦
    algebraMap A _ g * ⟨X i, isRestricted_X _ i⟩ - algebraMap A _ (f i)
  rw [rationalIdeal_eq_span, Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  -- the polynomial tuples with `‖1 - ∑ᵢ pᵢ rᵢ‖ < 1` form an open set containing `c`
  set F : (Fin m → IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1)) →
      IsRestricted.subring (R := A) (fun _ : Fin m ↦ 1) := fun q ↦ 1 - ∑ i, q i * r i
  have hF : Continuous F := by fun_prop
  have hc : F c ∈ Metric.ball 0 1 := by simp [F, r, hc]
  obtain ⟨p, hp⟩ := (DenseRange.piMap fun _ ↦ denseRange_polynomialToRestricted).exists_mem_open
    (Metric.isOpen_ball.preimage hF) ⟨c, hc⟩
  refine ⟨p, fun t ↦ ?_⟩
  have hmap : polynomialToRestricted (fun _ : Fin m ↦ 1)
      (1 - ∑ i, p i * (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) =
      F (Pi.map (fun _ ↦ polynomialToRestricted (fun _ : Fin m ↦ 1)) p) := by
    simp only [map_sub, map_one, map_sum, map_mul, MvPolynomial.algHom_C,
      polynomialToRestricted_X, F, r, Pi.map_apply]
  rw [← MvPolynomial.coeff_coe, ← coe_polynomialToRestricted (c := fun _ : Fin m ↦ 1)]
  refine (norm_coeff_le_norm _ t).trans_lt ?_
  simpa [hmap] using hp

/-- **A continuous valuation on the rational subset makes `A⟨f/g⟩` nonzero.** If a continuous
valuation `v` on `A` satisfies `v(g) ≠ 0` and `v(fᵢ) ≤ v(g)` for every `i`, then the rational
fraction algebra `A⟨f/g⟩` is nontrivial. -/
theorem nontrivial_of_isContinuous {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation A Γ₀} (hv : v.IsContinuous) (hg : v g ≠ 0) (hf : ∀ i, v (f i) ≤ v g) :
    Nontrivial (RationalFraction g f) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop ↦ ?_
  obtain ⟨p, hp⟩ := exists_norm_coeff_lt_one (htop ▸ Submodule.mem_top)
  set P := 1 - ∑ i, p i * (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))
  -- extend `v` to `A[1/g]` and evaluate `P` at `Xᵢ = fᵢ/g`
  have hS : Submonoid.powers g ≤ v.supp.primeCompl := by
    rintro _ ⟨n, rfl⟩
    simp only [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, map_pow]
    exact pow_ne_zero n hg
  let S := Localization.Away g
  let w := v.extendToLocalization hS S
  let y : Fin m → S := fun i ↦ IsLocalization.mk' S (f i) ⟨g, Submonoid.mem_powers g⟩
  have hy (i : Fin m) : w (y i) ≤ 1 := by
    simpa [w, y] using mul_inv_le_one_of_le₀ (hf i) zero_le
  -- the relations vanish at `f/g`, so `P` evaluates to `1`
  have hgy (i : Fin m) : algebraMap A S g * y i = algebraMap A S (f i) :=
    IsLocalization.mk'_spec' S (f i) ⟨g, Submonoid.mem_powers g⟩
  have hP : MvPolynomial.aeval y P = 1 := by
    simp [P, hgy]
  -- every term of `P(f/g)` has value less than one
  have hlt : w (MvPolynomial.aeval y P) < 1 := by
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    refine Valuation.map_sum_lt _ one_ne_zero fun d _ ↦ ?_
    rw [map_mul, map_prod, Valuation.extendToLocalization_apply_map_apply]
    refine (mul_le_of_le_one_right' (Finset.prod_le_one fun i _ ↦ ?_)).trans_lt ?_
    · exact (map_pow w _ _).trans_le (pow_le_one' (hy i) _)
    · exact hv.lt_one_of_isTopologicallyNilpotent
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hp d))
  simp [hP] at hlt

end RationalFraction

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]
  {m : ℕ} {g : A} {f : Fin m → A}

/-- **A continuous valuation on a rational subset gives a classical point.** Let `A` be an
affinoid algebra with a complete ultrametric algebra norm and `g, f₁, …, fₘ` generate the unit
ideal of `A`. If a continuous valuation `v` on `A` satisfies `v(g) ≠ 0` and `v(fᵢ) ≤ v(g)` for
every `i`, then the rational domain `R(f/g) ⊆ Sp A` is nonempty. -/
theorem rationalDomain_nonempty_of_isContinuous (hA : IsAffinoidAlgebra K A)
    (h : Ideal.span (insert g (Set.range f)) = ⊤) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀} (hv : v.IsContinuous)
    (hg : v g ≠ 0) (hf : ∀ i, v (f i) ≤ v g) :
    (rationalDomain K g f).Nonempty :=
  ((RationalFraction.isAffinoidSubdomainMap hA h).nonempty_iff_nontrivial hA).mpr
    (RationalFraction.nontrivial_of_isContinuous hv hg hf)

end IsAffinoidAlgebra

end TauCeti
