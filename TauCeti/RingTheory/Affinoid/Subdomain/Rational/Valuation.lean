/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic

import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.RingTheory.Huber.Restricted.GaussNorm
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.ExtendToLocalization
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Rational domains seen by continuous valuations

Let `A` be a normed ring with an ultrametric norm, and let `g, f₁, …, fₘ ∈ A`. A continuous
valuation `v` on `A` with `v(g) ≠ 0` and `v(fᵢ) ≤ v(g)` for every `i` lies in the rational subset
`R(f/g)` of the space of continuous valuations. This file shows that such a valuation forces the
rational fraction algebra `A⟨f/g⟩ = A⟨X₁, …, Xₘ⟩ ⧸ (g Xᵢ - fᵢ)` to be nonzero. For an affinoid
algebra `A` over a complete nonarchimedean field `K` with `(g, f₁, …, fₘ) = A`, the classical
rational domain `R(f/g) ⊆ Sp A` is then nonempty, since `A⟨f/g⟩` represents it.

The unit-ideal condition can be dropped: a continuous valuation gives some power `u` of a scalar
of norm less than one the value `v(u) < v(g)`, and adding the unit `u` to the numerators shrinks
`R(f/g)` to a rational domain whose numerators generate the unit ideal. Nor is a norm on `A`
needed: a `K`-algebra topologically of finite type is a quotient of a Tate algebra by a closed
ideal, which carries a complete ultrametric residue norm.

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
  with a complete ultrametric algebra norm, such a valuation makes the rational domain `R(f/g)`
  nonempty.
* `TauCeti.Huber.IsTopologicallyFiniteType.rationalDomain_nonempty_of_isContinuous`: the same for
  a `K`-algebra topologically of finite type, with no norm.

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
  let S := Localization.Away g
  let w := v.extendToLocalization (Valuation.powers_le_supp_primeCompl hg) S
  let y : Fin m → S := fun i ↦ Localization.divBy (f i) g
  -- the relations vanish at `f/g`, so `P` evaluates to `1`
  have hP : MvPolynomial.aeval y P = 1 := by
    simp [P, y]
  -- every term of `P(f/g)` has value less than one
  have hlt : w (MvPolynomial.aeval y P) < 1 := by
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    refine Valuation.map_sum_lt _ one_ne_zero fun d _ ↦ ?_
    rw [map_mul, map_prod, Valuation.extendToLocalization_apply_map_apply]
    refine (mul_le_of_le_one_right' (Finset.prod_le_one fun i _ ↦ ?_)).trans_lt ?_
    · exact (map_pow w _ _).trans_le
        (pow_le_one' (Valuation.extendToLocalization_divBy_le_one S hg (hf i)) _)
    · exact hv.lt_one_of_isTopologicallyNilpotent
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hp d))
  simp [hP] at hlt

end RationalFraction

namespace IsAffinoidAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A] [CompleteSpace A]
  {m : ℕ} {g : A} {f : Fin m → A}

/-- **A continuous valuation on a rational subset gives a classical point.** Let `A` be an
affinoid algebra with a complete ultrametric algebra norm. If a continuous valuation `v` on `A`
satisfies `v(g) ≠ 0` and `v(fᵢ) ≤ v(g)` for every `i`, then the rational domain `R(f/g) ⊆ Sp A`
is nonempty. -/
theorem rationalDomain_nonempty_of_isContinuous (hA : IsAffinoidAlgebra K A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀} (hv : v.IsContinuous)
    (hg : v g ≠ 0) (hf : ∀ i, v (f i) ≤ v g) :
    (rationalDomain K g f).Nonempty := by
  -- some power `u` of a scalar of norm less than one has `v u < v g`, as these powers tend to 0
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt K one_pos
  have hcnil : IsTopologicallyNilpotent c := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁
  obtain ⟨n, hn⟩ := ((hcnil.map (continuous_algebraMap K A)).eventually
    ((Valuation.isContinuous_def.mp hv g).mem_nhds (by simpa using pos_iff_ne_zero.mpr hg))).exists
  -- adding the unit `u` to the numerators makes them generate the unit ideal
  let f' : Fin (m + 1) → A := Fin.cons (algebraMap K A c ^ n) f
  have hu : IsUnit (algebraMap K A c ^ n) :=
    ((IsUnit.mk0 c (norm_pos_iff.mp hc₀)).map (algebraMap K A)).pow n
  have h : Ideal.span (insert g (Set.range f')) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨0, rfl⟩)) hu
  have hf' (i : Fin (m + 1)) : v (f' i) ≤ v g := Fin.cases hn.le hf i
  obtain ⟨x, hx⟩ := ((RationalFraction.isAffinoidSubdomainMap hA h).nonempty_iff_nontrivial hA).mpr
    (RationalFraction.nontrivial_of_isContinuous hv hg hf')
  exact ⟨x, mem_rationalDomain.mpr ⟨(mem_rationalDomain.mp hx).1,
    fun i ↦ by simpa [f'] using (mem_rationalDomain.mp hx).2 i.succ⟩⟩

end IsAffinoidAlgebra

namespace Huber.IsTopologicallyFiniteType

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra K A] {m : ℕ} {g : A} {f : Fin m → A}
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation A Γ₀}

/-- The case of `TauCeti.Huber.IsTopologicallyFiniteType.rationalDomain_nonempty_of_isContinuous`
for a continuous surjection `φ` from a normed affinoid algebra `B` onto `A` with `{0}` closed: the
quotient by the closed kernel, with its residue norm, is a normed affinoid algebra isomorphic to
`A`. -/
private theorem rationalDomain_nonempty_of_surjective {B : Type*} [NormedCommRing B]
    [IsUltrametricDist B] [NormedAlgebra K B] [CompleteSpace B] (hB : IsAffinoidAlgebra K B)
    (φ : B →A[K] A) (hφ : Function.Surjective φ) (h0 : IsClosed ({0} : Set A))
    (hv : v.IsContinuous) (hg : v g ≠ 0) (hf : ∀ i, v (f i) ≤ v g) :
    (rationalDomain K g f).Nonempty := by
  have : IsClosed ((RingHom.ker (φ : B →ₐ[K] A) : Ideal B) : Set B) := by
    simpa [RingHom.ker_eq] using h0.preimage φ.continuous
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := (φ : B →ₐ[K] A)) hφ
  have hC := hB.quotient (RingHom.ker (φ : B →ₐ[K] A))
  obtain ⟨y, hy⟩ := hC.rationalDomain_nonempty_of_isContinuous (g := e.symm g)
    (f := fun i ↦ e.symm (f i)) (v := v.comap e.toRingEquiv.toRingHom)
    (hv.comap (ContinuousAlgHom.continuous_quotientKerAlgEquivOfSurjective φ hφ))
    (by simpa using hg) (by simpa using hf)
  exact ⟨hC.maximalSpectrumComap e.symm.toAlgHom y, by simpa using hy⟩

/-- **A continuous valuation on a rational subset gives a classical point**, for a `K`-algebra
`A` topologically of finite type. If a continuous valuation `v` on `A` satisfies `v(g) ≠ 0` and
`v(fᵢ) ≤ v(g)` for every `i`, then the rational domain `R(f/g) ⊆ Sp A` is nonempty. A
presentation identifies `A` with a quotient of a Tate algebra by a closed ideal, which carries a
complete ultrametric residue norm, so this reduces to
`TauCeti.IsAffinoidAlgebra.rationalDomain_nonempty_of_isContinuous`. -/
theorem rationalDomain_nonempty_of_isContinuous (hA : IsTopologicallyFiniteType (algebraMap K A))
    (hv : v.IsContinuous) (hg : v g ≠ 0) (hf : ∀ i, v (f i) ≤ v g) :
    (rationalDomain K g f).Nonempty := by
  -- a continuous surjection `φ` onto `A` from the Gauss-normed Tate algebra
  obtain ⟨n, π, hπ, hcomp⟩ :=
    isStrictlyTopologicallyFiniteType_iff.mp hA.isStrictlyTopologicallyFiniteType
  let ε := (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)).symm
  let π' : restrictedMvPowerSeriesCompletion n K →ₐ[K] A :=
    { π with commutes' := fun r ↦ congrArg (· r) hcomp }
  let φ : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →A[K] A :=
    ⟨π'.comp ε.toAlgHom, hπ.continuous.comp <| by
      simpa [ε, coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm] using
        continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm (n := n) (R := K)⟩
  exact rationalDomain_nonempty_of_surjective isAffinoidAlgebra_tate φ
    (hπ.surjective.comp ε.surjective) (by simpa using hA.isClosed_ideal ⊥) hv hg hf

end Huber.IsTopologicallyFiniteType

end TauCeti
