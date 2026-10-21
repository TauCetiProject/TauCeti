/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# Good reduction outside finitely many primes

An elliptic Weierstrass equation over the fraction field of a Dedekind domain has integral
coefficients and unit discriminant in almost every completed valuation ring. The equation itself
therefore gives an elliptic integral model at all but finitely many primes; no global minimal
equation is needed.

For a nonzero multiplier `m`, one can also exclude the primes dividing `m`. The resulting finite
exceptional set supplies the good-reduction and residue-characteristic conditions used to show
that Kummer classes, and hence Selmer classes, are unramified outside a finite set.

The statements use the ring of integers `𝒪[K_v]` of the canonical valuative relation, so that
they apply directly to local Galois cohomology. An elliptic integral model means that its
discriminant is a unit in that ring, a stronger condition than just ellipticity over `K_v`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1 and X.4.2.
-/

public section

namespace TauCeti

open IsDedekindDomain ValuativeRel WeierstrassCurve

open scoped WithZero

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An elliptic equation has an elliptic integral model over almost every completed valuation
ring. The model base changes to the given equation itself, without a change of variables. -/
theorem eventually_isElliptic_integralModel_adicCompletion (W : WeierstrassCurve K)
    [W.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)),
        (integralModel 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K))).IsElliptic := by
  have hint (x : K) : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ∃ y : 𝒪[v.adicCompletion K],
        algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K) y =
          algebraMap K (v.adicCompletion K) x := by
    filter_upwards [(algebraMap K (FiniteAdeleRing R K) x).cofinite_mem_adicCompletionIntegers]
      with v hv
    refine ⟨⟨algebraMap K (v.adicCompletion K) x, ?_⟩, rfl⟩
    rw [v.integer_eq_adicCompletionIntegers, ValuationSubring.mem_toSubring]
    simpa only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self_apply] using hv
  filter_upwards [hint W.a₁, hint W.a₂, hint W.a₃, hint W.a₄, hint W.a₆,
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := R)
      W.isUnit_Δ.ne_zero).eventually_cofinite_notMem] with v h₁ h₂ h₃ h₄ h₆ hΔ
  have hΔ' : v.valuation K W.Δ = 1 := not_not.mp hΔ
  have hI : IsIntegral 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
    isIntegral_of_exists_lift _ h₁ h₂ h₃ h₄ h₆
  refine ⟨hI, ?_⟩
  rw [isElliptic_iff]
  exact (isUnit_integer_adicCompletion_iff_valuation_eq_one R v
    (by rw [integralModel_Δ_eq, baseChange, map_Δ])).mpr hΔ'

/-- Outside a finite set containing any prescribed finite set of primes, an elliptic equation
has an elliptic integral model and a nonzero multiplier is prime to the residue characteristic.
This supplies the exceptional set for the unramified local Kummer conditions. -/
theorem exists_finset_isElliptic_integralModel_adicCompletion (W : WeierstrassCurve K)
    [W.IsElliptic]
    {m : ℕ} (hm : (m : K) ≠ 0) (S : Finset (HeightOneSpectrum R)) :
    ∃ T : Finset (HeightOneSpectrum R), S ⊆ T ∧
      (∀ v ∉ T, ∃ _ : IsIntegral 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)),
        (integralModel 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K))).IsElliptic) ∧
      (∀ v ∉ T, (m : R) ∉ v.asIdeal) := by
  classical
  have hmodel := eventually_isElliptic_integralModel_adicCompletion R W
  have hm' : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (m : R) ∉ v.asIdeal := by
    filter_upwards [(HeightOneSpectrum.finite_setOfPred_valuation_ne_one
      (R := R) hm).eventually_cofinite_notMem] with v hv
    intro hmem
    exact hv (ne_of_lt (by
      simpa only [map_natCast] using
        (v.valuation_lt_one_iff_mem (K := K) (m : R)).mpr hmem))
  have hfinite := Filter.eventually_cofinite.mp (hm'.and hmodel)
  have hout (v) (hv : v ∉ S ∪ hfinite.toFinset) := by
    have hv' : v ∉ hfinite.toFinset := fun h => hv (Finset.mem_union_right S h)
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv'
  exact ⟨S ∪ hfinite.toFinset, Finset.subset_union_left,
    fun v hv => (hout v hv).2, fun v hv => (hout v hv).1⟩

end TauCeti
