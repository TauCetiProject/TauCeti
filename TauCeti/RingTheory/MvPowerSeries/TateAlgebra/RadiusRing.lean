/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
public import TauCeti.RingTheory.WittVector.RadiusRing

/-!
# Restricted power series over the radius rings `A^r` are noetherian

The radius ring `A^r` (`TauCeti.WittVector.RadiusRing`) is complete, with a multiplicative
ultrametric norm, and its degree only depends on the leading part of an element
(`TauCeti.WittVector.RadiusRing.degree_eq_of_norm_sub_lt`, Kedlaya's Remark 2.7) and admits
Euclidean division (`TauCeti.WittVector.RadiusRing.exists_eq_mul_add`, Kedlaya's
Proposition 2.9). These are the hypotheses of
`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`, so the rings
`A^r{T₁/ρ₁, …, Tₙ/ρₙ}` of restricted power series are noetherian (Kedlaya, Theorem 3.2).

## Main results

* `TauCeti.WittVector.RadiusRing.isNoetherianRing_isRestricted_subring` : the rings
  `A^r{T₁/ρ₁, …, Tₙ/ρₙ}` of restricted power series are noetherian.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Remark 2.7, Proposition 2.9 and Theorem 3.2.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector.RadiusRing

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  {v : Valuation K ℝ≥0} {ϖ : O} [CharP O p] [PerfectRing O p]
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ : ℝ≥0}
  (hρ : ρ ∈ Set.Ioo 0 1)

/-- **Kedlaya's Hilbert basis theorem for `A^r`** (Kedlaya, Theorem 3.2). For finitely many
variables and all positive radii `c`, the ring `A^r{T/c}` of restricted power series over the
radius ring with its Gauss norm is noetherian. -/
instance isNoetherianRing_isRestricted_subring {σ : Type*} [Finite σ] {c : σ → ℝ}
    [∀ i, Fact (0 < c i)] :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := RadiusRing p hv hϖ hϖ' hρ) c) :=
  TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division
    (degree p hv hϖ hϖ' hρ) (fun _ _ h ↦ degree_eq_of_norm_sub_lt p hv hϖ hϖ' hρ h)
    fun _ y hx ↦ exists_eq_mul_add p hv hϖ hϖ' hρ hx y

end TauCeti.WittVector.RadiusRing
