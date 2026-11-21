/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.PrModule
public import TauCeti.NumberTheory.NewtonPolygon.Preparation
import TauCeti.NumberTheory.NewtonPolygon.Factorization

/-!
# Finite-slope decompositions of compact operators

Let `u` be a `(Pr)`-compact endomorphism of a Banach module `M` with property `(Pr)` over a
complete ultrametric norm-one Tate ring `R`, with Fredholm series `H_u = det (1 - T u)`.

**Over a coefficient ring.** If `H_u` is multiplicatively distinguished of degree `N` at a
radius `c > 0`, its normalised entire preparation `H_u = Q * S` at `c` has a polynomial factor `Q`
of degree `N` with unit leading coefficient, coprime to the entire factor `S`. The Riesz–Coleman
decomposition along this factorisation splits off the finite projective summand `ker Q*(u)`, of
constant rank `N` on `Spec R`, together with a closed `u`-stable complement on which `Q*(u)` is
invertible.

**Over a field.** Let `K` be a complete ultrametric nontrivially normed field whose norm comes
from a real additive valuation `v` with base `b > 1`. For every real cutoff `h`, the Fredholm series
is multiplicatively distinguished at the radius `b ^ h` in the degree
`N_h = ∑ᶠ s ∈ Set.Iic h, H_u.newtonSlopeMultiplicity v s`, the number of slopes of the Fredholm
polygon at most `h`, counted with multiplicity. The normalised preparation at `b ^ h` is therefore
the slope factorisation `H_u = Q_(≤h) * S_(>h)`, where `Q_(≤h)` carries exactly the slopes at most
`h` and `S_(>h)` exactly those greater than `h`. The associated Riesz–Coleman summand

  `M_(≤h) = ker Q_(≤h)*(u)`

is the **finite-slope part** of `u` at the cutoff `h`: it has dimension `N_h`, `u` is invertible
on it, and it has a closed `u`-stable complement on which `Q_(≤h)*(u)` is invertible. These
subspaces are nested: `M_(≤h) ⊆ M_(≤h')` whenever `h ≤ h'`, because the polynomial factor at the
smaller radius divides the one at the larger radius. Each slope `σ ≤ h` also has its own summand
inside `M_(≤h)`: the slope-`σ` factor `g` of the pure slope factorisation of `Q_(≤h)` is coprime to
its cofactor in `H_u`, and the Riesz–Coleman summand `ker g*(u)` has dimension the multiplicity of
`σ`.

## Main results

* `ContinuousLinearMap.IsPrCompact.isMulDistinguished_finsum_newtonSlopeMultiplicity`: over a
  field, the Fredholm series is multiplicatively distinguished at `b ^ h` in the degree `N_h`.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection_of_isMulDistinguished`: the
  finite projective rank-`N` summand attached to a multiplicatively distinguished Fredholm series
  over a coefficient ring.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection_finiteSlope`: over a field, the
  finite-slope decomposition at any cutoff `h`, with the slopes of both factors and
  `dim M_(≤h) = N_h`.
* `ContinuousLinearMap.IsPrCompact.range_le_range_of_le`: the finite-slope summands increase with
  the cutoff.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszColemanProjection_pureSlope`: the summand of a
  single slope `σ ≤ h`, of dimension its multiplicity, inside the finite-slope summand at `h`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A4–A5.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open TauCeti.PowerSeries (IsEntirePreparation IsMulDistinguished)
open scoped PowerSeries

namespace ContinuousLinearMap

section Ring

variable {R M : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- **The finite projective summand of a distinguished Fredholm series.** Let `u` be a
`(Pr)`-compact endomorphism whose Fredholm series `H_u` is multiplicatively distinguished of degree
`N` at a radius `c > 0`. Then `H_u` has a normalised entire preparation `H_u = Q * S` at `c` in
degree `N`, and `u` has a Riesz–Coleman projection `E` for `Q` whose range `ker Q*(u)` has rank `N`
at every prime of `R`. -/
theorem IsPrCompact.exists_isRieszColemanProjection_of_isMulDistinguished {u : M →L[R] M}
    (hu : u.IsPrCompact) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : IsMulDistinguished c N u.charPowerSeries) :
    ∃ (Q : R[X]) (S : R⟦X⟧) (E : M →L[R] M),
      IsEntirePreparation c N u.charPowerSeries Q S ∧ IsRieszColemanProjection u Q E ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = N := by
  obtain ⟨Q, S, hQS⟩ := hN.exists_isEntirePreparation hc hu.isEntire_charPowerSeries
    u.constantCoeff_charPowerSeries
  have hcop := hQS.isCoprime hN hc
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQS.coeff_zero_eq_one
    hQS.isUnit_leadingCoeff hQS.isEntire hQS.eq_mul hcop
  refine ⟨Q, S, E, hQS, hE, fun p ↦ ?_⟩
  rw [hE.rankAtStalk_range_of_isPrCompact hu hQS.coeff_zero_eq_one hQS.isUnit_leadingCoeff
    hQS.isEntire hQS.eq_mul hcop p, hQS.natDegree_eq]

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M] {u : M →L[K] M}

include hb hv

omit [IsBoundedSMul K M] in
/-- **The distinguished degree of a Fredholm series.** The Fredholm series `H_u` of a
`(Pr)`-compact endomorphism over a complete ultrametric field whose norm comes from `v` with base
`b` is multiplicatively distinguished at the radius `b ^ h` in the degree
`N_h = ∑ᶠ s ∈ Set.Iic h, H_u.newtonSlopeMultiplicity v s`, the number of slopes of the Fredholm
polygon at most `h`, counted with multiplicity. -/
theorem IsPrCompact.isMulDistinguished_finsum_newtonSlopeMultiplicity (hu : u.IsPrCompact)
    (h : ℝ) :
    IsMulDistinguished (b ^ h)
      (∑ᶠ s ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v s) u.charPowerSeries :=
  hu.isEntire_charPowerSeries.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv (by simp) h

/-- **The finite-slope decomposition at a cutoff.** Let `u` be a `(Pr)`-compact endomorphism over a
complete ultrametric field whose norm comes from `v` with base `b`, and let `h` be a real cutoff.
Write `N_h = ∑ᶠ s ∈ Set.Iic h, H_u.newtonSlopeMultiplicity v s` for the number of slopes of the
Fredholm polygon at most `h`, with multiplicity. Then the normalised entire preparation
`H_u = Q * S` at the radius `b ^ h` has degree `N_h`, `Q` carries exactly the slopes of `H_u` at
most `h` and `S` exactly those greater than `h`, and `u` has a Riesz–Coleman projection `E` for `Q`
whose range `ker Q*(u)` has dimension `N_h`. -/
theorem IsPrCompact.exists_isRieszColemanProjection_finiteSlope (hu : u.IsPrCompact) (h : ℝ) :
    ∃ (Q : K[X]) (S : K⟦X⟧) (E : M →L[K] M),
      IsEntirePreparation (b ^ h)
        (∑ᶠ s ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v s) u.charPowerSeries Q S ∧
      (∀ s, (Q : K⟦X⟧).newtonSlopeMultiplicity v s =
        if s ≤ h then u.charPowerSeries.newtonSlopeMultiplicity v s else 0) ∧
      (∀ s, S.newtonSlopeMultiplicity v s =
        if s ≤ h then 0 else u.charPowerSeries.newtonSlopeMultiplicity v s) ∧
      IsRieszColemanProjection u Q E ∧
      Module.finrank K E.range =
        ∑ᶠ s ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v s := by
  have hN := hu.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv h
  have hc : 0 < b ^ h := Real.rpow_pos_of_pos (zero_lt_one.trans hb) h
  obtain ⟨Q, S, E, hQS, hE, -⟩ := hu.exists_isRieszColemanProjection_of_isMulDistinguished hc hN
  refine ⟨Q, S, E, hQS, hQS.newtonSlopeMultiplicity_left v hb hv hN.toIsDistinguished,
    hQS.newtonSlopeMultiplicity_right v hb hv hN.toIsDistinguished, hE, ?_⟩
  rw [hE.finrank_range_of_isPrCompact hu hQS.coeff_zero_eq_one hQS.isEntire hQS.eq_mul
    (hQS.isCoprime hN hc), hQS.natDegree_eq]

/-- **The finite-slope summands increase with the cutoff.** Let `u` be `(Pr)`-compact, let
`h ≤ h'`, and let `H_u = Q * S` be the normalised entire preparation at `b ^ h` in degree
`N_h = ∑ᶠ s ∈ Set.Iic h, H_u.newtonSlopeMultiplicity v s` and `H_u = Q' * S'` a normalised entire
preparation at `b ^ h'`. Then the range of any Riesz–Coleman projection of `u` for `Q` lies in the
range of any Riesz–Coleman projection of `u` for `Q'`. -/
theorem IsPrCompact.range_le_range_of_le (hu : u.IsPrCompact) {h h' : ℝ} (hhh' : h ≤ h')
    {Q Q' : K[X]} {S S' : K⟦X⟧} {d' : ℕ} {E E' : M →L[K] M}
    (hQS : IsEntirePreparation (b ^ h)
      (∑ᶠ s ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v s) u.charPowerSeries Q S)
    (hQS' : IsEntirePreparation (b ^ h') d' u.charPowerSeries Q' S')
    (hE : IsRieszColemanProjection u Q E) (hE' : IsRieszColemanProjection u Q' E') :
    E.range ≤ E'.range := by
  have hN := hu.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv h
  have hb0 : 0 < b := zero_lt_one.trans hb
  exact hE.range_le_range_of_dvd hE' hQS.isUnit_leadingCoeff <|
    hQS.dvd_of_le hQS' hN.toIsDistinguished (Real.rpow_pos_of_pos hb0 h)
      (Real.rpow_le_rpow_of_exponent_le hb.le hhh')

/-- **Pure-slope summands.** Let `u` be `(Pr)`-compact, and let `H_u = Q * S` be the normalised
entire preparation at `b ^ h` in degree `N_h = ∑ᶠ s ∈ Set.Iic h, H_u.newtonSlopeMultiplicity v s`.
For every slope `σ ≤ h` there are a factor `g` of `Q` with `g(0) = 1`, all of whose finite slopes
equal `σ`, of degree the multiplicity of `σ`, and a Riesz–Coleman projection `E` of `u` for `g`.
Its range `ker g*(u)` has dimension the multiplicity of `σ` and lies in the finite-slope summand
`ker Q*(u)`. -/
theorem IsPrCompact.exists_isRieszColemanProjection_pureSlope (hu : u.IsPrCompact) {h σ : ℝ}
    (hσh : σ ≤ h) {Q : K[X]} {S : K⟦X⟧}
    (hQS : IsEntirePreparation (b ^ h)
      (∑ᶠ s ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v s) u.charPowerSeries Q S) :
    ∃ (g : K[X]) (E : M →L[K] M), g.coeff 0 = 1 ∧ (∀ s ∈ g.newtonSlopes v, s = σ) ∧
      g.natDegree = u.charPowerSeries.newtonSlopeMultiplicity v σ ∧ g ∣ Q ∧
      IsRieszColemanProjection u g E ∧
      Module.finrank K E.range = u.charPowerSeries.newtonSlopeMultiplicity v σ ∧
      ∀ E' : M →L[K] M, IsRieszColemanProjection u Q E' → E.range ≤ E'.range := by
  have hN := hu.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv h
  have hc : 0 < b ^ h := Real.rpow_pos_of_pos (zero_lt_one.trans hb) h
  -- Split off the slope-`σ` factor `g σ` of `Q` together with a coprime cofactor `c`.
  obtain ⟨g, hg⟩ := Polynomial.exists_isPureSlopeFactorization v hb hv hQS.coeff_zero_eq_one
  obtain ⟨c, hgc, hgcQ⟩ := hg.exists_isCoprime_mul_eq σ
  have hdeg : (g σ).natDegree = u.charPowerSeries.newtonSlopeMultiplicity v σ := by
    rw [hg.natDegree_apply (fun _ ↦ v.top_iff.mp), ← Polynomial.newtonSlopeMultiplicity_coe,
      hQS.newtonSlopeMultiplicity_left v hb hv hN.toIsDistinguished]
    simp [hσh]
  have hlc : IsUnit (g σ).leadingCoeff :=
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (hg.apply_ne_zero σ))
  have hcS : ((c : K⟦X⟧) * S).IsEntire := (PowerSeries.isEntire_coe c).mul hQS.isEntire
  have hH : u.charPowerSeries = (g σ : K⟦X⟧) * ((c : K⟦X⟧) * S) := by
    rw [hQS.eq_mul, ← hgcQ, Polynomial.coe_mul, mul_assoc]
  have hcop := hQS.isCoprime_of_isCoprime_mul_eq hN hc hgc hgcQ
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection (hg.coeff_zero σ) hlc hcS hH hcop
  refine ⟨g σ, E, hg.coeff_zero σ, hg.newtonSlopes_eq σ, hdeg, ⟨c, hgcQ.symm⟩, hE, ?_,
    fun E' hE' ↦ hE.range_le_range_of_dvd hE' hlc ⟨c, hgcQ.symm⟩⟩
  rw [hE.finrank_range_of_isPrCompact hu (hg.coeff_zero σ) hcS hH hcop, hdeg]

end Field

end ContinuousLinearMap
