/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Division
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Weierstrass.Preparation

/-!
# Weierstrass theory in a specified variable

An equivalence `e : ι ≃ Option σ` selects the variable `e.symm none` and labels the other
variables by `σ`. The isometric comparison `MvPowerSeries.restrictedSplitEquiv` transports
Weierstrass division and preparation to that variable. The radii in the original labelling are
`c ∘ e`; no radius is replaced by one, and no scalar rescaling is required.

Remainders are characterized in the original coordinates: their coefficient at `t` vanishes
when `s ≤ t (e.symm none)`. The polynomial factor in preparation has restricted coefficients in
the remaining variables and is transported back by the inverse splitting equivalence. Thus
both division and preparation retain their uniqueness and their Gauss norm estimates after
reindexing. Taking `e = finSuccEquiv n` selects variable `0` in `Fin (n + 1)`.

The coefficient ring can have nilpotents; its norm need not be multiplicative. Neither the
variable types nor the coefficient ring need be finite. Completeness is used only for existence.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27, Corollary 1.28 and the several-variable
  remark following it.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {ι σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {c : Option σ → ℝ} [∀ i, Fact (0 < c i)] (e : ι ≃ Option σ) {s : ℕ}

local notation "Inner" => IsRestricted.subring (R := R) (fun i : σ ↦ c (some i))
local notation "Flat" => IsRestricted.subring (R := R) (c ∘ e)

/-- The division norm identity in the variable selected by `e`, expressed in the original
coordinates. No multiplicativity of the coefficient norm is assumed. -/
theorem norm_mul_add_eq_max_of_isMulDistinguished_split {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) (q : Flat) {r : Flat}
    (hr : ∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (r : MvPowerSeries ι R) = 0) :
    ‖g * q + r‖ = max (‖g‖ * ‖q‖) ‖r‖ := by
  have h := hg.gaussNorm_mul_add_eq_max Fact.out (restrictedSplitEquiv e q).2
    ((forall_coeff_restrictedSplitEquiv_eq_zero_iff e r s).mpr hr)
  simpa only [← PowerSeries.norm_eq_gaussNorm, ← Subring.coe_mul, ← Subring.coe_add,
    ← map_mul, ← map_add, norm_restrictedSplitEquiv] using h

/-- Division in the selected variable is unique, without completeness and without any norm
bounds on the competing decompositions. -/
theorem eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished_split {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) {q q' r r' : Flat}
    (hr : ∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (r : MvPowerSeries ι R) = 0)
    (hr' : ∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (r' : MvPowerSeries ι R) = 0)
    (h : g * q + r = g * q' + r') : q = q' ∧ r = r' := by
  have h' := congrArg (fun x : Flat ↦ (restrictedSplitEquiv e x : PowerSeries Inner)) h
  simp only [map_add, map_mul, Subring.coe_add, Subring.coe_mul] at h'
  obtain ⟨hq, hr⟩ := hg.eq_and_eq_of_mul_add_eq_mul_add Fact.out (restrictedSplitEquiv e q).2
    (restrictedSplitEquiv e q').2 ((forall_coeff_restrictedSplitEquiv_eq_zero_iff e r s).mpr hr)
    ((forall_coeff_restrictedSplitEquiv_eq_zero_iff e r' s).mpr hr') h'
  exact ⟨(restrictedSplitEquiv e).injective (Subtype.ext hq),
    (restrictedSplitEquiv e).injective (Subtype.ext hr)⟩

/-- Weierstrass division in any specified variable, with quotient and remainder estimates in
the original Gauss norm. The remainder has degree less than `s` in `e.symm none`.
This includes degree zero, where the remainder is zero. -/
theorem exists_mul_add_eq_of_isMulDistinguished_split [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) (f : Flat) :
    ∃ q r : Flat,
      (∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (r : MvPowerSeries ι R) = 0) ∧
      g * q + r = f ∧ ‖q‖ ≤ ‖f‖ / ‖g‖ ∧ ‖r‖ ≤ ‖f‖ := by
  let E := IsRestricted.renameAlgEquiv (R := R) e c
  obtain ⟨q, r, hr, hqr, hqnorm, hrnorm⟩ := exists_mul_add_eq_of_isMulDistinguished
    (g := E g) (by simpa only [restrictedSplitEquiv_apply] using hg) (E f)
  refine ⟨E.symm q, E.symm r, ?_, ?_, ?_, ?_⟩
  · apply (forall_coeff_restrictedSplitEquiv_eq_zero_iff e _ s).mp
    simpa only [restrictedSplitEquiv_apply, E, AlgEquiv.apply_symm_apply] using
      (forall_coeff_restrictedOptionEquiv_eq_zero_iff r s).mpr hr
  · apply E.injective
    simpa using hqr
  · rw [← IsRestricted.norm_renameAlgEquiv e c (E.symm q)]
    simpa only [E, AlgEquiv.apply_symm_apply, IsRestricted.norm_renameAlgEquiv] using hqnorm
  · rw [← IsRestricted.norm_renameAlgEquiv e c (E.symm r)]
    simpa only [E, AlgEquiv.apply_symm_apply, IsRestricted.norm_renameAlgEquiv] using hrnorm

/-- Every dividend has exactly one quotient-remainder pair in the selected variable.
Uniqueness does not impose the estimates as extra hypotheses. -/
theorem existsUnique_mul_add_eq_of_isMulDistinguished_split [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) (f : Flat) :
    ∃! p : Flat × Flat,
      (∀ t : ι →₀ ℕ, s ≤ t (e.symm none) → coeff t (p.2 : MvPowerSeries ι R) = 0) ∧
      g * p.1 + p.2 = f := by
  obtain ⟨q, r, hr, hqr, -⟩ := exists_mul_add_eq_of_isMulDistinguished_split e hg f
  refine ⟨(q, r), ⟨hr, hqr⟩, fun p ⟨hp, hpf⟩ ↦ ?_⟩
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_add_eq_mul_add_of_isMulDistinguished_split e hg
    hp hr (hpf.trans hqr.symm)
  exact Prod.ext h1 h2

/-- Preparation in the selected variable is unique among unit factors and monic degree-`s`
polynomials, even if no norm normalisation of the polynomial is assumed. -/
theorem eq_and_eq_of_mul_eq_of_mul_eq_of_isMulDistinguished_split {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) {u u' : Flat} {ω ω' : Polynomial Inner}
    (hu : IsUnit u) (hu' : IsUnit u')
    (hω : ω.IsMonicOfDegree s) (hω' : ω'.IsMonicOfDegree s)
    (h : u * (restrictedSplitEquiv e).symm (PowerSeries.polynomialToRestricted (c none) ω) = g)
    (h' : u' * (restrictedSplitEquiv e).symm (PowerSeries.polynomialToRestricted (c none) ω') = g) :
    u = u' ∧ ω = ω' := by
  have key {u : Flat} {ω : Polynomial Inner}
      (h : u * (restrictedSplitEquiv e).symm (PowerSeries.polynomialToRestricted (c none) ω) = g) :
      (restrictedSplitEquiv e u : PowerSeries Inner) * (ω : PowerSeries Inner) =
        (restrictedSplitEquiv e g : PowerSeries Inner) := by
    have hh := congrArg (fun x : Flat ↦ (restrictedSplitEquiv e x : PowerSeries Inner)) h
    simpa only [map_mul, AlgEquiv.apply_symm_apply, Subring.coe_mul,
      PowerSeries.coe_polynomialToRestricted] using hh
  obtain ⟨h1, h2⟩ := hg.eq_and_eq_of_mul_eq_of_mul_eq Fact.out
    (hu.map (restrictedSplitEquiv e)) (hu'.map (restrictedSplitEquiv e)) hω hω' (key h) (key h')
  exact ⟨(restrictedSplitEquiv e).injective h1, h2⟩

/-- Weierstrass preparation in any specified variable, with the polynomial's Gauss norm
normalised to `c none ^ s`. The unit factor is multiplicative even over a nonreduced Banach ring. -/
theorem exists_isNormMulUnit_isMonicOfDegree_mul_eq_of_isMulDistinguished_split
    [CompleteSpace R] {g : Flat}
    (hg : PowerSeries.IsMulDistinguished (c none) s
      (restrictedSplitEquiv e g : PowerSeries Inner)) :
    ∃ (u : Flat) (ω : Polynomial Inner), IsNormMulUnit u ∧ ω.IsMonicOfDegree s ∧
      ‖((restrictedSplitEquiv e).symm (PowerSeries.polynomialToRestricted (c none) ω) : Flat)‖ =
        c none ^ s ∧
      u * (restrictedSplitEquiv e).symm (PowerSeries.polynomialToRestricted (c none) ω) = g := by
  obtain ⟨u, ω, hu, hω, hn, huω⟩ :=
    hg.exists_isNormMulUnit_isMonicOfDegree_mul_eq (restrictedSplitEquiv e g).2
  refine ⟨(restrictedSplitEquiv e).symm u, ω, ?_, hω, ?_, ?_⟩
  · exact (MulEquiv.isNormMulUnit_iff (restrictedSplitEquiv e).toMulEquiv
      (norm_restrictedSplitEquiv e) _).mp (by simpa using hu)
  · rw [← norm_restrictedSplitEquiv e, AlgEquiv.apply_symm_apply,
      PowerSeries.norm_eq_gaussNorm, PowerSeries.coe_polynomialToRestricted]
    exact hn
  · apply (restrictedSplitEquiv e).injective
    apply Subtype.ext
    simpa only [map_mul, AlgEquiv.apply_symm_apply, Subring.coe_mul,
      PowerSeries.coe_polynomialToRestricted] using huω

end TauCeti.MvPowerSeries
