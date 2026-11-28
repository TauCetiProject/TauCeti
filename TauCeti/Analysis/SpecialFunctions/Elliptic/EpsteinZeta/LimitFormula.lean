/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.EpsteinZeta.Basic
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
public import TauCeti.NumberTheory.ModularForms.DedekindEta.LimitFormula
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Covolume
import TauCeti.NumberTheory.ModularForms.DedekindEta.LogPeriod.Lattice

/-!
# Kronecker's first limit formula for a lattice

For a lattice `Λ ⊂ ℂ` of area `A = covolume Λ`, the real Epstein zeta function

`E(Λ, s) = ∑_{0 ≠ l ∈ Λ} (A / |l|²) ^ s`

converges for `s > 1` (`PeriodPair.hasSum_epsteinZeta`). Kronecker's first limit formula gives
its expansion at the pole in terms of the area and of the discriminant `Δ(Λ) = g₂³ - 27 g₃²` of
the Weierstrass invariants of `Λ`:

`E(Λ, s) = π / (s - 1) + π (2 γ - log (A / π²) - log |Δ(Λ)| / 6) + o(1)` as `s → 1⁺`,

with `γ` Euler's constant. Both `E(Λ, s)` and the constant term only depend on the homothety class
of `Λ`. Through Kronecker's formula for `ℤ τ + ℤ` (`UpperHalfPlane.tendsto_epsteinZeta_sub`) this
expresses the logarithmic period `log (4 π Im τ |η(τ)|⁴)` through the area and the discriminant,
which is the form in which the constant term enters the Chowla–Selberg formula.

## Main results

* `UpperHalfPlane.epsteinZeta_periodPair`: for `Λ = ℤ τ + ℤ`, `E(Λ, s)` is
  `UpperHalfPlane.epsteinZeta τ`.
* `PeriodPair.tendsto_epsteinZeta_sub`: **Kronecker's first limit formula** for a lattice.
* `PeriodPair.tendsto_sub_one_mul_epsteinZeta`: the residue `π` at `s = 1`.
* `PeriodPair.hasDerivWithinAt_update_sub_one_mul_rpow_mul_epsteinZeta`: the same formula as a
  one-sided expansion: for `k > 0`, the function equal to
  `(s - 1) ∑_{0 ≠ l ∈ Λ} (|l|² / (k A)) ^ (-s) = (s - 1) k ^ s E(Λ, s)` for `s ≠ 1` and to `π k` at
  `s = 1` has right derivative `π k (2 γ - log (A / (k π²)) - log |Δ(Λ)| / 6)` at `1`.

## References

The lattice form of the formula, with the area and the discriminant, follows `New.kronecker_limit`
in the file `src/Lib/CM/KroneckerLimit.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC). Here it is
deduced from the form for `ℤ τ + ℤ` with the Dedekind eta function, through the expression
`UpperHalfPlane.logPeriod_eq_of_lattice_eq` of the logarithmic period by the area and the
discriminant.

* C. L. Siegel, *Lectures on Advanced Analytic Number Theory*, Tata Institute (1961),
  Chapter I, Theorem 1.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Real UpperHalfPlane

namespace UpperHalfPlane

/-- For the lattice `ℤ τ + ℤ`, the real Epstein zeta function of the period pair `(τ, 1)` is
`UpperHalfPlane.epsteinZeta τ`. -/
@[simp]
theorem epsteinZeta_periodPair (τ : ℍ) : τ.periodPair.epsteinZeta = epsteinZeta τ := by
  ext s
  rw [PeriodPair.epsteinZeta_def, epsteinZeta_def, covolume_lattice_periodPair,
    ← τ.periodPair.latticeEquivProd.symm.toEquiv.tsum_eq]
  congr 1 with p
  rw [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply, periodPair_ω₁, periodPair_ω₂,
    mul_one]

end UpperHalfPlane

namespace PeriodPair

variable (L : PeriodPair)

/-- **Kronecker's first limit formula** for a lattice `Λ` of area `A` and discriminant
`Δ = g₂³ - 27 g₃²`: as `s` decreases to `1`,

`E(Λ, s) = π / (s - 1) + π (2 γ - log (A / π²) - log |Δ| / 6) + o(1)`,

where `γ` is Euler's constant. -/
theorem tendsto_epsteinZeta_sub :
    Tendsto (fun s : ℝ ↦ L.epsteinZeta s - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (π * (2 * Real.eulerMascheroniConstant - Real.log (ZLattice.covolume L.lattice / π ^ 2) -
        Real.log ‖L.weierstrassCurve.Δ‖ / 6))) := by
  obtain ⟨c, τ, h⟩ := L.exists_lattice_eq_smul_periodPair
  have hA := ZLattice.covolume_pos L.lattice
  rw [epsteinZeta_eq_of_lattice_eq h, epsteinZeta_smul, UpperHalfPlane.epsteinZeta_periodPair]
  convert UpperHalfPlane.tendsto_epsteinZeta_sub τ using 3
  rw [UpperHalfPlane.logPeriod_eq_of_lattice_eq h, Real.log_div hA.ne' Real.pi_pos.ne',
    Real.log_div hA.ne' (by positivity), Real.log_pow]
  push_cast
  ring

/-- The residue of the real Epstein zeta function of a lattice at `s = 1` is `π`. -/
theorem tendsto_sub_one_mul_epsteinZeta :
    Tendsto (fun s : ℝ ↦ (s - 1) * L.epsteinZeta s) (𝓝[>] 1) (𝓝 π) := by
  obtain ⟨c, τ, h⟩ := L.exists_lattice_eq_smul_periodPair
  rw [epsteinZeta_eq_of_lattice_eq h, epsteinZeta_smul, UpperHalfPlane.epsteinZeta_periodPair]
  exact UpperHalfPlane.tendsto_sub_one_mul_epsteinZeta τ

/-- **Kronecker's first limit formula as a one-sided expansion.** Let `Λ` be a lattice of area `A`
and discriminant `Δ = g₂³ - 27 g₃²`, and let `k > 0`. The function `F` equal to
`(s - 1) k ^ s E(Λ, s) = (s - 1) ∑_{0 ≠ l ∈ Λ} (|l|² / (k A)) ^ (-s)` for `s ≠ 1` and to `π k` at
`s = 1` has right derivative `π k (2 γ - log (A / (k π²)) - log |Δ| / 6)` at `s = 1`; that is,
`F(s) = π k + π k (2 γ - log (A / (k π²)) - log |Δ| / 6) (s - 1) + o(s - 1)` as `s → 1⁺`. -/
theorem hasDerivWithinAt_update_sub_one_mul_rpow_mul_epsteinZeta {k : ℝ} (hk : 0 < k) :
    HasDerivWithinAt
      (Function.update (fun s : ℝ ↦ (s - 1) * (k ^ s * L.epsteinZeta s)) 1 (π * k))
      (π * k * (2 * Real.eulerMascheroniConstant -
        Real.log (ZLattice.covolume L.lattice / (k * π ^ 2)) -
        Real.log ‖L.weierstrassCurve.Δ‖ / 6)) (Ici 1) 1 := by
  have hA := ZLattice.covolume_pos L.lattice
  -- The slope is `k ^ s (E(Λ, s) - π / (s - 1)) + π (k ^ s - k) / (s - 1)`.
  have hpow : HasDerivAt (fun s : ℝ ↦ k ^ s) (Real.log k * 1 * k ^ (1 : ℝ)) 1 :=
    (hasDerivAt_id 1).const_rpow hk
  have h_slope : Tendsto (fun s : ℝ ↦ (k ^ s - k) / (s - 1)) (𝓝[>] 1)
      (𝓝 (Real.log k * 1 * k ^ (1 : ℝ))) := by
    refine (hpow.tendsto_slope.mono_left (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)).congr
      fun s ↦ ?_
    rw [slope_def_field, Real.rpow_one]
  have h_pow : Tendsto (fun s : ℝ ↦ k ^ s) (𝓝[>] 1) (𝓝 (k ^ (1 : ℝ))) :=
    ((Real.continuous_const_rpow hk.ne').tendsto 1).mono_left nhdsWithin_le_nhds
  have h_lim := (h_pow.mul L.tendsto_epsteinZeta_sub).add (h_slope.const_mul π)
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  refine (h_lim.congr' ?_).trans_eq ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs.ne'
    rw [slope_def_field, Function.update_of_ne hs.ne', Function.update_self]
    field_simp
    ring
  · rw [Real.rpow_one, Real.log_div hA.ne' (by positivity : π ^ 2 ≠ 0),
      Real.log_div hA.ne' (by positivity : k * π ^ 2 ≠ 0), Real.log_mul hk.ne' (by positivity)]
    congr 1
    ring

end PeriodPair
