/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FredholmDet
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann

/-!
# Invertibility and the nonzero spectrum of a row-compact operator

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete
index type, and `u` a row-compact endomorphism of the model space `C₀(I, R)` with Fredholm
series `H_u(T) = det (1 - T u)`, the principal-minor series `u.matrixCoeff.charPowerSeries`.
The Fredholm series detects exactly which operators `1 - a • u` are invertible in the algebra
of continuous endomorphisms:

`IsUnit (1 - a • u) ↔ IsUnit (H_u(a))`
(`ContinuousLinearMap.IsRowCompact.isUnit_one_sub_smul_iff`).

The resolvent `V(a)` supplies the inverse when `H_u(a)` is a unit, and multiplicativity of the
Fredholm determinant gives the converse. In terms of the spectrum of `u` over `R`, the inverse
`r⁻¹` of a unit `r` lies in the spectrum exactly when `H_u(r)` is not a unit
(`ContinuousLinearMap.IsRowCompact.inv_mem_spectrum_iff`). Over coefficient rings with
nilpotents this is a condition on units, not on vanishing.

Over a complete nontrivially normed ultrametric field `K` it becomes Serre's description of the
nonzero spectrum: for `μ ≠ 0`,

`μ ∈ spectrum K u ↔ H_u(μ⁻¹) = 0`
(`ContinuousLinearMap.IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero`).

Since `H_u(0) = 1`, every zero `a` of `H_u` is nonzero, and the zeros of `H_u` are exactly the
inverses of the nonzero spectral values
(`ContinuousLinearMap.IsRowCompact.evalAt_charPowerSeries_eq_zero_iff`). Nothing is asserted
about `0 ∈ spectrum K u`, which the Fredholm series does not see.

Strassmann's theorem then bounds the spectrum away from zero. If `H_u` is distinguished of degree
`s` at the radius `ε⁻¹`, that is, `s` is the largest index at which `‖cₙ‖ ε⁻ⁿ` attains its
maximum, then at most `s` spectral values have norm at least `ε`
(`ContinuousLinearMap.IsRowCompact.encard_setOf_mem_spectrum_le`). Such an `s` exists for every
`ε > 0`, since `H_u` is entire and nonzero, so only finitely many spectral values have norm
bounded below by a positive number, and every nonzero spectral value is isolated in the spectrum.
Zero may be an accumulation point of the spectrum. The same bound, finiteness and isolation hold
for the extension of `u` to `C₀(I, L)` along any complete normed field extension `L` of `K`, such
as a complete field over which `H_u` splits: the spectrum of the extension is controlled by the
zeros of `H_u` in `L`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isUnit_one_sub_smul_iff`: `1 - a • u` is invertible if and
  only if `H_u(a)` is a unit.
* `ContinuousLinearMap.IsRowCompact.isUnit_one_sub_iff`: `1 - u` is invertible if and only if
  the Fredholm determinant `det (1 - u)` is a unit.
* `ContinuousLinearMap.IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero`: over a field, a
  nonzero `μ` lies in the spectrum of `u` if and only if `H_u(μ⁻¹) = 0`.
* `ContinuousLinearMap.IsRowCompact.encard_setOf_mem_spectrum_mapCoeffs_le` and
  `ContinuousLinearMap.IsRowCompact.finite_setOf_mem_spectrum_mapCoeffs`: after extension to a
  complete normed field `L`, at most `s` spectral values, and in any case finitely many, have norm
  at least `ε`, where `H_u` is distinguished of degree `s` at `ε⁻¹`.
* `ContinuousLinearMap.IsRowCompact.encard_setOf_mem_spectrum_le` and
  `ContinuousLinearMap.IsRowCompact.finite_setOf_mem_spectrum`: the same over `K` itself.
* `ContinuousLinearMap.IsRowCompact.eventually_notMem_spectrum_mapCoeffs` and
  `ContinuousLinearMap.IsRowCompact.eventually_notMem_spectrum`: every nonzero spectral value is
  isolated in the spectrum, after extension to `L` and over `K` itself.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Topology
open scoped ZeroAtInfty NNReal

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

section Ring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

/-- **Invertibility and the Fredholm series.** For a row-compact endomorphism `u` of `C₀(I, R)`,
the operator `1 - a • u` is invertible if and only if the value `H_u(a)` of the Fredholm series
`det (1 - T u)` is a unit of `R`. -/
theorem IsRowCompact.isUnit_one_sub_smul_iff {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} :
    IsUnit (1 - a • u) ↔ IsUnit (u.matrixCoeff.charPowerSeries.evalAt a) :=
  ⟨hu.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul, hu.isUnit_one_sub_smul⟩

/-- **Invertibility and the Fredholm determinant.** For a row-compact endomorphism `u` of
`C₀(I, R)`, the operator `1 - u` is invertible if and only if the Fredholm determinant
`det (1 - u)` is a unit of `R`. -/
theorem IsRowCompact.isUnit_one_sub_iff {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) :
    IsUnit (1 - u) ↔ IsUnit u.fredholmDet := by
  simpa [fredholmDet_def] using hu.isUnit_one_sub_smul_iff (a := 1)

/-- **Unit spectral values.** For a row-compact endomorphism `u` of `C₀(I, R)` and a unit `r` of
`R`, the inverse `r⁻¹` lies in the spectrum of `u` if and only if the value `H_u(r)` of the
Fredholm series is not a unit of `R`. -/
theorem IsRowCompact.inv_mem_spectrum_iff {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {r : Rˣ} :
    ((r⁻¹ : Rˣ) : R) ∈ spectrum R u ↔ ¬IsUnit (u.matrixCoeff.charPowerSeries.evalAt (r : R)) := by
  rw [← spectrum.smul_mem_smul_iff (r := r)]
  simp only [Units.smul_def, smul_eq_mul, Units.mul_inv]
  rw [spectrum.mem_iff, map_one, hu.isUnit_one_sub_smul_iff]

end Ring

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The nonzero spectrum of a row-compact operator.** For a row-compact endomorphism `u` of
`C₀(I, K)` over a complete ultrametric field and `μ ≠ 0`, `μ` lies in the spectrum of `u` if and
only if `μ⁻¹` is a zero of the Fredholm series `det (1 - T u)`. -/
theorem IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {μ : K} (hμ : μ ≠ 0) :
    μ ∈ spectrum K u ↔ u.matrixCoeff.charPowerSeries.evalAt μ⁻¹ = 0 := by
  simpa [Units.val_inv_eq_inv_val] using
    hu.inv_mem_spectrum_iff (r := Units.mk0 μ⁻¹ (inv_ne_zero hμ))

/-- **The zeros of the Fredholm series.** For a row-compact endomorphism `u` of `C₀(I, K)`, the
zeros of the Fredholm series `det (1 - T u)` are exactly the inverses of the nonzero elements of
the spectrum of `u`. Since `det (1 - 0 u) = 1`, no zero is `0`. -/
theorem IsRowCompact.evalAt_charPowerSeries_eq_zero_iff {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {a : K} :
    u.matrixCoeff.charPowerSeries.evalAt a = 0 ↔ a ≠ 0 ∧ a⁻¹ ∈ spectrum K u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [PowerSeries.evalAt_at_zero, Matrix.constantCoeff_charPowerSeries]
  · rw [hu.mem_spectrum_iff_evalAt_inv_eq_zero (inv_ne_zero ha), inv_inv]
    exact ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

end Field

section Extension

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- **Strassmann's bound for the spectrum.** Let `u` be a row-compact endomorphism of `C₀(I, K)`,
and let its Fredholm series `H_u` be distinguished of degree `s` at the radius `ε⁻¹`. Then the
extension of `u` to `C₀(I, L)`, for a complete normed field extension `L` of `K`, has at most `s`
spectral values of norm at least `ε`. -/
theorem IsRowCompact.encard_setOf_mem_spectrum_mapCoeffs_le (hu : u.IsRowCompact) {ε : ℝ}
    (hε : 0 < ε) {s : ℕ}
    (hs : TauCeti.PowerSeries.IsDistinguished ε⁻¹ s u.matrixCoeff.charPowerSeries) :
    {μ ∈ spectrum L (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩) | ε ≤ ‖μ‖}.encard ≤ s := by
  refine (Set.encard_le_encard_of_injOn (f := (·⁻¹)) ?_ inv_injective.injOn).trans
    (hs.encard_setOf_evalAt_eq_zero_le (L := L) (inv_pos.2 hε)
      (hu.isEntire_charPowerSeries.isRestricted _))
  rintro μ ⟨hμ, hεμ⟩
  have hμ0 : μ ≠ 0 := norm_pos_iff.1 (hε.trans_le hεμ)
  refine ⟨by simpa only [norm_inv] using inv_anti₀ hε hεμ, ?_⟩
  rw [(hu.mapCoeffs _ _).mem_spectrum_iff_evalAt_inv_eq_zero hμ0,
    hu.charPowerSeries_map, PowerSeries.evalAt_map_algebraMap] at hμ
  exact hμ

/-- After extension to a complete normed field `L`, a row-compact endomorphism of `C₀(I, K)` has
only finitely many spectral values of norm at least `ε`, for every `ε > 0`. -/
theorem IsRowCompact.finite_setOf_mem_spectrum_mapCoeffs (hu : u.IsRowCompact) {ε : ℝ}
    (hε : 0 < ε) :
    {μ ∈ spectrum L (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩) | ε ≤ ‖μ‖}.Finite := by
  have hH : u.matrixCoeff.charPowerSeries ≠ 0 := fun h ↦ by
    simpa [h] using Matrix.constantCoeff_charPowerSeries u.matrixCoeff
  obtain ⟨s, hs⟩ := TauCeti.PowerSeries.exists_isDistinguished (inv_pos.2 hε)
    (hu.isEntire_charPowerSeries.isRestricted _) hH
  exact Set.finite_of_encard_le_coe (hu.encard_setOf_mem_spectrum_mapCoeffs_le hε hs)

/-- **Strassmann's bound for the spectrum** over the coefficient field: if the Fredholm series of
a row-compact endomorphism `u` of `C₀(I, K)` is distinguished of degree `s` at the radius `ε⁻¹`,
then `u` has at most `s` spectral values of norm at least `ε`. -/
theorem IsRowCompact.encard_setOf_mem_spectrum_le (hu : u.IsRowCompact) {ε : ℝ} (hε : 0 < ε)
    {s : ℕ} (hs : TauCeti.PowerSeries.IsDistinguished ε⁻¹ s u.matrixCoeff.charPowerSeries) :
    {μ ∈ spectrum K u | ε ≤ ‖μ‖}.encard ≤ s := by
  simpa using hu.encard_setOf_mem_spectrum_mapCoeffs_le (L := K) hε hs

/-- A row-compact endomorphism of `C₀(I, K)` has only finitely many spectral values of norm at
least `ε`, for every `ε > 0`. -/
theorem IsRowCompact.finite_setOf_mem_spectrum (hu : u.IsRowCompact) {ε : ℝ} (hε : 0 < ε) :
    {μ ∈ spectrum K u | ε ≤ ‖μ‖}.Finite := by
  simpa using hu.finite_setOf_mem_spectrum_mapCoeffs (L := K) hε

/-- **Nonzero spectral values are isolated.** For a row-compact endomorphism `u` of `C₀(I, K)`,
a complete normed field extension `L` of `K` and `μ : L` with `μ ≠ 0`, no point of a punctured
neighbourhood of `μ` lies in the spectrum of the extension of `u` to `C₀(I, L)`. -/
theorem IsRowCompact.eventually_notMem_spectrum_mapCoeffs (hu : u.IsRowCompact) {μ : L}
    (hμ : μ ≠ 0) :
    ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum L (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩) := by
  have hμ0 : 0 < ‖μ‖ := norm_pos_iff.2 hμ
  -- Near `μ` every point has norm above `‖μ‖ / 2`, and only finitely many spectral values do;
  -- removing these finitely many points leaves a punctured neighbourhood of `μ`.
  have hnorm : ∀ᶠ ν in 𝓝 μ, ‖μ‖ / 2 < ‖ν‖ :=
    (continuous_norm.tendsto μ).eventually (lt_mem_nhds (half_lt_self hμ0))
  have hF := (hu.finite_setOf_mem_spectrum_mapCoeffs (L := L) (half_pos hμ0)).to_subtype
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite (nhdsWithin_le_nhds hnorm) hF]
    with ν ⟨hν, hνF⟩ hνsp
  exact hνF ⟨hνsp, hν.le⟩

/-- **Nonzero spectral values are isolated** over the coefficient field: for a row-compact
endomorphism `u` of `C₀(I, K)` and `μ ≠ 0`, no point of a punctured neighbourhood of `μ` lies in
the spectrum of `u`. -/
theorem IsRowCompact.eventually_notMem_spectrum (hu : u.IsRowCompact) {μ : K} (hμ : μ ≠ 0) :
    ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum K u := by
  simpa using hu.eventually_notMem_spectrum_mapCoeffs (L := K) hμ

end Extension

end ContinuousLinearMap
