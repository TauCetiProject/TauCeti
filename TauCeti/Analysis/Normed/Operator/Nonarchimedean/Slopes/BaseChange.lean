/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Slopes

/-!
# Fredholm slopes and eigenvalues in a complete splitting extension

Let `K` be a complete ultrametric nontrivially normed field with a real additive valuation `v`,
and `u` a row-compact endomorphism of the model space `C₀(I, K)`. Over a field that is not
algebraically closed the slopes of the Fredholm series `H_u(T) = det (1 - T u)` need not be the
valuations of eigenvalues of `u`: over `ℚ_p` the series `1 - p T ^ 2` has the slope `1 / 2` twice,
while its eigenvalues `±√p` lie only in a quadratic extension. They are the valuations of the
eigenvalues of the extension of `u` to a complete algebraically closed field.

Let `f : K →+* L` be a bounded homomorphism into a complete algebraically closed ultrametric
field `L`, whose real additive valuation `w` recovers the norm, `‖y‖ = b ^ (-w y)` for `y ≠ 0`
and some base `b > 1`, and restricts to `v` along `f`. Write `u_L = u.mapCoeffs f hf` for the
coefficientwise extension of `u` to `C₀(I, L)`. All declarations below are in the
`ContinuousLinearMap` namespace. The Fredholm series of `u_L` is the image of `H_u` under
`f`, so it has the same Newton polygon (`IsRowCompact.newtonPolygon_charPowerSeries_mapCoeffs`).
Hence:

* the multiplicity of the slope `σ` of `H_u` is the sum of the algebraic multiplicities
  `dim (maxGenEigenspace u_L μ)` over the eigenvalues `μ ∈ L` of valuation `σ`
  (`IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs`);
* the number of finite unit edges of slope at most `c` is the sum of the algebraic
  multiplicities over the eigenvalues of valuation at most `c`
  (`IsRowCompact.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_mapCoeffs`);
* every finite slope of `H_u` is the valuation of an eigenvalue of `u_L`
  (`IsRowCompact.exists_hasEigenvalue_mapCoeffs_of_newtonSlopeMultiplicity_ne_zero`);
* these eigenvalue counts do not depend on the complete splitting extension
  (`IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq`).

The homomorphism `f` need only be bounded, not isometric, and neither field is assumed to be
discretely valued or spherically complete.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open TauCeti
open scoped ZeroAtInfty NNReal

namespace ContinuousLinearMap

/-- Bounded coefficient extension along a homomorphism compatible with the valuations does not
change the Fredholm polygon of a row-compact endomorphism. -/
theorem IsRowCompact.newtonPolygon_charPowerSeries_mapCoeffs {I R S : Type*}
    [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
    [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]
    [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
    (v : AddValuation R (WithTop ℝ)) (w : AddValuation S (WithTop ℝ))
    (hfw : ∀ x, w (f x) = v x) :
    (u.mapCoeffs f hf).matrixCoeff.charPowerSeries.newtonPolygon w =
      u.matrixCoeff.charPowerSeries.newtonPolygon v := by
  rw [hu.charPowerSeries_map f hf, PowerSeries.newtonPolygon_map _ v f hfw]

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {u : C₀(I, K) →L[K] C₀(I, K)} (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
  (v : AddValuation K (WithTop ℝ)) (w : AddValuation L (WithTop ℝ)) (hfw : ∀ x, w (f x) = v x)
  {b : ℝ} (hb : 1 < b) (hw : ∀ y ≠ 0, ‖y‖ = b ^ (-(w y).untop₀))

include hfw hb hw

/-- **Slopes are the valuations of the eigenvalues in a splitting extension.** The multiplicity
of the slope `σ` in the Fredholm polygon of a row-compact endomorphism `u` of `C₀(I, K)` is the
sum of the algebraic multiplicities `dim (maxGenEigenspace u_L μ)` over the eigenvalues `μ` of
valuation `σ` of its extension `u_L` to a complete algebraically closed field `L`. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs
    [IsAlgClosed L] (hu : u.IsRowCompact) (σ : ℝ) :
    u.matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : L | w μ = σ}, Module.finrank L (Module.End.maxGenEigenspace
        ((u.mapCoeffs f hf : C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L)) μ) := by
  have huL := hu.mapCoeffs f hf
  have huL' := isPrCompact_iff_isRowCompact.2 huL
  rw [← PowerSeries.newtonSlopeMultiplicity_map _ v f hfw, ← hu.charPowerSeries_map f hf,
    ← huL.charPowerSeries_eq_charPowerSeries_matrixCoeff]
  exact huL'.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank w hb hw σ

/-- **Cutoff counts in a splitting extension.** The number of finite unit edges of slope at most
`c` of the Fredholm polygon of a row-compact endomorphism `u` of `C₀(I, K)` is the sum of the
algebraic multiplicities over the eigenvalues of valuation at most `c` of its extension `u_L` to a
complete algebraically closed field `L`. -/
theorem IsRowCompact.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le_mapCoeffs
    [IsAlgClosed L] (hu : u.IsRowCompact) (c : ℝ) :
    {n | n ∈ finiteEdges (u.matrixCoeff.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.matrixCoeff.charPowerSeries.newtonPolygon v) n ≤ c}.ncard =
      ∑ᶠ μ ∈ {μ : L | w μ ≤ c}, Module.finrank L (Module.End.maxGenEigenspace
        ((u.mapCoeffs f hf : C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L)) μ) := by
  have huL := hu.mapCoeffs f hf
  have huL' := isPrCompact_iff_isRowCompact.2 huL
  rw [← hu.newtonPolygon_charPowerSeries_mapCoeffs f hf v w hfw,
    ← huL.charPowerSeries_eq_charPowerSeries_matrixCoeff]
  exact huL'.ncard_setOf_unitSlope_newtonPolygon_charPowerSeries_le w hb hw c

/-- **Eigenvalues at every slope.** Every finite slope `σ` of the Fredholm polygon of a
row-compact endomorphism `u` of `C₀(I, K)` is the valuation of an eigenvalue of its extension
`u_L` to a complete algebraically closed field `L`. -/
theorem IsRowCompact.exists_hasEigenvalue_mapCoeffs_of_newtonSlopeMultiplicity_ne_zero
    [IsAlgClosed L] (hu : u.IsRowCompact) {σ : ℝ}
    (hσ : u.matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0) :
    ∃ μ : L, w μ = σ ∧ Module.End.HasEigenvalue
      ((u.mapCoeffs f hf : C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L)) μ := by
  have huL := hu.mapCoeffs f hf
  have huL' := isPrCompact_iff_isRowCompact.2 huL
  rw [← PowerSeries.newtonSlopeMultiplicity_map _ v f hfw, ← hu.charPowerSeries_map f hf,
    ← huL.charPowerSeries_eq_charPowerSeries_matrixCoeff] at hσ
  exact huL'.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero w hb hw hσ

/-- **Independence of the splitting extension.** For a row-compact endomorphism `u` of
`C₀(I, K)` and two complete algebraically closed fields `L`, `L'` receiving `K`, the sums of the
algebraic multiplicities of the eigenvalues of valuation `σ` of the extensions of `u` to `L` and
to `L'` agree: both are the multiplicity of the slope `σ` of the Fredholm series of `u`. -/
theorem IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq [IsAlgClosed L]
    {L' : Type*} [NontriviallyNormedField L'] [CompleteSpace L'] [IsUltrametricDist L']
    [IsAlgClosed L'] (hu : u.IsRowCompact) (f' : K →+* L')
    (hf' : ∃ C : ℝ≥0, ∀ x, ‖f' x‖ ≤ C * ‖x‖) (w' : AddValuation L' (WithTop ℝ))
    (hfw' : ∀ x, w' (f' x) = v x) {b' : ℝ} (hb' : 1 < b')
    (hw' : ∀ y ≠ 0, ‖y‖ = b' ^ (-(w' y).untop₀)) (σ : ℝ) :
    ∑ᶠ μ ∈ {μ : L | w μ = σ}, Module.finrank L (Module.End.maxGenEigenspace
        ((u.mapCoeffs f hf : C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L)) μ) =
      ∑ᶠ μ ∈ {μ : L' | w' μ = σ}, Module.finrank L' (Module.End.maxGenEigenspace
        ((u.mapCoeffs f' hf' : C₀(I, L') →L[L'] C₀(I, L')) : Module.End L' C₀(I, L')) μ) := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs f hf v w hfw hb hw,
    hu.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs f' hf' v w' hfw' hb' hw']

end ContinuousLinearMap
