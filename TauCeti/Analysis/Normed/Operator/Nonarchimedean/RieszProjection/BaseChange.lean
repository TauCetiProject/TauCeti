/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Eigenvalues

/-!
# Algebraic multiplicities under bounded field extension

Coefficientwise extension of a row-compact operator preserves the dimensions of its
stabilized generalized eigenspaces. A good Fredholm zero has the same order after extension,
and the Riesz dimension formula identifies this order with the dimension over either field.
The stabilization bound can be chosen simultaneously before and after extension.

Nonzero eigenvalues in the original field are preserved and reflected. These results concern
bounded unital field homomorphisms; they require neither discrete valuations nor spherical
completeness. They assert no comparison of the spectrum at zero, and no identification of an
infinite-dimensional completed tensor product.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7, Proposition 12.
-/

public section

open scoped ZeroAtInfty NNReal

namespace ContinuousLinearMap

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- Bounded field extension preserves the dimension of every generalized eigenspace whose
exponent is at least the order of the corresponding good Fredholm zero. The dimensions are
computed over their respective coefficient fields. Order zero is included. -/
theorem IsRowCompact.finrank_ker_pow_mapCoeffs (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
    {a : K} {h n : ℕ} (ha : u.matrixCoeff.charPowerSeries.IsGoodZero a h) (hn : h ≤ n) :
    Module.finrank L (LinearMap.ker
      (((1 - f a • u.mapCoeffs f hf) ^ n : C₀(I, L) →L[L] C₀(I, L)) :
        Module.End L C₀(I, L))) =
    Module.finrank K (LinearMap.ker
      (((1 - a • u) ^ n : C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) := by
  have hE := hu.isRieszProjection_rieszProjection
    (fun _ ↦ ha.evalAt_hasseDeriv_eq_zero) ha.isUnit_evalAt_hasseDeriv
  rw [(hE.mapCoeffs f hf).finrank_ker_pow (hu.mapCoeffs f hf)
    (hu.isGoodZero_charPowerSeries_mapCoeffs f hf ha) hn,
    hE.finrank_ker_pow hu ha hn]

/-- At every scalar there is a common stabilization bound before and after bounded field
extension. Beyond that bound the generalized eigenspaces have equal dimensions. In particular,
no choice of multiplicity or splitting over the larger field is needed. -/
theorem IsRowCompact.exists_finrank_ker_pow_mapCoeffs (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) (a : K) :
    ∃ h, u.matrixCoeff.charPowerSeries.IsGoodZero a h ∧ ∀ n, h ≤ n →
      Module.finrank L (LinearMap.ker
        (((1 - f a • u.mapCoeffs f hf) ^ n : C₀(I, L) →L[L] C₀(I, L)) :
          Module.End L C₀(I, L))) =
      Module.finrank K (LinearMap.ker
        (((1 - a • u) ^ n : C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) := by
  obtain ⟨h, ha, -⟩ := hu.exists_isGoodZero_finrank_ker_pow a
  exact ⟨h, ha, fun _ hn ↦ hu.finrank_ker_pow_mapCoeffs f hf ha hn⟩

/-- A nonzero scalar of the original field is an eigenvalue after bounded field extension
exactly when it was an eigenvalue before extension. This does not address the eigenvalue zero.
-/
@[simp]
theorem IsRowCompact.hasEigenvalue_mapCoeffs_iff (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) {μ : K} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue
      (u.mapCoeffs f hf : Module.End L C₀(I, L)) (f μ) ↔
    Module.End.HasEigenvalue (u : Module.End K C₀(I, K)) μ := by
  have hμ' : f μ ≠ 0 := (map_ne_zero f).2 hμ
  have hK := hu.evalAt_charPowerSeries_eq_zero_iff_hasEigenvalue (a := μ⁻¹)
  have hL := (hu.mapCoeffs f hf).evalAt_charPowerSeries_eq_zero_iff_hasEigenvalue
    (a := f (μ⁻¹))
  rw [hu.evalAt_charPowerSeries_mapCoeffs f hf] at hL
  simp only [map_inv₀, ne_eq, inv_eq_zero, hμ, hμ', not_false_eq_true, inv_inv,
    true_and, map_eq_zero] at hK hL
  exact hL.symm.trans hK

end ContinuousLinearMap
