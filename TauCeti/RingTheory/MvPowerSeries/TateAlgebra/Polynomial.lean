/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Polynomial approximation of restricted power series

Let `R` be an ultrametric normed commutative ring and `c : σ → ℝ` positive polyradii. A
restricted series `f = ∑ₜ aₜ Xᵗ ∈ R{X/c}` is the limit, for the Gauss norm, of its truncations
`∑_{t ∈ s} aₜ Xᵗ` to finite sets `s` of exponents, ordered by inclusion. Outside `s` every
weighted coefficient norm `‖aₜ‖ cᵗ` is small once `s` contains the finitely many exponents where
it is large, and the Gauss norm of `f` minus its truncation is bounded by the weighted norms
outside `s`. When there are finitely many variables, truncation at total degree `n` suffices.
No completeness of `R` is needed.

Consequently the polynomials are dense in `R{X/c}`. Restricting the Gauss norm of `R{X/c}` gives
the Gauss norm on polynomials, with uniform structure
`TauCeti.MvPowerSeries.polynomialGaussUniformSpace`. Over a complete coefficient ring, `R{X/c}` is
the completion of the polynomial algebra for this norm
(`TauCeti.MvPowerSeries.polynomialCompletionPkg`), so every map from the polynomials to a complete
Hausdorff uniform space that is uniformly continuous for the Gauss norm has a unique uniformly
continuous extension to `R{X/c}`. The completion map is the
inclusion `TauCeti.MvPowerSeries.polynomialToRestricted`, which sends constants and variables to
constants and variables, and commutes with bounded coefficient maps by
`MvPowerSeries.restrictedMap_polynomialToRestricted`.

## Main definitions

* `TauCeti.MvPowerSeries.polynomialGaussUniformSpace`: the uniform structure of the Gauss norm on
  `MvPolynomial σ R`.
* `TauCeti.MvPowerSeries.polynomialCompletionPkg`: over a complete `R`, the restricted series
  `R{X/c}` as an abstract completion of the polynomials with their Gauss norm.

## Main results

* `TauCeti.MvPowerSeries.norm_sub_truncFinset_le`: the Gauss norm of `f` minus its truncation to
  `s` is bounded by every bound on the weighted coefficient norms outside `s`.
* `TauCeti.MvPowerSeries.tendsto_truncFinset_atTop`: finite-support truncations converge in the
  Gauss norm.
* `TauCeti.MvPowerSeries.tendsto_truncTotal_atTop`: in finitely many variables, total-degree
  truncations converge in the Gauss norm.
* `TauCeti.MvPowerSeries.denseRange_polynomialToRestricted`: the polynomials are dense.
* `TauCeti.MvPowerSeries.hasBasis_polynomialGaussUniformSpace`: the entourages of the Gauss
  uniform structure on polynomials are given by the Gauss norm of differences.

Dense coefficient subsets give dense polynomials with coefficients in them by
`MvPowerSeries.dense_closure_monomial`, and injectivity of the polynomial embedding is Mathlib's
`MvPolynomial.toRestricted_injective`.

The packaging as an `AbstractCompletion` follows Mathlib's `LaurentSeries.LaurentSeriesPkg` in
`Mathlib/RingTheory/LaurentSeries.lean`, as does `TauCeti.NovikovSeries.completionPkg`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology Uniformity

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- The truncation of a restricted series to a finite set `s` of exponents approximates it within
any bound on its weighted coefficient norms `‖aₜ‖ cᵗ` outside `s`. -/
theorem norm_sub_truncFinset_le (f : IsRestricted.subring (R := R) c) (s : Finset (σ →₀ ℕ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ t ∉ s, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε) :
    ‖f - polynomialToRestricted c (truncFinset R s (f : MvPowerSeries σ R))‖ ≤ ε := by
  refine (norm_le_iff hε).mpr fun t ↦ ?_
  by_cases ht : t ∈ s
  · simp [coeff_truncFinset_of_mem _ ht, hε]
  · simpa [coeff_truncFinset_eq_zero _ ht] using h t ht

/-- **Finite-support truncations converge**: as the finite set `s` of exponents grows, the
truncations `∑_{t ∈ s} aₜ Xᵗ` of a restricted series tend to it in the Gauss norm. -/
theorem tendsto_truncFinset_atTop (f : IsRestricted.subring (R := R) c) :
    Tendsto (fun s : Finset (σ →₀ ℕ) ↦
      polynomialToRestricted c (truncFinset R s (f : MvPowerSeries σ R))) atTop (𝓝 f) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  -- only finitely many weighted coefficient norms are at least `ε / 2`
  have hF : {t | ε / 2 ≤ ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)}.Finite := by
    simpa [Filter.eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds (half_pos hε))
  refine (eventually_ge_atTop hF.toFinset).mono fun s hs ↦ ?_
  rw [dist_comm, dist_eq_norm]
  refine (norm_sub_truncFinset_le f s (half_pos hε).le fun t ht ↦ ?_).trans_lt (half_lt_self hε)
  exact (not_le.mp fun h ↦ ht (hs (hF.mem_toFinset.mpr h))).le

/-- **Total-degree truncations converge**: in finitely many variables, the truncations of a
restricted series below total degree `n` tend to it in the Gauss norm as `n → ∞`. -/
theorem tendsto_truncTotal_atTop [Finite σ] (f : IsRestricted.subring (R := R) c) :
    Tendsto (fun n : ℕ ↦ polynomialToRestricted c (truncTotal n (f : MvPowerSeries σ R)))
      atTop (𝓝 f) := by
  refine (tendsto_truncFinset_atTop f).comp
    (tendsto_atTop_finset_of_monotone (fun m n hmn t ht ↦ ?_) fun t ↦ ⟨t.degree + 1, ?_⟩)
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
    exact ht.trans_le hmn
  · simp

/-- **The polynomials are dense** in the restricted series for the Gauss norm. -/
theorem denseRange_polynomialToRestricted : DenseRange (polynomialToRestricted (R := R) c) :=
  fun f ↦ mem_closure_of_tendsto (tendsto_truncFinset_atTop f)
    (Eventually.of_forall fun _ ↦ Set.mem_range_self _)

variable (c) in
/-- The uniform structure of the Gauss norm at the polyradii `c` on polynomials: the structure
induced by their inclusion into the restricted series. Its entourages are described by
`TauCeti.MvPowerSeries.hasBasis_polynomialGaussUniformSpace`. It is not an instance, since the
Gauss norm depends on `c`. -/
@[instance_reducible]
noncomputable def polynomialGaussUniformSpace : UniformSpace (MvPolynomial σ R) :=
  UniformSpace.comap (polynomialToRestricted c) inferInstance

/-- The entourages of the Gauss uniform structure on polynomials are the sets of pairs whose
difference has Gauss norm less than some `ε > 0`. -/
theorem hasBasis_polynomialGaussUniformSpace :
    (@uniformity (MvPolynomial σ R) (polynomialGaussUniformSpace c)).HasBasis (fun ε : ℝ ↦ 0 < ε)
      fun ε ↦ {p | gaussNorm norm c
        ((p.1 : MvPowerSeries σ R) - (p.2 : MvPowerSeries σ R)) < ε} := by
  refine (Metric.uniformity_basis_dist.comap _).to_hasBasis (fun ε hε ↦ ⟨ε, hε, fun p hp ↦ ?_⟩)
    fun ε hε ↦ ⟨ε, hε, fun p hp ↦ ?_⟩ <;>
  simpa [dist_eq_norm, norm_eq_gaussNorm, ← map_sub] using hp

/-- The polynomials carry the uniform structure induced by their inclusion into the restricted
series. -/
theorem isUniformInducing_polynomialToRestricted :
    @IsUniformInducing _ _ (polynomialGaussUniformSpace c) _ (polynomialToRestricted (R := R) c) :=
  @IsUniformInducing.mk _ _ (polynomialGaussUniformSpace c) _ _ rfl

variable (σ R c) in
/-- **The restricted series are the completion of the polynomials for the Gauss norm**: over a
complete coefficient ring, `R{X/c}` is complete and separated, and the polynomial inclusion
`TauCeti.MvPowerSeries.polynomialToRestricted` is uniform inducing with dense range. -/
-- The body is exposed so that the completion space unfolds to `R{X/c}` for consumers of the
-- `AbstractCompletion` API, such as `AbstractCompletion.compareEquiv`.
@[expose]
noncomputable def polynomialCompletionPkg [CompleteSpace R] :
    @AbstractCompletion (MvPolynomial σ R) (polynomialGaussUniformSpace c) :=
  @AbstractCompletion.mk _ (polynomialGaussUniformSpace c) (IsRestricted.subring (R := R) c)
    (polynomialToRestricted c) inferInstance inferInstance inferInstance
    isUniformInducing_polynomialToRestricted denseRange_polynomialToRestricted

/-- The completion map of `TauCeti.MvPowerSeries.polynomialCompletionPkg` is the polynomial
inclusion. -/
@[simp]
theorem polynomialCompletionPkg_coe [CompleteSpace R] :
    @AbstractCompletion.coe _ (polynomialGaussUniformSpace c) (polynomialCompletionPkg σ R c) =
      ⇑(polynomialToRestricted (R := R) c) :=
  rfl

end TauCeti.MvPowerSeries
