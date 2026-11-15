/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.PrModule
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Splitting
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Zeros
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# Slopes of the Fredholm series of a compact operator

Let `K` be a complete ultrametric nontrivially normed field with a real additive valuation `v`
and a base `b > 1` such that `‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. The Fredholm series
`H_u(T) = det (1 - T u)` of a row-compact endomorphism `u` of a module with property (Pr) is
entire with constant coefficient one. Its Newton polygon therefore has a finite face of every
real slope, so its finite slopes are locally finite: only finitely many
finite unit edges have slope at most any real cutoff
(`ContinuousLinearMap.IsPrCompact.finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le`), and
if there are infinitely many finite edges their slopes tend to infinity
(`ContinuousLinearMap.IsPrCompact.tendsto_unitSlope_newtonPolygon_charPowerSeries`). The
multiplicity of a slope `σ` is `PowerSeries.newtonSlopeMultiplicity`, the number of finite unit
edges of slope `σ`. A slope `σ` corresponds to zeros of `H_u` of valuation `-σ`, and a zero `α`
gives the eigenvalue `α⁻¹` of `u`, so the slopes describe the valuations of the eigenvalues.

The slopes behave as eigenvalue valuations should:

* scaling `u` by a scalar `a` of finite valuation shifts every slope by `v a`, since
  `H_{a u}(T) = H_u(a T)`
  (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul`);
* on a block diagonal operator the multiplicities of the two blocks add, since the Fredholm series
  multiply (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_prodMap`);
* on a finitely generated module the multiplicities are those of the finite slope multiset of
  the polynomial `det (1 - X u)`
  (`ContinuousLinearMap.newtonSlopeMultiplicity_charPowerSeries_of_finite`). Zero eigenvalues
  lower the degree of this polynomial and contribute no finite slope.

The scaling and finite comparisons hold over every complete ultrametric coefficient ring with
Tate scalars, and so does invariance under coefficient extension: extending the matrix
coefficients of a row-compact endomorphism of `C₀(I, R)` along a bounded ring homomorphism
compatible with the valuations preserves every multiplicity
(`ContinuousLinearMap.IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs`).

Over an algebraically closed `K` the slopes are exactly the valuations of the nonzero eigenvalues,
counted with algebraic multiplicity: the multiplicity of `σ` is the sum, over the eigenvalues `μ`
with `v μ = σ`, of the dimensions of the maximal generalised eigenspaces of `u` at `μ`
(`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`).
Thus every finite slope is the valuation of an eigenvalue
(`ContinuousLinearMap.IsPrCompact.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero`).
Summing over the slopes at most a cutoff `c`, the number of slopes at most `c`, counted with
multiplicity, is the total algebraic multiplicity of the eigenvalues of valuation at most `c`
(`IsPrCompact.finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`).
The zeros of `H_u` of norm `b ^ σ`, counted with the orders of the zeros, number the multiplicity
of `σ` (`PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`), and the order of
the zero at `μ⁻¹` is the algebraic multiplicity of `μ`
(`ContinuousLinearMap.IsPrCompact.finrank_maxGenEigenspace_eq_order_taylor`). Over a field that is
not algebraically closed a slope need not be the valuation of an eigenvalue: the Fredholm series
`1 - p T ^ 2` over `ℚ_p` has the slope `1 / 2` twice, while its eigenvalues `±√p` are not in
`ℚ_p`.

On a model space `C₀(I, K)` over any complete ultrametric field `K`, the eigenvalues are found in
a complete algebraically closed normed field extension `L` of `K`, such as `ℂ_p` over `ℚ_p`.
Since extending the coefficients of `u` to `L` does not change the Fredholm polygon, the
multiplicity of the slope `σ` of `u` is the total algebraic multiplicity of the eigenvalues of
valuation `σ` of the extension of `u` to `C₀(I, L)`
(`IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs`),
with the same statement for cutoff counts and for the existence of eigenvalues at every slope.
In particular these totals do not depend on the choice of `L`
(`ContinuousLinearMap.IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq`).

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_isFiniteFace_newtonPolygon_charPowerSeries`: the
  Fredholm polygon has a finite face of every slope.
* `ContinuousLinearMap.IsPrCompact.finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le`,
  `ContinuousLinearMap.IsPrCompact.tendsto_unitSlope_newtonPolygon_charPowerSeries`: local
  finiteness of the slopes.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul`: scaling shifts
  the slopes by the valuation of the scalar.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_prodMap`: block sums
  add multiplicities.
* `ContinuousLinearMap.newtonSlopeMultiplicity_charPowerSeries_of_finite`: comparison with the
  finite slope multiset on a finitely generated module.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`:
  over an algebraically closed field, the multiplicity of a slope is the sum of the algebraic
  multiplicities of the eigenvalues of that valuation.
* `ContinuousLinearMap.IsPrCompact.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero`: over
  an algebraically closed field, every finite slope is the valuation of an eigenvalue.
* `IsPrCompact.finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`:
  over an algebraically closed field, the cutoff count of slopes at most `c` is the total
  algebraic multiplicity of the eigenvalues of valuation at most `c`.
* `ContinuousLinearMap.IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs`:
  coefficient extension preserves the slope multiplicities.
* `IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs`,
  `IsRowCompact.finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs`,
  `IsRowCompact.exists_hasEigenvalue_mapCoeffs_of_newtonSlopeMultiplicity_ne_zero`:
  the comparison with eigenvalues in a complete algebraically closed extension, for individual
  slopes and cutoff counts, and eigenvalues at every slope.
* `ContinuousLinearMap.IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq`: independence
  of the algebraically closed extension.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter TauCeti
open scoped ZeroAtInfty NNReal

universe u w

namespace ContinuousLinearMap

section Ring

variable {R : Type w} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] (v : AddValuation R (WithTop ℝ))

/-- Scaling a row-compact endomorphism by a scalar `a` of finite valuation shifts every slope of
its Fredholm polygon by `v a`, preserving multiplicities. -/
theorem IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul {M : Type u}
    [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {a : R} (ha : v a ≠ ⊤) (σ : ℝ) :
    (a • u).charPowerSeries.newtonSlopeMultiplicity v (σ + (v a).untop₀) =
      u.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [hu.charPowerSeries_smul a, PowerSeries.newtonSlopeMultiplicity_rescale _ ha]

/-- On a finitely generated module with property (Pr), the multiplicity of a slope in the
Fredholm polygon is its multiplicity in the finite slope multiset of the finite projective
determinant `det (1 - X u)`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (σ : ℝ) :
    haveI := hM.projective
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      (((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).count σ := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.newtonSlopeMultiplicity_coe]

/-- **Coefficient extension preserves slopes.** Extending the matrix coefficients of a row-compact
endomorphism of `C₀(I, R)` along a bounded ring homomorphism `f : R →+* S` compatible with the
valuations does not change the slope multiplicities of its Fredholm polygon. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I] {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {w : AddValuation S (WithTop ℝ)}
    (hfw : ∀ x, w (f x) = v x) (σ : ℝ) :
    (u.mapCoeffs f hf).charPowerSeries.newtonSlopeMultiplicity w σ =
      u.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [(hu.mapCoeffs f hf).charPowerSeries_eq_charPowerSeries_matrixCoeff, hu.charPowerSeries_map,
    hu.charPowerSeries_eq_charPowerSeries_matrixCoeff,
    PowerSeries.newtonSlopeMultiplicity_map f hfw]

end Ring

section Field

variable {K : Type w} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {M N : Type u} [SeminormedAddCommGroup M] [Module K M]
  [SeminormedAddCommGroup N] [Module K N] {u : M →L[K] M} {w : N →L[K] N}

namespace IsPrCompact

variable {b : ℝ} (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- The Fredholm polygon of a row-compact endomorphism has a finite face of every real slope. -/
theorem exists_isFiniteFace_newtonPolygon_charPowerSeries (hu : u.IsPrCompact) (σ : ℝ) :
    ∃ l l' : ℕ, IsFiniteFace (u.charPowerSeries.newtonPolygon v) σ l l' :=
  hu.isEntire_charPowerSeries.exists_isFiniteFace_newtonPolygon v hb hv
    u.charPowerSeries_ne_zero σ

/-- **Local finiteness of Fredholm slopes.** Only finitely many finite unit edges of the
Fredholm polygon of a row-compact endomorphism have slope at most a given real number. -/
theorem finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le (hu : u.IsPrCompact) (c : ℝ) :
    {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ c}.Finite :=
  hu.isEntire_charPowerSeries.finite_setOf_unitSlope_newtonPolygon_le v hb hv c

/-- If the Fredholm polygon of a row-compact endomorphism has infinitely many finite unit edges,
their slopes tend to infinity. -/
theorem tendsto_unitSlope_newtonPolygon_charPowerSeries (hu : u.IsPrCompact)
    (hinf : (finiteEdges (u.charPowerSeries.newtonPolygon v)).Infinite) :
    Tendsto (unitSlope (u.charPowerSeries.newtonPolygon v)) atTop atTop :=
  hu.isEntire_charPowerSeries.tendsto_unitSlope_newtonPolygon v hb hv hinf

/-- **Block sums add multiplicities.** The multiplicity of every slope of the Fredholm polygon of
a block diagonal operator is the sum of its multiplicities for the two blocks. -/
theorem newtonSlopeMultiplicity_charPowerSeries_prodMap (hu : u.IsPrCompact)
    (hw : w.IsPrCompact) (σ : ℝ) :
    (u.prodMap w).charPowerSeries.newtonSlopeMultiplicity v σ =
      u.charPowerSeries.newtonSlopeMultiplicity v σ +
        w.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.newtonSlopeMultiplicity_mul v hb hv
    hw.isEntire_charPowerSeries u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero σ

/-- Only finitely many eigenvalues of valuation at most `c` have a nonzero maximal generalised
eigenspace: their inverses are zeros of the Fredholm series in the closed disc of radius `b ^ c`.
-/
private theorem finite_setOf_le_inter_support_finrank [IsBoundedSMul K M] (hu : u.IsPrCompact)
    (c : ℝ) :
    ({μ : K | v μ ≤ c} ∩ Function.support fun μ ↦
      Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ)).Finite := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  refine ((PowerSeries.IsRestricted.finite_setOf_norm_le_and_evalAt_eq_zero (L := K)
    (hu.isEntire_charPowerSeries.isRestricted (b ^ c)) u.charPowerSeries_ne_zero).image
      (·⁻¹)).subset ?_
  rintro μ ⟨hμc, hμ⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμc
  -- The algebraic multiplicity of `μ` is the order of the zero of the Fredholm series at `μ⁻¹`.
  rw [Function.mem_support, ← Nat.cast_ne_zero (R := ℕ∞),
    hu.finrank_maxGenEigenspace_eq_order_taylor hμ0, PowerSeries.order_taylor_ne_zero_iff] at hμ
  refine ⟨μ⁻¹, ⟨?_, hμ⟩, inv_inv μ⟩
  -- `‖μ⁻¹‖ = b ^ (v μ) ≤ b ^ c`.
  have hσ := WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hμ0)
  rw [norm_inv, hv μ hμ0, ← Real.rpow_neg hb0.le, neg_neg]
  exact Real.rpow_le_rpow_of_exponent_le hb.le
    (WithTop.coe_le_coe.mp (hσ.symm ▸ hμc : ((v μ).untop₀ : WithTop ℝ) ≤ c))

/-- **Slopes are the valuations of the eigenvalues, with multiplicity.** Over a complete
algebraically closed ultrametric field, the multiplicity of the slope `σ` in the Fredholm polygon
of a row-compact endomorphism `u` of a module with property (Pr) is the sum of the algebraic
multiplicities `dim (maxGenEigenspace u μ)` over the eigenvalues `μ` of valuation `σ`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : K | v μ = σ},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := by
  have hH := hu.isEntire_charPowerSeries
  have hH0 := u.charPowerSeries_ne_zero
  have hb0 : 0 < b := zero_lt_one.trans hb
  -- An eigenvalue of valuation `σ` is the inverse of a point of norm `b ^ σ`.
  have hmem (μ : K) : v μ = σ ↔ ‖μ⁻¹‖ = b ^ σ := by
    rw [norm_inv, inv_eq_iff_eq_inv, ← Real.rpow_neg hb0.le, v.norm_eq_rpow_iff hb hv, neg_neg]
  have hbij : Set.BijOn (·⁻¹) {μ : K | v μ = σ} (Metric.sphere 0 (b ^ σ)) := by
    refine ⟨fun μ hμ ↦ ?_, inv_injective.injOn, fun x hx ↦ ⟨x⁻¹, ?_, inv_inv x⟩⟩
    · simpa using (hmem μ).mp hμ
    · rw [Set.mem_ofPred_eq, hmem, inv_inv]
      simpa using hx
  -- The algebraic multiplicity of `μ` is the order of the zero of the Fredholm series at `μ⁻¹`.
  have hord {μ : K} (hμ : v μ = σ) :
      (Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ∞) =
        (PowerSeries.taylor μ⁻¹ u.charPowerSeries).order :=
    hu.finrank_maxGenEigenspace_eq_order_taylor fun hμ0 ↦ by simp [hμ0] at hμ
  -- Only the inverses of the finitely many zeros in the closed disc contribute.
  have hfin : ({μ : K | v μ = σ} ∩ Function.support fun μ ↦
      Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ)).Finite :=
    (finite_setOf_le_inter_support_finrank v hb hv hu σ).subset
      (Set.inter_subset_inter_left _ fun μ (hμ : v μ = σ) ↦ hμ.le)
  have key : (u.charPowerSeries.newtonSlopeMultiplicity v σ : ℕ∞) =
      ((∑ᶠ μ ∈ {μ : K | v μ = σ},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) := by
    rw [hH.newtonSlopeMultiplicity_eq_finsum_order_taylor v hb hv hH0 σ,
      ← Nat.coe_castAddMonoidHom, (Nat.castAddMonoidHom ℕ∞).map_finsum_mem' hfin]
    exact (finsum_mem_eq_of_bijOn _ hbij fun μ hμ ↦ hord hμ).symm
  exact_mod_cast key

/-- **Cutoff counts of slopes.** Over a complete algebraically closed ultrametric field, the number
of slopes at most `c` in the Fredholm polygon of a row-compact endomorphism `u` of a module with
property (Pr), counted with multiplicity, is the sum of the algebraic multiplicities
`dim (maxGenEigenspace u μ)` over the eigenvalues `μ` of valuation at most `c`. Both sums are
finite. -/
theorem finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (c : ℝ) :
    ∑ᶠ σ ∈ Set.Iic c, u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : K | v μ ≤ c},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := by
  have hc : {μ : K | v μ ≤ c} = v ⁻¹' (WithTop.some '' Set.Iic c) := by
    rw [WithTop.image_coe_Iic]
    ext μ
    simp
  -- Group the eigenvalues of valuation at most `c` by their valuation.
  calc ∑ᶠ σ ∈ Set.Iic c, u.charPowerSeries.newtonSlopeMultiplicity v σ
      = ∑ᶠ σ ∈ Set.Iic c, ∑ᶠ μ ∈ v ⁻¹' {(σ : WithTop ℝ)},
          Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) :=
        finsum_mem_congr rfl fun σ _ ↦
          newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank v hb hv hu σ
    _ = ∑ᶠ τ ∈ WithTop.some '' Set.Iic c, ∑ᶠ μ ∈ v ⁻¹' {τ},
          Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) :=
        (finsum_mem_image (f := fun τ ↦ ∑ᶠ μ ∈ v ⁻¹' {τ},
          Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ))
          WithTop.coe_injective.injOn).symm
    _ = _ := by
      rw [TauCeti.finsum_mem_fiberwise _ _ _
        (hc ▸ finite_setOf_le_inter_support_finrank v hb hv hu c), hc]

/-- **Eigenvalues at every slope.** Over a complete algebraically closed ultrametric field, every
finite slope `σ` of the Fredholm polygon of a row-compact endomorphism `u` of a module with
property (Pr) is the valuation of an eigenvalue of `u`. -/
theorem exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) {σ : ℝ}
    (hσ : u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0) :
    ∃ μ : K, v μ = σ ∧ Module.End.HasEigenvalue (u : Module.End K M) μ := by
  rw [newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank v hb hv hu] at hσ
  obtain ⟨μ, hμσ, hμ⟩ := exists_ne_zero_of_finsum_mem_ne_zero hσ
  refine ⟨μ, hμσ, ?_⟩
  -- A nonzero maximal generalised eigenspace contains an eigenvector.
  have hgen : Module.End.HasUnifEigenvalue (u : Module.End K M) μ ⊤ := fun hbot ↦
    hμ (by rw [Module.End.maxGenEigenspace, hbot, finrank_bot])
  exact (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).mp hgen

end IsPrCompact

end Field

section Extension

/-! ### Slopes and eigenvalues in an algebraically closed extension

Over a field `K` that is not algebraically closed, the eigenvalues accounting for the slopes of
`u` live in a complete algebraically closed extension `L`, such as `ℂ_p` over `ℚ_p`. Extending the
matrix coefficients of `u` to `L` does not change its Fredholm polygon, so the comparison over `L`
describes the slopes of `u` itself, and the answer does not depend on the choice of `L`. -/

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] (v : AddValuation K (WithTop ℝ)) (vL : AddValuation L (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  (hvL : ∀ y ≠ 0, ‖y‖ = b ^ (-(vL y).untop₀)) {u : C₀(I, K) →L[K] C₀(I, K)}

include hb hv hvL

namespace IsRowCompact

omit [IsAlgClosed L] in
/-- Extending the coefficients of a row-compact endomorphism of `C₀(I, K)` to a normed field
extension `L` preserves the slope multiplicities, for valuations recovering both norms with the
same base. -/
private theorem newtonSlopeMultiplicity_charPowerSeries_mapCoeffs_algebraMap
    (hu : u.IsRowCompact) (σ : ℝ) :
    (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩).charPowerSeries.newtonSlopeMultiplicity vL σ =
      u.charPowerSeries.newtonSlopeMultiplicity v σ :=
  hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs v (algebraMap K L) _
    (AddValuation.apply_eq_of_norm_eq_rpow _ (norm_algebraMap' L) v vL hb hv hvL) σ

/-- **Slopes are the valuations of the eigenvalues in an algebraically closed extension.** Let
`u` be a row-compact endomorphism of `C₀(I, K)` and `L` a complete algebraically closed normed
field extension of `K`. The multiplicity of the slope `σ` in the Fredholm polygon of `u` is the
sum of the algebraic multiplicities `dim (maxGenEigenspace u_L μ)` of the extension `u_L` of `u`
to `C₀(I, L)` over its eigenvalues `μ` of valuation `σ`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs
    (hu : u.IsRowCompact) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : L | vL μ = σ}, Module.finrank L (Module.End.maxGenEigenspace
        (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩ : Module.End L C₀(I, L)) μ) := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs_algebraMap v vL hb hv hvL]
  exact IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank vL hb hvL
    (isPrCompact_iff_isRowCompact.2 (hu.mapCoeffs _ _)) σ

/-- **Cutoff counts of slopes in an algebraically closed extension.** For a row-compact
endomorphism `u` of `C₀(I, K)` and a complete algebraically closed normed field extension `L`
of `K`, the number of slopes at most `c` of the Fredholm polygon of `u`, counted with
multiplicity, is the sum of the algebraic multiplicities of the eigenvalues of valuation at most
`c` of the extension `u_L` of `u` to `C₀(I, L)`. -/
theorem finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs
    (hu : u.IsRowCompact) (c : ℝ) :
    ∑ᶠ σ ∈ Set.Iic c, u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : L | vL μ ≤ c}, Module.finrank L (Module.End.maxGenEigenspace
        (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩ : Module.End L C₀(I, L)) μ) := by
  simp_rw [← hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs_algebraMap v vL hb hv hvL]
  exact IsPrCompact.finsum_mem_Iic_newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank vL
    hb hvL (isPrCompact_iff_isRowCompact.2 (hu.mapCoeffs _ _)) c

/-- **Eigenvalues at every slope in an algebraically closed extension.** Every finite slope `σ`
of the Fredholm polygon of a row-compact endomorphism `u` of `C₀(I, K)` is the valuation of an
eigenvalue of the extension of `u` to `C₀(I, L)`, for every complete algebraically closed normed
field extension `L` of `K`. -/
theorem exists_hasEigenvalue_mapCoeffs_of_newtonSlopeMultiplicity_ne_zero
    (hu : u.IsRowCompact) {σ : ℝ} (hσ : u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0) :
    ∃ μ : L, vL μ = σ ∧ Module.End.HasEigenvalue
      (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩ : Module.End L C₀(I, L)) μ := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs_algebraMap v vL hb hv hvL] at hσ
  exact IsPrCompact.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero vL hb hvL
    (isPrCompact_iff_isRowCompact.2 (hu.mapCoeffs _ _)) hσ

/-- **Independence of the algebraically closed extension.** For a row-compact endomorphism `u` of
`C₀(I, K)` and two complete algebraically closed normed field extensions `L` and `L'` of `K`, the
total algebraic multiplicity of the eigenvalues of valuation `σ` of the extension of `u` is the
same over `L` as over `L'`: both are the multiplicity of the slope `σ` of the Fredholm polygon of
`u`. -/
theorem finsum_finrank_maxGenEigenspace_mapCoeffs_eq {L' : Type*}
    [NontriviallyNormedField L'] [NormedAlgebra K L'] [IsUltrametricDist L'] [CompleteSpace L']
    [IsAlgClosed L'] (vL' : AddValuation L' (WithTop ℝ))
    (hvL' : ∀ y ≠ 0, ‖y‖ = b ^ (-(vL' y).untop₀)) (hu : u.IsRowCompact) (σ : ℝ) :
    ∑ᶠ μ ∈ {μ : L | vL μ = σ}, Module.finrank L (Module.End.maxGenEigenspace
        (u.mapCoeffs (algebraMap K L) ⟨1, by simp⟩ : Module.End L C₀(I, L)) μ) =
      ∑ᶠ μ ∈ {μ : L' | vL' μ = σ}, Module.finrank L' (Module.End.maxGenEigenspace
        (u.mapCoeffs (algebraMap K L') ⟨1, by simp⟩ : Module.End L' C₀(I, L')) μ) := by
  rw [← newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs v vL hb hv hvL hu,
    newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank_mapCoeffs v vL' hb hv hvL' hu]

end IsRowCompact

end Extension

end ContinuousLinearMap
