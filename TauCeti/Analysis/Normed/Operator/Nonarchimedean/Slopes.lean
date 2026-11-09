/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.PrModule
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Splitting
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Zeros
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
Tate scalars.

Over an algebraically closed `K` the slopes are exactly the valuations of the nonzero eigenvalues,
counted with algebraic multiplicity: the multiplicity of `σ` is the sum, over the eigenvalues `μ`
with `v μ = σ`, of the dimensions of the maximal generalised eigenspaces of `u` at `μ`
(`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`).
Thus every finite slope is the valuation of an eigenvalue
(`ContinuousLinearMap.IsPrCompact.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero`).
The zeros of `H_u` of norm `b ^ σ`, counted with the orders of the zeros, number the multiplicity
of `σ` (`PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`), and the order of
the zero at `μ⁻¹` is the algebraic multiplicity of `μ`
(`ContinuousLinearMap.IsPrCompact.finrank_maxGenEigenspace_eq_order_taylor`). Over a field that is
not algebraically closed a slope need not be the valuation of an eigenvalue: the Fredholm series
`1 - p T ^ 2` over `ℚ_p` has the slope `1 / 2` twice, while its eigenvalues `±√p` are not in
`ℚ_p`.

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

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter TauCeti

universe u w

namespace ContinuousLinearMap

section Ring

variable {R : Type w} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] (v : AddValuation R (WithTop ℝ))

omit [NormOneClass R] in
/-- Scaling a row-compact endomorphism by a scalar `a` of finite valuation shifts every slope of
its Fredholm polygon by `v a`, preserving multiplicities. -/
theorem IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul {M : Type u}
    [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {a : R} (ha : v a ≠ ⊤) (σ : ℝ) :
    (a • u).charPowerSeries.newtonSlopeMultiplicity v (σ + (v a).untop₀) =
      u.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [hu.charPowerSeries_smul a, PowerSeries.newtonSlopeMultiplicity_rescale _ ha]

omit [NormOneClass R] in
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
      Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ)).Finite := by
    refine ((PowerSeries.IsRestricted.finite_setOf_norm_le_and_evalAt_eq_zero (L := K)
      (hH.isRestricted (b ^ σ)) (Real.rpow_pos_of_pos hb0 σ) hH0).image (·⁻¹)).subset ?_
    rintro μ ⟨hμσ, hμ⟩
    rw [Function.mem_support, ← Nat.cast_ne_zero (R := ℕ∞), hord hμσ,
      PowerSeries.order_taylor_ne_zero_iff] at hμ
    exact ⟨μ⁻¹, ⟨((hmem μ).mp hμσ).le, hμ⟩, inv_inv μ⟩
  have key : (u.charPowerSeries.newtonSlopeMultiplicity v σ : ℕ∞) =
      ((∑ᶠ μ ∈ {μ : K | v μ = σ},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) := by
    rw [hH.newtonSlopeMultiplicity_eq_finsum_order_taylor v hb hv hH0 σ,
      ← Nat.coe_castAddMonoidHom, (Nat.castAddMonoidHom ℕ∞).map_finsum_mem' hfin]
    exact (finsum_mem_eq_of_bijOn _ hbij fun μ hμ ↦ hord hμ).symm
  exact_mod_cast key

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

end ContinuousLinearMap
