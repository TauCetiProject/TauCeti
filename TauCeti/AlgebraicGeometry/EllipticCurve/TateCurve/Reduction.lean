/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Specialization
-- Proof-only: the unit-`c₄` minimality criterion and Tate's test for split multiplicative
-- reduction on an equation whose reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Basic

/-!
# Reduction of the Tate curve

Let `K` be a complete nonarchimedean normed field whose valuation ring `𝒪[K]` is a discrete
valuation ring, and let `q ∈ Kˣ` with `|q| < 1`. The specialized Tate equation

`E_q : y² + xy = x³ + a₄(q) x + a₆(q)`

has its coefficients in `𝒪[K]`, and `a₄(q)` and `a₆(q)` lie in the maximal ideal, since the formal
series `a₄` and `a₆` have no constant term. So `E_q` reduces to the nodal cubic `y² + xy = x³`,
whose two tangent lines `y = 0` and `y = -x` at the node are defined over the residue field.
Its invariant `c₄(q) = 1 + 240 s₃(q)` is a unit of `𝒪[K]`, which makes the equation minimal, and
so `E_q` has **split multiplicative reduction**. Its discriminant is `q` times the evaluation of a
unit of `ℤ⟦q⟧`, so `v(Δ) = v(q)`.

In particular `E_q` never has potential good reduction
(`WeierstrassCurve.HasMultiplicativeReduction.not_hasPotentialGoodReduction`), matching
`|j(E_q)| = 1 / |q| > 1` (`TauCeti.norm_tateCurveAt_j`).

## Main results

* `TauCeti.isIntegral_tateCurveAt`: the specialized Tate equation is integral over `𝒪[K]`.
* `TauCeti.valuation_tateCurveAt_Δ`: `v(Δ(q)) = v(q)`.
* `TauCeti.hasSplitMultiplicativeReduction_tateCurveAt`: the specialized Tate equation is minimal
  and has split multiplicative reduction.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, V.3 and V.5.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

namespace TauCeti

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
  Polynomial
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The specialized Tate equation has its coefficients in the valuation ring `𝒪[K]`. -/
instance isIntegral_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    IsIntegral 𝒪[K] (tateCurveAt q hq) := by
  refine ⟨⟨⟨1, 0, 0, ⟨tateCurveA₄ (q : K) hq, ?_⟩, ⟨tateCurveA₆ (q : K) hq, ?_⟩⟩, ?_⟩⟩
  · exact Valued.integer.mem_iff.mpr ((norm_tateCurveA₄_le _ hq).trans hq.le)
  · exact Valued.integer.mem_iff.mpr ((norm_tateCurveA₆_le _ hq).trans hq.le)
  · ext <;> simp [WeierstrassCurve.baseChange, Algebra.algebraMap_ofSubsemiring_apply]

variable [IsDiscreteValuationRing 𝒪[K]]

/-- **`v(Δ) = v(q)`**: the discriminant of the specialized Tate equation is `q` times a unit of
`𝒪[K]`, so it has the same valuation as the parameter. -/
theorem valuation_tateCurveAt_Δ (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    valuation K (maximalIdeal 𝒪[K]) (tateCurveAt q hq).Δ =
      valuation K (maximalIdeal 𝒪[K]) (q : K) := by
  obtain ⟨u, -, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  -- the cofactor `u(q)` has norm one, so it is a unit of `𝒪[K]` and has valuation one
  have hu₁ : ‖evalIntSeries (q : K) hq u‖ = 1 := norm_evalIntSeries_eq_one_of_isUnit _ hq hu
  let r : 𝒪[K] := ⟨_, Valued.integer.mem_iff.mpr hu₁.le⟩
  have hr : valuation K (maximalIdeal 𝒪[K]) (algebraMap 𝒪[K] K r) = 1 :=
    (valuation_eq_one_iff_notMem _).mpr (notMem_maximalIdeal.mpr
      (Valued.integer.isUnit_iff_norm_eq_one.mpr (by rwa [AddSubgroupClass.coe_norm])))
  rw [Algebra.algebraMap_ofSubsemiring_apply] at hr
  rw [tateCurveAt_Δ, hΔ, map_mul, evalIntSeries_X, map_mul, hr, mul_one]

/-- **The Tate curve has split multiplicative reduction.** Over a complete field whose valuation
ring is a discrete valuation ring, the specialized Tate equation `E_q` is minimal, and it reduces
to the nodal cubic `y² + xy = x³`, whose tangent lines `y = 0` and `y = -x` at the node are
defined over the residue field. -/
instance hasSplitMultiplicativeReduction_tateCurveAt (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSplitMultiplicativeReduction 𝒪[K] (tateCurveAt q hq) := by
  set W := tateCurveAt q hq
  have hcoe (r : 𝒪[K]) : (r : K) = algebraMap 𝒪[K] K r :=
    (Algebra.algebraMap_ofSubsemiring_apply 𝒪[K] r).symm
  -- in `𝒪[K]`, the units are the elements of norm one
  have hunit (r : 𝒪[K]) : IsUnit r ↔ ‖(r : K)‖ = 1 := by
    rw [Valued.integer.isUnit_iff_norm_eq_one, AddSubgroupClass.coe_norm]
  have hmem (r : 𝒪[K]) (hr : ‖(r : K)‖ < 1) : r ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
    (mem_maximalIdeal _).mpr fun h ↦ ((hunit r).mp h).not_lt hr
  have hinj := IsFractionRing.injective 𝒪[K] K
  have ha₁ : (integralModel 𝒪[K] W).a₁ = 1 := hinj <| by simp [integralModel_a₁_eq, W]
  have ha₂ : (integralModel 𝒪[K] W).a₂ = 0 := hinj <| by simp [integralModel_a₂_eq, W]
  have ha₃ : (integralModel 𝒪[K] W).a₃ = 0 := hinj <| by simp [integralModel_a₃_eq, W]
  have ha₄ : (integralModel 𝒪[K] W).a₄ ∈ IsLocalRing.maximalIdeal 𝒪[K] := hmem _ <| by
    rw [hcoe, integralModel_a₄_eq, tateCurveAt_a₄]
    exact (norm_tateCurveA₄_le _ hq).trans_lt hq
  have ha₆ : (integralModel 𝒪[K] W).a₆ ∈ IsLocalRing.maximalIdeal 𝒪[K] := hmem _ <| by
    rw [hcoe, integralModel_a₆_eq, tateCurveAt_a₆]
    exact (norm_tateCurveA₆_le _ hq).trans_lt hq
  -- `c₄` is a unit of `𝒪[K]`, so the equation is minimal
  have : IsMinimal 𝒪[K] W := isMinimal_of_valuation_c₄_eq_one _ W <| by
    rw [← integralModel_c₄_eq 𝒪[K] W]
    refine (valuation_eq_one_iff_notMem _).mpr (notMem_maximalIdeal.mpr ((hunit _).mpr ?_))
    rw [hcoe, integralModel_c₄_eq, norm_tateCurveAt_c₄]
  -- the reduction is `y² + xy = x³`, singular at the origin, with tangent quadratic `T² + T`
  have hsing : (W.reduction 𝒪[K]).toAffine.IsSingular 0 0 :=
    (map_residue_isSingular_zero_iff (integralModel 𝒪[K] W)).mpr ⟨ha₆, ha₄, by simp [ha₃]⟩
  have hred₁ : (W.reduction 𝒪[K]).a₁ = 1 := by simp [reduction, ha₁]
  have hred₂ : (W.reduction 𝒪[K]).a₂ = 0 := by simp [reduction, ha₂]
  refine (hasSplitMultiplicativeReduction_iff_reduction_b₂_ne_zero_and_splits _ hsing).mpr
    ⟨by simp [b₂, hred₁, hred₂], ?_⟩
  convert Splits.X.mul (Splits.X_add_C (1 : ResidueField 𝒪[K])) using 1
  simp [hred₁, hred₂]
  ring

end TauCeti

end
