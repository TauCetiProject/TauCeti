/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.FiniteSlope
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Products
public import TauCeti.NumberTheory.NewtonPolygon.Factorization
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.RingTheory.Idempotents.Module

/-!
# Pure-slope projectors for compact operators

The scalar factorisation `Polynomial.IsPureSlopeFactorization` of the polynomial factor of a
Fredholm series at a cutoff gives orthogonal idempotents whose sum is the cutoff projection. Their
ranges give the direct sum decomposition of the finite-slope space. Each has dimension
equal to its slope multiplicity, and each projector commutes with every bounded operator
commuting with the original operator.
-/

public section

open Polynomial
open TauCeti.PowerSeries (IsEntirePreparation)
open scoped PowerSeries

namespace ContinuousLinearMap

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M] {u E : M →L[K] M}

/-- The pure-slope Riesz–Coleman projections are orthogonal and sum to the cutoff projection.
Their ranges form an internal direct sum equal to the range of the cutoff projection.
The dimension at each slope is its multiplicity in the polynomial factor of the preparation. -/
theorem IsPrCompact.exists_orthogonalIdempotents_pureSlope (hu : u.IsPrCompact)
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {h : ℝ} {Q : K[X]} {S : K⟦X⟧}
    (hQS : IsEntirePreparation (b ^ h)
      (∑ᶠ σ ∈ Set.Iic h, u.charPowerSeries.newtonSlopeMultiplicity v σ) u.charPowerSeries Q S)
    (hE : IsRieszColemanProjection u Q E) :
    ∃ (g : ℝ → K[X]) (e : ℝ → M →L[K] M), Q.IsPureSlopeFactorization v g ∧
      (∀ σ, IsRieszColemanProjection u (g σ) (e σ) ∧
        Module.finrank K (e σ).range = (Q.newtonSlopes v).count σ) ∧
      OrthogonalIdempotents e ∧ (∑ σ ∈ (Q.newtonSlopes v).toFinset, e σ) = E ∧
      iSupIndep (fun σ ↦ (e σ).range) ∧ (⨆ σ, (e σ).range) = E.range := by
  have hN := hu.isMulDistinguished_finsum_newtonSlopeMultiplicity v hb hv h
  have hc : 0 < b ^ h := Real.rpow_pos_of_pos (zero_lt_one.trans hb) h
  obtain ⟨g, hg⟩ := Polynomial.exists_isPureSlopeFactorization v hb hv hQS.coeff_zero_eq_one
  have hex (σ : ℝ) : ∃ e : M →L[K] M,
      IsRieszColemanProjection u (g σ) e ∧ Module.finrank K e.range = (g σ).natDegree := by
    obtain ⟨a, hga, hprod⟩ := hg.exists_isCoprime_mul_eq σ
    exact hu.exists_isRieszColemanProjection_of_isCoprime_mul_eq hc hQS hN hga hprod
  choose e he using hex
  have hproj (σ : ℝ) : IsRieszColemanProjection u (g σ) (e σ) := (he σ).1
  have ho := IsRieszColemanProjection.orthogonalIdempotents_of_pairwise_isCoprime_reverse hproj
    (fun _ _ hij ↦ isCoprime_reverse (hg.pairwise_isCoprime hij))
  have hv₀ (x : K) : v x = ⊤ → x = 0 := v.top_iff.mp
  let slopes := (Q.newtonSlopes v).toFinset
  have hsum : (∑ σ ∈ slopes, e σ) = E := by
    rw [← Finset.sum_coe_sort]
    refine hE.sum_eq_of_prod_reverse_eq (fun σ : slopes ↦ hproj σ)
      (ho.embedding ⟨Subtype.val, Subtype.val_injective⟩) ?_
    rw [Finset.prod_coe_sort slopes (fun σ ↦ (g σ).reverse), ← reverse_prod]
    exact congrArg Polynomial.reverse (hg.prod_toFinset_eq hv₀)
  refine ⟨g, e, hg, fun σ ↦ ⟨hproj σ, (he σ).2.trans (hg.natDegree_apply hv₀ σ)⟩,
    ho, hsum, ?_, ?_⟩
  · simpa only [Module.End.smul_top_eq_range, Function.comp_apply, toLinearMapRingHom_apply] using
      TauCeti.iSupIndep_smul_top (S := K) (M := M) (ho.map toLinearMapRingHom)
  · refine le_antisymm (iSup_le fun σ ↦ (hproj σ).range_le_range_of_dvd hE
      (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (hg.apply_ne_zero σ))) (hg.dvd σ)) ?_
    rintro _ ⟨x, rfl⟩
    rw [coe_coe, ← hsum, sum_apply]
    exact Submodule.sum_mem _ fun σ _ ↦ Submodule.mem_iSup_of_mem σ ⟨x, rfl⟩

end ContinuousLinearMap
