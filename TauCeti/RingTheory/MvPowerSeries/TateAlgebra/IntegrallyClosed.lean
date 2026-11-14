/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.MvPowerSeries.Convolution
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Restricted power series and Tate algebras are integrally closed

Over any ultrametric normed field `K` (without completeness or nontriviality of the norm on `K`),
for any finite variable type `σ` and positive polyradius `c : σ → ℝ`, the ring `T = K{X / c}` of
restricted power series is integrally closed
(`TauCeti.MvPowerSeries.isIntegrallyClosed_isRestricted_subring`).

Passing to the completion `L` of the Gauss-normed fraction field `GaussFractionField σ K c`
produces invertible scalars of norm `c i`, so `L{X / c} ≃ₐ[L] L⟨X⟩` is a unique factorization
domain and hence integrally closed; coefficientwise descent along
`MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` pulls the integral quotient `qL` back from
`L{X / c}` to `K{X / c}`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.1.1 and 5.2.6.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Over any ultrametric normed field `K` (complete or not), the ring `K{X / c}` of restricted power
series in finitely many variables at arbitrary positive polyradius `c` is integrally closed. -/
instance isIntegrallyClosed_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    IsIntegrallyClosed (IsRestricted.subring (R := K) c) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let L := (gaussFractionNorm σ K c).Completion
  have : IsUltrametricDist L :=
    ⟨fun x y z ↦ by
      simpa only [← (AbsoluteValue.Completion.isometry_toCompletion _).dist_eq] using
        dist_triangle_max _ _ _⟩
  let TL := IsRestricted.subring (R := L) c
  let FL := GaussFractionField σ L c
  -- Step 1: In `L = (gaussFractionNorm σ K c).Completion`, the coordinate elements `X i` give
  -- multiplicative units of norm `c i`, so `L{X / c} ≃ₐ[L] L⟨X⟩` is a UFD and integrally closed.
  have hTL_ic : IsIntegrallyClosed TL := by
    let u₀ (i : σ) : L := ((algebraMap T F ⟨X i, isRestricted_X c i⟩ : F) : L)
    have hu₀_norm (i : σ) : ‖u₀ i‖ = c i := by
      rw [← AbsoluteValue.Completion.norm_toCompletion, AbsoluteValue.Completion.toCompletion_coe,
        UniformSpace.Completion.norm_coe, norm_algebraMap_gaussFractionField_X]
    have hu₀_ne (i : σ) : u₀ i ≠ 0 :=
      norm_pos_iff.mp (by rw [hu₀_norm]; exact Fact.out)
    let u (i : σ) : Lˣ := Units.mk0 (u₀ i) (hu₀_ne i)
    have hu_mul (i : σ) : IsNormMulUnit (u i : L) :=
      (Units.isNormMulUnit_iff_norm_inv (u i)).mpr (by rw [Units.val_inv_eq_inv_val, norm_inv])
    have hrs (i : σ) : ‖(u i : L)‖ * (1 : ℝ) = c i := by
      rw [mul_one]; exact hu₀_norm i
    exact IsIntegrallyClosed.of_equiv (restrictedRescaleEquiv u hu_mul hrs).symm.toRingEquiv
  -- Step 2: Embed `T →+* TL` and `F →+* FL` isometrically via `algebraMap K L`.
  have hnorm_alg (a : K) : ‖algebraMap K L a‖ = ‖a‖ := by
    rw [AbsoluteValue.Completion.algebraMap_def, ← AbsoluteValue.Completion.norm_toCompletion,
      AbsoluteValue.Completion.toCompletion_coe, UniformSpace.Completion.norm_coe,
      norm_algebraMap']
  have h_iso (a : K) : ‖algebraMap K L a‖ ≤ 1 * ‖a‖ := by rw [one_mul, hnorm_alg]
  let ψ : T →+* TL := restrictedMap (algebraMap K L) h_iso
  have hψ_norm (f : T) : ‖ψ f‖ = ‖f‖ := norm_restrictedMap (algebraMap K L) h_iso hnorm_alg f
  have hψ_inj : Function.Injective ψ :=
    ((AddMonoidHomClass.isometry_iff_norm ψ).mpr hψ_norm).injective
  let Φ : F →+* FL := ψ.gaussFractionFieldMap hψ_inj
  -- Step 3: Pull back integral elements of `F` from `TL` to `T` coefficientwise.
  refine (isIntegrallyClosed_iff F).mpr fun {x} hx ↦ ?_
  have hΦx : IsIntegral TL (Φ x) := by
    obtain ⟨P, hPm, hPx⟩ := hx
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    have hcomp : Φ.comp (algebraMap T F) = (algebraMap TL FL).comp ψ :=
      RingHom.ext (ψ.gaussFractionFieldMap_algebraMap hψ_inj)
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hPx, map_zero]
  obtain ⟨qL, hqL⟩ := (isIntegrallyClosed_iff FL).mp hTL_ic hΦx
  obtain ⟨f, g, hg_mem, rfl⟩ := IsFractionRing.div_surjective T x
  have hg_ne : (g : T) ≠ 0 := nonZeroDivisors.ne_zero hg_mem
  have hψg_ne : algebraMap TL FL (ψ g) ≠ 0 := by
    refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
    exact fun h0 ↦ hg_ne (hψ_inj (h0.trans ψ.map_zero.symm))
  have hmul_TL : ψ g * qL = ψ f := by
    apply IsFractionRing.injective TL FL
    rw [map_mul, hqL, map_div₀, ψ.gaussFractionFieldMap_algebraMap hψ_inj f,
      ψ.gaussFractionFieldMap_algebraMap hψ_inj g, mul_div_cancel₀ _ hψg_ne]
  -- Step 4: Every coefficient of `qL` lies in `range (algebraMap K L)` by convolution descent.
  let E : Submodule K L := LinearMap.range (Algebra.linearMap K L)
  have hqL_mem : ∀ α, coeff α (qL : _root_.MvPowerSeries σ L) ∈ E := by
    refine _root_.MvPowerSeries.coeff_mem_of_coeff_map_mul_mem E
      (Subtype.coe_ne_coe.mpr hg_ne) (g := (qL : _root_.MvPowerSeries σ L)) fun α ↦ ?_
    have hcoeff := congrArg (fun h : TL ↦ coeff α (h : _root_.MvPowerSeries σ L)) hmul_TL
    rw [Subring.coe_mul, coe_restrictedMap, coeff_restrictedMap] at hcoeff
    rw [hcoeff]
    exact ⟨coeff α (f : _root_.MvPowerSeries σ K), rfl⟩
  choose cq hcq using hqL_mem
  let q_ser : _root_.MvPowerSeries σ K := fun α ↦ cq α
  have hcoeff_q (α : σ →₀ ℕ) : coeff α q_ser = cq α := rfl
  have hq_rest : IsRestricted c q_ser := by
    refine qL.2.congr fun α ↦ ?_
    have h1 : algebraMap K L (coeff α q_ser) = coeff α (qL : _root_.MvPowerSeries σ L) :=
      hcq α
    rw [← h1, hnorm_alg]
  let q : T := ⟨q_ser, hq_rest⟩
  have hψq : ψ q = qL := Subtype.ext <| _root_.MvPowerSeries.ext fun α ↦ by
    rw [coeff_restrictedMap, hcoeff_q]
    exact hcq α
  have hgq : (g : T) * q = f := hψ_inj (by rw [map_mul, hψq, hmul_TL])
  have hgF_ne : algebraMap T F g ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hg_mem
  exact ⟨q, (eq_div_iff hgF_ne).mpr (by rw [mul_comm, ← map_mul, hgq])⟩

end TauCeti.MvPowerSeries
