/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

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

First, `TauCeti.MvPowerSeries.isIntegrallyClosed_isRestricted_subring_of_isometry` shows that
integral closedness of `K{X / c}` descends along any isometric field homomorphism `K →+* L` (for
arbitrary `σ`): coefficientwise descent along `MvPowerSeries.coeff_mem_of_coeff_map_mul_mem` pulls
any integral element of `GaussFractionField σ K c` that lies in `L{X / c}` back to `K{X / c}`.
For finite `σ`, passing to the completion `L` of `GaussFractionField σ K c` produces invertible
scalars of norm `c i`, so `L{X / c} ≃ₐ[L] L⟨X⟩` is a unique factorization domain and hence
integrally closed.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.1.1 and 5.2.6.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Isometric descent of integral closedness.** If `f : K →+* L` is an isometric homomorphism of
ultrametric normed fields and `L{X / c}` is integrally closed for a positive polyradius `c`, then
`K{X / c}` is integrally closed (without finiteness of `σ` or completeness). -/
theorem isIntegrallyClosed_isRestricted_subring_of_isometry {L : Type*} [NormedField L]
    [IsUltrametricDist L] {c : σ → ℝ} [∀ i, Fact (0 < c i)] (f : K →+* L) (hf : Isometry f)
    (hL : IsIntegrallyClosed (IsRestricted.subring (R := L) c)) :
    IsIntegrallyClosed (IsRestricted.subring (R := K) c) := by
  let _ : Algebra K L := f.toAlgebra
  have hf_alg : algebraMap K L = f := RingHom.algebraMap_toAlgebra f
  have hnorm (a : K) : ‖f a‖ = ‖a‖ := (AddMonoidHomClass.isometry_iff_norm f).mp hf a
  have h_le (a : K) : ‖f a‖ ≤ 1 * ‖a‖ := by rw [one_mul, hnorm]
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let TL := IsRestricted.subring (R := L) c
  let FL := GaussFractionField σ L c
  let ψ : T →+* TL := restrictedMap f h_le
  have hψ_inj : Function.Injective ψ := (isometry_restrictedMap f h_le hnorm).injective
  let Φ : F →+* FL := ψ.gaussFractionFieldMap hψ_inj
  refine (isIntegrallyClosed_iff F).mpr fun {x} hx ↦ ?_
  have hΦx : IsIntegral TL (Φ x) :=
    hx.map_of_comp_eq ψ Φ (RingHom.ext fun t ↦ (ψ.gaussFractionFieldMap_algebraMap hψ_inj t).symm)
  obtain ⟨qL, hqL⟩ := (isIntegrallyClosed_iff FL).mp hL hΦx
  obtain ⟨a, b, hb_mem, rfl⟩ := IsFractionRing.div_surjective T x
  have hb_ne : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  have hψb_ne : algebraMap TL FL (ψ b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero fun h0 ↦
      hb_ne (hψ_inj (h0.trans ψ.map_zero.symm))
  have hmul_TL : ψ b * qL = ψ a := IsFractionRing.injective TL FL <| by
    rw [map_mul, hqL, map_div₀, ψ.gaussFractionFieldMap_algebraMap hψ_inj,
      ψ.gaussFractionFieldMap_algebraMap hψ_inj, mul_div_cancel₀ _ hψb_ne]
  have hqL_mem : ∀ α, coeff α (qL : _root_.MvPowerSeries σ L) ∈
      LinearMap.range (Algebra.linearMap K L) :=
    _root_.MvPowerSeries.coeff_mem_of_coeff_map_mul_mem _ (Subtype.coe_ne_coe.mpr hb_ne)
      (g := (qL : _root_.MvPowerSeries σ L)) fun α ↦ by
        have hcoeff := congrArg (fun h : TL ↦ coeff α (h : _root_.MvPowerSeries σ L)) hmul_TL
        rw [Subring.coe_mul, coe_restrictedMap, coeff_restrictedMap, ← hf_alg] at hcoeff
        exact ⟨coeff α (a : _root_.MvPowerSeries σ K), hcoeff.symm⟩
  choose cq hcq using hqL_mem
  let q_ser : _root_.MvPowerSeries σ K := cq
  let q : T := ⟨q_ser, qL.property.congr fun α ↦ by
    rw [← hcq α, Algebra.linearMap_apply, hf_alg, hnorm, _root_.MvPowerSeries.coeff_apply]⟩
  have hψq : ψ q = qL := Subtype.ext <| _root_.MvPowerSeries.ext fun α ↦ by
    rw [coeff_restrictedMap, _root_.MvPowerSeries.coeff_apply, ← hf_alg,
      ← Algebra.linearMap_apply K L, hcq α]
  have hbq : (b : T) * q = a := hψ_inj (by rw [map_mul, hψq, hmul_TL])
  exact ⟨q, (eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb_mem)).mpr
    (by rw [mul_comm, ← map_mul, hbq])⟩

/-- Over any ultrametric normed field `K` (complete or not), the ring `K{X / c}` of restricted power
series in finitely many variables at arbitrary positive polyradius `c` is integrally closed. -/
instance isIntegrallyClosed_isRestricted_subring [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)] :
    IsIntegrallyClosed (IsRestricted.subring (R := K) c) := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let L := (gaussFractionNorm σ K c).Completion
  have : IsUltrametricDist L := ⟨fun _ _ _ ↦ by
    simpa only [← (AbsoluteValue.Completion.isometry_toCompletion _).dist_eq] using
      dist_triangle_max _ _ _⟩
  let u₀ (i : σ) : L := ((algebraMap T F ⟨X i, isRestricted_X c i⟩ : F) : L)
  have hu₀_norm (i : σ) : ‖u₀ i‖ = c i := by
    rw [← AbsoluteValue.Completion.norm_toCompletion, AbsoluteValue.Completion.toCompletion_coe,
      UniformSpace.Completion.norm_coe, norm_algebraMap_gaussFractionField_X]
  let u (i : σ) : Lˣ := Units.mk0 (u₀ i) (norm_pos_iff.mp (hu₀_norm i ▸ Fact.out))
  have hu_mul (i : σ) : IsNormMulUnit (u i : L) := (isNormMulUnit_iff_isUnit _).mpr (u i).isUnit
  have hTL_ic : IsIntegrallyClosed (IsRestricted.subring (R := L) c) :=
    IsIntegrallyClosed.of_equiv
      (restrictedRescaleEquiv u hu_mul fun i ↦ (mul_one _).trans (hu₀_norm i)).symm.toRingEquiv
  have h_iso : Isometry (algebraMap K L) :=
    (AddMonoidHomClass.isometry_iff_norm (algebraMap K L)).mpr fun a ↦ by
      rw [AbsoluteValue.Completion.algebraMap_def, ← AbsoluteValue.Completion.norm_toCompletion,
        AbsoluteValue.Completion.toCompletion_coe, UniformSpace.Completion.norm_coe,
        norm_algebraMap']
  exact isIntegrallyClosed_isRestricted_subring_of_isometry (algebraMap K L) h_iso hTL_ic

end TauCeti.MvPowerSeries
