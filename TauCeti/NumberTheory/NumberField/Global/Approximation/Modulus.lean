/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak

/-!
# Weak approximation relative to a modulus

This file combines global weak approximation (`exists_fieldUnit_valuation_sub_lt_and_signHom_eq`)
with the local unit filtration at finite places of a number field `K`. Given a prime `v₀` dividing
a modulus `𝔪` and a local unit `z ∈ U(K_{v₀}, k)` with `k ≤ 𝔪.exponent v₀`, it produces a global
unit `x ∈ primeToSubgroup 𝔪` approximating `z` to modulus depth at `v₀`, congruent to `1` to
modulus depth at every other prime of `𝔪`, and congruent to `1` to depth `k` at `v₀`.

## Main results

* `TauCeti.GlobalNumberFields.exists_primeToSubgroup_approx_localUnit`: weak approximation in
  `primeToSubgroup 𝔪` for a local unit at a place of `𝔪`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField WithZero

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem valued_sub_le_max {L : Type*} [Field L] [Valued L ℤᵐ⁰] (a b c : L) :
    Valued.v (a - c) ≤ max (Valued.v (a - b)) (Valued.v (b - c)) :=
  sub_add_sub_cancel a b c ▸ Valuation.map_add Valued.v (a - b) (b - c)

private theorem exists_fieldUnit_approx_localUnit {𝔪 : Modulus K}
    {v₀ : HeightOneSpectrum (𝓞 K)} (hv₀ : v₀ ∈ 𝔪.support) (z : (v₀.adicCompletion K)ˣ) :
    ∃ x : Kˣ,
      Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) - (z : v₀.adicCompletion K)) <
          WithZero.exp (-(𝔪.exponent v₀ : ℤ)) ∧
        ∀ v ∈ 𝔪.support, v ≠ v₀ →
          v.valuation K ((x : K) - 1) < WithZero.exp (-(𝔪.exponent v : ℤ)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := v₀.exists_algebraMap_adicCompletion_sub_lt (z : v₀.adicCompletion K)
    (𝔪.exponent v₀)
  obtain ⟨x, hxf, -⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := 𝔪.support)
    (fun v ↦ if v = v₀ then a₀ else 1)
    (fun v ↦ WithZero.exp (-(𝔪.exponent v : ℤ)))
    (fun _ _ ↦ WithZero.exp_ne_zero) 1
  have hxa : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
      algebraMap K (v₀.adicCompletion K) a₀) < WithZero.exp (-(𝔪.exponent v₀ : ℤ)) := by
    rw [← map_sub, valued_algebraMap_adicCompletion]
    simpa using hxf v₀ hv₀
  refine ⟨x, (valued_sub_le_max _ (algebraMap K (v₀.adicCompletion K) a₀) _).trans_lt
      (max_lt hxa ha₀), fun v hv hne ↦ by simpa [hne] using hxf v hv⟩

/-- Given a prime `v₀ ∈ 𝔪.support` and a local unit `z ∈ U(K_{v₀}, k)` with `k ≤ 𝔪.exponent v₀`,
there is a nonzero global element `x ∈ primeToSubgroup 𝔪`, a local unit at every prime dividing
`𝔪`, approximating `z` to level `𝔪.exponent v₀` at `v₀`, congruent to `1` to level `𝔪.exponent v`
at every other `v ∈ 𝔪.support`, and satisfying `v₀.valuation K ((x : K) - 1) ≤ exp (-k)`
(congruent to `1` to depth `k` at `v₀`). -/
theorem exists_primeToSubgroup_approx_localUnit {𝔪 : Modulus K} {v₀ : HeightOneSpectrum (𝓞 K)}
    (hv₀ : v₀ ∈ 𝔪.support) {k : ℕ} (hk : k ≤ 𝔪.exponent v₀)
    (z : (v₀.adicCompletion K)ˣ)
    (hz : z ∈ TauCeti.unitFiltration (v₀.adicCompletion K) k) :
    ∃ x : primeToSubgroup 𝔪,
      Units.map (algebraMap K (v₀.adicCompletion K)).toMonoidHom (x : Kˣ) * z⁻¹ ∈
          TauCeti.unitFiltration (v₀.adicCompletion K) (𝔪.exponent v₀) ∧
        (∀ v ∈ 𝔪.support, v ≠ v₀ →
          Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ) ∈
            TauCeti.unitFiltration (v.adicCompletion K) (𝔪.exponent v)) ∧
        v₀.valuation K (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(k : ℤ)) := by
  obtain ⟨x, hxz, hother⟩ := exists_fieldUnit_approx_localUnit hv₀ z
  have hvpos (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ 𝔪.support) :
      WithZero.exp (-(𝔪.exponent v : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    have hne : 𝔪.exponent v ≠ 0 := (Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).mp hv
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hz_mem := (v₀.mem_unitFiltration_adicCompletion_iff (K := K)).mp hz
  have hx0_val : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K)) = 1 := by
    have hlt : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) -
        (z : v₀.adicCompletion K)) < Valued.v (z : v₀.adicCompletion K) :=
      hxz.trans ((hvpos v₀ hv₀).trans_eq hz_mem.1.symm)
    rw [Valuation.map_eq_of_sub_lt _ hlt, hz_mem.1]
  have hx_mem : x ∈ primeToSubgroup 𝔪 := by
    refine mem_primeToSubgroup.mpr fun v hv ↦ ?_
    have hv' : v ∈ 𝔪.support := (𝔪.mem_support_iff v).mpr hv
    by_cases heq : v = v₀
    · subst heq
      simpa only [valued_algebraMap_adicCompletion] using hx0_val
    · have hlt : v.valuation K ((x : K) - 1) < v.valuation K 1 := by
        rw [map_one]
        exact (hother v hv' heq).trans (hvpos v hv')
      rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  refine ⟨⟨x, hx_mem⟩,
    v₀.mul_inv_mem_unitFiltration_of_sub_lt hz_mem.1 (by simpa using hxz),
    fun v hv hne ↦ (v.unitsMap_algebraMap_mem_unitFiltration_iff (𝔪.exponent v) x).mpr
      ⟨mem_primeToSubgroup.mp hx_mem v ((𝔪.mem_support_iff v).mp hv), (hother v hv hne).le⟩,
    ?_⟩
  have hle : WithZero.exp (-(𝔪.exponent v₀ : ℤ)) ≤ WithZero.exp (-(k : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  have hsub : Valued.v (algebraMap K (v₀.adicCompletion K) (x : K) - 1) ≤
      WithZero.exp (-(k : ℤ)) :=
    (valued_sub_le_max _ (z : v₀.adicCompletion K) 1).trans
      (max_le (hxz.le.trans hle) hz_mem.2)
  simpa only [← map_one (algebraMap K (v₀.adicCompletion K)), ← map_sub,
    valued_algebraMap_adicCompletion] using hsub

end TauCeti.GlobalNumberFields
