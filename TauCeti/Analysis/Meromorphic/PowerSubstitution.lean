/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.PowerSubstitution
public import TauCeti.Analysis.Meromorphic.LaurentSeries
public import TauCeti.Analysis.Meromorphic.Pullback
public import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# Laurent expansion under a ramified power substitution

Pullback of meromorphic germs by `z ↦ z ^ d`, for a positive integer `d`, agrees with
formal exponent expansion `X ↦ X ^ d`. Thus the analytic map on the local coefficient
field and the formal map on Laurent expansions commute. This is the coefficient-field
comparison for the local power model of a branched cover. In particular, only exponents
divisible by `d` occur after pullback, including among the negative exponents.

## Main declarations

* `TauCeti.meromorphicGerms.pullbackPow`: pullback by a positive power at zero.
* `TauCeti.meromorphicGerms.laurentSeries_pullbackPow`: compatibility with formal expansion.
* `TauCeti.meromorphicGerms.coeff_laurentSeries_pullbackPow_mul` and
  `TauCeti.meromorphicGerms.coeff_laurentSeries_pullbackPow_of_not_dvd`: the coefficient formulas.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§1–2 (meromorphic functions and
  the local power model).

The constructions reuse `TauCeti.meromorphicGerms.pullback` and `LaurentSeries.expand`.
-/

public noncomputable section

open Filter Function HahnSeries Topology

namespace TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Pullback of meromorphic germs at zero by `z ↦ z ^ d`. Positive powers preserve
punctured neighbourhoods, so this does not depend on the value of a representative at zero. -/
def pullbackPow (d : ℕ+) : meromorphicGerms 𝕜 0 →ₐ[𝕜] meromorphicGerms 𝕜 0 :=
  { pullback (fun z ↦ z ^ (d : ℕ)) (by fun_prop) (zero_pow d.ne_zero)
    (tendsto_nhdsWithin_iff.mpr ⟨by
      simpa only [zero_pow d.ne_zero] using
        ((continuous_pow (d : ℕ)).continuousAt (x := (0 : 𝕜))).tendsto.mono_left
          nhdsWithin_le_nhds,
      by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact pow_ne_zero _ hz⟩) with
    commutes' c := by apply pullback_algebraMap }

/-- Power pullback of a represented germ is represented by power substitution. -/
@[simp]
theorem pullbackPow_mk (d : ℕ+) (f : 𝕜 → 𝕜) (hf : MeromorphicAt f 0) :
    pullbackPow d (mk f hf) = mk (fun z ↦ f (z ^ (d : ℕ)))
      (by
        apply MeromorphicAt.comp_analyticAt (g := fun z : 𝕜 ↦ z ^ (d : ℕ))
          (x := (0 : 𝕜)) _ (by fun_prop)
        simpa only [zero_pow d.ne_zero] using hf) := by
  apply Subtype.ext
  simp only [pullbackPow, AlgHom.coe_mk, coe_pullback, coe_mk, Germ.coe_compTendsto]
  rfl

/-- The coordinate pulls back to its `d`-th power. -/
@[simp]
theorem pullbackPow_coordinate (d : ℕ+) :
    pullbackPow d (coordinate (0 : 𝕜)) = coordinate 0 ^ (d : ℕ) := by
  apply Subtype.ext
  simp only [pullbackPow, AlgHom.coe_mk, coe_pullback, SubmonoidClass.coe_pow, coe_coordinate,
    Germ.coe_compTendsto, ← Germ.coe_pow]
  exact Germ.coe_eq.mpr (.of_forall fun z ↦ by simp)

/-- Pullback by the first power is the identity. -/
@[simp]
theorem pullbackPow_one : pullbackPow (𝕜 := 𝕜) 1 = AlgHom.id _ _ := by
  ext φ
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  simp only [pullbackPow_mk, PNat.val_ofNat, pow_one, AlgHom.id_apply]

/-- Composing power pullbacks multiplies their exponents. -/
theorem pullbackPow_mul (d e : ℕ+) :
    pullbackPow (𝕜 := 𝕜) (d * e) = (pullbackPow d).comp (pullbackPow e) := by
  ext φ
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  simp only [AlgHom.comp_apply, pullbackPow_mk, PNat.mul_coe, pow_mul]

/-- Laurent expansion identifies analytic power pullback with formal exponent expansion.
The identity includes principal parts, rather than only holomorphic germs. -/
theorem laurentSeries_pullbackPow (d : ℕ+) (φ : meromorphicGerms 𝕜 0) :
    laurentSeries 0 (pullbackPow d φ) = LaurentSeries.expand 𝕜 d (laurentSeries 0 φ) := by
  obtain ⟨f, ⟨N, hN⟩, hφ⟩ := mem_meromorphicGerms_iff.mp φ.2
  let h : 𝕜 → 𝕜 := fun z ↦ z ^ N • f z
  have hh : AnalyticAt 𝕜 h 0 := by simpa only [sub_zero] using hN
  have hrep : (φ : Germ (𝓝[≠] (0 : 𝕜)) 𝕜) =
      (fun z ↦ ((z - 0) ^ N)⁻¹ * h z : 𝕜 → 𝕜) := by
    rw [← hφ, Germ.coe_eq]
    filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
    simp [h, smul_eq_mul, hz]
  have hp : (pullbackPow d φ : Germ (𝓝[≠] (0 : 𝕜)) 𝕜) =
      (fun z ↦ ((z - 0) ^ ((d : ℕ) * N))⁻¹ * h (z ^ (d : ℕ)) : 𝕜 → 𝕜) := by
    rw [pullbackPow, AlgHom.coe_mk, coe_pullback, hrep, Germ.coe_compTendsto]
    simp only [Function.comp_def, sub_zero, pow_mul]
  have hhcomp : AnalyticAt 𝕜 (fun z ↦ h (z ^ (d : ℕ))) 0 :=
    hh.comp_of_eq (by fun_prop) (zero_pow d.ne_zero)
  rw [laurentSeries_eq hhcomp hp,
    laurentSeries_eq hh hrep, map_mul, LaurentSeries.expand_single,
    LaurentSeries.expand_coe, taylorSeries_comp_pow hh (d : ℕ) d.ne_zero]
  simp only [Nat.cast_mul, mul_neg]

/-- After power pullback, the coefficient at exponent `d * n` is the original coefficient
at exponent `n`, including when `n` is negative. -/
@[simp]
theorem coeff_laurentSeries_pullbackPow_mul (d : ℕ+) (φ : meromorphicGerms 𝕜 0) (n : ℤ) :
    (laurentSeries 0 (pullbackPow d φ)).coeff ((d : ℤ) * n) =
      (laurentSeries 0 φ).coeff n := by
  rw [laurentSeries_pullbackPow, LaurentSeries.coeff_expand_mul]

/-- Exponents not divisible by the local power degree have zero coefficient after pullback. -/
theorem coeff_laurentSeries_pullbackPow_of_not_dvd (d : ℕ+) (φ : meromorphicGerms 𝕜 0)
    {n : ℤ} (hn : ¬ (d : ℤ) ∣ n) : (laurentSeries 0 (pullbackPow d φ)).coeff n = 0 := by
  rw [laurentSeries_pullbackPow]
  exact LaurentSeries.coeff_expand_of_not_dvd d _ hn

end TauCeti.meromorphicGerms
