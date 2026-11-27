/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Esymm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TopPower
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.HermitianForm
import TauCeti.Analysis.MvPolynomial.NewtonMaclaurin

/-!
# The Maclaurin inequality for wedge powers of a positive (1,1)-form

Let `E` be a complex inner product space of dimension `n`, with `ω` the Kähler form of
multiplication by `i`, and let `β` be a positive real two-form of type (1,1): `β(u, i u) ≥ 0` for
every `u`. For `1 ≤ k ≤ m ≤ n` the mixed wedge powers satisfy the **Maclaurin form inequality**

`(β ^ m ∧ ω ^ (n - m) / ω ^ n) ^ (1 / m) ≤ (β ^ k ∧ ω ^ (n - k) / ω ^ n) ^ (1 / k)`,

and in particular, for `m = n`,

`(β ^ n / ω ^ n) ^ (1 / n) ≤ (β ^ k ∧ ω ^ (n - k) / ω ^ n) ^ (1 / k)`.

The quotients of top-degree forms are taken on any tuple `v` of `2 n` vectors; they do not depend
on `v` when `ω ^ n (v) ≠ 0`, and both sides vanish when `ω ^ n (v) = 0`.

By the form identity `β ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[β]) ω ^ n` for `k + l = n`
(`TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_ofComplexModule`) and its top case
`β ^ n = (∏ⱼ λⱼ[β]) ω ^ n` (`TauCeti.AlmostComplexStructure.wedgePow_ofComplexModule`), the
quotients are the elementary symmetric means `S_k = σ_k(λ[β]) / binom(n, k)`
(`TauCeti.normalizedEsymm`) of the eigenvalues `λ[β]` of the Hermitian form of `β`. These
eigenvalues are nonnegative (`ContinuousAlternatingMap.relEigenvalues_hermitianSesqForm_nonneg`),
and the inequality is Maclaurin's inequality `S_m^{1/m} ≤ S_k^{1/k}` for nonnegative reals
(`TauCeti.normalizedEsymm_rpow_le_of_nonneg`). For `β = ω` both sides are `1`.

## Main results

* `TauCeti.AlmostComplexStructure.wedge_wedgePow_div_rpow_le_wedge_wedgePow_div_rpow`: the
  Maclaurin form inequality between the mixed wedge powers `β ^ m ∧ ω ^ (n - m)` and
  `β ^ k ∧ ω ^ (n - k)`.
* `TauCeti.AlmostComplexStructure.wedgePow_div_rpow_le_wedge_wedgePow_div_rpow`: its case
  `m = n`, against the top power `β ^ n`.

## References

* B. Guo, D. H. Phong and F. Tong, *On L^∞ estimates for complex Monge–Ampère equations*, Ann. of
  Math. 198 (2023), read as arXiv:2106.02224v1 (the Maclaurin form inequality, lines 924–926).
-/

public section

noncomputable section

open Module ContinuousAlternatingMap Complex

namespace TauCeti.AlmostComplexStructure

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- On a tuple `v` with `ω ^ n (v) ≠ 0`, the quotient `(α ^ k ∧ ω ^ l)(v) / ω ^ n (v)` is the
normalized elementary symmetric function `S_k(λ[α])` of the eigenvalues of `α`. -/
private theorem wedge_wedgePow_wedgePow_div_eq_normalizedEsymm {n k l : ℕ}
    (hn : finrank ℂ E = n) (hkl : k + l = n) (v : Fin (2 * n) → E)
    (hv : (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v ≠ 0) :
    wedge (α.wedgePow k) ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
        (v ∘ Fin.cast (by omega)) /
      (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v =
      normalizedEsymm k ((isSymm_hermitianSesqForm hα).relEigenvalues hn) := by
  rw [wedge_wedgePow_wedgePow_ofComplexModule hα hn hkl, mul_div_assoc, div_self hv, mul_one,
    normalizedEsymm_def, Fintype.card_fin]
  have hc : ((n.choose k : ℕ) : ℝ) * k.factorial * l.factorial = n.factorial := by
    rw [show l = n - k by omega]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
  have : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp
  rw [← hc]
  ring

/-- **The Maclaurin form inequality.** On a complex inner product space of dimension `n`, with
`ω` the Kähler form of multiplication by `i`, a positive real two-form `α` of type (1,1),
`α(u, i u) ≥ 0`, satisfies
`(α ^ m ∧ ω ^ p / ω ^ n) ^ (1 / m) ≤ (α ^ k ∧ ω ^ l / ω ^ n) ^ (1 / k)` for `1 ≤ k ≤ m`,
`k + l = n` and `m + p = n`, the quotients being taken on any tuple `v` of `2 n` vectors. -/
theorem wedge_wedgePow_div_rpow_le_wedge_wedgePow_div_rpow {n k l m p : ℕ}
    (hn : finrank ℂ E = n) (hpos : ∀ u : E, 0 ≤ α ![u, I • u]) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hkl : k + l = n) (hmp : m + p = n) (v : Fin (2 * n) → E) :
    (wedge (α.wedgePow m) ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow p)
          (v ∘ Fin.cast (by omega)) /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^
        (1 / (m : ℝ)) ≤
      (wedge (α.wedgePow k) ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
          (v ∘ Fin.cast (by omega)) /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^
        (1 / (k : ℝ)) := by
  by_cases hv : (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v = 0
  · rw [hv, div_zero, div_zero, Real.zero_rpow (one_div_ne_zero (by norm_cast; omega)),
      Real.zero_rpow (one_div_ne_zero (by norm_cast; omega))]
  rw [wedge_wedgePow_wedgePow_div_eq_normalizedEsymm hα hn hmp v hv,
    wedge_wedgePow_wedgePow_div_eq_normalizedEsymm hα hn hkl v hv]
  exact normalizedEsymm_rpow_le_of_nonneg (relEigenvalues_hermitianSesqForm_nonneg hα hn hpos)
    hk hkm

/-- **The Maclaurin form inequality against the top power.** On a complex inner product space of
dimension `n`, with `ω` the Kähler form of multiplication by `i`, a positive real two-form `α` of
type (1,1), `α(u, i u) ≥ 0`, satisfies
`(α ^ n / ω ^ n) ^ (1 / n) ≤ (α ^ k ∧ ω ^ l / ω ^ n) ^ (1 / k)` for `k ≥ 1` and `k + l = n`, the
quotients being taken on any tuple `v` of `2 n` vectors. -/
theorem wedgePow_div_rpow_le_wedge_wedgePow_div_rpow {n k l : ℕ} (hn : finrank ℂ E = n)
    (hpos : ∀ u : E, 0 ≤ α ![u, I • u]) (hk : 1 ≤ k) (hkl : k + l = n) (v : Fin (2 * n) → E) :
    (α.wedgePow n v /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^ (1 / (n : ℝ)) ≤
      (wedge (α.wedgePow k)
          ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
          (v ∘ Fin.cast (by omega)) /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^
        (1 / (k : ℝ)) := by
  by_cases hv : (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v = 0
  · rw [hv, div_zero, div_zero, Real.zero_rpow (one_div_ne_zero (by norm_cast; omega)),
      Real.zero_rpow (one_div_ne_zero (by norm_cast; omega))]
  rw [wedgePow_ofComplexModule hα hn, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mul_div_assoc, div_self hv, mul_one,
    wedge_wedgePow_wedgePow_div_eq_normalizedEsymm hα hn hkl v hv, ← normalizedEsymm_card_fin]
  exact normalizedEsymm_rpow_le_of_nonneg (relEigenvalues_hermitianSesqForm_nonneg hα hn hpos)
    hk (by omega)

end TauCeti.AlmostComplexStructure
