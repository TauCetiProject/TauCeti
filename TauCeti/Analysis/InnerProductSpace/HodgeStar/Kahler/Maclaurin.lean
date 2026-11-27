/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Esymm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TopPower
import TauCeti.Analysis.MeanInequalities

/-!
# The Maclaurin inequality for wedge powers of a positive (1,1)-form

Let `E` be a complex inner product space of dimension `n`, with `ω` the Kähler form of
multiplication by `i`, and let `β` be a positive real two-form of type (1,1): `β(u, i u) ≥ 0` for
every `u`. For `1 ≤ k ≤ n` the wedge powers satisfy the **Maclaurin form inequality**

`(β ^ n / ω ^ n) ^ (1 / n) ≤ (β ^ k ∧ ω ^ (n - k) / ω ^ n) ^ (1 / k)`

(`TauCeti.AlmostComplexStructure.wedgePow_div_rpow_le_wedge_wedgePow_div_rpow`). The quotients
of top-degree forms are taken on any tuple `v` of `2 n` vectors with `ω ^ n (v) ≠ 0`; they do not
depend on `v`.

By the form identity `β ^ k ∧ ω ^ l = (k! l! / n!) σ_k(λ[β]) ω ^ n` for `k + l = n`
(`TauCeti.AlmostComplexStructure.wedge_wedgePow_wedgePow_ofComplexModule`) and its top case
`β ^ n = (∏ⱼ λⱼ[β]) ω ^ n` (`TauCeti.AlmostComplexStructure.wedgePow_ofComplexModule`), the
quotients are the elementary symmetric means `S_k = σ_k(λ[β]) / binom(n, k)` and `S_n` of the
eigenvalues `λ[β]` of the Hermitian form of `β`. These eigenvalues are the values `β(uⱼ, i uⱼ)`
on an eigenbasis, so they are nonnegative, and the inequality is Maclaurin's inequality
`S_n^{1/n} ≤ S_k^{1/k}` for nonnegative reals (`Multiset.esymm_div_choose_rpow_le_rpow_of_nonneg`).
For `β = ω` both sides are `1`.

## Main results

* `TauCeti.AlmostComplexStructure.relEigenvalues_nonneg_of_apply_I_smul_nonneg`: a positive
  (1,1)-form has nonnegative eigenvalues relative to the inner product.
* `TauCeti.AlmostComplexStructure.wedgePow_div_rpow_le_wedge_wedgePow_div_rpow`: the Maclaurin
  form inequality.

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

/-- A positive real two-form `α` of type (1,1), `α(u, i u) ≥ 0` for every `u`, has nonnegative
eigenvalues relative to the inner product: `λⱼ[α] = α(uⱼ, i uⱼ)` on the eigenbasis `u`. -/
theorem relEigenvalues_nonneg_of_apply_I_smul_nonneg {n : ℕ} (hn : finrank ℂ E = n)
    (hpos : ∀ u : E, 0 ≤ α ![u, I • u]) (j : Fin n) :
    0 ≤ (isSymm_hermitianSesqForm hα).relEigenvalues hn j := by
  have h := apply_relEigenvectorBasis_I_smul hα hn j j
  simp only [↓reduceIte] at h
  exact h ▸ hpos _

/-- **The Maclaurin form inequality.** On a complex inner product space of dimension `n`, with
`ω` the Kähler form of multiplication by `i`, a positive real two-form `α` of type (1,1),
`α(u, i u) ≥ 0`, satisfies `(α ^ n / ω ^ n) ^ (1 / n) ≤ (α ^ k ∧ ω ^ l / ω ^ n) ^ (1 / k)` for
`k ≥ 1` and `k + l = n`, the quotients being taken on any tuple `v` of `2 n` vectors with
`ω ^ n (v) ≠ 0`. -/
theorem wedgePow_div_rpow_le_wedge_wedgePow_div_rpow {n k l : ℕ} (hn : finrank ℂ E = n)
    (hpos : ∀ u : E, 0 ≤ α ![u, I • u]) (hk : 1 ≤ k) (hkl : k + l = n) (v : Fin (2 * n) → E)
    (hv : (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v ≠ 0) :
    (α.wedgePow n v /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^ (1 / (n : ℝ)) ≤
      (wedge (α.wedgePow k)
          ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow l)
          (v ∘ Fin.cast (by omega)) /
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow n v) ^
        (1 / (k : ℝ)) := by
  set μ := (isSymm_hermitianSesqForm hα).relEigenvalues hn
  set s : Multiset ℝ := Finset.univ.val.map μ
  have hs : Multiset.card s = n := by simp [s]
  have hmac := s.esymm_div_choose_rpow_le_rpow_of_nonneg hk (show k ≤ n by omega)
    (fun a ha ↦ by
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
      exact relEigenvalues_nonneg_of_apply_I_smul_nonneg hα hn hpos j)
  have hesymm (j : ℕ) : MvPolynomial.eval μ (MvPolynomial.esymm (Fin n) ℝ j) = s.esymm j := by
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℝ j μ
  have hprod : ∏ j, μ j = s.esymm n := by
    have h : s.esymm (Multiset.card s) = s.prod := by
      simp [Multiset.esymm, Multiset.powersetCard_self]
    rw [hs] at h
    rw [h, Finset.prod_eq_multiset_prod]
  rw [wedgePow_ofComplexModule hα hn, wedge_wedgePow_wedgePow_ofComplexModule hα hn hkl,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self hv, mul_one,
    mul_div_assoc, div_self hv, mul_one, hprod, hesymm]
  rw [hs, Nat.choose_self, Nat.cast_one, div_one] at hmac
  convert hmac using 2
  have hl : l = n - k := by omega
  have hc := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  rw [← hl] at hc
  have hc' : ((n.choose k : ℕ) : ℝ) * k.factorial * l.factorial = n.factorial := by
    exact_mod_cast hc
  have : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp
  rw [← hc']
  ring

end TauCeti.AlmostComplexStructure
