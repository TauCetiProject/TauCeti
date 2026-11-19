/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Duality
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Every tempered distribution is a polynomial weight times a Sobolev distribution

A tempered distribution `f` on a finite-dimensional real inner product space `E` need not lie in
any Bessel-potential space `H^s = H^{s,2}(E)`: the constant function `1`, or the function
`x ↦ ‖x‖ ^ k`, is in no `H^s`, because it does not decay at infinity. Its growth is however
polynomial, and its irregularity of finite order. This file proves the quantitative form: there
are `N : ℕ` and `s : ℝ` with

`f = (1 + ‖x‖ ^ 2) ^ N S` for a tempered distribution `S ∈ H^s`

(`TemperedDistribution.exists_memSobolev_and_eq_smulLeftCLM_pow`). This is how statements proved on
the Bessel-potential spaces extend to arbitrary tempered distributions, for instance the action of
smoothing pseudodifferential operators with compact spatial support.

## Proof

Continuity of `f` on Schwartz space bounds `|f ψ|` by finitely many Schwartz seminorms
`sup_x ‖x‖ ^ k ‖D^l ψ x‖` with `k ≤ N` and `l ≤ L`. For the weight `w(x) = (1 + ‖x‖ ^ 2) ^ (-N)`,
whose derivatives times `‖x‖ ^ k` stay bounded
(`TauCeti.exists_pow_mul_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_neg_le`), the Leibniz
rule bounds these seminorms of `w ψ` by the sup norms of the derivatives of `ψ` of order at most
`l`, and the Sobolev embedding
(`SchwartzMap.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM`) bounds
those by `‖ψ‖_{H^t}` for `t > L + n / 2`
(`SchwartzMap.exists_seminorm_smulLeftCLM_le_mul_norm_toBesselPotentialSpaceCLM`). So
`|(w f) ψ| = |f (w ψ)| ≤ C ‖ψ‖_{H^t}`, and a tempered distribution bounded by the `H^t` norm lies
in `H^{-t}` (`TemperedDistribution.memSobolev_neg_of_norm_le`), by the duality of `H^t` and
`H^{-t}` (`BesselPotentialSpace.dualEquiv`).

## Main results

* `SchwartzMap.exists_seminorm_smulLeftCLM_le_mul_norm_toBesselPotentialSpaceCLM`: the Schwartz
  seminorm `sup_x ‖x‖ ^ k ‖D^l (w ψ) x‖`, `k ≤ N`, is bounded by `‖ψ‖_{H^t}` for `t > l + n / 2`.
* `TemperedDistribution.exists_memSobolev_smulLeftCLM`: `(1 + ‖x‖ ^ 2) ^ (-N) f ∈ H^s` for some
  `N` and `s`.
* `TemperedDistribution.exists_memSobolev_and_eq_smulLeftCLM_pow`: `f = (1 + ‖x‖ ^ 2) ^ N S` with
  `S ∈ H^s`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1 (tempered
  distributions and the seminorm bounds expressing their continuity).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Chapter V (the structure theorem for tempered distributions).
-/

public section

noncomputable section

open MeasureTheory Module
open scoped SchwartzMap BesselPotentialSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace SchwartzMap

/-- **Schwartz seminorms of a decaying multiple.** For `k ≤ N` and `t > l + n / 2`, the Schwartz
seminorm `sup_x ‖x‖ ^ k ‖D^l (w ψ) x‖` of the product of `ψ` with the weight
`w(x) = (1 + ‖x‖ ^ 2) ^ (-N)` is bounded by a constant times `‖ψ‖_{H^t}`. -/
theorem exists_seminorm_smulLeftCLM_le_mul_norm_toBesselPotentialSpaceCLM {k l N : ℕ}
    (hkN : k ≤ N) {t : ℝ} (ht : finrank ℝ E < 2 * (t - l)) :
    ∃ C, ∀ ψ : 𝓢(E, ℂ), SchwartzMap.seminorm ℂ k l
      (smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ)) ψ) ≤
        C * ‖toBesselPotentialSpaceCLM t 2 ψ‖ := by
  set w : E → ℂ := fun x ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ)
  have hw : w.HasTemperateGrowth := by fun_prop
  -- The derivatives of `ψ` of order at most `l` are bounded by `K ‖ψ‖_{H^t}`.
  obtain ⟨K, hK0, hK⟩ := exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM
    (E := E) (F := ℂ) ht
  -- `‖x‖ ^ k` times a derivative of the weight is bounded.
  choose C hC using fun i ↦
    TauCeti.exists_pow_mul_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_neg_le (E := E) hkN i
  refine ⟨∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * C i * K, fun ψ ↦ ?_⟩
  have hC0 (i : ℕ) : 0 ≤ C i :=
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hC i 0)
  refine seminorm_le_bound ℂ k l _ (mul_nonneg (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i)) hK0) (norm_nonneg _)) fun x ↦ ?_
  rw [show (smulLeftCLM ℂ w ψ : E → ℂ) = fun y ↦ w y • ψ y from
    funext (smulLeftCLM_apply_apply hw ψ)]
  refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le
    (TauCeti.contDiff_ofReal_one_add_norm_sq_rpow _) (ψ.smooth ⊤) x
    (by exact_mod_cast le_top)) (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  calc ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
        ‖iteratedFDeriv ℝ (l - i) ψ x‖)
      = (l.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i w x‖) *
          ‖iteratedFDeriv ℝ (l - i) ψ x‖ := by ring
    _ ≤ (l.choose i : ℝ) * C i * (K * ‖toBesselPotentialSpaceCLM t 2 ψ‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hC i x) (Nat.cast_nonneg _))
          (hK ψ _ (Nat.sub_le l i) x) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hC0 i))
    _ = _ := by ring

end SchwartzMap

namespace TemperedDistribution

open SchwartzMap

/-- **Tempered distributions have finite weighted Sobolev order.** For every tempered
distribution `f` there are `N : ℕ` and `s : ℝ` with `(1 + ‖x‖ ^ 2) ^ (-N) f ∈ H^s`. -/
theorem exists_memSobolev_smulLeftCLM (f : 𝓢'(E, ℂ)) :
    ∃ (N : ℕ) (s : ℝ), (smulLeftCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ))
      f).MemSobolev s 2 := by
  -- `f` is bounded by finitely many Schwartz seminorms.
  have hq : Continuous ((normSeminorm ℂ ℂ).comp
      (PointwiseConvergenceCLM.coeLM (E := 𝓢(E, ℂ)) (F := ℂ) ℂ f)) :=
    continuous_norm.comp (map_continuous f)
  obtain ⟨S, c, -, hc⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ E ℂ) _ hq
  set N := S.sup Prod.fst
  set t : ℝ := S.sup Prod.snd + finrank ℝ E + 1
  have ht (i : ℕ × ℕ) (hi : i ∈ S) : (finrank ℝ E : ℝ) < 2 * (t - i.2) := by
    have : (i.2 : ℝ) ≤ S.sup Prod.snd := by exact_mod_cast Finset.le_sup (f := Prod.snd) hi
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    simp only [t]
    linarith
  have hb := fun i (hi : i ∈ S) ↦
    exists_seminorm_smulLeftCLM_le_mul_norm_toBesselPotentialSpaceCLM (E := E)
      (Finset.le_sup (f := Prod.fst) hi) (ht i hi)
  choose! B hB using hb
  refine ⟨N, -t, memSobolev_neg_of_norm_le (C := c * ∑ i ∈ S, B i) fun ψ ↦ ?_⟩
  rw [smulLeftCLM_apply_apply]
  set ψ' := SchwartzMap.smulLeftCLM ℂ
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ)) ψ
  calc ‖f ψ'‖ ≤ c * ∑ i ∈ S, SchwartzMap.seminorm ℂ i.1 i.2 ψ' := by
        refine (hc ψ').trans_eq ?_
        simp [schwartzSeminormFamily, NNReal.smul_def]
    _ ≤ c * ∑ i ∈ S, B i * ‖toBesselPotentialSpaceCLM t 2 ψ‖ := by
        gcongr with i hi
        exact hB i hi ψ
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

/-- **Tempered distributions are polynomial weights times Sobolev distributions.** Every tempered
distribution is `f = (1 + ‖x‖ ^ 2) ^ N S` for some `N : ℕ` and some tempered distribution `S`
in a Bessel-potential space `H^s`. -/
theorem exists_memSobolev_and_eq_smulLeftCLM_pow (f : 𝓢'(E, ℂ)) :
    ∃ (N : ℕ) (s : ℝ) (S : 𝓢'(E, ℂ)), S.MemSobolev s 2 ∧
      f = smulLeftCLM ℂ (fun x : E ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ N) S := by
  obtain ⟨N, s, hS⟩ := exists_memSobolev_smulLeftCLM f
  refine ⟨N, s, _, hS, ?_⟩
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  have h1 : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-(N : ℝ)) : ℝ) : ℂ)) *
      fun x : E ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ N) = fun _ ↦ 1 := by
    funext x
    have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    rw [Pi.mul_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Real.rpow_neg hx.le,
      Real.rpow_natCast, inv_mul_cancel₀ (pow_pos hx N).ne', Complex.ofReal_one]
  rw [h1, smulLeftCLM_const, one_smul]

end TemperedDistribution
