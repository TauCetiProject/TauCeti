/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Bounds
public import TauCeti.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Analysis.Calculus.Hadamard.Basic

/-!
# Parameter families of approximate solutions of every finite order

Let `F : P × ℝ × E → G` be a family of equations `F (p, h, x) = 0` in a parameter `p` and a small
variable `h`, with a solution `x₀ p` at `h = 0` for every `p`. Suppose the partial derivative of
`x ↦ F (p, 0, x)` at `x₀ p` has a right inverse `R p` of class `C^(k + N)` in `p`, and that `F`
and `x₀` are of class `C^(k + N + 1)`. Then the solution can be continued to every finite order `N`
in `h`, with `C^k` dependence on the parameter: there are `C^k` coefficients `yᵢ : P → E` such that
the polynomial profile `X (p, h) = x₀ p + ∑_{i < N} h^(i+1) • yᵢ p` has residual

`F (p, h, X (p, h)) = h^(N+1) • Q (p, h)`

for a function `Q` that is jointly `C^k` in `p` and `h`
(`TauCeti.exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse`). This is the parametric
form of `TauCeti.exists_isBigO_pow_of_surjective`, which works at a single parameter and only gives
`F (h, X h) = O(h^(N+1))`.

**The derivative ledger.** The statement keeps track of finitely many derivatives. If `F` and `x₀`
are `C^(k + N + 1)` and `R` is `C^(k + N)`, the coefficients and the quotient `Q` are `C^k`: each
order of the profile costs one derivative. A residual written as `h^(N+1)` times a `C^k` function
is the natural output for uniform estimates. On a compact set `K` of parameters and for
`|h| ≤ h₀`, the residual and its derivatives in `p` through order `k` are bounded by
`C |h|^(N+1)`, with `C` depending only on `K`, `h₀` and the order of the derivative
(`ContDiff.exists_forall_norm_iteratedFDeriv_le_mul_pow_of_eq_pow_smul` for a given residual
identity, `TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_pow_of_fderiv_rightInverse`,
`TauCeti.exists_forall_norm_le_mul_pow_of_fderiv_rightInverse`). An estimate
`F (p, h, X (p, h)) = O(h^(N+1))` at each `p` separately would give neither the uniformity in `p`
nor the bounds on derivatives in `p`.

**The construction.** It is one order at a time and uses only Hadamard division in `h`
(`ContDiff.exists_contDiff_sub_eq_smul`) and the averaged derivative
(`ContDiff.sub_eq_hadamardFactor_apply`), with no Taylor coefficients. At order `0`, dividing
`F (p, h, x₀ p)` by `h` gives the quotient. If the profile `X` of order `N` has residual
`h^(N+1) • Q`, the correction `h^(N+1) • z` with `z p = -R p (Q (p, 0))` changes the residual by
`h^(N+1) • H (p, h)`, where `H (p, h)` is the averaged derivative of `F` between the two profiles
applied to `(0, 0, z p)`. At `h = 0` the two profiles agree, so `H (p, 0)` is the derivative of
`F` at `(p, 0, x₀ p)` applied to `(0, 0, z p)`, which is `-Q (p, 0)`. The new residual is
therefore `h^(N+1) • ((Q (p, h) - Q (p, 0)) + (H (p, h) - H (p, 0)))`, and both differences are
divisible by `h`.

In Taubes's construction of
approximate Seiberg–Witten solutions near a pseudoholomorphic curve, `p` ranges over a compact
window of divisors of vortex zeros and the right inverses are those of the linearized vortex
equations, which depend smoothly on the divisor.

## Main results

* `TauCeti.exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse`: profiles of every finite
  order with `C^k` coefficients whose residual is `h^(N+1)` times a jointly `C^k` function.
* `TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_pow_of_fderiv_rightInverse`: the residual and
  its derivatives in the parameter are `O(|h|^(N+1))` uniformly on compact sets of parameters.
* `TauCeti.exists_forall_norm_le_mul_pow_of_fderiv_rightInverse`: the residual is `O(|h|^(N+1))`
  uniformly on compact sets of parameters, with continuous coefficients.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *GR = SW: Counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

open Finset

namespace TauCeti

variable {P E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The base order: dividing `F (p, h, x₀ p)` by `h`. -/
private theorem exists_contDiff_eq_pow_one_smul {k : ℕ∞} {F : P × ℝ × E → G} {x₀ : P → E}
    (hF : ContDiff ℝ (k + 1 : ℕ∞) F) (hx₀ : ContDiff ℝ (k + 1 : ℕ∞) x₀)
    (h₀ : ∀ p, F (p, 0, x₀ p) = 0) :
    ∃ Q : P × ℝ → G, ContDiff ℝ k Q ∧ ∀ p h, F (p, h, x₀ p) = h ^ 1 • Q (p, h) := by
  obtain ⟨Q, hQ, hQe⟩ := (hF.comp (by fun_prop :
    ContDiff ℝ (k + 1 : ℕ∞) fun q : P × ℝ ↦ (q.1, q.2, x₀ q.1))).exists_contDiff_sub_eq_smul
  refine ⟨Q, hQ, fun p h ↦ ?_⟩
  simpa [h₀] using hQe p h

/-- **The correction of one order.** Let the profile `X` have residual `h^(N+1) • Q`, and let
`z p` be a vertical direction on which the derivative of `F` at `(p, 0, X (p, 0))` is `-Q (p, 0)`.
Then the corrected profile `X + h^(N+1) • z` has residual `h^(N+2) • Q'`, losing one derivative. -/
private theorem exists_contDiff_eq_pow_succ_smul {k : ℕ∞} {N : ℕ} {F : P × ℝ × E → G}
    {X : P × ℝ → E} {z : P → E} {Q : P × ℝ → G} (hF : ContDiff ℝ (k + 1 + 1 : ℕ∞) F)
    (hX : ContDiff ℝ (k + 1 : ℕ∞) X) (hz : ContDiff ℝ (k + 1 : ℕ∞) z)
    (hQ : ContDiff ℝ (k + 1 : ℕ∞) Q) (hFQ : ∀ p h, F (p, h, X (p, h)) = h ^ (N + 1) • Q (p, h))
    (hz' : ∀ p, fderiv ℝ F (p, 0, X (p, 0)) (0, 0, z p) = -Q (p, 0)) :
    ∃ Q' : P × ℝ → G, ContDiff ℝ k Q' ∧
      ∀ p h, F (p, h, X (p, h) + h ^ (N + 1) • z p) = h ^ (N + 2) • Q' (p, h) := by
  -- The averaged derivative of `F` between the two profiles, applied to the direction `z`.
  set H : P × ℝ → G := fun q ↦ hadamardFactor F (q.1, q.2, X q)
    (q.1, q.2, X q + q.2 ^ (N + 1) • z q.1) (0, 0, z q.1)
  have hH : ContDiff ℝ (k + 1 : ℕ∞) H :=
    ((ContDiff.contDiff_hadamardFactor_uncurry_of_succ (k + 1) F hF).comp (by fun_prop :
      ContDiff ℝ (k + 1 : ℕ∞) fun q : P × ℝ ↦
        ((q.1, q.2, X q), (q.1, q.2, X q + q.2 ^ (N + 1) • z q.1)))).clm_apply (by fun_prop)
  -- The correction changes the residual by `h^(N+1) • H`.
  have hdiff (p : P) (h : ℝ) :
      F (p, h, X (p, h) + h ^ (N + 1) • z p) - F (p, h, X (p, h)) = h ^ (N + 1) • H (p, h) := by
    rw [ContDiff.sub_eq_hadamardFactor_apply F (hF.of_le (by exact_mod_cast le_add_self))]
    have hd : ((p, h, X (p, h) + h ^ (N + 1) • z p) : P × ℝ × E) - (p, h, X (p, h)) =
        h ^ (N + 1) • ((0 : P), (0 : ℝ), z p) := by ext <;> simp
    rw [hd, map_smul]
  -- At `h = 0` the two profiles agree, and `H` is the derivative of `F` applied to `z`.
  have hH0 (p : P) : H (p, 0) = -Q (p, 0) := by
    simp only [H, zero_pow (Nat.succ_ne_zero N), zero_smul, add_zero, hadamardFactor_self]
    exact hz' p
  obtain ⟨D₁, hD₁, hD₁e⟩ := hQ.exists_contDiff_sub_eq_smul
  obtain ⟨D₂, hD₂, hD₂e⟩ := hH.exists_contDiff_sub_eq_smul
  refine ⟨fun q ↦ D₁ q + D₂ q, hD₁.add hD₂, fun p h ↦ ?_⟩
  have e₁ := hdiff p h
  have e₂ := hD₁e p h
  have e₃ := hD₂e p h
  rw [hFQ] at e₁
  rw [hH0] at e₃
  linear_combination (norm := module) e₁ + h ^ (N + 1) • e₂ + h ^ (N + 1) • e₃

/-- **`C^k` families of approximate solutions of every finite order.** Let `F (p, 0, x₀ p) = 0`
for every parameter `p`, and let `R p` be a right inverse of the partial derivative of
`x ↦ F (p, 0, x)` at `x₀ p`. If `F` and `x₀` are `C^(k + N + 1)` and `R` is `C^(k + N)`, there are
`C^k` coefficients `yᵢ` and a `C^k` function `Q` such that along the profile
`x₀ p + ∑_{i < N} h^(i+1) • yᵢ p` the residual is `h^(N+1) • Q (p, h)`, for all `p` and `h`. -/
theorem exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse {k : ℕ∞} {N : ℕ}
    {F : P × ℝ × E → G} {x₀ : P → E} {R : P → G →L[ℝ] E} (hF : ContDiff ℝ (k + N + 1 : ℕ∞) F)
    (hx₀ : ContDiff ℝ (k + N + 1 : ℕ∞) x₀) (hR : ContDiff ℝ (k + N : ℕ∞) R)
    (h₀ : ∀ p, F (p, 0, x₀ p) = 0)
    (hR' : ∀ p v, fderiv ℝ (fun x ↦ F (p, 0, x)) (x₀ p) (R p v) = v) :
    ∃ y : ℕ → P → E, (∀ i, ContDiff ℝ k (y i)) ∧ ∃ Q : P × ℝ → G, ContDiff ℝ k Q ∧
      ∀ p h, F (p, h, x₀ p + ∑ i ∈ range N, h ^ (i + 1) • y i p) = h ^ (N + 1) • Q (p, h) := by
  induction N generalizing k with
  | zero =>
    obtain ⟨Q, hQ, hQe⟩ := exists_contDiff_eq_pow_one_smul (by simpa using hF)
      (by simpa using hx₀) h₀
    exact ⟨0, fun _ ↦ contDiff_const, Q, hQ, by simpa using hQe⟩
  | succ N ih =>
    have hle : ((k + 1 + N + 1 : ℕ∞) : WithTop ℕ∞) ≤ (k + ↑(N + 1) + 1 : ℕ∞) := by
      push_cast; exact le_of_eq (by ring)
    obtain ⟨y, hy, Q, hQ, hFQ⟩ := ih (k := k + 1) (hF.of_le hle) (hx₀.of_le hle)
      (hR.of_le (by push_cast; exact le_of_eq (by ring)))
    -- The next coefficient cancels the leading coefficient `Q (p, 0)` of the residual.
    have hk : (k + 1 : ℕ∞) ≤ k + ↑(N + 1) := by push_cast; gcongr; exact le_add_self
    set z : P → E := fun p ↦ -R p (Q (p, 0))
    have hz : ContDiff ℝ (k + 1 : ℕ∞) z :=
      ((hR.of_le (by exact_mod_cast hk)).clm_apply (hQ.comp (by fun_prop))).neg
    have hX : ContDiff ℝ (k + 1 : ℕ∞) fun q : P × ℝ ↦
        x₀ q.1 + ∑ i ∈ range N, q.2 ^ (i + 1) • y i q.1 :=
      ((hx₀.of_le (by exact_mod_cast hk.trans le_self_add)).comp contDiff_fst).add
        (ContDiff.sum fun i _ ↦ (contDiff_snd.pow _).smul ((hy i).comp contDiff_fst))
    have hz' (p : P) : fderiv ℝ F (p, 0, x₀ p + ∑ i ∈ range N, (0 : ℝ) ^ (i + 1) • y i p)
        (0, 0, z p) = -Q (p, 0) := by
      -- On vertical directions the derivative of `F` is the partial derivative in `x`.
      have hd : DifferentiableAt ℝ F (p, 0, x₀ p) := hF.differentiable (by simp) _
      have hRp := hR' p (Q (p, 0))
      rw [fderiv_slice_right (f := fun y : ℝ × E ↦ F (p, y))
        (hd.comp _ (differentiableAt_const p |>.prodMk differentiableAt_id)),
        fderiv_slice_right hd] at hRp
      have hneg : ((0 : P), (0 : ℝ), z p) = -((0 : P), (0 : ℝ), R p (Q (p, 0))) := by simp [z]
      simp only [zero_pow (Nat.succ_ne_zero _), zero_smul, sum_const_zero, add_zero]
      rw [hneg, map_neg]
      simpa using congrArg Neg.neg hRp
    obtain ⟨Q', hQ', hFQ'⟩ := exists_contDiff_eq_pow_succ_smul (N := N) (z := z)
      (hF.of_le (by exact_mod_cast add_le_add_left hk 1)) hX hz hQ hFQ hz'
    refine ⟨Function.update y N z, fun i ↦ ?_, Q', hQ', fun p h ↦ ?_⟩
    · rcases eq_or_ne i N with rfl | hi
      · simpa using hz.of_le (by exact_mod_cast le_self_add)
      · simpa [hi] using (hy i).of_le (by exact_mod_cast le_self_add)
    · rw [sum_range_succ, Function.update_self, ← add_assoc,
        sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (mem_range.1 hi).ne]]
      exact hFQ' p h

/-- **Uniform estimates for `C^k` families of approximate solutions.** Under the hypotheses of
`TauCeti.exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse`, there are `C^k` coefficients
`yᵢ` such that, on every compact set `K` of parameters and for `|h| ≤ h₀`, the derivatives in `p`
through order `k` of the residual along the profile `x₀ p + ∑_{i < N} h^(i+1) • yᵢ p` are at most
`C |h|^(N+1)`, with `C` depending only on the order, `K` and `h₀`. To have these bounds together
with the residual identity for the same coefficients, apply
`ContDiff.exists_forall_norm_iteratedFDeriv_le_mul_pow_of_eq_pow_smul` to the output of
`TauCeti.exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse`. -/
theorem exists_forall_norm_iteratedFDeriv_le_mul_pow_of_fderiv_rightInverse {k : ℕ∞} {N : ℕ}
    {F : P × ℝ × E → G} {x₀ : P → E} {R : P → G →L[ℝ] E} (hF : ContDiff ℝ (k + N + 1 : ℕ∞) F)
    (hx₀ : ContDiff ℝ (k + N + 1 : ℕ∞) x₀) (hR : ContDiff ℝ (k + N : ℕ∞) R)
    (h₀ : ∀ p, F (p, 0, x₀ p) = 0)
    (hR' : ∀ p v, fderiv ℝ (fun x ↦ F (p, 0, x)) (x₀ p) (R p v) = v) :
    ∃ y : ℕ → P → E, (∀ i, ContDiff ℝ k (y i)) ∧ ∀ j : ℕ, (j : ℕ∞) ≤ k → ∀ K : Set P,
      IsCompact K → ∀ h₀ : ℝ, ∃ C, ∀ p ∈ K, ∀ h : ℝ, |h| ≤ h₀ →
        ‖iteratedFDeriv ℝ j (fun q ↦ F (q, h, x₀ q + ∑ i ∈ range N, h ^ (i + 1) • y i q)) p‖ ≤
          C * |h| ^ (N + 1) := by
  obtain ⟨y, hy, Q, hQ, hFQ⟩ :=
    exists_contDiff_forall_eq_pow_smul_of_fderiv_rightInverse hF hx₀ hR h₀ hR'
  exact ⟨y, hy, fun j hj K hK h₀ ↦ hQ.exists_forall_norm_iteratedFDeriv_le_mul_pow_of_eq_pow_smul
    (f := fun q ↦ F (q.1, q.2, x₀ q.1 + ∑ i ∈ range N, q.2 ^ (i + 1) • y i q.1)) hFQ hj hK h₀⟩

/-- **Uniform residual of a continuous family of approximate solutions.** Let `F (p, 0, x₀ p) = 0`
for every `p`, and let `R p` be a right inverse of the partial derivative of `x ↦ F (p, 0, x)` at
`x₀ p`. If `F` and `x₀` are `C^(N+1)` and `R` is `C^N`, there are continuous coefficients `yᵢ`
such that, on every compact set `K` of parameters and for `|h| ≤ h₀`, the residual along the
profile `x₀ p + ∑_{i < N} h^(i+1) • yᵢ p` is at most `C |h|^(N+1)`. -/
theorem exists_forall_norm_le_mul_pow_of_fderiv_rightInverse {N : ℕ} {F : P × ℝ × E → G}
    {x₀ : P → E} {R : P → G →L[ℝ] E} (hF : ContDiff ℝ (N + 1) F) (hx₀ : ContDiff ℝ (N + 1) x₀)
    (hR : ContDiff ℝ N R) (h₀ : ∀ p, F (p, 0, x₀ p) = 0)
    (hR' : ∀ p v, fderiv ℝ (fun x ↦ F (p, 0, x)) (x₀ p) (R p v) = v) :
    ∃ y : ℕ → P → E, (∀ i, Continuous (y i)) ∧ ∀ K : Set P, IsCompact K → ∀ h₀ : ℝ, ∃ C,
      ∀ p ∈ K, ∀ h : ℝ, |h| ≤ h₀ →
        ‖F (p, h, x₀ p + ∑ i ∈ range N, h ^ (i + 1) • y i p)‖ ≤ C * |h| ^ (N + 1) := by
  obtain ⟨y, hy, hb⟩ :=
    exists_forall_norm_iteratedFDeriv_le_mul_pow_of_fderiv_rightInverse (k := 0)
    (by simpa using hF) (by simpa using hx₀) (by simpa using hR) h₀ hR'
  refine ⟨y, fun i ↦ (hy i).continuous, fun K hK h₀ ↦ ?_⟩
  simpa using hb 0 le_rfl K hK h₀

end TauCeti
