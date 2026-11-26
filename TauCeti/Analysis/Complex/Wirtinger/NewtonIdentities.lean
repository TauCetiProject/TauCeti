/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pow
import TauCeti.Analysis.Calculus.FDeriv.NewtonIdentities
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# The `\bar∂`-equation of the Newton coefficients of moments

Let `C` be a pseudoholomorphic curve with complex normal line `N`, and let `μ_z` be a smooth
family of measures on the normal fibres `N_z`, such as the normalized curvature slices of a
Seiberg–Witten solution concentrating along `C`. In a local frame its moments and mixed moments

`M_k = ∫ Wᵏ dμ_z`,  `Q_ℓ = ∫ W^ℓ \bar W dμ_z`

are smooth functions on the base, and Newton's recursion
`j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k`, `b₀ = 1`, turns them into the coefficients of the
monic polynomial `P_z(W) = Wᵐ - b₁ W^(m-1) + ⋯ + (-1)ᵐ b_m` whose roots `R_z` are the candidate
positions of the curve's local branches. A real normal Cauchy–Riemann operator has the form
`D_C = \bar∂ + ν W + μ \bar W`, with `(0,1)`-forms `ν` and `μ`, and the moments satisfy it up
to the defects

`E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}`.

This file proves the exact equation satisfied by the Newton coefficients at a point:

`\bar∂ b_j + j ν b_j + μ ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} Q_{k-1} = A_j`,
`A_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} E_k / k`

(`TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`). When the `b_i` with `i < j` are the
elementary symmetric functions of a multiset `R`, the mixed-moment term is rewritten through the
roots: with `e_{j-1}(R ∖ V)` the elementary symmetric functions of `R` with one copy of `V`
removed,

`\bar∂ b_j = -j ν b_j - μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V) + R_j`,

where the remainder `R_j` is `A_j` minus `μ` times the Newton combination of the mixed-moment
errors `Q_ℓ - ∑_{V ∈ R} V^ℓ \bar V`
(`TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton`). Its pointwise norm is bounded by
those of the `E_k` and of the mixed-moment errors
(`TauCeti.norm_conjWirtingerDeriv_add_esymm_erase_le_of_newton`). When the `E_k` and the
mixed-moment errors are small and the `b_{j-k}` are bounded, `b_j` thus nearly solves the
equation of the elementary symmetric functions of points moving by `D_C`.

Under a change of frame `W ↦ g W` the moments become `gᵏ M_k` and `g^ℓ \bar g Q_ℓ`, the Newton
coefficients become `gʲ b_j` (`TauCeti.newton_eq_pow_mul`), and the coefficients of `D_C` become
`ν - g⁻¹ \bar∂g` and `(g / \bar g) μ`. The defect `E_k` is then multiplied by `gᵏ`
(`TauCeti.conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul`), and the combination `A_j` by `gʲ`
(`TauCeti.sum_smul_conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul`), so the equation above is
frame-independent. In the form through the roots, the roots become `g R`, and the left side
`\bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)` is multiplied by `gʲ`
(`TauCeti.conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul`): the remainder `R_j`
transforms like `b_j`. For a constant frame this holds without differentiability
(`TauCeti.conjWirtingerDeriv_const_pow_mul_add_add_esymm_erase_eq_pow_smul`); a nonzero real
constant `a`, the passage from rescaled to physical coefficients `aʲ b_j`, leaves `ν` and `μ`
unchanged.

Here `\bar∂` is `TauCeti.conjWirtingerDeriv`, the base is any complex normed space, and the
`(0,1)`-forms `ν`, `μ` and `E_k` are complex-antilinear functionals.

## Main results

* `TauCeti.conjWirtingerDeriv_eq_sum_of_newton`: `\bar∂ b_j = ∑ (-1)^(k-1) (b_{j-k} / k) \bar∂ M_k`.
* `TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`: the equation of the Newton coefficients.
* `TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton`: its form through the roots.
* `TauCeti.norm_conjWirtingerDeriv_add_esymm_erase_le_of_newton`: the bound on its remainder.
* `TauCeti.conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul`: the frame law of the defects.
* `TauCeti.sum_smul_conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul`: the frame law of their
  Newton combination `A_j`.
* `TauCeti.conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul`: the frame law of the
  equation through the roots.
* `TauCeti.conjWirtingerDeriv_const_pow_mul_add_add_esymm_erase_eq_pow_smul`: the same for a
  constant frame, without differentiability.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Finset Filter Topology ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {b M : ℕ → V → ℂ} {x : V}
  {j : ℕ}

/-- **The `\bar∂`-derivative of the Newton coefficients.** If the `M_k` are real differentiable
at `x` for `1 ≤ k ≤ j`, and near `x` the `b_i` satisfy `b₀ = 1` and Newton's recursion
`i b_i = ∑_{k=1}^{i} (-1)^(k-1) b_{i-k} M_k` for `i ≤ j`, then
`\bar∂ b_j(x) = ∑_{k=1}^{j} (-1)^(k-1) (b_{j-k}(x) / k) \bar∂ M_k(x)`. -/
theorem conjWirtingerDeriv_eq_sum_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : ℂ) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt ℝ (M k) x) :
    conjWirtingerDeriv (b j) x =
      ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k) x / k) • conjWirtingerDeriv (M k) x :=
  conjWirtingerDeriv_eq_sum_smul (hasFDerivAt_of_newton hb₀ hb hM).fderiv

/-- **The equation of the Newton coefficients.** Let `ν, μ` be `(0,1)`-forms at `x` and `Q_ℓ`
numbers, standing for the coefficients of `D_C = \bar∂ + ν W + μ \bar W` and the mixed moments.
Under the hypotheses of `TauCeti.conjWirtingerDeriv_eq_sum_of_newton`,

`\bar∂ b_j + j ν b_j + μ ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} Q_{k-1} = A_j`,

where `A_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} E_k / k` and
`E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}`. -/
theorem conjWirtingerDeriv_add_eq_sum_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : ℂ) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt ℝ (M k) x) (ν μ : V →L⋆[ℂ] ℂ) (Q : ℕ → ℂ) :
    conjWirtingerDeriv (b j) x + (j * b j x) • ν +
        (∑ k ∈ Icc 1 j, (-1) ^ (k - 1) * b (j - k) x * Q (k - 1)) • μ =
      ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k) x / k) •
        (conjWirtingerDeriv (M k) x + (k * M k x) • ν + (k * Q (k - 1)) • μ) := by
  rw [conjWirtingerDeriv_eq_sum_of_newton hb₀ hb hM, (hb j le_rfl).self_of_nhds]
  rw [Finset.sum_smul (M := V →L⋆[ℂ] ℂ), Finset.sum_smul (M := V →L⋆[ℂ] ℂ),
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by simp only [mem_Icc] at hk; omega)
  match_scalars <;> field_simp

/-- **The equation of the Newton coefficients through the roots.** If moreover `b_i(x)` is the
`i`-th elementary symmetric function of a multiset `R` for `i < j`, with `0 < j`, then

`\bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V) = A_j - μ r_j`,
`r_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} q_{k-1}`,

where `A_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} E_k / k`, `E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}`,
and `q_ℓ = Q_ℓ - ∑_{V ∈ R} V^ℓ \bar V` are the mixed-moment errors. -/
theorem conjWirtingerDeriv_add_esymm_erase_eq_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : ℂ) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt ℝ (M k) x) (ν μ : V →L⋆[ℂ] ℂ) (Q : ℕ → ℂ)
    {R : Multiset ℂ} (hR : ∀ i < j, b i x = R.esymm i) (hj : 0 < j) :
    conjWirtingerDeriv (b j) x + (j * b j x) • ν +
        (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ =
      ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k) x / k) •
          (conjWirtingerDeriv (M k) x + (k * M k x) • ν + (k * Q (k - 1)) • μ) -
        (∑ k ∈ Icc 1 j, (-1) ^ (k - 1) * b (j - k) x *
          (Q (k - 1) - (R.map fun w ↦ w ^ (k - 1) * conj w).sum)) • μ := by
  -- The root term is the Newton combination of the weighted power sums `∑_{V ∈ R} V^ℓ \bar V`.
  have hroot : (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum =
      ∑ k ∈ Icc 1 j, (-1) ^ (k - 1) * b (j - k) x *
        (R.map fun w ↦ w ^ (k - 1) * conj w).sum := by
    rw [R.sum_map_mul_esymm_erase, Nat.sub_add_cancel hj, ← Ico_add_one_right_eq_Icc,
      sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [mem_range] at hk
    rw [hR _ (by omega), Nat.add_sub_cancel_left, Nat.sub_sub]
  rw [← conjWirtingerDeriv_add_eq_sum_of_newton hb₀ hb hM, hroot, add_sub_assoc, ← sub_smul,
    ← sum_sub_distrib]
  simp only [mul_sub, sub_sub_cancel]

/-- **The remainder bound.** Under the hypotheses of
`TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton`, the remainder
`R_j = \bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)` satisfies

`‖R_j‖ ≤ ∑_{k=1}^{j} (|b_{j-k}| / k) ‖E_k‖ + ‖μ‖ ∑_{k=1}^{j} |b_{j-k}| |q_{k-1}|`,

with `E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}` and `q_ℓ = Q_ℓ - ∑_{V ∈ R} V^ℓ \bar V`. -/
theorem norm_conjWirtingerDeriv_add_esymm_erase_le_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : ℂ) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt ℝ (M k) x) (ν μ : V →L⋆[ℂ] ℂ) (Q : ℕ → ℂ)
    {R : Multiset ℂ} (hR : ∀ i < j, b i x = R.esymm i) (hj : 0 < j) :
    ‖conjWirtingerDeriv (b j) x + (j * b j x) • ν +
        (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ‖ ≤
      ∑ k ∈ Icc 1 j, ‖b (j - k) x‖ / k *
          ‖conjWirtingerDeriv (M k) x + (k * M k x) • ν + (k * Q (k - 1)) • μ‖ +
        ‖μ‖ * ∑ k ∈ Icc 1 j, ‖b (j - k) x‖ *
          ‖Q (k - 1) - (R.map fun w ↦ w ^ (k - 1) * conj w).sum‖ := by
  rw [conjWirtingerDeriv_add_esymm_erase_eq_of_newton hb₀ hb hM ν μ Q hR hj]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans_eq ?_) ?_)
  · refine sum_congr rfl fun k _ ↦ ?_
    rw [norm_smul]
    simp
  · rw [norm_smul, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans_eq ?_) (norm_nonneg _)
    refine sum_congr rfl fun k _ ↦ ?_
    simp

/-- **The frame law of the moment defects.** Under a change of frame `W ↦ g W` of the normal
line, with `g(x) ≠ 0`, the moment `M` of order `k` becomes `gᵏ M`, the mixed moment `Q` of order
`k - 1` becomes `g^(k-1) \bar g Q`, and the coefficients of `D_C = \bar∂ + ν W + μ \bar W` become
`ν - g⁻¹ \bar∂g` and `(g / \bar g) μ`. The defect `E = \bar∂ M + k ν M + k μ Q` is then
multiplied by `gᵏ`. -/
theorem conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul {g : V → ℂ} {M : V → ℂ}
    (hg : DifferentiableAt ℝ g x) (hgx : g x ≠ 0) (hM : DifferentiableAt ℝ M x) (k : ℕ)
    (ν μ : V →L⋆[ℂ] ℂ) (Q : ℂ) :
    conjWirtingerDeriv (fun y ↦ g y ^ k * M y) x +
        (k * (g x ^ k * M x)) • (ν - (g x)⁻¹ • conjWirtingerDeriv g x) +
        (k * (g x ^ (k - 1) * conj (g x) * Q)) • ((g x / conj (g x)) • μ) =
      g x ^ k • (conjWirtingerDeriv M x + (k * M x) • ν + (k * Q) • μ) := by
  have hgx' : conj (g x) ≠ 0 := (map_ne_zero _).2 hgx
  rw [conjWirtingerDeriv_fun_mul (f := fun y ↦ g y ^ k) (hg.pow k) hM,
    conjWirtingerDeriv_fun_pow hg]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · module
  have hpow : g x ^ k = g x ^ (k - 1) * g x := by rw [← pow_succ, Nat.sub_add_cancel hk]
  simp only [smul_add, smul_sub, smul_smul]
  rw [hpow]
  field_simp
  module

/-- **The frame law of the Newton combination of the defects.** Under a change of frame
`W ↦ g W` as in `TauCeti.conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul`, with the coefficients
`b_i` becoming `gⁱ b_i`, the combination
`A_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} E_k / k` of the moment defects `E_k` is multiplied by
`gʲ`. -/
theorem sum_smul_conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul {g : V → ℂ}
    (hg : DifferentiableAt ℝ g x) (hgx : g x ≠ 0) (hM : ∀ k ∈ Icc 1 j, DifferentiableAt ℝ (M k) x)
    (ν μ : V →L⋆[ℂ] ℂ) (Q : ℕ → ℂ) :
    ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * (g x ^ (j - k) * b (j - k) x) / k) •
        (conjWirtingerDeriv (fun y ↦ g y ^ k * M k y) x +
          (k * (g x ^ k * M k x)) • (ν - (g x)⁻¹ • conjWirtingerDeriv g x) +
          (k * (g x ^ (k - 1) * conj (g x) * Q (k - 1))) • ((g x / conj (g x)) • μ)) =
      g x ^ j • ∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k) x / k) •
        (conjWirtingerDeriv (M k) x + (k * M k x) • ν + (k * Q (k - 1)) • μ) := by
  rw [smul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [conjWirtingerDeriv_pow_mul_add_add_eq_pow_smul hg hgx (hM k hk), smul_smul, smul_smul,
    ← pow_sub_mul_pow (g x) (mem_Icc.1 hk).2]
  congr 1
  ring

/-- **The frame law of the equation of the Newton coefficients through the roots.** Under a
change of frame `W ↦ g W` of the normal line, with `g(x) ≠ 0`, a coefficient `b_j` becomes
`gʲ b_j`, the multiset `R` of roots becomes `g R`, and the coefficients of
`D_C = \bar∂ + ν W + μ \bar W` become `ν - g⁻¹ \bar∂g` and `(g / \bar g) μ`. Then the left side

`\bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

of the equation of `TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton` is multiplied by
`gʲ`, for `0 < j`. So the equation is frame-independent, and its remainder `R_j` transforms like
the coefficient `b_j`. -/
theorem conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul {g b : V → ℂ}
    (hg : DifferentiableAt ℝ g x) (hgx : g x ≠ 0) (hb : DifferentiableAt ℝ b x) (hj : 0 < j)
    (ν μ : V →L⋆[ℂ] ℂ) (R : Multiset ℂ) :
    conjWirtingerDeriv (fun y ↦ g y ^ j * b y) x +
        (j * (g x ^ j * b x)) • (ν - (g x)⁻¹ • conjWirtingerDeriv g x) +
        ((R.map (g x * ·)).map fun w ↦ conj w * ((R.map (g x * ·)).erase w).esymm (j - 1)).sum •
          ((g x / conj (g x)) • μ) =
      g x ^ j • (conjWirtingerDeriv b x + (j * b x) • ν +
        (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ) := by
  have hgx' : conj (g x) ≠ 0 := (map_ne_zero _).2 hgx
  rw [R.sum_map_mul_esymm_erase_map_mul (fun a ↦ map_mul (starRingEnd ℂ) (g x) a),
    conjWirtingerDeriv_fun_mul (f := fun y ↦ g y ^ j) (hg.pow j) hb,
    conjWirtingerDeriv_fun_pow hg]
  simp only [smul_add, smul_sub, smul_smul]
  rw [← pow_sub_one_mul hj.ne' (g x)]
  field_simp
  module

/-- **The frame law of the equation through the roots for a constant frame.** For a constant
frame `W ↦ c W`, a coefficient `b_j` becomes `cʲ b_j`, the roots `R` become `c R`, `ν` is
unchanged and `μ` becomes `(c / \bar c) μ`; the left side

`\bar∂ b_j + j ν b_j + μ ∑_{V ∈ R} \bar V e_{j-1}(R ∖ V)`

of the equation of `TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton` is multiplied by
`cʲ`, for `0 < j`. Unlike `TauCeti.conjWirtingerDeriv_pow_mul_add_add_esymm_erase_eq_pow_smul`,
this needs no differentiability of `b` and allows `c = 0`. For a nonzero real `c = a`,
`c / \bar c = 1` and `μ` is unchanged:
this is the passage from rescaled coefficients `b_j` to physical coefficients `aʲ b_j`. -/
theorem conjWirtingerDeriv_const_pow_mul_add_add_esymm_erase_eq_pow_smul {b : V → ℂ} (c : ℂ)
    (hj : 0 < j) (ν μ : V →L⋆[ℂ] ℂ) (R : Multiset ℂ) :
    conjWirtingerDeriv (fun y ↦ c ^ j * b y) x + (j * (c ^ j * b x)) • ν +
        ((R.map (c * ·)).map fun w ↦ conj w * ((R.map (c * ·)).erase w).esymm (j - 1)).sum •
          ((c / conj c) • μ) =
      c ^ j • (conjWirtingerDeriv b x + (j * b x) • ν +
        (R.map fun w ↦ conj w * (R.erase w).esymm (j - 1)).sum • μ) := by
  have hb : (fun y ↦ c ^ j * b y) = c ^ j • b := funext fun y ↦ by rw [Pi.smul_apply, smul_eq_mul]
  rw [R.sum_map_mul_esymm_erase_map_mul (fun a ↦ map_mul (starRingEnd ℂ) c a), hb,
    conjWirtingerDeriv_const_smul]
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_pow hj.ne', zero_mul, zero_smul]
    module
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  simp only [smul_add, smul_smul]
  rw [← pow_sub_one_mul hj.ne' c]
  field_simp

end TauCeti
