/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ParameterDerivative
import TauCeti.Analysis.Fredholm.OrthogonalSplitting.IteratedDeriv
import TauCeti.Data.ENNReal.Mul
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Weighted estimates for the parameter derivatives of every order of the vortex splitting

At a smooth plane vortex `x` with `L∞` class `a`, the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the
gauge-fixed operator is Fredholm and onto, with kernel projection `π` along the `L²`-orthogonal
complement and right inverse `Q` with values in that complement. Along a curve of coefficients
`t ↦ a(t)`, such as the vortices of a curve of divisors, write `aⱼ`, `Qⱼ` and `πⱼ` for the `j`-th
derivatives of `a`, `Q` and `π` at `t₀`. Gluing plane vortices into solutions of the
four-dimensional equations uses these operators and their parameter derivatives of every finite
order on errors that decay exponentially away from the vortex cores, measured with the weight
`exp(c ρ)`, `ρ(z) = √(1 + |z|²)`, `|c| < 1/2`. The first and second derivatives are treated in
`TauCeti.Analysis.PDE.Vortex.ParameterDerivative`; this file proves the weighted `L²` estimates
for the derivatives of every order. If `‖aⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ n`, then

`‖exp(c ρ) Qₙ f‖₂ ≤ K Mⁿ ‖exp(c ρ) f‖₂`,  `‖exp(c ρ) πₙ e‖₂ ≤ K Mⁿ ‖exp(c ρ) e‖₂`

(`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le`,
`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le`),
with `K` depending only on the degree `m`, a radius `R₀` containing the zeros, `c` and `n`. They
hold uniformly over a window of divisors, collisions included. The normalization `‖aⱼ‖∞ ≤ Mʲ` is
the one preserved by reparametrizing the curve; bounds `Mⱼ` on the derivatives of the coefficient
give it with `M = maxⱼ Mⱼ^(1/j)`.

The proof is an induction on `n`, at the two rates `c` and `-c` together. The realization is
affine in the coefficient, so its `j`-th derivative is the zeroth-order operator `Z(aⱼ, ·)` for
`j ≥ 1`, which costs at most `‖Z‖ ‖aⱼ‖∞` in every weighted norm. Differentiating the identities of
the orthogonal splitting `n` times
(`TauCeti.Analysis.Fredholm.OrthogonalSplitting.IteratedDeriv`) expresses `Qₙ f` and `πₙ e`
through derivatives of lower order:

* the components orthogonal to the kernel are
  `-Q (∑_{i < n} (n choose i) Z(a_(n-i), Qᵢ f))` and `-Q (∑_{i < n} (n choose i) Z(a_(n-i), πᵢ e))`;
* the kernel components are determined by the pairings with kernel elements `k`,
  `⟪Qₙ f, k⟫ = -∑_{i < n} (n choose i) ⟪Qᵢ f, π_(n-i) k⟫` and `⟪πₙ e, k⟫ = ⟪e, πₙ k⟫`;
* on kernel elements, `πₙ k` itself is expressed through derivatives of lower order: its kernel
  component is `-∑_{i < n-1} (n choose i + 1) π_(i+1) (π_(n-1-i) k)`, from `π ∘ π = π`.

Moving the weight across the pairings at the rates `c` and `-c`
(`TauCeti.Vortex.eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner`), as in
the first- and second-order estimates, closes the induction.

## Main results

* `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le`:
  the weighted estimate for the derivatives of every order of the orthogonal right inverses.
* `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le`:
  the same for the orthogonal kernel projections.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap BesselPotentialSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff BesselPotentialSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The weighted norm of the derivatives of the realization -/

/-- **The complement component.** If `Q` costs at most `q` in the weighted norm at the rate `c`,
`‖bⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ N` and `‖exp(c ρ) yᵢ‖₂ ≤ Gᵢ Mⁱ N₀` for `i < N`, then

`‖exp(c ρ) Q (∑_{i<N} C(N,i) Z(b_(N-i), yᵢ))‖₂ ≤ (∑_{i<N} C(N,i) q ‖Z‖ Gᵢ) Mᴺ N₀`,

where `C(N,i)` is the binomial coefficient. -/
private theorem eLpNorm_exp_mul_smul_sobolevFieldValues_sum_holderL_le {c : ℝ} {q : ℝ≥0}
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)}
    (hQ : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q g) z) 2 μ⊤ ≤
      q * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    {N : ℕ} {b : ℕ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {M : ℝ≥0}
    (hb : ∀ j ∈ Finset.Icc 1 N, ‖b j‖₊ ≤ M ^ j)
    {y : ℕ → Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} {G : ℕ → ℝ≥0} {N₀ : ℝ≥0∞}
    (hy : ∀ i < N, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (y i) z) 2
      μ⊤ ≤ (G i * M ^ i : ℝ≥0) * N₀) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues (Q (∑ i ∈ Finset.range N,
      N.choose i • gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (b (N - i))
        (sobolevFieldValues (y i)))) z) 2 μ⊤ ≤
      ((∑ i ∈ Finset.range N, N.choose i * (q * ‖gaugeFixedZerothOrder‖₊ * G i)) * M ^ N : ℝ≥0) *
        N₀ := by
  simp only [map_sum, map_nsmul]
  refine (Lp.eLpNorm_smul_sum_nsmul_le one_le_two _ _ _ _).trans
    (ENNReal.sum_natCast_mul_le_coe_mul _ (N - ·) (fun i ↦ i) (fun i hi ↦ ?_) fun i hi ↦ ?_)
  · exact Nat.sub_add_cancel (Finset.mem_range.1 hi).le
  have hi' := Finset.mem_range.1 hi
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_holderL_le hQ _ (hy i hi')).trans ?_
  gcongr
  exact hb _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)

/-! ### The induction step -/

/-- The derivatives `T_(n-i)`, `i < n`, of the realizations along `a` are the zeroth-order operators
`Z(a_(n-i), ·)`, inside the Leibniz sums of the orthogonal splitting. -/
private theorem sum_choose_smul_iteratedDeriv_sobolevGaugeFixedOperator_apply
    {a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {t₀ : ℝ} {n : ℕ} (ha : ContDiffAt ℝ n a t₀)
    (y : ℕ → Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∑ i ∈ Finset.range n, n.choose i •
        iteratedDeriv (n - i) (fun t ↦ sobolevGaugeFixedOperator (a t)) t₀ (y i) =
      ∑ i ∈ Finset.range n, n.choose i • gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
        (iteratedDeriv (n - i) a t₀) (sobolevFieldValues (y i)) :=
  Finset.sum_congr rfl fun i hi ↦ by
    rw [iteratedDeriv_sobolevGaugeFixedOperator_comp_apply (ha.of_le (by norm_cast; omega))
      (by have := Finset.mem_range.1 hi; omega)]

/-- **The derivatives of the kernel projections on the kernel.** At a parameter `t₀` where the
realization `L_(a t₀)` is Fredholm and onto, with `‖aⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ N + 1`, suppose that
`Q₀` costs at most `q` in the weighted norm at the rate `s`, and that the derivatives `πⱼ` of order
`j ≤ N` cost at most `Kⱼ Mʲ`. Then on the kernel of `L_(a t₀)` the derivative of order `N + 1`
costs at most a constant, depending only on `q` and the `Kⱼ`, times `M^(N+1)`: its kernel
component is `-∑_{i<N} C(N+1,i+1) π_(i+1) (π_(N-i) k)` and its complement component is
`-Q₀ (∑_{i ≤ N} C(N+1,i) Z(a_(N+1-i), πᵢ k))`. -/
private theorem eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le_of_mem_ker
    {a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {t₀ : ℝ}
    (hT : (sobolevGaugeFixedOperator (a t₀)).IsFredholm)
    (hsurj : Function.Surjective (sobolevGaugeFixedOperator (a t₀))) {N : ℕ}
    (ha : ContDiffAt ℝ (N + 1) a t₀) {M : ℝ≥0}
    (hb : ∀ j ∈ Finset.Icc 1 (N + 1), ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) {s : ℝ} {q : ℝ≥0}
    (hq : ∀ g, eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a t₀)) g) z) 2 μ⊤ ≤
        q * eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    {K : ℕ → ℝ≥0} (hK : ∀ j < N + 1, ∀ e, eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ e) z) 2 μ⊤ ≤
          (K j * M ^ j : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) •
            sobolevFieldValues e z) 2 μ⊤)
    {k : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} (hk : k ∈ (sobolevGaugeFixedOperator (a t₀)).ker) :
    eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (iteratedDeriv (N + 1) (fun t ↦ orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ k) z) 2 μ⊤ ≤
      ((∑ i ∈ Finset.range N, (N + 1).choose (i + 1) * (K (i + 1) * K (N - i)) +
        ∑ i ∈ Finset.range (N + 1), (N + 1).choose i * (q * ‖gaugeFixedZerothOrder‖₊ * K i)) *
          M ^ (N + 1) : ℝ≥0) *
        eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤ := by
  have hd : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (fun t ↦ sobolevGaugeFixedOperator (a t))
      t₀ := by
    exact_mod_cast contDiff_sobolevGaugeFixedOperator.contDiffAt.comp t₀ ha
  set P := fun j ↦ iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a t))) t₀
  set N₀ := eLpNorm (fun z ↦ Real.exp (s * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤
  -- Split `P (N + 1) k` into its kernel and complement components.
  have h₁ := hT.orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_of_mem_ker
    sobolevFieldValues_injective hsurj hd hk
  have h₂ := hT.sub_orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_apply
    sobolevFieldValues_injective hsurj hd k
  rw [sum_choose_smul_iteratedDeriv_sobolevGaugeFixedOperator_apply (by exact_mod_cast ha)
    (fun i ↦ P i k)] at h₂
  have h₃ := sub_eq_iff_eq_add'.1 h₂
  rw [h₁] at h₃
  rw [h₃, map_add, map_neg, map_neg]
  refine (Lp.eLpNorm_smul_add_le one_le_two _ _ _).trans ?_
  rw [Lp.eLpNorm_smul_neg, Lp.eLpNorm_smul_neg, add_mul, ENNReal.coe_add, add_mul]
  refine add_le_add ?_ (eLpNorm_exp_mul_smul_sobolevFieldValues_sum_holderL_le hq hb
    fun i hi ↦ hK i (by omega) k)
  -- The kernel component, through the derivatives of lower order.
  simp only [map_sum, map_nsmul]
  refine (Lp.eLpNorm_smul_sum_nsmul_le one_le_two _ _ _ _).trans
    (ENNReal.sum_natCast_mul_le_coe_mul _ (· + 1) (N - ·) (fun i hi ↦ ?_) fun i hi ↦ ?_)
  · have := Finset.mem_range.1 hi
    omega
  have hi' := Finset.mem_range.1 hi
  exact (hK _ (by omega) _).trans (ENNReal.coe_mul_le_coe_mul (hK _ (by omega) _))

/-- **The derivatives of the right inverses.** At a parameter `t₀` where the realization
`L_(a t₀)` is Fredholm and onto, with `‖aⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ N`, `N ≠ 0`, suppose that the
weight costs at most `kc`, `kn` on the kernel at the rates `c`, `-c` and at most `qc` on `Q₀` at
the rate `c`, that the derivatives `Qⱼ`, `j < N`, cost at most `Kⱼ Mʲ` at the rate `c`, and that the
derivatives `πⱼ`, `1 ≤ j ≤ N`, cost at most `B Mʲ` on the kernel at the rate `-c`. Then `Q_N` costs
at most a constant, depending only on these, times `Mᴺ`. -/
private theorem eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le_of_le
    {a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {t₀ : ℝ}
    (hT : (sobolevGaugeFixedOperator (a t₀)).IsFredholm)
    (hsurj : Function.Surjective (sobolevGaugeFixedOperator (a t₀))) {N : ℕ}
    (ha : ContDiffAt ℝ N a t₀) (hN : N ≠ 0) {M : ℝ≥0}
    (hb : ∀ j ∈ Finset.Icc 1 N, ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) {c : ℝ} {kc kn qc B : ℝ≥0}
    (hkc : ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker, eLpNorm (fun z ↦
      Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤ ≤
        kc * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hkn : ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker, eLpNorm (fun z ↦
      Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤ ≤
        kn * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hqc : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a t₀)) g) z) 2 μ⊤ ≤
        qc * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    {K : ℕ → ℝ≥0} (hK : ∀ j < N, ∀ f, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (iteratedDeriv j (fun t ↦ orthogonalRightInverse sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ f) z) 2 μ⊤ ≤
          (K j * M ^ j : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤)
    (hB : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker,
      eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
        (iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
          (sobolevGaugeFixedOperator (a t))) t₀ k) z) 2 μ⊤ ≤
        (B * M ^ j : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
          sobolevFieldValues k z) 2 μ⊤)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (iteratedDeriv N (fun t ↦ orthogonalRightInverse sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ f) z) 2 μ⊤ ≤
      ((kc * ∑ i ∈ Finset.range N, N.choose i * (B * kn * K i) +
        ∑ i ∈ Finset.range N, N.choose i * (qc * ‖gaugeFixedZerothOrder‖₊ * K i)) * M ^ N : ℝ≥0) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤ := by
  have hd : ContDiffAt ℝ N (fun t ↦ sobolevGaugeFixedOperator (a t)) t₀ :=
    contDiff_sobolevGaugeFixedOperator.contDiffAt.comp t₀ ha
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection sobolevFieldValues_injective
    (sobolevGaugeFixedOperator (a t₀))
  set Q := fun j ↦ iteratedDeriv j (fun t ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a t))) t₀
  set P := fun j ↦ iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a t))) t₀
  set N₀ := eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤
  -- The kernel component, through `⟪Q_N f, k⟫ = -∑_{i<N} C(N,i) ⟪Qᵢ f, π_(N-i) k⟫`.
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner hπ hkc
    (s := Finset.range N) (q := fun i ↦ N.choose i * (B * M ^ (N - i) * kn))
    (e := fun k i ↦ (N.choose i : ℝ) • sobolevFieldValues (P (N - i) k))
    (A := fun i ↦ sobolevFieldValues (Q i f)) (fun k hk i hi ↦ ?_) (Q N f)
    fun k hk ↦ ?_).trans ?_
  · have hi' := Finset.mem_range.1 hi
    rw [Lp.eLpNorm_smul_const_smul, Real.eNorm_natCast]
    calc _ ≤ (N.choose i : ℝ≥0∞) * ((B * M ^ (N - i) : ℝ≥0) *
          (kn * eLpNorm (sobolevFieldValues k) 2 μ⊤)) := by
          gcongr
          exact (hB _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) k hk).trans
            (by gcongr; exact hkn k hk)
      _ = _ := by
          push_cast
          ring
  · rw [hT.inner_iteratedDeriv_orthogonalRightInverse_apply sobolevFieldValues_injective hsurj hd f
      hk, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [nsmul_eq_mul, real_inner_smul_left, real_inner_comm]
  -- The complement component, through `-Q₀ (∑_{i<N} C(N,i) Z(a_(N-i), Qᵢ f))`.
  rw [hT.sub_orthogonalKerProjection_iteratedDeriv_orthogonalRightInverse_apply
      sobolevFieldValues_injective hsurj hd hN f,
    sum_choose_smul_iteratedDeriv_sobolevGaugeFixedOperator_apply ha, map_neg,
    Lp.eLpNorm_smul_neg, add_mul, ENNReal.coe_add, add_mul]
  refine add_le_add ?_ (eLpNorm_exp_mul_smul_sobolevFieldValues_sum_holderL_le hqc hb
    fun i hi ↦ hK i hi f)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  calc _ ≤ (kc : ℝ≥0∞) * ((N.choose i * (B * M ^ (N - i) * kn) : ℝ≥0) *
        ((K i * M ^ i : ℝ≥0) * N₀)) := by
        gcongr
        exact hK i hi' f
    _ = _ := by
        rw [← pow_sub_mul_pow M hi'.le]
        push_cast
        ring

/-- **The derivatives of the kernel projections.** In the setting of
`eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le_of_le`, suppose that the derivatives
`πⱼ`, `j < N`, cost at most `Kⱼ Mʲ` at the rate `c`, and that `π_N` costs at most `B Mᴺ` on the
kernel at the rate `-c`. Then `π_N` costs at most a constant, depending only on these, times
`Mᴺ`. -/
private theorem eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le_of_le
    {a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {t₀ : ℝ}
    (hT : (sobolevGaugeFixedOperator (a t₀)).IsFredholm)
    (hsurj : Function.Surjective (sobolevGaugeFixedOperator (a t₀))) {N : ℕ}
    (ha : ContDiffAt ℝ N a t₀) {M : ℝ≥0}
    (hb : ∀ j ∈ Finset.Icc 1 N, ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) {c : ℝ} {kc kn qc B : ℝ≥0}
    (hkc : ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker, eLpNorm (fun z ↦
      Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤ ≤
        kc * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hkn : ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker, eLpNorm (fun z ↦
      Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues k z) 2 μ⊤ ≤
        kn * eLpNorm (sobolevFieldValues k) 2 μ⊤)
    (hqc : ∀ g, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a t₀)) g) z) 2 μ⊤ ≤
        qc * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 μ⊤)
    {K : ℕ → ℝ≥0} (hK : ∀ j < N, ∀ e, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      sobolevFieldValues (iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ e) z) 2 μ⊤ ≤
          (K j * M ^ j : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            sobolevFieldValues e z) 2 μ⊤)
    (hB : ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker,
      eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
        (iteratedDeriv N (fun t ↦ orthogonalKerProjection sobolevFieldValues
          (sobolevGaugeFixedOperator (a t))) t₀ k) z) 2 μ⊤ ≤
        (B * M ^ N : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
          sobolevFieldValues k z) 2 μ⊤)
    (e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (iteratedDeriv N (fun t ↦ orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ e) z) 2 μ⊤ ≤
      ((kc * (B * kn) +
        ∑ i ∈ Finset.range N, N.choose i * (qc * ‖gaugeFixedZerothOrder‖₊ * K i)) * M ^ N : ℝ≥0) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤ := by
  have hd : ContDiffAt ℝ N (fun t ↦ sobolevGaugeFixedOperator (a t)) t₀ :=
    contDiff_sobolevGaugeFixedOperator.contDiffAt.comp t₀ ha
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection sobolevFieldValues_injective
    (sobolevGaugeFixedOperator (a t₀))
  set P := fun j ↦ iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a t))) t₀
  -- The kernel component, through the symmetry `⟪π_N e, k⟫ = ⟪e, π_N k⟫`.
  refine (eLpNorm_exp_mul_smul_sobolevFieldValues_le_of_abs_inner_le_sum_abs_inner hπ hkc
    (s := Finset.univ) (q := fun _ : Unit ↦ B * M ^ N * kn)
    (e := fun k _ ↦ sobolevFieldValues (P N k)) (A := fun _ ↦ sobolevFieldValues e)
    (fun k hk _ _ ↦ ?_) (P N e) fun k _ ↦ ?_).trans ?_
  · calc _ ≤ (B * M ^ N : ℝ≥0) * (kn * eLpNorm (sobolevFieldValues k) 2 μ⊤) :=
          (hB k hk).trans (by gcongr; exact hkn k hk)
      _ = _ := by
          push_cast
          ring
  · rw [hT.inner_iteratedDeriv_orthogonalKerProjection_apply_left_eq_right
      sobolevFieldValues_injective hsurj hd e k, real_inner_comm]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact le_rfl
  -- The complement component, through `-Q₀ (∑_{i<N} C(N,i) Z(a_(N-i), πᵢ e))`.
  rw [hT.sub_orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_apply
      sobolevFieldValues_injective hsurj hd e,
    sum_choose_smul_iteratedDeriv_sobolevGaugeFixedOperator_apply ha, map_neg,
    Lp.eLpNorm_smul_neg, add_mul, ENNReal.coe_add, add_mul]
  refine add_le_add (le_of_eq ?_) (eLpNorm_exp_mul_smul_sobolevFieldValues_sum_holderL_le hqc hb
    fun i hi ↦ hK i hi e)
  simp only [Finset.univ_unique, Finset.sum_singleton, ENNReal.coe_mul, ENNReal.coe_pow]
  ring

/-! ### The induction on the order -/

/-- The weighted estimates of order `n` at the rate `c`, with constant `K`, for the derivatives
`Qₙ` and `πₙ` of the orthogonal right inverses and kernel projections along every curve of
coefficients through a vortex of the window, in the volume restricted to the plane. -/
private def IsIteratedDerivBound (m : ℕ) (R₀ c : ℝ) (n : ℕ) (K : ℝ≥0) : Prop :=
  ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
    (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
    (∀ z, equation x z = 0) →
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
    IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
    ∀ (a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (t₀ : ℝ), a t₀ =ᵐ[μ⊤] x →
    ContDiffAt ℝ n a t₀ → ∀ M : ℝ≥0, (∀ j ∈ Finset.Icc 1 n, ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) →
    (∀ f, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (iteratedDeriv n (fun t ↦ orthogonalRightInverse sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ f) z) 2 μ⊤ ≤
      (K * M ^ n : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ⊤) ∧
    ∀ e, eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
      (iteratedDeriv n (fun t ↦ orthogonalKerProjection sobolevFieldValues
        (sobolevGaugeFixedOperator (a t))) t₀ e) z) 2 μ⊤ ≤
      (K * M ^ n : ℝ≥0) *
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 μ⊤

/-- The estimates of order `0` are those of the right inverse and of the kernel projection. -/
private theorem exists_isIteratedDerivBound_zero (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K, IsIteratedDerivBound m R₀ c 0 K := by
  obtain ⟨_, _, qc, _, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  obtain ⟨kπ, hkπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ hc
  refine ⟨qc + kπ, fun x D hx hbound hsol hframe hD hD₀ a t₀ hax _ M _ ↦ ⟨fun f ↦ ?_, fun e ↦ ?_⟩⟩
  · simp only [iteratedDeriv_zero, pow_zero, mul_one]
    exact ((hest x D hx hbound hsol hframe hD hD₀ (a t₀) hax).2.2.1 f).trans
      (by gcongr; exact le_self_add)
  · simp only [iteratedDeriv_zero, pow_zero, mul_one]
    rw [eLpNorm_restrict_coe_opens_top, eLpNorm_restrict_coe_opens_top]
    exact (hkπ x D hx hbound hsol hframe hD hD₀ (a t₀) hax e).trans (by gcongr; exact le_add_self)

/-- **The induction step.** The estimates of order `N + 1` at the rate `c` follow from those of
lower order at the rates `c` and `-c`. -/
private theorem exists_isIteratedDerivBound_succ (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2)
    {N : ℕ} {K : ℕ → ℝ → ℝ≥0}
    (hK : ∀ j < N + 1, ∀ c', |c'| < 1 / 2 → IsIteratedDerivBound m R₀ c' j (K j c')) :
    ∃ K', IsIteratedDerivBound m R₀ c (N + 1) K' := by
  obtain ⟨kc, kn, qc, qn, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  have hc' : |-c| < 1 / 2 := by rwa [abs_neg]
  set Z := ‖gaugeFixedZerothOrder‖₊
  -- The constant for `π_(N+1)` on the kernel at the rate `-c`, and a common bound `B` for the
  -- derivatives `πⱼ`, `1 ≤ j ≤ N + 1`, on the kernel at that rate.
  set B := (∑ i ∈ Finset.range N, (N + 1).choose (i + 1) * (K (i + 1) (-c) * K (N - i) (-c)) +
    ∑ i ∈ Finset.range (N + 1), (N + 1).choose i * (qn * Z * K i (-c))) +
      ∑ j ∈ Finset.range (N + 1), K j (-c)
  refine ⟨(kc * ∑ i ∈ Finset.range (N + 1), (N + 1).choose i * (B * kn * K i c) +
      ∑ i ∈ Finset.range (N + 1), (N + 1).choose i * (qc * Z * K i c)) +
    (kc * (B * kn) + ∑ i ∈ Finset.range (N + 1), (N + 1).choose i * (qc * Z * K i c)),
    fun x D hx hbound hsol hframe hD hD₀ a t₀ hax ha M hb ↦ ?_⟩
  obtain ⟨hkc, hkn, hqc, hqn⟩ := hest x D hx hbound hsol hframe hD hD₀ (a t₀) hax
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hIH (j : ℕ) (hj : j < N + 1) (c' : ℝ) (hc' : |c'| < 1 / 2) :=
    hK j hj c' hc' x D hx hbound hsol hframe hD hD₀ a t₀ hax (ha.of_le (by exact_mod_cast hj.le))
      M fun i hi ↦ hb i (Finset.Icc_subset_Icc_right hj.le hi)
  have hB : ∀ j ∈ Finset.Icc 1 (N + 1), ∀ k ∈ (sobolevGaugeFixedOperator (a t₀)).ker,
      eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
        (iteratedDeriv j (fun t ↦ orthogonalKerProjection sobolevFieldValues
          (sobolevGaugeFixedOperator (a t))) t₀ k) z) 2 μ⊤ ≤
        (B * M ^ j : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
          sobolevFieldValues k z) 2 μ⊤ := by
    intro j hj k hk
    rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hj' | rfl
    · refine ((hIH j hj' (-c) hc').2 k).trans ?_
      gcongr
      exact le_add_left (Finset.single_le_sum (f := fun j ↦ K j (-c)) (fun _ _ ↦ zero_le)
        (Finset.mem_range.2 hj'))
    · refine (eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le_of_mem_ker hT hsurj
        (by exact_mod_cast ha) hb hqn (fun j hj e ↦ (hIH j hj (-c) hc').2 e) hk).trans ?_
      gcongr
      exact le_self_add
  refine ⟨fun f ↦ ?_, fun e ↦ ?_⟩
  · refine (eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le_of_le hT hsurj ha
      (Nat.succ_ne_zero N) hb hkc hkn hqc (fun j hj f ↦ (hIH j hj c hc).1 f) hB f).trans
      (mul_le_mul_left (ENNReal.coe_le_coe.2 (mul_le_mul_left le_self_add _)) _)
  · refine (eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le_of_le hT hsurj ha hb
      hkc hkn hqc (fun j hj e ↦ (hIH j hj c hc).2 e)
      (hB (N + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)) e).trans
      (mul_le_mul_left (ENNReal.coe_le_coe.2 (mul_le_mul_left le_add_self _)) _)

/-- The weighted estimates hold at every order and every rate `|c| < 1/2`. -/
private theorem exists_isIteratedDerivBound (m : ℕ) (R₀ : ℝ) (n : ℕ) :
    ∀ c, |c| < 1 / 2 → ∃ K, IsIteratedDerivBound m R₀ c n K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    rcases n with _ | N
    · exact exists_isIteratedDerivBound_zero m R₀ hc
    · choose! K hK using ih
      exact exists_isIteratedDerivBound_succ m R₀ hc hK

/-! ### The weighted estimates of every order -/

/-- **The weighted estimate for the derivatives of every order of the orthogonal right inverses,
uniformly over a window of divisors.** For every degree `m`, radius `R₀`, rate `|c| < 1/2` and
order `n` there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x`
be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of
radius `R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a curve of
`L∞` coefficients, `Cⁿ` at `t₀`, with `a t₀` the class of `x` and `‖aⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ n`,
where `aⱼ` is the `j`-th derivative of `a` at `t₀`, and let `Q t` be the right inverse of the
realization `L_(a t)` with values `L²`-orthogonal to its kernel. Then the `n`-th derivative `Qₙ` of
`Q` at `t₀` satisfies

`‖exp(c ρ) Qₙ f‖₂ ≤ K Mⁿ ‖exp(c ρ) f‖₂`

for every `f ∈ L²`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalRightInverse_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ (a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (t₀ : ℝ), a t₀ =ᵐ[μ⊤] x →
      ContDiffAt ℝ n a t₀ → ∀ M : ℝ≥0, (∀ j ∈ Finset.Icc 1 n, ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (iteratedDeriv n (fun t ↦ orthogonalRightInverse sobolevFieldValues
            (sobolevGaugeFixedOperator (a t))) t₀ f) z) 2 volume ≤
          K * M ^ n * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨K, hK⟩ := exists_isIteratedDerivBound m R₀ n c hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ a t₀ hax ha M hb f ↦ ?_⟩
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using
    (hK x D hx hbound hsol hframe hD hD₀ a t₀ hax ha M hb).1 f

/-- **The weighted estimate for the derivatives of every order of the orthogonal kernel
projections, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, rate
`|c| < 1/2` and order `n` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order. Let `a` be a curve of `L∞` coefficients, `Cⁿ` at `t₀`, with `a t₀` the class of `x` and
`‖aⱼ‖∞ ≤ Mʲ` for `1 ≤ j ≤ n`, where `aⱼ` is the `j`-th derivative of `a` at `t₀`, and let `π t` be
the projection of `H¹(ℂ)⁴` onto the kernel of the realization `L_(a t)` along its
`L²`-orthogonal complement. Then the `n`-th derivative `πₙ` of `π` at `t₀` satisfies

`‖exp(c ρ) πₙ e‖₂ ≤ K Mⁿ ‖exp(c ρ) e‖₂`

for every `e ∈ H¹(ℂ)⁴`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_iteratedDeriv_orthogonalKerProjection_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (n : ℕ) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ (a : ℝ → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (t₀ : ℝ), a t₀ =ᵐ[μ⊤] x →
      ContDiffAt ℝ n a t₀ → ∀ M : ℝ≥0, (∀ j ∈ Finset.Icc 1 n, ‖iteratedDeriv j a t₀‖₊ ≤ M ^ j) →
      ∀ e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
          (iteratedDeriv n (fun t ↦ orthogonalKerProjection sobolevFieldValues
            (sobolevGaugeFixedOperator (a t))) t₀ e) z) 2 volume ≤
          K * M ^ n * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2
            volume := by
  obtain ⟨K, hK⟩ := exists_isIteratedDerivBound m R₀ n c hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ a t₀ hax ha M hb e ↦ ?_⟩
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow] using
    (hK x D hx hbound hsol hframe hD hD₀ a t₀ hax ha M hb).2 e

end TauCeti.Vortex
