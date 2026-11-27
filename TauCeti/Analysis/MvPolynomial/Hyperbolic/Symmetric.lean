/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
import TauCeti.Algebra.BigOperators.Perm
import TauCeti.Analysis.MvPolynomial.Hyperbolic.Concave

/-!
# Gårding cones in the direction `e = (1, …, 1)`

Let `p` be a real polynomial, hyperbolic of degree `m` in the direction `e = (1, …, 1)`, with
Gårding cone `Γ = Γ(p, e)`.

If `p` is symmetric and `m ≥ 1`, then `Γ` lies in the half-space `σ_1 > 0`
(`MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`). The proof averages over permutations:
for `x ∈ Γ`, the sum `∑_π x ∘ π` over all permutations `π` lies in the convex cone `Γ`, and all
its coordinates are equal, to a multiple of `σ_1(x)` by a positive constant. If `σ_1(x) ≤ 0`, it
is `-s • e` with `s ≥ 0`, which is not in `Γ` since `p(-s • e + s • e) = p(0) = 0`
(`MvPolynomial.smul_notMem_gardingCone`).

If moreover `b` lies in the closure of the cone and `σ_1(b) > 0`, then the directional
derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ`
(`MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure_of_sum_pos`). This follows
from the general `MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure`, since
`σ_1 ≥ 0` on the closure of `Γ` puts `-b` outside it. In particular, if the
coordinate vector `eᵢ` lies in the closure of the cone, then `∂p/∂Xᵢ > 0` on `Γ`
(`MvPolynomial.IsHyperbolic.eval_pderiv_pos_of_single_mem_closure`). By
`MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`, this condition for every `i` says that
`Γ` contains the positive orthant `Γ_n`. Symmetry alone does not give it: for
`p = 2xy - 0.9(x² + y²)` on `ℝ²`, hyperbolic in `e`, the cone is a sector around the diagonal
that contains `(1, 0.7)`, where `∂p/∂x = -0.4`.

## Main results

* `MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`: for symmetric `p` of degree `m ≥ 1`,
  `σ_1 > 0` on `Γ(p, e)`.
* `MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure_of_sum_pos`: for symmetric
  `p` of degree `m ≥ 1`, `b ∈ closure Γ(p, e)` and `σ_1(b) > 0`, `D_b p > 0` on `Γ(p, e)`.
* `MvPolynomial.IsHyperbolic.eval_pderiv_pos_of_single_mem_closure`: for symmetric `p` of degree
  `m ≥ 1` and `eᵢ ∈ closure Γ(p, e)`, `∂p/∂Xᵢ > 0` on `Γ(p, e)`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Set

namespace MvPolynomial.IsHyperbolic

variable {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℝ} {m : ℕ}

/-- **A symmetric Gårding cone lies in the half-space `σ_1 > 0`.** For a symmetric polynomial `p`
of degree `m ≥ 1`, hyperbolic in the direction `e = (1, …, 1)`, every point of the Gårding cone
`Γ(p, e)` has positive coordinate sum. -/
theorem sum_pos_of_mem_gardingCone (hp : IsHyperbolic p m 1) (hm : 1 ≤ m) (hsymm : p.IsSymmetric)
    {x : σ → ℝ} (hx : x ∈ gardingCone p 1) : 0 < ∑ i, x i := by
  classical
  -- The sum over all permutations lies in the cone.
  set y : σ → ℝ := ∑ π : Equiv.Perm σ, x ∘ π
  have hy : y ∈ gardingCone p 1 :=
    Finset.sum_induction_nonempty _ (· ∈ gardingCone p 1)
      (fun _ _ ha hb ↦ hp.add_mem_gardingCone ha hb) Finset.univ_nonempty
      fun π _ ↦ comp_mem_gardingCone (hsymm π) rfl hx
  have hyi (i : σ) : y i = ∑ π : Equiv.Perm σ, x (π i) := by simp [y, Finset.sum_apply]
  by_contra! hneg
  -- A polynomial of positive degree vanishes at `0`, so the cone contains no `s • e` with `s ≤ 0`.
  -- Hence `σ` is nonempty: otherwise `y = 0 • e`.
  obtain ⟨i₀⟩ : Nonempty σ := by
    by_contra hσ
    rw [not_nonempty_iff] at hσ
    exact smul_notMem_gardingCone hp.isHomogeneous (by omega) le_rfl
      (Subsingleton.elim y ((0 : ℝ) • 1) ▸ hy)
  -- All coordinates of `y` equal `y i₀`, which has the sign of `σ_1(x)`.
  have hyc : y = y i₀ • (1 : σ → ℝ) := by
    ext i
    simp [hyi, Equiv.Perm.sum_apply_eq_sum_apply x i i₀]
  have hsum : (Fintype.card σ : ℝ) * y i₀ = Fintype.card (Equiv.Perm σ) * ∑ i, x i := by
    rw [← nsmul_eq_mul (Fintype.card (Equiv.Perm σ)), ← Equiv.Perm.sum_sum_apply, hyi]
    simp_rw [Equiv.Perm.sum_apply_eq_sum_apply x _ i₀]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hy₀ : y i₀ ≤ 0 := by
    have hcard : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i₀⟩
    nlinarith [show (0 : ℝ) < Fintype.card (Equiv.Perm σ) by exact_mod_cast Fintype.card_pos]
  exact smul_notMem_gardingCone hp.isHomogeneous (by omega) hy₀ (hyc ▸ hy)

/-- **Positivity of the directional derivatives on a symmetric Gårding cone.** Let `p` be a
symmetric polynomial, hyperbolic of degree `m ≥ 1` in the direction `e = (1, …, 1)`, and let `b`
lie in the closure of the Gårding cone `Γ(p, e)` with `σ_1(b) > 0`. Then the directional
derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ(p, e)`. -/
theorem eval_sum_smul_pderiv_pos_of_mem_closure_of_sum_pos (hp : IsHyperbolic p m 1)
    (hm : 1 ≤ m) (hsymm : p.IsSymmetric) {b : σ → ℝ} (hb : b ∈ closure (gardingCone p 1))
    (hb0 : 0 < ∑ j, b j) {x : σ → ℝ} (hx : x ∈ gardingCone p 1) :
    0 < eval x (∑ i, b i • pderiv i p) := by
  -- `σ_1 > 0` on the cone, hence `σ_1 ≥ 0` on its closure, so `-b` is not in the closure.
  refine hp.eval_sum_smul_pderiv_pos_of_mem_closure hm hb (fun hb' ↦ ?_) hx
  have := closure_minimal (fun y hy ↦ (hp.sum_pos_of_mem_gardingCone hm hsymm hy).le)
    (isClosed_le continuous_const (by fun_prop)) hb'
  simp only [mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib] at this
  linarith

omit [Fintype σ] in
/-- **Positivity of the partial derivatives on a symmetric Gårding cone.** Let `p` be a symmetric
polynomial, hyperbolic of degree `m ≥ 1` in the direction `e = (1, …, 1)`, such that the
coordinate vector `eᵢ` lies in the closure of the Gårding cone `Γ(p, e)`. Then `∂p/∂Xᵢ > 0` on
`Γ(p, e)`. -/
theorem eval_pderiv_pos_of_single_mem_closure [Finite σ] [DecidableEq σ] (hp : IsHyperbolic p m 1)
    (hm : 1 ≤ m) (hsymm : p.IsSymmetric) {i : σ}
    (hi : (Pi.single i 1 : σ → ℝ) ∈ closure (gardingCone p 1)) {x : σ → ℝ}
    (hx : x ∈ gardingCone p 1) : 0 < eval x (pderiv i p) := by
  have := Fintype.ofFinite σ
  simpa [Pi.single_apply] using
    hp.eval_sum_smul_pderiv_pos_of_mem_closure_of_sum_pos hm hsymm hi (by simp) hx

end MvPolynomial.IsHyperbolic
