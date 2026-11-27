/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Analysis.Convex.Cone.Orthant
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding

/-!
# Gårding cones in the direction `e = (1, …, 1)`

Let `p` be a real polynomial, hyperbolic of degree `m` in the direction `e = (1, …, 1)`, with
Gårding cone `Γ = Γ(p, e)`.

If `p` is symmetric and `m ≥ 1`, then `Γ` lies in the half-space `σ_1 > 0`
(`MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`). The proof averages over permutations:
for `x ∈ Γ`, the sum `∑_π x ∘ π` over all permutations `π` lies in the convex cone `Γ`, and all
its coordinates are equal, to a multiple of `σ_1(x)` by a positive constant. If `σ_1(x) ≤ 0`, it
is `-s • e` with `s ≥ 0`, which is not in `Γ` since `p(-s • e + s • e) = p(0) = 0`.

Without symmetry, `Γ` contains the positive orthant `Γ_n` exactly when every coordinate vector
`eᵢ` lies in the closure of `Γ` (`MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`). This
holds for every open nonempty convex cone (`ConvexCone.setOf_forall_pos_subset_iff`), and `Γ` is
one by Gårding's theorem.

## Main results

* `MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`: for symmetric `p` of degree `m ≥ 1`,
  `σ_1 > 0` on `Γ(p, e)`.
* `MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`: `Γ_n ⊆ Γ(p, e)` if and only if every
  `eᵢ` lies in the closure of `Γ(p, e)`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

namespace MvPolynomial.IsHyperbolic

variable {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℝ} {m : ℕ}

/-- The coordinates of the sum `∑_π x ∘ π` over all permutations `π` are equal. -/
private theorem sum_perm_apply_eq [DecidableEq σ] (x : σ → ℝ) (i j : σ) :
    ∑ π : Equiv.Perm σ, x (π i) = ∑ π : Equiv.Perm σ, x (π j) := by
  exact Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ fun π ↦ by
    simp [Equiv.Perm.mul_apply]

/-- The coordinates of the sum `∑_π x ∘ π` over all permutations `π` add up to the number of
permutations times `σ_1(x)`. -/
private theorem sum_sum_perm_apply [DecidableEq σ] (x : σ → ℝ) :
    ∑ i, ∑ π : Equiv.Perm σ, x (π i) = Fintype.card (Equiv.Perm σ) * ∑ i, x i := by
  rw [Finset.sum_comm]
  simp [Equiv.sum_comp]

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
  -- A polynomial of positive degree vanishes at `0`, so the cone does not contain `-s • e`.
  have h0 : eval (0 : σ → ℝ) p = 0 := by
    simpa [zero_pow (by omega : m ≠ 0)] using hp.isHomogeneous.eval_smul (0 : ℝ) 1
  by_contra! hneg
  -- `σ` is nonempty: otherwise `p` would be a homogeneous polynomial of positive degree in no
  -- variables, so `p(e) = p(0) = 0`.
  obtain ⟨i₀⟩ : Nonempty σ := by
    by_contra hσ
    rw [not_nonempty_iff] at hσ
    exact hp.eval_pos.ne' (by rwa [Subsingleton.elim (1 : σ → ℝ) 0])
  -- All coordinates of `y` equal `y i₀`, which has the sign of `σ_1(x)`.
  have hyc : y = y i₀ • (1 : σ → ℝ) := by
    ext i
    simp [hyi, sum_perm_apply_eq x i i₀]
  have hsum : (Fintype.card σ : ℝ) * y i₀ = Fintype.card (Equiv.Perm σ) * ∑ i, x i := by
    rw [← sum_sum_perm_apply, hyi]
    simp_rw [sum_perm_apply_eq x _ i₀]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hy₀ : y i₀ ≤ 0 := by
    have hcard : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i₀⟩
    nlinarith [show (0 : ℝ) < Fintype.card (Equiv.Perm σ) by exact_mod_cast Fintype.card_pos]
  have := (mem_gardingCone.1 hy) (-y i₀) (neg_nonneg.2 hy₀)
  nth_rw 1 [hyc] at this
  rw [← add_smul, add_neg_cancel, zero_smul] at this
  exact this h0

omit [Fintype σ] in
/-- **The positive orthant and the Gårding cone.** For `p` hyperbolic in the direction
`e = (1, …, 1)`, the Gårding cone `Γ(p, e)` contains the positive orthant `Γ_n` if and only if
every coordinate vector `eᵢ` lies in its closure. -/
theorem setOf_forall_pos_subset_iff [Finite σ] [DecidableEq σ] (hp : IsHyperbolic p m 1) :
    {x : σ → ℝ | ∀ i, 0 < x i} ⊆ gardingCone p 1 ↔
      ∀ i, (Pi.single i 1 : σ → ℝ) ∈ closure (gardingCone p 1) :=
  ConvexCone.setOf_forall_pos_subset_iff (K := ⟨gardingCone p 1,
      fun _ hc _ hx ↦ smul_mem_gardingCone hp.isHomogeneous hx hc,
      fun _ hx _ hy ↦ hp.add_mem_gardingCone hx hy⟩)
    (isOpen_gardingCone hp.isHomogeneous hp.eval_pos.ne')
    ⟨1, self_mem_gardingCone hp.isHomogeneous hp.eval_pos.ne'⟩

end MvPolynomial.IsHyperbolic
