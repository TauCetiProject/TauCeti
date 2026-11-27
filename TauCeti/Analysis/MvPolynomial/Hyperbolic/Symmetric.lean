/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
import TauCeti.RingTheory.MvPolynomial.Homogeneous

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
`eᵢ` lies in the closure of `Γ` (`MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`). If the
`eᵢ` lie in the closed convex cone `closure Γ`, so does the open orthant `Γ_n`, which then lies in
the interior of `closure Γ`; that interior is `Γ`, as `Γ` is open and convex. Conversely each
`eᵢ` is the limit of `eᵢ + ε • e ∈ Γ_n` as `ε → 0⁺`.

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

open Filter Topology Pointwise

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
    rw [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, hyi, hyi, sum_perm_apply_eq x i i₀]
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
/-- In a Gårding cone `Γ(p, e)`, a vector `eᵢ + ε • e` with `ε > 0`, which has positive
coordinates, tends to the coordinate vector `eᵢ` as `ε → 0⁺`. -/
private theorem tendsto_single_add_smul_one [DecidableEq σ] (i : σ) :
    Tendsto (fun ε : ℝ ↦ Pi.single i 1 + ε • (1 : σ → ℝ)) (𝓝[>] 0) (𝓝 (Pi.single i 1)) := by
  have hc : Continuous fun ε : ℝ ↦ Pi.single i 1 + ε • (1 : σ → ℝ) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

omit [Fintype σ] in
/-- **The positive orthant and the Gårding cone.** For `p` hyperbolic in the direction
`e = (1, …, 1)`, the Gårding cone `Γ(p, e)` contains the positive orthant `Γ_n` if and only if
every coordinate vector `eᵢ` lies in its closure. -/
theorem setOf_forall_pos_subset_iff [Finite σ] [DecidableEq σ] (hp : IsHyperbolic p m 1) :
    {x : σ → ℝ | ∀ i, 0 < x i} ⊆ gardingCone p 1 ↔
      ∀ i, (Pi.single i 1 : σ → ℝ) ∈ closure (gardingCone p 1) := by
  have := Fintype.ofFinite σ
  set Γ := gardingCone p 1
  have hconv : Convex ℝ Γ := hp.convex_gardingCone
  have hopen : IsOpen Γ := isOpen_gardingCone hp.isHomogeneous hp.eval_pos.ne'
  have hone : (1 : σ → ℝ) ∈ Γ := self_mem_gardingCone hp.isHomogeneous hp.eval_pos.ne'
  constructor
  · refine fun h i ↦ mem_closure_of_tendsto (tendsto_single_add_smul_one i) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine h fun j ↦ ?_
    by_cases hj : j = i <;> simp [hj, hε, add_pos_of_nonneg_of_pos]
  · intro h x hx
    -- The closure of `Γ` is closed under positive dilations and under addition, and contains `0`.
    have hsmul {s : ℝ} (hs : 0 < s) {y : σ → ℝ} (hy : y ∈ closure Γ) : s • y ∈ closure Γ := by
      have : s • closure Γ ⊆ closure Γ := by
        rw [← closure_smul₀]
        exact closure_mono fun _ ⟨z, hz, hzy⟩ ↦
          hzy ▸ smul_mem_gardingCone hp.isHomogeneous hz hs
      exact this (Set.smul_mem_smul_set hy)
    have hadd {y z : σ → ℝ} (hy : y ∈ closure Γ) (hz : z ∈ closure Γ) : y + z ∈ closure Γ := by
      have := hsmul two_pos (hconv.closure hy hz (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
        one_smul] at this
    have hzero : (0 : σ → ℝ) ∈ closure Γ := by
      have hc : Continuous fun ε : ℝ ↦ ε • (1 : σ → ℝ) := by fun_prop
      refine mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
        (by simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact smul_mem_gardingCone hp.isHomogeneous hone hε
    -- Every point of the open orthant lies in the closure of `Γ`, hence in its interior.
    have horth : {x : σ → ℝ | ∀ i, 0 < x i} ⊆ closure Γ := fun y hy ↦ by
      rw [← Finset.univ_sum_single y]
      refine Finset.sum_induction _ (· ∈ closure Γ) (fun _ _ ↦ hadd) hzero fun i _ ↦ ?_
      have : Pi.single i (y i) = y i • (Pi.single i 1 : σ → ℝ) := by
        ext j
        by_cases hj : j = i <;> simp [hj]
      exact this ▸ hsmul (hy i) (h i)
    have hint : interior (closure Γ) = Γ := by
      rw [hconv.interior_closure_eq_interior_of_nonempty_interior
        ⟨1, hopen.interior_eq.symm ▸ hone⟩, hopen.interior_eq]
    have hopen' : IsOpen {x : σ → ℝ | ∀ i, 0 < x i} := by
      simp_rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
    exact hint ▸ interior_maximal horth hopen' hx

end MvPolynomial.IsHyperbolic
