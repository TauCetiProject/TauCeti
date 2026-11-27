/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.HessianCone
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Order.Field

/-!
# Positivity of the partial derivatives of `σ_k` on `Γ_k`

For `λ` in the Hessian cone `Γ_{k+1} ⊆ ℝⁿ`, every `σ_{k;i}(λ)`, the `k`-th elementary symmetric
function of the entries of `λ` other than `λᵢ`, is positive
(`TauCeti.eval_update_zero_esymm_pos_of_mem_hessianCone`). Equivalently, the partial derivatives
`∂ᵢ σ_{k+1} = σ_{k;i}` are positive on `Γ_{k+1}`
(`TauCeti.eval_pderiv_esymm_pos_of_mem_hessianCone`).

The proof restricts `σ_{k+1}` to the line `λ + t eᵢ`, on which it is affine,
`σ_{k+1}(λ + t eᵢ) = (λᵢ + t) σ_{k;i}(λ) + σ_{k+1;i}(λ)`. The coordinate vector `eᵢ` lies in the
closure of the open convex cone `Γ_{k+1}`, so the half-line `t ≥ 0` stays in `Γ_{k+1}`, where
`σ_{k+1} > 0`; hence the slope `σ_{k;i}(λ)` is nonnegative. If it were zero, `σ_{k+1}` would be
the positive constant `σ_{k+1}(λ)` on the whole line, and the line would lie in `Γ_{k+1}`: the set
of its points in `Γ_{k+1}` is open, and closed because a point of the closure of a Gårding cone
where the polynomial does not vanish lies in the cone. But `σ_1(λ + t eᵢ) = σ_1(λ) + t` is
negative for `t < -σ_1(λ)`, while `Γ_{k+1} ⊆ Γ_1`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Finset MvPolynomial Function

namespace TauCeti

variable {n k : ℕ}

/-- In the Hessian cone `Γ_k`, moving along a vector with nonnegative coordinates stays in the
cone: `Γ_k + closure Γ_n ⊆ Γ_k`. -/
theorem add_mem_hessianCone_of_nonneg {μ ν : Fin n → ℝ} (hμ : μ ∈ hessianCone n k)
    (hν : ∀ i, 0 ≤ ν i) : μ + ν ∈ hessianCone n k := by
  rcases le_or_gt k n with hkn | hkn
  · have hconv := convex_hessianCone n k
    have hopen := isOpen_hessianCone n k
    -- `μ / 2 + ν / 2` is a combination of an interior point and a point of the closure.
    have h := hconv.combo_interior_closure_mem_interior (hopen.interior_eq.symm ▸ hμ)
      (mem_closure_hessianCone_of_nonneg hν hkn) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [hopen.interior_eq] at h
    have h2 := smul_mem_hessianCone two_pos h
    rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
      one_smul] at h2
  · -- For `k > n` the cone is empty, as `σ_{n+1} = 0` on `ℝⁿ`.
    have h := mem_hessianCone.1 hμ (n + 1) (mem_Icc.2 ⟨by omega, hkn⟩)
    have hzero : esymm (Fin n) ℝ (n + 1) = 0 := by
      rw [esymm_eq_multiset_esymm]
      exact Multiset.esymm_of_card_lt (by simp)
    simp [hzero] at h

/-- On the line `μ + t eᵢ`, `σ_{k+1}` is affine with slope `σ_{k;i}(μ)`. -/
private theorem eval_add_smul_single_esymm_succ (μ : Fin n → ℝ) (i : Fin n) (k : ℕ) (t : ℝ) :
    eval (μ + t • Pi.single i 1) (esymm (Fin n) ℝ (k + 1)) =
      (μ i + t) * eval (update μ i 0) (esymm (Fin n) ℝ k) +
        eval (update μ i 0) (esymm (Fin n) ℝ (k + 1)) := by
  have hu : update (μ + t • Pi.single i 1) i 0 = update μ i 0 := by
    ext j
    by_cases hj : j = i <;> simp [hj, update_of_ne]
  have h := aeval_esymm_succ_eq_mul_add (R := ℝ) (μ + t • Pi.single i 1) i k
  simp only [hu] at h
  simpa using h

/-- An affine function `t ↦ (a + t) c + d` positive on the half-line `t ≥ 0` has nonnegative
slope `c`. -/
private theorem nonneg_of_forall_pos {a c d : ℝ} (h : ∀ t : ℝ, 0 ≤ t → 0 < (a + t) * c + d) :
    0 ≤ c := by
  by_contra! hc
  have hc' : 0 < -c := by linarith
  have := h (|a| + |d| / -c + 1) (by positivity)
  have h1 : (a + (|a| + |d| / -c + 1)) * c ≤ (|d| / -c + 1) * c :=
    mul_le_mul_of_nonpos_right (by linarith [neg_abs_le a]) hc.le
  have h2 : (|d| / -c + 1) * c = -|d| + c := by
    have := hc.ne
    field_simp
  linarith [le_abs_self d]

/-- **`σ_{k;i} > 0` on `Γ_{k+1}`.** For `λ` in the Hessian cone `Γ_{k+1}`, the `k`-th elementary
symmetric function of the entries of `λ` other than `λᵢ` is positive. -/
theorem eval_update_zero_esymm_pos_of_mem_hessianCone {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n (k + 1)) (i : Fin n) :
    0 < eval (update μ i 0) (esymm (Fin n) ℝ k) := by
  set c := eval (update μ i 0) (esymm (Fin n) ℝ k)
  set d := eval (update μ i 0) (esymm (Fin n) ℝ (k + 1))
  have hline (t : ℝ) : eval (μ + t • Pi.single i 1) (esymm (Fin n) ℝ (k + 1)) = (μ i + t) * c + d :=
    eval_add_smul_single_esymm_succ μ i k t
  have hsingle : ∀ t : ℝ, 0 ≤ t → ∀ j, 0 ≤ (t • (Pi.single i 1 : Fin n → ℝ)) j := fun t ht j ↦ by
    by_cases hj : j = i <;> simp [hj, ht]
  -- On the half-line `t ≥ 0` the value `(μᵢ + t) c + d` of `σ_{k+1}` is positive.
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < (μ i + t) * c + d := by
    rw [← hline]
    exact mem_hessianCone.1 (add_mem_hessianCone_of_nonneg hμ (hsingle t ht)) (k + 1)
      (mem_Icc.2 ⟨by omega, le_rfl⟩)
  -- So the slope `c` is nonnegative.
  have hc : 0 ≤ c := nonneg_of_forall_pos hpos
  refine hc.lt_of_ne fun hc0 ↦ ?_
  -- If `c = 0`, the whole line lies in `Γ_{k+1}`, since `σ_{k+1}` is a positive constant on it.
  have hkn : k + 1 ≤ n := by
    by_contra! hkn
    have h := mem_hessianCone.1 hμ (n + 1) (mem_Icc.2 ⟨by omega, hkn⟩)
    have hzero : esymm (Fin n) ℝ (n + 1) = 0 := by
      rw [esymm_eq_multiset_esymm]
      exact Multiset.esymm_of_card_lt (by simp)
    simp [hzero] at h
  have hd : 0 < d := by simpa [← hc0] using hpos 0 le_rfl
  have hf : Continuous fun t : ℝ ↦ μ + t • (Pi.single i 1 : Fin n → ℝ) := by fun_prop
  set S := {t : ℝ | μ + t • (Pi.single i 1 : Fin n → ℝ) ∈ hessianCone n (k + 1)}
  have hS : IsClopen S := by
    refine ⟨isClosed_of_closure_subset fun t ht ↦ ?_, (isOpen_hessianCone n (k + 1)).preimage hf⟩
    have hcl := map_mem_closure hf ht fun _ h ↦ h
    change μ + t • _ ∈ hessianCone n (k + 1)
    rw [← gardingCone_esymm_eq_hessianCone] at hcl ⊢
    refine (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn)).mem_gardingCone_of_mem_closure
      hcl ?_
    rw [hline, ← hc0, mul_zero, zero_add]
    exact hd.ne'
  have hall := hS.eq_univ ⟨0, by simpa [S] using hμ⟩
  -- But `σ_1` is negative far along the line in the direction `-eᵢ`.
  have hmem : μ + (-(∑ j, μ j) - 1) • (Pi.single i 1 : Fin n → ℝ) ∈ hessianCone n (k + 1) := by
    have : (-(∑ j, μ j) - 1) ∈ S := hall ▸ Set.mem_univ _
    exact this
  have := sum_pos_of_mem_hessianCone (by omega) hmem
  simp [Finset.sum_add_distrib, Pi.single_apply] at this
  linarith

/-- **`∂ᵢ σ_{k+1} > 0` on `Γ_{k+1}`.** The partial derivatives of the elementary symmetric
polynomial `σ_{k+1}` are positive on the Hessian cone `Γ_{k+1}`. -/
theorem eval_pderiv_esymm_pos_of_mem_hessianCone {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n (k + 1)) (i : Fin n) :
    0 < eval μ (pderiv i (esymm (Fin n) ℝ (k + 1))) := by
  rw [eval_pderiv_esymm_succ]
  exact eval_update_zero_esymm_pos_of_mem_hessianCone hμ i

end TauCeti
