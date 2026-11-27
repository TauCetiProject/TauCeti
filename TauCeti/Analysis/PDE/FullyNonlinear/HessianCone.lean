/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Esymm
public import TauCeti.Analysis.MvPolynomial.NewtonMaclaurin
public import TauCeti.Analysis.PDE.FullyNonlinear.AdmissiblePair
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous

/-!
# The Hessian cones `Γ_k` are admissible cones

The Hessian cone `Γ_k = {λ ∈ ℝⁿ | σ_1(λ) > 0, …, σ_k(λ) > 0}` (`TauCeti.hessianCone n k`) is the
Gårding cone `Γ(σ_k, e)` of the elementary symmetric polynomial `σ_k` in the direction
`e = (1, …, 1)` (`TauCeti.gardingCone_esymm_eq_hessianCone`, a restatement of
`MvPolynomial.gardingCone_esymm`). Through this identification the Hessian cones inherit the
properties of Gårding cones of symmetric homogeneous polynomials: they are invariant under
permutations of the coordinates and under positive dilations. Together with openness
(`TauCeti.isOpen_hessianCone`) and `Γ_n ⊆ Γ_k ⊆ Γ_1` (`TauCeti.sum_pos_of_mem_hessianCone`), both
from the basic cone API next to the definition, this makes `Γ_k` an admissible cone for
`1 ≤ k ≤ n` (`TauCeti.isAdmissibleCone_hessianCone`). The largest index `Γ_n` is the positive
orthant (`TauCeti.hessianCone_self`). By Gårding's theorem on the convexity of the cones of
hyperbolic polynomials (`MvPolynomial.IsHyperbolic.convex_gardingCone`), every `Γ_k` is convex
(`TauCeti.convex_hessianCone`); for `k > n` it is empty, since `σ_{n+1} = 0`
(`TauCeti.le_of_mem_hessianCone`). As for every Gårding cone
(`MvPolynomial.IsHyperbolic.add_mem_gardingCone_of_mem_closure`), `Γ_k + closure Γ_n ⊆ Γ_k`
(`TauCeti.add_mem_hessianCone_of_nonneg`).

## Main results

* `TauCeti.gardingCone_esymm_eq_hessianCone`: `Γ(σ_k, e) = Γ_k`.
* `TauCeti.comp_perm_mem_hessianCone`, `TauCeti.smul_mem_hessianCone`: `Γ_k` is symmetric and a
  cone.
* `TauCeti.hessianCone_self`: `Γ_n` is the positive orthant.
* `TauCeti.isAdmissibleCone_hessianCone`: for `1 ≤ k ≤ n`, `Γ_k` is an admissible cone.
* `TauCeti.convex_hessianCone`: `Γ_k` is convex.
* `TauCeti.le_of_mem_hessianCone`: `Γ_k` is empty for `k > n`.
* `TauCeti.add_mem_hessianCone_of_nonneg`: `Γ_k + closure Γ_n ⊆ Γ_k`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {n k : ℕ}

/-- **The Gårding cone of `σ_k` is the Hessian cone**: `Γ(σ_k, e) = Γ_k` in `ℝⁿ`, for every `k`
(both sides are `ℝⁿ` for `k = 0` and empty for `k > n`). -/
theorem gardingCone_esymm_eq_hessianCone (n k : ℕ) :
    gardingCone (esymm (Fin n) ℝ k) 1 = hessianCone n k := by
  ext μ
  rw [gardingCone_esymm, Set.mem_ofPred_eq, mem_hessianCone]
  exact ⟨fun h j hj ↦ h j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2,
    fun h j hj1 hjk ↦ h j (mem_Icc.2 ⟨hj1, hjk⟩)⟩

/-- The Hessian cone `Γ_k` is invariant under permutations of the coordinates. -/
theorem comp_perm_mem_hessianCone (σ : Equiv.Perm (Fin n)) {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n k) : μ ∘ σ ∈ hessianCone n k := by
  rw [← gardingCone_esymm_eq_hessianCone] at hμ ⊢
  exact comp_mem_gardingCone (esymm_isSymmetric (Fin n) ℝ k σ) rfl hμ

/-- The Hessian cone `Γ_k` is invariant under positive dilations. -/
theorem smul_mem_hessianCone {t : ℝ} (ht : 0 < t) {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n k) : t • μ ∈ hessianCone n k := by
  rw [← gardingCone_esymm_eq_hessianCone] at hμ ⊢
  exact smul_mem_gardingCone (MvPolynomial.isHomogeneous_esymm (σ := Fin n) (R := ℝ) k) hμ ht

/-- `Γ_n` is the positive orthant. -/
theorem hessianCone_self (n : ℕ) : hessianCone n n = {μ : Fin n → ℝ | ∀ i, 0 < μ i} := by
  rw [← gardingCone_esymm_eq_hessianCone]
  simpa using gardingCone_esymm_card (σ := Fin n)

/-- **The Hessian cone `Γ_k` is an admissible cone** for `1 ≤ k ≤ n`: it is open, symmetric,
invariant under positive dilations, and `Γ_n ⊆ Γ_k ⊆ Γ_1`. -/
theorem isAdmissibleCone_hessianCone (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsAdmissibleCone (hessianCone n k) where
  isOpen := isOpen_hessianCone n k
  comp_perm_mem σ _ hμ := comp_perm_mem_hessianCone σ hμ
  smul_mem ht _ hμ := smul_mem_hessianCone ht hμ
  mem_of_forall_pos hμ := mem_hessianCone_of_pos hμ hkn
  sum_pos hμ := sum_pos_of_mem_hessianCone hk hμ

/-- The Hessian cone `Γ_k` is empty for `k > n`, since `σ_{n+1}` vanishes on `ℝⁿ`: a point of
`Γ_k` forces `k ≤ n`. -/
theorem le_of_mem_hessianCone {μ : Fin n → ℝ} (hμ : μ ∈ hessianCone n k) : k ≤ n := by
  by_contra! hkn
  have h := mem_hessianCone.1 hμ (n + 1) (mem_Icc.2 ⟨by omega, hkn⟩)
  have hzero : esymm (Fin n) ℝ (n + 1) = 0 := by
    rw [esymm_eq_multiset_esymm]
    exact Multiset.esymm_of_card_lt (by simp)
  simp [hzero] at h

/-- **The Hessian cone `Γ_k` is convex** (Gårding). For `k ≤ n` it is the Gårding cone of the
hyperbolic polynomial `σ_k`; for `k > n` it is empty, since `σ_{n+1}` vanishes on `ℝⁿ`. -/
theorem convex_hessianCone (n k : ℕ) : Convex ℝ (hessianCone n k) := by
  rcases le_or_gt k n with hkn | hkn
  · rw [← gardingCone_esymm_eq_hessianCone]
    exact (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn)).convex_gardingCone
  · convert convex_empty (𝕜 := ℝ) (E := Fin n → ℝ)
    exact Set.eq_empty_of_forall_notMem fun μ hμ ↦ (le_of_mem_hessianCone hμ).not_gt hkn

/-- In the Hessian cone `Γ_k`, moving along a vector with nonnegative coordinates stays in the
cone: `Γ_k + closure Γ_n ⊆ Γ_k`. -/
theorem add_mem_hessianCone_of_nonneg {μ ν : Fin n → ℝ} (hμ : μ ∈ hessianCone n k)
    (hν : ∀ i, 0 ≤ ν i) : μ + ν ∈ hessianCone n k := by
  have hkn := le_of_mem_hessianCone hμ
  rw [← gardingCone_esymm_eq_hessianCone] at hμ ⊢
  refine (isHyperbolic_esymm (σ := Fin n) (by simpa using hkn)).add_mem_gardingCone_of_mem_closure
    hμ ?_
  rw [gardingCone_esymm_eq_hessianCone]
  exact mem_closure_hessianCone_of_nonneg hν hkn

end TauCeti
