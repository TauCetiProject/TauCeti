/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
permutations of the coordinates and under positive dilations. They are open, as finite
intersections of the open sets `{σ_j > 0}`. With `Γ_n ⊆ Γ_k ⊆ Γ_1` this makes
`Γ_k` an admissible cone for `1 ≤ k ≤ n` (`TauCeti.isAdmissibleCone_hessianCone`). The extreme
cases are the positive orthant `Γ_n` (`TauCeti.hessianCone_self`) and the half-space `Γ_1`
(`TauCeti.hessianCone_one`), and the cones are nested, `Γ_k ⊆ Γ_j` for `j ≤ k`
(`TauCeti.hessianCone_subset_hessianCone`).

## Main results

* `TauCeti.gardingCone_esymm_eq_hessianCone`: `Γ(σ_k, e) = Γ_k`.
* `TauCeti.isOpen_hessianCone`, `TauCeti.comp_perm_mem_hessianCone`,
  `TauCeti.smul_mem_hessianCone`: `Γ_k` is open, symmetric and a cone.
* `TauCeti.hessianCone_self`, `TauCeti.hessianCone_one`: `Γ_n` is the positive orthant and `Γ_1`
  the half-space `σ_1 > 0`.
* `TauCeti.isAdmissibleCone_hessianCone`: for `1 ≤ k ≤ n`, `Γ_k` is an admissible cone.

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

/-- The Hessian cone `Γ_k` is open. -/
theorem isOpen_hessianCone (n k : ℕ) : IsOpen (hessianCone n k) := by
  have h : hessianCone n k = ⋂ j ∈ Icc 1 k, {μ | 0 < eval μ (esymm (Fin n) ℝ j)} := by
    ext; simp
  rw [h]
  exact isOpen_biInter_finset fun j _ ↦ isOpen_lt continuous_const (MvPolynomial.continuous_eval _)

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

/-- The Hessian cones are nested: `Γ_k ⊆ Γ_j` for `j ≤ k`. -/
theorem hessianCone_subset_hessianCone {j : ℕ} (hjk : j ≤ k) :
    hessianCone n k ⊆ hessianCone n j := fun _ hμ ↦ mem_hessianCone.2 fun i hi ↦
  mem_hessianCone.1 hμ i (mem_Icc.2 ⟨(mem_Icc.1 hi).1, (mem_Icc.1 hi).2.trans hjk⟩)

/-- `Γ_n` is the positive orthant. -/
theorem hessianCone_self (n : ℕ) : hessianCone n n = {μ : Fin n → ℝ | ∀ i, 0 < μ i} := by
  rw [← gardingCone_esymm_eq_hessianCone]
  simpa using gardingCone_esymm_card (σ := Fin n)

/-- `Γ_1` is the half-space `σ_1 = λ_1 + ⋯ + λ_n > 0`. -/
theorem hessianCone_one (n : ℕ) : hessianCone n 1 = {μ : Fin n → ℝ | 0 < ∑ i, μ i} := by
  ext μ
  simp [esymm_one]

/-- `Γ_k ⊆ Γ_1` for `k ≥ 1`: every point of `Γ_k` has positive coordinate sum. -/
theorem sum_pos_of_mem_hessianCone (hk : 1 ≤ k) {μ : Fin n → ℝ} (hμ : μ ∈ hessianCone n k) :
    0 < ∑ i, μ i := by
  have := hessianCone_subset_hessianCone hk hμ
  rwa [hessianCone_one] at this

/-- **The Hessian cone `Γ_k` is an admissible cone** for `1 ≤ k ≤ n`: it is open, symmetric,
invariant under positive dilations, and `Γ_n ⊆ Γ_k ⊆ Γ_1`. -/
theorem isAdmissibleCone_hessianCone (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsAdmissibleCone (hessianCone n k) where
  isOpen := isOpen_hessianCone n k
  comp_perm_mem σ _ hμ := comp_perm_mem_hessianCone σ hμ
  smul_mem ht _ hμ := smul_mem_hessianCone ht hμ
  mem_of_forall_pos hμ := mem_hessianCone_of_pos hμ hkn
  sum_pos hμ := sum_pos_of_mem_hessianCone hk hμ

end TauCeti
