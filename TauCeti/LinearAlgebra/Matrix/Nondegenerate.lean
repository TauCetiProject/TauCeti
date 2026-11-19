/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Separating vectors by a left- or right-separating form

For a left-separating matrix `M` over a field (for example a nondegenerate one), the linear forms
`w ↦ v ⬝ᵥ M *ᵥ w` determine `v`. This file records the two-vector form of that statement: if `x`
is not a multiple of `u`, then some `w` is orthogonal to `u` but not to `x`. Otherwise the form of
`x` would vanish on the kernel of the form of `u`, making it a multiple of that form by Mathlib's
`mem_span_of_iInf_ker_le_ker`, and left separation would make `x` the same multiple of `u`. This
complements Mathlib's `Matrix.Nondegenerate.exists_not_ortho_of_ne_zero`, the case `u = 0`, and is
the basic tool for moving vectors by transvections in the classical groups.

For a right-separating matrix `M` over any commutative semiring (for example a nondegenerate one,
over the field with two elements as well), two nonzero vectors `x` and `y` have a common vector `z`
pairing nontrivially with both `M *ᵥ x` and `M *ᵥ y`.

## Main results

* `Matrix.SeparatingLeft.exists_ortho_and_not_ortho_of_notMem_span` and
  `Matrix.SeparatingLeft.exists_ortho_and_not_ortho_pair_of_notMem_span`: a vector orthogonal to
  `u` but not to `x` (or to neither `x` nor `y`), when `x` (and `y`) do not lie on `K ∙ u`.
* `Matrix.SeparatingRight.exists_not_ortho_and_not_ortho_of_ne_zero_of_ne_zero`: a vector `z` with
  `z ⬝ᵥ M *ᵥ x ≠ 0` and `z ⬝ᵥ M *ᵥ y ≠ 0`, for nonzero `x` and `y`.
* `Matrix.notMem_span_of_dotProduct_mulVec` and
  `Matrix.notMem_span_of_dotProduct_mulVec_of_ne_zero`: separating a vector from `R ∙ a` when
  `v ⬝ᵥ M *ᵥ ·` vanishes on one of `a`, `z` and not the other.
-/

public section

namespace Matrix.SeparatingLeft

variable {m n K : Type*} [Fintype m] [Fintype n] [Field K] {M : Matrix m n K}

/-- **A vector orthogonal to `u` but not to `x`**, for a left-separating matrix `M`, when `x` is
not a multiple of `u`. -/
theorem exists_ortho_and_not_ortho_of_notMem_span (hM : M.SeparatingLeft) {u x : m → K}
    (hx : x ∉ K ∙ u) : ∃ w, u ⬝ᵥ M *ᵥ w = 0 ∧ x ⬝ᵥ M *ᵥ w ≠ 0 := by
  classical
  by_contra! h
  apply hx
  -- The form of `x` vanishes on the kernel of the form of `u`, so it is a multiple of it.
  let F : (m → K) →ₗ[K] (n → K) →ₗ[K] K := Matrix.toLinearMap₂' K M
  have hker : ⨅ _ : Unit, LinearMap.ker (F u) ≤ LinearMap.ker (F x) := by
    intro w hw
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, F, Matrix.toLinearMap₂'_apply'] at hw ⊢
    exact h w (hw ())
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
    simpa using mem_span_of_iInf_ker_le_ker hker
  -- Left separation turns the equality of forms into `x = c • u`.
  refine Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp ?_).symm⟩
  refine separatingLeft_def.mp hM _ fun w ↦ ?_
  simpa [F, Matrix.toLinearMap₂'_apply', sub_dotProduct, smul_dotProduct, sub_eq_zero,
    eq_comm] using congr($hc w)

/-- **A vector orthogonal to `u` and to neither `x` nor `y`**, for a left-separating matrix `M`,
when neither `x` nor `y` lies on `K ∙ u`. -/
theorem exists_ortho_and_not_ortho_pair_of_notMem_span (hM : M.SeparatingLeft) {u x y : m → K}
    (hx : x ∉ K ∙ u) (hy : y ∉ K ∙ u) :
    ∃ w, u ⬝ᵥ M *ᵥ w = 0 ∧ x ⬝ᵥ M *ᵥ w ≠ 0 ∧ y ⬝ᵥ M *ᵥ w ≠ 0 := by
  obtain ⟨w₁, hw₁u, hw₁x⟩ := hM.exists_ortho_and_not_ortho_of_notMem_span hx
  obtain ⟨w₂, hw₂u, hw₂y⟩ := hM.exists_ortho_and_not_ortho_of_notMem_span hy
  by_cases h₁ : y ⬝ᵥ M *ᵥ w₁ = 0
  · by_cases h₂ : x ⬝ᵥ M *ᵥ w₂ = 0
    · exact ⟨w₁ + w₂, by simp [mulVec_add, hw₁u, hw₂u], by simp [mulVec_add, h₂, hw₁x],
        by simp [mulVec_add, h₁, hw₂y]⟩
    · exact ⟨w₂, hw₂u, h₂, hw₂y⟩
  · exact ⟨w₁, hw₁u, hw₁x, h₁⟩

end Matrix.SeparatingLeft

namespace Matrix.SeparatingRight

variable {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R] {M : Matrix m n R}

/-- If `M` is right-separating (for example nondegenerate) and `x`, `y` are nonzero, then some `z`
pairs nontrivially with both: `z ⬝ᵥ M *ᵥ x ≠ 0` and `z ⬝ᵥ M *ᵥ y ≠ 0`. This holds over any
commutative semiring, in particular over the field with two elements. -/
theorem exists_not_ortho_and_not_ortho_of_ne_zero_of_ne_zero (hM : M.SeparatingRight)
    {x y : n → R} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ⬝ᵥ M *ᵥ x ≠ 0 ∧ z ⬝ᵥ M *ᵥ y ≠ 0 := by
  obtain ⟨v, hv⟩ := not_forall.mp (mt (separatingRight_def.mp hM x) hx)
  obtain ⟨w, hw⟩ := not_forall.mp (mt (separatingRight_def.mp hM y) hy)
  by_cases hvy : v ⬝ᵥ M *ᵥ y = 0
  · by_cases hwx : w ⬝ᵥ M *ᵥ x = 0
    · exact ⟨v + w, by simpa [add_dotProduct, hwx] using hv,
        by simpa [add_dotProduct, hvy] using hw⟩
    · exact ⟨w, hwx, hw⟩
  · exact ⟨v, hv, hvy⟩

end Matrix.SeparatingRight

namespace Matrix

/-- If `v ⬝ᵥ M *ᵥ a = 0` and `v ⬝ᵥ M *ᵥ z ≠ 0`, then `z` is not a scalar multiple of `a`. -/
theorem notMem_span_of_dotProduct_mulVec {m n R : Type*} [Fintype m] [Fintype n]
    [CommSemiring R] {M : Matrix m n R} {v : m → R} {a z : n → R}
    (ha : v ⬝ᵥ M *ᵥ a = 0) (hz : v ⬝ᵥ M *ᵥ z ≠ 0) : z ∉ R ∙ a := fun hza ↦ by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hza
  simp [mulVec_smul, ha] at hz

/-- Over a commutative semiring without zero divisors, if `v ⬝ᵥ M *ᵥ z = 0`, `v ⬝ᵥ M *ᵥ a ≠ 0`,
and `z ≠ 0`, then `z` is not a scalar multiple of `a`. -/
theorem notMem_span_of_dotProduct_mulVec_of_ne_zero {m n R : Type*} [Fintype m] [Fintype n]
    [CommSemiring R] [NoZeroDivisors R] {M : Matrix m n R} {v : m → R} {a z : n → R}
    (hz : v ⬝ᵥ M *ᵥ z = 0) (ha : v ⬝ᵥ M *ᵥ a ≠ 0) (hz₀ : z ≠ 0) : z ∉ R ∙ a := fun hza ↦ by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hza
  obtain rfl : c = 0 := by simpa [mulVec_smul, ha] using hz
  exact hz₀ (zero_smul R a)

end Matrix
