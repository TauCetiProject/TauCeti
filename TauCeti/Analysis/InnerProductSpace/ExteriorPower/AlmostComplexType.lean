/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Complexification
public import TauCeti.LinearAlgebra.ExteriorPower.AlmostComplexType

/-!
# Gram orthogonality of exterior types

Distinct `(p,q)` types in a fixed exterior degree are orthogonal for the Hermitian
complexification of the real Gram metric. Consequently the Gram pairing of two finite type
decompositions is the sum of the pairings of their matching components. These are pointwise
metric identities underlying the orthogonal type splitting of complex differential forms.

The hypothesis is skew-adjointness of the real endomorphism `J`; an orthogonal complex
structure satisfies it, but its square is not needed here. The metric is the Gram-determinant
metric on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`, conjugate-linear in the first slot. The statements use the existing
`exteriorPower.typeSubmodule`, not a second type carrier. Under the metric identification with
covectors the two type indices are exchanged; this does not affect orthogonality.

The argument uses `exteriorPower.inner_lieMap_left` and the skew-adjoint complexification
identity for real bilinear forms.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 1.2.
-/

public noncomputable section

open Module
open scoped TensorProduct RealInnerProductSpace

namespace exteriorPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {J : V →ₗ[ℝ] V} {k p q r s : ℕ}

/-- Distinct exterior types of the same degree are orthogonal for the Hermitian Gram metric.
The conclusion also covers type submodules whose indices do not sum to the degree. -/
theorem sesqComplexification_eq_zero_of_mem_typeSubmodule
    (hJ : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫) (hne : (p, q) ≠ (r, s))
    {x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V} (hx : x ∈ typeSubmodule k J p q)
    (hy : y ∈ typeSubmodule k J r s) :
    LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y = 0 := by
  by_cases hpq : p + q = k
  swap
  · rw [typeSubmodule_eq_bot hpq, Submodule.mem_bot] at hx
    simp [hx]
  by_cases hrs : r + s = k
  swap
  · rw [typeSubmodule_eq_bot hrs, Submodule.mem_bot] at hy
    simp [hy]
  have hev : starRingEnd ℂ (((p : ℂ) - q) * Complex.I) +
      ((r : ℂ) - s) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    have hsums : (p : ℝ) + q = r + s := by exact_mod_cast hpq.trans hrs.symm
    have hp : (p : ℝ) = r := by linarith
    have hq : (q : ℝ) = s := by linarith
    exact hne (Prod.ext (by exact_mod_cast hp) (by exact_mod_cast hq))
  exact LinearMap.BilinForm.sesqComplexification_eq_zero_of_mem_eigenspace_of_skewAdjoint
    (innerₗ (⋀[ℝ]^k V)) (inner_lieMap_left hJ) hev
    (Module.End.mem_eigenspace_iff.mpr ((mem_typeSubmodule hpq).mp hx))
    (Module.End.mem_eigenspace_iff.mpr ((mem_typeSubmodule hrs).mp hy))

/-- Pairing two type decompositions discards every cross term. This statement requires only
that the supplied components have the indicated types, not a chosen basis or projections. -/
theorem sesqComplexification_sum_antidiagonal
    (hJ : ∀ u v, ⟪J u, v⟫ = -⟪u, J v⟫)
    (x y : ℕ × ℕ → ℂ ⊗[ℝ] ⋀[ℝ]^k V)
    (hx : ∀ a ∈ Finset.antidiagonal k, x a ∈ typeSubmodule k J a.1 a.2)
    (hy : ∀ a ∈ Finset.antidiagonal k, y a ∈ typeSubmodule k J a.1 a.2) :
    LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))
        (∑ a ∈ Finset.antidiagonal k, x a) (∑ a ∈ Finset.antidiagonal k, y a) =
      ∑ a ∈ Finset.antidiagonal k,
        LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) (x a) (y a) := by
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact sesqComplexification_eq_zero_of_mem_typeSubmodule hJ
      (by simpa only [Prod.mk.eta] using hba) (hx b hb) (hy a ha)
  · simp_all

end exteriorPower
