/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic

/-!
# The symplectic form of the symplectic matrices

Mathlib's real symplectic matrices `Matrix.symplecticGroup (Fin n) ℝ`, the matrices `A` with
`A * J * Aᵀ = J`, are defined through the canonical skew-symmetric matrix
`J = Matrix.J (Fin n) ℝ`. The alternating form `u ⬝ᵥ J w` behind them is
`TauCeti.stdSymplecticBilinForm ℝ n`. This file bundles it as a symplectic form
`TauCeti.stdSumSymplecticForm n` on `ℝ²ⁿ = Fin n ⊕ Fin n → ℝ`,

`ω(u, w) = u ⬝ᵥ J w = ∑ i, (u (inr i) * w (inl i) - u (inl i) * w (inr i))`

(`TauCeti.stdSumSymplecticForm_apply_eq_sum`), so that the symplectic matrices are the linear
symmetries of a symplectic vector space in the sense of `TauCeti.SymplecticForm`: a matrix
preserves `ω` exactly when it is symplectic (`TauCeti.stdSumSymplecticForm_mulVec_mulVec_iff`).
Its bilinear form is `TauCeti.stdSymplecticBilinForm ℝ n`
(`TauCeti.stdSumSymplecticForm_toBilinForm`), so the infinitesimal symmetries are described by
`TauCeti.toLin'_mem_skewAdjointLieSubalgebra_stdSymplecticBilinForm_iff`.

This is the linear model on which the real symplectic group acts, and the input for its moment
map in `TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.SymplecticGroup`.

## Main definitions

* `TauCeti.stdSumSymplecticForm n`: the symplectic form `u ⬝ᵥ J w` on `Fin n ⊕ Fin n → ℝ`.

## Main results

* `TauCeti.stdSumSymplecticForm_mulVec_mulVec_iff`: the linear symplectomorphisms of
  `stdSumSymplecticForm n` are the symplectic matrices.
* `TauCeti.stdSumSymplecticForm_smul_smul`: the symplectic group acts by linear
  symplectomorphisms of `stdSumSymplecticForm n`.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable (n : ℕ)

/-- The **standard symplectic form on `Fin n ⊕ Fin n → ℝ`**: the form `ω(u, w) = u ⬝ᵥ J w` with
Gram matrix Mathlib's canonical skew-symmetric matrix `J = Matrix.J (Fin n) ℝ`, that is
`TauCeti.stdSymplecticBilinForm ℝ n` bundled as a symplectic form. In coordinates it is
`∑ i, dpᵢ ∧ dqᵢ` for `qᵢ = inl i` and `pᵢ = inr i` (`TauCeti.stdSumSymplecticForm_apply_eq_sum`). -/
def stdSumSymplecticForm : SymplecticForm (Fin n ⊕ Fin n → ℝ) where
  toBilinForm := stdSymplecticBilinForm ℝ n
  isAlt := isAlt_stdSymplecticBilinForm ℝ n
  nondegenerate := stdSymplecticBilinForm_nondegenerate ℝ n

variable {n}

/-- The bilinear form of the standard symplectic form is `TauCeti.stdSymplecticBilinForm ℝ n`. -/
theorem stdSumSymplecticForm_toBilinForm :
    (stdSumSymplecticForm n).toBilinForm = stdSymplecticBilinForm ℝ n :=
  (rfl)

/-- The standard symplectic form is `ω(u, w) = u ⬝ᵥ J w`. -/
@[simp]
theorem stdSumSymplecticForm_apply (u w : Fin n ⊕ Fin n → ℝ) :
    stdSumSymplecticForm n u w = u ⬝ᵥ J (Fin n) ℝ *ᵥ w :=
  stdSymplecticBilinForm_apply ℝ n u w

/-- The standard symplectic form in coordinates: `ω = ∑ i, dpᵢ ∧ dqᵢ` for `qᵢ = inl i` and
`pᵢ = inr i`. -/
theorem stdSumSymplecticForm_apply_eq_sum (u w : Fin n ⊕ Fin n → ℝ) :
    stdSumSymplecticForm n u w =
      ∑ i, (u (Sum.inr i) * w (Sum.inl i) - u (Sum.inl i) * w (Sum.inr i)) := by
  simp [J, fromBlocks_mulVec, neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Finset.sum_add_distrib, sub_eq_neg_add]

/-- **The linear symplectomorphisms of `u ⬝ᵥ J w` are the symplectic matrices.** A matrix `A`
preserves the standard symplectic form, `ω(A u, A w) = ω(u, w)` for all `u` and `w`, exactly when
it lies in `Matrix.symplecticGroup (Fin n) ℝ`. This is `TauCeti.toMatrix'_mem_symplecticGroup_iff`
for the endomorphism `toLin' A`. -/
theorem stdSumSymplecticForm_mulVec_mulVec_iff (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (∀ u w, stdSumSymplecticForm n (A *ᵥ u) (A *ᵥ w) = stdSumSymplecticForm n u w) ↔
      A ∈ symplecticGroup (Fin n) ℝ := by
  simpa [BilinForm.isIsometry_iff] using
    (toMatrix'_mem_symplecticGroup_iff ℝ n (f := toLin' A)).symm

/-- Symplectic matrices preserve the standard symplectic form: `ω(A u, A w) = ω(u, w)`. -/
theorem stdSumSymplecticForm_mulVec_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ symplecticGroup (Fin n) ℝ) (u w : Fin n ⊕ Fin n → ℝ) :
    stdSumSymplecticForm n (A *ᵥ u) (A *ᵥ w) = stdSumSymplecticForm n u w :=
  LinearMap.congr_fun₂ (stdSymplecticBilinForm_comp_stdSymplecticRep ℝ n ⟨A, hA⟩) u w

/-- The symplectic group acts by linear symplectomorphisms of `u ⬝ᵥ J w`. -/
theorem stdSumSymplecticForm_smul_smul (g : symplecticGroup (Fin n) ℝ)
    (u w : Fin n ⊕ Fin n → ℝ) :
    stdSumSymplecticForm n (g • u) (g • w) = stdSumSymplecticForm n u w :=
  stdSumSymplecticForm_mulVec_mulVec g.property u w

end TauCeti
