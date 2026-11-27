/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Tensor
public import TauCeti.Analysis.CStarAlgebra.MinTensor.Norm

/-!
# The minimal and maximal norms on `M_n ⊙ A`

For every, possibly non-unital, C*-algebra `A`, the map `M_n(ℂ) ⊗[ℂ] A → M_n(A)`,
`m ⊗ a ↦ [mᵢⱼ a]`, is a star algebra isomorphism (`TauCeti.cstarMatrixTensorEquiv`, in
`TauCeti.Analysis.CStarAlgebra.Matrix.Tensor`), with inverse `x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ`. Since
`M_n(A)` is a C*-algebra, every injective star homomorphism from `M_n(ℂ) ⊗[ℂ] A` into a
C*-algebra induces the `CStarMatrix` norm (`NonUnitalStarAlgHom.norm_apply_eq_of_bijective`).
In particular the minimal and the maximal norm
on `M_n ⊙ A` coincide with the `CStarMatrix` norm
(`TauCeti.minTensorNorm_eq_norm_cstarMatrixTensorEquiv`,
`TauCeti.maxTensorNorm_eq_norm_cstarMatrixTensorEquiv`), and both norms of `Σ Eᵢⱼ ⊗ aᵢⱼ` are
`‖[aᵢⱼ]‖` (`TauCeti.minTensorNorm_cstarMatrixTensorEquiv_symm`,
`TauCeti.maxTensorNorm_cstarMatrixTensorEquiv_symm`).

That `M_n ⊙ A` carries exactly one C*-norm also needs that the completion of an arbitrary C*-norm
gives an injective star homomorphism into a C*-algebra; that step is not in this file.

## Main declarations

* `TauCeti.minTensorNorm_eq_norm_cstarMatrixTensorEquiv`,
  `TauCeti.maxTensorNorm_eq_norm_cstarMatrixTensorEquiv`: both norms on `M_n(ℂ) ⊗[ℂ] A` are the
  `CStarMatrix` norm, and `TauCeti.minTensorNorm_cstarMatrixTensorEquiv_symm`,
  `TauCeti.maxTensorNorm_cstarMatrixTensorEquiv_symm`: both norms of `Σ Eᵢⱼ ⊗ aᵢⱼ` are `‖[aᵢⱼ]‖`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.4.2.
-/

public section

noncomputable section

open TensorProduct
open scoped ComplexOrder

universe u

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- **The minimal norm on `M_n ⊙ A`** is the `CStarMatrix` norm (Blackadar II.9.4.2). -/
theorem minTensorNorm_eq_norm_cstarMatrixTensorEquiv (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    minTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorEquiv n A x‖ :=
  minTensorNorm_eq_norm_of_bijective
    (Φ := NonUnitalStarAlgHom.ofClass (cstarMatrixTensorEquiv n A))
    (cstarMatrixTensorEquiv n A).bijective x

/-- **The maximal norm on `M_n ⊙ A`** is the `CStarMatrix` norm (Blackadar II.9.4.2). -/
theorem maxTensorNorm_eq_norm_cstarMatrixTensorEquiv (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    maxTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorEquiv n A x‖ :=
  maxTensorNorm_eq_norm_of_bijective
    (Φ := NonUnitalStarAlgHom.ofClass (cstarMatrixTensorEquiv n A))
    (cstarMatrixTensorEquiv n A).bijective x

/-- The minimal norm of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` is the `CStarMatrix` norm of `[aᵢⱼ]`. -/
theorem minTensorNorm_cstarMatrixTensorEquiv_symm (x : CStarMatrix n n A) :
    minTensorNorm (CStarMatrix n n ℂ) A ((cstarMatrixTensorEquiv n A).symm x) = ‖x‖ := by
  rw [minTensorNorm_eq_norm_cstarMatrixTensorEquiv, StarAlgEquiv.apply_symm_apply]

/-- The maximal norm of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` is the `CStarMatrix` norm of `[aᵢⱼ]`. -/
theorem maxTensorNorm_cstarMatrixTensorEquiv_symm (x : CStarMatrix n n A) :
    maxTensorNorm (CStarMatrix n n ℂ) A ((cstarMatrixTensorEquiv n A).symm x) = ‖x‖ := by
  rw [maxTensorNorm_eq_norm_cstarMatrixTensorEquiv, StarAlgEquiv.apply_symm_apply]

end TauCeti
