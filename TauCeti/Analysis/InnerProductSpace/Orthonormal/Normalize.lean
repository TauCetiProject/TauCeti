/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily

/-!
# Normalizing a pairwise orthogonal basis

Given a finite basis `b` of a real or complex inner product space whose vectors are pairwise
orthogonal (`Pairwise fun i j ↦ ⟪b i, b j⟫_𝕜 = 0`), dividing each vector by its norm produces an
`OrthonormalBasis`. Since every vector of a basis is nonzero, no separate nonvanishing hypothesis is
needed.

## Main declarations

* `Module.Basis.toOrthonormalBasisOfOrthogonal`: the `OrthonormalBasis` obtained by scaling each
  vector `b i` of a pairwise orthogonal finite basis `b` by `(‖b i‖ : 𝕜)⁻¹`.
* `Module.Basis.toOrthonormalBasisOfOrthogonal_apply`: the `i`-th basis vector is
  `(‖b i‖ : 𝕜)⁻¹ • b i`.
* `Module.Basis.toOrthonormalBasisOfOrthogonal_repr_apply`: the `i`-th coordinate of `x` is
  `(‖b i‖ : 𝕜) * b.repr x i`.
* `Module.Basis.toOrthonormalBasisOfOrthogonal_of_orthonormal`: when `b` is already orthonormal,
  normalization agrees with `Module.Basis.toOrthonormalBasis`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Module.Basis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- Normalize a finite pairwise orthogonal basis into an orthonormal basis by dividing each basis
vector by its norm. -/
def toOrthonormalBasisOfOrthogonal (b : Basis ι 𝕜 E)
    (hb : Pairwise fun i j ↦ ⟪b i, b j⟫_𝕜 = 0) : OrthonormalBasis ι 𝕜 E :=
  (b.isUnitSMul (w := fun i ↦ (‖b i‖ : 𝕜)⁻¹) fun i ↦
    (inv_ne_zero (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (b.ne_zero i)))).isUnit
    ).toOrthonormalBasis <| by
    have h := (TauCeti.orthonormal_inv_norm_smul_of_pairwise_inner_eq_zero hb).comp
      (fun i : ι ↦ (⟨i, b.ne_zero i⟩ : {i // b i ≠ 0}))
      (fun i j hij ↦ by simpa using hij)
    convert h using 1
    funext i
    simp [Basis.isUnitSMul_apply]

/-- The `i`-th vector of `b.toOrthonormalBasisOfOrthogonal hb` is `(‖b i‖ : 𝕜)⁻¹ • b i`. -/
@[simp]
theorem toOrthonormalBasisOfOrthogonal_apply (b : Basis ι 𝕜 E)
    (hb : Pairwise fun i j ↦ ⟪b i, b j⟫_𝕜 = 0) (i : ι) :
    b.toOrthonormalBasisOfOrthogonal hb i = (‖b i‖ : 𝕜)⁻¹ • b i := by
  simp [toOrthonormalBasisOfOrthogonal, Basis.coe_toOrthonormalBasis, Basis.isUnitSMul_apply]

/-- The `i`-th coordinate of `x` in `b.toOrthonormalBasisOfOrthogonal hb` is `‖b i‖` times its
`i`-th coordinate in `b`. -/
@[simp]
theorem toOrthonormalBasisOfOrthogonal_repr_apply (b : Basis ι 𝕜 E)
    (hb : Pairwise fun i j ↦ ⟪b i, b j⟫_𝕜 = 0) (x : E) (i : ι) :
    (b.toOrthonormalBasisOfOrthogonal hb).repr x i = (‖b i‖ : 𝕜) * b.repr x i := by
  rw [toOrthonormalBasisOfOrthogonal, coe_toOrthonormalBasis_repr]
  simp [Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val]

/-- When `b` is already orthonormal, normalizing it agrees with
`Module.Basis.toOrthonormalBasis`. -/
theorem toOrthonormalBasisOfOrthogonal_of_orthonormal (b : Basis ι 𝕜 E) (hb : Orthonormal 𝕜 b) :
    b.toOrthonormalBasisOfOrthogonal hb.2 = b.toOrthonormalBasis hb :=
  DFunLike.ext _ _ fun i ↦ by simp [Basis.coe_toOrthonormalBasis, hb.1 i]

end Module.Basis

end
