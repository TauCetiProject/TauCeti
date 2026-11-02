/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The inverse-transpose involution of the symplectic group

On the symplectic group, inverse transpose is conjugation by the standard alternating
matrix `J`. It therefore preserves the group over every commutative ring. Over the reals,
its fixed subgroup is the orthogonal symplectic subgroup, identified with the realified
unitary group by `TauCeti.GLSymplectic.inf_unitarySubgroup`.

The construction reuses `Matrix.GeneralLinearGroup.inverseTranspose` and `MulAut.conj`.
Its infinitesimal counterpart is negative transpose on the symplectic Lie algebra.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.2 (the symplectic linear group).
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition.
-/

public section

namespace TauCeti.GLSymplectic

open Matrix Matrix.GeneralLinearGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

/-- The inverse-transpose involution on the symplectic group, realized as conjugation by `J`. -/
def cartanInvolution : GLSymplectic l R ≃* GLSymplectic l R :=
  MulAut.conj (symJ l R)

/-- The symplectic inverse-transpose involution is inner. -/
theorem cartanInvolution_apply (g : GLSymplectic l R) :
    cartanInvolution g = symJ l R * g * (symJ l R)⁻¹ :=
  (rfl)

/-- In ambient general-linear coordinates the involution is inverse transpose. -/
@[simp]
theorem coe_cartanInvolution (g : GLSymplectic l R) :
    (cartanInvolution g : GL (l ⊕ l) R) = inverseTranspose (g : GL (l ⊕ l) R) := by
  apply Units.ext
  rw [cartanInvolution_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_symJ,
    coe_inverseTranspose, coe_units_inv]
  rw [SymplecticGroup.inv_eq_symplectic_inv _ (mem_iff_mem_symplecticGroup.mp g.property)]
  simp [transpose_mul, J_transpose, J_inv, mul_assoc]

/-- Applying the symplectic inverse-transpose involution twice is the identity. -/
@[simp]
theorem cartanInvolution_cartanInvolution (g : GLSymplectic l R) :
    cartanInvolution (cartanInvolution g) = g := by
  apply Subtype.ext
  simp only [coe_cartanInvolution, inverseTranspose_inverseTranspose]

/-- The symplectic inverse-transpose involution is its own inverse automorphism. -/
@[simp]
theorem cartanInvolution_symm :
    (cartanInvolution : GLSymplectic l R ≃* GLSymplectic l R).symm = cartanInvolution := by
  apply MulEquiv.ext
  intro g
  rw [MulEquiv.symm_apply_eq, cartanInvolution_cartanInvolution]

/-- The fixed points are exactly the orthogonal symplectic elements. -/
@[simp]
theorem cartanInvolution_eq_self_iff (g : GLSymplectic l R) :
    cartanInvolution g = g ↔
      ((g : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) ∈ orthogonalGroup (l ⊕ l) R := by
  rw [← Subtype.coe_inj, coe_cartanInvolution, ← Units.val_inj,
    coe_inverseTranspose, mem_orthogonalGroup_iff]
  constructor
  · intro h
    have ht := congrArg Matrix.transpose h
    simp only [transpose_transpose] at ht
    rw [← ht, Units.mul_inv]
  · intro h
    have hinv : ((g.val⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
        (g.val : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ := by
      exact left_inv_eq_right_inv (Units.inv_mul g.val) h
    simp [hinv]

end TauCeti.GLSymplectic
