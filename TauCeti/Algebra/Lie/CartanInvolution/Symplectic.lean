/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# The standard Cartan involution on the symplectic Lie algebra

Over any ordered field `K`, the negative-transpose involution
`LieAlgebra.Symplectic.cartanInvolution l K : sp l K ≃ₗ⁅K⁆ sp l K` is a Cartan involution in
the sense of `LieEquiv.IsCartanInvolution`
(`LieAlgebra.Symplectic.isCartanInvolution_cartanInvolution`). Its `+1`-eigenspace consists of the
skew-symmetric symplectic matrices and its `-1`-eigenspace consists of the symmetric symplectic
matrices. For nonempty `l`, the symplectic Lie algebra is noncompact: the identity automorphism is
not a Cartan involution (`LieAlgebra.Symplectic.not_isCartanInvolution_refl`).

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Chapter VI, §2.
-/

public section

namespace LieAlgebra.Symplectic

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Negative transpose `X ↦ -Xᵀ` is a Cartan involution of the symplectic Lie algebra `sp l K`
over any ordered field `K`. -/
theorem isCartanInvolution_cartanInvolution (l : Type*) [Fintype l] [DecidableEq l]
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (cartanInvolution l K).IsCartanInvolution where
  involutive := cartanInvolution_cartanInvolution
  neg_killingForm_pos _ hX := neg_pos.mpr (killingForm_cartanInvolution_self_neg hX)

/-- The fixed subalgebra `𝔨` of `cartanInvolution l R` consists of the skew-symmetric matrices in
`sp l R`. -/
theorem mem_fixedSubalgebra_cartanInvolution {l : Type*} [Fintype l] [DecidableEq l]
    {R : Type*} [CommRing R] {X : sp l R} :
    X ∈ (cartanInvolution l R).toLieHom.fixedSubalgebra ↔
      (X : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = -(X : Matrix (l ⊕ l) (l ⊕ l) R) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, cartanInvolution_eq_self_iff]

/-- The `-1`-eigenspace `𝔭` of `cartanInvolution l R` consists of the symmetric matrices in
`sp l R`. -/
theorem mem_cartanP_cartanInvolution {l : Type*} [Fintype l] [DecidableEq l]
    {R : Type*} [CommRing R] {X : sp l R} :
    X ∈ (cartanInvolution l R).cartanP ↔
      (X : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (X : Matrix (l ⊕ l) (l ⊕ l) R) := by
  rw [LieEquiv.mem_cartanP, cartanInvolution_eq_neg_iff]

/-- For nonempty `l`, the symplectic Lie algebra `sp l K` over an ordered field is noncompact: the
identity automorphism is not a Cartan involution. -/
theorem not_isCartanInvolution_refl (l : Type*) [Fintype l] [DecidableEq l] [Nonempty l]
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ¬ (LieEquiv.refl : sp l K ≃ₗ⁅K⁆ sp l K).IsCartanInvolution := by
  intro hrefl
  let Hmat : Matrix (l ⊕ l) (l ⊕ l) K := Matrix.fromBlocks 1 0 0 (-1)
  have hHmem : Hmat ∈ sp l K := by
    simp [Hmat, mem_sp, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_neg]
  let H : sp l K := ⟨Hmat, hHmem⟩
  have hHne : H ≠ 0 := by
    intro h0
    have hval := congrArg (fun M : sp l K ↦
      (M : Matrix (l ⊕ l) (l ⊕ l) K) (Sum.inl (Classical.arbitrary l))
        (Sum.inl (Classical.arbitrary l))) h0
    simp [H, Hmat] at hval
  have hHp : H ∈ (cartanInvolution l K).cartanP := by
    rw [mem_cartanP_cartanInvolution]
    simp [H, Hmat, Matrix.fromBlocks_transpose]
  have hpos : 0 < killingForm K (sp l K) H H :=
    (isCartanInvolution_cartanInvolution l K).killingForm_pos_of_mem_cartanP hHp hHne
  have hneg : killingForm K (sp l K) H H < 0 :=
    (LieEquiv.isCartanInvolution_refl_iff_neg.mp hrefl) H hHne
  exact lt_asymm hpos hneg

end LieAlgebra.Symplectic
