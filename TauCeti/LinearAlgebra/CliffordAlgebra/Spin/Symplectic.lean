/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The even unitary carrier as a symplectic group

An algebra isomorphism from the even Clifford algebra `C₀` to a matrix algebra of even size which
carries reversal `σ` to the standard symplectic adjoint `X ↦ J⁻¹ Xᵀ J = -(J Xᵀ J)` identifies the
reverse-unitary carrier `U(C₀, σ)` with Mathlib's `Matrix.symplecticGroup`. This is a
specialisation of `CliffordAlgebra.evenUnitaryGroupEquivOfAlgEquiv`, valid over any commutative
ring and with no assumption on the dimension.

## Main definitions

* `CliffordAlgebra.evenUnitaryGroupEquivSymplecticGroup`: an algebra isomorphism from `C₀` to a
  matrix algebra carrying `σ` to the symplectic adjoint identifies `U(C₀, σ)` with the symplectic
  group.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §8.D.
-/

public section

open Matrix

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
  {l : Type*} [Fintype l] [DecidableEq l]

/-- An algebra isomorphism from the even Clifford algebra to a matrix algebra of even size which
carries reversal to the symplectic adjoint `X ↦ -(J Xᵀ J)` identifies the even unitary carrier
`U(C₀, σ)` with the symplectic group. -/
noncomputable def evenUnitaryGroupEquivSymplecticGroup
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) :
    evenUnitaryGroup Q ≃* symplecticGroup l R :=
  evenUnitaryGroupEquivOfAlgEquiv Q e (· ∈ symplecticGroup l R) (symplecticGroup l R).subtype
    Subtype.val_injective (fun a ha => ⟨a, ha⟩) (fun _ _ => rfl) (fun g => g.2) fun x => by
      rw [SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one, ← Matrix.neg_mul, ← he,
        ← map_mul, ← map_one e, e.injective.eq_iff]

/-- The symplectic transport applies the algebra isomorphism to the even Clifford value. -/
@[simp]
theorem coe_evenUnitaryGroupEquivSymplecticGroup_apply
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupEquivSymplecticGroup Q e he x : Matrix (l ⊕ l) (l ⊕ l) R) =
      e (evenUnitaryGroupEvenPart Q x) := by
  rw [evenUnitaryGroupEquivSymplecticGroup]
  exact coe_evenUnitaryGroupEquivOfAlgEquiv_apply Q e _ (symplecticGroup l R).subtype _ _ _ _ _ x

/-- The inverse symplectic transport applies the inverse algebra isomorphism. -/
@[simp]
theorem evenUnitaryGroupEvenPart_evenUnitaryGroupEquivSymplecticGroup_symm_apply
    (e : even Q ≃ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R)
    (he : ∀ x, e (reverseEven Q x) = -(J l R * (e x)ᵀ * J l R)) (g : symplecticGroup l R) :
    evenUnitaryGroupEvenPart Q ((evenUnitaryGroupEquivSymplecticGroup Q e he).symm g) =
      e.symm g := by
  rw [evenUnitaryGroupEquivSymplecticGroup]
  exact evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart Q e _ (symplecticGroup l R).subtype
    _ _ _ _ _ g

end CliffordAlgebra
