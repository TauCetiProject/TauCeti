/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic

/-!
# Weil restriction preserves products of affine schemes

For a finite projective algebra `B` over `A`, the Weil restriction of a product of finitely
presented affine `B`-schemes is the product of their Weil restrictions. On coordinate rings,
`tensorAlgEquiv` identifies the Weil restriction of `C ⊗[B] D` with the tensor product over `A`
of the Weil restrictions of `C` and `D`.

The comparison respects the two inclusions of coordinate algebras, is natural in both factors,
and commutes with exchanging the factors. Its point formula identifies a point with the pair of
points obtained by restriction to `C` and `D`; thus the comparison fixes the projections, not just
the isomorphism class of the representing algebra. This is the product comparison used when
transporting multiplication maps through restriction of scalars.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, §1.5.3–1.5.4.
* J. S. Milne, *Algebraic Groups*, version 2.00 (2015), §2, 2.38–2.41.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Module.Finite A B] [Module.Projective A B]
  [Algebra B C] [Algebra B D] [Algebra.FinitePresentation B C]
  [Algebra.FinitePresentation B D]

-- Cache the finite-presentation proof for the product, by base change and transitivity.
local instance : Algebra.FinitePresentation B (C ⊗[B] D) :=
  .trans B C (C ⊗[B] D)

-- The universal pair of points, viewed as a point of the product over `B`.
private def tensorPoint : C ⊗[B] D →ₐ[B]
    B ⊗[A] (WeilRestriction A B C ⊗[A] WeilRestriction A B D) :=
  Algebra.TensorProduct.lift
    (homEquiv A B C _ Algebra.TensorProduct.includeLeft)
    (homEquiv A B D _ Algebra.TensorProduct.includeRight) (fun _ _ ↦ .all _ _)

private def toTensor : WeilRestriction A B (C ⊗[B] D) →ₐ[A]
    WeilRestriction A B C ⊗[A] WeilRestriction A B D :=
  (homEquiv A B (C ⊗[B] D) _).symm tensorPoint

private lemma homEquiv_comp_toTensor {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C ⊗[A] WeilRestriction A B D →ₐ[A] T) :
    homEquiv A B (C ⊗[B] D) T (g.comp toTensor) =
      Algebra.TensorProduct.lift
        (homEquiv A B C T (g.comp Algebra.TensorProduct.includeLeft))
        (homEquiv A B D T (g.comp Algebra.TensorProduct.includeRight))
        (fun _ _ ↦ .all _ _) := by
  rw [homEquiv_comp]
  simp only [toTensor, Equiv.apply_symm_apply]
  apply Algebra.TensorProduct.ext'
  intro c d
  simp only [tensorPoint, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
  exact congrArg₂ (· * ·)
    (congr($(homEquiv_comp Algebra.TensorProduct.includeLeft g) c)).symm
    (congr($(homEquiv_comp Algebra.TensorProduct.includeRight g) d)).symm

private lemma toTensor_comp_map_includeLeft :
    (toTensor (A := A) (B := B) (C := C) (D := D)).comp
      (map A B (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] D)) =
        Algebra.TensorProduct.includeLeft := by
  apply (homEquiv A B C _).injective
  rw [homEquiv_comp_map]
  simp [toTensor, tensorPoint]

private lemma toTensor_comp_map_includeRight :
    (toTensor (A := A) (B := B) (C := C) (D := D)).comp
      (map A B (Algebra.TensorProduct.includeRight : D →ₐ[B] C ⊗[B] D)) =
        Algebra.TensorProduct.includeRight := by
  apply (homEquiv A B D _).injective
  rw [homEquiv_comp_map]
  simp [toTensor, tensorPoint]

variable (A B C D) in
/-- Weil restriction along a finite projective algebra preserves products of finitely presented
affine schemes: the coordinate algebra of the restricted product is the tensor product of the
restricted coordinate algebras. -/
def tensorAlgEquiv : WeilRestriction A B (C ⊗[B] D) ≃ₐ[A]
    WeilRestriction A B C ⊗[A] WeilRestriction A B D :=
  AlgEquiv.ofAlgHom toTensor
    (Algebra.TensorProduct.lift
      (map A B Algebra.TensorProduct.includeLeft)
      (map A B Algebra.TensorProduct.includeRight) (fun _ _ ↦ .all _ _))
    (by
      apply Algebra.TensorProduct.ext'
      intro c d
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.id_apply]
      rw [← AlgHom.comp_apply, toTensor_comp_map_includeLeft,
        ← AlgHom.comp_apply, toTensor_comp_map_includeRight]
      simp)
    (by
      apply (homEquiv A B (C ⊗[B] D) _).injective
      rw [homEquiv_comp_toTensor]
      simp only [Algebra.TensorProduct.lift_comp_includeLeft,
        Algebra.TensorProduct.lift_comp_includeRight', homEquiv_map]
      apply Algebra.TensorProduct.ext'
      intro c d
      simp [← map_mul])

/-- The product comparison sends the restricted left inclusion to the left tensor inclusion. -/
@[simp]
theorem tensorAlgEquiv_comp_map_includeLeft :
    (tensorAlgEquiv A B C D).toAlgHom.comp
      (map A B (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] D)) =
        Algebra.TensorProduct.includeLeft :=
  toTensor_comp_map_includeLeft

/-- The product comparison sends the restricted right inclusion to the right tensor inclusion. -/
@[simp]
theorem tensorAlgEquiv_comp_map_includeRight :
    (tensorAlgEquiv A B C D).toAlgHom.comp
      (map A B (Algebra.TensorProduct.includeRight : D →ₐ[B] C ⊗[B] D)) =
        Algebra.TensorProduct.includeRight :=
  toTensor_comp_map_includeRight

/-- The inverse product comparison sends a pure tensor to the product of the two restricted
coordinate inclusions. -/
@[simp]
theorem tensorAlgEquiv_symm_tmul (c : WeilRestriction A B C) (d : WeilRestriction A B D) :
    (tensorAlgEquiv A B C D).symm (c ⊗ₜ[A] d) =
      map A B (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] D) c *
        map A B (Algebra.TensorProduct.includeRight : D →ₐ[B] C ⊗[B] D) d :=
  (rfl)

/-- On points the product comparison pairs the points classified by restriction to the two
factors. This characterizes the comparison with its projections. -/
theorem homEquiv_comp_tensorAlgEquiv {T : Type*} [CommRing T] [Algebra A T]
    (g : WeilRestriction A B C ⊗[A] WeilRestriction A B D →ₐ[A] T) :
    homEquiv A B (C ⊗[B] D) T (g.comp (tensorAlgEquiv A B C D).toAlgHom) =
      Algebra.TensorProduct.lift
        (homEquiv A B C T (g.comp Algebra.TensorProduct.includeLeft))
        (homEquiv A B D T (g.comp Algebra.TensorProduct.includeRight))
        (fun _ _ ↦ .all _ _) :=
  homEquiv_comp_toTensor g

/-- The inverse comparison restricts on the left tensor factor to the restricted inclusion. -/
@[simp]
theorem tensorAlgEquiv_symm_comp_includeLeft :
    (tensorAlgEquiv A B C D).symm.toAlgHom.comp Algebra.TensorProduct.includeLeft =
      map A B (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] D) := by
  apply AlgHom.ext
  intro c
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply, tensorAlgEquiv_symm_tmul, map_one, mul_one]

/-- The inverse comparison restricts on the right tensor factor to the restricted inclusion. -/
@[simp]
theorem tensorAlgEquiv_symm_comp_includeRight :
    (tensorAlgEquiv A B C D).symm.toAlgHom.comp Algebra.TensorProduct.includeRight =
      map A B (Algebra.TensorProduct.includeRight : D →ₐ[B] C ⊗[B] D) := by
  apply AlgHom.ext
  intro d
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    Algebra.TensorProduct.includeRight_apply, tensorAlgEquiv_symm_tmul, map_one, one_mul]

/-- The product comparison is natural in both coordinate algebras. -/
theorem tensorAlgEquiv_natural {C' D' : Type*} [CommRing C'] [CommRing D']
    [Algebra B C'] [Algebra B D'] [Algebra.FinitePresentation B C']
    [Algebra.FinitePresentation B D'] (f : C →ₐ[B] C') (g : D →ₐ[B] D') :
    (tensorAlgEquiv A B C' D').toAlgHom.comp (map A B (Algebra.TensorProduct.map f g)) =
      (Algebra.TensorProduct.map (map A B f) (map A B g)).comp
        (tensorAlgEquiv A B C D).toAlgHom := by
  apply (homEquiv A B (C ⊗[B] D) _).injective
  have h := homEquiv_comp_tensorAlgEquiv (A := A) (B := B) (C := C') (D := D')
    (AlgHom.id A _)
  simp only [AlgHom.id_comp] at h
  rw [homEquiv_comp_map, h, homEquiv_comp_tensorAlgEquiv,
    Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight,
    homEquiv_comp_map, homEquiv_comp_map]
  apply Algebra.TensorProduct.ext'
  intro c d
  simp

/-- Exchanging the two factors before or after restriction of scalars gives the same map. -/
theorem tensorAlgEquiv_comm :
    (Algebra.TensorProduct.comm A (WeilRestriction A B C) (WeilRestriction A B D)).toAlgHom.comp
        (tensorAlgEquiv A B C D).toAlgHom =
      (tensorAlgEquiv A B D C).toAlgHom.comp
        (map A B (Algebra.TensorProduct.comm B C D).toAlgHom) := by
  apply (homEquiv A B (C ⊗[B] D) _).injective
  have h := homEquiv_comp_tensorAlgEquiv (A := A) (B := B) (C := D) (D := C)
    (AlgHom.id A _)
  simp only [AlgHom.id_comp] at h
  rw [homEquiv_comp_tensorAlgEquiv, homEquiv_comp_map, h,
    Algebra.TensorProduct.comm_comp_includeLeft, Algebra.TensorProduct.comm_comp_includeRight]
  apply Algebra.TensorProduct.ext'
  intro c d
  simp [mul_comm]

end TauCeti.Algebra.WeilRestriction
