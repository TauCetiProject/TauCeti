/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Root.Basis
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism

/-!
# Signed root coordinates of the pinned type-A graph automorphism

The native graph map reverses the simple-coroot coordinates and reverses and swaps the
root indices. A root of height `h` acquires the sign `(-1) ^ (h - 1)`.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

private theorem graph_sign_eq_height_sign (i j : Fin (r + 1)) (hij : i ≠ j) :
    (-1 : A) ^ (i.val + j.val + 1) = (-1 : A) ^ (Nat.dist i.val j.val - 1) :=
  (specialLinearRootSign_mul_swap_eq_neg_one_pow r A i j hij).symm.trans
    (specialLinearRootSign_mul_swap r A i j hij)

/-- Signed root vectors transform by reversed indices and the interval-height sign. -/
@[simp]
theorem typeASpecialLinearGraphAutomorphism_signedRoot
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    typeASpecialLinearGraphAutomorphism r A (specialLinearSignedRoot r A i j hij) =
      (-1 : A) ^ (Nat.dist i.val j.val - 1) •
        specialLinearSignedRoot r A j.rev i.rev (Fin.rev_injective.ne hij.symm) := by
  apply Subtype.ext
  simp only [coe_typeASpecialLinearGraphAutomorphism, specialLinearSignedRoot_val,
    typeAGraphLieEquiv_single, SetLike.val_smul, specialLinearSignedRoot_val,
    Matrix.smul_single, smul_eq_mul, specialLinearRootSign_rev_rev]
  rw [graph_sign_eq_height_sign r A i j hij]

/-- On the coroot part of the full basis, the graph map reverses the Dynkin node. -/
theorem typeASpecialLinearGraphAutomorphism_specialLinearRootBasis_inl (i : Fin r) :
    typeASpecialLinearGraphAutomorphism r A (specialLinearRootBasis r A (.inl i)) =
      specialLinearRootBasis r A (.inl i.rev) := by
  simp only [specialLinearRootBasis_inl, specialLinearCorootBasis_apply,
    typeASpecialLinearGraphAutomorphism_coroot]

/-- The graph map reverses the simple-coroot coordinates of every trace-zero matrix. -/
theorem specialLinearRootEquiv_typeASpecialLinearGraphAutomorphism_inl
    (X : sl (Fin (r + 1)) A) (i : Fin r) :
    specialLinearRootEquiv r A (typeASpecialLinearGraphAutomorphism r A X) (.inl i.rev) =
      specialLinearRootEquiv r A X (.inl i) := by
  let f : sl (Fin (r + 1)) A →ₗ[A] A :=
    (LinearMap.proj (.inl i.rev)).comp ((specialLinearRootEquiv r A).toLinearMap.comp
      (typeASpecialLinearGraphAutomorphism r A).toLinearMap)
  let g : sl (Fin (r + 1)) A →ₗ[A] A :=
    (LinearMap.proj (.inl i)).comp (specialLinearRootEquiv r A).toLinearMap
  have h : f = g := by
    apply (specialLinearRootBasis r A).ext
    intro q
    -- Evaluate the coordinate projections and their linear-map compositions.
    change specialLinearRootEquiv r A
      (typeASpecialLinearGraphAutomorphism r A (specialLinearRootBasis r A q)) (.inl i.rev) =
        specialLinearRootEquiv r A (specialLinearRootBasis r A q) (.inl i)
    cases q with
    | inl j =>
      simp only [typeASpecialLinearGraphAutomorphism_specialLinearRootBasis_inl,
        ← specialLinearRootBasis_repr, Module.Basis.repr_self, Finsupp.single_apply,
        Sum.inl.injEq, Fin.rev_inj]
    | inr p =>
      have hroot : typeASpecialLinearGraphAutomorphism r A
          (specialLinearRootBasis r A (.inr p)) =
          (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) •
            specialLinearRootBasis r A
              (.inr ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩) := by
        simp only [specialLinearRootBasis_inr, typeASpecialLinearGraphAutomorphism_signedRoot]
      rw [hroot, map_smul]
      simp only [Pi.smul_apply, ← specialLinearRootBasis_repr, Module.Basis.repr_self,
        Finsupp.single_apply, Sum.inr_ne_inl, ite_false, smul_zero]
  exact DFunLike.congr_fun h X

/-- The graph map permutes the signed root coordinates with the interval-height sign. -/
theorem specialLinearRootEquiv_typeASpecialLinearGraphAutomorphism_inr (X : sl (Fin (r + 1)) A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A (typeASpecialLinearGraphAutomorphism r A X)
        (.inr ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩) =
      (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) *
        specialLinearRootEquiv r A X (.inr p) := by
  simp only [specialLinearRootEquiv_inr, coe_typeASpecialLinearGraphAutomorphism,
    typeAGraphLieEquiv_apply_apply, Fin.rev_rev, specialLinearRootSign_rev_rev]
  have hsign : (-1 : A) ^ (p.val.2.rev.val + p.val.1.rev.val + 1) =
      (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) := by
    rw [graph_sign_eq_height_sign r A p.val.2.rev p.val.1.rev
      (Fin.rev_injective.ne p.property.symm)]
    congr 1
    simp only [Nat.dist, Fin.val_rev]
    omega
  rw [← hsign, pow_add, pow_add, pow_one]
  ring

end TauCeti
