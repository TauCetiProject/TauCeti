/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# The Leibniz rule of a differential graded algebra through the Koszul twist

For an internally `ℤ`-graded differential graded algebra `A`, the Koszul twist
`σ : a ↦ (-1) ^ |a| a` of `TauCeti.InternalGrading.koszulTwist` turns the graded Leibniz rule,
which constrains only a homogeneous left factor, into an identity for arbitrary elements,

`d (a * b) = d a * b + σ a * d b`.

This is the sign rule for the tensor factors of the enveloping algebra `A ⊗ Aᵐᵒᵖ` of a
differential graded algebra, where the elements are sums of pure tensors of inhomogeneous
elements.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.leibniz_koszulTwist`: the Leibniz rule for an arbitrary left
  factor.
* `TauCeti.IsNonUnitalDGAlgebra.koszulTwist_map`: the differential anticommutes with the Koszul
  twist.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}

namespace IsNonUnitalDGAlgebra

/-- The differential of a nonunital DG algebra is homogeneous of degree one for the internal
grading of `𝒜`. -/
theorem isHomogeneous (h : IsNonUnitalDGAlgebra 𝒜 d) :
    LinearMap.IsHomogeneous d (InternalGrading.ofDecomposition 𝒜).piece
      (InternalGrading.ofDecomposition 𝒜).piece 1 := by
  rw [InternalGrading.ofDecomposition_piece]
  exact LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha

/-- **The differential anticommutes with the Koszul twist** `a ↦ (-1) ^ |a| a`, since it has odd
degree. -/
theorem koszulTwist_map (h : IsNonUnitalDGAlgebra 𝒜 d) (a : A) :
    (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 (d a) =
      -d ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a) := by
  rw [h.isHomogeneous.koszulTwist_apply 1 a, mul_one, Int.negOnePow_one, Units.val_neg,
    Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul]

/-- **The Leibniz rule for an arbitrary left factor**: the sign `(-1) ^ |a|` of the graded Leibniz
rule is the Koszul twist `a ↦ (-1) ^ |a| a` of the left factor. -/
theorem leibniz_koszulTwist (h : IsNonUnitalDGAlgebra 𝒜 d) (a b : A) :
    d (a * b) = d a * b + (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a * d b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, map_add, add_mul, add_mul]; abel
  | homogeneous a =>
    obtain ⟨a, hap⟩ := a
    rw [h.leibniz hap, InternalGrading.koszulTwist_ofDecomposition_apply_of_mem _ hap, one_mul,
      smul_mul_assoc, Units.smul_def, Int.cast_smul_eq_zsmul]

end IsNonUnitalDGAlgebra

end TauCeti
