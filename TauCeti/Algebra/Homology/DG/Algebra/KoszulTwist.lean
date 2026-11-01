/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# The Koszul twist of a differential graded algebra

For an internally `ℤ`-graded algebra `A`, the Koszul twist `σ : a ↦ (-1) ^ |a| a` of
`TauCeti.InternalGrading.koszulTwist` is multiplicative, since degrees add under multiplication.
For a differential graded algebra it turns the graded Leibniz rule, which constrains only a
homogeneous left factor, into an identity for arbitrary elements,

`d (a * b) = d a * b + σ a * d b`,

and, since `d` raises degrees by one, it anticommutes with the differential: `d ∘ σ = -σ ∘ d`.
These are the sign rules for the tensor factors of the enveloping algebra `A ⊗ Aᵐᵒᵖ` of a
differential graded algebra, where the elements are sums of pure tensors of inhomogeneous
elements.

## Main results

* `TauCeti.InternalGrading.koszulTwist_ofDecomposition_mul`: the Koszul twist of a graded algebra
  is multiplicative.
* `TauCeti.IsNonUnitalDGAlgebra.leibniz_koszulTwist`: the Leibniz rule for an arbitrary left
  factor.
* `TauCeti.IsNonUnitalDGAlgebra.map_koszulTwist`: the differential anticommutes with the Koszul
  twist.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention `d (a * b) = d a * b + (-1) ^ |a| * (a * d b)`.
-/

public section

namespace TauCeti

section Twist

variable {R A : Type*} [CommRing R] [AddCommMonoid A] [Module R A] {𝒜 : ℤ → Submodule R A}
  [DirectSum.Decomposition 𝒜]

/-- The Koszul twist of a homogeneous element of degree `p` is the sign `(-1) ^ (q p)`, read in the
grading of a decomposition. -/
private theorem koszulTwist_ofDecomposition_apply_of_mem {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (q : ℤ) :
    (InternalGrading.ofDecomposition 𝒜).koszulTwist q a = (((q * p).negOnePow : ℤ) : R) • a :=
  InternalGrading.koszulTwist_apply_of_mem _
    (by rwa [InternalGrading.ofDecomposition_piece]) q

end Twist

section Mul

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]

/-- **The Koszul twist of a graded algebra is multiplicative**: degrees add under multiplication,
so the signs `(-1) ^ (q |a|)` multiply. -/
theorem InternalGrading.koszulTwist_ofDecomposition_mul (q : ℤ) (a b : A) :
    (InternalGrading.ofDecomposition 𝒜).koszulTwist q (a * b) =
      (InternalGrading.ofDecomposition 𝒜).koszulTwist q a *
        (InternalGrading.ofDecomposition 𝒜).koszulTwist q b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]
  | homogeneous a =>
    obtain ⟨a, hap⟩ := a
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
    | homogeneous b =>
      obtain ⟨b, hbq⟩ := b
      rw [koszulTwist_ofDecomposition_apply_of_mem (SetLike.GradedMul.mul_mem hap hbq),
        koszulTwist_ofDecomposition_apply_of_mem hap, koszulTwist_ofDecomposition_apply_of_mem hbq,
        smul_mul_smul_comm, mul_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

end Mul

section DG

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] {d : A →ₗ[R] A}

namespace IsNonUnitalDGAlgebra

/-- **The Leibniz rule for an arbitrary left factor**: the sign `(-1) ^ |a|` of the graded Leibniz
rule is the Koszul twist `a ↦ (-1) ^ |a| a` of the left factor. -/
theorem leibniz_koszulTwist (h : IsNonUnitalDGAlgebra 𝒜 d) (a b : A) :
    d (a * b) = d a * b + (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a * d b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, map_add, add_mul, add_mul]; abel
  | homogeneous a =>
    obtain ⟨a, hap⟩ := a
    rw [h.leibniz hap, koszulTwist_ofDecomposition_apply_of_mem hap, one_mul, smul_mul_assoc,
      Units.smul_def, Int.cast_smul_eq_zsmul]

/-- **The differential anticommutes with the Koszul twist** `a ↦ (-1) ^ |a| a`, since it raises
degrees by one. -/
theorem map_koszulTwist (h : IsNonUnitalDGAlgebra 𝒜 d) (a : A) :
    d ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a) =
      -(InternalGrading.ofDecomposition 𝒜).koszulTwist 1 (d a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [map_add, map_add, ha, ha', map_add, map_add, neg_add]
  | homogeneous a =>
    obtain ⟨a, hap⟩ := a
    rw [koszulTwist_ofDecomposition_apply_of_mem hap,
      koszulTwist_ofDecomposition_apply_of_mem (h.map_mem hap), map_smul, one_mul, one_mul,
      Int.negOnePow_succ, Units.val_neg, Int.cast_neg, neg_smul, neg_neg]

end IsNonUnitalDGAlgebra

end DG

end TauCeti
