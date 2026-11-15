/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# Algebraic cancellation in Hopf algebras

The canonical maps `a ⊗ b ↦ Δ(a) (1 ⊗ b)` and `a ⊗ b ↦ (a ⊗ 1) Δ(b)`
are linear equivalences, with inverses given by the antipode. For a bijective
antipode we also construct `a ⊗ b ↦ Δ(a) (b ⊗ 1)` and its inverse using `S⁻¹`.
Consequently, both `Δ(H) (1 ⊗ H)` and `Δ(H) (H ⊗ 1)` span the tensor square.
For Hopf star algebras, bijectivity is supplied by
`TauCeti.HopfAlgebra.antipode_bijective`.

These are linear equivalences, not algebra equivalences: the Hopf algebra need
not be commutative. The span statements supply algebraic surjectivity for the
regular corepresentation before completion in a Haar inner product.

## References

* C. Kassel, *Quantum Groups*, Chapter III, for the antipode cancellation identities.
-/

public section

open TensorProduct Coalgebra WithConv

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

-- This parameterized contraction packages both the canonical map and its inverse.
private noncomputable def rightCanonicalWith (f : H →ₗ[R] H) :
    H ⊗[R] H →ₗ[R] H ⊗[R] H :=
  (LinearMap.mul' R H ∘ₗ f.rTensor H).lTensor H ∘ₗ
    (TensorProduct.assoc R H H H).toLinearMap ∘ₗ
    (Coalgebra.comul (R := R)).rTensor H

private theorem rightCanonicalWith_tmul (f : H →ₗ[R] H) (a b : H) :
    rightCanonicalWith f (a ⊗ₜ[R] b) =
      ∑ i ∈ (ℛ R a).index, (ℛ R a).left i ⊗ₜ[R] (f ((ℛ R a).right i) * b) := by
  simp [rightCanonicalWith, ← (ℛ R a).eq, map_sum, TensorProduct.sum_tmul]

private theorem rightCanonicalWith_comp (f g : H →ₗ[R] H) :
    (rightCanonicalWith f).comp (rightCanonicalWith g) =
      rightCanonicalWith (toConv f * toConv g).ofConv := by
  ext a b
  -- Contract coassociativity by `x ⊗ y ⊗ z ↦ x ⊗ f(y) g(z) b`.
  let P : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    ((LinearMap.mulRight R b).comp
      (LinearMap.mul' R H ∘ₗ TensorProduct.map f g)).lTensor H
  have hc := congrArg P (Coalgebra.sum_tmul_tmul_eq (ℛ R a)
    (fun i ↦ ℛ R ((ℛ R a).left i)) (fun i ↦ ℛ R ((ℛ R a).right i)))
  simpa [P, rightCanonicalWith_tmul, map_sum, (ℛ R _).convMul_apply,
    TensorProduct.tmul_sum, Finset.sum_mul, mul_assoc] using hc

private theorem rightCanonicalWith_one :
    rightCanonicalWith (1 : WithConv (H →ₗ[R] H)).ofConv = LinearMap.id := by
  ext a b
  have hc := congrArg (fun t : H ⊗[R] R ↦ (TensorProduct.rid R H t) ⊗ₜ[R] b)
    (sum_tmul_counit_eq (ℛ R a))
  simpa [rightCanonicalWith_tmul, Algebra.algebraMap_eq_smul_one,
    map_sum, TensorProduct.sum_tmul, TensorProduct.smul_tmul', -sum_tmul_counit_eq] using hc

/-- The canonical right cancellation equivalence of a Hopf algebra. Its forward map is
`a ⊗ b ↦ Δ(a) (1 ⊗ b)` and its inverse uses the antipode on the second coproduct leg. -/
noncomputable def comulMulRightEquiv : H ⊗[R] H ≃ₗ[R] H ⊗[R] H :=
  LinearEquiv.ofLinearMap (rightCanonicalWith LinearMap.id)
    (rightCanonicalWith (HopfAlgebraStruct.antipode R))
    (by rw [rightCanonicalWith_comp, LinearMap.id_mul_antipode, rightCanonicalWith_one])
    (by rw [rightCanonicalWith_comp, LinearMap.antipode_mul_id, rightCanonicalWith_one])

/-- The forward canonical map multiplies a coproduct by the right tensor factor. -/
@[simp]
theorem comulMulRightEquiv_tmul (a b : H) :
    comulMulRightEquiv (R := R) (a ⊗ₜ[R] b) =
      Coalgebra.comul (R := R) a * (1 ⊗ₜ[R] b) := by
  simp [comulMulRightEquiv, rightCanonicalWith_tmul, ← (ℛ R a).eq,
    Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The inverse canonical map applies the antipode on the second coproduct leg. -/
@[simp]
theorem comulMulRightEquiv_symm_tmul (a b : H) :
    (comulMulRightEquiv (R := R)).symm (a ⊗ₜ[R] b) =
      TensorProduct.map LinearMap.id (HopfAlgebraStruct.antipode R)
        (Coalgebra.comul (R := R) a) * (1 ⊗ₜ[R] b) := by
  simp [comulMulRightEquiv, rightCanonicalWith_tmul, ← (ℛ R a).eq,
    map_sum, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- Algebraic right cancellation: the span of `Δ(H) (1 ⊗ H)` is the whole tensor square.
This is a span assertion, not surjectivity of the map on pairs of elements. -/
theorem span_comul_mul_one_tmul :
    Submodule.span R {x : H ⊗[R] H | ∃ a b, Coalgebra.comul (R := R) a * (1 ⊗ₜ[R] b) = x} =
      ⊤ := by
  have h := congrArg (Submodule.map (comulMulRightEquiv (R := R) (H := H)).toLinearMap)
    (TensorProduct.span_tmul_eq_top (R := R) (M := H) (N := H))
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (comulMulRightEquiv (R := R)).surjective] at h
  rw [← h]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ[R] b, ⟨a, b, rfl⟩, comulMulRightEquiv_tmul a b⟩
  · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, (comulMulRightEquiv_tmul a b).symm⟩

-- The mirror contraction multiplies on the left of the first coproduct leg.
private noncomputable def leftCanonicalWith (f : H →ₗ[R] H) :
    H ⊗[R] H →ₗ[R] H ⊗[R] H :=
  (LinearMap.mul' R H ∘ₗ f.lTensor H).rTensor H ∘ₗ
    (TensorProduct.assoc R H H H).symm.toLinearMap ∘ₗ
    (Coalgebra.comul (R := R)).lTensor H

private theorem leftCanonicalWith_tmul (f : H →ₗ[R] H) (a b : H) :
    leftCanonicalWith f (a ⊗ₜ[R] b) =
      ∑ i ∈ (ℛ R b).index, (a * f ((ℛ R b).left i)) ⊗ₜ[R] (ℛ R b).right i := by
  simp [leftCanonicalWith, ← (ℛ R b).eq, map_sum, TensorProduct.tmul_sum]

private theorem leftCanonicalWith_comp (f g : H →ₗ[R] H) :
    (leftCanonicalWith f).comp (leftCanonicalWith g) =
      leftCanonicalWith (toConv g * toConv f).ofConv := by
  ext a b
  -- Multiplication in the first leg reverses the order of convolution.
  let P : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    ((LinearMap.mulLeft R a).comp
      (LinearMap.mul' R H ∘ₗ TensorProduct.map g f)).rTensor H ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have hc := congrArg P (Coalgebra.sum_tmul_tmul_eq (ℛ R b)
    (fun i ↦ ℛ R ((ℛ R b).left i)) (fun i ↦ ℛ R ((ℛ R b).right i)))
  simpa [P, leftCanonicalWith_tmul, map_sum, (ℛ R _).convMul_apply,
    TensorProduct.sum_tmul, Finset.mul_sum, mul_assoc] using hc.symm

private theorem leftCanonicalWith_one :
    leftCanonicalWith (1 : WithConv (H →ₗ[R] H)).ofConv = LinearMap.id := by
  ext a b
  have hc := congrArg (fun t : H ↦ a ⊗ₜ[R] t) (sum_counit_smul (ℛ R b))
  simpa [leftCanonicalWith_tmul, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using hc

/-- The canonical equivalence `a ⊗ b ↦ (a ⊗ 1) Δ(b)`. Unlike cancellation with
`Δ(a) (b ⊗ 1)`, this orientation does not require a bijective antipode. -/
noncomputable def leftMulComulEquiv : H ⊗[R] H ≃ₗ[R] H ⊗[R] H :=
  LinearEquiv.ofLinearMap (leftCanonicalWith LinearMap.id)
    (leftCanonicalWith (HopfAlgebraStruct.antipode R))
    (by rw [leftCanonicalWith_comp, LinearMap.antipode_mul_id, leftCanonicalWith_one])
    (by rw [leftCanonicalWith_comp, LinearMap.id_mul_antipode, leftCanonicalWith_one])

/-- The left-multiplication canonical map on pure tensors. -/
@[simp]
theorem leftMulComulEquiv_tmul (a b : H) :
    leftMulComulEquiv (R := R) (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * Coalgebra.comul (R := R) b := by
  simp [leftMulComulEquiv, leftCanonicalWith_tmul, ← (ℛ R b).eq,
    Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]

/-- Its inverse applies the antipode on the first coproduct leg. -/
@[simp]
theorem leftMulComulEquiv_symm_tmul (a b : H) :
    (leftMulComulEquiv (R := R)).symm (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * TensorProduct.map (HopfAlgebraStruct.antipode R) LinearMap.id
        (Coalgebra.comul (R := R) b) := by
  simp [leftMulComulEquiv, leftCanonicalWith_tmul, ← (ℛ R b).eq,
    map_sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]

section Bijective

variable (hS : Function.Bijective (HopfAlgebraStruct.antipode R : H →ₗ[R] H))

/-- Left cancellation `a ⊗ b ↦ Δ(a) (b ⊗ 1)` for a bijective antipode.
The inverse uses the inverse antipode and the reversed coproduct. -/
noncomputable def comulMulLeftEquiv : H ⊗[R] H ≃ₗ[R] H ⊗[R] H :=
  (TensorProduct.comm R H H).trans <|
    (TensorProduct.congr (LinearEquiv.ofBijective (HopfAlgebraStruct.antipode R) hS)
      (LinearEquiv.refl R H)).trans <|
    (leftMulComulEquiv (R := R)).symm.trans <|
    TensorProduct.congr (LinearEquiv.ofBijective (HopfAlgebraStruct.antipode R) hS).symm
      (LinearEquiv.refl R H)

/-- The left cancellation map multiplies a coproduct by the left tensor factor. -/
@[simp]
theorem comulMulLeftEquiv_tmul (a b : H) :
    comulMulLeftEquiv hS (a ⊗ₜ[R] b) =
      Coalgebra.comul (R := R) a * (b ⊗ₜ[R] 1) := by
  simp only [comulMulLeftEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.ofBijective_apply,
    leftMulComulEquiv_symm_tmul]
  -- Expand the coproduct, so antimultiplicativity cancels the two antipodes termwise.
  simp [← (ℛ R a).eq, map_sum, Finset.sum_mul, Finset.mul_sum,
    ← _root_.HopfAlgebra.antipode_mul_antidistrib, Algebra.TensorProduct.tmul_mul_tmul]

/-- The inverse left cancellation map uses the reversed coproduct and `S⁻¹`. -/
@[simp]
theorem comulMulLeftEquiv_symm_tmul (a b : H) :
    (comulMulLeftEquiv hS).symm (a ⊗ₜ[R] b) =
      TensorProduct.map LinearMap.id (inverseAntipode hS)
        (TensorProduct.comm R H H (Coalgebra.comul (R := R) b)) * (1 ⊗ₜ[R] a) := by
  simp only [comulMulLeftEquiv, LinearEquiv.symm_trans_apply, TensorProduct.congr_symm,
    LinearEquiv.symm_symm, TensorProduct.congr_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, LinearEquiv.ofBijective_apply, leftMulComulEquiv_tmul]
  -- Identify the two inverses through their characteristic equations.
  have hi : ⇑(LinearEquiv.ofBijective (HopfAlgebraStruct.antipode R) hS).symm =
      ⇑(inverseAntipode hS) := by
    funext x
    apply hS.injective
    exact ((LinearEquiv.ofBijective (HopfAlgebraStruct.antipode R) hS).apply_symm_apply x).trans
      (antipode_inverseAntipode hS x).symm
  simp [← (ℛ R b).eq, map_sum, Finset.sum_mul, Finset.mul_sum, hi,
    inverseAntipode_mul, Algebra.TensorProduct.tmul_mul_tmul]

include hS in
/-- Algebraic left cancellation: the span of `Δ(H) (H ⊗ 1)` is the tensor square. -/
theorem span_comul_mul_tmul_one :
    Submodule.span R {x : H ⊗[R] H | ∃ a b, Coalgebra.comul (R := R) a * (b ⊗ₜ[R] 1) = x} =
      ⊤ := by
  have h := congrArg (Submodule.map (comulMulLeftEquiv hS).toLinearMap)
    (TensorProduct.span_tmul_eq_top (R := R) (M := H) (N := H))
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (comulMulLeftEquiv hS).surjective] at h
  rw [← h]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ[R] b, ⟨a, b, rfl⟩, comulMulLeftEquiv_tmul hS a b⟩
  · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, (comulMulLeftEquiv_tmul hS a b).symm⟩

end Bijective

end TauCeti.HopfAlgebra
