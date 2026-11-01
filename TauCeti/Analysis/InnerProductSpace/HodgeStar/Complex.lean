/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.Complexification

/-!
# The complex-linear Hodge star and the conjugate Hodge star

The real Hodge star extends complex-linearly to `ℂ ⊗[ℝ] ⋀[ℝ]^k V`. The Gram metric on
this space is the sesquilinear complexification of the real exterior-power inner product;
it is conjugate-linear in the first slot. The volume coefficient of a wedge of complementary
complexified exterior powers is `Orientation.complexWedgePairing`.

These conventions distinguish two operators. The complex-linear `Orientation.complexHodgeStar`
satisfies `α ∧ *β = B_ℂ(α, β) vol = h(conj α, β) vol`, where `B_ℂ` is the bilinear
extension of the real Gram product. The conjugate-linear `Orientation.barHodgeStar` is
`β ↦ *(conj β)` and satisfies `α ∧ barStar β = h(β, α) vol`. Both have square
`(-1)^(k*l)` in complementary degrees and preserve the Gram metric (the latter with
conjugation). These pointwise identities supply the pairing conventions for complex-valued
forms; no integrability or almost complex structure on `V` is required.

All constructions use the tensor complexification, Mathlib's scalar extension of linear maps,
and `LinearMap.BilinForm.sesqComplexification`. In particular, the exterior-power metric is
the Gram-determinant metric, not the sum over all ordered tuples.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, §6.1.
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2.
-/

public noncomputable section

open Module exteriorPower TauCeti
open scoped TensorProduct RealInnerProductSpace ComplexOrder

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  (o : Orientation ℝ V (Fin n))

/-- The complex-linear extension of the real Hodge star to the complexified exterior powers. -/
def complexHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    ℂ ⊗[ℝ] ⋀[ℝ]^k V ≃ₗ[ℂ] ℂ ⊗[ℝ] ⋀[ℝ]^l V :=
  (o.hodgeStar hkl).baseChange ℝ ℂ _ _

/-- The complex Hodge star leaves the scalar factor unchanged. -/
@[simp]
theorem complexHodgeStar_tmul {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (c : ℂ) (x : ⋀[ℝ]^k V) :
    o.complexHodgeStar hkl (c ⊗ₜ x) = c ⊗ₜ o.hodgeStar hkl x :=
  (rfl)

/-- The complex Hodge star commutes with conjugation of the coefficients. -/
theorem tmulConj_complexHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    tmulConj _ (o.complexHodgeStar hkl x) = o.complexHodgeStar hkl (tmulConj _ x) :=
  tmulConj_baseChange (o.hodgeStar hkl).toLinearMap x

/-- The square of the complex-linear Hodge star in complementary degrees. -/
theorem complexHodgeStar_complexHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (hlk : l + k = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    o.complexHodgeStar hlk (o.complexHodgeStar hkl x) = (-1 : ℂ) ^ (k * l) • x := by
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    simp [o.hodgeStar_hodgeStar hkl hlk, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Complex.real_smul, mul_comm]
  | add x y hx hy => simp [hx, hy, smul_add]

/-- The complex-linear Hodge star preserves the Hermitian Gram product. -/
@[simp]
theorem sesqComplexification_complexHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^l V))
        (o.complexHodgeStar hkl x) (o.complexHodgeStar hkl y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y :=
  LinearMap.BilinForm.sesqComplexification_baseChange_baseChange _
    (fun v w ↦ o.inner_hodgeStar_hodgeStar hkl v w) x y

/-- The volume coefficient of the wedge of complementary complexified exterior powers,
obtained by scalar extension of the real wedge pairing. -/
def complexWedgePairing {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    ℂ ⊗[ℝ] ⋀[ℝ]^k V →ₗ[ℂ] ℂ ⊗[ℝ] ⋀[ℝ]^l V →ₗ[ℂ] ℂ :=
  TensorProduct.curry <|
    (TensorProduct.AlgebraTensorModule.rid ℝ ℂ ℂ).toLinearMap ∘ₗ
      (TensorProduct.lift (wedgePairing o.volumeEquiv hkl)).baseChange ℂ ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange ℝ ℂ _ _).symm.toLinearMap

/-- On pure tensors the complex wedge pairing multiplies the scalar coefficients. -/
@[simp]
theorem complexWedgePairing_tmul_tmul {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (c d : ℂ) (x : ⋀[ℝ]^k V) (y : ⋀[ℝ]^l V) :
    o.complexWedgePairing hkl (c ⊗ₜ x) (d ⊗ₜ y) =
      c * d * (wedgePairing o.volumeEquiv hkl x y : ℝ) := by
  simp [complexWedgePairing, Complex.real_smul, mul_comm]

/-- The complex wedge characterization uses the bilinear extension of the real Gram metric,
not its Hermitian extension. -/
theorem complexWedgePairing_complexHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    o.complexWedgePairing hkl x (o.complexHodgeStar hkl y) =
      LinearMap.BilinForm.baseChange ℂ (innerₗ (⋀[ℝ]^k V)) x y := by
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | tmul d y =>
      simp [o.wedgePairing_hodgeStar, Complex.real_smul, mul_comm]
    | add y z hy hz => simp [hy, hz]
  | add x z hx hz => simp [hx, hz]

/-- The conjugate Hodge star `β ↦ *(conj β)`, conjugate-linear in the coefficients. -/
def barHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    ℂ ⊗[ℝ] ⋀[ℝ]^k V →ₗ⋆[ℂ] ℂ ⊗[ℝ] ⋀[ℝ]^l V :=
  (o.complexHodgeStar hkl).toLinearMap.comp (tmulConj _)

/-- The conjugate Hodge star is the complex-linear star after coefficient conjugation. -/
theorem barHodgeStar_apply {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    o.barHodgeStar hkl x = o.complexHodgeStar hkl (tmulConj _ x) :=
  (rfl)

/-- The conjugate Hodge star conjugates the scalar factor of a pure tensor. -/
@[simp]
theorem barHodgeStar_tmul {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (c : ℂ) (x : ⋀[ℝ]^k V) :
    o.barHodgeStar hkl (c ⊗ₜ x) = starRingEnd ℂ c ⊗ₜ o.hodgeStar hkl x := by
  simp [barHodgeStar_apply]

/-- The square of the conjugate Hodge star has the same degree sign as the real star. -/
theorem barHodgeStar_barHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (hlk : l + k = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    o.barHodgeStar hlk (o.barHodgeStar hkl x) = (-1 : ℂ) ^ (k * l) • x := by
  simp only [barHodgeStar_apply, tmulConj_complexHodgeStar, tmulConj_tmulConj,
    complexHodgeStar_complexHodgeStar]

/-- The conjugate Hodge star is antiunitary for the Hermitian Gram metric. -/
@[simp]
theorem sesqComplexification_barHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^l V))
        (o.barHodgeStar hkl x) (o.barHodgeStar hkl y) =
      starRingEnd ℂ (LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y) := by
  rw [barHodgeStar_apply, barHodgeStar_apply, sesqComplexification_complexHodgeStar,
    LinearMap.BilinForm.sesqComplexification_tmulConj_tmulConj]

/-- The conjugate-star wedge identity has the Hermitian slots in the order `h(β, α)`. -/
theorem complexWedgePairing_barHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    o.complexWedgePairing hkl x (o.barHodgeStar hkl y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) y x := by
  rw [barHodgeStar_apply, complexWedgePairing_complexHodgeStar,
    LinearMap.BilinForm.sesqComplexification_apply]
  have hsymm : (innerₗ (⋀[ℝ]^k V) : LinearMap.BilinForm ℝ _).IsSymm :=
    ⟨fun v w ↦ by simp [real_inner_comm]⟩
  exact (LinearMap.BilinForm.IsSymm.baseChange ℂ hsymm).eq x (tmulConj _ y)

/-- A nonzero complexified form has strictly positive volume pairing with its conjugate star. -/
theorem complexWedgePairing_barHodgeStar_self_pos {k l : ℕ}
    (hkl : k + l = finrank ℝ V) {x : ℂ ⊗[ℝ] ⋀[ℝ]^k V} (hx : x ≠ 0) :
    0 < o.complexWedgePairing hkl x (o.barHodgeStar hkl x) := by
  rw [complexWedgePairing_barHodgeStar]
  exact LinearMap.BilinForm.sesqComplexification_self_pos
    ⟨fun v w ↦ by simp [real_inner_comm]⟩ (fun v hv ↦ real_inner_self_pos.mpr hv) hx

/-- Orientation reversal negates the complex-linear Hodge star. -/
@[simp]
theorem complexHodgeStar_neg_orientation {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (-o).complexHodgeStar hkl x = -(o.complexHodgeStar hkl x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => simp [TensorProduct.tmul_neg]
  | add x y hx hy => simp [hx, hy, add_comm]

/-- Orientation reversal negates the conjugate Hodge star. -/
@[simp]
theorem barHodgeStar_neg_orientation {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (-o).barHodgeStar hkl x = -(o.barHodgeStar hkl x) := by
  simp only [barHodgeStar_apply, complexHodgeStar_neg_orientation]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fact (finrank ℝ W = n)]

/-- An oriented real isometry, complexified on exterior powers, commutes with the complex star. -/
theorem complexHodgeStar_map (φ : V ≃ₗᵢ[ℝ] W) {k l : ℕ}
    (hV : k + l = finrank ℝ V) (hW : k + l = finrank ℝ W)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).complexHodgeStar hW
        ((exteriorPower.map k φ.toLinearMap).baseChange ℂ x) =
      (exteriorPower.map l φ.toLinearMap).baseChange ℂ (o.complexHodgeStar hV x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => simp [o.hodgeStar_map φ hV hW]
  | add x y hx hy => simp [hx, hy]

/-- An oriented real isometry, complexified on exterior powers, commutes with the conjugate star. -/
theorem barHodgeStar_map (φ : V ≃ₗᵢ[ℝ] W) {k l : ℕ}
    (hV : k + l = finrank ℝ V) (hW : k + l = finrank ℝ W)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).barHodgeStar hW
        ((exteriorPower.map k φ.toLinearMap).baseChange ℂ x) =
      (exteriorPower.map l φ.toLinearMap).baseChange ℂ (o.barHodgeStar hV x) := by
  simp only [barHodgeStar_apply, tmulConj_baseChange]
  exact o.complexHodgeStar_map φ hV hW (tmulConj _ x)

end Orientation
