/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Coalgebra.Basic

/-!
# Invariant integrals on Hopf algebras

An invariant integral is a linear functional satisfying a Haar slice identity. A nonzero
right invariant integral has a nondegenerate multiplication pairing in its first argument;
a nonzero left invariant integral has a nondegenerate pairing in its second argument.
These are algebraic statements: no norm, positivity, finite dimension, or normalization
is required. Nondegeneracy is the algebraic input to strict positivity of positive Haar
integrals and to the faithful algebraic GNS construction.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, Proposition 2.2.4,
  for algebraic faithfulness of invariant integrals.
-/

public section

open TensorProduct Coalgebra WithConv Module

namespace LinearMap

variable {R H : Type*}

section Bialgebra

variable [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- Right invariance of an algebraic integral: `(h ⊗ id) Δ(a) = h(a) 1`. -/
def IsRightInvariantIntegral (h : H →ₗ[R] R) : Prop :=
  ∀ a, TensorProduct.lid R H (h.rTensor H (Coalgebra.comul a)) = h a • (1 : H)

/-- Left invariance of an algebraic integral: `(id ⊗ h) Δ(a) = h(a) 1`. -/
def IsLeftInvariantIntegral (h : H →ₗ[R] R) : Prop :=
  ∀ a, TensorProduct.rid R H (h.lTensor H (Coalgebra.comul a)) = h a • (1 : H)

variable {h : H →ₗ[R] R}

/-- The slice characterization of right invariance. -/
theorem isRightInvariantIntegral_iff : h.IsRightInvariantIntegral ↔
    ∀ a, TensorProduct.lid R H (h.rTensor H (Coalgebra.comul a)) = h a • (1 : H) :=
  Iff.rfl

/-- The slice characterization of left invariance. -/
theorem isLeftInvariantIntegral_iff : h.IsLeftInvariantIntegral ↔
    ∀ a, TensorProduct.rid R H (h.lTensor H (Coalgebra.comul a)) = h a • (1 : H) :=
  Iff.rfl

/-- Right invariance in any finite representation of the coproduct. -/
theorem IsRightInvariantIntegral.sum_smul {a : H} {ι : Type*}
    (hh : h.IsRightInvariantIntegral) (r : Coalgebra.Repr R a ι) :
    ∑ i ∈ r.index, h (r.left i) • r.right i = h a • (1 : H) := by
  simpa [← r.eq, map_sum] using hh a

/-- Left invariance in any finite representation of the coproduct. -/
theorem IsLeftInvariantIntegral.sum_smul {a : H} {ι : Type*}
    (hh : h.IsLeftInvariantIntegral) (r : Coalgebra.Repr R a ι) :
    ∑ i ∈ r.index, h (r.right i) • r.left i = h a • (1 : H) := by
  simpa [← r.eq, map_sum] using hh a

/-- Right invariance on a product, expanded in two representations of the coproduct. -/
theorem IsRightInvariantIntegral.sum_sum_mul {a b : H} {ι κ : Type*}
    (hh : h.IsRightInvariantIntegral) (ra : Coalgebra.Repr R a ι) (rb : Coalgebra.Repr R b κ) :
    ∑ i ∈ ra.index, ∑ j ∈ rb.index,
      h (ra.left i * rb.left j) • (ra.right i * rb.right j) = h (a * b) • (1 : H) := by
  simpa [Finset.sum_product] using hh.sum_smul (ra.mul rb)

/-- Left invariance on a product, expanded in two representations of the coproduct. -/
theorem IsLeftInvariantIntegral.sum_sum_mul {a b : H} {ι κ : Type*}
    (hh : h.IsLeftInvariantIntegral) (ra : Coalgebra.Repr R a ι) (rb : Coalgebra.Repr R b κ) :
    ∑ i ∈ ra.index, ∑ j ∈ rb.index,
      h (ra.right i * rb.right j) • (ra.left i * rb.left j) = h (a * b) • (1 : H) := by
  simpa [Finset.sum_product] using hh.sum_smul (ra.mul rb)

end Bialgebra

section Hopf

variable [CommSemiring R] [Semiring H] [HopfAlgebra R H] {h : H →ₗ[R] R}

/-- Strong right invariance, with the antipode moved across the integral. -/
theorem IsRightInvariantIntegral.strong_invariance (hh : h.IsRightInvariantIntegral)
    {a b : H} {ι κ : Type*} (ra : Coalgebra.Repr R a ι) (rb : Coalgebra.Repr R b κ) :
    ∑ i ∈ ra.index, h (ra.left i * b) • ra.right i =
      ∑ j ∈ rb.index, h (a * rb.left j) • HopfAlgebraStruct.antipode R (rb.right j) := by
  classical
  let f : H →ₗ[R] H := ∑ i ∈ ra.index,
    (h.comp (LinearMap.mulLeft R (ra.left i))).smulRight (ra.right i)
  let g : H →ₗ[R] H := (Algebra.linearMap R H).comp (h.comp (LinearMap.mulLeft R a))
  -- Invariance on products says `f * id = g`; convolution with the antipode cancels `id`.
  have hfg : toConv f * toConv LinearMap.id = toConv g := by
    apply WithConv.ofConv_injective
    ext x
    have hr := hh.sum_sum_mul ra (ℛ R x)
    simpa [f, g, (ℛ R x).convMul_apply, map_sum, Finset.sum_mul,
      smul_mul_assoc, Algebra.algebraMap_eq_smul_one] using hr
  have hf : toConv f = toConv g * toConv (HopfAlgebraStruct.antipode R) := by
    rw [← hfg, mul_assoc, LinearMap.id_mul_antipode, mul_one]
  have := congrArg (fun u : WithConv (H →ₗ[R] H) ↦ u.ofConv b) hf
  simpa [f, g, rb.convMul_apply, Algebra.algebraMap_eq_smul_one] using this

/-- Strong left invariance, with the antipode moved across the integral. -/
theorem IsLeftInvariantIntegral.strong_invariance (hh : h.IsLeftInvariantIntegral)
    {a b : H} {ι κ : Type*} (ra : Coalgebra.Repr R a ι) (rb : Coalgebra.Repr R b κ) :
    ∑ i ∈ ra.index, h (b * ra.right i) • ra.left i =
      ∑ j ∈ rb.index, h (rb.right j * a) • HopfAlgebraStruct.antipode R (rb.left j) := by
  classical
  let f : H →ₗ[R] H := ∑ i ∈ ra.index,
    (h.comp (LinearMap.mulRight R (ra.right i))).smulRight (ra.left i)
  let g : H →ₗ[R] H := (Algebra.linearMap R H).comp (h.comp (LinearMap.mulRight R a))
  -- Here the same cancellation takes place on the other side: `id * f = g`.
  have hfg : toConv LinearMap.id * toConv f = toConv g := by
    apply WithConv.ofConv_injective
    ext x
    have hr := hh.sum_sum_mul (ℛ R x) ra
    rw [Finset.sum_comm] at hr
    simpa [f, g, (ℛ R x).convMul_apply, map_sum, Finset.mul_sum,
      mul_smul_comm, Algebra.algebraMap_eq_smul_one] using hr
  have hf : toConv f = toConv (HopfAlgebraStruct.antipode R) * toConv g := by
    rw [← hfg, ← mul_assoc, LinearMap.antipode_mul_id, one_mul]
  have := congrArg (fun u : WithConv (H →ₗ[R] H) ↦ u.ofConv b) hf
  simpa [f, g, rb.convMul_apply, Algebra.algebraMap_eq_smul_one] using this

end Hopf

section Field

variable {k : Type*} [Field k] [Ring H] [HopfAlgebra k H] {h : H →ₗ[k] k}

private theorem IsRightInvariantIntegral.coeff_mul_eq_zero
    (hh : h.IsRightInvariantIntegral) {a : H} (ha : ∀ b, h (a * b) = 0)
    {ι : Type*} (B : Basis ι k H) (c : ι →₀ H)
    (hc : c.sum (fun i x ↦ x ⊗ₜ[k] B i) = Coalgebra.comul a)
    {i : ι} (hi : i ∈ c.support) (b : H) : h (c i * b) = 0 := by
  classical
  let ra : Coalgebra.Repr k a ι := ⟨c.support, c, B, hc⟩
  have hz : ∑ j ∈ c.support, h (c j * b) • B j = 0 := by
    simpa [ra, ha] using hh.strong_invariance ra (ℛ k b)
  have ht := congrArg (B.coord i) hz
  simpa [map_sum, Basis.coord_apply, Finsupp.single_apply, hi, eq_comm] using ht

private theorem IsRightInvariantIntegral.counit_eq_zero
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) {a : H}
    {ι : Type*} (B : Basis ι k H)
    (ha : ∀ b, h (a * b) = 0) : Coalgebra.counit (R := k) a = 0 := by
  classical
  -- Strong invariance puts each first-leg coefficient in the right radical.
  -- Antipode cancellation then puts `ε(a) 1` in that radical as well.
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right B (Coalgebra.comul (R := k) a)
  let ra : Coalgebra.Repr k a _ := ⟨c.support, c, B, hc⟩
  have heps := HopfAlgebra.sum_mul_antipode_eq_smul ra
  have hz (b : H) : h ((Coalgebra.counit (R := k) a • (1 : H)) * b) = 0 := by
    rw [← heps]
    simp only [ra, Finset.sum_mul, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simpa only [mul_assoc] using
      hh.coeff_mul_eq_zero ha B c hc hi (HopfAlgebraStruct.antipode k (B i) * b)
  obtain ⟨b, hb⟩ : ∃ b, h b ≠ 0 := DFunLike.ne_iff.mp h0
  have := hz b
  simpa [smul_mul_assoc, hb] using this

/-- A nonzero right invariant integral detects every nonzero first factor of a product.
This is algebraic faithfulness, not faithfulness of a state on a completion. -/
theorem IsRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero
    (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0) {a : H}
    (ha : ∀ b, h (a * b) = 0) : a = 0 := by
  classical
  let B := Module.Free.chooseBasis k H
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right B (Coalgebra.comul (R := k) a)
  let ra : Coalgebra.Repr k a _ := ⟨c.support, c, B, hc⟩
  rw [← Coalgebra.sum_counit_smul ra]
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 := hh.counit_eq_zero h0 B (hh.coeff_mul_eq_zero ha B c hc hi)
  simp [ra, hi0]

private theorem IsLeftInvariantIntegral.coeff_mul_eq_zero
    (hh : h.IsLeftInvariantIntegral) {a : H} (ha : ∀ b, h (b * a) = 0)
    {ι : Type*} (B : Basis ι k H) (c : ι →₀ H)
    (hc : c.sum (fun i x ↦ B i ⊗ₜ[k] x) = Coalgebra.comul a)
    {i : ι} (hi : i ∈ c.support) (b : H) : h (b * c i) = 0 := by
  classical
  let ra : Coalgebra.Repr k a ι := ⟨c.support, B, c, hc⟩
  have hz : ∑ j ∈ c.support, h (b * c j) • B j = 0 := by
    simpa [ra, ha] using hh.strong_invariance ra (ℛ k b)
  have ht := congrArg (B.coord i) hz
  simpa [map_sum, Basis.coord_apply, Finsupp.single_apply, hi, eq_comm] using ht

private theorem IsLeftInvariantIntegral.counit_eq_zero
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) {a : H}
    {ι : Type*} (B : Basis ι k H)
    (ha : ∀ b, h (b * a) = 0) : Coalgebra.counit (R := k) a = 0 := by
  classical
  -- This time the second-leg coefficients lie in the left radical.
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B (Coalgebra.comul (R := k) a)
  let ra : Coalgebra.Repr k a _ := ⟨c.support, B, c, hc⟩
  have heps := HopfAlgebra.sum_antipode_mul_eq_smul ra
  have hz (b : H) : h (b * (Coalgebra.counit (R := k) a • (1 : H))) = 0 := by
    rw [← heps]
    simp only [ra, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simpa only [mul_assoc] using
      hh.coeff_mul_eq_zero ha B c hc hi (b * HopfAlgebraStruct.antipode k (B i))
  obtain ⟨b, hb⟩ : ∃ b, h b ≠ 0 := DFunLike.ne_iff.mp h0
  have := hz b
  simpa [mul_smul_comm, hb] using this

/-- A nonzero left invariant integral detects every nonzero second factor of a product. -/
theorem IsLeftInvariantIntegral.eq_zero_of_forall_mul_eq_zero
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) {a : H}
    (ha : ∀ b, h (b * a) = 0) : a = 0 := by
  classical
  let B := Module.Free.chooseBasis k H
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B (Coalgebra.comul (R := k) a)
  let ra : Coalgebra.Repr k a _ := ⟨c.support, B, c, hc⟩
  rw [← Coalgebra.sum_smul_counit ra]
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 := hh.counit_eq_zero h0 B (hh.coeff_mul_eq_zero ha B c hc hi)
  simp [ra, hi0]

end Field
end LinearMap
