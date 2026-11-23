/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC

/-!
# `Spinᶜ` groups of an orthogonal sum

For nonzero real quadratic forms `Q₁` and `Q₂`, the `Spinᶜ` homomorphisms induced by the two
orthogonal inclusions `Q₁ → Q₁ ⊕ Q₂ ← Q₂` have commuting images, and combine into

`CliffordAlgebra.spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ : Spinᶜ(Q₁) × Spinᶜ(Q₂) →* Spinᶜ(Q₁ ⊕ Q₂)`,

`([s, z], [t, w]) ↦ [spinGroupProd (s, t), z w]`. It is the structure-group form of the sum of two
`Spinᶜ` structures: its rotation part is the block sum `SO(Q₁) × SO(Q₂) → SO(Q₁ ⊕ Q₂)`, and the
determinant character is multiplicative, `det [st, zw] = det [s, z] · det [t, w]`, so the
determinant line of a sum is the tensor product of the determinant lines. For finite-dimensional
nondegenerate forms on nonzero spaces its kernel is the antidiagonal circle
`{([1, z], [1, z⁻¹])}`, unlike the kernel `{(1, 1), (-1, -1)}` of the Spin homomorphism.

## Main definitions

* `CliffordAlgebra.spinCGroupProd`: the homomorphism `Spinᶜ(Q₁) × Spinᶜ(Q₂) →* Spinᶜ(Q₁ ⊕ Q₂)`.

## Main results

* `CliffordAlgebra.spinCGroupProd_mk_mk`: its value on representatives.
* `CliffordAlgebra.det_spinCGroupProd`: the determinant character is multiplicative.
* `CliffordAlgebra.toSpecialOrthogonal_spinCGroupProd`: its rotation is the block sum of the
  rotations.
* `CliffordAlgebra.mem_ker_spinCGroupProd_iff`: its kernel is the antidiagonal circle.

## References

* TauCetiRoadmap, `FourManifolds/README.md`, §4.1 (sums of `Spinᶜ` structures).
-/

public section

noncomputable section

open QuadraticMap

namespace QuadraticMap

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The orthogonal sum of a nonzero form with any form is nonzero. -/
theorem prod_ne_zero_left (h : Q₁ ≠ 0) : Q₁.prod Q₂ ≠ 0 :=
  fun h' ↦ h <| QuadraticMap.ext fun m ↦ by simpa using QuadraticMap.congr_fun h' (m, 0)

end QuadraticMap

namespace CliffordAlgebra

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
  (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂) (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)

/-- The `Spinᶜ` images of the two orthogonal summands commute. -/
theorem commute_spinCGroupMap_inl_spinCGroupMap_inr (x : spinCGroup Q₁ hQ₁)
    (y : spinCGroup Q₂ hQ₂) :
    Commute ((QuadraticMap.Isometry.inl Q₁ Q₂).spinCGroupMap hQ₁ (prod_ne_zero_left hQ₁) x)
      ((QuadraticMap.Isometry.inr Q₁ Q₂).spinCGroupMap hQ₂ (prod_ne_zero_left hQ₁) y) := by
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q₁ hQ₁ x
  obtain ⟨⟨t, w⟩, rfl⟩ := spinCGroup.mk_surjective Q₂ hQ₂ y
  simp only [Isometry.spinCGroupMap_mk, Commute, SemiconjBy, ← map_mul, Prod.mk_mul_mk,
    (commute_spinGroupMap_inl_spinGroupMap_inr Q₁ Q₂ s t).eq, mul_comm z]

/-- **The `Spinᶜ` group of an orthogonal sum receives the product of the `Spinᶜ` groups of the
summands**, `([s, z], [t, w]) ↦ [spinGroupProd (s, t), z w]`. -/
def spinCGroupProd :
    spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂ →* spinCGroup (Q₁.prod Q₂) (prod_ne_zero_left hQ₁) :=
  ((QuadraticMap.Isometry.inl Q₁ Q₂).spinCGroupMap hQ₁ _).noncommCoprod
    ((QuadraticMap.Isometry.inr Q₁ Q₂).spinCGroupMap hQ₂ _)
    (commute_spinCGroupMap_inl_spinCGroupMap_inr Q₁ Q₂ hQ₁ hQ₂)

/-- `spinCGroupProd` on representatives. -/
@[simp]
theorem spinCGroupProd_mk_mk (p : spinGroup Q₁ × Circle) (q : spinGroup Q₂ × Circle) :
    spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ (spinCGroup.mk Q₁ hQ₁ p, spinCGroup.mk Q₂ hQ₂ q) =
      spinCGroup.mk _ _ (spinGroupProd Q₁ Q₂ (p.1, q.1), p.2 * q.2) := by
  simp only [spinCGroupProd, MonoidHom.noncommCoprod_apply,
    QuadraticMap.Isometry.spinCGroupMap_mk, ← map_mul, Prod.mk_mul_mk, spinGroupProd_apply]

/-- On the Spin subgroups, `spinCGroupProd` is `spinGroupProd`. -/
theorem spinCGroupProd_ofSpin_ofSpin (s : spinGroup Q₁) (t : spinGroup Q₂) :
    spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ (spinCGroup.ofSpin Q₁ hQ₁ s, spinCGroup.ofSpin Q₂ hQ₂ t) =
      spinCGroup.ofSpin _ _ (spinGroupProd Q₁ Q₂ (s, t)) := by
  simp [spinCGroup.ofSpin_apply]

/-- On the central circles, `spinCGroupProd` is multiplication. -/
theorem spinCGroupProd_ofCircle_ofCircle (z w : Circle) :
    spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ (spinCGroup.ofCircle Q₁ hQ₁ z, spinCGroup.ofCircle Q₂ hQ₂ w) =
      spinCGroup.ofCircle _ _ (z * w) := by
  simp [spinCGroup.ofCircle_apply, ← Prod.one_eq_mk]

/-- **The determinant character is multiplicative on sums.** -/
@[simp]
theorem det_spinCGroupProd (x : spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂) :
    spinCGroup.det _ _ (spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ x) =
      spinCGroup.det Q₁ hQ₁ x.1 * spinCGroup.det Q₂ hQ₂ x.2 := by
  obtain ⟨x, y⟩ := x
  obtain ⟨p, rfl⟩ := spinCGroup.mk_surjective Q₁ hQ₁ x
  obtain ⟨q, rfl⟩ := spinCGroup.mk_surjective Q₂ hQ₂ y
  simp [mul_pow]

/-- **The rotation of a sum is the block sum of the rotations.** -/
@[simp]
theorem toSpecialOrthogonal_spinCGroupProd [FiniteDimensional ℝ M₁] [FiniteDimensional ℝ M₂]
    (x : spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂) :
    spinCGroup.toSpecialOrthogonal _ _ (spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ x) =
      specialOrthogonalGroupProd Q₁ Q₂ (spinCGroup.toSpecialOrthogonal Q₁ hQ₁ x.1,
        spinCGroup.toSpecialOrthogonal Q₂ hQ₂ x.2) := by
  obtain ⟨x, y⟩ := x
  obtain ⟨p, rfl⟩ := spinCGroup.mk_surjective Q₁ hQ₁ x
  obtain ⟨q, rfl⟩ := spinCGroup.mk_surjective Q₂ hQ₂ y
  simp

section Kernel

variable [FiniteDimensional ℝ M₁] [Nontrivial M₁] [FiniteDimensional ℝ M₂] [Nontrivial M₂]

/-- For a finite-dimensional nondegenerate form on a nonzero space, an element of `Spinᶜ(Q)` with
trivial rotation lies in the central circle. -/
theorem spinCGroup.exists_eq_ofCircle_of_toSpecialOrthogonal_eq_one {M : Type*}
    [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M] [Nontrivial M]
    {Q : QuadraticForm ℝ M} (hQ : Q.Nondegenerate) {x : spinCGroup Q hQ.ne_zero}
    (hx : spinCGroup.toSpecialOrthogonal Q hQ.ne_zero x = 1) :
    ∃ z : Circle, x = spinCGroup.ofCircle Q hQ.ne_zero z := by
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q hQ.ne_zero x
  rw [spinCGroup.toSpecialOrthogonal_mk] at hx
  rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ s).mp hx with rfl | rfl
  · exact ⟨z, (spinCGroup.ofCircle_apply Q hQ.ne_zero z).symm⟩
  · refine ⟨-z, ?_⟩
    rw [← spinCGroup.ofSpin_mul_ofCircle, spinCGroup.ofSpin_negOne, ← map_mul, neg_one_mul]

/-- **The kernel of `spinCGroupProd` is the antidiagonal circle** `{([1, z], [1, z⁻¹])}`, for
finite-dimensional nondegenerate forms on nonzero spaces. -/
theorem mem_ker_spinCGroupProd_iff (hn₁ : Q₁.Nondegenerate) (hn₂ : Q₂.Nondegenerate)
    (x : spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂) :
    x ∈ (spinCGroupProd Q₁ Q₂ hQ₁ hQ₂).ker ↔
      ∃ z : Circle, x = (spinCGroup.ofCircle Q₁ hQ₁ z, spinCGroup.ofCircle Q₂ hQ₂ z⁻¹) := by
  constructor
  · intro hx
    have hSO := congrArg (spinCGroup.toSpecialOrthogonal _ _) (MonoidHom.mem_ker.mp hx)
    rw [toSpecialOrthogonal_spinCGroupProd, map_one,
      ← map_one (specialOrthogonalGroupProd Q₁ Q₂),
      (specialOrthogonalGroupProd_injective Q₁ Q₂).eq_iff, Prod.mk_eq_one] at hSO
    obtain ⟨z, hz⟩ := spinCGroup.exists_eq_ofCircle_of_toSpecialOrthogonal_eq_one hn₁ hSO.1
    obtain ⟨w, hw⟩ := spinCGroup.exists_eq_ofCircle_of_toSpecialOrthogonal_eq_one hn₂ hSO.2
    obtain ⟨x, y⟩ := x
    dsimp only at hz hw
    subst hz hw
    rw [MonoidHom.mem_ker, spinCGroupProd_ofCircle_ofCircle, ← map_one (spinCGroup.ofCircle _ _),
      (spinCGroup.ofCircle_injective _ _).eq_iff] at hx
    exact ⟨z, by rw [eq_inv_of_mul_eq_one_right hx]⟩
  · rintro ⟨z, rfl⟩
    rw [MonoidHom.mem_ker, spinCGroupProd_ofCircle_ofCircle, mul_inv_cancel, map_one]

end Kernel

end CliffordAlgebra
