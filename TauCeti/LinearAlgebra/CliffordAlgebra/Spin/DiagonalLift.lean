/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# The Spin lift of the diagonal `A ↦ A ⊕ A`

For a quadratic form `Q`, the diagonal homomorphism `SO(Q) → SO(Q ⊕ Q)`, `A ↦ A ⊕ A`, lifts to a
group homomorphism

`CliffordAlgebra.diagSpinLift Q hQ hsurj : SO(Q) →* Spin(Q ⊕ Q)`.

If `x ∈ Spin(Q)` lies over `A`, the lift of `A` is the Clifford product of the images of `x` in
the two orthogonal summands, `spinGroupProd Q Q (x, x)`. The other element over `A` is `-x`, and
`(-x, -x)` has the same image, since the two signs `-1` multiply to `1`. So the lift is
well defined without any choice. For a plane rotation of a real positive-definite form, it is the
product of the two half-angle rotations, one in each copy of the plane; the two signs that each
half-angle rotation picks up over a full turn cancel.

The construction assumes that `Spin(Q) → SO(Q)` is surjective. This holds for real
positive-definite forms (`CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_posDef`), the case
of the compact groups `SO(k)`, and over separably closed fields
(`CliffordAlgebra.spinToSpecialOrthogonal_surjective`).

This is the group-level input of the distinguished spin structure on the ordered double `E ⊕ E` of
an oriented vector bundle `E`, which needs no spin structure on `E` itself.

The one-block inclusion `A ↦ A ⊕ 1` has no such lift as soon as `Q` contains an orthogonal pair
`u, w` with `Q u * Q w = 1` (for instance an orthonormal pair of a real positive-definite form):
the Spin element `ι u ι w` squares to `-1`, but its image in `SO(Q)` squares to `1`
(`CliffordAlgebra.not_exists_spinLift_prod_one`).

## Main definitions

* `CliffordAlgebra.diagSpinLift Q hQ hsurj`: the lift `SO(Q) →* Spin(Q ⊕ Q)` of `A ↦ A ⊕ A`, for a
  finite-dimensional nondegenerate form whose Spin group surjects onto `SO(Q)`.

## Main results

* `CliffordAlgebra.diagSpinLift_spinToSpecialOrthogonal`: the lift of the image of `x ∈ Spin(Q)`
  is `spinGroupProd Q Q (x, x)`.
* `CliffordAlgebra.spinToSpecialOrthogonal_diagSpinLift`: it lifts `A ↦ A ⊕ A`.
* `CliffordAlgebra.eq_diagSpinLift`: it is the unique homomorphism with the first property.
* `CliffordAlgebra.diagSpinLift_specialOrthogonalGroupCongr`: naturality under isometric
  equivalences.
* `CliffordAlgebra.diagSpinLift_specialOrthogonalGroupProd`: the ordered direct-sum law; the lift
  for `Q₁ ⊕ Q₂` is the product of the lifts for `Q₁` and `Q₂`, transported along the block
  permutation `(Q₁ ⊕ Q₁) ⊕ (Q₂ ⊕ Q₂) ≃ (Q₁ ⊕ Q₂) ⊕ (Q₁ ⊕ Q₂)`.
* `CliffordAlgebra.not_exists_spinLift_prod_one`: the one-block inclusion `A ↦ A ⊕ 1` has no lift.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap TauCeti.QuadraticMap

namespace CliffordAlgebra

variable {K M : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M] {Q : QuadraticForm K M}

/-- An element of the kernel of `Spin(Q) → SO(Q)` doubles to `1` in `Spin(Q ⊕ Q)`: the kernel is
`{1, -1}`, and the two signs `-1` multiply to `1`. -/
theorem spinGroupProd_self_eq_one_of_mem_ker (hQ : Q.Nondegenerate) {x : spinGroup Q}
    (hx : x ∈ (spinToSpecialOrthogonal Q).ker) : spinGroupProd Q Q (x, x) = 1 := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [ker_spinToSpecialOrthogonal_eq_bot_of_subsingleton, Subgroup.mem_bot] at hx
    rw [hx, Prod.mk_one_one, map_one]
  · rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).mp hx with rfl | rfl
    · rw [Prod.mk_one_one, map_one]
    · exact spinGroupProd_negOne_negOne _ _

variable (Q) in
/-- **The Spin lift of the diagonal `A ↦ A ⊕ A`.** For a finite-dimensional nondegenerate form
whose Spin group surjects onto `SO(Q)`, the element `A ∈ SO(Q)` lifts to
`spinGroupProd Q Q (x, x) ∈ Spin(Q ⊕ Q)` for any `x ∈ Spin(Q)` over `A`. -/
noncomputable def diagSpinLift (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    specialOrthogonalGroup Q →* spinGroup (Q.prod Q) :=
  (spinToSpecialOrthogonal Q).liftOfSurjective hsurj
    ⟨(spinGroupProd Q Q).comp ((MonoidHom.id _).prod (MonoidHom.id _)),
      fun _ hx ↦ MonoidHom.mem_ker.mpr (spinGroupProd_self_eq_one_of_mem_ker hQ hx)⟩

variable (hQ : Q.Nondegenerate) (hsurj : Function.Surjective (spinToSpecialOrthogonal Q))

/-- **The Spin lift of the diagonal on the image of `x ∈ Spin(Q)`** is the product of the images of
`x` in the two orthogonal summands of `Q ⊕ Q`. -/
@[simp]
theorem diagSpinLift_spinToSpecialOrthogonal (x : spinGroup Q) :
    diagSpinLift Q hQ hsurj (spinToSpecialOrthogonal Q x) = spinGroupProd Q Q (x, x) :=
  MonoidHom.liftOfRightInverse_comp_apply ..

/-- **`diagSpinLift` lifts the diagonal**: its image in `SO(Q ⊕ Q)` is `A ⊕ A`. -/
@[simp]
theorem spinToSpecialOrthogonal_diagSpinLift (A : specialOrthogonalGroup Q) :
    spinToSpecialOrthogonal (Q.prod Q) (diagSpinLift Q hQ hsurj A) =
      specialOrthogonalGroupProd Q Q (A, A) := by
  obtain ⟨x, rfl⟩ := hsurj A
  simp

/-- **Uniqueness of the Spin lift of the diagonal**: a homomorphism `SO(Q) →* Spin(Q ⊕ Q)` sending
the image of every `x ∈ Spin(Q)` to `spinGroupProd Q Q (x, x)` is `diagSpinLift`. -/
theorem eq_diagSpinLift (φ : specialOrthogonalGroup Q →* spinGroup (Q.prod Q))
    (hφ : ∀ x, φ (spinToSpecialOrthogonal Q x) = spinGroupProd Q Q (x, x)) :
    φ = diagSpinLift Q hQ hsurj :=
  MonoidHom.eq_liftOfRightInverse _ _ _ _ _ _ (MonoidHom.ext hφ)

/-- **Naturality of the Spin lift of the diagonal**: transporting `A` along an isometric
equivalence `e` and lifting agrees with lifting `A` and transporting along `e ⊕ e`. -/
theorem diagSpinLift_specialOrthogonalGroupCongr {N : Type*} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] {Q' : QuadraticForm K N} (hQ' : Q'.Nondegenerate)
    (hsurj' : Function.Surjective (spinToSpecialOrthogonal Q')) (e : Q.IsometryEquiv Q')
    (A : specialOrthogonalGroup Q) :
    diagSpinLift Q' hQ' hsurj' (e.specialOrthogonalGroupCongr A) =
      (e.prod e).spinGroupEquiv (diagSpinLift Q hQ hsurj A) := by
  obtain ⟨x, rfl⟩ := hsurj A
  rw [IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    diagSpinLift_spinToSpecialOrthogonal, diagSpinLift_spinToSpecialOrthogonal,
    spinGroupEquiv_prod_spinGroupProd]

/-- **The ordered direct-sum law for the Spin lift of the diagonal.** The lift of `A₁ ⊕ A₂` for
`Q₁ ⊕ Q₂` is the product of the lifts of `A₁` for `Q₁` and of `A₂` for `Q₂`, transported along
the block permutation `(Q₁ ⊕ Q₁) ⊕ (Q₂ ⊕ Q₂) ≃ (Q₁ ⊕ Q₂) ⊕ (Q₁ ⊕ Q₂)`. No sign appears: Spin
elements are even, so their images in orthogonal summands commute. -/
theorem diagSpinLift_specialOrthogonalGroupProd {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁]
    [FiniteDimensional K M₁] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂} (hQ₁ : Q₁.Nondegenerate)
    (hsurj₁ : Function.Surjective (spinToSpecialOrthogonal Q₁)) (hQ₂ : Q₂.Nondegenerate)
    (hsurj₂ : Function.Surjective (spinToSpecialOrthogonal Q₂))
    (hsurj₁₂ : Function.Surjective (spinToSpecialOrthogonal (Q₁.prod Q₂)))
    (A₁ : specialOrthogonalGroup Q₁) (A₂ : specialOrthogonalGroup Q₂) :
    diagSpinLift (Q₁.prod Q₂) (hQ₁.prod hQ₂) hsurj₁₂ (specialOrthogonalGroupProd Q₁ Q₂ (A₁, A₂)) =
      (IsometryEquiv.prodProdProdComm Q₁ Q₁ Q₂ Q₂).spinGroupEquiv
        (spinGroupProd (Q₁.prod Q₁) (Q₂.prod Q₂)
          (diagSpinLift Q₁ hQ₁ hsurj₁ A₁, diagSpinLift Q₂ hQ₂ hsurj₂ A₂)) := by
  obtain ⟨x₁, rfl⟩ := hsurj₁ A₁
  obtain ⟨x₂, rfl⟩ := hsurj₂ A₂
  rw [← spinToSpecialOrthogonal_spinGroupProd Q₁ Q₂ (x₁, x₂), diagSpinLift_spinToSpecialOrthogonal,
    diagSpinLift_spinToSpecialOrthogonal, diagSpinLift_spinToSpecialOrthogonal]
  -- The block permutation carries each of the four summand inclusions to the corresponding one.
  have h₁ : (IsometryEquiv.prodProdProdComm Q₁ Q₁ Q₂ Q₂).toIsometry.comp
      ((Isometry.inl (Q₁.prod Q₁) (Q₂.prod Q₂)).comp (Isometry.inl Q₁ Q₁)) =
      (Isometry.inl (Q₁.prod Q₂) (Q₁.prod Q₂)).comp (Isometry.inl Q₁ Q₂) :=
    Isometry.ext fun _ ↦ by simp
  have h₂ : (IsometryEquiv.prodProdProdComm Q₁ Q₁ Q₂ Q₂).toIsometry.comp
      ((Isometry.inl (Q₁.prod Q₁) (Q₂.prod Q₂)).comp (Isometry.inr Q₁ Q₁)) =
      (Isometry.inr (Q₁.prod Q₂) (Q₁.prod Q₂)).comp (Isometry.inl Q₁ Q₂) :=
    Isometry.ext fun _ ↦ by simp
  have h₃ : (IsometryEquiv.prodProdProdComm Q₁ Q₁ Q₂ Q₂).toIsometry.comp
      ((Isometry.inr (Q₁.prod Q₁) (Q₂.prod Q₂)).comp (Isometry.inl Q₂ Q₂)) =
      (Isometry.inl (Q₁.prod Q₂) (Q₁.prod Q₂)).comp (Isometry.inr Q₁ Q₂) :=
    Isometry.ext fun _ ↦ by simp
  have h₄ : (IsometryEquiv.prodProdProdComm Q₁ Q₁ Q₂ Q₂).toIsometry.comp
      ((Isometry.inr (Q₁.prod Q₁) (Q₂.prod Q₂)).comp (Isometry.inr Q₂ Q₂)) =
      (Isometry.inr (Q₁.prod Q₂) (Q₁.prod Q₂)).comp (Isometry.inr Q₁ Q₂) :=
    Isometry.ext fun _ ↦ by simp
  have hc := commute_spinGroupMap_inl_spinGroupMap_inr (Q₁.prod Q₂) (Q₁.prod Q₂)
    ((Isometry.inr Q₁ Q₂).spinGroupMap x₂) ((Isometry.inl Q₁ Q₂).spinGroupMap x₁)
  simp only [Isometry.spinGroupMap_spinGroupMap] at hc
  simp only [IsometryEquiv.spinGroupEquiv_apply, spinGroupProd_apply, map_mul,
    Isometry.spinGroupMap_spinGroupMap, h₁, h₂, h₃, h₄]
  exact hc.mul_mul_mul_comm _ _

/-- **The one-block inclusion `A ↦ A ⊕ 1` has no Spin lift.** If `Q` has an orthogonal pair `u, w`
with `Q u * Q w = 1`, no homomorphism `SO(Q) →* Spin(Q ⊕ Q₂)` lifts `A ↦ A ⊕ 1`: the Spin
element `ι u ι w` squares to `-1` and its image `A` squares to `1`, while every lift of `A ⊕ 1` is
`±(ι u ι w)` and squares to `-1`. Doubling, as in `diagSpinLift`, is what makes the lift exist. -/
theorem not_exists_spinLift_prod_one {M₂ : Type*} [AddCommGroup M₂] [Module K M₂]
    [FiniteDimensional K M₂] {Q₂ : QuadraticForm K M₂} (hQ : Q.Nondegenerate)
    (hQ₂ : Q₂.Nondegenerate) {u w : M} (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) :
    ¬∃ s : specialOrthogonalGroup Q →* spinGroup (Q.prod Q₂),
      ∀ A, spinToSpecialOrthogonal (Q.prod Q₂) (s A) = specialOrthogonalGroupProd Q Q₂ (A, 1) := by
  rintro ⟨s, hs⟩
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at h
  have : Nontrivial M := ⟨⟨u, 0, by rintro rfl; simp at h⟩⟩
  let x : spinGroup Q := ⟨ι Q u * ι Q w, ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one u w h⟩
  have hx : x * x = spinGroup.negOne Q hQ0 :=
    Subtype.ext <| by simp [x, ι_mul_ι_mul_self_of_isOrtho huw, h]
  have hA : spinToSpecialOrthogonal Q x * spinToSpecialOrthogonal Q x = 1 := by
    rw [← map_mul, hx, spinGroup.spinToSpecialOrthogonal_negOne]
  have hy : spinToSpecialOrthogonal (Q.prod Q₂) (s (spinToSpecialOrthogonal Q x)) =
      spinToSpecialOrthogonal (Q.prod Q₂) (spinGroupProd Q Q₂ (x, 1)) := by
    rw [hs, spinToSpecialOrthogonal_spinGroupProd, map_one]
  have hyy : spinGroupProd Q Q₂ (x, 1) * spinGroupProd Q Q₂ (x, 1) =
      spinGroupProd Q Q₂ (spinGroup.negOne Q hQ0, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, hx, one_mul]
  have hsA : s (spinToSpecialOrthogonal Q x) * s (spinToSpecialOrthogonal Q x) = 1 := by
    rw [← map_mul, hA, map_one]
  rcases eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq (Q.prod Q₂) (hQ.prod hQ₂) _ _ hy
    with h' | h'
  · rw [h', hyy, spinGroupProd_negOne_one] at hsA
    exact spinGroup.negOne_ne_one _ _ hsA
  · have hc : Commute (spinGroupProd Q Q₂ (x, 1))
        (spinGroup.negOne (Q.prod Q₂) (hQ.prod hQ₂).ne_zero) :=
      (spinGroup.negOne_mul_comm _ _ _).symm
    rw [h', hc.mul_mul_mul_comm, spinGroup.negOne_mul_self, one_mul, hyy,
      spinGroupProd_negOne_one] at hsA
    exact spinGroup.negOne_ne_one _ _ hsA

end CliffordAlgebra
