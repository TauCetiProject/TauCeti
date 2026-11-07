/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.TorusCharacter
import TauCeti.Analysis.Complex.Circle

/-!
# The `Spinᶜ` lift of the rotations of an oriented plane

Let `u, w` be orthogonal vectors with `Q u * Q w = 1`, for instance an orthonormal pair for
`Q v = -‖v‖²`. The circle subgroup `CliffordAlgebra.spinCircle`, `y ↦ Re y + Im y J` with
`J = ι u ι w`, is a double cover of the rotations of the plane of `u` and `w`: the element `y`
rotates that plane by `y²`. In `Spinᶜ(Q)` this double cover is undone by twisting with the same
circle element. The class

`[Re y + Im y J, y] ∈ Spinᶜ(Q)`

depends only on `z = y²`, because replacing `y` by `-y` changes the sign of both entries
(`CliffordAlgebra.spinCGroup.mk_spinCircle_neg`). This defines a homomorphism
`CliffordAlgebra.spinCCircle : U(1) → Spinᶜ(Q)`. Since `cos (θ / 2) + sin (θ / 2) J` is
`exp (θ J / 2)`, its angle form is

`spinCCircle (exp (i θ)) = [exp (θ J / 2), exp (i θ / 2)]`

(`CliffordAlgebra.spinCCircle_exp`). At `θ = 2π` both entries equal `-1`, and `[-1, -1] = 1`.
The rotation of `spinCCircle z` is the rotation of the plane by `z`, fixing the orthogonal
complement, and its determinant character is `z`. So `spinCCircle` lifts `z ↦ (rotation by z, z)`
along `Spinᶜ(Q) → SO(Q) × U(1)`. For a finite-dimensional nondegenerate form it is the only
homomorphism from the circle doing so (`CliffordAlgebra.eq_spinCCircle`).

This is the structure-group form of the canonical `Spinᶜ` structure of an oriented plane field
`ξ` on an oriented Riemannian three-manifold. The oriented orthonormal frames adapted to `ξ` form a
circle bundle, and the `Spinᶜ` structure is associated to it through `spinCCircle`; its
determinant line is `ξ`, regarded as a complex line. The construction is natural under quadratic
isometries (`CliffordAlgebra.spinCGroupMap_spinCCircle`). In particular it is compatible with the
stabilization `V → ℝ × V` by a line, which turns the three-dimensional structure on `Y` into a
four-dimensional one on `S¹ × Y`.

In dimension four, take `Q v = -‖v‖²`, a positively oriented orthonormal basis
`(b₀, b₁, b₂, b₃)` and the plane `⟨b₂, b₃⟩`. The element `spinCCircle z` acts on each half-spinor
space with weights `1` and `z` on the two eigenspaces of `c(b₀) c(b₁)`. On `W⁺` it fixes the
`-i`-eigenspace of `c(b₀) c(b₁)` and multiplies its `i`-eigenspace by `z`. On `W⁻` the roles of the
two eigenspaces are exchanged. Since `c(b₂) c(b₃) = c(b₀) c(b₁)` on `W⁺`, these are the `-2i`- and
`2i`-eigenspaces of `c(b₀) c(b₁) + c(b₂) c(b₃)` in `W⁺`: the circle acts trivially on the first and
through its determinant character on the second.

## Main definitions

* `CliffordAlgebra.spinCCircle Q hQ u w huw h`: the homomorphism `U(1) → Spinᶜ(Q)`,
  `y² ↦ [Re y + Im y ι u ι w, y]`.

## Main results

* `CliffordAlgebra.spinCGroup.mk_spinCircle_neg`: `[Re y + Im y J, y]` is unchanged when `y` is
  replaced by `-y`.
* `CliffordAlgebra.spinCCircle_sq` and `CliffordAlgebra.spinCCircle_exp`: the defining formula
  and its angle form.
* `CliffordAlgebra.det_spinCCircle`: the determinant character of `spinCCircle z` is `z`.
* `CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_left`,
  `CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_right` and
  `CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_of_isOrtho`: `spinCCircle z` rotates the
  plane of `u` and `w` by `z` and fixes the vectors orthogonal to it.
* `CliffordAlgebra.eq_spinCCircle`: uniqueness of a homomorphic lift of `z ↦ (rotation by z, z)`.
* `CliffordAlgebra.spinCGroupMap_spinCCircle`: naturality under quadratic isometries.
* `CliffordAlgebra.coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_I_smul`,
  `CliffordAlgebra.coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_neg_I_smul`,
  `CliffordAlgebra.coe_spinCGroupHalfSpinRep_neg_one_spinCCircle_apply_of_eq_I_smul` and
  `CliffordAlgebra.coe_spinCGroupHalfSpinRep_neg_one_spinCCircle_apply_of_eq_neg_I_smul`: the
  weights of the half-spin representations of `Spinᶜ(4)` on the lift of the rotations of
  `⟨b₂, b₃⟩`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* P. B. Kronheimer and T. S. Mrowka, *Monopoles and contact structures*, Inventiones
  Mathematicae 130 (1997), 209–255 (the canonical `Spinᶜ` structure of an oriented plane field).
-/

public section

noncomputable section

open Module Module.End

namespace CliffordAlgebra

section Lift

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M} (hQ : Q ≠ 0)
  {u w : M} (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)

/-- **Simultaneous sign change**: `[-(Re y + Im y J), -y] = [Re y + Im y J, y]` in `Spinᶜ(Q)`,
where `J = ι u ι w`. -/
theorem spinCGroup.mk_spinCircle_neg (y : Circle) :
    spinCGroup.mk Q hQ (spinCircle Q u w huw h (-y), -y) =
      spinCGroup.mk Q hQ (spinCircle Q u w huw h y, y) := by
  rw [← neg_one_mul y, map_mul, spinCircle_neg_one, ← Prod.mk_mul_mk, map_mul,
    spinCGroup.mk_negOne_neg_one, one_mul]

/-- The class `[Re y + Im y J, y]` is trivial when `y² = 1`. -/
private theorem mk_spinCircle_eq_one_of_sq_eq_one {y : Circle} (hy : y ^ 2 = 1) :
    spinCGroup.mk Q hQ (spinCircle Q u w huw h y, y) = 1 := by
  have hy' := congrArg ((↑) : Circle → ℂ) hy
  rw [Circle.coe_pow, Circle.coe_one, sq, mul_self_eq_one_iff] at hy'
  rcases hy' with hy' | hy'
  · rw [show y = 1 from Circle.ext (by simpa using hy'), map_one, Prod.mk_one_one, map_one]
  · rw [show y = -1 from Circle.ext (by simpa using hy'), spinCircle_neg_one,
      spinCGroup.mk_negOne_neg_one]

variable (Q u w) in
/-- **The `Spinᶜ` lift of the rotations of an oriented plane.** For orthogonal `u, w` with
`Q u * Q w = 1` and `J = ι u ι w`, the homomorphism `U(1) → Spinᶜ(Q)` sending `y²` to
`[Re y + Im y J, y]`; the class does not depend on the choice of square root `y`
(`CliffordAlgebra.spinCGroup.mk_spinCircle_neg`). The element `z` rotates the plane of `u` and `w`
by `z` and has determinant character `z`. -/
def spinCCircle : Circle →* spinCGroup Q hQ :=
  (powMonoidHom 2 : Circle →* Circle).liftOfRightInverse
    (fun z ↦ (z.exists_pow_nat_eq two_ne_zero).choose)
    (fun z ↦ (z.exists_pow_nat_eq two_ne_zero).choose_spec)
    ⟨(spinCGroup.mk Q hQ).comp ((spinCircle Q u w huw h).prod (MonoidHom.id Circle)),
      fun _ hy ↦ mk_spinCircle_eq_one_of_sq_eq_one hQ huw h hy⟩

/-- **The defining formula**: `spinCCircle (y²) = [Re y + Im y ι u ι w, y]`. -/
@[simp]
theorem spinCCircle_sq (y : Circle) :
    spinCCircle Q hQ u w huw h (y ^ 2) = spinCGroup.mk Q hQ (spinCircle Q u w huw h y, y) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y

/-- **The angle form**: `spinCCircle (exp (i θ)) = [exp (θ J / 2), exp (i θ / 2)]`, where
`exp (θ J / 2) = cos (θ / 2) + sin (θ / 2) J` is the circle element `exp (i θ / 2)` of
`spinCircle`. -/
theorem spinCCircle_exp (θ : ℝ) :
    spinCCircle Q hQ u w huw h (Circle.exp θ) =
      spinCGroup.mk Q hQ (spinCircle Q u w huw h (Circle.exp (θ / 2)), Circle.exp (θ / 2)) := by
  rw [← spinCCircle_sq, ← Circle.exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat,
    mul_div_cancel₀ _ two_ne_zero]

/-- **The determinant character of `spinCCircle z` is `z`.** -/
@[simp]
theorem det_spinCCircle (z : Circle) :
    spinCGroup.det Q hQ (spinCCircle Q hQ u w huw h z) = z := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroup.det_mk]

/-- **`spinCCircle` rotates its plane, first vector.** The element `z` moves `u` to
`Re z u - Im z Q u w`; for `Q u = -1` this is the rotation of `u` towards `w` by `z`. -/
theorem toSpecialOrthogonal_spinCCircle_apply_left (z : Circle) :
    (spinCGroup.toSpecialOrthogonal Q hQ (spinCCircle Q hQ u w huw h z) : M ≃ₗ[ℝ] M) u =
      (z : ℂ).re • u - ((z : ℂ).im * Q u) • w := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply,
    spinVectorAction_spinCircle_left huw h, Circle.coe_pow]

/-- **`spinCCircle` rotates its plane, second vector.** The element `z` moves `w` to
`Re z w + Im z Q w u`; for `Q w = -1` this is the rotation of `w` away from `u` by `z`. -/
theorem toSpecialOrthogonal_spinCCircle_apply_right (z : Circle) :
    (spinCGroup.toSpecialOrthogonal Q hQ (spinCCircle Q hQ u w huw h z) : M ≃ₗ[ℝ] M) w =
      (z : ℂ).re • w + ((z : ℂ).im * Q w) • u := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply,
    spinVectorAction_spinCircle_right huw h, Circle.coe_pow]

/-- **`spinCCircle` fixes the orthogonal complement of its plane.** -/
theorem toSpecialOrthogonal_spinCCircle_apply_of_isOrtho {v : M} (hu : Q.IsOrtho u v)
    (hw : Q.IsOrtho w v) (z : Circle) :
    (spinCGroup.toSpecialOrthogonal Q hQ (spinCCircle Q hQ u w huw h z) : M ≃ₗ[ℝ] M) v = v := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply,
    spinVectorAction_spinCircle_of_isOrtho huw h hu hw]

/-- **Uniqueness of the lift.** For a finite-dimensional nondegenerate form, a homomorphism
`U(1) → Spinᶜ(Q)` with the same rotations as `spinCCircle` and with the identity as determinant
character is `spinCCircle`. -/
theorem eq_spinCCircle [FiniteDimensional ℝ M] (hQn : Q.Nondegenerate)
    {φ : Circle →* spinCGroup Q hQ}
    (hrot : (spinCGroup.toSpecialOrthogonal Q hQ).comp φ =
      (spinCGroup.toSpecialOrthogonal Q hQ).comp (spinCCircle Q hQ u w huw h))
    (hdet : (spinCGroup.det Q hQ).comp φ = MonoidHom.id Circle) :
    φ = spinCCircle Q hQ u w huw h := by
  refine spinCGroup.circle_hom_ext Q hQ hQn (MonoidHom.ext fun z ↦ ?_)
  simp only [MonoidHom.comp_apply, MonoidHom.prod_apply, det_spinCCircle]
  exact Prod.ext (DFunLike.congr_fun hrot z) (DFunLike.congr_fun hdet z)

/-- **Naturality under quadratic isometries**: the map of `Spinᶜ` groups induced by `f` carries
the lift of the rotations of the plane of `u` and `w` to the lift of the rotations of the plane of
`f u` and `f w`. For the stabilization `V → ℝ × V` by a line, this extends the plane lift on `V`
to `ℝ × V`. -/
theorem spinCGroupMap_spinCCircle {N : Type*} [AddCommGroup N] [Module ℝ N]
    {P : QuadraticForm ℝ N} (f : Q →qᵢ P) (hP : P ≠ 0) (huw' : P.IsOrtho (f u) (f w))
    (h' : P (f u) * P (f w) = 1) (z : Circle) :
    f.spinCGroupMap hQ hP (spinCCircle Q hQ u w huw h z) =
      spinCCircle P hP (f u) (f w) huw' h' z := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCCircle_sq, QuadraticMap.Isometry.spinCGroupMap_mk,
    QuadraticMap.Isometry.spinGroupMap_spinCircle f huw h huw' h']

end Lift

/-! ### The weights on the half-spinors in dimension four -/

section HalfSpin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (hQ₀ : Q ≠ 0) (b : OrthonormalBasis (Fin 4) ℝ V)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) {o : Orientation ℝ V (Fin 4)} (hb : b.toBasis.orientation = o)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

omit [Fact (finrank ℝ V = 4)] in
/-- The circle subgroup of `⟨b₂, b₃⟩` is the torus element `(1, y)`. -/
private theorem spinCircle_eq_spinTorus (y : Circle) :
    spinCircle Q (b 2) (b 3) (b.isOrtho_apply hQ (by decide)) (b.map_apply_mul_map_apply hQ 2 3)
      y = b.spinTorus hQ (1, y) := by
  rw [OrthonormalBasis.spinTorus_apply, map_one, one_mul]

include hb

/-- **The weight `z` on `W⁺`**: the lift of the rotations of `⟨b₂, b₃⟩` acts by `z` on a positive
half-spinor on which `c(b₀) c(b₁)` acts by `i`. -/
theorem coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_I_smul (z : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) 1}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = Complex.I • (ψ : W)) :
    (spinCGroupHalfSpinRep o ρ 1 hQ₀
        (spinCCircle Q hQ₀ (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 2 3) z) ψ : W) = (z : ℂ) • (ψ : W) := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, LinearMap.smul_apply,
    Submodule.coe_smul, spinCircle_eq_spinTorus b hQ, halfSpinRep_one_spinTorus b hQ ρ hb,
    one_mul,
    coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_I_smul b hQ o ρ y hψ, smul_smul, Circle.coe_pow,
    sq]

/-- **The weight `1` on `W⁺`**: the lift of the rotations of `⟨b₂, b₃⟩` fixes a positive
half-spinor on which `c(b₀) c(b₁)` acts by `-i`. -/
theorem coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_neg_I_smul (z : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) 1}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = -Complex.I • (ψ : W)) :
    (spinCGroupHalfSpinRep o ρ 1 hQ₀
        (spinCCircle Q hQ₀ (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 2 3) z) ψ : W) = ψ := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, LinearMap.smul_apply,
    Submodule.coe_smul, spinCircle_eq_spinTorus b hQ, halfSpinRep_one_spinTorus b hQ ρ hb,
    one_mul,
    coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_neg_I_smul b hQ o ρ y hψ, smul_smul,
    mul_inv_cancel₀ (Circle.coe_ne_zero y), one_smul]

/-- **The weight `1` on `W⁻`**: the lift of the rotations of `⟨b₂, b₃⟩` fixes a negative
half-spinor on which `c(b₀) c(b₁)` acts by `i`. -/
theorem coe_spinCGroupHalfSpinRep_neg_one_spinCCircle_apply_of_eq_I_smul (z : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) (-1)}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = Complex.I • (ψ : W)) :
    (spinCGroupHalfSpinRep o ρ (-1) hQ₀
        (spinCCircle Q hQ₀ (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 2 3) z) ψ : W) = ψ := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, LinearMap.smul_apply,
    Submodule.coe_smul, spinCircle_eq_spinTorus b hQ, halfSpinRep_neg_one_spinTorus b hQ ρ hb,
    one_mul,
    coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_I_smul b hQ o ρ y⁻¹ hψ, smul_smul,
    Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero y), one_smul]

/-- **The weight `z` on `W⁻`**: the lift of the rotations of `⟨b₂, b₃⟩` acts by `z` on a negative
half-spinor on which `c(b₀) c(b₁)` acts by `-i`. -/
theorem coe_spinCGroupHalfSpinRep_neg_one_spinCCircle_apply_of_eq_neg_I_smul (z : Circle)
    {ψ : eigenspace (ρ (chirality Q o)) (-1)}
    (hψ : ρ (ι Q (b 0) * ι Q (b 1)) ψ = -Complex.I • (ψ : W)) :
    (spinCGroupHalfSpinRep o ρ (-1) hQ₀
        (spinCCircle Q hQ₀ (b 2) (b 3) (b.isOrtho_apply hQ (by decide))
          (b.map_apply_mul_map_apply hQ 2 3) z) ψ : W) = (z : ℂ) • (ψ : W) := by
  obtain ⟨y, rfl⟩ := z.exists_pow_nat_eq two_ne_zero
  rw [spinCCircle_sq, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply, LinearMap.smul_apply,
    Submodule.coe_smul, spinCircle_eq_spinTorus b hQ, halfSpinRep_neg_one_spinTorus b hQ ρ hb,
    one_mul,
    coe_halfSpinRep_spinTorus_mk_one_apply_of_eq_neg_I_smul b hQ o ρ y⁻¹ hψ, smul_smul,
    Circle.coe_inv, inv_inv, Circle.coe_pow, sq]

end HalfSpin

end CliffordAlgebra
