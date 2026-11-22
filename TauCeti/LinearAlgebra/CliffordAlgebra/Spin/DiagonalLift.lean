/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.LowRank

/-!
# The diagonal Spin lift `SO(Q) →* Spin(Q ⊕ Q)`

Let `Q` be a finite-dimensional nondegenerate quadratic form over a field `K` with `2` invertible,
and suppose the Spin projection `Spin(Q) →* SO(Q)` is surjective (for instance, `Q` is
positive-definite over `ℝ`, or `K` is quadratically closed). Although the Spin projection
`Spin(Q) →* SO(Q)` generally admits no section, the doubled orthogonal sum `Q ⊕ Q` canonically
receives the diagonal homomorphism

`CliffordAlgebra.spinDiagonalLift Q hQ hsurj : SO(Q) →* Spin(Q ⊕ Q)`

sending `g ∈ SO(Q)` to `spinGroupProd Q Q (x, x)` for any preimage `x ∈ Spin(Q)` of `g`. This is
independent of the choice of `x`: in rank zero (`dim V = 0`) the kernel of `Spin(Q) →* SO(Q)` is
trivial and the preimage `x` is unique, whereas in positive dimension (`dim V > 0`) the kernel is
`{1, -1}` and `spinGroupProd Q Q (-1, -1) = 1`.

Composing with the Spin projection of `Q ⊕ Q` recovers the diagonal embedding `g ↦ (g, g)` of
`SO(Q)` into `SO(Q ⊕ Q)`, so `spinDiagonalLift` is injective and acts diagonally on `V × V`. It
is natural under isometric equivalences `e : Q₁ ≃qᵢ Q₂`, invariant under swapping the two summands
of `Q ⊕ Q`, trivial when `dim V ≤ 1`, and compatible with orthogonal sums via the middle-block
exchange `QuadraticMap.IsometryEquiv.prodProdProdComm`: assuming surjectivity of the Spin
projection for both summands `Q₁`, `Q₂` and for their sum `Q₁ ⊕ Q₂`, since even Clifford elements
on orthogonal summands commute, transporting `spinDiagonalLift (Q₁ ⊕ Q₂)` along
`prodProdProdComm` gives the `spinGroupProd` of `spinDiagonalLift Q₁` and `spinDiagonalLift Q₂`
with no sign.

Over `ℝ`, the diagonal lift of the rotation induced by a circle element `spinCircle Q u w` (or
`spinRotation Q u w t`) is the commuting product of the two circle elements in the first and second
summands of `Q ⊕ Q`. At the half-turn `z = -1` (angle `t = π` in `Spin`, corresponding to a full
`2π` rotation in `SO`), both factors equal `-1`, so their product closes to `1`.

## Main definitions

* `CliffordAlgebra.spinDiagonalLift`: the canonical homomorphism `SO(Q) →* Spin(Q ⊕ Q)` lifting the
  diagonal embedding `g ↦ (g, g)`.

## Main results

* `CliffordAlgebra.spinDiagonalLift_spinToSpecialOrthogonal` and
  `CliffordAlgebra.eq_spinDiagonalLift_of_comp_spinToSpecialOrthogonal`: evaluation on Spin
  preimages and algebraic descent uniqueness of `spinDiagonalLift`.
* `CliffordAlgebra.spinToSpecialOrthogonal_spinDiagonalLift`,
  `CliffordAlgebra.spinVectorAction_spinDiagonalLift`, and
  `CliffordAlgebra.spinDiagonalLift_injective`: `spinDiagonalLift` lifts `g ↦ (g, g)`, acts
  diagonally on `V × V`, and is injective.
* `CliffordAlgebra.spinDiagonalLift_eq_one_of_finrank_le_one`: when `dim V ≤ 1`, the diagonal lift
  is constantly `1`.
* `CliffordAlgebra.spinGroupEquiv_prod_spinDiagonalLift`,
  `CliffordAlgebra.spinGroupEquiv_prodComm_spinDiagonalLift`, and
  `CliffordAlgebra.spinGroupEquiv_prodProdProdComm_spinDiagonalLift`: naturality, swap invariance,
  and orthogonal-sum coherence of `spinDiagonalLift`.
* `CliffordAlgebra.spinDiagonalLift_spinToSpecialOrthogonal_spinCircle` and
  `CliffordAlgebra.spinDiagonalLift_spinToSpecialOrthogonal_spinRotation`: explicit plane-rotation
  formulas over `ℝ`, closing to `1` at `z = -1` / `t = π`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§2 and 6.
* C. Chevalley, *The Algebraic Theory of Spinors*, Columbia (1954), Chapter II.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

section DiagonalLift

open TauCeti.QuadraticMap

noncomputable section

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The diagonal map `x ↦ spinGroupProd Q Q (x, x)` on `Spin(Q)`, which kills the kernel of the
Spin projection `Spin(Q) →* SO(Q)`. -/
private def spinDiag (Q : QuadraticForm K V) : spinGroup Q →* spinGroup (Q.prod Q) :=
  (spinGroupProd Q Q).comp (MonoidHom.prod (MonoidHom.id (spinGroup Q)) (MonoidHom.id _))

private theorem ker_spinToSpecialOrthogonal_le_ker_spinDiag
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinToSpecialOrthogonal Q).ker ≤ (spinDiag Q).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · rw [ker_spinToSpecialOrthogonal_eq_bot_of_subsingleton Q, Subgroup.mem_bot] at hx
    rw [hx, map_one]
  · rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).mp hx with rfl | rfl
    · exact map_one _
    · exact spinGroupProd_negOne_negOne hQ.ne_zero hQ.ne_zero

/-- **The diagonal Spin lift `SO(Q) →* Spin(Q ⊕ Q)`.**

For a finite-dimensional nondegenerate quadratic form `Q` over a field with `2` invertible whose
Spin projection `Spin(Q) →* SO(Q)` is surjective, sending `g ∈ SO(Q)` to
`spinGroupProd Q Q (x, x)` for any Spin preimage `x` of `g` defines a group homomorphism lifting
the diagonal embedding `g ↦ (g, g)`. In rank zero (`dim V = 0`) the kernel is trivial and `x` is
unique; in positive dimension (`dim V > 0`) `x` is defined up to a sign choice `±x`, which
`spinGroupProd Q Q (-1, -1) = 1` kills. -/
def spinDiagonalLift (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    specialOrthogonalGroup Q →* spinGroup (Q.prod Q) :=
  (QuotientGroup.lift (spinToSpecialOrthogonal Q).ker (spinDiag Q)
    (ker_spinToSpecialOrthogonal_le_ker_spinDiag Q hQ)).comp
      (QuotientGroup.quotientKerEquivOfSurjective
        (spinToSpecialOrthogonal Q) hsurj).symm.toMonoidHom

/-- Evaluating `spinDiagonalLift` on the special-orthogonal projection of `x ∈ Spin(Q)` yields the
diagonal product `spinGroupProd Q Q (x, x)`. -/
@[simp]
theorem spinDiagonalLift_spinToSpecialOrthogonal (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (x : spinGroup Q) :
    spinDiagonalLift Q hQ hsurj (spinToSpecialOrthogonal Q x) = spinGroupProd Q Q (x, x) := by
  have hsymm :
      (QuotientGroup.quotientKerEquivOfSurjective (spinToSpecialOrthogonal Q) hsurj).symm
        (spinToSpecialOrthogonal Q x) = (x : spinGroup Q ⧸ (spinToSpecialOrthogonal Q).ker) :=
    (QuotientGroup.quotientKerEquivOfSurjective (spinToSpecialOrthogonal Q) hsurj).symm_apply_apply
      (x : spinGroup Q ⧸ (spinToSpecialOrthogonal Q).ker)
  rw [spinDiagonalLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    QuotientGroup.lift_mk]
  rfl

/-- **Algebraic descent uniqueness for `spinDiagonalLift`**: any homomorphism
`SO(Q) →* Spin(Q ⊕ Q)` agreeing with `x ↦ spinGroupProd Q Q (x, x)` after precomposition with
`spinToSpecialOrthogonal` equals `spinDiagonalLift`. -/
theorem eq_spinDiagonalLift_of_comp_spinToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsurj : Function.Surjective (spinToSpecialOrthogonal Q))
    (f : specialOrthogonalGroup Q →* spinGroup (Q.prod Q))
    (hf : ∀ x : spinGroup Q, f (spinToSpecialOrthogonal Q x) = spinGroupProd Q Q (x, x)) :
    f = spinDiagonalLift Q hQ hsurj := by
  refine MonoidHom.ext fun g ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj g
  rw [hf, spinDiagonalLift_spinToSpecialOrthogonal]

/-- Evaluating `spinDiagonalLift` on the projection of `x ∈ Spin(Q)` multiplies the images of `x`
under the two orthogonal summand inclusions. -/
theorem spinDiagonalLift_spinToSpecialOrthogonal_eq_mul (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hsurj : Function.Surjective (spinToSpecialOrthogonal Q))
    (x : spinGroup Q) :
    spinDiagonalLift Q hQ hsurj (spinToSpecialOrthogonal Q x) =
      (QuadraticMap.Isometry.inl Q Q).spinGroupMap x *
        (QuadraticMap.Isometry.inr Q Q).spinGroupMap x := by
  rw [spinDiagonalLift_spinToSpecialOrthogonal, spinGroupProd_apply]

/-- **The projection of `spinDiagonalLift` to `SO(Q ⊕ Q)`** is the diagonal embedding
`g ↦ (g, g)`. -/
@[simp]
theorem spinToSpecialOrthogonal_spinDiagonalLift (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (g : specialOrthogonalGroup Q) :
    spinToSpecialOrthogonal (Q.prod Q) (spinDiagonalLift Q hQ hsurj g) =
      specialOrthogonalGroupProd Q Q (g, g) := by
  obtain ⟨x, rfl⟩ := hsurj g
  rw [spinDiagonalLift_spinToSpecialOrthogonal, spinToSpecialOrthogonal_spinGroupProd]

/-- **The projection of `spinDiagonalLift` to `O(Q ⊕ Q)`** is the diagonal embedding
`g ↦ (g, g)`. -/
@[simp]
theorem spinToOrthogonal_spinDiagonalLift (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (g : specialOrthogonalGroup Q) :
    spinToOrthogonal (Q.prod Q) (spinDiagonalLift Q hQ hsurj g) =
      orthogonalGroupProd Q Q
        (specialOrthogonalToOrthogonal Q g, specialOrthogonalToOrthogonal Q g) := by
  rw [← specialOrthogonalToOrthogonal_spinToSpecialOrthogonal,
    spinToSpecialOrthogonal_spinDiagonalLift,
    specialOrthogonalToOrthogonal_specialOrthogonalGroupProd]

/-- **`spinDiagonalLift` acts diagonally on `V × V`**: `spinDiagonalLift g` sends `(u, v)` to
`(g u, g v)`. -/
@[simp]
theorem spinVectorAction_spinDiagonalLift (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (g : specialOrthogonalGroup Q)
    (u v : V) :
    spinVectorAction (Q.prod Q) (spinDiagonalLift Q hQ hsurj g) (u, v) =
      ((g : V ≃ₗ[K] V) u, (g : V ≃ₗ[K] V) v) := by
  obtain ⟨x, rfl⟩ := hsurj g
  rw [spinDiagonalLift_spinToSpecialOrthogonal, spinVectorAction_spinGroupProd,
    coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply]

/-- **The diagonal Spin lift `SO(Q) →* Spin(Q ⊕ Q)` is injective.** -/
theorem spinDiagonalLift_injective (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) :
    Function.Injective (spinDiagonalLift Q hQ hsurj) := by
  intro g₁ g₂ h
  have hSO := congrArg (spinToSpecialOrthogonal (Q.prod Q)) h
  rw [spinToSpecialOrthogonal_spinDiagonalLift, spinToSpecialOrthogonal_spinDiagonalLift] at hSO
  exact congrArg Prod.fst (specialOrthogonalGroupProd_injective Q Q hSO)

/-- When `dim V ≤ 1`, `SO(Q)` is trivial and `spinDiagonalLift` is constantly `1`. -/
theorem spinDiagonalLift_eq_one_of_finrank_le_one (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (hV : Module.finrank K V ≤ 1)
    (g : specialOrthogonalGroup Q) :
    spinDiagonalLift Q hQ hsurj g = 1 := by
  have hsub : Subsingleton (specialOrthogonalGroup Q) := by
    rw [QuadraticMap.specialOrthogonalGroup_eq_bot_of_finrank_le_one Q hV]
    infer_instance
  rw [Subsingleton.elim g 1, map_one]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **`spinDiagonalLift` is natural under isometric equivalences.** -/
theorem spinGroupEquiv_prod_spinDiagonalLift {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K W}
    (hQ₁ : Q₁.Nondegenerate) (hsurj₁ : Function.Surjective (spinToSpecialOrthogonal Q₁))
    (hQ₂ : Q₂.Nondegenerate) (hsurj₂ : Function.Surjective (spinToSpecialOrthogonal Q₂))
    (e : Q₁.IsometryEquiv Q₂) (g : specialOrthogonalGroup Q₁) :
    (e.prod e).spinGroupEquiv (spinDiagonalLift Q₁ hQ₁ hsurj₁ g) =
      spinDiagonalLift Q₂ hQ₂ hsurj₂ (e.specialOrthogonalGroupCongr g) := by
  obtain ⟨x, rfl⟩ := hsurj₁ g
  rw [spinDiagonalLift_spinToSpecialOrthogonal, spinGroupEquiv_prod_spinGroupProd,
    IsometryEquiv.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    spinDiagonalLift_spinToSpecialOrthogonal]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Swapping the two copies of `Q` fixes the diagonal Spin lift.** -/
theorem spinGroupEquiv_prodComm_spinDiagonalLift (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsurj : Function.Surjective (spinToSpecialOrthogonal Q)) (g : specialOrthogonalGroup Q) :
    (IsometryEquiv.prodComm Q Q).spinGroupEquiv (spinDiagonalLift Q hQ hsurj g) =
      spinDiagonalLift Q hQ hsurj g := by
  obtain ⟨x, rfl⟩ := hsurj g
  rw [spinDiagonalLift_spinToSpecialOrthogonal, spinGroupEquiv_prodComm_spinGroupProd,
    Prod.swap_prod_mk]

-- Not `@[simp]`: `IsometryEquiv.spinGroupEquiv_apply` simplifies the LHS head to `spinGroupMap`.
/-- **Orthogonal-sum coherence for `spinDiagonalLift`**: assuming surjectivity of the Spin
projection for both summands `Q₁`, `Q₂` and for their orthogonal sum `Q₁ ⊕ Q₂`, transporting the
diagonal lift of a block sum `(g₁, g₂) ∈ SO(Q₁) × SO(Q₂)` along the middle-block exchange
`IsometryEquiv.prodProdProdComm` recovers the `spinGroupProd` of the diagonal lifts of `g₁` and
`g₂`. -/
theorem spinGroupEquiv_prodProdProdComm_spinDiagonalLift {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K W}
    (hQ₁ : Q₁.Nondegenerate) (hsurj₁ : Function.Surjective (spinToSpecialOrthogonal Q₁))
    (hQ₂ : Q₂.Nondegenerate) (hsurj₂ : Function.Surjective (spinToSpecialOrthogonal Q₂))
    (hsurj₁₂ : Function.Surjective (spinToSpecialOrthogonal (Q₁.prod Q₂)))
    (g₁ : specialOrthogonalGroup Q₁) (g₂ : specialOrthogonalGroup Q₂) :
    (IsometryEquiv.prodProdProdComm Q₁ Q₂ Q₁ Q₂).spinGroupEquiv
        (spinDiagonalLift (Q₁.prod Q₂) (hQ₁.prod hQ₂) hsurj₁₂
          (specialOrthogonalGroupProd Q₁ Q₂ (g₁, g₂))) =
      spinGroupProd (Q₁.prod Q₁) (Q₂.prod Q₂)
        (spinDiagonalLift Q₁ hQ₁ hsurj₁ g₁, spinDiagonalLift Q₂ hQ₂ hsurj₂ g₂) := by
  obtain ⟨x₁, rfl⟩ := hsurj₁ g₁
  obtain ⟨x₂, rfl⟩ := hsurj₂ g₂
  rw [← spinToSpecialOrthogonal_spinGroupProd (x := (x₁, x₂)),
    spinDiagonalLift_spinToSpecialOrthogonal, spinDiagonalLift_spinToSpecialOrthogonal,
    spinDiagonalLift_spinToSpecialOrthogonal, spinGroupEquiv_prodProdProdComm_spinGroupProd]

end

end DiagonalLift

section RealRotation

open TauCeti.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
  (hsurj : Function.Surjective (spinToSpecialOrthogonal Q))

/-- **Circle-subgroup formula for `spinDiagonalLift`**: the diagonal lift of the rotation induced
by `spinCircle Q u w z` is the commuting product of the two circle elements in the first and second
summands of `Q ⊕ Q`. -/
theorem spinDiagonalLift_spinToSpecialOrthogonal_spinCircle {u w : V}
    (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) (z : Circle) :
    spinDiagonalLift Q hQ hsurj (spinToSpecialOrthogonal Q (spinCircle Q u w huw h z)) =
      spinCircle (Q.prod Q) (u, 0) (w, 0) (by simpa [QuadraticMap.isOrtho_def] using huw)
          (by simpa using h) z *
        spinCircle (Q.prod Q) (0, u) (0, w) (by simpa [QuadraticMap.isOrtho_def] using huw)
          (by simpa using h) z := by
  rw [spinDiagonalLift_spinToSpecialOrthogonal_eq_mul,
    (QuadraticMap.Isometry.inl Q Q).spinGroupMap_spinCircle huw h _ _,
    (QuadraticMap.Isometry.inr Q Q).spinGroupMap_spinCircle huw h _ _]
  rfl

/-- At `z = -1`, the circle-subgroup rotation projects to the identity in `SO(Q)` and its diagonal
lift closes to `1` in `Spin(Q ⊕ Q)`. -/
theorem spinDiagonalLift_spinToSpecialOrthogonal_spinCircle_neg_one {u w : V}
    (huw : Q.IsOrtho u w) (h : Q u * Q w = 1) :
    spinDiagonalLift Q hQ hsurj (spinToSpecialOrthogonal Q (spinCircle Q u w huw h (-1))) = 1 := by
  rw [spinCircle_neg_one, spinGroup.spinToSpecialOrthogonal_negOne, map_one]

/-- **Plane-rotation formula for `spinDiagonalLift`**: the diagonal lift of the rotation induced
by `spinRotation Q u w t` is the commuting product of the two `spinRotation` elements in the first
and second summands of `Q ⊕ Q`. -/
theorem spinDiagonalLift_spinToSpecialOrthogonal_spinRotation {u w : V}
    (hu : Q u = 1) (hw : Q w = 1) (huw : Q.IsOrtho u w) (t : ℝ) :
    spinDiagonalLift Q hQ hsurj (spinToSpecialOrthogonal Q (spinRotation Q u w hu hw huw t)) =
      spinRotation (Q.prod Q) (u, 0) (w, 0) (by simpa using hu) (by simpa using hw)
          (by simpa [QuadraticMap.isOrtho_def] using huw) t *
        spinRotation (Q.prod Q) (0, u) (0, w) (by simpa using hu) (by simpa using hw)
          (by simpa [QuadraticMap.isOrtho_def] using huw) t := by
  rw [spinDiagonalLift_spinToSpecialOrthogonal_eq_mul,
    (QuadraticMap.Isometry.inl Q Q).spinGroupMap_spinRotation hu hw huw t,
    (QuadraticMap.Isometry.inr Q Q).spinGroupMap_spinRotation hu hw huw t]
  rfl

/-- At Spin angle `π` (a full `2π` rotation in `SO(Q)`), each single-summand rotation equals `-1`,
and the diagonal lift closes to `1` in `Spin(Q ⊕ Q)`. -/
theorem spinDiagonalLift_spinToSpecialOrthogonal_spinRotation_pi {u w : V}
    (hu : Q u = 1) (hw : Q w = 1) (huw : Q.IsOrtho u w) :
    spinDiagonalLift Q hQ hsurj
        (spinToSpecialOrthogonal Q (spinRotation Q u w hu hw huw Real.pi)) = 1 := by
  rw [spinRotation_pi, spinGroup.spinToSpecialOrthogonal_negOne, map_one]

end

end RealRotation

end CliffordAlgebra
