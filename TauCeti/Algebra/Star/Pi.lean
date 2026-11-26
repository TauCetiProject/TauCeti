/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.Ring.Pi

/-!
# Star-invariant coordinate slices along a product ring equivalence

When `star` fixes `e.symm (Pi.single i 1)` for `e : E ≃+* ∀ i, A i`, `star` preserves the
`i`-th slice (`RingEquiv.apply_star_eq_coord`, `RingEquiv.apply_star_single`), induces a `StarRing`
on `ULift.{0} (A i)` (`RingEquiv.coordStarRing`), and lifts `E ≃ₐ[R] ∀ i, A i` to
`E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i)` (`AlgEquiv.starPiULift`).
-/

public section

namespace RingEquiv

section Semiring

variable {E : Type*} [Semiring E] [StarRing E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)] (e : E ≃+* ∀ i, A i)

/-- When `star` fixes the coordinate central idempotent `e.symm (Pi.single i 1)`, `star` acts on
the `i`-th coordinate via `a ↦ e (star (e.symm (Pi.single i a))) i`. -/
theorem apply_star_eq_coord (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : E) :
    e (star x) i = e (star (e.symm (Pi.single i (e x i)))) i := by
  have hst : star x * e.symm (Pi.single i 1) = star (e.symm (Pi.single i (e x i))) := by
    rw [← e.symm_single_one_mul i x, star_mul, hδ]
  simpa using congrFun (congrArg e hst) i

/-- When `star` fixes the coordinate central idempotent `e.symm (Pi.single i 1)`, `star` sends
each `i`-th coordinate slice `e.symm (Pi.single i a)` back into the same coordinate slice. -/
theorem apply_star_single (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (a : A i) :
    e (star (e.symm (Pi.single i a))) = Pi.single i (e (star (e.symm (Pi.single i a))) i) := by
  have hst : star (e.symm (Pi.single i a)) =
      star (e.symm (Pi.single i a)) * e.symm (Pi.single i 1) := by
    conv_lhs => rw [← show e.symm (Pi.single i 1) * e.symm (Pi.single i a) =
      e.symm (Pi.single i a) by simpa using e.symm_single_one_mul i (e.symm (Pi.single i a)),
      star_mul, hδ]
  funext j; rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [hst, map_mul, Pi.mul_apply, e.apply_symm_apply, Pi.single_eq_of_ne hji, mul_zero,
      Pi.single_eq_of_ne hji]

/-- Re-embedding the `i`-th coordinate of `star (e.symm (Pi.single i a))` recovers
`star (e.symm (Pi.single i a))`. -/
theorem symm_single_apply_star_single (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (a : A i) :
    e.symm (Pi.single i (e (star (e.symm (Pi.single i a))) i)) = star (e.symm (Pi.single i a)) := by
  rw [← e.apply_star_single i hδ a, e.symm_apply_apply]

/-- Induced `StarRing` structure on `ULift.{0} (A i)` from a star-invariant coordinate central
idempotent `e.symm (Pi.single i 1)`. -/
@[expose, instance_reducible]
def coordStarRing (i : ι) (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) :
    StarRing (ULift.{0} (A i)) where
  star x := ULift.up (e (star (e.symm (Pi.single i x.down))) i)
  star_involutive x := ULift.ext <| by
    dsimp only; rw [e.symm_single_apply_star_single i hδ, star_star, e.apply_symm_apply,
      Pi.single_eq_same]
  star_mul x y := ULift.ext <| by
    change e (star (e.symm (Pi.single i (x.down * y.down)))) i = _
    rw [e.symm_single_mul, star_mul, map_mul, Pi.mul_apply]; rfl
  star_add x y := ULift.ext <| by
    change e (star (e.symm (Pi.single i (x.down + y.down)))) i = _
    rw [Pi.single_add, map_add, star_add, map_add, Pi.add_apply]; rfl

@[simp] theorem coordStarRing_down_star (i : ι)
    (hδ : star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : ULift.{0} (A i)) :
    letI := e.coordStarRing i hδ; (star x).down = e (star (e.symm (Pi.single i x.down))) i := rfl

end Semiring

end RingEquiv

namespace AlgEquiv

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E] [StarRing E]
  {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- Bundled product star-algebra isomorphism `E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i)` induced from
`e : E ≃ₐ[R] ∀ i, A i` when `star` fixes every coordinate central idempotent. -/
@[expose] def starPiULift (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    E ≃⋆ₐ[R] ∀ i, ULift.{0} (A i) :=
  let _ : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
  StarAlgEquiv.ofAlgEquiv (e.trans (AlgEquiv.piCongrRight fun _ ↦ ULift.algEquiv.symm)) fun x ↦
    funext fun i ↦ ULift.ext <| by
      dsimp only [AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply, Pi.star_apply]
      erw [RingEquiv.coordStarRing_down_star, ULift.down_algEquiv_symm_apply (R := R)]
      exact e.toRingEquiv.apply_star_eq_coord i (hδ i) x

@[simp] theorem starPiULift_apply_down (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1)) (x : E) (i : ι) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    (e.starPiULift hδ x i).down = e x i := rfl

@[simp] theorem starPiULift_symm_apply (e : E ≃ₐ[R] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (x : ∀ i, ULift.{0} (A i)) :
    letI : ∀ i, StarRing (ULift.{0} (A i)) := fun i ↦ e.toRingEquiv.coordStarRing i (hδ i)
    (e.starPiULift hδ).symm x = e.symm (fun i ↦ (x i).down) := rfl

end AlgEquiv
