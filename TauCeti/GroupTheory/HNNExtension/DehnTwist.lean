/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Dehn twists of HNN extensions

For an HNN extension with relation `t a t⁻¹ = φ(a)`, an element `z` centralizing the
associated subgroup `A` defines an automorphism fixing the base group and sending `t` to
`t * of z`. These twists compose in the same order as their parameters. The parameter is
recovered from the image of `t`, so a twist is the identity exactly when its parameter is one.
In particular, centrality of the parameter does not make an HNN twist trivial.

These are the one-edge twists used in modular groups of splittings. The construction uses
Mathlib's `HNNExtension.lift` and its injective base inclusion.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, §5.1.4 and §9.
* J.-P. Serre, *Trees*, Chapter I, §1.4 (the HNN universal property).
-/

public section

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

private def twistHom (z : Subgroup.centralizer (A : Set G)) :
    HNNExtension G A B φ →* HNNExtension G A B φ :=
  lift of (t * of (z : G)) fun a => by
    have h := congrArg (of (φ := φ)) ((Subgroup.mem_centralizer_iff.mp z.property) a a.property)
    simp only [map_mul] at h
    rw [mul_assoc, ← h, ← mul_assoc, t_mul_of, mul_assoc]

private theorem twistHom_of (z : Subgroup.centralizer (A : Set G)) (g : G) :
    twistHom φ z (of g) = of g := lift_of ..

private theorem twistHom_t (z : Subgroup.centralizer (A : Set G)) :
    twistHom φ z t = t * of (z : G) := lift_t ..

private theorem twistHom_comp (z w : Subgroup.centralizer (A : Set G)) :
    (twistHom φ z).comp (twistHom φ w) = twistHom φ (z * w) := by
  apply hom_ext
  · ext g
    simp [twistHom_of]
  · simp [twistHom_t, twistHom_of, mul_assoc]

private theorem twistHom_one : twistHom φ 1 = MonoidHom.id _ := by
  apply hom_ext
  · ext g
    simp [twistHom_of]
  · simp [twistHom_t]

/-- The Dehn twist fixing the base group and sending `t` to `t * of z`, for `z` in the
centralizer of the source associated subgroup. -/
def dehnTwist (z : Subgroup.centralizer (A : Set G)) : MulAut (HNNExtension G A B φ) :=
  MonoidHom.toMulEquiv (twistHom φ z) (twistHom φ z⁻¹)
    (by rw [twistHom_comp, inv_mul_cancel, twistHom_one])
    (by rw [twistHom_comp, mul_inv_cancel, twistHom_one])

/-- An HNN twist fixes every element of the base group. -/
@[simp] theorem dehnTwist_of (z : Subgroup.centralizer (A : Set G)) (g : G) :
    dehnTwist φ z (of g) = of g := twistHom_of φ z g

/-- The stable letter is multiplied on the right by the parameter. -/
@[simp] theorem dehnTwist_t (z : Subgroup.centralizer (A : Set G)) :
    dehnTwist φ z t = t * of (z : G) := twistHom_t φ z

/-- The parameter one gives the identity twist. -/
@[simp] theorem dehnTwist_one : dehnTwist φ 1 = 1 :=
  MulEquiv.toMonoidHom_injective (twistHom_one φ)

/-- Composition of HNN twists has the same order as multiplication of their parameters. -/
@[simp] theorem dehnTwist_mul (z w : Subgroup.centralizer (A : Set G)) :
    dehnTwist φ (z * w) = dehnTwist φ z * dehnTwist φ w :=
  MulEquiv.toMonoidHom_injective (twistHom_comp φ z w).symm

/-- Inverting the parameter gives the inverse twist. -/
@[simp] theorem dehnTwist_inv (z : Subgroup.centralizer (A : Set G)) :
    dehnTwist φ z⁻¹ = (dehnTwist φ z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← dehnTwist_mul, inv_mul_cancel, dehnTwist_one]

/-- The stable-letter formula recovers the parameter, so the family of twists is faithful. -/
theorem dehnTwist_injective : Function.Injective (dehnTwist φ) := by
  intro z w h
  have ht := congrArg (fun f : MulAut (HNNExtension G A B φ) => f t) h
  simp only [dehnTwist_t, mul_left_cancel_iff] at ht
  exact Subtype.ext (of_injective φ ht)

/-- A Dehn twist of an HNN extension is trivial exactly when its parameter is one. -/
@[simp] theorem dehnTwist_eq_one_iff (z : Subgroup.centralizer (A : Set G)) :
    dehnTwist φ z = 1 ↔ z = 1 := by
  rw [← dehnTwist_one φ, (dehnTwist_injective φ).eq_iff]

/-- Every subgroup of the base group is fixed by an HNN twist. -/
@[simp] theorem map_dehnTwist_map_of (z : Subgroup.centralizer (A : Set G))
    (K : Subgroup G) :
    (K.map (of (φ := φ))).map (dehnTwist φ z : HNNExtension G A B φ →* HNNExtension G A B φ) =
      K.map of := by
  rw [Subgroup.map_map]
  congr 1

end HNNExtension
