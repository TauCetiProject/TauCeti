/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup

/-!
# The roots-of-unity group scheme

This file records the functor-of-points calculation for the diagonalizable group
`D(Multiplicative (ZMod n))`. For positive `n`, this is the usual finite diagonalizable group
scheme `μ_n`: for every commutative `R`-algebra `A`, its convolution group of `A`-points is the
group of `n`th roots of unity in `A`.

The result is deliberately just the points calculation. The represented Hopf algebra is the
group algebra `R[Multiplicative (ZMod n)]`; identifying it with the more classical
coordinate ring `R[X]/(X^n - 1)` is separate quotient-polynomial infrastructure.

## Main definitions

* `TauCeti.RootsOfUnityGroup.pointsMulEquiv`: the multiplicative equivalence from
  convolution points of `R[Multiplicative (ZMod n)]` to `rootsOfUnity n A`.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_apply`: the equivalence sends a point to its
  value on the standard generator `single (ofAdd 1) 1`.

This is a worked-example check for the reductive-groups roadmap, Layer 4:
"`μ_n = D(ℤ/n)`" in the diagonalizable-groups lane, together with the Layer 0 functor-of-points
calculation.

## References

The diagonalizable-group points calculation is Tau Ceti's
`DiagonalizableGroup.pointsMulEquiv`. The cyclic character group calculation is Mathlib's
`IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator`, from
`Mathlib.RingTheory.RootsOfUnity.Basic`.
-/

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The standard generator of the character group defining `μ_n = D(ℤ/n)`. -/
abbrev generator (n : ℕ) : Multiplicative (ZMod n) :=
  Multiplicative.ofAdd 1

/-- Every element of `Multiplicative (ZMod n)` is a power of the standard generator. -/
lemma mem_zpowers_generator (n : ℕ) (x : Multiplicative (ZMod n)) :
    x ∈ Subgroup.zpowers (generator n) := by
  refine ⟨(Multiplicative.toAdd x).cast, ?_⟩
  change (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd x).cast = x
  rw [← ofAdd_zsmul]
  calc
    Multiplicative.ofAdd ((Multiplicative.toAdd x).cast • (1 : ZMod n)) =
        Multiplicative.ofAdd (((Multiplicative.toAdd x).cast : ℤ) : ZMod n) := by simp
    _ =
        Multiplicative.ofAdd (Multiplicative.toAdd x) := by rw [ZMod.intCast_zmod_cast]
    _ = x := ofAdd_toAdd x

/-- The cardinality of the standard cyclic character group is `n`. -/
@[simp]
lemma natCard_multiplicative_zmod (n : ℕ) :
    Nat.card (Multiplicative (ZMod n)) = n := by
  exact (Nat.card_congr (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans
    (Nat.card_zmod n)

/-- Characters of `Multiplicative (ZMod n)` are canonically `n`th roots of unity, by evaluation
on the standard generator. -/
noncomputable def characterMulEquivRootsOfUnity (n : ℕ) :
    (Multiplicative (ZMod n) →* Aˣ) ≃* rootsOfUnity n A :=
  ((IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator (mem_zpowers_generator n) Aˣ).trans
      (MulEquiv.subgroupCongr (by rw [natCard_multiplicative_zmod n]))).trans
    (rootsOfUnityUnitsMulEquiv A n)

/-- A character is sent to its value on the standard generator. -/
@[simp]
lemma characterMulEquivRootsOfUnity_apply (n : ℕ) (χ : Multiplicative (ZMod n) →* Aˣ) :
    ((characterMulEquivRootsOfUnity (A := A) n χ : Aˣ) : A) =
      (χ (generator n) : A) :=
  rfl

/-- The functor of points of `μ_n = D(ℤ/n)` is the group of `n`th roots of unity.

The source is the convolution group of `R`-algebra maps out of the group algebra
`R[Multiplicative (ZMod n)]`, and the target is Mathlib's subgroup of units whose `n`th power
is one. -/
noncomputable def pointsMulEquiv (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) ≃*
      rootsOfUnity n A :=
  (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).trans (characterMulEquivRootsOfUnity n)

/-- The points equivalence sends a point to its value on the standard generator. -/
@[simp]
lemma pointsMulEquiv_apply (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    ((pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) =
      f.ofConv (MonoidAlgebra.single (generator n) 1) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, DiagonalizableGroup.pointsMulEquiv_apply,
    characterMulEquivRootsOfUnity_apply]
  rfl

/-- Under the points equivalence, convolution multiplication is multiplication of roots of
unity. -/
lemma pointsMulEquiv_mul (n : ℕ)
    (f g : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) n (f * g) =
      pointsMulEquiv (R := R) (A := A) n f * pointsMulEquiv (R := R) (A := A) n g := by
  exact (pointsMulEquiv (R := R) (A := A) n).map_mul f g

end RootsOfUnityGroup

end TauCeti
