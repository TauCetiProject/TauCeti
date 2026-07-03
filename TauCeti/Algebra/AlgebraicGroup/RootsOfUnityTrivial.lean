/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity

/-!
# The first roots-of-unity group is trivial

This file records the boundary case of the roots-of-unity worked example: `μ_1` has the
one-element functor of points.  The main roots-of-unity file identifies the `A`-points of
`μ_n = D(Multiplicative (ZMod n))` with Mathlib's subgroup `rootsOfUnity n A`; here we
specialize that equivalence at `n = 1` and use the fact that a unit whose first power is one
is the unit `1`.

This is a small worked-example check for the reductive-groups roadmap, Layer 4, which lists
`μ_n = D(ℤ/n)` among the diagonalizable groups and asks for concrete examples alongside the
general theory.

## Main declarations

* `TauCeti.RootsOfUnityGroup.pointsMulEquivOne`: the convolution group of points of `μ_1`
  is multiplicatively equivalent to `PUnit`.
* `TauCeti.RootsOfUnityGroup.convPoint_one_eq_one`: every convolution point of `μ_1` is the
  identity point.

## References

The points calculation reuses Tau Ceti's `RootsOfUnityGroup.pointsMulEquiv` and Mathlib's
`rootsOfUnity` subgroup from `Mathlib.RingTheory.RootsOfUnity.Basic`.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The functor of points of `μ_1` is the one-element group.

This is the `n = 1` specialization of `RootsOfUnityGroup.pointsMulEquiv`, followed by the
unique equivalence from `rootsOfUnity 1 A` to `PUnit`. -/
noncomputable def pointsMulEquivOne :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A) ≃* PUnit.{1} := by
  letI : Inhabited (WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) := ⟨1⟩
  haveI : Unique (WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) :=
    (pointsMulEquiv (R := R) (A := A) 1).injective.unique
  exact MulEquiv.ofUnique

/-- The equivalence from `μ_1`-points to `PUnit` sends every point to the unique element. -/
@[simp]
theorem pointsMulEquivOne_apply
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) :
    pointsMulEquivOne (R := R) (A := A) f = PUnit.unit :=
  rfl

/-- The inverse equivalence sends the unique element to the point corresponding to the
trivial first root of unity. -/
@[simp]
theorem pointsMulEquivOne_symm_apply (u : PUnit.{1}) :
    (pointsMulEquivOne (R := R) (A := A)).symm u =
      (pointsMulEquiv (R := R) (A := A) 1).symm 1 := by
  apply (pointsMulEquiv (R := R) (A := A) 1).injective
  exact Subsingleton.elim _ _

/-- Every convolution point of `μ_1` is the identity point. -/
theorem convPoint_one_eq_one
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) : f = 1 := by
  apply (pointsMulEquivOne (R := R) (A := A)).injective
  simp

/-- The identity normal form for `μ_1` convolution points, as a simp proposition. -/
@[simp]
theorem convPoint_one_eq_one_iff
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) :
    f = 1 ↔ True :=
  ⟨fun _ => trivial, fun _ => convPoint_one_eq_one (R := R) (A := A) f⟩

/-- Any `μ_1`-point evaluates the standard generator to `1`. -/
@[simp]
theorem convPoint_one_apply_single_generator
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) :
    f.ofConv (MonoidAlgebra.single (generator 1) (1 : R)) = 1 := by
  have h := pointsMulEquiv_apply (R := R) (A := A) 1 f
  rw [← h]
  exact congrArg (fun u : Aˣ => (u : A))
    (congrArg Subtype.val (Subsingleton.elim (pointsMulEquiv (R := R) (A := A) 1 f) 1))

section Naturality

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The `μ_1` points equivalence is natural in the value algebra. -/
@[simp]
theorem pointsMulEquivOne_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod 1)) →ₐ[R] A)) :
    pointsMulEquivOne (R := R) (A := B)
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod 1))) φ f) =
      pointsMulEquivOne (R := R) (A := A) f :=
  rfl

/-- Naturality of the inverse `μ_1` points equivalence in the value algebra. -/
theorem mapValue_pointsMulEquivOne_symm_apply (φ : A →ₐ[R] B) (u : PUnit.{1}) :
    AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod 1))) φ
        ((pointsMulEquivOne (R := R) (A := A)).symm u) =
      (pointsMulEquivOne (R := R) (A := B)).symm u := by
  apply (pointsMulEquivOne (R := R) (A := B)).injective
  rw [pointsMulEquivOne_mapValue]

end Naturality

end RootsOfUnityGroup

end TauCeti
