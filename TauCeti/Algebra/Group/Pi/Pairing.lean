/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Coordinatewise sums of pairings on finite products

A finite family of biadditive pairings `e i : M i →+ N i →+ A` induces a pairing of the products

`(x, y) ↦ ∑ i, e i (x i) (y i)`

of `Π i, M i` with `Π i, N i`. If every left adjoint `e i` is injective, so is the left adjoint of
the sum: pairing with the one-point families `Pi.single i y` recovers each coordinate. Over a
finite set of places, this is how local duality pairings are summed into one pairing of the
products of the local cohomology groups.

## Main definitions

* `AddMonoidHom.piPairing`: the coordinatewise sum of a finite family of pairings.

## Main results

* `AddMonoidHom.piPairing_apply`: its value is `∑ i, e i (x i) (y i)`.
* `AddMonoidHom.injective_piPairing`: its left adjoint is injective when every `e i` has an
  injective left adjoint.
-/

public section

namespace AddMonoidHom

variable {ι : Type*} [Fintype ι] {M N : ι → Type*} [∀ i, AddZeroClass (M i)]
  [∀ i, AddZeroClass (N i)] {A : Type*} [AddCommMonoid A] (e : ∀ i, M i →+ N i →+ A)

/-- **The coordinatewise sum of a finite family of pairings**: the pairing of `Π i, M i` with
`Π i, N i` given by `(x, y) ↦ ∑ i, e i (x i) (y i)`. -/
def piPairing : (∀ i, M i) →+ (∀ i, N i) →+ A :=
  ∑ i, (compHom' (Pi.evalAddMonoidHom N i)).comp ((e i).comp (Pi.evalAddMonoidHom M i))

@[simp]
theorem piPairing_apply (x : ∀ i, M i) (y : ∀ i, N i) :
    piPairing e x y = ∑ i, e i (x i) (y i) := by
  simp [piPairing, finsetSum_apply]

/-- **The coordinatewise sum of pairings with injective left adjoints has injective left
adjoint**: two families pairing in the same way with every family of `Π i, N i` are equal. -/
theorem injective_piPairing (he : ∀ i, Function.Injective (e i)) :
    Function.Injective (piPairing e) := by
  classical
  intro x x' h
  funext i
  refine he i (ext fun y ↦ ?_)
  have hy := congr($h (Pi.single i y))
  simp only [piPairing_apply] at hy
  rwa [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
    Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
    Pi.single_eq_same] at hy

end AddMonoidHom
