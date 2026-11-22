/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Data.Fintype.EquivFin

/-!
# Sums of pairings over a finite product

Let `ι` be a finite type and let `e i : M i →+ N i →+ P` be biadditive pairings into a common
additive commutative monoid `P`. Their sum

`AddMonoidHom.piPairing e x y = ∑ i, e i (x i) (y i)`

is a biadditive pairing of the products `∀ i, M i` and `∀ i, N i`. If every left adjoint
`e i : M i → (N i →+ P)` is bijective, so is the left adjoint of the sum
(`AddMonoidHom.bijective_piPairing`): an additive map out of a finite product is the sum of its
restrictions to the coordinates. This is how local duality at finitely many places assembles into
duality for the product of the local cohomology groups.
-/

public section

namespace AddMonoidHom

variable {ι : Type*} [Fintype ι] {M N : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, AddCommMonoid (N i)] {P : Type*} [AddCommMonoid P] (e : ∀ i, M i →+ N i →+ P)

/-- The sum over a finite index type of pairings `M i × N i → P`, as a pairing of the products:
`piPairing e x y = ∑ i, e i (x i) (y i)`. -/
def piPairing : (∀ i, M i) →+ (∀ i, N i) →+ P :=
  ∑ i, ((e i).comp (Pi.evalAddMonoidHom M i)).compl₂ (Pi.evalAddMonoidHom N i)

@[simp]
theorem piPairing_apply (x : ∀ i, M i) (y : ∀ i, N i) :
    piPairing e x y = ∑ i, e i (x i) (y i) := by
  simp [piPairing]

theorem piPairing_apply_single [DecidableEq ι] (x : ∀ i, M i) (i : ι) (y : N i) :
    piPairing e x (Pi.single i y) = e i (x i) y := by
  rw [piPairing_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero], Pi.single_eq_same]

/-- The sum of pairings with bijective left adjoints has bijective left adjoint. -/
theorem bijective_piPairing (he : ∀ i, Function.Bijective (e i)) :
    Function.Bijective (piPairing e) := by
  classical
  refine ⟨fun x x' h ↦ funext fun i ↦ (he i).1 <| AddMonoidHom.ext fun y ↦ ?_, fun χ ↦ ?_⟩
  · simpa only [piPairing_apply_single] using DFunLike.congr_fun h (Pi.single i y)
  · choose x hx using fun i ↦ (he i).2 (χ.comp (AddMonoidHom.single N i))
    refine ⟨x, AddMonoidHom.functions_ext' P _ _ fun i ↦ AddMonoidHom.ext fun y ↦ ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.single_apply, piPairing_apply_single, hx]

end AddMonoidHom
