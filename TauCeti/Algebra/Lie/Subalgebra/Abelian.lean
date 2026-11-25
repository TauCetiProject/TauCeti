/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Abelian submodules as Lie subalgebras

A submodule `𝔞` of a Lie algebra on which the bracket vanishes, `[x, y] = 0` for `x, y ∈ 𝔞`, is
closed under the bracket, so it is a Lie subalgebra, and this Lie subalgebra is abelian. For
example, a maximal abelian subspace of the `-1`-eigenspace of a Cartan involution is a Lie
subalgebra in this way.

## Main definitions

* `Submodule.toLieSubalgebraOfAbelian`: an abelian submodule as a Lie subalgebra.

## Main results

* `Submodule.isLieAbelian_toLieSubalgebraOfAbelian`: this Lie subalgebra is abelian.
-/

public section

namespace Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- An abelian submodule `𝔞` of a Lie algebra, `[x, y] = 0` for `x, y ∈ 𝔞`, as a Lie
subalgebra. -/
def toLieSubalgebraOfAbelian (𝔞 : Submodule R L) (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) :
    LieSubalgebra R L where
  toSubmodule := 𝔞
  lie_mem' hx hy := by rw [h𝔞 _ hx _ hy]; exact 𝔞.zero_mem

@[simp]
theorem toSubmodule_toLieSubalgebraOfAbelian (𝔞 : Submodule R L)
    (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : (𝔞.toLieSubalgebraOfAbelian h𝔞).toSubmodule = 𝔞 :=
  (rfl)

@[simp]
theorem mem_toLieSubalgebraOfAbelian (𝔞 : Submodule R L) (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0)
    {x : L} : x ∈ 𝔞.toLieSubalgebraOfAbelian h𝔞 ↔ x ∈ 𝔞 :=
  Iff.rfl

/-- An abelian submodule is an abelian Lie subalgebra. -/
instance isLieAbelian_toLieSubalgebraOfAbelian (𝔞 : Submodule R L)
    (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : IsLieAbelian (𝔞.toLieSubalgebraOfAbelian h𝔞) :=
  ⟨fun x y ↦ Subtype.ext (h𝔞 _ x.property _ y.property)⟩

end Submodule
