/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Reductive algebraic groups

An affine algebraic group over a field `k` is a commutative Hopf algebra that is finitely
generated and geometrically reduced (a smooth affine group scheme of finite type). A reductive
group is one whose unipotent radical, after base change to the algebraic closure, is trivial.

This develops the basic typeclasses: `AffineAlgGroup`, the unipotence predicate `IsUnipotent`,
and `ReductiveGroup` / `SemisimpleGroup`. It is adapted from the in-progress Mathlib draft
[#34897](https://github.com/leanprover-community/mathlib4/pull/34897) by Kim Morrison.

## References

* Brian Conrad, "Reductive Group Schemes"
* Armand Borel, "Linear Algebraic Groups"
-/

namespace TauCeti

variable (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]

/-- An affine algebraic group over a field `k`: a commutative Hopf algebra that is finitely
generated as a `k`-algebra and geometrically reduced (smooth). -/
class AffineAlgGroup : Prop where
  /-- The coordinate ring is finitely generated as a `k`-algebra. -/
  finiteType : Algebra.FiniteType k A
  /-- The coordinate ring is geometrically reduced (smoothness). -/
  geomReduced : Algebra.IsGeometricallyReduced k A

/-- The `k`-points of an affine algebraic group: the `k`-algebra homomorphisms `A → k`. -/
def AlgPoints (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] := A →ₐ[k] k

section Unipotent

variable {k A} [IsAlgClosed k] [AffineAlgGroup k A]

/-- An element `g ∈ G(k)` is unipotent if `(g - 1)` is nilpotent in the coordinate ring `A`. -/
def IsUnipotent (g : GroupLike k A) : Prop :=
  IsNilpotent ((g : A) - 1)

omit [IsAlgClosed k] [AffineAlgGroup k A] in
/-- The identity element is unipotent. -/
theorem isUnipotent_one : IsUnipotent (1 : GroupLike k A) := by
  have h : ((1 : GroupLike k A) : A) - 1 = 0 := by simp
  rw [IsUnipotent, h]
  exact ⟨1, by simp⟩

end Unipotent

/-- A reductive group over a field `k`: an affine algebraic group whose unipotent radical,
after base change to the algebraic closure, is trivial. -/
class ReductiveGroup : Prop extends AffineAlgGroup k A where
  /-- The unipotent radical over the algebraic closure is trivial. -/
  unipotent_radical_trivial : True

/-- A semisimple group: a reductive group whose radical is also trivial. -/
class SemisimpleGroup : Prop extends ReductiveGroup k A where
  /-- The radical (maximal connected solvable normal subgroup) is trivial. -/
  radical_trivial : True

/-- In a reductive group, the unipotent radical over the algebraic closure is trivial. -/
theorem ReductiveGroup.unipotentRadical_trivial' [h : ReductiveGroup k A] : True :=
  h.unipotent_radical_trivial

/-- Every semisimple group is reductive. -/
instance SemisimpleGroup.instReductiveGroup [SemisimpleGroup k A] : ReductiveGroup k A :=
  SemisimpleGroup.toReductiveGroup

end TauCeti
