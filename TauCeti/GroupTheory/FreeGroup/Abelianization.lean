/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.FreeAbelianGroup.Basic
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

/-!
# The abelianization of a free group

The abelianization of a group with a free basis is a free abelian group with basis the classes of
the same elements (`FreeGroupBasis.abelianizationBasis`). In particular the abelianization of a
free group, written additively, is a free `ℤ`-module.

The free abelian group `FreeAbelianGroup α` has unique division
(`FreeAbelianGroup.instHasUniqueDiv`), and it is by definition the additive version of the
abelianization of the free group `FreeGroup α`. Hence the abelianization of every free group has
unique roots, and in particular is torsion-free: if `g ^ n` lies in the commutator subgroup of a
free group for some `n ≠ 0`, then so does `g`.

## Main results

* `FreeGroupBasis.abelianizationBasis`: the classes of the elements of a free basis form a basis
  of the abelianization as a `ℤ`-module.
* `TauCeti.instModuleFreeAbelianization`: the abelianization of a free group is a free
  `ℤ`-module.
* `IsFreeGroup.instHasUniqueRootsAbelianization`: the abelianization of a free group has unique
  roots.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2, p. 42 (the abelianization of a free group is free
  abelian on the same basis).
-/

public section

namespace IsFreeGroup

/-- The abelianization of a free group has unique roots: `a ^ n = b ^ n` with `n ≠ 0` forces
`a = b`. In particular it is torsion-free. -/
instance instHasUniqueRootsAbelianization {G : Type*} [Group G] [IsFreeGroup G] :
    HasUniqueRoots (Group.Abelianization G) :=
  -- `FreeAbelianGroup α` is defined as `Additive (Group.Abelianization (FreeGroup α))`.
  have : HasUniqueRoots (Group.Abelianization (FreeGroup (Generators G))) :=
    inferInstanceAs (HasUniqueRoots (Multiplicative (FreeAbelianGroup _)))
  (toFreeGroup G).abelianizationCongr.injective.hasUniqueRoots
    (toFreeGroup G).abelianizationCongr.toMonoidHom

end IsFreeGroup

namespace FreeGroupBasis

variable {ι H : Type*} [Group H]

/-- **The abelianization of a free group is free abelian on the same basis.** For a free basis `b`
of `H`, the classes of the elements `b i` form a basis of the abelianization of `H`, written
additively, as a `ℤ`-module. -/
noncomputable def abelianizationBasis (b : FreeGroupBasis ι H) :
    Module.Basis ι ℤ (Additive (Group.Abelianization H)) :=
  -- `FreeAbelianGroup ι` is by definition `Additive (Group.Abelianization (FreeGroup ι))`.
  (FreeAbelianGroup.basis ι).map
    (AddEquiv.toIntLinearEquiv (M := FreeAbelianGroup ι) b.repr.symm.abelianizationCongr.toAdditive)

@[simp]
theorem abelianizationBasis_apply (b : FreeGroupBasis ι H) (i : ι) :
    b.abelianizationBasis i = .ofMul (.of (b i)) := by
  have h : FreeAbelianGroup.basis ι i = FreeAbelianGroup.of i :=
    (FreeAbelianGroup.basis ι).repr.injective <| by simp [FreeAbelianGroup.basis]
  rw [abelianizationBasis, Module.Basis.map_apply, h]
  -- `FreeAbelianGroup.of i` is by definition the additive class of `FreeGroup.of i`, which the
  -- abelianized isomorphism sends to the class of `b.repr.symm (FreeGroup.of i) = b i`.
  rfl

end FreeGroupBasis

namespace TauCeti

/-- The abelianization of a free group is a free `ℤ`-module. -/
instance instModuleFreeAbelianization {H : Type*} [Group H] [IsFreeGroup H] :
    Module.Free ℤ (Additive (Group.Abelianization H)) :=
  .of_basis (IsFreeGroup.basis H).abelianizationBasis

end TauCeti
