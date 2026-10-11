/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Induction
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Augmentation
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.Symmetric.Standard
import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# The natural permutation class of a symmetric group

For a nonempty finite set `α`, the natural permutation module of `Equiv.Perm α` has class
`1 + [standard]` over every field. The same formula computes induction of the trivial line
from any point stabilizer. These exact Grothendieck group identities allow permutation-class
calculations in every characteristic, including when the augmentation sequence does not split.

The underlying augmentation relation over arbitrary commutative rings is
`TauCeti.permK0_eq_augmentation_add_trivial`. Here the field hypothesis supplies the
Grothendieck ring structure and identifies the trivial class with its unit `1`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

variable (k : Type u) [Field k] (α : Type u) [Finite α] [Nonempty α]

/-- The natural permutation module on a nonempty finite set has the standard module and
the trivial line as its Grothendieck constituents in every characteristic. -/
@[simp]
theorem permK0_eq_one_add_standard :
    letI : Module.Finite k[Equiv.Perm α] (standardRepresentation k α).asModule :=
      Module.Finite.of_restrictScalars_finite k k[Equiv.Perm α] _
    permK0 k (Equiv.Perm α) α =
      1 + ExactK0.of (FGModuleCat.of k[Equiv.Perm α]
        (standardRepresentation k α).asModule) := by
  rw [permK0_eq_augmentation_add_trivial, toRepresentation_augmentationSubrepresentation,
    ← exactK0_one_eq_of_trivial, add_comm]

variable {α}

omit [Nonempty α] in
/-- Inducing the trivial line from any point stabilizer in a finite symmetric group gives
the natural permutation class, namely the trivial class plus the standard class. -/
@[simp]
theorem indK0_one_stabilizer_eq_one_add_standard (a : α) :
    letI : Module.Finite k[Equiv.Perm α] (standardRepresentation k α).asModule :=
      Module.Finite.of_restrictScalars_finite k k[Equiv.Perm α] _
    indK0 k (MulAction.stabilizer (Equiv.Perm α) a) 1 =
      1 + ExactK0.of (FGModuleCat.of k[Equiv.Perm α]
        (standardRepresentation k α).asModule) := by
  let : Nonempty α := ⟨a⟩
  rw [exactK0_one_eq_of_trivial, indK0_of_trivial,
    permK0_congr k (quotientStabilizerEquiv (Equiv.Perm α) a)
      (quotientStabilizerEquiv_smul (Equiv.Perm α) a),
    permK0_eq_one_add_standard]

end TauCeti
