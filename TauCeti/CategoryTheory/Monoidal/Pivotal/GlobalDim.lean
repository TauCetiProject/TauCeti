/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Simple
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# The global dimension of a pivotal category

Let `C` be a pivotal category which is preadditive and has finitely many isomorphism classes of
simple objects. Its *global dimension* is the scalar
`globalDim C = ∑ S, leftDim S ≫ leftDim Sᘁ : 𝟙_ C ⟶ 𝟙_ C`,
summed over the chosen representatives `S` of the simple classes `TauCeti.SimpleClasses C`. Since
the left dimension of `Sᘁ` is the right dimension of `S`, it is also `∑ S, leftDim S ≫ rightDim S`,
and in a spherical category it is the sum of the squares of the quantum dimensions of the simple
objects.

The global dimension is defined from a pivotal structure, but it does not depend on it, at least
when the endomorphisms of each simple object are the scalars of an algebraically closed field `k`
over which `C` is linear: for a simple object `S`, the product `leftDim S ≫ rightDim S` is the same
for all pivotal structures (`TauCeti.leftDim_comp_rightDim_eq`), even though the two factors are
not. So the global dimension is an invariant of the rigid category `C` alone, as soon as `C`
admits a pivotal structure. This is what lets a property such as pseudo-unitarity, which compares
the global dimension with the Frobenius–Perron dimension, be a property of `C`.

## Main declarations

* `TauCeti.globalDim`: the global dimension of a pivotal category, with
  `TauCeti.globalDim_def` and `TauCeti.globalDim_eq_sum_leftDim_comp_rightDim` computing it;
* `TauCeti.globalDim_eq_sum_quantumDim_comp_quantumDim`: in a spherical category it is the sum of
  the squared quantum dimensions of the simple objects;
* `TauCeti.globalDim_pivotalCategory_eq`: it does not depend on the pivotal structure.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. 162 (2005), §2
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]

/-- The *global dimension* `∑ S, leftDim S ≫ leftDim Sᘁ` of a preadditive pivotal category with
finitely many simple isomorphism classes, summed over the chosen representatives `S` of the
simple classes. -/
noncomputable def globalDim [PivotalCategory C] : 𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, leftDim S.repr ≫ leftDim (S.repr)ᘁ

/-- The defining formula of the global dimension. -/
theorem globalDim_def [PivotalCategory C] :
    globalDim C = ∑ S : SimpleClasses C, leftDim S.repr ≫ leftDim (S.repr)ᘁ :=
  (rfl)

/-- The global dimension is the sum, over the simple classes, of the left dimension followed by
the right dimension of the chosen representative. -/
theorem globalDim_eq_sum_leftDim_comp_rightDim [PivotalCategory C] :
    globalDim C = ∑ S : SimpleClasses C, leftDim S.repr ≫ rightDim S.repr := by
  simp only [globalDim_def, leftDim_rightDual]

/-- In a spherical category the global dimension is the sum of the squared quantum dimensions of
the simple objects. -/
theorem globalDim_eq_sum_quantumDim_comp_quantumDim [PivotalCategory C] [SphericalCategory C] :
    globalDim C = ∑ S : SimpleClasses C, quantumDim S.repr ≫ quantumDim S.repr := by
  simp only [globalDim_eq_sum_leftDim_comp_rightDim, quantumDim_eq_leftDim,
    ← quantumDim_eq_rightDim]

variable (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [HasKernels C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- **The global dimension does not depend on the pivotal structure**: over an algebraically
closed field `k`, if the endomorphisms of each simple object are finite-dimensional, then any two
pivotal structures `P` and `Q` on `C` give the same global dimension. -/
theorem globalDim_pivotalCategory_eq (P Q : PivotalCategory C) :
    @globalDim C _ _ _ _ _ P = @globalDim C _ _ _ _ _ Q := by
  rw [@globalDim_eq_sum_leftDim_comp_rightDim C _ _ _ _ _ P,
    @globalDim_eq_sum_leftDim_comp_rightDim C _ _ _ _ _ Q]
  exact Finset.sum_congr rfl fun S _ => leftDim_comp_rightDim_eq k P Q

end TauCeti
