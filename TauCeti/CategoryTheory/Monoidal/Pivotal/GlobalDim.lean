/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Simple
public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
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

Without a pivotal structure, `TauCeti.squaredNorm` and `TauCeti.normGlobalDim`
(`TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm`) recover `leftDim X ≫ rightDim X` and
`globalDim C` when evaluated at `pivotalIsoApp` (`TauCeti.squaredNorm_pivotalIsoApp`,
`TauCeti.normGlobalDim_pivotalIsoApp`), and agree with `globalDim C` for any family of double-dual
isomorphisms once every simple representative has scalar endomorphisms
(`TauCeti.normGlobalDim_eq_globalDim`).

The global dimension is defined from a pivotal structure, but it does not depend on it, at least
when the endomorphisms of each simple object are the scalars of an algebraically closed field `k`
over which `C` is linear: for a simple object `S`, the product `leftDim S ≫ rightDim S` is the same
for all pivotal structures (`TauCeti.leftDim_comp_rightDim_eq`), even though the two factors are
not. So the global dimension is an invariant of the rigid category `C` alone, as soon as `C`
admits a pivotal structure. This is what lets a property such as pseudo-unitarity, which compares
the global dimension with the Frobenius–Perron dimension, be a property of `C`.

## Main declarations

* `TauCeti.squaredNorm_pivotalIsoApp`, `TauCeti.normGlobalDim_pivotalIsoApp`, and
  `TauCeti.normGlobalDim_eq_globalDim`: comparison of `squaredNorm`/`normGlobalDim` with
  `globalDim`;
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

/-- **Comparison of squared norm with a pivotal structure**: evaluating `TauCeti.squaredNorm` at
the pivotal isomorphism `pivotalIsoApp X` gives `leftDim X ≫ rightDim X`. -/
theorem squaredNorm_pivotalIsoApp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] (X : C) :
    squaredNorm (pivotalIsoApp X) = leftDim X ≫ rightDim X := by
  rw [squaredNorm_def, doubleDualTrace_def, doubleDualTrace_rightAdjointMate]
  rw [← rightTrace_id, rightTrace_eq_pivotalIsoApp, ← leftTrace_id, leftTrace_eq_pivotalIsoApp]
  simp [scalar_comm]

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

/-- Evaluating `TauCeti.normGlobalDim` at the pivotal isomorphisms `pivotalIsoApp` recovers
`TauCeti.globalDim`. -/
theorem normGlobalDim_pivotalIsoApp [PivotalCategory C] :
    normGlobalDim C (fun S ↦ pivotalIsoApp S.repr) = globalDim C := by
  simp only [normGlobalDim_def, globalDim_eq_sum_leftDim_comp_rightDim, squaredNorm_pivotalIsoApp]

/-- **Comparison with the pivotal global dimension**: when every simple representative has scalar
endomorphisms over a commutative semiring `R`, `TauCeti.normGlobalDim C a` equals
`TauCeti.globalDim C` for any family `a` of double-dual isomorphisms. -/
theorem normGlobalDim_eq_globalDim (R : Type w) [CommSemiring R] [PivotalCategory C]
    [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = globalDim C := by
  rw [normGlobalDim_congr C R hS a (fun S ↦ pivotalIsoApp S.repr), normGlobalDim_pivotalIsoApp]

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
