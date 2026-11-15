/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Simple
public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm

/-!
# The global dimension of a pivotal category

Let `C` be a pivotal category which is preadditive and has finitely many isomorphism classes of
simple objects. Its *global dimension* is the scalar
`globalDim C = ∑ S, leftDim S ≫ leftDim Sᘁ : 𝟙_ C ⟶ 𝟙_ C`,
summed over the chosen representatives `S` of the simple classes `TauCeti.SimpleClasses C`. Since
the left dimension of `Sᘁ` is the right dimension of `S`, it is also `∑ S, leftDim S ≫ rightDim S`,
and in a spherical category it is the sum of the squares of the quantum dimensions of the simple
objects.

Comparing with the pivot-free constructions of `TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm`,
the right trace of `f : X ⟶ X` is `doubleDualTrace (f ≫ (pivotalIsoApp X).hom)` and the left trace
is `doubleDualTrace ((pivotalIsoApp X).inv ≫ f)ᘁ`; in particular,
`squaredNorm (pivotalIsoApp X) = leftDim X ≫ rightDim X`. When every simple representative has
scalar endomorphisms, `squaredNorm (a S) = squaredNorm (pivotalIsoApp S.repr)` for any family
`a : ∀ S : SimpleClasses C, S.repr ≅ S.reprᘁᘁ`, so the pivot-free global dimension
`TauCeti.normGlobalDim C a` equals `TauCeti.globalDim C` (`TauCeti.normGlobalDim_eq_globalDim`),
and consequently `globalDim C` does not depend on the pivotal structure.

## Main declarations

* `TauCeti.rightTrace_eq_doubleDualTrace`, `TauCeti.leftTrace_eq_doubleDualTrace`, and
  `TauCeti.squaredNorm_pivotalIsoApp`: comparison of pivotal traces, dimensions, and squared norms;
* `TauCeti.globalDim`: the global dimension of a pivotal category, with
  `TauCeti.globalDim_def` and `TauCeti.globalDim_eq_sum_leftDim_comp_rightDim` computing it;
* `TauCeti.globalDim_eq_sum_quantumDim_comp_quantumDim`: in a spherical category it is the sum of
  the squared quantum dimensions of the simple objects;
* `TauCeti.normGlobalDim_eq_globalDim_of_bijective` and `TauCeti.normGlobalDim_eq_globalDim`:
  agreement of the pivot-free global dimension with `TauCeti.globalDim`;
* `TauCeti.globalDim_pivotalCategory_eq_of_bijective` and `TauCeti.globalDim_pivotalCategory_eq`:
  independence of `TauCeti.globalDim` from the pivotal structure.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

section TraceComparison

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- In a pivotal category, the right trace of `f : X ⟶ X` is the bidual trace of
`f ≫ (pivotalIsoApp X).hom`. -/
theorem rightTrace_eq_doubleDualTrace {X : C} (f : X ⟶ X) :
    rightTrace f = doubleDualTrace (f ≫ (pivotalIsoApp X).hom) := by
  rw [rightTrace_eq_pivotalIsoApp, doubleDualTrace_def, comp_whiskerRight, Category.assoc]

/-- In a pivotal category, the left trace of `f : X ⟶ X` is the bidual trace of the right adjoint
mate of `(pivotalIsoApp X).inv ≫ f`. -/
theorem leftTrace_eq_doubleDualTrace {X : C} (f : X ⟶ X) :
    leftTrace f = doubleDualTrace (rightAdjointMate ((pivotalIsoApp X).inv ≫ f)) := by
  rw [← rightTrace_rightAdjointMate, rightTrace_eq_doubleDualTrace, comp_rightAdjointMate,
    pivotalIsoApp_rightDual]

/-- At the component `pivotalIsoApp X` of a pivotal structure, `doubleDualTrace` gives the right
dimension of `X`. -/
@[simp]
theorem doubleDualTrace_pivotalIsoApp_hom (X : C) :
    doubleDualTrace (pivotalIsoApp X).hom = rightDim X := by
  rw [← rightTrace_id, rightTrace_eq_doubleDualTrace, Category.id_comp]

/-- At the mate of the inverse component `(pivotalIsoApp X).inv`, `doubleDualTrace` gives the left
dimension of `X`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv (X : C) :
    doubleDualTrace (rightAdjointMate (pivotalIsoApp X).inv) = leftDim X := by
  rw [← leftTrace_id, leftTrace_eq_doubleDualTrace, Category.comp_id]

/-- **Comparison with a pivotal structure**: the squared norm of `pivotalIsoApp X` is
`leftDim X ≫ rightDim X`, the summand of `TauCeti.globalDim`. -/
@[simp]
theorem squaredNorm_pivotalIsoApp (X : C) :
    squaredNorm (pivotalIsoApp X) = leftDim X ≫ rightDim X := by
  rw [squaredNorm_eq_comm, doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv,
    doubleDualTrace_pivotalIsoApp_hom]

end TraceComparison

section GlobalDim

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

/-- The pivotal global dimension is `normGlobalDim` evaluated at `pivotalIsoApp`. -/
theorem globalDim_eq_normGlobalDim_pivotalIsoApp [PivotalCategory C] :
    globalDim C = normGlobalDim C (fun S ↦ pivotalIsoApp S.repr) := by
  simp only [globalDim_eq_sum_leftDim_comp_rightDim, normGlobalDim_def, squaredNorm_pivotalIsoApp]

/-- In a spherical category the global dimension is the sum of the squared quantum dimensions of
the simple objects. -/
theorem globalDim_eq_sum_quantumDim_comp_quantumDim [PivotalCategory C] [SphericalCategory C] :
    globalDim C = ∑ S : SimpleClasses C, quantumDim S.repr ≫ quantumDim S.repr := by
  simp only [globalDim_eq_sum_leftDim_comp_rightDim, quantumDim_eq_leftDim,
    ← quantumDim_eq_rightDim]

/-- When every simple representative has scalar endomorphisms over a commutative semiring `R`,
the pivot-free global dimension equals `TauCeti.globalDim` for any pivotal structure. -/
theorem normGlobalDim_eq_globalDim_of_bijective (R : Type w) [CommSemiring R] [PivotalCategory C]
    [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = globalDim C := by
  rw [globalDim_eq_normGlobalDim_pivotalIsoApp]
  exact normGlobalDim_congr_of_bijective C R hS a _

/-- When every simple representative has scalar endomorphisms over a commutative semiring `R`,
`TauCeti.globalDim` does not depend on the pivotal structure. -/
theorem globalDim_pivotalCategory_eq_of_bijective (R : Type w) [CommSemiring R]
    [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
    (hS : ∀ S : SimpleClasses C, Function.Bijective (algebraMap R (End S.repr)))
    (P Q : PivotalCategory C) :
    @globalDim C _ _ _ _ _ P = @globalDim C _ _ _ _ _ Q := by
  rw [@globalDim_eq_sum_leftDim_comp_rightDim C _ _ _ _ _ P,
    @globalDim_eq_sum_leftDim_comp_rightDim C _ _ _ _ _ Q]
  exact Finset.sum_congr rfl fun S _ ↦ leftDim_comp_rightDim_eq_of_bijective R P Q (hS S)

end GlobalDim

section Field

variable (k : Type w) [Field k] [IsAlgClosed k] (C : Type u) [Category.{v} C]
  [MonoidalCategory C] [RigidCategory C] [Preadditive C] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [HasKernels C] [Fintype (SimpleClasses C)]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- **Comparison with the pivotal global dimension**: over an algebraically closed field `k`, if
the endomorphisms of each simple representative are finite-dimensional, then `normGlobalDim C a`
equals `globalDim C` for every pivotal structure on `C`. -/
theorem normGlobalDim_eq_globalDim [PivotalCategory C]
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = globalDim C :=
  normGlobalDim_eq_globalDim_of_bijective C k
    (fun S ↦ bijective_algebraMap_end_of_simple k S.repr) a

end Field

section PivotalEq

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [Preadditive C]
  [Fintype (SimpleClasses C)]
variable (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [HasKernels C]
  [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- **The global dimension does not depend on the pivotal structure**: over an algebraically
closed field `k`, if the endomorphisms of each simple object are finite-dimensional, then any two
pivotal structures `P` and `Q` on `C` give the same global dimension. -/
theorem globalDim_pivotalCategory_eq (P Q : PivotalCategory C) :
    @globalDim C _ _ _ _ _ P = @globalDim C _ _ _ _ _ Q :=
  globalDim_pivotalCategory_eq_of_bijective C k
    (fun S ↦ bijective_algebraMap_end_of_simple k S.repr) P Q

end PivotalEq

end TauCeti
