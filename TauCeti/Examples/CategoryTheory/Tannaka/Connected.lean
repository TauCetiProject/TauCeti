/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Tannaka.Connected
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Regular
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular

/-!
# Checks of the tensor-hull connectedness criterion

The trivial group has only sums of units as finite representations. For a nontrivial finite
constant group, the regular representation is not a sum of units and has a tensor-closed hull.
Both calculations hold in every characteristic, including when the group order is divisible by
the characteristic. They exercise the meaning of nontrivial action in the connectedness
criterion without imposing semisimplicity.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.Examples.TannakaConnected

universe u v w

/-- Every finite representation of the trivial group is a sum of units, also after transport
to a monoidally equivalent category. -/
theorem trivialGroup_isSumOfUnits (K : Type u) [Field K]
    {C : Type w} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    [MonoidalCategory C]
    (E : C ≌ FGComoduleCat.{u, u, u} K K) [E.functor.Monoidal] (X : C) :
    IsSumOfUnits X := by
  apply (E.isSumOfUnits_obj_iff X).1
  rw [FGComoduleCat.isSumOfUnits_iff_matrixCoefficientSubmodule_le]
  intro x _
  exact Submodule.mem_span_singleton.mpr ⟨x, by simp⟩

/-- The regular representation of a nontrivial finite constant group is not a sum of units
and its finite-sum and subquotient hull is tensor closed, over a field of any characteristic. -/
theorem constantGroup_regular (K : Type u) [Field K]
    (G : Type u) [Group G] [Finite G] [Nontrivial G] :
    ¬ IsSumOfUnits (FGComoduleCat.regular K (ConstantGroup.coordinateRing K G)) ∧
      (subquotientHull (FGComoduleCat.regular K (ConstantGroup.coordinateRing K G))).TensorLE
        (subquotientHull (FGComoduleCat.regular K (ConstantGroup.coordinateRing K G)))
        (subquotientHull (FGComoduleCat.regular K (ConstantGroup.coordinateRing K G))) := by
  classical
  have hcoeff : Comodule.matrixCoefficientSubmodule (R := K)
      (C := ConstantGroup.coordinateRing K G)
      (M := FGComoduleCat.regular K (ConstantGroup.coordinateRing K G)) = ⊤ :=
    Comodule.regular_matrixCoefficientSubmodule_eq_top
  constructor
  · intro h
    rw [FGComoduleCat.isSumOfUnits_iff_matrixCoefficientSubmodule_le, hcoeff] at h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (h (Submodule.mem_top : ConstantGroup.delta K G 1 ∈ (⊤ : Submodule K _)))
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have h1 := congrArg (fun f ↦ ConstantGroup.functionAlgEquiv K G f 1) ha
    have hg' := congrArg (fun f ↦ ConstantGroup.functionAlgEquiv K G f g) ha
    simp at h1
    simp [hg, h1] at hg'
  · rw [FGComoduleCat.tensorLE_subquotientHull_iff, hcoeff]
    exact le_top

end TauCeti.Examples.TannakaConnected
