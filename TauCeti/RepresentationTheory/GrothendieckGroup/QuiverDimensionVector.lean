/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Exact
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Dimension vectors on the Grothendieck group of quiver representations

Pointwise finite-dimensional representations form an extension-closed additive category. The
dimension vector is additive on its short exact sequences, so it descends to an integral linear
map on its exact Grothendieck group. This map supplies the vertex coordinates in which the
Ext-Euler pairing of a quiver is compared with its Ringel form.

The categorical presentation uses the induced exact structure, so its relations are exactly the
short exact sequences of pointwise finite-dimensional representations.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped ZeroObject

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

section GrothendieckGroup

variable [EssentiallySmall.{t}
  (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))]

private noncomputable def quiverDimensionVectorInvariant :
    ExactK0.AdditiveInvariant
      (finiteDimensionalQuiverRepresentationsExactStructure k Q) (Q → ℤ) where
  obj M := fun i ↦ (dimVector M.1 i : ℤ)
  map_iso {_ _} e := by
    funext i
    exact congrArg (fun n : ℕ ↦ (n : ℤ))
      (congrFun (dimVector_eq_of_iso ((ObjectProperty.ι (IsFinDim k Q)).mapIso e)) i)
  map_conflation {S} hS := by
    have hs := (finiteDimensionalQuiverRepresentationsExactStructure_conflation_iff k Q S).mp hS
    have h₁ : ∀ i : Q, FiniteDimensional k
        ((S.map (ObjectProperty.ι (IsFinDim k Q))).X₁.obj ((Paths.of Q).obj i)) :=
      fun i ↦ by
        simpa only [ShortComplex.map_X₁, ObjectProperty.ι_obj] using
          (isFinDim_iff.mp S.X₁.property) ((Paths.of Q).obj i)
    have h₃ : ∀ i : Q, FiniteDimensional k
        ((S.map (ObjectProperty.ι (IsFinDim k Q))).X₃.obj ((Paths.of Q).obj i)) :=
      fun i ↦ by
        simpa only [ShortComplex.map_X₃, ObjectProperty.ι_obj] using
          (isFinDim_iff.mp S.X₃.property) ((Paths.of Q).obj i)
    have hdim := dimVector_add_of_shortExact hs h₁ h₃
    funext i
    simpa only [Pi.add_apply, Nat.cast_add, ShortComplex.map_X₁,
      ShortComplex.map_X₂, ShortComplex.map_X₃, ObjectProperty.ι_obj] using
      congrArg (fun n : ℕ ↦ (n : ℤ)) (congrFun hdim i)

/-- The dimension vector as an additive map from the exact Grothendieck group of pointwise
finite-dimensional quiver representations to the integral vertex lattice. -/
noncomputable def quiverDimensionVector :
    ExactK0 (finiteDimensionalQuiverRepresentationsExactStructure k Q) →+ (Q → ℤ) :=
  ExactK0.lift (quiverDimensionVectorInvariant k Q)

/-- The Grothendieck-group dimension map sends an object class to its dimension vector. -/
@[simp]
theorem quiverDimensionVector_of
    (M : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    quiverDimensionVector k Q (ExactK0.of M) = fun i ↦ (dimVector M.1 i : ℤ) :=
  ExactK0.lift_of (quiverDimensionVectorInvariant k Q) M

section FiniteQuiver

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The Ringel form transported to the exact Grothendieck group of pointwise finite-dimensional
quiver representations through their dimension vectors. -/
noncomputable def quiverEulerPairing :
    LinearMap.BilinForm ℤ
      (ExactK0 (finiteDimensionalQuiverRepresentationsExactStructure k Q)) :=
  (eulerForm Q).comp (quiverDimensionVector k Q).toIntLinearMap
    (quiverDimensionVector k Q).toIntLinearMap

/-- The transported pairing evaluates by applying the Ringel form to the two dimension vectors. -/
@[simp]
theorem quiverEulerPairing_apply
    (x y : ExactK0 (finiteDimensionalQuiverRepresentationsExactStructure k Q)) :
    quiverEulerPairing k Q x y =
      eulerForm Q (quiverDimensionVector k Q x) (quiverDimensionVector k Q y) := by
  simp [quiverEulerPairing]

/-- On classes of finite-dimensional representations, the transported pairing is the Euler form
of their dimension vectors. -/
@[simp]
theorem quiverEulerPairing_of_of
    (M N : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    quiverEulerPairing k Q (ExactK0.of M) (ExactK0.of N) =
      eulerForm Q (fun i ↦ (dimVector M.1 i : ℤ))
        (fun i ↦ (dimVector N.1 i : ℤ)) := by
  simp [quiverEulerPairing]

end FiniteQuiver

end GrothendieckGroup

end TauCeti
