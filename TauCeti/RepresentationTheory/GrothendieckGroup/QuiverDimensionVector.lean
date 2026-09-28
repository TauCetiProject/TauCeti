/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Dimension vectors on Grothendieck groups of quiver representations and path algebra modules

For a finite-dimensional path algebra, a finitely generated module has finite-dimensional vertex
spaces. The dimension vector is therefore additive in every short exact sequence of finitely
generated modules, and defines a homomorphism from their exact Grothendieck group to the integral
dimension lattice. This is the map through which the quiver Euler form can be compared with an
Ext-Euler pairing on object classes.

The restriction to finite-dimensional path algebras is essential: `Module.finrank` has a junk value
on infinite-dimensional spaces, and a finitely generated module over a cyclic quiver's path algebra
need not be finite-dimensional over the base field.

For a finite quiver, pointwise finite-dimensional representations form an essentially small
category, and their exact Grothendieck group has a dimension-vector map. For finite vertex sets
with finite arrow types, this map pulls back the Euler form to a pairing on that group.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter III, Section 3, for dimension vectors and the Grothendieck group of finite-dimensional
representations.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v w

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

section DimensionVector

variable [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

private noncomputable def pathAlgebraDimensionVectorInvariant :
    ExactK0.AdditiveInvariant (finiteModulesExactStructure (pathAlgebra k Q)) (Q → ℤ) where
  obj M := fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ)
  map_iso {_ _} e := by
    funext i
    exact congrArg (fun n : ℕ ↦ (n : ℤ))
      (congrFun (dimVector_eq_of_iso ((quiverRepFunctor k Q).mapIso
        ((ModuleCat.isFG (pathAlgebra k Q)).ι.mapIso e))) i)
  map_conflation {S} hS := by
    have h₁ : FiniteDimensional k S.X₁.obj :=
      Module.Finite.trans (pathAlgebra k Q) S.X₁.obj
    have h₃ : FiniteDimensional k S.X₃.obj :=
      Module.Finite.trans (pathAlgebra k Q) S.X₃.obj
    have hshort : (S.map (ModuleCat.isFG (pathAlgebra k Q)).ι).ShortExact :=
      (finiteModulesExactStructure_conflation_iff (pathAlgebra k Q) S).mp hS
    have hmap : ((S.map (ModuleCat.isFG (pathAlgebra k Q)).ι).map
        (quiverRepFunctor k Q)).ShortExact := hshort.map_of_exact (quiverRepFunctor k Q)
    have hdim := dimVector_add_of_shortExact hmap
      (fun i ↦ (isFinDim_iff.mp (isFinDim_quiverRepFunctor_obj k Q S.X₁.obj h₁)) i)
      (fun i ↦ (isFinDim_iff.mp (isFinDim_quiverRepFunctor_obj k Q S.X₃.obj h₃)) i)
    funext i
    simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
      CategoryTheory.ObjectProperty.ι_obj, Nat.cast_add, Pi.add_apply] using
      congrArg (fun n : ℕ ↦ (n : ℤ)) (congrFun hdim i)

/-- The integral dimension vector as an additive map on exact `K₀` of finitely generated
modules over a finite-dimensional path algebra. -/
noncomputable def pathAlgebraDimensionVectorK0 :
    ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ (Q → ℤ) :=
  ExactK0.lift (pathAlgebraDimensionVectorInvariant k Q)

/-- The dimension-vector map sends the class of a module to the dimensions of its vertex
components. -/
@[simp]
theorem pathAlgebraDimensionVectorK0_of (M : FGModuleCat (pathAlgebra k Q)) :
    pathAlgebraDimensionVectorK0 k Q (ExactK0.of M) =
      fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ) :=
  ExactK0.lift_of (pathAlgebraDimensionVectorInvariant k Q) M

/-- The map on `K₀` is characterized by its values on module classes. -/
theorem pathAlgebraDimensionVectorK0_unique
    (f : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ (Q → ℤ))
    (hf : ∀ M : FGModuleCat (pathAlgebra k Q),
      f (ExactK0.of M) = fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ)) :
    f = pathAlgebraDimensionVectorK0 k Q :=
  ExactK0.lift_unique (pathAlgebraDimensionVectorInvariant k Q) f hf

end DimensionVector

section EulerPairing

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- The Ringel form pulled back to the exact Grothendieck group of finite-dimensional path
algebra modules. This is the integral form against which the Ext-Euler pairing is compared. -/
noncomputable def pathAlgebraEulerPairingK0 :
    LinearMap.BilinForm ℤ (ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :=
  (eulerForm Q).comp (pathAlgebraDimensionVectorK0 k Q).toIntLinearMap
    (pathAlgebraDimensionVectorK0 k Q).toIntLinearMap

/-- On module classes, the pulled-back form is the quiver Euler form of the two dimension
vectors. -/
@[simp]
theorem pathAlgebraEulerPairingK0_of_of
    (M N : FGModuleCat (pathAlgebra k Q)) :
    pathAlgebraEulerPairingK0 k Q (ExactK0.of M) (ExactK0.of N) =
      eulerForm Q
        (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ))
        (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj N.obj) i : ℤ)) := by
  simp [pathAlgebraEulerPairingK0, LinearMap.BilinForm.comp_apply, pathAlgebraDimensionVectorK0_of]

/-- The pulled-back Ringel form is determined by its values on pairs of module classes. -/
theorem pathAlgebraEulerPairingK0_unique
    (b : LinearMap.BilinForm ℤ (ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))))
    (hb : ∀ M N : FGModuleCat (pathAlgebra k Q),
      b (ExactK0.of M) (ExactK0.of N) =
        eulerForm Q
          (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ))
          (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj N.obj) i : ℤ))) :
    b = pathAlgebraEulerPairingK0 k Q := by
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro M
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro N
  exact (hb M N).trans (pathAlgebraEulerPairingK0_of_of k Q M N).symm

end EulerPairing

open CategoryTheory.ObjectProperty
open scoped ZeroObject

universe t

section GrothendieckGroup

variable [EssentiallySmall.{t}
  (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))]

private noncomputable def quiverRepDimensionVectorInvariant :
    ExactK0.AdditiveInvariant
      (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q) (Q → ℤ) where
  obj M := fun i ↦ (dimVector M.1 i : ℤ)
  map_iso {_ _} e := by
    funext i
    exact congrArg (fun n : ℕ ↦ (n : ℤ))
      (congrFun (dimVector_eq_of_iso ((ObjectProperty.ι (IsFinDim k Q)).mapIso e)) i)
  map_conflation {S} hS := by
    have hs :=
      (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure_conflation_iff k Q S).mp hS
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
noncomputable def quiverRepDimensionVectorK0 :
    ExactK0 (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q) →+ (Q → ℤ) :=
  ExactK0.lift (quiverRepDimensionVectorInvariant k Q)

/-- The Grothendieck-group dimension map sends an object class to its dimension vector. -/
@[simp]
theorem quiverRepDimensionVectorK0_of
    (M : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    quiverRepDimensionVectorK0 k Q (ExactK0.of M) = fun i ↦ (dimVector M.1 i : ℤ) :=
  ExactK0.lift_of (quiverRepDimensionVectorInvariant k Q) M

/-- The dimension-vector map is determined by its values on representation classes. -/
theorem quiverRepDimensionVectorK0_unique
    (f : ExactK0 (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q) →+ (Q → ℤ))
    (hf : ∀ M : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q),
      f (ExactK0.of M) = fun i ↦ (dimVector M.1 i : ℤ)) :
    f = quiverRepDimensionVectorK0 k Q :=
  ExactK0.lift_unique (quiverRepDimensionVectorInvariant k Q) f hf

section FiniteQuiver

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The Ringel form transported to the exact Grothendieck group of pointwise finite-dimensional
quiver representations through their dimension vectors. -/
noncomputable def quiverRepEulerPairingK0 :
    LinearMap.BilinForm ℤ
      (ExactK0 (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q)) :=
  (eulerForm Q).comp (quiverRepDimensionVectorK0 k Q).toIntLinearMap
    (quiverRepDimensionVectorK0 k Q).toIntLinearMap

/-- On representation classes, the transported pairing is the Ringel form of their dimension
vectors. -/
@[simp]
theorem quiverRepEulerPairingK0_of_of
    (M N : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    quiverRepEulerPairingK0 k Q (ExactK0.of M) (ExactK0.of N) =
      eulerForm Q (fun i ↦ (dimVector M.1 i : ℤ))
        (fun i ↦ (dimVector N.1 i : ℤ)) := by
  simp [quiverRepEulerPairingK0, LinearMap.BilinForm.comp_apply, quiverRepDimensionVectorK0_of]

/-- The transported pairing is determined by its values on pairs of representation classes. -/
theorem quiverRepEulerPairingK0_unique
    (b : LinearMap.BilinForm ℤ
      (ExactK0 (pointwiseFiniteDimensionalQuiverRepresentationsExactStructure k Q)))
    (hb : ∀ M N : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q),
      b (ExactK0.of M) (ExactK0.of N) =
        eulerForm Q (fun i ↦ (dimVector M.1 i : ℤ))
          (fun i ↦ (dimVector N.1 i : ℤ))) :
    b = quiverRepEulerPairingK0 k Q := by
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro M
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro N
  exact (hb M N).trans (quiverRepEulerPairingK0_of_of k Q M N).symm

end FiniteQuiver

end GrothendieckGroup

end TauCeti
