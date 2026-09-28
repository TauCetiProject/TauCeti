/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The equivalence instance is needed for `quiverRepFunctor` to preserve short exact sequences.
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Dimension vectors on the Grothendieck group of path algebra modules

For a finite-dimensional path algebra, a finitely generated module has finite-dimensional vertex
spaces. The dimension vector is therefore additive in every short exact sequence of finitely
generated modules, and defines a homomorphism from their exact Grothendieck group to the integral
dimension lattice. This is the map through which the quiver Euler form can be compared with an
Ext-Euler pairing on object classes.

The restriction to finite-dimensional path algebras is essential: `Module.finrank` has a junk value
on infinite-dimensional spaces, and a finitely generated module over a cyclic quiver's path algebra
need not be finite-dimensional over the base field.

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

private noncomputable def quiverDimensionVectorInvariant :
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
noncomputable def quiverDimensionVectorK0 :
    ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ (Q → ℤ) :=
  ExactK0.lift (quiverDimensionVectorInvariant k Q)

/-- The dimension-vector map sends the class of a module to the dimensions of its vertex
components. -/
@[simp]
theorem quiverDimensionVectorK0_of (M : FGModuleCat (pathAlgebra k Q)) :
    quiverDimensionVectorK0 k Q (ExactK0.of M) =
      fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ) :=
  ExactK0.lift_of (quiverDimensionVectorInvariant k Q) M

/-- The map on `K₀` is characterized by its values on module classes. -/
theorem quiverDimensionVectorK0_unique
    (f : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ (Q → ℤ))
    (hf : ∀ M : FGModuleCat (pathAlgebra k Q),
      f (ExactK0.of M) = fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ)) :
    f = quiverDimensionVectorK0 k Q :=
  ExactK0.lift_unique (quiverDimensionVectorInvariant k Q) f hf

end DimensionVector

section EulerPairing

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [FiniteDimensional k (pathAlgebra k Q)]

/-- The Ringel form pulled back to the exact Grothendieck group of finite-dimensional path
algebra modules. This is the integral form against which the Ext-Euler pairing is compared. -/
noncomputable def quiverEulerPairingK0 :
    LinearMap.BilinForm ℤ (ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :=
  (eulerForm Q).comp (quiverDimensionVectorK0 k Q).toIntLinearMap
    (quiverDimensionVectorK0 k Q).toIntLinearMap

/-- On module classes, the pulled-back form is the quiver Euler form of the two dimension
vectors. -/
@[simp]
theorem quiverEulerPairingK0_of_of
    (M N : FGModuleCat (pathAlgebra k Q)) :
    quiverEulerPairingK0 k Q (ExactK0.of M) (ExactK0.of N) =
      eulerForm Q
        (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ))
        (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj N.obj) i : ℤ)) := by
  simp [quiverEulerPairingK0, LinearMap.BilinForm.comp_apply, quiverDimensionVectorK0_of]

/-- The pulled-back Ringel form is determined by its values on pairs of module classes. -/
theorem quiverEulerPairingK0_unique
    (b : LinearMap.BilinForm ℤ (ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))))
    (hb : ∀ M N : FGModuleCat (pathAlgebra k Q),
      b (ExactK0.of M) (ExactK0.of N) =
        eulerForm Q
          (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj M.obj) i : ℤ))
          (fun i ↦ (dimVector ((quiverRepFunctor k Q).obj N.obj) i : ℤ))) :
    b = quiverEulerPairingK0 k Q := by
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro M
  apply LinearMap.toAddMonoidHom_injective
  apply ExactK0.hom_ext
  intro N
  exact (hb M N).trans (quiverEulerPairingK0_of_of k Q M N).symm

end EulerPairing

end TauCeti
