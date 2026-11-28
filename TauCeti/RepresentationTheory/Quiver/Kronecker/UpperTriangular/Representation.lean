/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Modules over upper-triangular matrices as one-arrow representations

The identification `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv` of the one-arrow path
algebra with upper-triangular `2 × 2` matrices induces a linear equivalence between the module
and representation categories.
Finitely generated modules correspond to pointwise finite-dimensional representations.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition III.2.2.
-/

public section

namespace TauCeti

open CategoryTheory ModuleCat Quiver.Kronecker
open scoped ModuleCat.Algebra

universe u

variable (k : Type u) [Field k]

local notation "T₂" => Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)
local notation "Q" => Quiver.Kronecker Unit

local notation "matrixEquiv" => AlgEquiv.toRingEquiv (upperTriangularAlgEquiv (A := Unit) k)

/-- The module category of upper-triangular `2 × 2` matrices is equivalent to representations
of the one-arrow quiver. The off-diagonal matrix unit acts as the arrow map. -/
noncomputable def upperTriangularRepEquivalence :
    ModuleCat.{u} T₂ ≌ QuiverRep.{u, 0, 0, u} k Q :=
  (restrictScalarsEquivalenceOfRingEquiv matrixEquiv).trans
    (quiverRepFunctor k Q).asEquivalence

local notation "e" => upperTriangularRepEquivalence k

/-- The forward functor reads the representation of the path-algebra module obtained by
restricting scalars along the upper-triangular algebra identification. -/
theorem upperTriangularRepEquivalence_functor :
    (e).functor = restrictScalars (RingEquiv.toRingHom matrixEquiv) ⋙ quiverRepFunctor k Q :=
  (rfl)

/-- The comparison functor preserves addition of module homomorphisms. -/
instance : (e).functor.Additive :=
  inferInstanceAs <| Functor.Additive
    ((restrictScalarsEquivalenceOfRingEquiv matrixEquiv).functor ⋙ quiverRepFunctor k Q)

/-- The comparison functor preserves scalar multiplication by the ground field. -/
instance : (e).functor.Linear k :=
  inferInstanceAs <| Functor.Linear k
    ((restrictScalarsEquivalenceOfRingEquiv matrixEquiv).functor ⋙ quiverRepFunctor k Q)

/-- Finite generation of an upper-triangular module is equivalent to finite dimensionality of
both vertex spaces in the corresponding representation. -/
theorem isFinDim_upperTriangularRep_iff (M : ModuleCat.{u} T₂) :
    IsFinDim k Q ((e).functor.obj M) ↔ Module.Finite T₂ M := by
  let a := upperTriangularAlgEquiv (A := Unit) k
  let N := (restrictScalars a.toRingEquiv.toRingHom).obj M
  have hN := a.toRingEquiv.toRingHom.finite_restrictScalars_iff a.surjective M
  rw [upperTriangularRepEquivalence_functor, Functor.comp_obj, ← hN]
  constructor
  · intro h
    have : Module.Finite (pathAlgebra k Q)
        (((quiverRepEquivalence k Q).inverse ⋙ (quiverRepEquivalence k Q).functor).obj N) :=
      module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q _
        (by rwa [quiverRepEquivalence_inverse])
    exact Module.Finite.equiv ((quiverRepEquivalence k Q).counitIso.app N).toLinearEquiv
  · intro h
    exact isFinDim_quiverRepFunctor_obj k Q N (Module.Finite.trans (pathAlgebra k Q) N)

end TauCeti
