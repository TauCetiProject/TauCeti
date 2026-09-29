/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.Algebra.Category.FGModuleCat.Projective

/-!
# Finiteness of vertex projectives

When a path algebra is finite-dimensional, every vertex projective is a finitely generated module.
The proof transports the finite-dimensionality of its path basis through the equivalence between
quiver representations and path-algebra modules. This lets vertex projectives enter the finite
module category and its Grothendieck group.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u v w

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- A vertex projective is finitely generated when the path algebra is finite-dimensional. -/
theorem module_finite_indecProjModule [FiniteDimensional k (pathAlgebra k Q)] (i : Q) :
    Module.Finite (pathAlgebra k Q) (indecProjModule k Q i) := by
  classical
  let hpaths : Finite (Σ a b : Q, Quiver.Path a b) :=
    (module_finite_pathAlgebra_iff k Q).mp inferInstance
  let hpath (a b : Q) : Finite (Quiver.Path a b) :=
    Finite.of_injective
      (fun p : Quiver.Path a b ↦ (⟨a, b, p⟩ : Σ x y : Q, Quiver.Path x y))
      (fun _ _ h ↦ by cases h; rfl)
  let M := indecProjRep k Q i
  have hM : IsFinDim k Q M := by
    rw [isFinDim_iff]
    intro v
    let _ : Finite (Quiver.Path i v) := hpath i v
    exact finiteDimensional_indecProjRep_obj i v
  let hmodule : Module.Finite (pathAlgebra k Q) (QuiverRep.asModule k Q M) :=
    module_finite_asModule_of_isFinDim k Q M hM
  let hshrink : Module.Finite (pathAlgebra k Q) (QuiverRep.asModuleShrink k Q M) :=
    Module.Finite.equiv (QuiverRep.asModuleShrinkEquiv k Q M).symm
  let e : indecProjModule k Q i ≅ QuiverRep.asModuleShrink k Q M :=
    (quiverRepFunctorFullyFaithful k Q).preimageIso
      (indecProjModuleIso k Q i ≪≫ (QuiverRep.asModuleShrinkIso k Q M).symm)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- A vertex projective as a finitely generated path-algebra module. -/
noncomputable def vertexProjectiveModuleFG [FiniteDimensional k (pathAlgebra k Q)] (i : Q) :
    FGModuleCat (pathAlgebra k Q) :=
  ⟨indecProjModule k Q i, module_finite_indecProjModule k Q i⟩

/-- The underlying module of a finite vertex projective is `indecProjModule`. -/
@[simp]
theorem vertexProjectiveModuleFG_obj [FiniteDimensional k (pathAlgebra k Q)] (i : Q) :
    (vertexProjectiveModuleFG k Q i).obj = indecProjModule k Q i := by
  rfl

/-- A finite vertex projective is projective as a path-algebra module. -/
instance [FiniteDimensional k (pathAlgebra k Q)] (i : Q) :
    Module.Projective (pathAlgebra k Q) (vertexProjectiveModuleFG k Q i) := by
  -- The module coercion of `FGModuleCat` unfolds to `.obj`, where the object equality rewrites.
  change Module.Projective (pathAlgebra k Q) (vertexProjectiveModuleFG k Q i).obj
  rw [vertexProjectiveModuleFG_obj]
  infer_instance

/-- A finite vertex projective is a projective object of finitely generated modules. -/
instance [FiniteDimensional k (pathAlgebra k Q)] (i : Q) :
    Projective (vertexProjectiveModuleFG k Q i) :=
  FGModuleCat.projective_of_moduleProjective (pathAlgebra k Q) _

end TauCeti
