/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis
public import TauCeti.RepresentationTheory.Quiver.Acyclic.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Representation.VertexSimpleModule

/-!
# The vertex simples as a simple family of a path algebra

Let `Q` be a finite quiver whose path algebra `kQ` is finite-dimensional, that is, a finite
acyclic quiver. Its simple modules are the vertex simples `Sᵢ`, so the family of vertex simples,
viewed as finitely generated `kQ`-modules, is an exhaustive family of simple modules in the sense of
`TauCeti.IsExhaustiveSimpleFamily`. Their classes therefore span `G₀(mod kQ)`, and any additive
identity on that group can be checked on them.

## Main results

* `TauCeti.vertexSimpleModuleFG`: the vertex simple `Sᵢ` as a finitely generated module.
* `TauCeti.isExhaustiveSimpleFamily_vertexSimpleModuleFG`: the vertex simples exhaust the simple
  modules of a finite-dimensional path algebra.

## References

* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory
  of Associative Algebras I*, Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- The vertex simple `Sᵢ` as an object of the category of finitely generated modules. -/
-- Exposed so that the underlying module is `vertexSimpleModule k Q i` by `rfl` in importing
-- modules, where the implicit module arguments of `extEuler` have to match definitionally.
@[expose]
noncomputable def vertexSimpleModuleFG (i : Q) : FGModuleCat (pathAlgebra k Q) :=
  ⟨vertexSimpleModule k Q i, inferInstanceAs (Module.Finite _ (vertexSimpleModule k Q i))⟩

/-- The underlying module of the finitely generated vertex simple is the vertex simple module. -/
@[simp]
theorem vertexSimpleModuleFG_obj (i : Q) :
    (vertexSimpleModuleFG k Q i).obj = vertexSimpleModule k Q i := by
  rfl

/-- The finitely generated vertex simple is a simple module. -/
instance isSimpleModule_vertexSimpleModuleFG (i : Q) :
    IsSimpleModule (pathAlgebra k Q) (vertexSimpleModuleFG k Q i) :=
  inferInstanceAs (IsSimpleModule (pathAlgebra k Q) (vertexSimpleModule k Q i))

variable [FiniteDimensional k (pathAlgebra k Q)]

/-- **The vertex simples exhaust the simple modules of a finite-dimensional path algebra.** -/
theorem isExhaustiveSimpleFamily_vertexSimpleModuleFG :
    IsExhaustiveSimpleFamily (vertexSimpleModuleFG k Q) := by
  rw [isExhaustiveSimpleFamily_iff]
  intro M hM
  have hQ : Quiver.IsAcyclic Q := isAcyclic_of_module_finite_pathAlgebra k Q inferInstance
  have : Simple M.obj := (simple_iff_isSimpleModule' M.obj).mpr hM
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_vertexSimpleModule_of_simple k Q hQ M.obj
  exact ⟨i, ⟨e.toLinearEquiv⟩⟩

end TauCeti
