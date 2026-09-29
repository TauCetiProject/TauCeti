/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.DimensionVector
public import TauCeti.RepresentationTheory.GrothendieckGroup.Quiver.SimpleBasis
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Finite

/-!
# Composition multiplicities and vertex dimensions for path algebras

For a finite acyclic quiver, the multiplicity of the vertex simple `Sᵢ` in a finite-dimensional
path-algebra module is the dimension of its `i`th vertex space. Both functions are additive in
short exact sequences. They agree on the vertex simples, which generate the Grothendieck group.
For a vertex projective `Pⱼ`, this identifies its multiplicity of `Sᵢ` with the number of paths
from `j` to `i`. These are the columns of the Cartan matrix in the left-module convention.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter III, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

/-- The `i`th Jordan--Hölder coordinate on `G₀(mod kQ)` equals the `i`th vertex dimension. -/
@[simp]
theorem jordanHolderCoordinate_vertexSimpleModuleFG_eq_dimVector (i : Q)
    (x : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :
    jordanHolderCoordinate (pathAlgebra k Q) (vertexSimpleModuleFG k Q i) x =
      pathAlgebraDimensionVectorK0 k Q x i := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let S := vertexSimpleModuleFG k Q
  let f : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ ℤ :=
    jordanHolderCoordinate (pathAlgebra k Q) (S i)
  let g : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) →+ ℤ :=
    (Pi.evalAddMonoidHom (fun _ : Q ↦ ℤ) i).comp (pathAlgebraDimensionVectorK0 k Q)
  have hfg : f = g := by
    apply AddMonoidHom.toIntLinearMap_injective
    refine LinearMap.ext_on_range
      (span_range_exactK0OfFamily_eq_top S
        (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q)) fun j ↦ ?_
    have hS := jordanHolderCoordinate_exactK0OfFamily S
      (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q) i j
    have hdim := dimVector_eq_of_iso (vertexSimpleModuleIso k Q j)
    simp only [f, g, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply,
      exactK0OfFamily_apply, pathAlgebraDimensionVectorK0_of,
      Pi.evalAddMonoidHom_apply] at hS ⊢
    simp only [S, vertexSimpleModuleFG_obj] at hS ⊢
    rw [hdim, dimVector_simpleRep, Pi.single_apply]
    simpa only [eq_comm, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hS
  exact DFunLike.congr_fun hfg x

/-- The exact Grothendieck group of finite-dimensional `kQ`-modules is the integral lattice of
vertex dimensions. The inverse sends a dimension vector to the corresponding integral combination
of vertex-simple classes. -/
noncomputable def pathAlgebraDimensionVectorK0Equiv :
    ExactK0 (finiteModulesExactStructure (pathAlgebra k Q)) ≃+ (Q → ℤ) :=
  (simpleClassBasis (vertexSimpleModuleFG k Q)
    (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
    (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q)).equivFun.toAddEquiv

/-- The forward Grothendieck-group equivalence is the dimension-vector map. -/
@[simp]
theorem pathAlgebraDimensionVectorK0Equiv_apply
    (x : ExactK0 (finiteModulesExactStructure (pathAlgebra k Q))) :
    pathAlgebraDimensionVectorK0Equiv k Q x = pathAlgebraDimensionVectorK0 k Q x := by
  classical
  funext i
  let b := simpleClassBasis (vertexSimpleModuleFG k Q)
    (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
    (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q)
  have h := congrFun (b.equivFun_apply x) i
  rw [simpleClassBasis_repr_apply] at h
  simpa only [pathAlgebraDimensionVectorK0Equiv, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply, b]
    using h.trans (jordanHolderCoordinate_vertexSimpleModuleFG_eq_dimVector k Q i x)

/-- A vertex simple maps to the corresponding standard basis vector. -/
-- The general equivalence and dimension-vector simp lemmas already simplify the left-hand side.
theorem pathAlgebraDimensionVectorK0Equiv_vertexSimple [DecidableEq Q] (i : Q) :
    pathAlgebraDimensionVectorK0Equiv k Q (ExactK0.of (vertexSimpleModuleFG k Q i)) =
      Pi.single i 1 := by
  classical
  rw [pathAlgebraDimensionVectorK0Equiv_apply, pathAlgebraDimensionVectorK0_of,
    vertexSimpleModuleFG_obj, dimVector_eq_of_iso (vertexSimpleModuleIso k Q i),
    dimVector_simpleRep]
  funext j
  simp [Pi.single_apply]

section

attribute [local instance] Fintype.ofFinite

/-- The inverse dimension-vector equivalence expands an integral vertex vector in the classes of
the vertex simples. -/
@[simp]
theorem pathAlgebraDimensionVectorK0Equiv_symm_apply (d : Q → ℤ) :
    (pathAlgebraDimensionVectorK0Equiv k Q).symm d =
      ∑ i, d i • ExactK0.of (vertexSimpleModuleFG k Q i) := by
  classical
  let b := simpleClassBasis (vertexSimpleModuleFG k Q)
    (pairwise_isEmpty_linearEquiv_vertexSimpleModuleFG k Q)
    (isExhaustiveSimpleFamily_vertexSimpleModuleFG k Q)
  simpa only [pathAlgebraDimensionVectorK0Equiv,
    ← LinearEquiv.coe_toAddEquiv_symm, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply, b, simpleClassBasis_apply]
    using b.equivFun_symm_apply d

end

/-- The multiplicity of `Sᵢ` in a finitely generated `kQ`-module is the dimension of its `i`th
vertex space. -/
@[simp]
theorem jordanHolderMultiplicity_vertexSimpleModuleFG_eq_dimVector
    (M : FGModuleCat.{max v w} (pathAlgebra k Q)) (i : Q) :
    jordanHolderMultiplicity (pathAlgebra k Q) M (vertexSimpleModuleFG k Q i) =
      dimVector ((quiverRepFunctor k Q).obj M.obj) i := by
  have h := jordanHolderCoordinate_vertexSimpleModuleFG_eq_dimVector k Q i (ExactK0.of M)
  simp only [jordanHolderCoordinate_of, pathAlgebraDimensionVectorK0_of] at h
  exact_mod_cast h

/-- **The Cartan path-count formula.** The multiplicity of `Sᵢ` in the vertex projective `Pⱼ`
is the number of oriented paths from `j` to `i`. With simples in rows and projectives in columns,
these are the entries of the Cartan matrix of a finite acyclic path algebra. -/
-- The general multiplicity and projective-object simp lemmas simplify the left-hand side first;
-- marking this specialization `@[simp]` fails the `simpNF` linter.
theorem jordanHolderMultiplicity_vertexProjectiveModuleFG_eq_card_path (i j : Q) :
    jordanHolderMultiplicity (pathAlgebra k Q)
      (vertexProjectiveModuleFG k Q j)
      (vertexSimpleModuleFG k Q i) = Nat.card (Quiver.Path j i) := by
  rw [jordanHolderMultiplicity_vertexSimpleModuleFG_eq_dimVector,
    vertexProjectiveModuleFG_obj,
    dimVector_eq_of_iso (indecProjModuleIso k Q j), dimVector_indecProjRep]

end TauCeti
