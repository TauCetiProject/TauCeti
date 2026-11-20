/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous and algebraic intertwiners

For finite-dimensional Hausdorff topological vector spaces over a complete nontrivially normed
field, automatic continuity identifies continuous intertwiners and equivalences with their
algebraic counterparts. The object and character side is already supplied by the
universe-polymorphic `FDRep.ofShrink`,
`FDRep.ofShrinkEquiv`, and `FDRep.character_ofShrink`; this file adds the missing intertwiner
side, together with the passage from an algebraic representation on such a space to a continuous
one.

## Main declarations

* `ContIntertwiningMap.toIntertwiningMap_apply`: the algebraic intertwiner underlying a
  continuous one has the same values.
* `ContRepresentation.intertwiningMapEquiv`: continuous intertwiners are linearly equivalent to
  algebraic intertwiners.
* `ContRepresentation.nonempty_equiv_iff`: continuous and algebraic representation equivalence
  agree.
* `Representation.toContRepresentation`: a representation on a finite-dimensional space as a
  continuous representation, with `Representation.toContRepresentation_toRepresentation` recovering
  the original representation and `ContRepresentation.toRepresentation_toContRepresentation`
  recovering a continuous one.

The file also records that continuous intertwiners from a finitely generated representation to a
Noetherian one form a finitely generated module, over any commutative ring and without
completeness; over a field, intertwiners between finite-dimensional representations thus form a
finite-dimensional space.
-/

public section

namespace ContIntertwiningMap

variable {R G V W : Type*} [Ring R] [Monoid G]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  {π : ContRepresentation R G V} {ρ : ContRepresentation R G W}

/-- Evaluation of the algebraic intertwining map underlying a continuous one: forgetting
continuity does not change the map. -/
@[simp]
theorem toIntertwiningMap_apply (f : ContIntertwiningMap π ρ) (v : V) :
    f.toIntertwiningMap v = f v :=
  (rfl)

end ContIntertwiningMap

namespace ContIntertwiningMap

variable {R G V W : Type*} [CommRing R] [Monoid G]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul R W] {π : ContRepresentation R G V} {ρ : ContRepresentation R G W}

/-- Continuous intertwiners from a finitely generated representation to a Noetherian one form a
finitely generated module. In particular, over a field, continuous intertwiners between
finite-dimensional representations form a finite-dimensional space.

This is the continuous counterpart of Mathlib's instance
`Representation.IntertwiningMap.instFiniteOfIsNoetherian` for algebraic intertwiners. -/
instance instModuleFinite [Module.Finite R V] [IsNoetherian R W] :
    Module.Finite R (ContIntertwiningMap π ρ) :=
  -- As in Mathlib's algebraic instance: embed into the linear maps `V →ₗ[R] W`, which form a
  -- Noetherian module by `isNoetherian_linearMap`.
  .of_injective (σ := RingHom.id R)
    { toFun f := (f.toContinuousLinearMap : V →ₗ[R] W)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    fun _ _ h ↦ ContIntertwiningMap.ext (ContinuousLinearMap.coe_injective h)

end ContIntertwiningMap

namespace ContRepresentation

section Intertwiners

variable {𝕜 G V W U : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W]
  [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul 𝕜 U]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
  {τ : ContRepresentation 𝕜 G U}

/-- In finite dimensions, forgetting continuity identifies continuous intertwining maps with
algebraic intertwining maps. The inverse equips the underlying linear map with its automatic
continuity. -/
noncomputable def intertwiningMapEquiv :
    ContIntertwiningMap π ρ ≃ₗ[𝕜]
      Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation where
  toFun f := f.toIntertwiningMap
  invFun f :=
    { toContinuousLinearMap := LinearMap.toContinuousLinearMap f.toLinearMap
      isIntertwining' g := ContinuousLinearMap.ext (f.isIntertwining _ _ g) }
  left_inv _ := ContIntertwiningMap.ext rfl
  right_inv _ := Representation.IntertwiningMap.ext rfl
  map_add' _ _ := Representation.IntertwiningMap.ext rfl
  map_smul' _ _ := Representation.IntertwiningMap.ext rfl

/-- The forward intertwiner identification is the existing forgetful map. -/
theorem intertwiningMapEquiv_apply (f : ContIntertwiningMap π ρ) :
    intertwiningMapEquiv f = f.toIntertwiningMap :=
  (rfl)

/-- The forward intertwiner identification preserves pointwise evaluation. -/
@[simp]
theorem intertwiningMapEquiv_apply_apply (f : ContIntertwiningMap π ρ) (v : V) :
    intertwiningMapEquiv f v = f v :=
  (rfl)

/-- The inverse intertwiner identification preserves pointwise evaluation. -/
@[simp]
theorem intertwiningMapEquiv_symm_apply_apply
    (f : Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation) (v : V) :
    intertwiningMapEquiv.symm f v = f v :=
  (rfl)

/-- The intertwiner identification preserves identity maps. -/
@[simp high]
theorem intertwiningMapEquiv_id :
    intertwiningMapEquiv (ContIntertwiningMap.id : ContIntertwiningMap π π) =
      Representation.IntertwiningMap.id π.toRepresentation :=
  (rfl)

/-- The intertwiner identification preserves composition. -/
@[simp high]
theorem intertwiningMapEquiv_comp [T2Space W] [FiniteDimensional 𝕜 W]
    (f : ContIntertwiningMap ρ τ) (g : ContIntertwiningMap π ρ) :
    intertwiningMapEquiv (f.comp g) =
      (intertwiningMapEquiv f).comp (intertwiningMapEquiv g) :=
  (rfl)

/-- The inverse intertwiner identification preserves identity maps. -/
@[simp high]
theorem intertwiningMapEquiv_symm_id :
    intertwiningMapEquiv.symm (Representation.IntertwiningMap.id π.toRepresentation) =
      (ContIntertwiningMap.id : ContIntertwiningMap π π) :=
  ContIntertwiningMap.ext rfl

/-- The inverse intertwiner identification preserves composition. -/
@[simp high]
theorem intertwiningMapEquiv_symm_comp [T2Space W] [FiniteDimensional 𝕜 W]
    (f : Representation.IntertwiningMap ρ.toRepresentation τ.toRepresentation)
    (g : Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation) :
    intertwiningMapEquiv.symm (f.comp g) =
      (intertwiningMapEquiv.symm f).comp (intertwiningMapEquiv.symm g) :=
  ContIntertwiningMap.ext rfl

end Intertwiners

section Equivalence

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W] [T2Space W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- Two finite-dimensional Hausdorff continuous representations over a complete field are
continuously equivalent exactly when their underlying algebraic representations are equivalent. -/
theorem nonempty_equiv_iff :
    Nonempty (_root_.ContRepresentation.Equiv π ρ) ↔
      Nonempty (Representation.Equiv π.toRepresentation ρ.toRepresentation) :=
  ⟨fun ⟨φ⟩ ↦ ⟨.mk φ.toContinuousLinearEquiv.toLinearEquiv fun g ↦
      LinearMap.ext (φ.toContIntertwiningMap.isIntertwining g)⟩,
    fun ⟨φ⟩ ↦ ⟨.mk φ.toLinearEquiv.toContinuousLinearEquiv fun g ↦
      ContinuousLinearMap.ext (φ.toIntertwiningMap.isIntertwining _ _ g)⟩⟩

end Equivalence

end ContRepresentation

namespace Representation

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

/-- A representation on a finite-dimensional Hausdorff topological vector space over a complete
field, as a continuous representation: each operator `ρ g` is equipped with its automatic
continuity. -/
noncomputable def toContRepresentation (ρ : Representation 𝕜 G V) : ContRepresentation 𝕜 G V :=
  .ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap (ρ g)
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

/-- The continuous representation built from `ρ` acts on vectors as `ρ` does. -/
@[simp]
theorem toContRepresentation_apply (ρ : Representation 𝕜 G V) (g : G) (v : V) :
    ρ.toContRepresentation g v = ρ g v :=
  (rfl)

/-- Forgetting continuity of `ρ.toContRepresentation` recovers `ρ`. -/
@[simp]
theorem toContRepresentation_toRepresentation (ρ : Representation 𝕜 G V) :
    ρ.toContRepresentation.toRepresentation = ρ :=
  (rfl)

/-- Equipping the underlying representation of `π` with its automatic continuity recovers `π`. -/
@[simp]
theorem _root_.ContRepresentation.toRepresentation_toContRepresentation
    (π : ContRepresentation 𝕜 G V) : π.toRepresentation.toContRepresentation = π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

end Representation
