/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Product
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.PathSpace.Prepend

/-!
# Null-homotopies of a loop as a torsor under the second homotopy group

Let `γ` be a loop at `x` in a space `X`. A *null-homotopy* of `γ` is a path in the loop space
`Ω X x` from the constant loop to `γ`, that is, a map `h : I × I → X` with `h(0, t) = x`,
`h(1, t) = γ t` and `h(s, 0) = h(s, 1) = x`. Collapsing the three edges of the square on which
`h` is constant to a point turns `h` into a disc bounding `γ`; classes of null-homotopies are the
based model of homotopy classes of discs bounding `γ`. In Hamiltonian Floer theory they serve as
the raw caps of a contractible periodic orbit.

This file proves that the classes of null-homotopies `Path.NullHomotopyClass γ` form a torsor
under the second homotopy group `π_2(X, x)` as soon as `γ` is contractible
(`Path.nonempty_nullHomotopyClass_iff`). An element `a ∈ π_2(X, x)` is a loop at the constant
loop in `Ω X x` (`HomotopyGroup.pi2MulEquivFundamentalGroupLoopSpace`), and `a +ᵥ D` runs this
loop before the null-homotopy `D`: on discs, it glues a sphere representing `a` to the disc
representing `D`. The difference `D -ᵥ D'` is the sphere obtained by gluing `D` to the reverse of
`D'` along `γ`.

A homotopy class `u` of homotopies from the concatenation `γ₁ · γ₂` to a loop `γ₀`, a pair of
pants with inputs `γ₁`, `γ₂` and output `γ₀`, glues null-homotopies `D₁` of `γ₁` and `D₂` of
`γ₂` to the null-homotopy `Path.NullHomotopyClass.glue u D₁ D₂` of `γ₀`: concatenate `D₁` and
`D₂` pointwise in the loop space, then follow `u`. Gluing is equivariant in each input
(`Path.NullHomotopyClass.glue_vadd_left`, `Path.NullHomotopyClass.glue_vadd_right`), so recapping
an input of a pair of pants by a sphere recaps the glued output by the same sphere. The proof
uses that concatenating with the constant loop is homotopic to the identity of `Ω X x` relative
to the constant loop (`Path.Homotopic.Quotient.cast_map_trans_prod_refl`,
`Path.Homotopic.Quotient.cast_map_trans_refl_prod`).

## Main declarations

* `Path.NullHomotopyClass γ`: homotopy classes of null-homotopies of the loop `γ`.
* `Path.NullHomotopyClass.instAddTorsor`: for contractible `γ`, these classes form a torsor under
  `π_2(X, x)`.
* `Path.NullHomotopyClass.glue`: gluing null-homotopies of two loops along a homotopy from their
  concatenation, equivariant in each input.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, for caps of contractible loops.
* A. Hatcher, *Algebraic Topology*, Section 4.1, for `π_n(Ω X) ≅ π_(n + 1)(X)`.
-/

public section

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

namespace Path

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The homotopy classes of **null-homotopies** of a loop `γ` at `x`: paths in the loop space
`Ω X x` from the constant loop to `γ`, up to homotopy relative to the endpoints. They model
homotopy classes of discs bounding `γ`. -/
abbrev NullHomotopyClass (γ : Path x x) : Type _ :=
  Path.Homotopic.Quotient (Path.refl x) γ

/-- A loop has a null-homotopy exactly when it is homotopic to the constant loop. -/
theorem nonempty_nullHomotopyClass_iff {γ : Path x x} :
    Nonempty γ.NullHomotopyClass ↔ γ.Homotopic (Path.refl x) := by
  refine ⟨fun ⟨D⟩ => ?_, fun h =>
    ⟨Path.Homotopic.Quotient.mk (Path.joined_iff_homotopic.2 h.symm).somePath⟩⟩
  induction D using Path.Homotopic.Quotient.ind with
  | mk p => exact (Path.joined_iff_homotopic.1 ⟨p⟩).symm

namespace NullHomotopyClass

open HomotopyGroup

variable {γ : Path x x}

/-- An element `a` of `π_2(X, x)` acts on null-homotopies of `γ` by running the corresponding loop
at the constant loop before the null-homotopy. -/
instance instVAdd : VAdd (Additive (π_ 2 X x)) γ.NullHomotopyClass where
  vadd a D := (pi2MulEquivFundamentalGroupLoopSpace a.toMul).toPath.trans D

theorem vadd_def (a : Additive (π_ 2 X x)) (D : γ.NullHomotopyClass) :
    a +ᵥ D = (pi2MulEquivFundamentalGroupLoopSpace a.toMul).toPath.trans D :=
  (rfl)

instance instAddAction : AddAction (Additive (π_ 2 X x)) γ.NullHomotopyClass where
  zero_vadd D := by
    rw [vadd_def, toMul_zero, _root_.map_one]
    exact Path.Homotopic.Quotient.refl_trans D
  add_vadd a b D := by
    -- `π_2` is commutative, while the loop of `a + b` runs the loop of `b` first.
    rw [add_comm a b, vadd_def, vadd_def, vadd_def, toMul_add, _root_.map_mul]
    exact Path.Homotopic.Quotient.trans_assoc _ _ D

/-- The difference of two null-homotopies `D` and `D'` of `γ`: the element of `π_2(X, x)` given by
the loop `D` followed by the reverse of `D'`. -/
instance instVSub : VSub (Additive (π_ 2 X x)) γ.NullHomotopyClass where
  vsub D D' := .ofMul (pi2MulEquivFundamentalGroupLoopSpace.symm
    (FundamentalGroup.fromPath (D.trans D'.symm)))

theorem vsub_def (D D' : γ.NullHomotopyClass) :
    D -ᵥ D' = .ofMul (pi2MulEquivFundamentalGroupLoopSpace.symm
      (FundamentalGroup.fromPath (D.trans D'.symm))) :=
  (rfl)

/-- **The null-homotopies of a contractible loop form a torsor under `π_2(X, x)`.** -/
instance instAddTorsor [Nonempty γ.NullHomotopyClass] :
    AddTorsor (Additive (π_ 2 X x)) γ.NullHomotopyClass where
  vsub_vadd' D D' := by
    rw [vsub_def, vadd_def, toMul_ofMul, MulEquiv.apply_symm_apply,
      Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans]
    exact Path.Homotopic.Quotient.trans_refl D
  vadd_vsub' a D := by
    rw [vsub_def, vadd_def, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]
    exact congrArg Additive.ofMul (MulEquiv.symm_apply_apply _ _)

/-! ### Gluing null-homotopies along a pair of pants -/

section Glue

/-- Concatenating every loop of a loop of loops `L` at the constant loop with the constant loop
does not change its homotopy class. -/
theorem _root_.Path.Homotopic.Quotient.cast_map_trans_prod_refl
    (L : Path.Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Path.Homotopic.prod L (Path.Homotopic.Quotient.refl (Path.refl x))).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
        Path.refl_trans_refl.symm Path.refl_trans_refl.symm = L := by
  induction L using Path.Homotopic.Quotient.ind with
  | mk L =>
    rw [← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.prod_lift,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    refine Quotient.sound (show Path.Homotopic _ _ from ?_)
    convert Path.Homotopic.cast_map_reparam L
      (f := fun t =>
        ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩)
      (by fun_prop) (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) using 1
    ext s : 2
    exact Path.Homotopy.trans_refl_reparam (L s)

/-- Concatenating the constant loop with every loop of a loop of loops `L` at the constant loop
does not change its homotopy class. -/
theorem _root_.Path.Homotopic.Quotient.cast_map_trans_refl_prod
    (L : Path.Homotopic.Quotient (Path.refl x) (Path.refl x)) :
    ((Path.Homotopic.prod (Path.Homotopic.Quotient.refl (Path.refl x)) L).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
        Path.refl_trans_refl.symm Path.refl_trans_refl.symm = L := by
  induction L using Path.Homotopic.Quotient.ind with
  | mk L =>
    rw [← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.prod_lift,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    refine Quotient.sound (show Path.Homotopic _ _ from ?_)
    convert Path.Homotopic.cast_map_reparam L
      (f := fun t => Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))
      (by fun_prop) (Subtype.ext (by norm_num)) (Subtype.ext (by norm_num)) using 1
    ext s : 2
    exact Path.refl_trans_eq_reparam (L s)

variable {γ₁ γ₂ γ₀ : Path x x}

/-- **Gluing null-homotopies along a pair of pants.** A homotopy class `u` of homotopies from the
concatenation `γ₁.trans γ₂` to `γ₀` glues null-homotopies `D₁` of `γ₁` and `D₂` of `γ₂` to a
null-homotopy of `γ₀`: concatenate `D₁` and `D₂` pointwise in the loop space, then follow `u`. -/
def glue (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀) (D₁ : γ₁.NullHomotopyClass)
    (D₂ : γ₂.NullHomotopyClass) : γ₀.NullHomotopyClass :=
  (((Path.Homotopic.prod D₁ D₂).map
    ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
      Path.refl_trans_refl.symm rfl).trans u

theorem glue_def (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀) (D₁ : γ₁.NullHomotopyClass)
    (D₂ : γ₂.NullHomotopyClass) :
    glue u D₁ D₂ = (((Path.Homotopic.prod D₁ D₂).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast
        Path.refl_trans_refl.symm rfl).trans u :=
  (rfl)

/-- Gluing a sphere to the first input of a pair of pants glues it to the output. -/
theorem glue_vadd_left (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀)
    (a : Additive (π_ 2 X x)) (D₁ : γ₁.NullHomotopyClass) (D₂ : γ₂.NullHomotopyClass) :
    glue u (a +ᵥ D₁) D₂ = a +ᵥ glue u D₁ D₂ := by
  rw [glue_def, glue_def, vadd_def, vadd_def]
  conv_lhs => rw [← Path.Homotopic.Quotient.refl_trans D₂,
    ← Path.Homotopic.comp_prod_eq_prod_comp,
    Path.Homotopic.Quotient.map_trans_cast _ _ _ Path.refl_trans_refl.symm rfl,
    Path.Homotopic.Quotient.cast_map_trans_prod_refl]
  exact Path.Homotopic.Quotient.trans_assoc _ _ u

/-- Gluing a sphere to the second input of a pair of pants glues it to the output. -/
theorem glue_vadd_right (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀)
    (a : Additive (π_ 2 X x)) (D₁ : γ₁.NullHomotopyClass) (D₂ : γ₂.NullHomotopyClass) :
    glue u D₁ (a +ᵥ D₂) = a +ᵥ glue u D₁ D₂ := by
  rw [glue_def, glue_def, vadd_def, vadd_def]
  conv_lhs => rw [← Path.Homotopic.Quotient.refl_trans D₁,
    ← Path.Homotopic.comp_prod_eq_prod_comp,
    Path.Homotopic.Quotient.map_trans_cast _ _ _ Path.refl_trans_refl.symm rfl,
    Path.Homotopic.Quotient.cast_map_trans_refl_prod]
  exact Path.Homotopic.Quotient.trans_assoc _ _ u

end Glue

end NullHomotopyClass

end Path
