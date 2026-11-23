/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic
public import TauCeti.Algebra.DirectSum.Supported
import Mathlib.LinearAlgebra.DFinsupp
import TauCeti.Algebra.Lie.Basic

/-!
# Wall spaces at a joint

The wall spaces whose normals annihilate a set of tangent vectors span a Lie
subalgebra. Their brackets lie in the transverse submodule, which is spanned by
those wall spaces whose geometric degrees lie outside the tangent set. In an
internal grading this forces every homogeneous bracket component with geometric
degree in the tangent set to vanish.

For a scattering-diagram joint one takes the tangent set to be its tangent
lattice. The algebraic statement also applies to an arbitrary set of tangent
vectors. It uses the contracted-bracket law and the existing vanishing
criterion for a homogeneous bracket.

Adapted from `Mei/Geometry/ScatteringDiagram/WallSpace/Joint.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).

For the joint calculation in the directed setting, see Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Theorem 2.6.
-/

public section

namespace TauCeti.DirectedWallSpaces

variable {Γ Λ R L : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ) (W : Set Λ)

private abbrev JointIndex (Γ : Type*) (W : Set Λ) :=
  Γ × {m : Λ →+ ℤ // ∀ v ∈ W, m v = 0}

private def jointSpan : Submodule R L :=
  ⨆ p : JointIndex Γ W, H.wall p.1 p.2

/-- The wall spaces whose normal annihilates the tangent set and whose geometric
degree lies outside it span the transverse submodule. -/
def transverseJointSubmodule : Submodule R L :=
  ⨆ p : {p : JointIndex Γ W // ρ p.1 ∉ W}, H.wall p.val.1 p.val.2

/-- The transverse submodule is the supremum indexed by tangent-annihilating
normals and degrees whose images lie outside the tangent set. -/
theorem transverseJointSubmodule_eq_iSup :
    H.transverseJointSubmodule W =
      ⨆ p : {p : Γ × {m : Λ →+ ℤ // ∀ v ∈ W, m v = 0} // ρ p.1 ∉ W},
        H.wall p.val.1 p.val.2 := (rfl)

/-- A transverse joint element is a finite sum of transverse wall elements whose normals
annihilate the tangent set. -/
theorem mem_transverseJointSubmodule_iff {x : L} :
    x ∈ H.transverseJointSubmodule W ↔
      ∃ f : {p : Γ × {m : Λ →+ ℤ // ∀ v ∈ W, m v = 0} // ρ p.1 ∉ W} →₀ L,
        (∀ p, f p ∈ H.wall p.val.1 p.val.2) ∧ f.sum (fun _ y => y) = x := by
  rw [H.transverseJointSubmodule_eq_iSup, Submodule.mem_iSup_iff_exists_finsupp]

/-- Containing the transverse joint submodule is equivalent to containing each of its generating
wall spaces. -/
theorem transverseJointSubmodule_le_iff {S : Submodule R L} :
    H.transverseJointSubmodule W ≤ S ↔
      ∀ n m, ρ n ∉ W → (∀ v ∈ W, m v = 0) → H.wall n m ≤ S := by
  rw [H.transverseJointSubmodule_eq_iSup, iSup_le_iff]
  exact ⟨fun h n m hn hm => h ⟨⟨n, ⟨m, hm⟩⟩, hn⟩,
    fun h p => h p.val.1 p.val.2 p.property p.val.2.property⟩

variable {W} in
/-- A wall space of transverse degree with normal annihilating the tangent set
lies in the transverse submodule. -/
theorem wall_le_transverseJointSubmodule {n : Γ} {m : Λ →+ ℤ} (hn : ρ n ∉ W)
    (hm : ∀ v ∈ W, m v = 0) : H.wall n m ≤ H.transverseJointSubmodule W :=
  le_iSup_of_le ⟨⟨n, ⟨m, hm⟩⟩, hn⟩ le_rfl

private theorem lie_mem_transverseJointSubmodule_aux {x y : L}
    (hx : x ∈ H.jointSpan W) (hy : y ∈ H.jointSpan W) :
    ⁅x, y⁆ ∈ H.transverseJointSubmodule W := by
  let T := H.transverseJointSubmodule W
  let A : JointIndex Γ W → Submodule R L := fun p => H.wall p.1 p.2
  refine TauCeti.lie_mem_of_mem_iSup A A T (fun p q x hx y hy => ?_) hx hy
  by_cases hn : ρ (p.1 + q.1) ∈ W
  · rw [H.lie_eq_zero_of_normal_total_eq_zero hx hy (p.2.property _ hn) (q.2.property _ hn)]
    exact T.zero_mem
  · refine H.wall_le_transverseJointSubmodule hn (fun v hv => ?_) (H.bracket_mem hx hy)
    simp [p.2.property v hv, q.2.property v hv]

/-- Wall spaces whose normals annihilate the tangent set span the joint subalgebra. -/
def jointSubalgebra : LieSubalgebra R L where
  toSubmodule := H.jointSpan W
  lie_mem' hx hy :=
    (iSup_le fun p : {p : JointIndex Γ W // ρ p.1 ∉ W} =>
      le_iSup_of_le p.val le_rfl : H.transverseJointSubmodule W ≤ H.jointSpan W)
      (H.lie_mem_transverseJointSubmodule_aux W hx hy)

/-- The joint subalgebra has the wall-space supremum as its underlying submodule. -/
theorem jointSubalgebra_toSubmodule :
    (H.jointSubalgebra W).toSubmodule =
      ⨆ p : Γ × {m : Λ →+ ℤ // ∀ v ∈ W, m v = 0}, H.wall p.1 p.2 := (rfl)

/-- A joint element is a finite sum of wall elements whose normals annihilate the tangent set. -/
theorem mem_jointSubalgebra_iff {x : L} :
    x ∈ H.jointSubalgebra W ↔
      ∃ f : (Γ × {m : Λ →+ ℤ // ∀ v ∈ W, m v = 0}) →₀ L,
        (∀ p, f p ∈ H.wall p.1 p.2) ∧ f.sum (fun _ y => y) = x := by
  rw [← LieSubalgebra.mem_toSubmodule, H.jointSubalgebra_toSubmodule,
    Submodule.mem_iSup_iff_exists_finsupp]

/-- A Lie subalgebra contains the joint subalgebra exactly when it contains each wall space
whose normal annihilates the tangent set. -/
theorem jointSubalgebra_le_iff {S : LieSubalgebra R L} :
    H.jointSubalgebra W ≤ S ↔
      ∀ n m, (∀ v ∈ W, m v = 0) → H.wall n m ≤ S.toSubmodule := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, H.jointSubalgebra_toSubmodule, iSup_le_iff]
  exact ⟨fun h n m hm => h ⟨n, ⟨m, hm⟩⟩, fun h p => h p.1 p.2 p.2.property⟩

variable {W} in
/-- A wall space with normal annihilating the tangent set lies in the joint subalgebra. -/
theorem wall_le_jointSubalgebra {n : Γ} {m : Λ →+ ℤ} (hm : ∀ v ∈ W, m v = 0) :
    H.wall n m ≤ (H.jointSubalgebra W).toSubmodule :=
  le_iSup_of_le ⟨n, ⟨m, hm⟩⟩ le_rfl

/-- The transverse submodule is contained in the joint subalgebra. -/
theorem transverseJointSubmodule_le_jointSubalgebra :
    H.transverseJointSubmodule W ≤ (H.jointSubalgebra W).toSubmodule :=
  iSup_le fun p => H.wall_le_jointSubalgebra p.val.2.property

variable {W} in
/-- Brackets of elements of the joint subalgebra are transverse. -/
theorem lie_mem_transverseJointSubmodule {x y : L}
    (hx : x ∈ H.jointSubalgebra W) (hy : y ∈ H.jointSubalgebra W) :
    ⁅x, y⁆ ∈ H.transverseJointSubmodule W :=
  H.lie_mem_transverseJointSubmodule_aux W hx hy

section Decomposition

variable [DecidableEq Γ] [_root_.DirectSum.Decomposition ℒ]

variable {W} in
/-- A transverse element has zero component in every degree whose geometric
direction lies in the tangent set. -/
theorem decompose_eq_zero_of_mem_transverseJointSubmodule {x : L}
    (hx : x ∈ H.transverseJointSubmodule W) {n : Γ} (hn : ρ n ∈ W) :
    (_root_.DirectSum.decompose ℒ x n : L) = 0 := by
  let S : Set Γ := {k | ρ k ∉ W}
  have hle : H.transverseJointSubmodule W ≤ ⨆ k : S, ℒ k := by
    refine iSup_le fun p : {p : JointIndex Γ W // ρ p.1 ∉ W} => ?_
    exact (H.wall_le_piece p.val.1 p.val.2).trans (le_iSup (fun k : S => ℒ k) ⟨p.val.1, p.property⟩)
  exact (TauCeti.DirectSum.mem_iSup_iff_decompose_eq_zero ℒ S).mp (hle hx) n
    (fun hn' => hn' hn)

variable {W} in
/-- A bracket in the joint subalgebra has zero tangent homogeneous components. -/
theorem decompose_lie_eq_zero_of_direction_mem {x y : L}
    (hx : x ∈ H.jointSubalgebra W) (hy : y ∈ H.jointSubalgebra W) {n : Γ}
    (hn : ρ n ∈ W) : (_root_.DirectSum.decompose ℒ ⁅x, y⁆ n : L) = 0 :=
  H.decompose_eq_zero_of_mem_transverseJointSubmodule (H.lie_mem_transverseJointSubmodule hx hy) hn

end Decomposition

end TauCeti.DirectedWallSpaces
