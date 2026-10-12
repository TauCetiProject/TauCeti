/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Local orientations from chart homology

A local orientation at a point of an `n`-dimensional manifold is a generator of the integral
local homology group in degree `n`. This file defines that generator condition and proves that
every point in a finite-dimensional charted space has local orientations. Integral coefficients
are represented by the universe-lifted module `ULift ℤ`. The construction is the inverse image of
`1` under the chart computation of local homology.

The local orientation is the generator of `Hₙ(M, M ∖ {x}; ℤ)` described in Hatcher's
*Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

/-- An element of the integral local homology group is a local orientation when it generates the
whole group as a `ℤ`-module. -/
def IsLocalOrientation {M : Type w} [TopologicalSpace M] (x : M) (d : ℕ)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) : Prop :=
  ∀ y, ∃ c : ℤ, c • z = y

/-- An element of local homology is a local orientation exactly when every class is an integral
multiple of it. -/
theorem isLocalOrientation_iff {M : Type w} [TopologicalSpace M] (x : M) (d : ℕ)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ ∀ y, ∃ c : ℤ, c • z = y := Iff.rfl

/-- The integral local homology group at `x` in degree `d`, with its local orientations. -/
abbrev LocalOrientation (M : Type w) [TopologicalSpace M] (x : M) (d : ℕ) :=
  {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d //
    IsLocalOrientation x d z}

/-- The inverse image of `1` under an isomorphism from integral local homology to `ℤ` is a local
orientation. -/
theorem isLocalOrientation_inv_one {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ)) :
    IsLocalOrientation x d (e.inv 1) := by
  intro y
  refine ⟨(e.hom y).down, ?_⟩
  have h : (e.hom y).down • (1 : ULift.{w} ℤ) = e.hom y := by
    apply ULift.ext
    simp
  calc
    (e.hom y).down • e.inv 1 = e.inv ((e.hom y).down • (1 : ULift.{w} ℤ)) :=
      (e.inv.hom.toAddMonoidHom.map_zsmul ((e.hom y).down) (1 : ULift.{w} ℤ)).symm
    _ = e.inv (e.hom y) := congrArg e.inv h
    _ = y := e.hom_inv_id_apply y

/-- The local orientation at `x` selected by a chart and its chart-induced local homology
isomorphism. -/
def localOrientationOfChart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (hn : finrank ℝ E = n + 1) : LocalOrientation M x (n + 1) :=
  ⟨(singularHomologyComplSingletonIsoOfFinrankEq (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx hn).inv 1,
    isLocalOrientation_inv_one _⟩

/-- A point in a positive-dimensional finite-dimensional charted space has a local orientation.
The chart computation identifies its local homology group with `ℤ`, and the inverse image of `1`
is a generator. -/
theorem exists_localOrientation_of_chart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]
    (x : M) {n : ℕ} (hn : finrank ℝ E = n + 1) :
    Nonempty (LocalOrientation M x (n + 1)) :=
  ⟨localOrientationOfChart (chartAt E x) (mem_chart_source E x) hn⟩

/-- A point with a zero-dimensional chart also has a local orientation, represented by the class
of the point in degree-zero local homology. -/
def localOrientationOfZeroDimChart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)
    (hn : finrank ℝ E = 0) : LocalOrientation M x 0 :=
  ⟨(singularHomologyComplSingletonIsoOfFinrankEqZero (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx hn).inv 1,
    isLocalOrientation_inv_one _⟩

/-- Every point of a zero-dimensional finite-dimensional charted space has a local orientation. -/
theorem exists_localOrientation_of_zero_dim_chart {M E : Type w} [TopologicalSpace M]
    [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] (x : M) (hn : finrank ℝ E = 0) : Nonempty (LocalOrientation M x 0) :=
  ⟨localOrientationOfZeroDimChart (chartAt E x) (mem_chart_source E x) hn⟩

end TauCeti
