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
`1` under the chart computation of local homology. The two generators of a fibre isomorphic to
`ℤ` differ by sign; reversal and preservation by local homology isomorphisms are also proved.

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

/-- Reversing a local orientation gives a local orientation. -/
theorem IsLocalOrientation.neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : IsLocalOrientation x d (-z) := by
  intro y
  obtain ⟨c, rfl⟩ := hz y
  exact ⟨-c, by simp⟩

/-- Reversal of local orientations is involutive. -/
instance {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ} :
    InvolutiveNeg (LocalOrientation M x d) where
  neg z := ⟨-z.val, z.property.neg⟩
  neg_neg z := Subtype.ext (neg_neg z.val)

@[simp]
lemma LocalOrientation.coe_neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (z : LocalOrientation M x d) : (↑(-z) : localHomology (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) = -z.val :=
  (rfl)

/-- An isomorphism of integral local homology groups preserves the generator condition. -/
theorem IsLocalOrientation.map {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    {x : M} {y : N} {d : ℕ}
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z)
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({y} : Set N) d) :
    IsLocalOrientation y d (e.hom z) := by
  intro a
  obtain ⟨c, hc⟩ := hz (e.inv a)
  refine ⟨c, ?_⟩
  calc
    c • e.hom z = e.hom (c • z) :=
      (e.hom.hom.toAddMonoidHom.map_zsmul c z).symm
    _ = e.hom (e.inv a) := congrArg e.hom hc
    _ = a := e.inv_hom_id_apply a

/-- If integral local homology is isomorphic to `ℤ`, its generators are precisely the inverse
images of `1` and `-1`. In particular a top-degree local homology fibre has two orientations. -/
theorem isLocalOrientation_iff_eq_or_eq_neg_inv_one {M : Type w} [TopologicalSpace M]
    {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ z = e.inv 1 ∨ z = -e.inv 1 := by
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := hz (e.inv 1)
    have he : c * (e.hom z).down = 1 := by
      have h := congrArg (fun a ↦ (e.hom a).down) hc
      simpa using h
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp he with ⟨_, h⟩ | ⟨_, h⟩
    · left
      calc
        z = e.inv (e.hom z) := (e.hom_inv_id_apply z).symm
        _ = e.inv 1 := congrArg e.inv (ULift.ext h)
    · right
      calc
        z = e.inv (e.hom z) := (e.hom_inv_id_apply z).symm
        _ = e.inv (-1) := congrArg e.inv (ULift.ext h)
        _ = -e.inv 1 := e.inv.hom.map_neg 1
  · rintro (rfl | rfl)
    · exact isLocalOrientation_inv_one e
    · exact (isLocalOrientation_inv_one e).neg

/-- A local homology fibre isomorphic to `ℤ` has exactly two local orientations. -/
theorem nat_card_localOrientation {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ)) :
    Nat.card (LocalOrientation M x d) = 2 := by
  let z : LocalOrientation M x d := ⟨e.inv 1, isLocalOrientation_inv_one e⟩
  refine Nat.card_eq_two_iff.mpr ⟨z, -z, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun a : LocalOrientation M x d ↦ (e.hom a.val).down) h
    simp [z] at h'
  · apply Set.eq_univ_of_forall
    intro a
    rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e a.val).mp a.property with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext h))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (Subtype.ext h))

/-- In a local homology fibre isomorphic to `ℤ`, two local orientations agree up to sign. -/
theorem IsLocalOrientation.eq_or_eq_neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z z' : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) (hz' : IsLocalOrientation x d z') : z' = z ∨ z' = -z := by
  rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z).1 hz with rfl | rfl <;>
    rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z').1 hz' with rfl | rfl <;> simp

/-- In a local homology fibre isomorphic to `ℤ`, a local orientation has infinite order. -/
theorem IsLocalOrientation.zsmul_eq_zero_iff {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) {c : ℤ} : c • z = 0 ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h' := congrArg (fun a ↦ (e.hom a).down) h
  rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z).1 hz with rfl | rfl <;> simpa using h'

/-- In a local homology fibre isomorphic to `ℤ`, a local orientation differs from its reversal. -/
theorem IsLocalOrientation.neg_ne {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : -z ≠ z := by
  intro h
  have h2 : (2 : ℤ) • z = 0 := by
    rw [two_zsmul]
    nth_rw 1 [← h]
    exact neg_add_cancel z
  exact two_ne_zero ((hz.zsmul_eq_zero_iff e).1 h2)

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
