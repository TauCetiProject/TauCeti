/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Defs
import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading
import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched

/-!
# Products and gradings in small strands algebras

Two products in the strands algebras `A(4, 2)` and `A(3, 1)` of Lipshitz, Ozsváth and Thurston
over `𝔽₂`, one grading, and the noncommutativity of the grading group, with points `1, …, n`
written `0, …, n - 1`.

* In `A(4, 2)` the diagrams `φ = (1 ↦ 3, 2 ↦ 2)` and `ψ = (2 ↦ 4, 3 ↦ 3)` each have one
  crossing, and their composite `(1 ↦ 3, 2 ↦ 4)` has none. Since `0 ≠ 1 + 1` the concatenation
  has a double crossing and the product `φ ψ` is zero, although the target of `φ` is the source of
  `ψ`.
* In `A(3, 1)` the product of `(1 ↦ 2)` and `(2 ↦ 3)` is `(1 ↦ 3)`: no diagram has a crossing.
* In `A(3, 1)` the strand `(1 ↦ 2)` has grading `(-1/2, e₂ - e₁)`: it has no crossing, and the
  multiplicity of its class at its starting point is `1/2`. This is the grading of the chord `ρ₁`
  of the torus algebra.
* The gradings of `(1 ↦ 2)` and `(2 ↦ 3)` do not commute: `gr(1 ↦ 2) gr(2 ↦ 3)` is
  `λ gr(2 ↦ 3) gr(1 ↦ 2)`. The classes are the segments `[1, 2]` and `[2, 3]`, and the correction
  terms `L([1, 2], [2, 3]) = 1/2` and `L([2, 3], [1, 2]) = -1/2` differ by one.

Two products in the algebra `A(T²)` of the genus-one pointed matched circle, whose points
`1, 2, 3, 4` are matched as `{1, 3}` and `{2, 4}`, encoded by the parity of `0, 1, 2, 3`. Its Reeb
chords `ρ₁ = (1 ↦ 2)`, `ρ₂ = (2 ↦ 3)` and `ρ₁₂ = (1 ↦ 3)` give the generators `a(ρ)` without
horizontal strands.

* `ρ₁ ρ₂ = ρ₁₂`.
* `ρ₂ ρ₁ = 0`, although the end point `3` of `ρ₂` and the starting point `1` of `ρ₁` are matched:
  the product of generators needs the actual points to agree, not just their pairs.
-/

open TauCeti StrandsAlgebra StrandDiagram StrandGradingGroup

example :
    let φ : StrandDiagram (Fin 4) :=
      ⟨(PEquiv.ofSet ({0, 1} : Finset (Fin 4))).trans (Equiv.swap 0 2).toPEquiv, by decide⟩
    let ψ : StrandDiagram (Fin 4) :=
      ⟨(PEquiv.ofSet ({1, 2} : Finset (Fin 4))).trans (Equiv.swap 1 3).toPEquiv, by decide⟩
    φ.inversionCount = 1 ∧ ψ.inversionCount = 1 ∧ (φ.trans ψ).inversionCount = 0 ∧
      φ.target = ψ.source ∧ (of φ * of ψ : StrandsAlgebra (ZMod 2) (Fin 4)) = 0 := by
  intro φ ψ
  have hφ : φ.inversions = {(0, 1)} := by
    ext p
    rw [mem_inversions, Finset.mem_singleton]
    revert p
    decide
  have hψ : ψ.inversions = {(1, 2)} := by
    ext p
    rw [mem_inversions, Finset.mem_singleton]
    revert p
    decide
  have hφψ : (φ.trans ψ).inversions = ∅ := by
    ext p
    simp only [mem_inversions, mem_trans, Finset.notMem_empty, iff_false]
    revert p
    decide
  have hT : φ.target = ψ.source := by
    ext j
    simp only [mem_target, mem_source]
    revert j
    decide
  have h₁ : φ.inversionCount = 1 := by rw [inversionCount_def, hφ, Finset.card_singleton]
  have h₂ : ψ.inversionCount = 1 := by rw [inversionCount_def, hψ, Finset.card_singleton]
  have h₃ : (φ.trans ψ).inversionCount = 0 := by rw [inversionCount_def, hφψ, Finset.card_empty]
  refine ⟨h₁, h₂, h₃, hT, of_mul_of_of_not_composable fun h ↦ ?_⟩
  have := h.inversionCount_trans
  omega

example :
    (of (single (0 : Fin 3) 1 (by decide)) * of (single 1 2 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 3)) = of (single 0 2 (by decide)) := by
  rw [of_mul_of_of_composable (composable_single_single _ _), single_trans_single]

example :
    let φ : StrandDiagram (Fin 3) :=
      ⟨PEquiv.single 0 1, fun _ _ hk ↦ by
        obtain ⟨rfl, rfl⟩ := (PEquiv.mem_single_iff _ _ _ _).1 hk
        decide⟩
    φ.grading = mk (-1 / 2) ![-1, 1, 0] := by
  intro φ
  have hinv : φ.inversionCount = 0 := by
    rw [inversionCount_def, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    simp only [mem_inversions]
    decide
  have hS : φ.source = {0} := by
    ext j
    simp only [mem_source, Finset.mem_singleton]
    revert j
    decide
  have hb : φ.boundary = ![-1, 1, 0] := by
    funext x
    simp only [boundary_apply, mem_target, mem_source]
    revert x
    decide
  have hlt : ({y | y < 0} : Finset (Fin 3)) = ∅ := by decide
  ext
  · rw [grading_maslov, hinv, hS, Finset.sum_singleton, pointMultiplicity_apply, hb, hlt]
    norm_num
  · rw [grading_boundary, hb, mk_boundary]

example :
    let M : Fin 4 → ℕ := fun i ↦ i % 2
    (horizontalCompletion M (single 0 1 (by decide)) ∅ *
        horizontalCompletion M (single 1 2 (by decide)) ∅ :
          StrandsAlgebra (ZMod 2) (Fin 4)) = horizontalCompletion M (single 0 2 (by decide)) ∅ ∧
    (horizontalCompletion M (single 1 2 (by decide)) ∅ *
        horizontalCompletion M (single 0 1 (by decide)) ∅ :
          StrandsAlgebra (ZMod 2) (Fin 4)) = 0 := by
  intro M
  -- A Reeb chord, with no horizontal strands added, indexes a generator.
  have hgen (i j : Fin 4) (h : i < j) : IsMatchedGenerator M (single i j h.le) ∅ :=
    ⟨fun k hk ↦ h.ne ((mem_single.1 hk).1.symm.trans (mem_single.1 hk).2), by simp, by simp,
      Finset.disjoint_empty_right _, Finset.disjoint_empty_right _⟩
  refine ⟨?_, ?_⟩
  · rw [horizontalCompletion_mul_horizontalCompletion (hgen 0 1 (by decide)) (hgen 1 2 (by decide))]
    simp [composable_single_single]
  · rw [horizontalCompletion_mul_horizontalCompletion (hgen 1 2 (by decide)) (hgen 0 1 (by decide))]
    refine ite_eq_right_iff.2 fun hc ↦ absurd hc.2.target_eq ?_
    simp

example :
    (single (0 : Fin 3) 1 (by decide)).grading * (single 1 2 (by decide)).grading =
      lambda * ((single (1 : Fin 3) 2 (by decide)).grading *
        (single 0 1 (by decide)).grading) := by
  have hb₁ : (single (0 : Fin 3) 1 (by decide)).boundary = ![-1, 1, 0] := by
    funext x
    simp only [boundary_apply, target_single, source_single, Finset.mem_singleton]
    revert x
    decide
  have hb₂ : (single (1 : Fin 3) 2 (by decide)).boundary = ![0, -1, 1] := by
    funext x
    simp only [boundary_apply, target_single, source_single, Finset.mem_singleton]
    revert x
    decide
  -- The correction terms of the two products differ by one.
  have hL₁ : linking (![-1, 1, 0] : Fin 3 → ℤ) ![0, -1, 1] = 1 / 2 := by
    norm_num [linking_apply, pointMultiplicity_apply, Finset.sum_filter, Fin.sum_univ_three]
  have hL₂ : linking (![0, -1, 1] : Fin 3 → ℤ) ![-1, 1, 0] = -1 / 2 := by
    norm_num [linking_apply, pointMultiplicity_apply, Finset.sum_filter, Fin.sum_univ_three]
  refine StrandGradingGroup.ext ?_ ?_
  · rw [mul_maslov, mul_maslov, mul_maslov, lambda_maslov, lambda_boundary, map_zero,
      AddMonoidHom.zero_apply, grading_boundary, grading_boundary, hb₁, hb₂, hL₁, hL₂]
    ring
  · rw [mul_boundary, mul_boundary, mul_boundary, lambda_boundary, zero_add, add_comm]
