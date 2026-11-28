/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Graph
public import TauCeti.Topology.Grassmannian.Realification.Basic
public import TauCeti.Topology.Grassmannian.Map

/-!
# Coordinate graph charts under Grassmannian realification

The realification of a coordinate graph is the graph obtained by replacing each complex
matrix entry by its real two-by-two block in the interleaved coordinates.
-/

public section

namespace TauCeti
namespace finiteGrassmannian

/-- After reindexing the ambient coordinates by distributivity, realification sends the graph
of `A` to the graph whose rows are the real and imaginary parts of each row of `A` and of that
row multiplied by `I`, interleaved in adjacent pairs. -/
theorem realify_graph {r q : ℕ} (A : Matrix (Fin r) (Fin q) ℂ) :
    let e := LinearEquiv.funCongrLeft ℝ ℝ
      (finCongr (Nat.mul_add 2 r q).symm)
    map e.toLinearMap e.injective (graph A).realify =
      graph (Matrix.of (complexPiEquivRealPi q ∘ complexToRealFamily (fun i j ↦ A i j))) := by
  dsimp only
  have hcoord {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (l : Fin 2) :
      complexPiEquivRealPi n z (complexRealIndexEquiv n (j, l)) = ![(z j).re, (z j).im] l := by
    have h₀ : complexRealIndexEquiv n (j, 0) = ⟨2 * j.val, by omega⟩ := Fin.ext (by simp)
    have h₁ : complexRealIndexEquiv n (j, 1) = ⟨2 * j.val + 1, by omega⟩ := Fin.ext (by simp)
    have hl : l = 0 ∨ l = 1 := by omega
    rcases hl with rfl | rfl
    · rw [h₀]
      exact complexPiEquivRealPi_apply_two_mul z j
    · rw [h₁]
      exact complexPiEquivRealPi_apply_two_mul_add_one z j
  rw [← frameSpan_graphFrame A, ← frameSpan_realify, ← frameSpan_map, ← frameSpan_graphFrame]
  congr 1
  apply Subtype.ext
  funext i j
  obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
  simp only [finiteFullRankFrame.coe_map, Function.comp_apply, finiteFullRankFrame.coe_realify,
    complexToRealFamily_complexRealIndexEquiv, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]
  -- The realified frame has an identity block followed by the realified rows of A.
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · obtain ⟨⟨j, l⟩, rfl⟩ := (complexRealIndexEquiv r).surjective j
    rw [graphFrame_castAdd]
    have hj : finCongr (Nat.mul_add 2 r q).symm
        (Fin.castAdd (2 * q) (complexRealIndexEquiv r (j, l))) =
          complexRealIndexEquiv (r + q) (Fin.castAdd q j, l) := Fin.ext (by simp)
    rw [hj, hcoord]
    by_cases h : j = i
    · subst j
      fin_cases k <;> fin_cases l <;>
        simp [Complex.coe_basisOneI, Pi.smul_apply, smul_eq_mul]
    · fin_cases l <;>
        simp [Pi.smul_apply, h]
  · obtain ⟨⟨j, l⟩, rfl⟩ := (complexRealIndexEquiv q).surjective j
    rw [graphFrame_natAdd, Matrix.of_apply, Function.comp_apply,
      complexToRealFamily_complexRealIndexEquiv]
    have hj : finCongr (Nat.mul_add 2 r q).symm
        (Fin.natAdd (2 * r) (complexRealIndexEquiv q (j, l))) =
          complexRealIndexEquiv (r + q) (Fin.natAdd r j, l) := Fin.ext (by simp; omega)
    simp only [hj, hcoord, Pi.smul_apply, graphFrame_natAdd]

end finiteGrassmannian

end TauCeti
