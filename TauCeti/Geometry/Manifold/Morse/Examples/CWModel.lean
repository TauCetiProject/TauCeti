/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell

/-!
# CW models of proper Morse functions: examples

A Morse function `f` on a boundaryless manifold `M`, proper and bounded below, makes `M` homotopy
equivalent to a CW complex with one `λ`-cell for each critical point of `f` of index `λ`
(`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv`). This file computes the cells of this model in
four basic cases, which test the labelling of the cells by critical points.

* The height on the unit sphere `Sⁿ`, `n ≠ 0`, has a minimum of index `0` and a maximum of index
  `n` and no other critical point, so `Sⁿ` is homotopy equivalent to a CW complex with one `0`-cell,
  one `n`-cell and no other cells (`TauCeti.exists_cwComplex_homotopyEquiv_sphere`), the cells of
  the standard CW structure `TauCeti.sphereCWComplex`.
* The function `x ↦ x²` on `ℝ` has a single critical point, a minimum, so `ℝ` is homotopy equivalent
  to a CW complex with exactly one cell, a `0`-cell; this model is contractible
  (`TauCeti.exists_cwComplex_homotopyEquiv_real`).
* The empty manifold has no critical points, so its model is empty and has no cells in any
  dimension, not a distinguished `0`-cell (`TauCeti.exists_cwComplex_homotopyEquiv_empty`).
* On a manifold modelled on a zero-dimensional space every function is Morse
  (`TauCeti.isMorse_of_subsingleton`) and every point is critical of index `0`. For `ℕ`, with the
  discrete topology, the proper function `n ↦ n` therefore gives a model whose `0`-cells
  correspond to the natural numbers and which has no other cells
  (`TauCeti.exists_cwComplex_homotopyEquiv_nat`): the CW model of a proper Morse function need not
  be finite.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
-/

public section

noncomputable section

open Set Metric Module Topology Topology.RelCWComplex
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

section Discrete

attribute [local instance] ChartedSpace.ofDiscreteTopology

/-- **The CW model of the empty manifold** is empty, with no cells in any dimension: the empty
manifold has no critical points, and the cells of the CW model of the (Morse) function
`isEmptyElim` are labelled by its critical points. -/
theorem exists_cwComplex_homotopyEquiv_empty :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (Empty ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, Fin 0 → ℝ) (isEmptyElim : Empty → ℝ) |
            manifoldMorseIndex 𝓘(ℝ, Fin 0 → ℝ) (isEmptyElim : Empty → ℝ) x = m})) ∧
        IsEmpty X ∧ ∀ m, IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ :=
    (isMorse_of_subsingleton (I := 𝓘(ℝ, Fin 0 → ℝ)) (f := (isEmptyElim : Empty → ℝ))
      ).exists_cwComplex_homotopyEquiv continuous_of_discreteTopology.isProperMap (by simp)
  have : IsEmpty X := ⟨fun x ↦ isEmptyElim (h.invFun x)⟩
  exact ⟨X, _, ‹_›, ‹_›, ⟨h⟩, hcell, ‹_›, fun m ↦ (hcell m).some.isEmpty⟩

/-- **The CW model of a countable discrete manifold.** The natural numbers, a zero-dimensional
manifold, are homotopy equivalent to a CW complex whose cells are labelled by the critical points of
the proper Morse function `n ↦ n`; all of these are of index `0`, so the model has countably
infinitely many `0`-cells and no other cells. In particular the CW model of a proper Morse function
need not be finite. -/
theorem exists_cwComplex_homotopyEquiv_nat :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℕ ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) |
            manifoldMorseIndex 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) x = m})) ∧
        Nonempty (cell (univ : Set X) 0 ≃ ℕ) ∧ ∀ m, m ≠ 0 → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ ℕ := .of_discreteTopology _
  obtain ⟨X, _, _, _, hh, hcell⟩ :=
    (isMorse_of_subsingleton (I := 𝓘(ℝ, Fin 0 → ℝ)) (f := ((↑) : ℕ → ℝ))
      ).exists_cwComplex_homotopyEquiv Nat.isClosedEmbedding_coe_real.isProperMap
      ⟨0, forall_mem_range.2 Nat.cast_nonneg⟩
  -- Every point is critical, of index `0`.
  refine ⟨X, _, ‹_›, ‹_›, hh, hcell, ⟨(hcell 0).some.trans (Equiv.subtypeUnivEquiv fun x ↦
    ⟨by simp, manifoldMorseIndex_eq_zero_of_subsingleton⟩)⟩, fun m hm ↦ ?_⟩
  have hE : {x ∈ criticalPoints 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) |
      manifoldMorseIndex 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) x = m} = ∅ := by
    simp [Ne.symm hm]
  exact ((hcell m).some.trans (Set.equivOfEq hE)).isEmpty

end Discrete

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The CW model of the sphere.** For `n ≠ 0`, the unit sphere `Sⁿ` is homotopy equivalent to a
CW complex whose cells are labelled by the critical points of the height function towards a pole
`v`. These are the south pole, of index `0`, and the north pole, of index `n`, so the model has one
`0`-cell, one `n`-cell and no other cells, the cells of the standard CW structure
`TauCeti.sphereCWComplex` on `Sⁿ`. -/
theorem exists_cwComplex_homotopyEquiv_sphere (hn : n ≠ 0) (v : sphere (0 : E) 1) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (sphere (0 : E) 1 ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints (𝓡 n) (sphereHeight v) |
            manifoldMorseIndex (𝓡 n) (sphereHeight v) x = m})) ∧
        Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧ Nonempty (cell (univ : Set X) n ≃ Unit) ∧
          ∀ m, m ≠ 0 → m ≠ n → IsEmpty (cell (univ : Set X) m) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨X, _, _, _, hh, hcell⟩ := (isMorse_sphereHeight (n := n) v).exists_cwComplex_homotopyEquiv
    (contMDiff_sphereHeight (n := n) (m := 0) v).continuous.isProperMap
    ⟨-1, forall_mem_range.2 (neg_one_le_sphereHeight v)⟩
  -- The critical points of index `m` are the north pole if `m = n`, the south pole if `m = 0`,
  -- and none otherwise.
  have hS := sep_criticalPoints_sphereHeight_manifoldMorseIndex_eq (n := n) v
  refine ⟨X, _, ‹_›, ‹_›, hh, hcell,
    ⟨(hcell 0).some.trans ((Set.equivOfEq ((hS 0).trans (by simp [Ne.symm hn]))).trans
      (Equiv.Set.singleton (-v)))⟩,
    ⟨(hcell n).some.trans ((Set.equivOfEq ((hS n).trans (by simp [hn]))).trans
      (Equiv.Set.singleton v))⟩,
    fun m hm₀ hmn ↦ ((hcell m).some.trans
      (Set.equivOfEq ((hS m).trans (by simp [hm₀, hmn]) : _ = ∅))).isEmpty⟩

end Sphere

/-- **The CW model of the real line.** The real line is homotopy equivalent to a CW complex whose
cells are labelled by the critical points of `x ↦ x²`. Its only critical point is its minimum, so
the model has exactly one cell, a `0`-cell; in particular this model is contractible. -/
theorem exists_cwComplex_homotopyEquiv_real :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℝ ≃ₕ X) ∧
        (∀ m, Nonempty (cell (univ : Set X) m ≃
          ↥{x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) |
            manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) x = m})) ∧
        ContractibleSpace X ∧ Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧
          ∀ m, m ≠ 0 → IsEmpty (cell (univ : Set X) m) := by
  have hp : IsProperMap fun x : ℝ ↦ x ^ 2 := by
    refine isProperMap_iff_tendsto_cocompact.2 ⟨continuous_pow 2, ?_⟩
    have h := (Filter.tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))
    simp only [Function.comp_def, Real.norm_eq_abs, sq_abs] at h
    exact h.mono_right atTop_le_cocompact
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ :=
    isMorse_sq_real.exists_cwComplex_homotopyEquiv hp ⟨0, forall_mem_range.2 sq_nonneg⟩
  -- The only critical point is the minimum `0`, of index `0`.
  have hidx : manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0 = 0 :=
    manifoldMorseIndex_eq_zero_of_isLocalMin ((isMorse_sq_real.contMDiff 0).of_le (by norm_cast))
      (Filter.Eventually.of_forall fun y ↦ by simpa using sq_nonneg y)
  have hS (m : ℕ) : {x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) |
      manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) x = m} = if m = 0 then {0} else ∅ := by
    ext x
    rw [criticalPoints_sq_real, mem_sep_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      simp [hidx]
    · split_ifs with hm <;> simp_all
  have : ContractibleSpace X := h.symm.contractibleSpace
  refine ⟨X, _, ‹_›, ‹_›, ⟨h⟩, hcell, ‹_›,
    ⟨(hcell 0).some.trans ((Set.equivOfEq (hS 0)).trans (Equiv.Set.singleton 0))⟩,
    fun m hm ↦ ((hcell m).some.trans (Set.equivOfEq ((hS m).trans (by simp [hm]) : _ = ∅))).isEmpty⟩

end TauCeti
