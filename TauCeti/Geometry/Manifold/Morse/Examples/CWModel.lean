/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
public import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

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
manifold has no critical points, and the cells of the model are labelled by critical points. -/
theorem exists_cwComplex_homotopyEquiv_empty :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (Empty ≃ₕ X) ∧ IsEmpty X ∧ ∀ m, IsEmpty (cell (univ : Set X) m) := by
  obtain ⟨X, _, _, _, ⟨h⟩, hcell⟩ :=
    (isMorse_of_subsingleton (I := 𝓘(ℝ, Fin 0 → ℝ)) (f := (isEmptyElim : Empty → ℝ))
      ).exists_cwComplex_homotopyEquiv continuous_of_discreteTopology.isProperMap (by simp)
  have : IsEmpty X := ⟨fun x ↦ isEmptyElim (h.invFun x)⟩
  exact ⟨X, _, ‹_›, ‹_›, ⟨h⟩, ‹_›, fun m ↦ (hcell m).some.isEmpty⟩

/-- **The CW model of a countable discrete manifold.** The natural numbers, a zero-dimensional
manifold, are homotopy equivalent to a CW complex with countably infinitely many `0`-cells and no
other cells: this is the CW model of the proper Morse function `n ↦ n`, all of whose points are
critical of index `0`. In particular the CW model of a proper Morse function need not be
finite. -/
theorem exists_cwComplex_homotopyEquiv_nat :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℕ ≃ₕ X) ∧ Nonempty (cell (univ : Set X) 0 ≃ ℕ) ∧
        ∀ m, m ≠ 0 → IsEmpty (cell (univ : Set X) m) := by
  have : IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ ℕ := .of_discreteTopology _
  obtain ⟨X, _, _, _, hh, hcell⟩ :=
    (isMorse_of_subsingleton (I := 𝓘(ℝ, Fin 0 → ℝ)) (f := ((↑) : ℕ → ℝ))
      ).exists_cwComplex_homotopyEquiv Nat.isClosedEmbedding_coe_real.isProperMap
      ⟨0, forall_mem_range.2 Nat.cast_nonneg⟩
  -- Every point is critical, of index `0`.
  refine ⟨X, _, ‹_›, ‹_›, hh, ⟨(hcell 0).some.trans (Equiv.subtypeUnivEquiv fun x ↦
    ⟨by simp, manifoldMorseIndex_eq_zero_of_subsingleton⟩)⟩, fun m hm ↦ ?_⟩
  have : IsEmpty {x ∈ criticalPoints 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) |
      manifoldMorseIndex 𝓘(ℝ, Fin 0 → ℝ) ((↑) : ℕ → ℝ) x = m} :=
    isEmpty_coe_sort.2 (eq_empty_of_forall_notMem fun _ hx ↦
      hm (hx.2.symm.trans manifoldMorseIndex_eq_zero_of_subsingleton))
  exact (hcell m).some.isEmpty

end Discrete

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The CW model of the sphere.** For `n ≠ 0`, the unit sphere `Sⁿ` is homotopy equivalent to a
CW complex with one `0`-cell, one `n`-cell and no other cells. This is the CW model of the height
function, whose only critical points are the south pole, of index `0`, and the north pole, of index
`n`; its cells are those of the standard CW structure `TauCeti.sphereCWComplex` on `Sⁿ`. -/
theorem exists_cwComplex_homotopyEquiv_sphere (hn : n ≠ 0) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (sphere (0 : E) 1 ≃ₕ X) ∧ Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧
        Nonempty (cell (univ : Set X) n ≃ Unit) ∧
          ∀ m, m ≠ 0 → m ≠ n → IsEmpty (cell (univ : Set X) m) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨X, _, _, _, hh, hcell⟩ := (isMorse_sphereHeight (n := n) v).exists_cwComplex_homotopyEquiv
    (contMDiff_sphereHeight (n := n) (m := 0) v).continuous.isProperMap
    ⟨-1, forall_mem_range.2 (neg_one_le_sphereHeight v)⟩
  -- The critical points of index `m` are the north pole if `m = n`, the south pole if `m = 0`,
  -- and none otherwise.
  have hN : {x ∈ criticalPoints (𝓡 n) (sphereHeight v) |
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x = n} = {v} := by
    ext x
    simp only [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · rw [manifoldMorseIndex_sphereHeight_neg] at h
        exact absurd h.symm hn
    · rintro rfl
      exact ⟨Or.inl rfl, manifoldMorseIndex_sphereHeight_self x⟩
  have hS : {x ∈ criticalPoints (𝓡 n) (sphereHeight v) |
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x = 0} = {-v} := by
    ext x
    simp only [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rw [manifoldMorseIndex_sphereHeight_self] at h
        exact absurd h hn
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, manifoldMorseIndex_sphereHeight_neg v⟩
  have hpt (m : ℕ) (p : sphere (0 : E) 1)
      (hp : {x ∈ criticalPoints (𝓡 n) (sphereHeight v) |
        manifoldMorseIndex (𝓡 n) (sphereHeight v) x = m} = {p}) :
      Nonempty (cell (univ : Set X) m ≃ Unit) :=
    ⟨(hcell m).some.trans (hp ▸ (Equiv.Set.singleton p : ({p} : Set (sphere (0 : E) 1)) ≃ Unit))⟩
  refine ⟨X, _, ‹_›, ‹_›, hh, hpt 0 (-v) hS, hpt n v hN, fun m hm₀ hmn ↦ ?_⟩
  have hE : {x ∈ criticalPoints (𝓡 n) (sphereHeight v) |
      manifoldMorseIndex (𝓡 n) (sphereHeight v) x = m} = ∅ := by
    refine eq_empty_of_forall_notMem fun x ↦ ?_
    rw [criticalPoints_sphereHeight, mem_sep_iff, mem_insert_iff, mem_singleton_iff]
    rintro ⟨rfl | rfl, h⟩
    · rw [manifoldMorseIndex_sphereHeight_self] at h
      exact hmn h.symm
    · rw [manifoldMorseIndex_sphereHeight_neg] at h
      exact hm₀ h.symm
  have := isEmpty_coe_sort.2 hE
  exact (hcell m).some.isEmpty

end Sphere

/-- **The CW model of the real line.** The function `x ↦ x²` has a single critical point, its
minimum, so `ℝ` is homotopy equivalent to a CW complex with exactly one cell, a `0`-cell; in
particular this model is contractible. -/
theorem exists_cwComplex_homotopyEquiv_real :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CWComplex (univ : Set X)),
      Nonempty (ℝ ≃ₕ X) ∧ ContractibleSpace X ∧ Nonempty (cell (univ : Set X) 0 ≃ Unit) ∧
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
  have h0 : {x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) |
      manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) x = 0} = {0} := by
    rw [criticalPoints_sq_real, sep_eq_self_iff_mem_true.2]
    rintro x rfl
    exact hidx
  have : ContractibleSpace X := ⟨⟨h.symm.trans (ContractibleSpace.hequiv_unit ℝ).some⟩⟩
  refine ⟨X, _, ‹_›, ‹_›, ⟨h⟩, ‹_›,
    ⟨(hcell 0).some.trans (h0 ▸ (Equiv.Set.singleton 0 : ({0} : Set ℝ) ≃ Unit))⟩,
    fun m hm ↦ ?_⟩
  have : IsEmpty {x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) |
      manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) x = m} := by
    refine isEmpty_coe_sort.2 (eq_empty_of_forall_notMem fun x ⟨hx, hxm⟩ ↦ hm ?_)
    rw [criticalPoints_sq_real, mem_singleton_iff] at hx
    rw [← hxm, hx, hidx]
  exact (hcell m).some.isEmpty

end TauCeti
