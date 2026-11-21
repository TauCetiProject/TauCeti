/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Analysis.Complex.Runge.Rational
import TauCeti.Analysis.Normed.Module.Basic

/-!
# The finite-rank Runge approximation operator

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

Via rational Runge approximation (`TauCeti.Analysis.Complex.Runge.Rational`), this file establishes
the vector-valued finite-rank Runge operator (`TauCeti.IsFilledIn.exists_norm_sub_sum_smul_le`)
without requiring `Ω` to be open, and derives the domain-relative operator
(`TauCeti.exists_finite_rank_runge_operator`) for any Runge compact pair `(Ω, K)` and open
neighbourhood `U ⊇ K` on a compact neighbourhood `L` of `K` inside `U ∩ Ω`.

## Main declarations and results

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.
* `TauCeti.IsFilledIn.exists_norm_sub_sum_smul_le`: vector-valued finite-rank Runge operator for
  compact sets filled in an arbitrary `Ω ⊆ ℂ`.
* `TauCeti.exists_finite_rank_runge_operator`: existence of the compact neighbourhood `L ⊆ U ∩ Ω`
  and `f`-independent finite-rank evaluation approximants with operator norm bound `ε * B`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Set

universe u

namespace TauCeti

/-- A **Runge compact pair**: an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω` that is filled in
`Ω` (no connected component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

/-- Unfolding `TauCeti.IsRungeCompactPair`. -/
theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  (Iff.rfl)

/-- The ambient set of a Runge compact pair is open. -/
protected theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsOpen Ω :=
  h.1

/-- The compact member of a Runge compact pair is compact. -/
protected theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsCompact K :=
  h.2.1

/-- The compact member of a Runge compact pair is contained in the ambient set. -/
protected theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    K ⊆ Ω :=
  h.2.2.1

/-- The compact member of a Runge compact pair is filled in the ambient set. -/
protected theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

/-- The empty set forms a Runge compact pair with `Ω` if and only if `Ω` is open. -/
@[simp]
theorem isRungeCompactPair_empty_right {Ω : Set ℂ} :
    IsRungeCompactPair Ω ∅ ↔ IsOpen Ω := by
  refine ⟨fun h => h.isOpen, fun hΩ => ⟨hΩ, isCompact_empty, empty_subset Ω, ?_⟩⟩
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω),
    filledHull_eq_self (by simpa using isPreconnected_univ)
      (by simpa using NormedSpace.unbounded_univ ℂ ℂ)]
  simp

/-- A set `K` forms a Runge compact pair with `∅` if and only if `K = ∅`. -/
@[simp]
theorem isRungeCompactPair_empty_left {K : Set ℂ} :
    IsRungeCompactPair ∅ K ↔ K = ∅ :=
  ⟨fun h => subset_empty_iff.mp h.subset,
    fun h => h ▸ isRungeCompactPair_empty_right.mpr isOpen_empty⟩

/-- **Finite-rank Runge approximation operator.** Let `K` be a compact set filled in `Ω ⊆ ℂ`
(without requiring `Ω` to be open), and let `V ⊆ ℂ` be an open neighbourhood of `K`. For every
`ε > 0` there are finitely many evaluation points `ζ i ∈ V \ K` and functions `g i : ℂ → ℂ`
holomorphic on `Ω` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and
bounded by `M` there, satisfies `‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

The points `ζ i` and holomorphic kernels `g i` depend only on `K`, `Ω`, `V`, and `ε`, not on `f`
or `F`. The resulting operator `f ↦ ∑ i, g i · • f (ζ i)` is linear in `f`, takes values in
functions holomorphic on `Ω`, and has finite rank for scalar `f`. -/
theorem IsFilledIn.exists_norm_sub_sum_smul_le {K Ω V : Set ℂ} (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨N, ζ, p, q, hζ, -, hqΩ, hop⟩ := exists_rational_norm_sub_sum_smul_le.{u} hK hV hKV
    (fun _ hx => hfill.compl_inter_connectedComponentIn_nonempty hK.isClosed hKΩ hx) hε
  refine ⟨N, ζ, fun i w => (p i).eval w / (q i).eval w, hζ, fun i =>
    (p i).differentiable.differentiableOn.div (q i).differentiable.differentiableOn
      fun z hz h0 => (hqΩ i z h0).1 hz, hop⟩

/-- **Finite-rank Runge operator.** For a Runge compact pair `(Ω, K)` and an open neighbourhood
`U ⊇ K`, there exists a compact neighbourhood `L` of `K` inside `U ∩ Ω` such that for every
`ε > 0` there are finitely many nodes `ζ j ∈ interior L`, weights `w j`, and `Ω`-holomorphic
functions `g j` (all independent of `f`) approximating every `U`-holomorphic function `f` on `K`
within `ε * B` for any upper bound `B ≥ 0` of `‖f‖` on `L`. -/
theorem exists_finite_rank_runge_operator {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
          ∃ g : Fin N → ℂ → ℂ,
            (∀ j, ζ j ∈ interior L) ∧
            (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
            ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
              ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
                ∀ z ∈ K,
                  ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨hΩ, hK, hKΩ, hfill⟩ := hRunge
  obtain ⟨L, hL, hKL, hLUO⟩ := exists_compact_between hK (hU.inter hΩ) (subset_inter hKU hKΩ)
  refine ⟨L, hL, hKL, hLUO, fun ε hε => ?_⟩
  obtain ⟨N, ζ, g, hζ, hg, hop⟩ := hfill.exists_norm_sub_sum_smul_le hK hKΩ isOpen_interior hKL hε
  refine ⟨N, ζ, fun _ => 1, g, fun j => (hζ j).1, hg, fun f hf B _ hLf z hz => ?_⟩
  have hbound := hop f B (hf.mono (interior_subset.trans (hLUO.trans inter_subset_left)))
    (fun y hy => hLf y (interior_subset hy)) z hz
  simpa only [one_mul, mul_comm (g _ z), smul_eq_mul] using hbound

end TauCeti
