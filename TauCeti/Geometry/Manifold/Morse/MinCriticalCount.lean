/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Morse.LusternikSchnirelmann
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.Morse.Generic

/-!
# The minimal number of critical points of a smooth function

The invariant `TauCeti.minCriticalCount I M` of a manifold `M` is the least number of critical
points of a smooth real function on `M`, the number `c(M)` of Lusternik–Schnirelmann theory. It
takes values in `ℕ∞` and minimizes over **all** smooth functions, with no Morse condition: a
function with infinitely many critical points contributes `⊤` and so never lowers the minimum.
Since `ℕ∞` is well-ordered, the minimum is attained by a smooth function
(`TauCeti.exists_totalCriticalCount_eq_minCriticalCount`).

On a compact boundaryless manifold the minimum is finite (`TauCeti.minCriticalCount_ne_top`):
a Morse function exists, and it has finitely many critical points. Together with attainment this
makes `c(M)` a natural number, realized by a smooth function with a finite critical set; no default
natural value is assigned when the minimum is infinite. The minimum is bounded below by the
Lusternik–Schnirelmann count of `M` (`TauCeti.lsCategoryCount_univ_le_minCriticalCount`), it
vanishes exactly on the empty manifold (`TauCeti.minCriticalCount_eq_zero_iff`), and it is at
least `2` as soon as `M` has two points (`TauCeti.two_le_minCriticalCount`), attained on every
sphere by the height function (`TauCeti.minCriticalCount_sphere`).

## Main declarations

* `TauCeti.minCriticalCount`: the minimal number of critical points of a smooth function.
* `TauCeti.minCriticalCount_le` and `TauCeti.le_minCriticalCount_iff`: its characterization as
  the greatest lower bound of the critical counts of smooth functions.
* `TauCeti.exists_totalCriticalCount_eq_minCriticalCount`: the minimum is attained.
* `TauCeti.minCriticalCount_ne_top`: the minimum is finite on a compact manifold.
* `TauCeti.lsCategoryCount_univ_le_minCriticalCount`: the Lusternik–Schnirelmann lower bound.
* `TauCeti.minCriticalCount_eq_zero_iff` and `TauCeti.two_le_minCriticalCount`: the elementary
  lower bounds.
* `TauCeti.minCriticalCount_sphere`: the minimum is `2` on every sphere.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
-/

public section

open Metric Module Set
open scoped ContDiff Manifold

namespace TauCeti

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

variable (I M) in
/-- The **minimal number of critical points** `c(M)` of a smooth real function on `M`, in `ℕ∞`.
It is the infimum of `TauCeti.totalCriticalCount I f` over all smooth `f`, Morse or not; it is
attained (`TauCeti.exists_totalCriticalCount_eq_minCriticalCount`) and it is `⊤` exactly when
every smooth function has infinitely many critical points. -/
noncomputable def minCriticalCount : ℕ∞ :=
  ⨅ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, totalCriticalCount I f

/-- Every smooth function has at least `c(M)` critical points. -/
theorem minCriticalCount_le (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    minCriticalCount I M ≤ totalCriticalCount I f :=
  iInf_le (fun g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ ↦ totalCriticalCount I g) ⟨f, hf⟩

/-- A lower bound for the number of critical points of every smooth function is a lower bound
for `c(M)`. -/
theorem le_minCriticalCount_iff {n : ℕ∞} :
    n ≤ minCriticalCount I M ↔ ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f → n ≤ totalCriticalCount I f :=
  ⟨fun h _ hf ↦ h.trans (minCriticalCount_le hf), fun h ↦ le_iInf fun g ↦ h g g.contMDiff⟩

/-- The minimal number of critical points is attained by a smooth function. -/
theorem exists_totalCriticalCount_eq_minCriticalCount :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ totalCriticalCount I f = minCriticalCount I M := by
  obtain ⟨g, hg⟩ := ciInf_mem fun g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ ↦ totalCriticalCount I g
  exact ⟨g, g.contMDiff, hg⟩

/-- The empty manifold has `c(M) = 0`. -/
@[simp]
theorem minCriticalCount_of_isEmpty [IsEmpty M] : minCriticalCount I M = 0 := by
  simpa [totalCriticalCount_def, eq_empty_of_isEmpty] using
    minCriticalCount_le (I := I) (f := (0 : M → ℝ)) contMDiff_const

section Boundaryless

variable [I.Boundaryless] [CompactSpace M]

/-- On a compact boundaryless manifold, `c(M) = 0` exactly when `M` is empty: on a nonempty one
every continuous function has a critical point. -/
theorem minCriticalCount_eq_zero_iff : minCriticalCount I M = 0 ↔ IsEmpty M := by
  refine ⟨fun h ↦ not_nonempty_iff.1 fun hM ↦ ?_, fun _ ↦ minCriticalCount_of_isEmpty⟩
  obtain ⟨f, hf, hfc⟩ := exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := M)
  rw [h, totalCriticalCount_def, encard_eq_zero] at hfc
  exact (criticalPoints_nonempty (I := I) hf.continuous).ne_empty hfc

/-- On a compact boundaryless manifold with at least two points, every smooth function has at
least two critical points, so `2 ≤ c(M)`. -/
theorem two_le_minCriticalCount [Nontrivial M] : 2 ≤ minCriticalCount I M :=
  le_minCriticalCount_iff.2 fun _ hf ↦ two_le_totalCriticalCount hf.continuous

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- On a compact boundaryless manifold the minimal number of critical points is finite: a Morse
function exists, and it has finitely many critical points. -/
theorem minCriticalCount_ne_top : minCriticalCount I M ≠ ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  exact ne_top_of_le_ne_top hf.totalCriticalCount_ne_top (minCriticalCount_le hf.contMDiff)

/-- **The Lusternik–Schnirelmann lower bound for `c(M)`.** On a compact boundaryless manifold,
every smooth function has at least as many critical points as the Lusternik–Schnirelmann count of
`M`, so `c(M)` is bounded below by that count. -/
theorem lsCategoryCount_univ_le_minCriticalCount : lsCategoryCount M univ ≤ minCriticalCount I M :=
  le_minCriticalCount_iff.2 fun _ hf ↦ lsCategoryCount_univ_le_totalCriticalCount hf

end Boundaryless

end General

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The minimal number of critical points of a sphere is `2`.** The height function has exactly
the two poles as critical points, and no smooth function on a compact manifold with at least two
points has fewer. -/
@[simp]
theorem minCriticalCount_sphere : minCriticalCount (𝓡 n) (sphere (0 : E) 1) = 2 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E :=
    nontrivial_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = n + 1)]; lia)
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have : Nontrivial (sphere (0 : E) 1) := ⟨⟨v, -v, ne_neg_of_mem_unit_sphere ℝ v⟩⟩
  refine le_antisymm ((minCriticalCount_le (contMDiff_sphereHeight v)).trans_eq ?_)
    two_le_minCriticalCount
  have hcrit : criticalPoints (𝓡 n) (sphereHeight v) = {v, -v} := by
    ext x
    simp [mem_criticalPoints]
  rw [totalCriticalCount_def, hcrit, encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]

end Sphere

end TauCeti
