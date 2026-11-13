/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Morse.LusternikSchnirelmann
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

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
Lusternik–Schnirelmann count of `M` (`TauCeti.lsCategoryCount_univ_le_minCriticalCount`), hence,
when `M` is nonempty, by the cup length of `M` plus one
(`TauCeti.lsCupLength_add_one_le_minCriticalCount`); it
vanishes exactly on the empty manifold (`TauCeti.minCriticalCount_eq_zero_iff`), and it is at
least `2` as soon as `M` has two points (`TauCeti.two_le_minCriticalCount`), attained on every
sphere by the height function (`TauCeti.minCriticalCount_sphere`).

The minimum is additive over a finite cover by pairwise disjoint open sets
(`TauCeti.minCriticalCount_eq_sum`), in particular over the connected components of a locally
connected manifold with finitely many components
(`TauCeti.minCriticalCount_eq_sum_connectedComponents`): a smooth function restricts to smooth
functions on the pieces, and smooth functions on the pieces glue to a smooth function. On a compact
boundaryless manifold of positive dimension every component is a compact manifold with at least two
points, so every continuous function has at least twice as many critical points as there are
components (`TauCeti.two_mul_card_connectedComponents_le_totalCriticalCount`), hence so does `c(M)`
(`TauCeti.two_mul_card_connectedComponents_le_minCriticalCount`).

## Main declarations

* `TauCeti.minCriticalCount`: the minimal number of critical points of a smooth function.
* `TauCeti.minCriticalCount_le` and `TauCeti.le_minCriticalCount_iff`: its characterization as
  the greatest lower bound of the critical counts of smooth functions.
* `TauCeti.exists_totalCriticalCount_eq_minCriticalCount`: the minimum is attained.
* `TauCeti.minCriticalCount_ne_top`: the minimum is finite on a compact manifold.
* `TauCeti.lsCategoryCount_univ_le_minCriticalCount`: the Lusternik–Schnirelmann lower bound.
* `TauCeti.lsCupLength_add_one_le_minCriticalCount`: the cup-length lower bound for nonempty `M`.
* `TauCeti.minCriticalCount_eq_zero_iff` and `TauCeti.two_le_minCriticalCount`: the elementary
  lower bounds.
* `TauCeti.minCriticalCount_sphere`: the minimum is `2` on every sphere.
* `TauCeti.minCriticalCount_eq_sum` and `TauCeti.minCriticalCount_eq_sum_connectedComponents`:
  the minimum is additive over finite disjoint open covers and over connected components.
* `TauCeti.two_mul_card_connectedComponents_le_minCriticalCount`: each component of a compact
  boundaryless manifold of positive dimension contributes at least two to `c(M)`.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
-/

public section

open Function Metric Module Set TopologicalSpace
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

/-- **Additivity of `c(M)`.** If finitely many pairwise disjoint open subsets `U i` cover `M`, the
minimal number of critical points of a smooth function on `M` is the sum of those of the open
submanifolds `U i`. -/
theorem minCriticalCount_eq_sum {ι : Type*} [Fintype ι] (U : ι → Opens M)
    (hd : Pairwise (Disjoint on U)) (hU : ⨆ i, U i = ⊤) :
    minCriticalCount I M = ∑ i, minCriticalCount I (U i) := by
  refine le_antisymm ?_ (le_minCriticalCount_iff.2 fun f hf ↦ ?_)
  · -- Glue smooth functions `g i` on the `U i` with `c(U i)` critical points into one function
    -- `F` on `M`, agreeing with `g i` on `U i`.
    choose g hg hgc using fun i ↦ exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := U i)
    have hcover : ⋃ i, (U i : Set M) = univ := by rw [← Opens.coe_iSup, hU, Opens.coe_top]
    have hg_eq (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) : g i ⟨x, hi⟩ = g j ⟨x, hj⟩ := by
      obtain rfl : i = j := by_contra fun h ↦ disjoint_left.1 (Opens.coe_disjoint.2 (hd h)) hi hj
      rfl
    set F : M → ℝ := liftCover (fun i ↦ (U i : Set M)) g hg_eq hcover
    have hF (i : ι) : (F ∘ Subtype.val : U i → ℝ) = g i :=
      funext fun x ↦ liftCover_coe (S := fun i ↦ (U i : Set M)) (hf := hg_eq) (hS := hcover) x
    have hFs : ContMDiff I 𝓘(ℝ) ∞ F := fun x ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover.symm ▸ mem_univ x : x ∈ ⋃ i, (U i : Set M))
      rw [← contMDiffAt_subtype_iff (U := U i) (x := ⟨x, hi⟩)]
      exact (hF i ▸ hg i).contMDiffAt
    calc minCriticalCount I M ≤ totalCriticalCount I F := minCriticalCount_le hFs
      _ = ∑ i, minCriticalCount I (U i) := by
        rw [totalCriticalCount_eq_sum U hd hU]
        exact Finset.sum_congr rfl fun i _ ↦ hF i ▸ hgc i
  · rw [totalCriticalCount_eq_sum U hd hU]
    exact Finset.sum_le_sum fun i _ ↦ minCriticalCount_le (hf.comp contMDiff_subtype_val)

/-- **The component sum formula for `c(M)`.** If `M` is locally connected with finitely many
connected components, for instance compact and boundaryless, then `c(M)` is the sum of the minimal
numbers of critical points of its components, each an open submanifold. -/
theorem minCriticalCount_eq_sum_connectedComponents [LocallyConnectedSpace M]
    [Fintype (ConnectedComponents M)] :
    minCriticalCount I M = ∑ C : ConnectedComponents M, minCriticalCount I C.opens :=
  minCriticalCount_eq_sum _ ConnectedComponents.pairwise_disjoint_opens
    ConnectedComponents.iSup_opens

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

/-- On a compact boundaryless manifold of positive dimension, `c(M)` is at least twice the number
of connected components. -/
theorem two_mul_card_connectedComponents_le_minCriticalCount [Nontrivial E] :
    2 * ENat.card (ConnectedComponents M) ≤ minCriticalCount I M :=
  le_minCriticalCount_iff.2 fun _ hf ↦
    two_mul_card_connectedComponents_le_totalCriticalCount hf.continuous

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
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

/-- **The cup-length lower bound for `c(M)`.** On a nonempty compact boundaryless manifold `M`,
every smooth function has more critical points than the cup length of `M` with coefficients in any
commutative ring `R` in the universe of `M`, so `lsCupLength M R + 1 ≤ c(M)`. -/
theorem lsCupLength_add_one_le_minCriticalCount [Nonempty M] (R : Type _) [CommRing R] :
    lsCupLength M R + 1 ≤ minCriticalCount I M :=
  lsCupLength_add_one_le_lsCategoryCount_univ.trans lsCategoryCount_univ_le_minCriticalCount

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
  rw [totalCriticalCount_def, criticalPoints_sphereHeight,
    encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]

end Sphere

end TauCeti
