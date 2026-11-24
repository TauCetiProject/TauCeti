/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Morse.LusternikSchnirelmann
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import Mathlib.Topology.Algebra.Projectivization
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.Torus
import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.Topology.Homotopy.LusternikSchnirelmann.RealProjective
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
import TauCeti.Geometry.Manifold.Morse.Generic.Basic
import TauCeti.Geometry.Manifold.Morse.TwoCriticalPoints

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
sphere by the height function (`TauCeti.minCriticalCount_sphere`). Conversely, `c(M) = 2` only on
a topological sphere: a smooth function with two critical points, degenerate or not, makes a
compact boundaryless manifold of dimension `m` homeomorphic to `Sᵐ`
(`TauCeti.nonempty_homeomorph_sphere_of_two_criticalPoints`), so
`TauCeti.nonempty_homeomorph_sphere_of_minCriticalCount_eq_two` holds. Hence a compact
boundaryless manifold with at least two points which is not homeomorphic to `Sᵐ` has `3 ≤ c(M)`
(`TauCeti.three_le_minCriticalCount_of_isEmpty_homeomorph`), in particular when `m ≥ 2` and `M`
is nonempty and not simply connected
(`TauCeti.three_le_minCriticalCount_of_not_simplyConnectedSpace`). On real projective space
`ℝPⁿ`, `n ≥ 2`, whose fundamental group has two elements, this gives `3 ≤ c(ℝPⁿ)`
(`TauCeti.three_le_minCriticalCount_projectivization_real`), while a moment function with
distinct weights has `n + 1` critical points on `ℝPⁿ` and on `ℂPⁿ`, so `c(ℝPⁿ) ≤ n + 1` and
`c(ℂPⁿ) ≤ n + 1` (`TauCeti.minCriticalCount_projectivization_le`).
So `c(ℝP²) = 3` (`TauCeti.minCriticalCount_projectivization_real_fin_three`): every smooth
function on the real projective plane has at least three critical points, and the moment function
has exactly three. On the torus `Tᵐ` the Lusternik–Schnirelmann count is `m + 1`
(`TauCeti.lsCategoryCount_univ_pi_addCircle`), so every
smooth function on `Tᵐ`, degenerate or not, has at least `m + 1` critical points
(`TauCeti.card_add_one_le_totalCriticalCount_torus` and
`TauCeti.card_add_one_le_minCriticalCount_torus`). On the real projective plane the
Lusternik–Schnirelmann count is `3`
(`TauCeti.lsCategoryCount_univ_projectivization_real_fin_three`): its cup length over `ZMod 2` is
`2`, and the moment function with three distinct weights has three critical points.

The minimum is additive over a finite cover by pairwise disjoint open sets
(`TauCeti.minCriticalCount_eq_sum`), in particular over the connected components of a locally
connected manifold with finitely many components
(`TauCeti.minCriticalCount_eq_sum_connectedComponents`): a smooth function restricts to smooth
functions on the pieces, and smooth functions on the pieces glue to a smooth function. For the same
reason it is additive over disjoint unions `M ⊕ M'` (`TauCeti.minCriticalCount_sum`); two disjoint
spheres have `c = 2 + 2 = 4` (`TauCeti.minCriticalCount_sum_sphere`). On a compact
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
* `TauCeti.nonempty_homeomorph_sphere_of_minCriticalCount_eq_two`: a compact boundaryless
  manifold with `c(M) = 2` is homeomorphic to a sphere.
* `TauCeti.three_le_minCriticalCount_of_isEmpty_homeomorph` and
  `TauCeti.three_le_minCriticalCount_of_not_simplyConnectedSpace`: `3 ≤ c(M)` when `M` is not
  homeomorphic to a sphere, in particular when it is not simply connected and `dim M ≥ 2`.
* `TauCeti.minCriticalCount_projectivization_real_fin_three`: `c(ℝP²) = 3`.
* `TauCeti.minCriticalCount_eq_sum` and `TauCeti.minCriticalCount_eq_sum_connectedComponents`:
  the minimum is additive over finite disjoint open covers and over connected components.
* `TauCeti.minCriticalCount_sum` and `TauCeti.minCriticalCount_sum_sphere`: the minimum is
  additive over disjoint unions `M ⊕ M'`, so two disjoint spheres have `c = 4`.
* `TauCeti.two_mul_card_connectedComponents_le_minCriticalCount`: each component of a compact
  boundaryless manifold of positive dimension contributes at least two to `c(M)`.
* `TauCeti.card_add_one_le_totalCriticalCount_torus` and
  `TauCeti.card_add_one_le_minCriticalCount_torus`: every smooth function on the torus `Tᵐ` has at
  least `m + 1` critical points.
* `TauCeti.lsCategoryCount_univ_projectivization_real_fin_three`: the Lusternik–Schnirelmann
  count of the real projective plane is `3`.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Corollary 1: a compact space covered by two open
  sets homeomorphic to `ℝᵐ` is homeomorphic to `Sᵐ`, which gives Reeb's theorem that a closed
  manifold carrying a function with two critical points is homeomorphic to a sphere.
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
    exact Finset.sum_le_sum fun i _ ↦ minCriticalCount_le (hf.comp contMDiff_subtypeVal)

/-- **The component sum formula for `c(M)`.** If `M` is locally connected with finitely many
connected components, for instance compact and boundaryless, then `c(M)` is the sum of the minimal
numbers of critical points of its components, each an open submanifold. -/
theorem minCriticalCount_eq_sum_connectedComponents [LocallyConnectedSpace M]
    [Fintype (ConnectedComponents M)] :
    minCriticalCount I M = ∑ C : ConnectedComponents M, minCriticalCount I C.opens :=
  minCriticalCount_eq_sum _ ConnectedComponents.pairwise_disjoint_opens
    ConnectedComponents.iSup_opens

/-- **`c(M)` of a disjoint union.** The minimal number of critical points of a smooth function on
`M ⊕ M'` is the sum of those of `M` and `M'`: a smooth function on `M ⊕ M'` is a pair of smooth
functions on the summands, and its critical points are theirs. -/
@[simp]
theorem minCriticalCount_sum {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] :
    minCriticalCount I (M ⊕ M') = minCriticalCount I M + minCriticalCount I M' := by
  refine le_antisymm ?_ (le_minCriticalCount_iff.2 fun F hF ↦ ?_)
  · obtain ⟨f, hf, hfc⟩ := exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := M)
    obtain ⟨g, hg, hgc⟩ := exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := M')
    calc minCriticalCount I (M ⊕ M') ≤ totalCriticalCount I (Sum.elim f g) :=
          minCriticalCount_le (hf.sumElim hg)
      _ = minCriticalCount I M + minCriticalCount I M' := by
        rw [totalCriticalCount_sumElim, hfc, hgc]
  · rw [← Sum.elim_comp_inl_inr F, totalCriticalCount_sumElim]
    exact add_le_add (minCriticalCount_le (hF.comp ContMDiff.inl))
      (minCriticalCount_le (hF.comp ContMDiff.inr))

section Boundaryless

variable [I.Boundaryless] [CompactSpace M]

/-- On a compact boundaryless manifold, `c(M) = 0` exactly when `M` is empty: on a nonempty one
every function has a critical point. -/
theorem minCriticalCount_eq_zero_iff : minCriticalCount I M = 0 ↔ IsEmpty M := by
  refine ⟨fun h ↦ not_nonempty_iff.1 fun hM ↦ ?_, fun _ ↦ minCriticalCount_of_isEmpty⟩
  obtain ⟨f, -, hfc⟩ := exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := M)
  rw [h, totalCriticalCount_def, encard_eq_zero] at hfc
  exact (criticalPoints_nonempty (I := I) (f := f)).ne_empty hfc

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

variable [T2Space M] [IsManifold I ∞ M] in
/-- On a compact boundaryless manifold the minimal number of critical points is finite: a Morse
function exists, and it has finitely many critical points. -/
theorem minCriticalCount_ne_top : minCriticalCount I M ≠ ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  exact ne_top_of_le_ne_top hf.totalCriticalCount_ne_top (minCriticalCount_le hf.contMDiff)

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

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

/-- **A manifold with `c(M) = 2` is a sphere.** If the minimal number of critical points of a
smooth function on a compact boundaryless manifold `M` modelled on a space of dimension `m` is
`2`, then `M` is homeomorphic to the sphere `Sᵐ`: a smooth function attaining the minimum has
exactly two critical points, possibly degenerate. The conclusion is topological; `M` need not be
diffeomorphic to the standard sphere. -/
theorem nonempty_homeomorph_sphere_of_minCriticalCount_eq_two (h : minCriticalCount I M = 2) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) := by
  obtain ⟨f, hf, hfc⟩ := exists_totalCriticalCount_eq_minCriticalCount (I := I) (M := M)
  exact nonempty_homeomorph_sphere_of_two_criticalPoints hf (hfc.trans h)

/-- **Three critical points off the sphere.** On a compact boundaryless manifold `M` with at
least two points, modelled on a space of dimension `m`, which is not homeomorphic to the sphere
`Sᵐ`, every smooth function has at least three critical points, so `3 ≤ c(M)`. -/
theorem three_le_minCriticalCount_of_isEmpty_homeomorph [Nontrivial M]
    (h : IsEmpty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1)) :
    3 ≤ minCriticalCount I M :=
  Order.add_one_le_of_lt (two_le_minCriticalCount.lt_of_ne fun h2 ↦
    h.false (nonempty_homeomorph_sphere_of_minCriticalCount_eq_two h2.symm).some)

/-- **Three critical points on a manifold that is not simply connected.** On a nonempty compact
boundaryless manifold of dimension at least `2` which is not simply connected, every smooth
function has at least three critical points, so `3 ≤ c(M)`: such a manifold has at least two
points and is not homeomorphic to a sphere, since spheres of dimension at least `2` are simply
connected. -/
theorem three_le_minCriticalCount_of_not_simplyConnectedSpace [Nonempty M]
    (hE : 2 ≤ finrank ℝ E) (h : ¬SimplyConnectedSpace M) : 3 ≤ minCriticalCount I M := by
  -- A nonempty subsingleton is contractible, hence simply connected.
  have : Nontrivial M := not_subsingleton_iff_nontrivial.1 fun _ ↦ h inferInstance
  refine three_le_minCriticalCount_of_isEmpty_homeomorph ⟨fun e ↦ h ?_⟩
  have := simplyConnectedSpace_sphere_euclideanSpace hE
  exact e.toHomotopyEquiv.simplyConnectedSpace

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

/-- **The minimal number of critical points of two disjoint spheres is `4`.** It is `2 + 2`, one
pair of poles of a height function on each sphere, a value that a count for connected manifolds
only, such as Takens' `F(M)`, does not define. -/
theorem minCriticalCount_sum_sphere {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [Fact (finrank ℝ E' = n + 1)] :
    minCriticalCount (𝓡 n) (sphere (0 : E) 1 ⊕ sphere (0 : E') 1) = 4 := by
  rw [minCriticalCount_sum, minCriticalCount_sphere, minCriticalCount_sphere]
  norm_num

end Sphere

section Projectivization

open Projectivization
open scoped LinearAlgebra.Projectivization

variable {n : ℕ}

/-- **At least three critical points on `ℝPⁿ`.** For `n ≥ 2`, every smooth function on real
projective space `ℝPⁿ` has at least three critical points, since `ℝPⁿ` is not simply
connected. -/
theorem three_le_minCriticalCount_projectivization_real (hn : 2 ≤ n) :
    3 ≤ minCriticalCount 𝓘(ℝ, Fin n → ℝ) (ℙ ℝ (Fin (n + 1) → ℝ)) := by
  have : Nonempty (ℙ ℝ (Fin (n + 1) → ℝ)) := ⟨mk ℝ (Pi.single 0 1) (by simp)⟩
  refine three_le_minCriticalCount_of_not_simplyConnectedSpace (by simpa using hn) fun h ↦ ?_
  exact RealProjectiveSpace.not_simplyConnectedSpace n hn
    (RealProjectiveSpace.homeomorphProjectivization n).toHomotopyEquiv.simplyConnectedSpace

/-- Some smooth function on the projective space `𝕜Pⁿ`, `𝕜 = ℝ` or `ℂ`, a moment function with
distinct weights, has exactly `n + 1` critical points, so `c(𝕜Pⁿ) ≤ n + 1`. -/
theorem minCriticalCount_projectivization_le {𝕜 : Type*} [RCLike 𝕜] :
    minCriticalCount 𝓘(ℝ, Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) ≤ n + 1 :=
  (minCriticalCount_le (contMDiff_projectiveMomentFunction (𝕜 := 𝕜) fun i ↦ (i : ℝ))).trans_eq
    (totalCriticalCount_projectiveMomentFunction fun _ _ h ↦ Fin.ext (by exact_mod_cast h))

/-- **The minimal number of critical points of the real projective plane is `3`.** Every smooth
function on `ℝP²` has at least three critical points, degenerate or not, and a moment function
with distinct weights has exactly three. -/
theorem minCriticalCount_projectivization_real_fin_three :
    minCriticalCount 𝓘(ℝ, Fin 2 → ℝ) (ℙ ℝ (Fin 3 → ℝ)) = 3 :=
  le_antisymm minCriticalCount_projectivization_le
    (three_le_minCriticalCount_projectivization_real le_rfl)

end Projectivization

section Torus

variable {ι : Type*} [Fintype ι]

/-- **The Lusternik–Schnirelmann bound on the torus.** Every smooth function on the torus
`Tᵐ = ∀ i, AddCircle (p i)` has at least `m + 1` critical points, degenerate or not, since the
Lusternik–Schnirelmann count of `Tᵐ` is `m + 1`. For Morse functions the stronger bound `2ᵐ` holds
(`TauCeti.IsMorse.two_pow_card_le_totalCriticalCount_torus`). -/
theorem card_add_one_le_totalCriticalCount_torus {p : ι → ℝ} [∀ i, Fact (0 < p i)]
    {f : (∀ i, AddCircle (p i)) → ℝ}
    (hf : ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 𝓘(ℝ) ∞ f) :
    (Fintype.card ι + 1 : ℕ∞) ≤ totalCriticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f :=
  lsCategoryCount_univ_pi_addCircle.symm.trans_le
    (lsCategoryCount_univ_le_totalCriticalCount hf)

/-- **The minimal number of critical points of the torus `Tᵐ` is at least `m + 1`.** -/
theorem card_add_one_le_minCriticalCount_torus (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    (Fintype.card ι + 1 : ℕ∞) ≤
      minCriticalCount (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  le_minCriticalCount_iff.2 fun _ ↦ card_add_one_le_totalCriticalCount_torus

end Torus

section RealProjectivePlane

open scoped LinearAlgebra.Projectivization

/-- **The Lusternik–Schnirelmann count of the real projective plane is `3`**: three open subsets of
`ℙ ℝ (Fin 3 → ℝ)` whose inclusions are nullhomotopic cover it, and two do not. -/
theorem lsCategoryCount_univ_projectivization_real_fin_three :
    lsCategoryCount (ℙ ℝ (Fin 3 → ℝ)) univ = 3 := by
  have hw : Injective fun i : Fin 3 ↦ (i : ℝ) := Nat.cast_injective.comp Fin.val_injective
  refine le_antisymm ((lsCategoryCount_univ_le_totalCriticalCount (I := 𝓘(ℝ, Fin 2 → ℝ))
    (contMDiff_projectiveMomentFunction (𝕜 := ℝ) fun i : Fin 3 ↦ (i : ℝ))).trans_eq ?_)
    (le_of_eq_of_le ?_ (lsCupLength_add_one_le_lsCategoryCount_univ (R := ZMod 2)))
  · rw [totalCriticalCount_projectiveMomentFunction hw]
    norm_num
  · rw [lsCupLength_projectivization_real_fin_three_zmod_two]
    norm_num

end RealProjectivePlane

end TauCeti
