/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Interior
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier

/-!
# Subdividing a triangulation along finitely many affine functionals

Let `K` be a finite geometric simplicial complex in a finite-dimensional real normed space and let
`g i` be finitely many continuous affine functionals. Then `K` has a finite subdivision `K'` on
each simplex of which every `g i` keeps a constant sign in the weak sense: it is either
nonnegative on the whole simplex or nonpositive on the whole simplex
(`Geometry.SimplicialComplex.exists_isSubdivision_forall_nonneg_or_forall_nonpos`). The part of
each hyperplane `g i = 0` in `|K|` is then a union of simplices of `K'`.

Consequently, for finitely many convex polyhedra `C j` there is a finite subdivision `K'` of `K`
each of whose simplices lies in `C j` as soon as its open simplex meets `C j`
(`Geometry.SimplicialComplex.exists_isSubdivision_convexHull_subset_of_inter_nonempty`): an
affine functional which is nonnegative on a simplex and vanishes at a point of its open simplex
vanishes on the whole simplex (`TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior`). This is
the form in which the theorem is used for piecewise-linear maps: if `f` is affine on each `C j`
and the `C j` cover `|K|`, then `f` is affine on every simplex of `K'`
(`TauCeti.IsPLOn.exists_isSubdivision_eqOn` in `TauCeti.Topology.PL.Simplicial`).

The proof cuts `|K|` into the cells of the arrangement of the hyperplanes `g i = 0`, intersected
with the simplices of `K`. A sign vector `τ : ι → SignType` defines the closed cell
`{x | ∀ i, sign (g i x) = τ i ∨ g i x = 0}` and the open cell `{x | ∀ i, sign (g i x) = τ i}`.
When the open cell is nonempty it is the intrinsic interior of the closed cell. So, as for the
common subdivision of two triangulations
(`Geometry.SimplicialComplex.exists_space_eq_inter`), the convex cells `σ ∩ C(τ)`, for the
simplices `σ` of `K` and the sign vectors `τ` whose open cell meets the open simplex of `σ`, have
pairwise disjoint intrinsic interiors, and the intrinsic frontier of each is covered by strictly
smaller ones. They therefore have a simplicial subdivision
(`Geometry.SimplicialComplex.exists_subdivision`).

## Main results

* `Geometry.SimplicialComplex.exists_isSubdivision_forall_nonneg_or_forall_nonpos`: a finite
  subdivision on whose simplices finitely many affine functionals do not change sign.
* `Geometry.SimplicialComplex.exists_isSubdivision_convexHull_subset_of_inter_nonempty`: a finite
  subdivision each of whose simplices lies in each of finitely many convex polyhedra that its open
  simplex meets.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (subdivisions of cell complexes, and triangulations of piecewise-linear maps).
* J. F. P. Hudson, *Piecewise Linear Topology*, Benjamin (1969), Chapter I (cell complexes and
  their simplicial subdivisions).
-/

public section

open Set

namespace Geometry.SimplicialComplex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Subdividing along the arrangement -/

variable [FiniteDimensional ℝ E] {K : SimplicialComplex ℝ E}

/-- **Subdividing a triangulation along finitely many hyperplanes.** A finite geometric simplicial
complex `K` in a finite-dimensional real normed space has a finite subdivision on each simplex of
which each of finitely many continuous affine functionals `g i` is nonnegative throughout or
nonpositive throughout. -/
theorem exists_isSubdivision_forall_nonneg_or_forall_nonpos [Finite ι] (hK : K.faces.Finite)
    (g : ι → E →ᴬ[ℝ] ℝ) :
    ∃ K' : SimplicialComplex ℝ E, K'.IsSubdivision K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∀ i, (∀ y ∈ convexHull ℝ (s : Set E), 0 ≤ g i y) ∨
        ∀ y ∈ convexHull ℝ (s : Set E), g i y ≤ 0 := by
  -- The proof checks the hypotheses of `exists_subdivision` for the cells `σ ∩ C(τ)`: they are
  -- compact and convex, finite in number, with intrinsic interiors the pieces `σ° ∩ C(τ)°`
  -- (`hri`), hence pairwise disjoint (`hdisj`), and each point of a cell is an intrinsic interior
  -- point of a smaller cell (`hcell`), which covers the intrinsic frontiers (`hfr`).
  have : Finite K.faces := hK.to_subtype
  -- The cells: `σ ∩ C(τ)` for simplices `σ` of `K` and sign vectors `τ` whose open cell meets the
  -- open simplex of `σ`.
  let J := {p : K.faces × (ι → SignType) //
    (intrinsicInterior ℝ (convexHull ℝ (p.1.1 : Set E)) ∩ TauCeti.Convex.signCell g p.2).Nonempty}
  let P : J → Set E := fun p => convexHull ℝ (p.1.1.1 : Set E) ∩ TauCeti.Convex.weakSignCell g p.1.2
  have hPv : ∀ p, Convex ℝ (P p) := fun p =>
    (convex_convexHull ℝ _).inter (TauCeti.Convex.convex_weakSignCell g _)
  have hPc : ∀ p, IsCompact (P p) := fun p =>
    (p.1.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).inter_right
      (TauCeti.Convex.isClosed_weakSignCell g _)
  have hri : ∀ p, intrinsicInterior ℝ (P p) =
      intrinsicInterior ℝ (convexHull ℝ (p.1.1.1 : Set E)) ∩
        TauCeti.Convex.signCell g p.1.2 := fun p => by
    obtain ⟨x, hxσ, hxτ⟩ := p.2
    have hτ := TauCeti.Convex.intrinsicInterior_closure_signCell (g := g) (σ := p.1.2)
    rw [TauCeti.Convex.closure_signCell ⟨x, hxτ⟩] at hτ
    rw [TauCeti.intrinsicInterior_inter (convex_convexHull ℝ _)
      (TauCeti.Convex.convex_weakSignCell g _)
      (hτ ▸ ⟨x, hxσ, hxτ⟩), hτ]
  -- A point of a cell lies in the intrinsic interior of a cell contained in it: the cell of its
  -- carrier simplex and of its own sign vector.
  have hcell : ∀ ⦃x : E⦄ ⦃σ : Finset E⦄ (_ : σ ∈ K.faces) ⦃τ : ι → SignType⦄,
      x ∈ convexHull ℝ (σ : Set E) → x ∈ TauCeti.Convex.weakSignCell g τ →
      ∃ q : J, x ∈ intrinsicInterior ℝ (P q) ∧
        P q ⊆ convexHull ℝ (σ : Set E) ∩ TauCeti.Convex.weakSignCell g τ := by
    intro x σ hσ τ hxσ hxτ
    obtain ⟨σ', hσ', hσσ', hxσ'⟩ := exists_mem_faces_subset_mem_intrinsicInterior hσ hxσ
    let q : J := ⟨(⟨σ', hσ'⟩, fun i => SignType.sign (g i x)), x, hxσ',
      TauCeti.Convex.mem_signCell_sign g x⟩
    exact ⟨q, (hri q).symm ▸ ⟨hxσ', TauCeti.Convex.mem_signCell_sign g x⟩, inter_subset_inter
      (convexHull_mono (Finset.coe_subset.2 hσσ'))
      (TauCeti.Convex.weakSignCell_subset_of_specializes
        (TauCeti.Convex.mem_weakSignCell_iff_specializes.mp hxτ))⟩
  have hPne : ∀ p, (P p).Nonempty := fun p => p.2.mono
    (inter_subset_inter intrinsicInterior_subset (TauCeti.Convex.signCell_subset_weakSignCell g _))
  have hdisj : Pairwise fun p q : J => Disjoint (intrinsicInterior ℝ (P p))
      (intrinsicInterior ℝ (P q)) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun x hxp hxq => hpq ?_
    rw [hri] at hxp hxq
    refine Subtype.ext (Prod.ext
      (Subtype.ext (eq_of_mem_intrinsicInterior p.1.1.2 q.1.1.2 hxp.1 hxq.1)) ?_)
    funext i
    exact (TauCeti.Convex.mem_signCell.mp hxp.2 i).symm.trans
      (TauCeti.Convex.mem_signCell.mp hxq.2 i)
  have hfr := fun p => TauCeti.intrinsicFrontier_subset_iUnion_of_exists_mem_intrinsicInterior p
    (hPc p).isClosed fun x hx => hcell p.1.1.2 hx.1 hx.2
  obtain ⟨M, hMs, hMP, hMface, -⟩ := exists_subdivision P hPc hPv
    (fun q => ((hPne q).intrinsicInterior (hPv q)).some)
    (fun q => ((hPne q).intrinsicInterior (hPv q)).some_mem) (locallyFinite_of_finite P) hdisj hfr
  have hcov : ∀ x ∈ K.space, ∃ q, x ∈ P q := fun x hx => by
    obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.1 hx
    obtain ⟨q, hxq, -⟩ := hcell hσ hxσ
      (TauCeti.Convex.signCell_subset_weakSignCell g _ (TauCeti.Convex.mem_signCell_sign g x))
    exact ⟨q, intrinsicInterior_subset hxq⟩
  obtain ⟨hM, hMfin, hconv⟩ := isSubdivision_of_cells (fun p => p.1.1.2)
    (fun p => inter_subset_left) hPv hcov hMs (fun p => (hMP p).2)
    fun s hs => (hMface s hs).imp fun _ h => h.2
  refine ⟨M, hM, hMfin, fun s hs i => ?_⟩
  obtain ⟨p, hp⟩ := hconv s hs
  exact TauCeti.Convex.nonneg_or_nonpos_of_subset_weakSignCell (hp.trans inter_subset_right) i

/-- **Subdividing a triangulation along finitely many convex polyhedra.** A finite geometric
simplicial complex `K` in a finite-dimensional real normed space has a finite subdivision each of
whose simplices lies in each of finitely many convex polyhedra `C j` that its open simplex meets.
-/
theorem exists_isSubdivision_convexHull_subset_of_inter_nonempty {J : Type*} [Finite J]
    (hK : K.faces.Finite) {C : J → Set E} (hC : ∀ j, TauCeti.IsConvexPolyhedron (C j)) :
    ∃ K' : SimplicialComplex ℝ E, K'.IsSubdivision K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∀ j,
        (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩ C j).Nonempty →
          convexHull ℝ (s : Set E) ⊆ C j := by
  choose n g hg using fun j => TauCeti.isConvexPolyhedron_iff.1 (hC j)
  obtain ⟨K', hK'K, hK'f, hsign⟩ := exists_isSubdivision_forall_nonneg_or_forall_nonpos hK
    fun p : Σ j, Fin (n j) => g p.1 p.2
  refine ⟨K', hK'K, hK'f, fun s hs j ⟨x, hxs, hxC⟩ y hy => ?_⟩
  rw [hg] at hxC ⊢
  intro k
  rcases hsign s hs ⟨j, k⟩ with h | h
  · -- `g j k` is nonnegative on the simplex and vanishes at `x`, hence on the whole simplex
    have hx0 : g j k x = 0 := le_antisymm (hxC k) (h x (intrinsicInterior_subset hxs))
    exact (TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior (g := (g j k : E →ᵃ[ℝ] ℝ)) h hxs
      hx0 hy).le
  · exact h y hy

end Geometry.SimplicialComplex
