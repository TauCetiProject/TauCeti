/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.Intrinsic
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

/-! ### Cells of a hyperplane arrangement -/

section SignCell

/-- The real numbers whose sign is `t` or which vanish. -/
private def signSet (t : SignType) : Set ℝ := {r | SignType.sign r = t ∨ r = 0}

private theorem convex_and_isClosed_signSet (t : SignType) :
    Convex ℝ (signSet t) ∧ IsClosed (signSet t) := by
  rcases t with _ | _ | _
  · have : signSet 0 = {0} := by ext r; simp [signSet]
    exact this ▸ ⟨convex_singleton 0, isClosed_singleton⟩
  · have : signSet (-1) = Iic 0 := by
      ext r; simp [signSet, sign_eq_neg_one_iff, le_iff_lt_or_eq]
    exact this ▸ ⟨convex_Iic 0, isClosed_Iic⟩
  · have : signSet 1 = Ici 0 := by
      ext r
      simp only [signSet, mem_ofPred_eq, mem_Ici, sign_eq_one_iff]
      exact ⟨fun h => h.elim le_of_lt ge_of_eq, fun h => h.lt_or_eq.imp_right Eq.symm⟩
    exact this ▸ ⟨convex_Ici 0, isClosed_Ici⟩

/-- The closed cell of the arrangement of the hyperplanes `g i = 0` with sign vector `τ`: the
points at which each `g i` has the sign `τ i` or vanishes. -/
private def signCell (g : ι → E →ᴬ[ℝ] ℝ) (τ : ι → SignType) : Set E :=
  ⋂ i, g i ⁻¹' signSet (τ i)

/-- The open cell of the arrangement with sign vector `τ`: the points at which each `g i` has the
sign `τ i`. -/
private def openSignCell (g : ι → E →ᴬ[ℝ] ℝ) (τ : ι → SignType) : Set E :=
  {x | ∀ i, SignType.sign (g i x) = τ i}

variable {g : ι → E →ᴬ[ℝ] ℝ} {τ : ι → SignType} {x : E}

private theorem mem_signCell : x ∈ signCell g τ ↔ ∀ i, SignType.sign (g i x) = τ i ∨ g i x = 0 :=
  by simp [signCell, signSet]

private theorem convex_signCell : Convex ℝ (signCell g τ) :=
  convex_iInter fun i => (convex_and_isClosed_signSet (τ i)).1.affine_preimage (g i : E →ᵃ[ℝ] ℝ)

private theorem isClosed_signCell : IsClosed (signCell g τ) :=
  isClosed_iInter fun i => (convex_and_isClosed_signSet (τ i)).2.preimage (g i).continuous

private theorem openSignCell_subset_signCell : openSignCell g τ ⊆ signCell g τ :=
  fun _ hx => mem_signCell.2 fun i => .inl (hx i)

/-- Every point lies in the open cell of its own sign vector. -/
private theorem mem_openSignCell_sign (g : ι → E →ᴬ[ℝ] ℝ) (x : E) :
    x ∈ openSignCell g (fun i => SignType.sign (g i x)) :=
  fun _ => rfl

/-- The closed cell of the sign vector of a point of a closed cell lies in that closed cell. -/
private theorem signCell_sign_subset (hx : x ∈ signCell g τ) :
    signCell g (fun i => SignType.sign (g i x)) ⊆ signCell g τ := by
  intro y hy
  rw [mem_signCell] at hx hy ⊢
  intro i
  rcases hy i with hy | hy
  · rcases hx i with hx | hx
    · exact .inl (hy.trans hx)
    · exact .inr (sign_eq_zero_iff.1 (hy.trans (by simp [hx])))
  · exact .inr hy

/-- On a closed cell each `g i` is nonnegative or nonpositive throughout. -/
private theorem nonneg_or_nonpos_of_subset_signCell {S : Set E} (hS : S ⊆ signCell g τ) (i : ι) :
    (∀ y ∈ S, 0 ≤ g i y) ∨ ∀ y ∈ S, g i y ≤ 0 := by
  have h : ∀ y ∈ S, SignType.sign (g i y) = τ i ∨ g i y = 0 := fun y hy => mem_signCell.1 (hS hy) i
  rcases hτ : τ i with _ | _ | _
  · exact .inr fun y hy => by
      rcases h y hy with h | h
      · exact (sign_eq_zero_iff.1 (h.trans hτ)).le
      · exact h.le
  · exact .inr fun y hy => by
      rcases h y hy with h | h
      · exact (sign_eq_neg_one_iff.1 (h.trans hτ)).le
      · exact h.le
  · exact .inl fun y hy => by
      rcases h y hy with h | h
      · exact (sign_eq_one_iff.1 (h.trans hτ)).le
      · exact h.ge

/-- If `g i` vanishes at an intrinsic interior point of a subset `S` of a closed cell, it vanishes
on all of `S`. -/
private theorem apply_eq_zero_of_mem_intrinsicInterior {S : Set E} (hS : S ⊆ signCell g τ)
    {i : ι} (hx : x ∈ intrinsicInterior ℝ S) (hgx : g i x = 0) {y : E} (hy : y ∈ S) :
    g i y = 0 := by
  rcases nonneg_or_nonpos_of_subset_signCell hS i with h | h
  · exact TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior (g := (g i : E →ᵃ[ℝ] ℝ)) h hx hgx hy
  · have := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior (g := -(g i : E →ᵃ[ℝ] ℝ))
      (fun y hy => by simpa using h y hy) hx (by simp [hgx]) hy
    simpa using this

/-- A nonempty open cell is the intrinsic interior of its closed cell. -/
private theorem intrinsicInterior_signCell [Finite ι] (h : (openSignCell g τ).Nonempty) :
    intrinsicInterior ℝ (signCell g τ) = openSignCell g τ := by
  obtain ⟨p, hp⟩ := h
  refine Subset.antisymm (fun x hx i => ?_) fun x hx => ?_
  · -- a vanishing `g i` at `x` vanishes on the whole closed cell, in particular at `p`
    rcases mem_signCell.1 (intrinsicInterior_subset hx) i with h | h
    · exact h
    · have hp0 := apply_eq_zero_of_mem_intrinsicInterior subset_rfl hx h
        (openSignCell_subset_signCell hp)
      rw [h, ← hp i, hp0]
  · -- near `x`, the signs `τ i ≠ 0` persist, and the equations `g i = 0` for `τ i = 0` hold on
    -- the affine span of the closed cell
    rw [TauCeti.mem_intrinsicInterior_iff_eventually]
    refine ⟨subset_affineSpan ℝ _ (openSignCell_subset_signCell hx), ?_⟩
    have hev : ∀ i, ∀ᶠ y in nhds x, y ∈ affineSpan ℝ (signCell g τ) →
        SignType.sign (g i y) = τ i := by
      intro i
      have hc : ContinuousAt (g i) x := (g i).continuous.continuousAt
      rcases lt_trichotomy (g i x) 0 with hlt | heq | hgt
      · filter_upwards [hc.eventually_lt continuousAt_const hlt] with y hy _
        rw [← hx i, sign_neg hlt, sign_neg hy]
      · have hτ : τ i = 0 := by rw [← hx i, heq, sign_zero]
        have hS : (signCell g τ).EqOn (g i : E →ᵃ[ℝ] ℝ) (0 : E →ᵃ[ℝ] ℝ) := fun z hz => by
          rcases mem_signCell.1 hz i with h | h
          · simpa using sign_eq_zero_iff.1 (h.trans hτ)
          · simpa using h
        refine Filter.Eventually.of_forall fun y hyA => ?_
        have : g i y = 0 := by simpa using AffineMap.eqOn_affineSpan hS hyA
        rw [hτ, this, sign_zero]
      · filter_upwards [continuousAt_const.eventually_lt hc hgt] with y hy _
        rw [← hx i, sign_pos hgt, sign_pos hy]
    filter_upwards [Filter.eventually_all.2 hev] with y hy hyA
    exact openSignCell_subset_signCell fun i => hy i hyA

end SignCell

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
    (intrinsicInterior ℝ (convexHull ℝ (p.1.1 : Set E)) ∩ openSignCell g p.2).Nonempty}
  let P : J → Set E := fun p => convexHull ℝ (p.1.1.1 : Set E) ∩ signCell g p.1.2
  have hPv : ∀ p, Convex ℝ (P p) := fun p => (convex_convexHull ℝ _).inter convex_signCell
  have hPc : ∀ p, IsCompact (P p) := fun p =>
    (p.1.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).inter_right isClosed_signCell
  have hri : ∀ p, intrinsicInterior ℝ (P p) =
      intrinsicInterior ℝ (convexHull ℝ (p.1.1.1 : Set E)) ∩ openSignCell g p.1.2 := fun p => by
    obtain ⟨x, hxσ, hxτ⟩ := p.2
    have hτ := intrinsicInterior_signCell ⟨x, hxτ⟩
    rw [TauCeti.intrinsicInterior_inter (convex_convexHull ℝ _) convex_signCell
      (hτ ▸ ⟨x, hxσ, hxτ⟩), hτ]
  -- A point of a cell lies in the intrinsic interior of a cell contained in it: the cell of its
  -- carrier simplex and of its own sign vector.
  have hcell : ∀ ⦃x : E⦄ ⦃σ : Finset E⦄ (hσ : σ ∈ K.faces) ⦃τ : ι → SignType⦄,
      x ∈ convexHull ℝ (σ : Set E) → x ∈ signCell g τ →
      ∃ q : J, x ∈ intrinsicInterior ℝ (P q) ∧
        P q ⊆ convexHull ℝ (σ : Set E) ∩ signCell g τ := by
    intro x σ hσ τ hxσ hxτ
    obtain ⟨σ', hσ', hσσ', hxσ'⟩ := exists_mem_faces_subset_mem_intrinsicInterior hσ hxσ
    let q : J := ⟨(⟨σ', hσ'⟩, fun i => SignType.sign (g i x)), x, hxσ',
      mem_openSignCell_sign g x⟩
    exact ⟨q, (hri q).symm ▸ ⟨hxσ', mem_openSignCell_sign g x⟩, inter_subset_inter
      (convexHull_mono (Finset.coe_subset.2 hσσ')) (signCell_sign_subset hxτ)⟩
  have hPne : ∀ p, (P p).Nonempty := fun p => p.2.mono
    (inter_subset_inter intrinsicInterior_subset openSignCell_subset_signCell)
  have hdisj : Pairwise fun p q : J => Disjoint (intrinsicInterior ℝ (P p))
      (intrinsicInterior ℝ (P q)) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun x hxp hxq => hpq ?_
    rw [hri] at hxp hxq
    refine Subtype.ext (Prod.ext
      (Subtype.ext (eq_of_mem_intrinsicInterior p.1.1.2 q.1.1.2 hxp.1 hxq.1)) ?_)
    funext i
    exact (hxp.2 i).symm.trans (hxq.2 i)
  have hfr : ∀ p, intrinsicFrontier ℝ (P p) ⊆ ⋃ (q) (_ : q ≠ p ∧ P q ⊆ P p), P q := by
    intro p x hx
    have hxP := intrinsicFrontier_subset (hPc p).isClosed hx
    obtain ⟨q, hxq, hqp⟩ := hcell p.1.1.2 hxP.1 hxP.2
    have hxi : x ∉ intrinsicInterior ℝ (P p) := by
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hx
      exact hx.2
    exact mem_iUnion₂.2 ⟨q, ⟨fun hqp' => hxi (hqp' ▸ hxq), hqp⟩, intrinsicInterior_subset hxq⟩
  obtain ⟨M, hMs, hMP, hMface, -⟩ := exists_subdivision P hPc hPv hPne
    (locallyFinite_of_finite P) hdisj hfr
  have hspace : M.space = K.space := by
    rw [hMs]
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨p, hxp⟩ := mem_iUnion.1 hx
      exact mem_space_iff.2 ⟨_, p.1.1.2, hxp.1⟩
    · obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.1 hx
      obtain ⟨q, hxq, -⟩ := hcell hσ hxσ (openSignCell_subset_signCell (mem_openSignCell_sign g x))
      exact mem_iUnion.2 ⟨q, intrinsicInterior_subset hxq⟩
  have hconv : ∀ s ∈ M.faces, ∃ p : J, convexHull ℝ (s : Set E) ⊆ P p := fun s hs => by
    obtain ⟨p, hsp⟩ := hMface s hs
    exact ⟨p, convexHull_min hsp (hPv p)⟩
  refine ⟨M, ⟨hspace, fun s hs => ?_⟩, ?_, fun s hs i => ?_⟩
  · obtain ⟨p, hp⟩ := hconv s hs
    exact ⟨_, p.1.1.2, hp.trans inter_subset_left⟩
  · refine (Set.finite_iUnion fun p => (hMP p).2).subset fun s hs => ?_
    obtain ⟨p, hsp⟩ := hMface s hs
    exact mem_iUnion.2 ⟨p, mem_restrict_faces.2 ⟨hs, hsp⟩⟩
  · obtain ⟨p, hp⟩ := hconv s hs
    exact nonneg_or_nonpos_of_subset_signCell (hp.trans inter_subset_right) i

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
