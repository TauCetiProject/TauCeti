/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Convex.Gauge

/-!
# Intrinsic interior points of compact and convex sets

Follow the ray from a point `p` of a compact set `C` through another point `x` of `C`. The last
point of `C` on this ray lies in the intrinsic frontier of `C`
(`IsCompact.exists_lineMap_mem_intrinsicFrontier`): beyond it the ray leaves `C`, so it cannot be
an intrinsic interior point. No convexity is needed.

A nonempty convex subset of `t` whose intrinsic interior misses that of `t`, such as a convex piece
of the intrinsic frontier of `t`, has strictly smaller dimension
(`TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior`): equal dimensions would force
equal affine spans, and the intrinsic interior is monotone on sets with a common affine span
(`TauCeti.intrinsicInterior_mono_of_affineSpan_eq`). Consequently, in a family of convex
cells with pairwise disjoint intrinsic interiors whose intrinsic frontiers are covered by a set
`S` and the smaller cells, every point of a cell lies in `S` or in the intrinsic interior of a
cell contained in it (`TauCeti.mem_intrinsicInterior_or_of_mem`), and the intrinsic interior of a
cell avoiding `S` meets no other cell of smaller or equal dimension
(`TauCeti.eq_or_finrank_lt_of_mem_intrinsicInterior`).

If `s` has the same affine span as `t` and contains the part of `t` in an open set `U`, then the
intrinsic interior points of `t` in `U` are intrinsic interior points of `s`
(`TauCeti.intrinsicInterior_inter_subset_of_affineSpan_eq`). From an intrinsic interior point,
every small move along the affine span stays in the set
(`TauCeti.eventually_add_smul_mem_of_mem_intrinsicInterior`). Consequently an affine function
which is nonnegative on a set and vanishes at one of its intrinsic interior points vanishes on the
whole set (`TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior`). In particular, an inequality
`a ≤ b` between affine functions on `s`, which persists on the convex hull of `s`
(`TauCeti.le_of_forall_le_of_mem_convexHull`), is strict on the intrinsic interior of that hull
unless `a = b` on all of it (`TauCeti.eq_of_le_of_mem_intrinsicInterior`). The intrinsic
frontier of a closed set consists of its points outside its intrinsic interior
(`IsClosed.sdiff_intrinsicInterior`). These are the tools for computing intrinsic interiors and
frontiers of concrete cells, such as the bands of `TauCeti/Analysis/Convex/RegionBetween.lean`,
and the cells of a hyperplane arrangement.

Read in the ambient space, `x` is an intrinsic interior point of `s` when it lies in the affine
span of `s` and the points of that span near `x` lie in `s`
(`TauCeti.mem_intrinsicInterior_iff_eventually`). A subset `u` of a convex set `s` which meets the
intrinsic interior of `s` has its intrinsic interior inside that of `s`
(`TauCeti.intrinsicInterior_mono_of_inter_intrinsicInterior_nonempty`). Consequently, if the
intrinsic interiors of two convex sets meet, the intrinsic interior of their intersection is the
intersection of their intrinsic interiors (`TauCeti.intrinsicInterior_inter`; Rockafellar,
*Convex Analysis*, Theorem 6.5). This computes the intrinsic interiors of the cells `σ ∩ τ` cut
out by two triangulations.

A closed bounded convex set `C` of a real normed space, with a point `c` of its intrinsic
interior, is homeomorphic to the closed unit ball of the direction `V` of its affine span
(`TauCeti.convexClosedBallHomeomorph`). Translating by `-c` turns `C` into a closed bounded convex
neighbourhood `S` of `0` in `V`, and Mathlib's `gaugeRescaleHomeomorph` rescales each ray of `V`
through the origin to carry the closed unit ball onto `S`. Explicitly, the homeomorphism sends `v`
to `c + (‖v‖ / gauge (-c +ᵥ C) v) • v` (`TauCeti.coe_convexClosedBallHomeomorph_apply`); for a
unit vector `u` of `V` the number `(gauge (-c +ᵥ C) u)⁻¹` is the length of the segment from `c` in
direction `u` inside `C`. No finite-dimensionality is needed. This identifies every nonempty
compact convex set of a finite-dimensional space with a disk, which is how Brouwer's fixed-point
theorem passes from the disk to compact convex sets.
-/

public section

open Set

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] {C : Set E} {p x : E}

/-- On the ray from a point `p` of a compact set `C` through another point `x` of `C`, some point
at parameter `T ≥ 1` lies in the intrinsic frontier of `C`. -/
theorem IsCompact.exists_lineMap_mem_intrinsicFrontier (hC : IsCompact C) (hp : p ∈ C)
    (hx : x ∈ C) (hxp : x ≠ p) :
    ∃ T : ℝ, 1 ≤ T ∧ AffineMap.lineMap p x T ∈ intrinsicFrontier ℝ C := by
  -- the last parameter `T` at which the ray `f` is still in `C`
  set f : ℝ → E := ⇑(AffineMap.lineMap (k := ℝ) p x)
  have hf : Topology.IsClosedEmbedding f := by
    have : f = (· + p) ∘ fun t : ℝ => t • (x - p) := by
      ext t
      simp [f, AffineMap.lineMap_apply]
    rw [this]
    exact (Homeomorph.addRight p).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (sub_ne_zero.2 hxp))
  have hf1 : (1 : ℝ) ∈ f ⁻¹' C ∩ Ici 0 := ⟨by simpa [f] using hx, zero_le_one⟩
  obtain ⟨T, ⟨hTC, hT0⟩, hTmax⟩ :=
    ((hf.isCompact_preimage hC).inter_right isClosed_Ici).exists_isGreatest ⟨1, hf1⟩
  refine ⟨T, hTmax hf1, ?_⟩
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  refine ⟨subset_intrinsicClosure hTC, fun hTi => ?_⟩
  -- an intrinsic interior point would let the ray stay in `C` slightly past `T`
  obtain ⟨z, hz, hzT⟩ := mem_intrinsicInterior.1 hTi
  let g : ℝ → affineSpan ℝ C := fun t => ⟨f t, AffineMap.lineMap_mem t
    (subset_affineSpan ℝ C hp) (subset_affineSpan ℝ C hx)⟩
  have hg : ∀ t, (g t : E) = f t := fun _ => rfl
  have hgT : g T = z := Subtype.ext ((hg T).trans hzT.symm)
  have hgTi : g T ∈ interior ((↑) ⁻¹' C) := hgT ▸ hz
  have hnhds : g ⁻¹' interior ((↑) ⁻¹' C) ∈ nhds T :=
    (isOpen_interior.preimage (hf.continuous.subtype_mk _)).mem_nhds hgTi
  obtain ⟨u, hTu, hsub⟩ := exists_Ico_subset_of_mem_nhds hnhds ⟨T + 1, by linarith⟩
  have hmid : (T + u) / 2 ∈ Ico T u := ⟨by linarith, by linarith⟩
  have hgmid : g ((T + u) / 2) ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C)) :=
    interior_subset (hsub hmid)
  have hmemC : f ((T + u) / 2) ∈ C := by
    rw [← hg]
    exact mem_preimage.1 hgmid
  linarith [hTmax ⟨hmemC, mem_Ici.2 (by linarith [mem_Ici.1 hT0])⟩]

end Ray

namespace TauCeti

section AffineSpan

variable {𝕜 V P : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P]
  [AddTorsor V P] {s t : Set P}

/-- The intrinsic interior of the whole space is the whole space. -/
@[simp]
theorem intrinsicInterior_univ : intrinsicInterior 𝕜 (univ : Set P) = univ := by
  simp [intrinsicInterior]

/-- The intrinsic interior is monotone on sets with a common affine span. -/
theorem intrinsicInterior_mono_of_affineSpan_eq (hst : s ⊆ t)
    (h : affineSpan 𝕜 s = affineSpan 𝕜 t) : intrinsicInterior 𝕜 s ⊆ intrinsicInterior 𝕜 t := by
  rw [intrinsicInterior, intrinsicInterior, h]
  exact image_mono (interior_mono (preimage_mono hst))

/-- If `s` has the same affine span as `t` and contains the part `t ∩ U` of `t` in an open set
`U`, then the intrinsic interior points of `t` in `U` are intrinsic interior points of `s`. -/
theorem intrinsicInterior_inter_subset_of_affineSpan_eq {U : Set P} (hU : IsOpen U)
    (htU : t ∩ U ⊆ s) (h : affineSpan 𝕜 s = affineSpan 𝕜 t) :
    intrinsicInterior 𝕜 t ∩ U ⊆ intrinsicInterior 𝕜 s := by
  rintro _ ⟨⟨y, hy, rfl⟩, hyU⟩
  rw [intrinsicInterior, h]
  have hsub : interior ((↑) ⁻¹' t) ∩ (↑) ⁻¹' U ⊆ ((↑) ⁻¹' s : Set (affineSpan 𝕜 t)) :=
    fun z hz ↦ htU ⟨(interior_subset hz.1 : z ∈ (↑) ⁻¹' t), hz.2⟩
  exact ⟨y, interior_maximal hsub (isOpen_interior.inter (hU.preimage continuous_subtype_val))
    ⟨hy, hyU⟩, rfl⟩

/-- The intrinsic frontier of a closed set consists of its points outside its intrinsic
interior. -/
theorem _root_.IsClosed.sdiff_intrinsicInterior (hs : IsClosed s) :
    s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s := by
  rw [← intrinsicClosure_sdiff_intrinsicInterior,
    (hs.preimage continuous_subtype_val).intrinsicClosure]

/-- Membership in the intrinsic interior, read in the ambient space: `x` is an intrinsic interior
point of `s` when it lies in the affine span of `s` and every point of that span close to `x` lies
in `s`. -/
theorem mem_intrinsicInterior_iff_eventually {x : P} :
    x ∈ intrinsicInterior 𝕜 s ↔
      x ∈ affineSpan 𝕜 s ∧ ∀ᶠ y in nhds x, y ∈ affineSpan 𝕜 s → y ∈ s := by
  refine ⟨fun ⟨z, hz, hzx⟩ ↦ ?_, fun ⟨hx, h⟩ ↦ ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 (mem_interior_iff_mem_nhds.1 hz)
    exact hzx ▸ ⟨z.2, Filter.mem_of_superset hu fun y hy hyA ↦ hus (a := ⟨y, hyA⟩) hy⟩
  · exact mem_interior_iff_mem_nhds.2 ((mem_nhds_subtype _ _ _).2 ⟨_, h, fun y hy ↦ hy y.2⟩)

/-- A point in the intrinsic interiors of two sets is in the intrinsic interior of their
intersection. -/
theorem intrinsicInterior_inter_intrinsicInterior_subset :
    intrinsicInterior 𝕜 s ∩ intrinsicInterior 𝕜 t ⊆ intrinsicInterior 𝕜 (s ∩ t) := by
  rintro x ⟨hxs, hxt⟩
  have hx : x ∈ s ∩ t := ⟨intrinsicInterior_subset hxs, intrinsicInterior_subset hxt⟩
  rw [mem_intrinsicInterior_iff_eventually] at hxs hxt ⊢
  refine ⟨subset_affineSpan 𝕜 _ hx, ?_⟩
  filter_upwards [hxs.2, hxt.2] with y hys hyt hy
  exact ⟨hys (affineSpan_mono 𝕜 inter_subset_left hy),
    hyt (affineSpan_mono 𝕜 inter_subset_right hy)⟩

/-- The intrinsic frontier of a closed cell is covered by the other cells contained in it, when
every point of the cell lies in the intrinsic interior of a cell contained in it. -/
theorem intrinsicFrontier_subset_iUnion_of_exists_mem_intrinsicInterior {ι : Type*}
    {Q : ι → Set P} (i : ι) (hQc : IsClosed (Q i))
    (h : ∀ x ∈ Q i, ∃ j, x ∈ intrinsicInterior 𝕜 (Q j) ∧ Q j ⊆ Q i) :
    intrinsicFrontier 𝕜 (Q i) ⊆ ⋃ (j) (_ : j ≠ i ∧ Q j ⊆ Q i), Q j := by
  intro x hx
  obtain ⟨j, hxj, hji⟩ := h x (intrinsicFrontier_subset hQc hx)
  have hxi : x ∉ intrinsicInterior 𝕜 (Q i) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hx
    exact hx.2
  exact mem_iUnion₂.2 ⟨j, ⟨fun hji' => hxi (hji' ▸ hxj), hji⟩, intrinsicInterior_subset hxj⟩

end AffineSpan

section Frontier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C S : Set E}

/-- A point of `C` lying in a set `S` which the intrinsic interior of `C` avoids lies in the
intrinsic frontier of `C`. -/
theorem inter_subset_intrinsicFrontier_of_disjoint
    (hint : Disjoint (intrinsicInterior ℝ C) S) : C ∩ S ⊆ intrinsicFrontier ℝ C :=
  fun x ⟨hxC, hxS⟩ => by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hxC, fun hxi => Set.disjoint_left.1 hint hxi hxS⟩

end Frontier

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s t : Set E}

/-- A nonempty convex subset `s` of `t` whose intrinsic interior is disjoint from that of `t`
(for instance a nonempty convex subset of the intrinsic frontier of `t`) has strictly smaller
dimension than `t`. -/
theorem finrank_vectorSpan_lt_of_disjoint_intrinsicInterior (hs : Convex ℝ s) (hsne : s.Nonempty)
    (hst : s ⊆ t) (hd : Disjoint (intrinsicInterior ℝ s) (intrinsicInterior ℝ t)) :
    Module.finrank ℝ (vectorSpan ℝ s) < Module.finrank ℝ (vectorSpan ℝ t) := by
  refine (Submodule.finrank_mono (vectorSpan_mono ℝ hst)).lt_of_ne fun h => ?_
  -- equal dimensions force equal affine spans, so the intrinsic interior of `s` lies in that of `t`
  have hspan : affineSpan ℝ s = affineSpan ℝ t := by
    refine AffineSubspace.ext_of_direction_eq ?_ ?_
    · rw [direction_affineSpan, direction_affineSpan]
      exact Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hst) h
    · obtain ⟨x, hx⟩ := hsne
      exact ⟨x, subset_affineSpan ℝ s hx, subset_affineSpan ℝ t (hst hx)⟩
  obtain ⟨x, hx⟩ := hsne.intrinsicInterior hs
  exact Set.disjoint_left.1 hd hx (intrinsicInterior_mono_of_affineSpan_eq hst hspan hx)

section Cells

variable {ι : Type*} {P : ι → Set E} {S : Set E}

/-- A point of a cell lies in its intrinsic interior, in `S`, or in the intrinsic interior of a
smaller-dimensional cell contained in it, when the frontier of every cell is covered by `S` and
the other cells contained in it. -/
theorem mem_intrinsicInterior_or_of_mem (hPv : ∀ i, Convex ℝ (P i))
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ S ∪ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j)
    {i : ι} {x : E} (hx : x ∈ P i) :
    x ∈ intrinsicInterior ℝ (P i) ∨ x ∈ S ∨ ∃ k, Module.finrank ℝ (vectorSpan ℝ (P k)) <
      Module.finrank ℝ (vectorSpan ℝ (P i)) ∧ P k ⊆ P i ∧ x ∈ intrinsicInterior ℝ (P k) := by
  induction hn : Module.finrank ℝ (vectorSpan ℝ (P i)) using Nat.strong_induction_on
    generalizing i with
  | _ n ih =>
  by_cases hxi : x ∈ intrinsicInterior ℝ (P i)
  · exact .inl hxi
  have hxf : x ∈ intrinsicFrontier ℝ (P i) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hx, hxi⟩
  rcases hfr i hxf with hxS | hx'
  · exact .inr (.inl hxS)
  simp only [mem_iUnion, exists_prop] at hx'
  obtain ⟨j, ⟨hji, hjP⟩, hxj⟩ := hx'
  -- the cell `P j` lies in the frontier of `P i`, so it has smaller dimension
  have hj : _ < n :=
    hn ▸ finrank_vectorSpan_lt_of_disjoint_intrinsicInterior (hPv j) ⟨x, hxj⟩ hjP (hri hji)
  rcases ih _ hj hxj rfl with h | h | ⟨k, hk, hkj, hxk⟩
  · exact .inr (.inr ⟨j, hj, hjP, h⟩)
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨k, hk.trans hj, hkj.trans hjP, hxk⟩)

/-- Under the hypotheses of `TauCeti.mem_intrinsicInterior_or_of_mem`, if the intrinsic
interiors of the cells avoid `S`, the intrinsic interior of a cell meets no other cell of smaller
or equal dimension. -/
theorem eq_or_finrank_lt_of_mem_intrinsicInterior (hPv : ∀ i, Convex ℝ (P i))
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ S ∪ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j)
    (hS : ∀ i, Disjoint (intrinsicInterior ℝ (P i)) S) {i j : ι} {x : E}
    (hxi : x ∈ intrinsicInterior ℝ (P i)) (hxj : x ∈ P j) :
    i = j ∨ Module.finrank ℝ (vectorSpan ℝ (P i)) < Module.finrank ℝ (vectorSpan ℝ (P j)) := by
  rcases mem_intrinsicInterior_or_of_mem hPv hri hfr hxj with h | h | ⟨k, hk, -, hxk⟩
  · by_contra hij
    exact Set.disjoint_left.1 (hri fun h => hij (.inl h)) hxi h
  · exact (Set.disjoint_left.1 (hS i) hxi h).elim
  · rcases eq_or_ne i k with rfl | hik
    · exact .inr hk
    · exact (Set.disjoint_left.1 (hri hik) hxi hxk).elim

end Cells

end FiniteDimensional

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An inequality between two affine functions on a set persists on its convex hull. -/
theorem le_of_forall_le_of_mem_convexHull {a b : E →ᵃ[ℝ] ℝ} {s : Set E}
    (h : ∀ x ∈ s, a x ≤ b x) {x : E} (hx : x ∈ convexHull ℝ s) : a x ≤ b x := by
  have hc : Convex ℝ {y | a y ≤ b y} := by
    convert (convex_Ici (0 : ℝ)).affine_preimage (b - a) using 1
    ext y
    simp [sub_nonneg]
  exact convexHull_min (fun y hy ↦ h y hy) hc hx

end Convex

open Bornology Metric Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {c : E}

/-! ### A closed bounded convex set as a ball around an intrinsic interior point -/

variable (C c) in
/-- The displacements from `c` inside `C`, read in the direction of the affine span of `C`, are
the preimage of the translate `-c +ᵥ C`. -/
lemma setOf_add_mem_eq_preimage :
    {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} =
      (affineSpan ℝ C).direction.subtype ⁻¹' ((-c) +ᵥ C) := by
  ext v
  simp [mem_vadd_set_iff_neg_vadd_mem]

/-- The gauge of the displacement set agrees with the gauge of the translated set in the
ambient space. -/
lemma gauge_setOf_add_mem (v : (affineSpan ℝ C).direction) :
    gauge {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} v =
      gauge ((-c) +ᵥ C) (v : E) := by
  rw [setOf_add_mem_eq_preimage]
  exact LinearMap.gauge_preimage _ _ _

/-- For convex `C` and any `c`, the displacements `v` in the direction of `affineSpan ℝ C`
with `c + v ∈ C` form a convex set. -/
lemma convex_setOf_add_mem (hconv : Convex ℝ C) :
    Convex ℝ {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} := by
  rw [setOf_add_mem_eq_preimage]
  exact (hconv.vadd (-c)).linear_preimage _

/-- Displacements from a point into a closed set form a closed set in its affine direction. -/
lemma isClosed_setOf_add_mem (hcl : IsClosed C) :
    IsClosed {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} :=
  hcl.preimage (f := fun v : (affineSpan ℝ C).direction ↦ c + (v : E)) (by fun_prop)

/-- Displacements into a bounded set are von Neumann bounded in its affine direction. -/
lemma isVonNBounded_setOf_add_mem (hb : IsBounded C) :
    IsVonNBounded ℝ {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} := by
  refine NormedSpace.isVonNBounded_of_isBounded ℝ ?_
  obtain ⟨r, hr⟩ := hb.subset_closedBall c
  refine (isBounded_closedBall (x := (0 : (affineSpan ℝ C).direction)) (r := r)).subset
    fun v hv ↦ ?_
  have hv' := hr hv
  rw [mem_closedBall, dist_self_add_left] at hv'
  rwa [mem_closedBall_zero_iff, ← Submodule.norm_coe]

/-- `c + v` lies in the intrinsic frontier of `C` iff `v` lies in the frontier, within the
direction of the affine span of `C`, of the displacement set `{w | c + w ∈ C}`. -/
lemma add_mem_intrinsicFrontier_iff (v : (affineSpan ℝ C).direction) :
    c + (v : E) ∈ intrinsicFrontier ℝ C ↔
      v ∈ frontier {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} := by
  by_cases hc : c ∈ affineSpan ℝ C
  swap
  · -- A displacement `w` in the direction with `c + w` in the span puts `c` in the span.
    have key (w : (affineSpan ℝ C).direction) (h : c + (w : E) ∈ affineSpan ℝ C) :
        c ∈ affineSpan ℝ C := by
      have := AffineSubspace.vadd_mem_of_mem_direction (neg_mem w.2) h
      rwa [vadd_eq_add, show -(w : E) + (c + w) = c by abel] at this
    have hempty : {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw ↦ hc (key w (subset_affineSpan ℝ C hw))
    rw [hempty, frontier_empty]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨y, -, hy⟩
    exact hc (key v (hy ▸ y.2))
  let cA : affineSpan ℝ C := ⟨c, hc⟩
  let : Nonempty (affineSpan ℝ C) := ⟨cA⟩
  let e := Homeomorph.vaddConst cA
  have he (w : (affineSpan ℝ C).direction) : (e w : E) = c + (w : E) := by
    simp [e, Homeomorph.vaddConst, cA, add_comm]
  rw [intrinsicFrontier, ← image_frontier_preimage_comp e e.isHomeomorph]
  simp only [Function.comp_def, he]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = v := Subtype.ext (add_left_cancel hwv)
    exact this ▸ hw
  · exact fun hv ↦ ⟨v, hv, rfl⟩

/-- For a point `c` of the intrinsic interior of `C`, the displacements `v` in the direction of
the affine span of `C` with `c + v ∈ C` form a neighbourhood of `0`. -/
theorem setOf_add_mem_mem_nhds_of_mem_intrinsicInterior (hc : c ∈ intrinsicInterior ℝ C) :
    {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} ∈ 𝓝 0 := by
  obtain ⟨y, hy, rfl⟩ := hc
  -- Translating the direction by `y` is a continuous map into the affine span sending `0` to `y`.
  let φ : (affineSpan ℝ C).direction → affineSpan ℝ C :=
    fun v ↦ ⟨(v : E) + y, by simpa using AffineSubspace.vadd_mem_of_mem_direction v.2 y.2⟩
  have hφ : Continuous φ := (by fun_prop : Continuous fun v : (affineSpan ℝ C).direction ↦
    (v : E) + y).subtype_mk _
  have hφ0 : φ 0 = y := Subtype.ext (zero_add _)
  refine Filter.mem_of_superset
    (hφ.continuousAt.preimage_mem_nhds (hφ0 ▸ isOpen_interior.mem_nhds hy)) fun v hv ↦ ?_
  simpa [φ, add_comm] using interior_subset hv

/-- The gauge of the translated set in its affine direction is positive exactly away from
zero, for a bounded set with an intrinsic interior center. -/
lemma gauge_setOf_add_mem_pos_iff (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C)
    (v : (affineSpan ℝ C).direction) :
    0 < gauge {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} v ↔ v ≠ 0 :=
  gauge_pos (absorbent_nhds_zero (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc))
    (isVonNBounded_setOf_add_mem hb)

/-- From a point `c` of the intrinsic interior of `C`, every sufficiently small move `ε • v` along
a direction `v` of the affine span of `C` stays in `C`. -/
theorem eventually_add_smul_mem_of_mem_intrinsicInterior (hc : c ∈ intrinsicInterior ℝ C)
    {v : E} (hv : v ∈ (affineSpan ℝ C).direction) : ∀ᶠ ε in 𝓝 (0 : ℝ), c + ε • v ∈ C := by
  have hcont : Continuous fun ε : ℝ ↦ (ε • ⟨v, hv⟩ : (affineSpan ℝ C).direction) := by fun_prop
  simpa using (hcont.tendsto' 0 0 (zero_smul ℝ _)).eventually
    (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc)

/-- An affine function which is nonnegative on a set `C` and vanishes at an intrinsic interior
point `c` of `C` vanishes on all of `C`. -/
theorem eq_zero_of_nonneg_of_mem_intrinsicInterior {g : E →ᵃ[ℝ] ℝ} (hg : ∀ y ∈ C, 0 ≤ g y)
    (hc : c ∈ intrinsicInterior ℝ C) (hgc : g c = 0) {y : E} (hy : y ∈ C) : g y = 0 := by
  -- Push `c` slightly away from `y` inside `C`; there `g` takes the value `-ε * g y`.
  have hv : c - y ∈ (affineSpan ℝ C).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ (intrinsicInterior_subset hc) hy
  obtain ⟨ε, hε, hεpos⟩ := (((eventually_add_smul_mem_of_mem_intrinsicInterior hc hv).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 0))).exists
  have hgε : g (c + ε • (c - y)) = g c + ε * (g c - g y) := by
    rw [add_comm c, ← vadd_eq_add, AffineMap.map_vadd, map_smul, ← vsub_eq_sub,
      AffineMap.linear_apply_vsub, vadd_eq_add, smul_eq_mul, vsub_eq_sub, add_comm]
  have h := hg _ hε
  rw [hgε, hgc] at h
  nlinarith [hg y hy, mem_Ioi.1 hεpos]

/-- If `a ≤ b` on `s` for two affine functions, with equality at an intrinsic interior point of
the convex hull of `s`, then `a = b` on the whole convex hull. -/
theorem eq_of_le_of_mem_intrinsicInterior {a b : E →ᵃ[ℝ] ℝ} {s : Set E}
    (h : ∀ x ∈ s, a x ≤ b x) {x y : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ s))
    (hxe : a x = b x) (hy : y ∈ convexHull ℝ s) : a y = b y := by
  have := eq_zero_of_nonneg_of_mem_intrinsicInterior (g := b - a)
    (fun z hz ↦ by simpa [sub_nonneg] using le_of_forall_le_of_mem_convexHull h hz) hx
    (by simp [hxe]) hy
  rw [AffineMap.coe_sub, Pi.sub_apply, sub_eq_zero] at this
  exact this.symm

/-- A subset `u` of a convex set `s` meeting the intrinsic interior of `s` has its intrinsic
interior inside that of `s`. -/
theorem intrinsicInterior_mono_of_inter_intrinsicInterior_nonempty {s u : Set E}
    (hs : Convex ℝ s) (hus : u ⊆ s) (h : (u ∩ intrinsicInterior ℝ s).Nonempty) :
    intrinsicInterior ℝ u ⊆ intrinsicInterior ℝ s := by
  intro y hy
  obtain ⟨z, hzu, hzs⟩ := h
  -- Push `y` slightly away from `z` inside `u`; then `y` lies strictly between `z` and that point.
  have hv : y - z ∈ (affineSpan ℝ u).direction := by
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ (intrinsicInterior_subset hy) hzu
  obtain ⟨ε, hε, hεpos⟩ := (((eventually_add_smul_mem_of_mem_intrinsicInterior hy hv).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 0))).exists
  replace hεpos : 0 < ε := mem_Ioi.1 hεpos
  refine hs.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hzs
    (subset_intrinsicClosure (hus hε)) ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity,
      by field_simp; ring, ?_⟩
  match_scalars
  · field_simp
    ring
  · field_simp

/-- **The intrinsic interior of an intersection** (Rockafellar, Theorem 6.5). If the intrinsic
interiors of two convex sets meet, the intrinsic interior of their intersection is the
intersection of their intrinsic interiors. -/
theorem intrinsicInterior_inter {s t : Set E} (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h : (intrinsicInterior ℝ s ∩ intrinsicInterior ℝ t).Nonempty) :
    intrinsicInterior ℝ (s ∩ t) = intrinsicInterior ℝ s ∩ intrinsicInterior ℝ t := by
  obtain ⟨z, hzs, hzt⟩ := h
  have hz : z ∈ s ∩ t := ⟨intrinsicInterior_subset hzs, intrinsicInterior_subset hzt⟩
  exact (subset_inter
    (intrinsicInterior_mono_of_inter_intrinsicInterior_nonempty hs inter_subset_left ⟨z, hz, hzs⟩)
    (intrinsicInterior_mono_of_inter_intrinsicInterior_nonempty ht inter_subset_right
      ⟨z, hz, hzt⟩)).antisymm intrinsicInterior_inter_intrinsicInterior_subset

/-- **A closed bounded convex set is a ball around each intrinsic interior point.** For a closed
bounded convex set `C` of a real normed space and a point `c` of its intrinsic interior, the closed
unit ball of the direction of the affine span of `C` is homeomorphic to `C`. The homeomorphism
sends `0` to `c` and `v` to `c + (‖v‖ / gauge (-c +ᵥ C) v) • v`
(`TauCeti.coe_convexClosedBallHomeomorph_apply`): it rescales the ray through `v` by Mathlib's
`gaugeRescaleHomeomorph`, then translates by `c`. -/
noncomputable def convexClosedBallHomeomorph (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) :
    closedBall (0 : (affineSpan ℝ C).direction) 1 ≃ₜ C :=
  let V := (affineSpan ℝ C).direction
  let S : Set V := {v | c + (v : E) ∈ C}
  have hcspan : c ∈ affineSpan ℝ C := subset_affineSpan ℝ C (intrinsicInterior_subset hc)
  -- The gauge rescaling carries the closed unit ball of `V` onto the closed set `S`.
  have hg := image_gaugeRescaleHomeomorph_closure (convex_closedBall (0 : V) 1)
    (closedBall_mem_nhds 0 one_pos) (NormedSpace.isVonNBounded_closedBall ℝ V 1)
    (convex_setOf_add_mem hconv) (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc)
    (isVonNBounded_setOf_add_mem hb)
  have hgS : _ '' closedBall (0 : V) 1 = S := by
    rwa [closure_closedBall, (isClosed_setOf_add_mem hcl).closure_eq] at hg
  ((Homeomorph.image _ _).trans (Homeomorph.setCongr hgS)).trans
    { toFun v := ⟨c + (v : V), v.2⟩
      invFun x := ⟨⟨(x : E) - c, by
        simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C x.2) hcspan⟩,
        by simp [S]⟩
      left_inv v := by ext; simp
      right_inv x := by ext; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The convex-ball homeomorphism is gauge rescaling followed by translation by `c`. -/
theorem coe_convexClosedBallHomeomorph_apply_eq_gaugeRescale (hconv : Convex ℝ C)
    (hcl : IsClosed C) (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C)
    (v : closedBall (0 : (affineSpan ℝ C).direction) 1) :
    (convexClosedBallHomeomorph hconv hcl hb hc v : E) =
      c + ((gaugeRescale (closedBall 0 1)
        {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} v :
          (affineSpan ℝ C).direction) : E) := (rfl)

/-- `TauCeti.convexClosedBallHomeomorph` in explicit coordinates: `v` is sent to
`c + (‖v‖ / gauge (-c +ᵥ C) v) • v`. -/
theorem coe_convexClosedBallHomeomorph_apply (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C)
    (v : closedBall (0 : (affineSpan ℝ C).direction) 1) :
    (convexClosedBallHomeomorph hconv hcl hb hc v : E) =
      c + (‖(v : E)‖ / gauge ((-c) +ᵥ C) (v : E)) • (v : E) := by
  rw [coe_convexClosedBallHomeomorph_apply_eq_gaugeRescale,
    gaugeRescale_def, gauge_closedBall zero_le_one, gauge_setOf_add_mem, div_one,
    Submodule.coe_smul, ← Submodule.norm_coe]

/-- `TauCeti.convexClosedBallHomeomorph` sends the centre of the ball to `c`. -/
@[simp]
theorem coe_convexClosedBallHomeomorph_zero (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) :
    (convexClosedBallHomeomorph hconv hcl hb hc ⟨0, mem_closedBall_self zero_le_one⟩ : E) = c := by
  simp [coe_convexClosedBallHomeomorph_apply]

/-- The inverse convex-ball homeomorphism translates by `-c`, then rescales by the gauge. -/
theorem coe_convexClosedBallHomeomorph_symm_apply_eq_gaugeRescale (hconv : Convex ℝ C)
    (hcl : IsClosed C) (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) (x : C) :
    (((convexClosedBallHomeomorph hconv hcl hb hc).symm x : (affineSpan ℝ C).direction) : E) =
      ((gaugeRescale {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} (closedBall 0 1)
        ⟨(x : E) - c, by
          simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C x.2)
            (subset_affineSpan ℝ C (intrinsicInterior_subset hc))⟩ :
              (affineSpan ℝ C).direction) : E) := (rfl)

/-- The inverse of `TauCeti.convexClosedBallHomeomorph` in explicit coordinates: `x` is sent to
`(gauge (-c +ᵥ C) (x - c) / ‖x - c‖) • (x - c)`. -/
theorem coe_convexClosedBallHomeomorph_symm_apply (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) (x : C) :
    (((convexClosedBallHomeomorph hconv hcl hb hc).symm x : (affineSpan ℝ C).direction) : E) =
      (gauge ((-c) +ᵥ C) ((x : E) - c) / ‖(x : E) - c‖) • ((x : E) - c) := by
  rw [coe_convexClosedBallHomeomorph_symm_apply_eq_gaugeRescale,
    gaugeRescale_def, gauge_closedBall zero_le_one, gauge_setOf_add_mem, div_one,
    Submodule.coe_smul, ← Submodule.norm_coe]

/-- The unit sphere corresponds exactly to the intrinsic frontier under the convex-ball
homeomorphism. No full-dimensionality assumption is needed. Use this as an explicit rewrite;
the native simp normal form expands membership in the intrinsic frontier. -/
theorem coe_convexClosedBallHomeomorph_mem_intrinsicFrontier_iff (hconv : Convex ℝ C)
    (hcl : IsClosed C) (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C)
    (v : closedBall (0 : (affineSpan ℝ C).direction) 1) :
    (convexClosedBallHomeomorph hconv hcl hb hc v : E) ∈ intrinsicFrontier ℝ C ↔
      ‖v.1‖ = 1 := by
  rw [coe_convexClosedBallHomeomorph_apply_eq_gaugeRescale,
    add_mem_intrinsicFrontier_iff,
    ← gauge_eq_one_iff_mem_frontier (convex_setOf_add_mem hconv)
      (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc),
    gauge_gaugeRescale _
      (absorbent_nhds_zero (setOf_add_mem_mem_nhds_of_mem_intrinsicInterior hc))
      (isVonNBounded_setOf_add_mem hb), gauge_closedBall zero_le_one, div_one]

end TauCeti
