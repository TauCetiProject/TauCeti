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
(`TauCeti.intrinsicInterior_mono_of_affineSpan_eq`). Consequently, in a family of nonempty convex
cells with pairwise disjoint intrinsic interiors whose intrinsic frontiers are covered by a set
`S` and the smaller cells, every point of a cell lies in `S` or in the intrinsic interior of a
cell contained in it (`TauCeti.mem_intrinsicInterior_or_of_mem`), and the intrinsic interior of a
cell avoiding `S` meets no other cell of smaller or equal dimension
(`TauCeti.eq_or_finrank_lt_of_mem_intrinsicInterior`).

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

/-- The intrinsic interior is monotone on sets with a common affine span. -/
theorem intrinsicInterior_mono_of_affineSpan_eq (hst : s ⊆ t)
    (h : affineSpan 𝕜 s = affineSpan 𝕜 t) : intrinsicInterior 𝕜 s ⊆ intrinsicInterior 𝕜 t := by
  rw [intrinsicInterior, intrinsicInterior, h]
  exact image_mono (interior_mono (preimage_mono hst))

end AffineSpan

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
    (hPne : ∀ i, (P i).Nonempty)
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
    hn ▸ finrank_vectorSpan_lt_of_disjoint_intrinsicInterior (hPv j) (hPne j) hjP (hri hji)
  rcases ih _ hj hxj rfl with h | h | ⟨k, hk, hkj, hxk⟩
  · exact .inr (.inr ⟨j, hj, hjP, h⟩)
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨k, hk.trans hj, hkj.trans hjP, hxk⟩)

/-- Under the hypotheses of `TauCeti.mem_intrinsicInterior_or_of_mem`, if the intrinsic
interiors of the cells avoid `S`, the intrinsic interior of a cell meets no other cell of smaller
or equal dimension. -/
theorem eq_or_finrank_lt_of_mem_intrinsicInterior (hPv : ∀ i, Convex ℝ (P i))
    (hPne : ∀ i, (P i).Nonempty)
    (hri : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (P i)) (intrinsicInterior ℝ (P j)))
    (hfr : ∀ i, intrinsicFrontier ℝ (P i) ⊆ S ∪ ⋃ (j) (_ : j ≠ i ∧ P j ⊆ P i), P j)
    (hS : ∀ i, Disjoint (intrinsicInterior ℝ (P i)) S) {i j : ι} {x : E}
    (hxi : x ∈ intrinsicInterior ℝ (P i)) (hxj : x ∈ P j) :
    i = j ∨ Module.finrank ℝ (vectorSpan ℝ (P i)) < Module.finrank ℝ (vectorSpan ℝ (P j)) := by
  rcases mem_intrinsicInterior_or_of_mem hPv hPne hri hfr hxj with h | h | ⟨k, hk, -, hxk⟩
  · by_contra hij
    exact Set.disjoint_left.1 (hri fun h => hij (.inl h)) hxi h
  · exact (Set.disjoint_left.1 (hS i) hxi h).elim
  · rcases eq_or_ne i k with rfl | hik
    · exact .inr hk
    · exact (Set.disjoint_left.1 (hri hik) hxi hxk).elim

end Cells

end FiniteDimensional


open Bornology Metric Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {c : E}

/-! ### A closed bounded convex set as a ball around an intrinsic interior point -/

variable (C c) in
/-- The displacements from `c` inside `C`, read in the direction of the affine span of `C`, are
the preimage of the translate `-c +ᵥ C`. -/
private lemma setOf_add_mem_eq_preimage :
    {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} =
      (affineSpan ℝ C).direction.subtype ⁻¹' ((-c) +ᵥ C) := by
  ext v
  simp [mem_vadd_set_iff_neg_vadd_mem]

private lemma convex_setOf_add_mem (hconv : Convex ℝ C) :
    Convex ℝ {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} := by
  rw [setOf_add_mem_eq_preimage]
  exact (hconv.vadd (-c)).linear_preimage _

private lemma isClosed_setOf_add_mem (hcl : IsClosed C) :
    IsClosed {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} :=
  hcl.preimage (f := fun v : (affineSpan ℝ C).direction ↦ c + (v : E)) (by fun_prop)

private lemma isVonNBounded_setOf_add_mem (hb : IsBounded C) :
    IsVonNBounded ℝ {v : (affineSpan ℝ C).direction | c + (v : E) ∈ C} := by
  refine NormedSpace.isVonNBounded_of_isBounded ℝ ?_
  obtain ⟨r, hr⟩ := hb.subset_closedBall c
  refine (isBounded_closedBall (x := (0 : (affineSpan ℝ C).direction)) (r := r)).subset
    fun v hv ↦ ?_
  have hv' := hr hv
  rw [mem_closedBall, dist_self_add_left] at hv'
  rwa [mem_closedBall_zero_iff, ← Submodule.norm_coe]

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

/-- `TauCeti.convexClosedBallHomeomorph` in explicit coordinates: `v` is sent to
`c + (‖v‖ / gauge (-c +ᵥ C) v) • v`. -/
theorem coe_convexClosedBallHomeomorph_apply (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C)
    (v : closedBall (0 : (affineSpan ℝ C).direction) 1) :
    (convexClosedBallHomeomorph hconv hcl hb hc v : E) =
      c + (‖(v : E)‖ / gauge ((-c) +ᵥ C) (v : E)) • (v : E) := by
  have hS : gauge {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} v =
      gauge ((-c) +ᵥ C) (v : E) := by
    rw [setOf_add_mem_eq_preimage]
    exact LinearMap.gauge_preimage _ _ _
  -- By definition the homeomorphism is the gauge rescaling followed by translation by `c`.
  change c + ((gaugeRescale (closedBall 0 1) {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C}
    v : (affineSpan ℝ C).direction) : E) = _
  rw [gaugeRescale_def, gauge_closedBall zero_le_one, hS, div_one, Submodule.coe_smul,
    ← Submodule.norm_coe]

/-- `TauCeti.convexClosedBallHomeomorph` sends the centre of the ball to `c`. -/
@[simp]
theorem coe_convexClosedBallHomeomorph_zero (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) :
    (convexClosedBallHomeomorph hconv hcl hb hc ⟨0, mem_closedBall_self zero_le_one⟩ : E) = c := by
  simp [coe_convexClosedBallHomeomorph_apply]

/-- The inverse of `TauCeti.convexClosedBallHomeomorph` in explicit coordinates: `x` is sent to
`(gauge (-c +ᵥ C) (x - c) / ‖x - c‖) • (x - c)`. -/
theorem coe_convexClosedBallHomeomorph_symm_apply (hconv : Convex ℝ C) (hcl : IsClosed C)
    (hb : IsBounded C) (hc : c ∈ intrinsicInterior ℝ C) (x : C) :
    (((convexClosedBallHomeomorph hconv hcl hb hc).symm x : (affineSpan ℝ C).direction) : E) =
      (gauge ((-c) +ᵥ C) ((x : E) - c) / ‖(x : E) - c‖) • ((x : E) - c) := by
  set w : (affineSpan ℝ C).direction := ⟨(x : E) - c, by
    simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C x.2)
      (subset_affineSpan ℝ C (intrinsicInterior_subset hc))⟩
  have hS : gauge {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} w =
      gauge ((-c) +ᵥ C) ((x : E) - c) := by
    rw [setOf_add_mem_eq_preimage]
    exact LinearMap.gauge_preimage _ _ _
  -- By definition the inverse is translation by `-c` followed by the inverse gauge rescaling.
  change ((gaugeRescale {w : (affineSpan ℝ C).direction | c + (w : E) ∈ C} (closedBall 0 1)
    w : (affineSpan ℝ C).direction) : E) = _
  rw [gaugeRescale_def, gauge_closedBall zero_le_one, hS, div_one, Submodule.coe_smul,
    ← Submodule.norm_coe]

end TauCeti
