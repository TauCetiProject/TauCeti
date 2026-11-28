/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.LocallyFinite
public import TauCeti.GroupTheory.BruhatTits.AffineRoot
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Set.Finite.Lattice

/-!
# Local finiteness of Bruhat–Tits apartment walls

Using `AffineRoot.eval_def` and `Valuation.primedValueSet_subset_valueSet`, we show in
`AffineRoot.finite_wall_inter_of_bounded` that only finitely many walls meet a set on which
the finitely many root coordinates stay in bounded intervals. In particular
`AffineRoot.finite_wall_inter_segment` applies to every closed line segment, and
`AffineRoot.locallyFinite_wall` gives local finiteness when the root coordinates are continuous.
The latter allows Mathlib's `LocallyFinite.isClosed_iUnion` to be used for the wall arrangement.

See [Bruhat–Tits I], §1.3.2, p. 20 and §7.2.5, p. 162, for discrete wall arrangements
and their role in defining facets.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972).
-/

public section

open Set Topology

namespace TauCeti.BruhatTits.AffineRoot

variable {ι M N G : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [Group G] {P : RootPairing ι ℝ M N} {D : RootDatum P G} {φ : Valuation D}

section Finite

variable [Finite ι]

/-- When the negative root coordinates on a set stay in prescribed intervals, only affine
roots with constants in those intervals can have walls meeting the set. Finiteness of the
primed value sets in those intervals therefore gives finitely many such roots. -/
theorem finite_wall_inter_of_bounded {s : Set (Apartment φ)} {a b : ι → ℝ}
    (hfinite : ∀ i, (φ.primedValueSet i ∩ Icc (a i) (b i)).Finite)
    (hs : ∀ i x, x ∈ s → -P.root' i x.displacement ∈ Icc (a i) (b i)) :
    {α : AffineRoot φ | (α.wall ∩ s).Nonempty}.Finite := by
  refine Set.Finite.of_finite_fibers gradient (Set.toFinite _) (fun i _ ↦ ?_)
  refine Set.Finite.of_finite_image (f := constant) ((hfinite i).subset ?_) ?_
  · rintro k ⟨α, ⟨⟨x, hx, hxs⟩, hi⟩, rfl⟩
    have hg : α.gradient = i := hi
    have hk : α.constant = -P.root' i x.displacement := by
      have hzero := mem_wall_iff.mp hx
      rw [eval_def, hg] at hzero
      exact eq_neg_of_add_eq_zero_right hzero
    exact ⟨hg ▸ α.constant_mem, hk.symm ▸ hs i x hxs⟩
  · intro α hα β hβ heq
    have hαi : α.gradient = i := hα.2
    have hβi : β.gradient = i := hβ.2
    exact AffineRoot.ext (hαi.trans hβi.symm) heq

/-- A closed segment in an apartment of a discrete valuation meets only finitely many
affine-root walls, including when the segment is contained in a wall or is a singleton. -/
theorem finite_wall_inter_segment (hφ : φ.IsDiscrete) (x y : Apartment φ) :
    {α : AffineRoot φ | (α.wall ∩ AffineMap.lineMap x y '' Icc (0 : ℝ) 1).Nonempty}.Finite := by
  let c (i : ι) (z : Apartment φ) := -P.root' i z.displacement
  refine finite_wall_inter_of_bounded
    (a := fun i ↦ min (c i x) (c i y)) (b := fun i ↦ max (c i x) (c i y))
    (fun i ↦ ((φ.isDiscrete_iff.mp hφ) i _ _).subset
      (inter_subset_inter_left _ (φ.primedValueSet_subset_valueSet i)))
    ?_
  rintro i _ ⟨t, ht, rfl⟩
  have hline : c i (AffineMap.lineMap x y t) = AffineMap.lineMap (c i x) (c i y) t := by
    simp only [c, ← Apartment.vsub_base, AffineMap.lineMap_vsub]
    simpa only [LinearMap.coe_toAffineMap, LinearMap.neg_apply] using
      (-(P.root' i)).toAffineMap.apply_lineMap (x -ᵥ Apartment.base φ) (y -ᵥ Apartment.base φ) t
  have hb : c i (AffineMap.lineMap x y t) ∈ Icc (min (c i x) (c i y)) (max (c i x) (c i y)) := by
    rw [hline]
    simpa only [segment_eq_Icc'] using lineMap_mem_segment ℝ (c i x) (c i y) ht
  exact hb

/-- The walls of a discrete valuation with finitely many root directions are locally finite
in any topology on the apartment in which the root coordinates are continuous. -/
theorem locallyFinite_wall [TopologicalSpace (Apartment φ)] (hφ : φ.IsDiscrete)
    (hcont : ∀ i, Continuous fun x : Apartment φ ↦ P.root' i x.displacement) :
    LocallyFinite (wall (φ := φ)) := by
  intro x
  let c (i : ι) (z : Apartment φ) := -P.root' i z.displacement
  let U := {y | ∀ i, c i y ∈ Icc (c i x - 1) (c i x + 1)}
  refine ⟨U, ?_, finite_wall_inter_of_bounded
    (fun i ↦ ((φ.isDiscrete_iff.mp hφ) i _ _).subset
      (inter_subset_inter_left _ (φ.primedValueSet_subset_valueSet i)))
    (fun i _ hy ↦ hy i)⟩
  apply Filter.eventually_all.mpr
  intro i
  exact (hcont i).neg.continuousAt (Icc_mem_nhds (sub_lt_self _ zero_lt_one)
    (lt_add_of_pos_right _ zero_lt_one))

end Finite

end TauCeti.BruhatTits.AffineRoot
