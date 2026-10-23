/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Comparison of categorical and classical CW structures

The conversions between categorical and classical relative CW complexes preserve their
cellular presentations. Starting with a categorical complex, its stages are naturally
homeomorphic to the stages obtained by passing to the classical structure and back. The
homeomorphisms commute with the inclusions into the target. Starting with a classical complex,
the recovered cells correspond to the original cells, and their characteristic maps agree on
the closed unit ball after inclusion into the original ambient space.

These comparisons use the specified CW structures throughout: no replacement CW model or
choice of characteristic maps is made. The target of the categorical round trip is the
subspace `Set.univ` of the original target, identified with it by `Homeomorph.Set.univ`.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.2.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

noncomputable section

open CategoryTheory HomotopicalAlgebra Topology Topology.RelCWComplex Metric Set

universe u

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f) [T2Space Y]

/-- Each stage of a categorical relative CW complex is homeomorphic to the corresponding
stage obtained by converting to the classical structure and back. -/
def classicalRoundTripStageHomeomorph (n : ℕ) :
    letI := c.toRelCWComplex
    c.F.obj n ≃ₜ TauCeti.skeletonObj (univ : Set Y) n := by
  letI := c.toRelCWComplex
  exact (c.isClosedEmbedding_incl_app n).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (c.range_incl_app_eq_toRelCWComplex_skeletonLT n))

/-- The stage comparison is the original inclusion, read in the corresponding skeleton. -/
@[simp↓] lemma classicalRoundTripStageHomeomorph_apply_coe (n : ℕ) (x : c.F.obj n) :
    letI := c.toRelCWComplex
    (c.classicalRoundTripStageHomeomorph n x : Y) = c.incl.app n x :=
  (rfl)

/-- The inverse stage comparison recovers the point of the original stage with the specified
image in the target. -/
@[simp↓] lemma classicalRoundTripStageHomeomorph_symm_apply_coe (n : ℕ)
    (x : letI := c.toRelCWComplex; TauCeti.skeletonObj (univ : Set Y) n) :
    letI := c.toRelCWComplex
    c.incl.app n ((c.classicalRoundTripStageHomeomorph n).symm x) = (x : Y) := by
  rw [← c.classicalRoundTripStageHomeomorph_apply_coe]
  exact congrArg Subtype.val ((c.classicalRoundTripStageHomeomorph n).apply_symm_apply x)

/-- The stage homeomorphisms form an isomorphism of the sequential diagrams, so they preserve
all skeletal inclusions, not only the individual spaces. -/
def classicalRoundTripIso :
    letI := c.toRelCWComplex
    c.F ≅ (TauCeti.toRelativeCWComplex (univ : Set Y)).F := by
  letI := c.toRelCWComplex
  refine NatIso.ofComponents (fun n ↦ TopCat.isoOfHomeo
    (c.classicalRoundTripStageHomeomorph n)) ?_
  intro m n g
  ext x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (c.incl.naturality g) x

lemma classicalRoundTripIso_hom_app (n : ℕ) :
    letI := c.toRelCWComplex
    c.classicalRoundTripIso.hom.app n =
      (TopCat.isoOfHomeo (c.classicalRoundTripStageHomeomorph n)).hom :=
  (rfl)

lemma classicalRoundTripIso_inv_app (n : ℕ) :
    letI := c.toRelCWComplex
    c.classicalRoundTripIso.inv.app n =
      (TopCat.isoOfHomeo (c.classicalRoundTripStageHomeomorph n)).inv :=
  (rfl)

/-- Evaluation of the forward comparison uses the stage homeomorphism. The application form
also fixes the dependent presentation of the reconstructed stage for simplification. -/
lemma classicalRoundTripIso_hom_app_apply (n : ℕ) (x : c.F.obj n) :
    letI := c.toRelCWComplex
    c.classicalRoundTripIso.hom.app n x = c.classicalRoundTripStageHomeomorph n x :=
  (rfl)

/-- Evaluation of the inverse comparison uses the inverse stage homeomorphism. -/
lemma classicalRoundTripIso_inv_app_apply (n : ℕ)
    (x : letI := c.toRelCWComplex; TauCeti.skeletonObj (univ : Set Y) n) :
    letI := c.toRelCWComplex
    c.classicalRoundTripIso.inv.app n x = (c.classicalRoundTripStageHomeomorph n).symm x :=
  (rfl)

/-- The comparison of sequential diagrams commutes with their maps to the original target,
using the canonical identification of the round trip's target `Set.univ` with that target. -/
lemma classicalRoundTripIso_hom_app_incl (n : ℕ) :
    letI := c.toRelCWComplex
    (c.classicalRoundTripIso.hom.app n) ≫
      (TauCeti.toRelativeCWComplex (univ : Set Y)).incl.app n ≫
      (TopCat.isoOfHomeo (Homeomorph.Set.univ Y)).hom = c.incl.app n := by
  ext x
  exact c.classicalRoundTripStageHomeomorph_apply_coe n x

/-- At the initial stage, the comparison identifies the original base with its image under
the given closed embedding. -/
lemma isoBot_inv_classicalRoundTripIso_hom_app_zero :
    letI := c.toRelCWComplex
    c.isoBot.inv ≫ c.classicalRoundTripIso.hom.app 0 ≫
      (TauCeti.toRelativeCWComplex (univ : Set Y)).isoBot.hom =
      (TopCat.isoOfHomeo c.isClosedEmbedding.isEmbedding.toHomeomorph).hom := by
  let _ := c.toRelCWComplex
  let d := TauCeti.toRelativeCWComplex (univ : Set Y)
  have hd : d.incl.app 0 = d.isoBot.hom ≫
      TopCat.ofHom (ContinuousMap.inclusion (Set.subset_univ (range f))) := by
    simpa only [Iso.hom_inv_id_assoc, Nat.bot_eq_zero] using
      congrArg (fun q ↦ d.isoBot.hom ≫ q) d.fac
  ext x
  have h := congrArg Subtype.val (ConcreteCategory.congr_hom hd
    (c.classicalRoundTripStageHomeomorph 0 (c.isoBot.inv x)))
  exact h.symm.trans (ConcreteCategory.congr_hom c.fac x)

/-- After identifying the target, the cell inclusions of the categorical round trip are the
original cell inclusions. -/
lemma classicalRoundTrip_cells_ι_apply (n : ℕ)
    (i : letI := c.toRelCWComplex
      ((TauCeti.toRelativeCWComplex (univ : Set Y)).attachCells n (not_isMax n)).ι)
    (z : TopCat.disk.{u} n) :
    letI := c.toRelCWComplex
    (((⟨n, not_isMax n, i⟩ : (TauCeti.toRelativeCWComplex (univ : Set Y)).Cells).ι z :
      (univ : Set Y)) : Y) =
      (⟨n, not_isMax n, c.toRelCWComplexCellEquiv n i⟩ : c.Cells).ι z := by
  let _ := c.toRelCWComplex
  rw [TauCeti.coe_toRelativeCWComplex_cells_ι_apply]
  exact c.toRelCWComplex_map_disk n i z

end TopCat.RelativeCWComplex

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

/-- The characteristic maps recovered by the classical round trip agree with the original
maps on the closed unit ball, after inclusion of the complex into its ambient space. -/
lemma categoricalRoundTrip_map_apply (n : ℕ)
    (i : (toRelativeCWComplex C).toRelCWComplex.cell n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    letI := (toRelativeCWComplex C).toRelCWComplex
    (map (C := (univ : Set C)) n i x : X) =
      map n ((toRelativeCWComplex C).toRelCWComplexCellEquiv n i) x := by
  rw [(toRelativeCWComplex C).toRelCWComplex_map_apply]
  rw [coe_toRelativeCWComplex_cells_ι_apply]
  simp only [Homeomorph.apply_symm_apply]

/-- The skeleta of the recovered classical structure are exactly the original skeleta after
inclusion into the ambient space. This includes the base, at stage zero. -/
lemma image_categoricalRoundTrip_skeletonLT (n : ℕ) :
    letI := (toRelativeCWComplex C).toRelCWComplex
    Subtype.val '' (skeletonLT (univ : Set C) n : Set C) =
      (skeletonLT C n : Set X) := by
  let _ := (toRelativeCWComplex C).toRelCWComplex
  rw [← (toRelativeCWComplex C).range_incl_app_eq_toRelCWComplex_skeletonLT]
  rw [← Set.range_comp]
  exact range_toRelativeCWComplex_incl_app n

end TauCeti
