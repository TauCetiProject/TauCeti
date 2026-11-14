/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Topology.Sheaves.Leray.Colimit
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Algebra.Category.Grp.IsSheafFor
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.AddCommGrp
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# The first cohomology of the structure sheaf of the Riemann sphere vanishes

The Riemann sphere `OnePoint ℂ` is covered by two coordinate discs: `|z| < 2` in the affine chart
and `|z| > 1/2`, together with `∞`, in the inverted chart
(`TauCeti.RiemannSurface.sphereDiscCover`).
Their intersection is the annulus `1/2 < |z| < 2`. A holomorphic function `f` on the annulus splits
as `f = f₊ + f₋` by Laurent's theorem: the nonnegative part `f₊` of its Laurent series is
holomorphic on `|z| < 2`, and the principal part `f₋` is holomorphic on `|z| > 1/2` and vanishes at
`∞`, so in the coordinate `w = 1/z` it extends holomorphically across `w = 0` by the removable
singularity theorem. So the Čech differential from the two discs to their intersection is onto,
and the Čech complex of this cover has no first cohomology.

Both members are coordinate discs, so they have vanishing `H¹` for the structure sheaf
(`TauCeti.subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball`). The degree one Leray
comparison therefore gives `H¹(ℙ¹, 𝒪) = 0` in sheaf cohomology, and, since every open cover of the
compact sphere is refined by a finite cover by coordinate discs, the degree one Čech cohomology of
the structure sheaf vanishes as well.

## Main definitions

* `TauCeti.RiemannSurface.sphereDiscCover`: the cover of `OnePoint ℂ` by the coordinate discs
  `|z| < 2` and `|z| > 1/2`.

## Main results

* `TauCeti.RiemannSurface.exists_sub_eq_sphereDiscCover`: the Laurent splitting of a holomorphic
  function on the overlap annulus into holomorphic functions on the two discs.
* `TauCeti.RiemannSurface.isZero_homology_one_cechComplex_sphereDiscCover`: the Čech complex of the
  two-disc cover has no first cohomology.
* `TauCeti.RiemannSurface.subsingleton_H_one_holomorphicStructureSheafModules_sphere`: the sheaf
  cohomology `H¹(ℙ¹, 𝒪)` vanishes.
* `TauCeti.RiemannSurface.isZero_cechCohomology_one_holomorphicStructureSheafModules_sphere`: the
  degree one Čech cohomology of the structure sheaf of `ℙ¹` vanishes.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 12.8 (Leray's theorem) and Theorem 13.5 (`H¹(ℙ¹, 𝒪) = 0`).
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology Filter OnePoint
open TauCeti.Topology TauCeti.CategoryTheory
open scoped Manifold ENNReal

namespace TauCeti.RiemannSurface

/-- Membership in the disc of radius `2`, the image of both members of the cover in their charts. -/
private lemma mem_eball_ofReal_two {z : ℂ} : z ∈ Metric.eball 0 (ENNReal.ofReal 2) ↔ ‖z‖ < 2 := by
  rw [Metric.eball_ofReal, mem_ball_zero_iff]

/-- The cover of the Riemann sphere by two coordinate discs: the disc `|z| < 2` in the affine
chart, and the disc `|w| < 2` in the inverted chart `w = 1/z`, which is `|z| > 1/2` together with
`∞`. -/
def sphereDiscCover : Fin 2 → Opens (TopCat.of (OnePoint ℂ)) :=
  ![⟨affineChart.source ∩ affineChart ⁻¹' Metric.eball 0 (ENNReal.ofReal 2),
      affineChart.isOpen_inter_preimage Metric.isOpen_eball⟩,
    ⟨invChart.source ∩ invChart ⁻¹' Metric.eball 0 (ENNReal.ofReal 2),
      invChart.isOpen_inter_preimage Metric.isOpen_eball⟩]

/-- A finite point lies in the first disc exactly when `|z| < 2`. -/
@[simp]
theorem coe_mem_sphereDiscCover_zero {z : ℂ} :
    (z : OnePoint ℂ) ∈ sphereDiscCover 0 ↔ ‖z‖ < 2 := by
  simp only [sphereDiscCover, Fin.isValue, Matrix.cons_val_zero, ← SetLike.mem_coe, Opens.coe_mk,
    Set.mem_inter_iff, Set.mem_preimage, affineChart_coe, mem_eball_ofReal_two]
  simp [coe_ne_infty]

/-- The point at infinity does not lie in the first disc. -/
@[simp]
theorem infty_notMem_sphereDiscCover_zero : (∞ : OnePoint ℂ) ∉ sphereDiscCover 0 := by
  simp [sphereDiscCover, ← SetLike.mem_coe]

/-- A finite point lies in the second disc exactly when `|z| > 1/2`. -/
@[simp]
theorem coe_mem_sphereDiscCover_one {z : ℂ} :
    (z : OnePoint ℂ) ∈ sphereDiscCover 1 ↔ 1 / 2 < ‖z‖ := by
  simp only [sphereDiscCover, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ← SetLike.mem_coe, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage, invChart_coe,
    mem_eball_ofReal_two, invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe,
    norm_inv]
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [inv_lt_comm₀ hz' two_pos]
    simp [hz, one_div]

/-- The point at infinity lies in the second disc. -/
@[simp]
theorem infty_mem_sphereDiscCover_one : (∞ : OnePoint ℂ) ∈ sphereDiscCover 1 := by
  simp [sphereDiscCover, ← SetLike.mem_coe, infty_ne_coe]

/-- The two discs cover the Riemann sphere. -/
theorem iSup_sphereDiscCover : ⨆ i, sphereDiscCover i = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ?_
  induction x using OnePoint.rec with
  | infty => exact ⟨1, infty_mem_sphereDiscCover_one⟩
  | coe z =>
    by_cases hz : ‖z‖ < 2
    · exact ⟨0, coe_mem_sphereDiscCover_zero.2 hz⟩
    · exact ⟨1, coe_mem_sphereDiscCover_one.2 (by linarith)⟩

/-- Both discs are coordinate discs, so they have vanishing `H¹` for the structure sheaf. -/
theorem subsingleton_H'_one_holomorphicStructureSheafModules_sphereDiscCover (i : Fin 2) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))) 1 (sphereDiscCover i)) := by
  fin_cases i
  · exact subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
      affineChart_mem_maximalAtlas (by simp)
  · exact subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
      invChart_mem_maximalAtlas (by simp)

/-- **Laurent splitting on the overlap of the two discs.** Every holomorphic function on the annulus
`1/2 < |z| < 2` is the difference of the restrictions of a holomorphic function on the disc
`|z| < 2` and of a holomorphic function on the disc `|z| > 1/2` around `∞`. These are the
nonnegative part and minus the principal part of its Laurent series. -/
theorem exists_sub_eq_sphereDiscCover
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj.obj
      (op (sphereDiscCover 0 ⊓ sphereDiscCover 1))) :
    ∃ (s₀ : (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj.obj (op (sphereDiscCover 0)))
      (s₁ : (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj.obj (op (sphereDiscCover 1))),
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj.map (homOfLE inf_le_left).op s₀ -
        (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj.map
          (homOfLE inf_le_right).op s₁ = s := by
  classical
  -- `s` read in the affine coordinate, extended by zero off the annulus
  let f : ℂ → ℂ := fun z ↦ Subtype.val.extend s 0 (z : OnePoint ℂ)
  have hmem {z : ℂ}
      (hz : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal 2) \ Metric.closedBall 0 (1 / 2)) :
      (z : OnePoint ℂ) ∈ sphereDiscCover 0 ⊓ sphereDiscCover 1 := by
    rw [Set.mem_sdiff, mem_eball_ofReal_two, Metric.mem_closedBall,
      dist_zero_right, not_le] at hz
    exact ⟨coe_mem_sphereDiscCover_zero.2 hz.1, coe_mem_sphereDiscCover_one.2 hz.2⟩
  have hfs {z : ℂ} (hz : (z : OnePoint ℂ) ∈ sphereDiscCover 0 ⊓ sphereDiscCover 1) :
      f z = s ⟨z, hz⟩ :=
    Subtype.val_injective.extend_apply _ _ (⟨z, hz⟩ : ↥(sphereDiscCover 0 ⊓ sphereDiscCover 1))
  have hf : DifferentiableOn ℂ f
      (Metric.eball (0 : ℂ) (ENNReal.ofReal 2) \ Metric.closedBall 0 (1 / 2)) := fun z hz ↦ by
    have h₁ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val.extend s 0) (z : OnePoint ℂ) :=
      (((holomorphicStructureSheafModules.contMDiff s) ⟨z, hmem hz⟩).extend_subtypeVal
        0).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.1
      (h₁.comp z (contMDiff_coe.mdifferentiable (by simp) z))).differentiableWithinAt
  have hL := hf.hasLaurentSeriesOnAnnulus (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
    (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by norm_num, by norm_num⟩)
  set a := circleLaurentCoeff f 0 1
  -- the principal part in the coordinate `w = 1/z`, holomorphic across `w = 0`
  let h : ℂ → ℂ := fun w ↦ laurentNegPart a 0 w⁻¹
  have hh0 : h 0 = 0 := by
    simp only [h, inv_zero, laurentNegPart_def, sub_zero]
    exact (tsum_congr fun n ↦ by rw [zero_zpow _ (by omega), zero_smul]).trans tsum_zero
  have hh : DifferentiableOn ℂ h (Metric.eball 0 (ENNReal.ofReal 2)) := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self (by simp)))).1 ⟨fun w hw ↦ ?_, ?_⟩
    · have hw0 : w ≠ 0 := hw.2
      have hw2 : ‖w‖ < 2 := mem_eball_ofReal_two.1 hw.1
      refine (((hL.differentiableOn_laurentNegPart w⁻¹ ?_).differentiableAt
        (Metric.isClosed_closedBall.isOpen_compl.mem_nhds ?_)).comp w
          (differentiableAt_inv hw0)).differentiableWithinAt <;>
      · rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, norm_inv,
          lt_inv_comm₀ (by norm_num) (norm_pos_iff.2 hw0)]
        linarith
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hh0]
      refine hL.tendsto_laurentNegPart_cocompact.comp ?_
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
  refine ⟨holomorphicStructureSheafModules.ofContMDiff _
      (Manifold.mdifferentiable_restrict_comp_chart affineChart_mem_maximalAtlas
        (W := sphereDiscCover 0) Set.inter_subset_left (g := laurentPosPart a 0)
        fun x hx ↦ ((hL.differentiableOn_laurentPosPart _ hx.2).differentiableAt
          (Metric.isOpen_eball.mem_nhds hx.2)).mdifferentiableAt).contMDiff,
    -holomorphicStructureSheafModules.ofContMDiff _
      (Manifold.mdifferentiable_restrict_comp_chart invChart_mem_maximalAtlas
        (W := sphereDiscCover 1) Set.inter_subset_left (g := h)
        fun x hx ↦ ((hh _ hx.2).differentiableAt
          (Metric.isOpen_eball.mem_nhds hx.2)).mdifferentiableAt).contMDiff,
    ?_⟩
  ext ⟨x, hx⟩
  induction x using OnePoint.rec with
  | infty => exact absurd hx.1 infty_notMem_sphereDiscCover_zero
  | coe z =>
    have hz : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal 2) \ Metric.closedBall 0 (1 / 2) := by
      refine ⟨mem_eball_ofReal_two.2 (coe_mem_sphereDiscCover_zero.1 hx.1), ?_⟩
      simpa [Metric.mem_closedBall] using coe_mem_sphereDiscCover_one.1 hx.2
    simp only [holomorphicStructureSheafModules.sub_apply,
      holomorphicStructureSheafModules.neg_apply, holomorphicStructureSheafModules.map_apply,
      holomorphicStructureSheafModules.ofContMDiff_apply, sub_neg_eq_add]
    rw [← hfs hx, hL.eq_laurentPosPart_add_laurentNegPart hz]
    simp [h]

/-- **The two-disc cover is acyclic.** The augmented Čech complex of the structure sheaf of the
Riemann sphere for the cover by the discs `|z| < 2` and `|z| > 1/2` is exact. -/
theorem quasiIso_cechAugmentation_sphereDiscCover :
    QuasiIso (cechAugmentation sphereDiscCover isTerminalTop
      ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))).obj) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective]
  refine ⟨(Presieve.isSheafFor_comp_forget_addCommGrpCat_iff _ _).2 fun E ↦ ?_, fun s ↦ ?_⟩
  · convert isSheafFor_ofArrows_of_iSup_eq_top sphereDiscCover iSup_sphereDiscCover
      ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))) E
    exact Subsingleton.elim _ _
  · obtain ⟨s₀, s₁, hs⟩ := exists_sub_eq_sphereDiscCover s
    exact ⟨(s₀, s₁), hs⟩

/-- The Čech complex of the structure sheaf for the two-disc cover of the Riemann sphere has no
first cohomology. -/
theorem isZero_homology_one_cechComplex_sphereDiscCover :
    IsZero (((cechComplexFunctor sphereDiscCover).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))).obj).homology 1) :=
  have := quasiIso_cechAugmentation_sphereDiscCover
  ((exactAt_iff_of_quasiIsoAt (cechAugmentation sphereDiscCover isTerminalTop
    ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))).obj) 1).mp
    (CochainComplex.exactAt_succ_single_obj _ 0)).isZero_homology

/-- **`H¹(ℙ¹, 𝒪) = 0`.** The first sheaf cohomology of the structure sheaf of the Riemann sphere
vanishes. -/
theorem subsingleton_H_one_holomorphicStructureSheafModules_sphere :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ))) 1) :=
  AddCommGrpCat.subsingleton_of_isZero <| isZero_homology_one_cechComplex_sphereDiscCover.of_iso
    (homologyCechComplexIsoHOne sphereDiscCover iSup_sphereDiscCover _
      subsingleton_H'_one_holomorphicStructureSheafModules_sphereDiscCover).symm

/-- The degree one Čech cohomology of the structure sheaf of the Riemann sphere vanishes. -/
theorem isZero_cechCohomology_one_holomorphicStructureSheafModules_sphere :
    IsZero ((cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) (OnePoint ℂ)).obj) :=
  Sheaf.isZero_cechCohomology_one_of_subsingleton_H _
    (fun V hV ↦
      let ⟨ι, _, U, hU⟩ :=
        exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules V hV
      ⟨ι, U, hU⟩)
    subsingleton_H_one_holomorphicStructureSheafModules_sphere

end TauCeti.RiemannSurface
