/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-!
# Gluing Henstock and McShane integrals along a finite box partition

A gauge can prevent tags from crossing the faces of a fixed finite partition. Refinement then
preserves the Henstock condition, allowing genuinely conditional integrals on the pieces to glue.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology

open BoxIntegral

namespace TauCeti.BoxIntegral

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J K : Box ι}

/-- The closed box representing the intersection of two boxes is the intersection of their closed
boxes. -/
theorem _root_.BoxIntegral.Box.Icc_eq_inter_of_coe_eq_inf {A B C : Box ι}
    (h : (C : WithBot (Box ι)) = (A : WithBot (Box ι)) ⊓ B) :
    Box.Icc C = Box.Icc A ∩ Box.Icc B := by
  obtain ⟨hl, hu⟩ := Box.mk'_eq_coe.mp h.symm
  simp only [Box.Icc_def, Icc_inter_Icc, hl, hu]

open scoped Classical in
private def taggedPiece (p : Prepartition I) (π : TaggedPrepartition I) (J : Box ι)
    (h : ∀ K ∈ π.toPrepartition.restrict J, (π.infPrepartition p).tag K ∈ Box.Icc J) :
    TaggedPrepartition J where
  toPrepartition := π.toPrepartition.restrict J
  tag K := if K ∈ π.toPrepartition.restrict J then (π.infPrepartition p).tag K else J.upper
  tag_mem_Icc K := by
    split_ifs with hK
    · exact h K hK
    · exact J.upper_mem_Icc

private theorem integralSum_eq_sum_pieces {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F}
    (p : Prepartition I) (hp : p.IsPartition) (π : TaggedPrepartition I)
    (πi : ∀ J, TaggedPrepartition J)
    (hi : ∀ J ∈ p, (πi J).toPrepartition = π.toPrepartition.restrict J)
    (ht : ∀ J ∈ p, ∀ K ∈ πi J, (πi J).tag K = (π.infPrepartition p).tag K) :
    integralSum f vol π = ∑ J ∈ p.boxes, integralSum f vol (πi J) := by
  classical
  rw [← integralSum_inf_partition f vol π hp, integralSum,
    TaggedPrepartition.infPrepartition_toPrepartition, inf_comm, Prepartition.inf_def,
    Prepartition.biUnion_boxes, p.sum_biUnion_boxes]
  refine Finset.sum_congr rfl fun J hJ ↦ ?_
  rw [integralSum, ← hi J hJ]
  exact Finset.sum_congr rfl fun K hK ↦ by rw [ht J hJ K hK]

/-- In the refinement `π.infPrepartition p`, any box `K ∈ p.restrict A` inherits the tag of the
box `A ∈ π` containing it. -/
theorem _root_.BoxIntegral.TaggedPrepartition.infPrepartition_tag_of_mem
    {π : TaggedPrepartition I} {p : Prepartition I}
    {A : Box ι} (hA : A ∈ π) (hK : K ∈ p.restrict A) :
    (π.infPrepartition p).tag K = π.tag A := by
  simp [TaggedPrepartition.infPrepartition, π.toPrepartition.biUnionIndex_of_mem hA hK]

variable [Fintype ι]

/-- A finite box prepartition admits a gauge preventing tags from crossing its faces. -/
theorem _root_.BoxIntegral.Prepartition.exists_gauge_tag_mem_Icc (p : Prepartition I) :
    ∃ r : (ι → ℝ) → Ioi (0 : ℝ), ∀ x z, z ∈ closedBall x (r x) →
      ∀ J ∈ p, z ∈ Box.Icc J → x ∈ Box.Icc J := by
  have h (x : ι → ℝ) : ∃ r > 0, ∀ z ∈ closedBall x r,
      ∀ J ∈ p, z ∈ Box.Icc J → x ∈ Box.Icc J := by
    have hn : ∀ᶠ z in 𝓝 x, ∀ J ∈ p.boxes, z ∈ Box.Icc J → x ∈ Box.Icc J := by
      refine p.boxes.eventually_all.mpr fun J _ ↦ ?_
      by_cases hx : x ∈ Box.Icc J
      · exact .of_forall fun _ _ ↦ hx
      · exact (J.isCompact_Icc.isClosed.isOpen_compl.eventually_mem hx).mono
          fun _ hz h ↦ (hz h).elim
    exact nhds_basis_closedBall.mem_iff.mp hn
  choose r hr h using h
  exact ⟨fun x ↦ ⟨r x, hr x⟩, h⟩

/-- Refinement tags remain in the fixed piece when its gauge prevents face crossing. -/
theorem _root_.BoxIntegral.Prepartition.infPrepartition_tag_mem_Icc_of_gauge (p : Prepartition I)
    {π : TaggedPrepartition I}
    {r : (ι → ℝ) → Ioi (0 : ℝ)}
    (hr : ∀ x z, z ∈ closedBall x (r x) → ∀ J ∈ p,
      z ∈ Box.Icc J → x ∈ Box.Icc J)
    (hπ : π.IsSubordinate r) (hJ : J ∈ p)
    (hK : K ∈ π.toPrepartition.restrict J) :
    (π.infPrepartition p).tag K ∈ Box.Icc J := by
  obtain ⟨A, hA, hKA⟩ := (Prepartition.mem_restrict _).mp hK
  have hKp : K ∈ p.restrict A := (Prepartition.mem_restrict _).mpr
    ⟨J, hJ, by simpa only [inf_comm] using hKA⟩
  rw [π.infPrepartition_tag_of_mem hA hKp]
  have hleA : K ≤ A := (p.restrict A).le_of_mem hKp
  exact hr (π.tag A) K.upper
    (hπ A hA (Box.le_iff_Icc.mp hleA K.upper_mem_Icc)) J hJ
    (Box.le_iff_Icc.mp ((π.toPrepartition.restrict J).le_of_mem hK) K.upper_mem_Icc)

/-- A gauge preventing face crossing preserves the Henstock condition under refinement. -/
theorem _root_.BoxIntegral.Prepartition.isHenstock_infPrepartition_of_gauge (p : Prepartition I)
    {π : TaggedPrepartition I}
    {r : (ι → ℝ) → Ioi (0 : ℝ)}
    (hr : ∀ x z, z ∈ closedBall x (r x) → ∀ J ∈ p,
      z ∈ Box.Icc J → x ∈ Box.Icc J)
    (hπ : π.IsSubordinate r) (hH : π.IsHenstock) :
    (π.infPrepartition p).IsHenstock := by
  intro K hK
  obtain ⟨A, hA, hKA⟩ := π.toPrepartition.mem_biUnion.mp hK
  obtain ⟨J, hJ, hKJ⟩ := (Prepartition.mem_restrict _).mp hKA
  have hK' : K ∈ π.toPrepartition.restrict J := (Prepartition.mem_restrict _).mpr
    ⟨A, hA, by simpa only [inf_comm] using hKJ⟩
  refine (Box.Icc_eq_inter_of_coe_eq_inf hKJ).superset
    ⟨?_, p.infPrepartition_tag_mem_Icc_of_gauge hr hπ hJ hK'⟩
  rw [π.infPrepartition_tag_of_mem hA hKA]
  exact hH A hA

/-- Integrals on the members of a finite box partition glue to an integral on the entire box, for
integration parameters whose gauges may vary from point to point (`l.bRiemann = false`) and which
impose no distortion bound (`l.bDistortion = false`), that is, for the Henstock and the McShane
integrals. No absolute-integrability or primitive hypothesis is used. -/
theorem _root_.BoxIntegral.Prepartition.IsPartition.hasIntegral_sum {p : Prepartition I}
    (hp : p.IsPartition) {l : IntegrationParams} (hlR : l.bRiemann = false)
    (hlD : l.bDistortion = false) {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {y : Box ι → F}
    (hy : ∀ J ∈ p, HasIntegral J l f vol (y J)) :
    HasIntegral I l f vol (∑ J ∈ p.boxes, y J) := by
  classical
  -- Choose gauges for face crossing and each piece, then take their finite minimum.
  obtain ⟨r₀, hr₀⟩ := p.exists_gauge_tag_mem_Icc
  apply HasIntegral.of_mul (p.boxes.card : ℝ)
  intro ε hε
  choose r _ he using fun J (hJ : J ∈ p) ↦ hasIntegral_iff.mp (hy J hJ) ε hε
  let rJ (J : Box ι) (x : ι → ℝ) : Ioi (0 : ℝ) :=
    if hJ : J ∈ p then r J hJ 0 x else ⟨1, zero_lt_one⟩
  let R (x : ι → ℝ) : Ioi (0 : ℝ) := min (r₀ x) (p.boxes.inf' hp.nonempty_boxes (fun J ↦ rJ J x))
  have hR₀ (x) : R x ≤ r₀ x := min_le_left _ _
  have hRJ (J) (hJ : J ∈ p) (x) : R x ≤ r J hJ 0 x :=
    (min_le_right _ _).trans ((Finset.inf'_le _ hJ).trans_eq (by simp [rJ, hJ]))
  refine ⟨fun _ ↦ R, fun _ ↦ l.rCond_of_bRiemann_eq_false hlR, ?_⟩
  intro c π hπ hπp
  have hsub₀ := hπ.isSubordinate.mono' (fun K _ ↦ hR₀ (π.tag K))
  have htag (J) (hJ : J ∈ p) (K) (hK : K ∈ π.toPrepartition.restrict J) :=
    p.infPrepartition_tag_mem_Icc_of_gauge hr₀ hsub₀ hJ hK
  -- Refine an arbitrary test partition and restrict its tags to each fixed piece.
  let πi (J : Box ι) : TaggedPrepartition J :=
    if hJ : J ∈ p then taggedPiece p π J (htag J hJ)
    else TaggedPrepartition.single J J le_rfl J.upper J.upper_mem_Icc
  have hi (J) (hJ : J ∈ p) : (πi J).toPrepartition = π.toPrepartition.restrict J := by
    simp only [πi, dite_eq_left hJ, taggedPiece]
  have ht (J) (hJ : J ∈ p) (K) (hK : K ∈ πi J) :
      (πi J).tag K = (π.infPrepartition p).tag K := by
    have hK' : K ∈ π.toPrepartition.restrict J := by
      rwa [← TaggedPrepartition.mem_toPrepartition, hi J hJ] at hK
    simp only [πi, dite_eq_left hJ, taggedPiece, ite_eq_left hK']
  have hmem (J) (hJ : J ∈ p) (K) (hK : K ∈ πi J) : K ∈ π.infPrepartition p := by
    rw [← TaggedPrepartition.mem_toPrepartition, hi J hJ] at hK
    rw [← TaggedPrepartition.mem_toPrepartition, TaggedPrepartition.infPrepartition_toPrepartition,
      inf_comm, Prepartition.inf_def]
    exact p.mem_biUnion.mpr ⟨J, hJ, hK⟩
  have hH (hl : l.bHenstock) :=
    p.isHenstock_infPrepartition_of_gauge hr₀ hsub₀ (hπ.isHenstock hl)
  have hS := hπ.isSubordinate.infPrepartition p
  -- Each restricted tagged partition meets the piece gauge and, if required, Henstock conditions.
  have hbound (J) (hJ : J ∈ p) : dist (integralSum f vol (πi J)) (y J) ≤ ε := by
    apply he J hJ 0 (πi J)
    · refine ⟨?_, fun hl ↦ ?_, by simp [hlD], by simp [hlD]⟩
      · intro K hK x hx
        rw [ht J hJ K hK]
        exact closedBall_subset_closedBall (hRJ J hJ _)
          (hS K (hmem J hJ K hK) hx)
      · intro K hK
        rw [ht J hJ K hK]
        exact hH hl K (hmem J hJ K hK)
    · rw [TaggedPrepartition.IsPartition, hi J hJ]
      exact hπp.restrict (p.le_of_mem hJ)
  -- Sum the piecewise error bounds to obtain the global finite-cardinality estimate.
  rw [integralSum_eq_sum_pieces p hp π πi hi ht]
  exact (dist_sum_sum_le_of_le _ hbound).trans_eq (by simp)

end TauCeti.BoxIntegral
