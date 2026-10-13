/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-!
# Gluing Henstock integrals along a finite box partition

A gauge can prevent tags from crossing the faces of a fixed finite partition. Refinement then
preserves the Henstock condition, allowing genuinely conditional integrals on the pieces to glue.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology

open BoxIntegral

namespace TauCeti.BoxIntegral

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J K : Box ι}

/-- A finite box prepartition admits a gauge preventing tags from crossing its faces. -/
theorem _root_.BoxIntegral.Prepartition.exists_gauge_tag_mem_Icc (p : Prepartition I) :
    ∃ r : (ι → ℝ) → Ioi (0 : ℝ), ∀ x z, z ∈ closedBall x (r x) →
      ∀ J ∈ p, z ∈ Box.Icc J → x ∈ Box.Icc J := by
  have h (x : ι → ℝ) : ∃ r > 0, ∀ z ∈ closedBall x r,
      ∀ J ∈ p, z ∈ Box.Icc J → x ∈ Box.Icc J := by
    have hn : ∀ᶠ z in 𝓝 x, ∀ J ∈ p.boxes, x ∉ Box.Icc J → z ∉ Box.Icc J := by
      rw [Finset.eventually_all]
      intro J _
      by_cases hx : x ∈ Box.Icc J
      · exact Eventually.of_forall (by simp [hx])
      · filter_upwards [J.isCompact_Icc.isClosed.isOpen_compl.mem_nhds hx] with z hz
        exact fun _ ↦ hz
    obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp hn
    exact ⟨r, hr, fun z hz J hJ hzi ↦ by
      by_contra hxi
      exact hball hz J hJ hxi hzi⟩
  choose r hr h using h
  exact ⟨fun x ↦ ⟨r x, hr x⟩, h⟩

omit [Fintype ι] in
/-- A point in both closed boxes lies in the closed box representing their intersection. -/
theorem _root_.BoxIntegral.Box.mem_Icc_of_coe_eq_inf {A B C : Box ι} {x : ι → ℝ}
    (h : (C : WithBot (Box ι)) = (A : WithBot (Box ι)) ⊓ B)
    (hxA : x ∈ Box.Icc A) (hxB : x ∈ Box.Icc B) : x ∈ Box.Icc C := by
  have hh : A.lower ⊔ B.lower = C.lower ∧ A.upper ⊓ B.upper = C.upper :=
    Box.mk'_eq_coe.mp h.symm
  rw [Box.Icc_def, mem_Icc, ← hh.1, ← hh.2]
  exact ⟨sup_le hxA.1 hxB.1, le_inf hxA.2 hxB.2⟩

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
  have htag : (π.infPrepartition p).tag K = π.tag A := by
    -- Refinement tags are defined through biUnionIndex; expose it for the membership rewrite.
    change π.tag (π.toPrepartition.biUnionIndex (fun A ↦ p.restrict A) K) = _
    rw [π.toPrepartition.biUnionIndex_of_mem hA hKp]
  rw [htag]
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
  have htag : (π.infPrepartition p).tag K = π.tag A := by
    -- Refinement tags are defined through biUnionIndex; expose it for the membership rewrite.
    change π.tag (π.toPrepartition.biUnionIndex (fun A ↦ p.restrict A) K) = _
    rw [π.toPrepartition.biUnionIndex_of_mem hA hKA]
  exact Box.mem_Icc_of_coe_eq_inf hKJ (by simpa only [htag] using hH A hA)
    (p.infPrepartition_tag_mem_Icc_of_gauge hr hπ hJ hK')

omit [Fintype ι] in
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

omit [Fintype ι] in
private theorem integralSum_eq_sum_pieces {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F}
    (p : Prepartition I) (hp : p.IsPartition) (π : TaggedPrepartition I)
    (πi : ∀ J, TaggedPrepartition J)
    (hi : ∀ J ∈ p, (πi J).toPrepartition = π.toPrepartition.restrict J)
    (ht : ∀ J ∈ p, ∀ K ∈ πi J, (πi J).tag K = (π.infPrepartition p).tag K) :
    integralSum f vol π = ∑ J ∈ p.boxes, integralSum f vol (πi J) := by
  classical
  rw [← integralSum_inf_partition f vol π hp]
  have hboxes : (π.infPrepartition p).boxes = p.boxes.biUnion
      (fun J ↦ (π.toPrepartition.restrict J).boxes) := by
    -- infPrepartition has the underlying infimum boxes by definition.
    change (π.toPrepartition ⊓ p).boxes = (p ⊓ π.toPrepartition).boxes
    rw [inf_comm]
  rw [integralSum, hboxes, p.sum_biUnion_boxes]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [integralSum, ← hi J hJ]
  apply Finset.sum_congr rfl
  intro K hK
  rw [ht J hJ K hK]

/-- Genuine Henstock integrals on the members of a finite box partition glue to an integral
on the entire box. No absolute-integrability or primitive hypothesis is used. -/
theorem hasIntegral_Henstock_of_partition {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F}
    (p : Prepartition I) (hp : p.IsPartition) (y : Box ι → F)
    (hy : ∀ J ∈ p, HasIntegral J IntegrationParams.Henstock f vol (y J)) :
    HasIntegral I IntegrationParams.Henstock f vol (∑ J ∈ p.boxes, y J) := by
  classical
  have hpne : p.boxes.Nonempty := by
    by_contra h
    have he : p = ⊥ := Prepartition.injective_boxes (Finset.not_nonempty_iff_eq_empty.mp h)
    have hu := hp.iUnion_eq
    rw [he, Prepartition.iUnion_bot] at hu
    exact I.coe_ne_empty hu.symm
  -- Choose gauges for face crossing and each piece, then take their finite minimum.
  obtain ⟨r₀, hr₀⟩ := p.exists_gauge_tag_mem_Icc
  apply HasIntegral.of_mul (p.boxes.card : ℝ)
  intro ε hε
  choose r hr he using fun J (hJ : J ∈ p) ↦ hasIntegral_iff.mp (hy J hJ) ε hε
  let rJ (J : Box ι) (x : ι → ℝ) : Ioi (0 : ℝ) :=
    if hJ : J ∈ p then r J hJ 0 x else ⟨1, zero_lt_one⟩
  let R (x : ι → ℝ) : Ioi (0 : ℝ) := min (r₀ x) (p.boxes.inf' hpne (fun J ↦ rJ J x))
  have hR₀ (x) : R x ≤ r₀ x := min_le_left _ _
  have hRJ (J) (hJ : J ∈ p) (x) : R x ≤ r J hJ 0 x := by
    exact (min_le_right _ _).trans ((Finset.inf'_le _ hJ).trans_eq (by simp [rJ, hJ]))
  refine ⟨fun _ ↦ R, fun _ ↦ IntegrationParams.rCond_of_bRiemann_eq_false _ rfl, ?_⟩
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
      -- Tagged membership is membership in the underlying prepartition.
      change K ∈ (πi J).toPrepartition at hK
      rwa [hi J hJ] at hK
    simp only [πi, dite_eq_left hJ, taggedPiece, ite_eq_left hK']
  have hmem (J) (hJ : J ∈ p) (K) (hK : K ∈ πi J) : K ∈ π.infPrepartition p := by
    -- Tagged membership is membership in the underlying prepartition.
    change K ∈ (πi J).toPrepartition at hK
    rw [hi J hJ] at hK
    -- Tagged refinement uses the same underlying infimum prepartition.
    change K ∈ π.toPrepartition ⊓ p
    rw [inf_comm]
    exact p.mem_biUnion.mpr ⟨J, hJ, hK⟩
  have hH := p.isHenstock_infPrepartition_of_gauge hr₀ hsub₀ (hπ.isHenstock rfl)
  have hS := hπ.isSubordinate.infPrepartition p
  -- Each restricted tagged partition meets the piece gauge and Henstock conditions.
  have hbound (J) (hJ : J ∈ p) : dist (integralSum f vol (πi J)) (y J) ≤ ε := by
    apply he J hJ 0 (πi J)
    · refine ⟨?_, fun _ ↦ ?_, by simp [IntegrationParams.Henstock],
        by simp [IntegrationParams.Henstock]⟩
      · intro K hK x hx
        rw [ht J hJ K hK]
        exact closedBall_subset_closedBall (hRJ J hJ _)
          (hS K (hmem J hJ K hK) hx)
      · intro K hK
        rw [ht J hJ K hK]
        exact hH K (hmem J hJ K hK)
    · -- The tagged partition predicate is defined on its underlying prepartition.
      change ((πi J).toPrepartition).IsPartition
      rw [hi J hJ]
      exact hπp.restrict (p.le_of_mem hJ)
  -- Sum the piecewise error bounds to obtain the global finite-cardinality estimate.
  rw [integralSum_eq_sum_pieces p hp π πi hi ht]
  calc
    dist (∑ J ∈ p.boxes, integralSum f vol (πi J)) (∑ J ∈ p.boxes, y J) ≤
        ∑ J ∈ p.boxes, dist (integralSum f vol (πi J)) (y J) := dist_sum_sum_le _ _ _
    _ ≤ ∑ _J ∈ p.boxes, ε := Finset.sum_le_sum hbound
    _ = (p.boxes.card : ℝ) * ε := by simp

end TauCeti.BoxIntegral
