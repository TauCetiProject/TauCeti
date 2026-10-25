/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Sign
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Semianalytic subsets of the real line

Near any point, a semianalytic subset of the real line is a union of some of the three cells
given by the left interval, the center, and the right interval. Conversely, every such germ
is semianalytic. This gives the one-dimensional local normal form without a polynomial
assumption on the analytic functions defining the set.

In particular the frontier is locally contained in the center point. A set that is semianalytic
at every point therefore has discrete frontier, meeting each compact set in finitely many points.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- In any prescribed neighborhood of the center, a semianalytic subset of the real line
is a union of some of the left interval, the center, and the right interval. -/
theorem SemianalyticAt.exists_Ioo_mem_iff_sign_mem {s U : Set ℝ} {x : ℝ}
    (hs : SemianalyticAt s x) (hU : U ∈ 𝓝 x) :
    ∃ a b, x ∈ Ioo a b ∧ Ioo a b ⊆ U ∧ ∃ C : Set SignType,
      ∀ y ∈ Ioo a b, y ∈ s ↔ SignType.sign (y - x) ∈ C := by
  obtain ⟨V, hV, t, ht, hst⟩ := semianalyticAt_def.1 hs
  obtain ⟨m, f, hf, Φ, rfl⟩ := ht.exists_eq_setOf_sign
  obtain ⟨a, b, hx, hab, hsign⟩ := exists_Ioo_sign_eq_of_finite_analyticAt
    (fun i => hf i x (mem_of_mem_nhds hV)) (inter_mem hU hV)
  have hmem (y) (hy : y ∈ Ioo a b) :
      y ∈ s ↔ Φ (fun i => SignType.sign (f i y)) := by
    have h := Set.ext_iff.1 hst y
    simpa only [mem_inter_iff, mem_ofPred_eq, (hab hy).2, and_true] using h
  refine ⟨a, b, hx, fun y hy => (hab hy).1,
    (fun y => SignType.sign (y - x)) '' (s ∩ Ioo a b), fun y hy => ?_⟩
  constructor
  · intro hys
    exact ⟨y, ⟨hys, hy⟩, rfl⟩
  · rintro ⟨z, ⟨hzs, hz⟩, hzy⟩
    have heq := funext fun i => hsign i z hz y hy hzy
    exact (hmem y hy).2 (heq ▸ (hmem z hz).1 hzs)

/-- A germ of a subset of the real line is semianalytic exactly when membership near the
center depends only on which side of the center a point lies, including the center itself. -/
theorem semianalyticAt_real_iff {s : Set ℝ} {x : ℝ} :
    SemianalyticAt s x ↔ ∃ C : Set SignType,
      s =ᶠ[𝓝 x] {y | SignType.sign (y - x) ∈ C} := by
  constructor
  · intro hs
    obtain ⟨a, b, hx, _, C, hmem⟩ := hs.exists_Ioo_mem_iff_sign_mem (U := univ) univ_mem
    refine ⟨C, eventuallyEqSet_iff.2 ?_⟩
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hmem y hy
  · rintro ⟨C, hC⟩
    have h : IsAnalyticBooleanCombination (univ : Set ℝ)
        {y | SignType.sign (y - x) ∈ C} := by
      simpa using isAnalyticBooleanCombination_setOf_sign
        (f := fun _ : Unit => fun y : ℝ => y - x)
        (fun _ => analyticOnNhd_id.sub analyticOnNhd_const) (fun ε => ε () ∈ C)
    exact (semianalyticAt_def.2 ⟨univ, univ_mem, _, h, rfl⟩).congr hC.symm

/-- The frontier of a subset semianalytic at a real point is locally contained in that point.
The assertion applies even when the center does not belong to the set or to its frontier. -/
theorem SemianalyticAt.exists_Ioo_frontier_subset {s : Set ℝ} {x : ℝ}
    (hs : SemianalyticAt s x) :
    ∃ a b, x ∈ Ioo a b ∧ frontier s ∩ Ioo a b ⊆ {x} := by
  obtain ⟨a, b, hx, _, C, hmem⟩ := hs.exists_Ioo_mem_iff_sign_mem (U := univ) univ_mem
  have hside {y : ℝ} {J : Set ℝ} (hJ : IsOpen J) (hyJ : y ∈ J)
      (hJab : J ⊆ Ioo a b)
      (hsgn : ∀ z ∈ J, SignType.sign (z - x) = SignType.sign (y - x)) :
      y ∉ frontier s := by
    rw [frontier_eq_closure_inter_closure]
    rintro ⟨hcl, hclc⟩
    by_cases hys : y ∈ s
    · obtain ⟨z, hzJ, hzs⟩ := mem_closure_iff.1 hclc J hJ hyJ
      exact hzs <| (hmem z (hJab hzJ)).2 <| (hsgn z hzJ).symm ▸ (hmem y (hJab hyJ)).1 hys
    · obtain ⟨z, hzJ, hzs⟩ := mem_closure_iff.1 hcl J hJ hyJ
      exact hys <| (hmem y (hJab hyJ)).2 <| (hsgn z hzJ) ▸ (hmem z (hJab hzJ)).1 hzs
  refine ⟨a, b, hx, fun y ⟨hyf, hy⟩ => ?_⟩
  rcases lt_trichotomy y x with hyx | hyx | hxy
  · exact False.elim <| hside isOpen_Ioo ⟨hy.1, hyx⟩
      (fun z hz => ⟨hz.1, hz.2.trans hx.2⟩)
      (fun z hz => (sign_neg (sub_neg.2 hz.2)).trans (sign_neg (sub_neg.2 hyx)).symm) hyf
  · exact hyx
  · exact False.elim <| hside isOpen_Ioo ⟨hxy, hy.2⟩
      (fun z hz => ⟨hx.1.trans hz.1, hz.2⟩)
      (fun z hz => (sign_pos (sub_pos.2 hz.1)).trans (sign_pos (sub_pos.2 hxy)).symm) hyf

/-- A semianalytic subset of the real line has discrete frontier. -/
theorem IsSemianalytic.isDiscrete_frontier {s : Set ℝ} (hs : IsSemianalytic s) :
    IsDiscrete (frontier s) := by
  refine isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx => ?_
  obtain ⟨a, b, hab, hsub⟩ := (hs.semianalyticAt x).exists_Ioo_frontier_subset
  refine ⟨Ioo a b, isOpen_Ioo, Subset.antisymm ?_ ?_⟩
  · exact fun y hy => hsub ⟨hy.2, hy.1⟩
  · exact singleton_subset_iff.2 ⟨hab, hx⟩

/-- Only finitely many frontier points of a semianalytic subset of the real line lie in any
given compact set. No boundedness or closedness assumption on the semianalytic set is needed. -/
theorem IsSemianalytic.finite_frontier_inter {s K : Set ℝ} (hs : IsSemianalytic s)
    (hK : IsCompact K) : (frontier s ∩ K).Finite :=
  (hK.inter_left isClosed_frontier).finite (hs.isDiscrete_frontier.mono inter_subset_left)

end TauCeti
