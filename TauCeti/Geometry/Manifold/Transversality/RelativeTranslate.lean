/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Incidence.RelativeTranslate
public import TauCeti.Geometry.Manifold.Transversality.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Relative transverse perturbations of maps from manifolds

Let `M` and `N` be boundaryless manifolds over finite-dimensional real models, Lindelöf (for
instance second countable) but not necessarily Hausdorff, and let `f : M → V`, `j : N → V` and
`β : M → ℝ` be `C^n` maps into a finite-dimensional real normed space, with `β ≥ 0`. If `f` is
transverse to `j` at every zero of `β`, then for every parameter `p ∈ V` outside a set that is null
for every additive Haar measure, the relative translate `TauCeti.relativeTranslate f β p`,
`x ↦ f x + β x • p`, is transverse to `j` at every point of `M`
(`TauCeti.addHaar_setOf_not_forall_isTransverseAt_relativeTranslate`). It agrees with `f` on the
zero set of `β`, so it is a perturbation of `f` relative to that set. The smoothness `n` must reach
the Morse–Sard threshold `dim M + dim N - dim V + 1`.

The family `(x, p) ↦ f x + β x • p` is universally transverse to `j`: where `β x > 0` the
parameter derivative `β x • id` is onto, and at a zero of `β ≥ 0`, which is a minimum and hence a
critical point of `β` since `M` is boundaryless, the source derivative is that of `f`. Countably
many extended charts cover `M` and `N`; on the product of the targets of two of them the
coordinate expressions are `C^n` on open sets, and transversality of the translate there is
regularity of `p` for the coordinate family, by
`TauCeti.surjective_coprod_fderiv_comp_extChartAt_symm_iff`. The flat local form,
`TauCeti.addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero`, makes the bad
parameters of each product null, and a countable union of null sets is null.

The manifolds need not be Hausdorff, and of countability only the Lindelöf property is used, which
second countability implies. Some countability is needed: for `N` the discrete line mapped
identically to `V = ℝ`, `M` a point, `f = 0` and `β = 1`, every parameter is bad.

## Main declarations

* `TauCeti.addHaar_setOf_not_forall_isTransverseAt_relativeTranslate`: the parameters whose
  relative translate fails to be transverse to `j` somewhere form a Haar-null set.
* `TauCeti.dense_setOf_forall_isTransverseAt_relativeTranslate`,
  `TauCeti.exists_forall_isTransverseAt_relativeTranslate`: good parameters are dense, and
  arbitrarily small ones fix `f` on the zero set of `β`.
* `IsClosed.exists_forall_isTransverseAt_relativeTranslate`: on a Hausdorff σ-compact manifold
  every closed set is the zero set of a suitable cutoff, so a map transverse to `j` along a closed
  set has arbitrarily small transverse perturbations fixing it on that set.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 6.35 (parametric transversality) and 6.36 (transversality homotopy).
-/

public section

open Function Set Filter Module MeasureTheory Measure Metric
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E F H G M N V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- A `C^n` map on a boundaryless `C^n` manifold, read in an extended chart, is `C^n` at every
point of the chart target. -/
private theorem contDiffAt_comp_extChartAt_symm_of_mem_target {n : ℕ∞ω} [IsManifold I n M]
    {g : M → V} (hg : ContMDiff I 𝓘(ℝ, V) n g) (a : M) {w : E}
    (hw : w ∈ (extChartAt I a).target) :
    ContDiffAt ℝ n (g ∘ (extChartAt I a).symm) w :=
  (contMDiffOn_iff_contDiffOn.1 (hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm a))).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hw)

/-- **Parametric transversality relative to a closed set, on manifolds.** Let `f : M → V`,
`j : N → V` and `β : M → ℝ` be `C^n` maps from boundaryless Lindelöf manifolds over
finite-dimensional models, with `β ≥ 0` and `n` at least `dim M + dim N - dim V + 1`. If `f` is
transverse to `j` at every zero of `β`, then the parameters `p` for which
`relativeTranslate f β p = f + β • p` fails to be transverse to `j` at some point of `M` form a
set of (outer) measure zero for every additive Haar measure on `V`. -/
theorem addHaar_setOf_not_forall_isTransverseAt_relativeTranslate
    [LindelofSpace M] [LindelofSpace N] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ] {f : M → V} {β : M → ℝ} {j : N → V} {n : ℕ∞ω}
    [IsManifold I n M] [IsManifold J n N]
    (hf : ContMDiff I 𝓘(ℝ, V) n f) (hβ : ContMDiff I 𝓘(ℝ) n β) (hj : ContMDiff J 𝓘(ℝ, V) n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hgood : ∀ x, β x = 0 → IsTransverseAt I J f j x)
    (hn : ((finrank ℝ E + finrank ℝ F - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    μ {p | ¬ ∀ x, IsTransverseAt I J (relativeTranslate f β p) j x} = 0 := by
  have h1 : (1 : ℕ∞ω) ≤ n := le_trans (by exact_mod_cast Nat.le_add_left 1 _) hn
  have : IsManifold I 1 M := .of_le h1
  have : IsManifold J 1 N := .of_le h1
  -- Countably many extended charts cover `M` and `N`.
  obtain ⟨A, hA, hAcov⟩ := countable_cover_nhds fun x : M ↦ extChartAt_source_mem_nhds (I := I) x
  obtain ⟨B, hB, hBcov⟩ := countable_cover_nhds fun y : N ↦ extChartAt_source_mem_nhds (I := J) y
  -- The bad parameters of the coordinate family on the product of the chart targets at `a` and
  -- `b` form a null set.
  let bad (a : M) (b : N) : Set V := {p | ¬ IsRegularIncidenceParameterOn
    (fun z : E × V ↦ relativeTranslate (f ∘ (extChartAt I a).symm) (β ∘ (extChartAt I a).symm)
      z.2 z.1) (j ∘ (extChartAt J b).symm)
    (((extChartAt I a).target ×ˢ (extChartAt J b).target) ×ˢ univ) p}
  have hbad (a : M) (b : N) : μ (bad a b) = 0 := by
    refine addHaar_setOf_not_isRegularIncidenceParameterOn_relativeTranslate_eq_zero μ
      (fun z hz _ ↦ contDiffAt_comp_extChartAt_symm_of_mem_target hf a hz.1.1)
      (fun z hz _ ↦ contDiffAt_comp_extChartAt_symm_of_mem_target hβ a hz.1.1)
      (fun z hz _ ↦ contDiffAt_comp_extChartAt_symm_of_mem_target hj b hz.1.2)
      (fun z _ h0 _ ↦ IsLocalMin.fderiv_eq_zero
        (Eventually.of_forall fun w ↦ h0.symm ▸ hnonneg _))
      (fun z hz h0 heq ↦ ?_) hn
    -- At a zero of the coordinate cutoff, transversality of `f` gives that of its coordinate
    -- expression.
    have hx := (extChartAt I a).map_target hz.1.1
    have hy := (extChartAt J b).map_target hz.1.2
    have h := (surjective_coprod_fderiv_comp_extChartAt_symm_iff hx hy).2
      (isTransverseAt_iff.1 (hgood _ h0) _ heq)
    rwa [(extChartAt I a).right_inv hz.1.1, (extChartAt J b).right_inv hz.1.2] at h
  refine measure_mono_null (t := ⋃ a ∈ A, ⋃ b ∈ B, bad a b) ?_
    ((measure_biUnion_null_iff hA).2 fun a _ ↦ (measure_biUnion_null_iff hB).2 fun b _ ↦ hbad a b)
  -- A failure of transversality at an incidence `(x, y)` is read in charts at `a ∋ x`, `b ∋ y`.
  intro p hp
  obtain ⟨x, hx⟩ := not_forall.1 hp
  obtain ⟨y, hxy, hsurj⟩ := not_forall₂.1 (mt isTransverseAt_iff.2 hx)
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hAcov.symm ▸ mem_univ x : x ∈ ⋃ a ∈ A, _)
  obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.1 (hBcov.symm ▸ mem_univ y : y ∈ ⋃ b ∈ B, _)
  refine mem_iUnion₂.2 ⟨a, ha, mem_iUnion₂.2 ⟨b, hb, fun hreg ↦ hsurj ?_⟩⟩
  have h : Surjective ((fderiv ℝ (relativeTranslate (f ∘ (extChartAt I a).symm)
      (β ∘ (extChartAt I a).symm) p) (extChartAt I a x)).coprod
        (-fderiv ℝ (j ∘ (extChartAt J b).symm) (extChartAt J b y))) :=
    hreg.surjective_coprod
      ⟨⟨(extChartAt I a).map_source hxa, (extChartAt J b).map_source hyb⟩, mem_univ p⟩
      (by simpa only [relativeTranslate_apply, comp_apply, (extChartAt I a).left_inv hxa,
        (extChartAt J b).left_inv hyb] using hxy)
  rw [relativeTranslate_comp] at h
  exact (surjective_coprod_fderiv_comp_extChartAt_symm_iff hxa hyb).1 h

/-- Under the hypotheses of `TauCeti.addHaar_setOf_not_forall_isTransverseAt_relativeTranslate`,
the parameters `p` for which `relativeTranslate f β p` is transverse to `j` at every point are
dense in `V`. -/
theorem dense_setOf_forall_isTransverseAt_relativeTranslate [LindelofSpace M] [LindelofSpace N]
    {f : M → V} {β : M → ℝ} {j : N → V} {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    (hf : ContMDiff I 𝓘(ℝ, V) n f) (hβ : ContMDiff I 𝓘(ℝ) n β) (hj : ContMDiff J 𝓘(ℝ, V) n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hgood : ∀ x, β x = 0 → IsTransverseAt I J f j x)
    (hn : ((finrank ℝ E + finrank ℝ F - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {p | ∀ x, IsTransverseAt I J (relativeTranslate f β p) j x} := by
  borelize V
  exact Measure.dense_of_ae (μ := (addHaar : Measure V)) <| ae_iff.2 <|
    addHaar_setOf_not_forall_isTransverseAt_relativeTranslate addHaar hf hβ hj hnonneg hgood hn

/-- **Small relative transverse perturbations on manifolds.** Under the hypotheses of
`TauCeti.addHaar_setOf_not_forall_isTransverseAt_relativeTranslate`, for every `r > 0` there is
`p` with `‖p‖ < r` such that `relativeTranslate f β p` is transverse to `j` at every point of `M`
and agrees with `f` on the zero set of `β`. -/
theorem exists_forall_isTransverseAt_relativeTranslate [LindelofSpace M] [LindelofSpace N]
    {f : M → V} {β : M → ℝ} {j : N → V} {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
    (hf : ContMDiff I 𝓘(ℝ, V) n f) (hβ : ContMDiff I 𝓘(ℝ) n β) (hj : ContMDiff J 𝓘(ℝ, V) n j)
    (hnonneg : ∀ x, 0 ≤ β x) (hgood : ∀ x, β x = 0 → IsTransverseAt I J f j x)
    (hn : ((finrank ℝ E + finrank ℝ F - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) {r : ℝ} (hr : 0 < r) :
    ∃ p : V, ‖p‖ < r ∧ (∀ x, IsTransverseAt I J (relativeTranslate f β p) j x) ∧
      EqOn (relativeTranslate f β p) f {x | β x = 0} := by
  obtain ⟨p, hp, hpr⟩ := (dense_setOf_forall_isTransverseAt_relativeTranslate hf hβ hj hnonneg
    hgood hn).exists_mem_open isOpen_ball ⟨0, mem_ball_self hr⟩
  exact ⟨p, mem_ball_zero_iff.1 hpr, hp, eqOn_relativeTranslate_of_eq_zero p fun _ h ↦ h⟩

/-- **Transverse perturbations fixing a closed set.** Let `M` be a Hausdorff σ-compact boundaryless
smooth manifold and `C ⊆ M` closed. If a `C^n` map `f : M → V` is transverse to `j` at every point
of `C`, with `n` at least `dim M + dim N - dim V + 1`, then there is a smooth cutoff
`β : M → [0, 1]` vanishing exactly on `C` such that for every `r > 0` some `p` with `‖p‖ < r`
makes `relativeTranslate f β p` transverse to `j` at every point, while agreeing with `f` on
`C`. -/
theorem _root_.IsClosed.exists_forall_isTransverseAt_relativeTranslate [T2Space M]
    [SigmaCompactSpace M] [IsManifold I ∞ M] [LindelofSpace N] {C : Set M} (hC : IsClosed C)
    {f : M → V} {j : N → V} {n : ℕ∞ω} [IsManifold J n N]
    (hf : ContMDiff I 𝓘(ℝ, V) n f) (hj : ContMDiff J 𝓘(ℝ, V) n j)
    (hgood : ∀ x ∈ C, IsTransverseAt I J f j x)
    (hn : ((finrank ℝ E + finrank ℝ F - finrank ℝ V + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∃ β : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ β ∧ range β ⊆ Icc 0 1 ∧ (∀ x, β x = 0 ↔ x ∈ C) ∧
      ∀ ⦃r : ℝ⦄, 0 < r → ∃ p : V, ‖p‖ < r ∧
        (∀ x, IsTransverseAt I J (relativeTranslate f β p) j x) ∧
        EqOn (relativeTranslate f β p) f C := by
  obtain ⟨β, hβ, hrange, hzero, -⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed I (n := ⊤) hC isClosed_empty
      (disjoint_empty C)
  refine ⟨β, hβ, hrange, fun x ↦ (hzero x).symm, fun r hr ↦ ?_⟩
  have : IsManifold I (min n ∞) M := .of_le (min_le_right _ _)
  have : IsManifold J (min n ∞) N := .of_le (min_le_left _ _)
  obtain ⟨p, hpr, hp, hpC⟩ := TauCeti.exists_forall_isTransverseAt_relativeTranslate
    (hf.of_le (min_le_left _ _)) (hβ.of_le (min_le_right _ _)) (hj.of_le (min_le_left _ _))
    (fun x ↦ (hrange (mem_range_self x)).1) (fun x hx ↦ hgood x ((hzero x).2 hx))
    (le_min hn (by simp)) hr
  exact ⟨p, hpr, hp, fun x hx ↦ hpC ((hzero x).1 hx)⟩

end TauCeti
