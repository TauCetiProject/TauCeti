/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Incidence.Basic
public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Holomorphic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The complex incidence model of the plane blow-up

The incidence locus in `ℂ² × ℙ¹` has two explicit parametrizations:
`(u, v) ↦ ((u, u * v), [1 : v])` and `(s, t) ↦ ((s * t, t), [s : 1])`.
Their images are the inverse images of the two projective coordinate opens. They give a
complex atlas for the existing subspace topology, with transition
`(u, v) ↦ (v⁻¹, u * v)` where `v ≠ 0`.

For this atlas the incidence comparison from the toric blow-up is biholomorphic. Thus the
identification respects the complex structures, including on the exceptional fibre, rather
than merely identifying the underlying topological spaces. The atlas is assembled by
`TauCeti.chartedSpaceOfIsOpenEmbedding` from the explicit incidence parametrizations.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric

local notation "B" => affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan
local notation "I" => 𝓘(ℂ, ℂ × ℂ)
local notation "IB" => 𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)

/-- The two incidence parametrizations. `false` is the positive projective chart, with
coordinates `(u, v)`; `true` is the negative chart, with coordinates `(s, t)`. -/
noncomputable def planeBlowUpIncidenceChartMap : Bool → (ℂ × ℂ) → planeBlowUpIncidence
  | false, z => ⟨((z.1, z.1 * z.2), projectiveLinePositiveChartMap z.2), by simp⟩
  | true, z => ⟨((z.1 * z.2, z.2), projectiveLineNegativeChartMap z.1), by simp [mul_comm]⟩

@[simp]
theorem planeBlowUpIncidenceChartMap_false (z : ℂ × ℂ) :
    (planeBlowUpIncidenceChartMap false z).val =
      ((z.1, z.1 * z.2), projectiveLinePositiveChartMap z.2) := (rfl)

@[simp]
theorem planeBlowUpIncidenceChartMap_true (z : ℂ × ℂ) :
    (planeBlowUpIncidenceChartMap true z).val =
      ((z.1 * z.2, z.2), projectiveLineNegativeChartMap z.1) := (rfl)

private noncomputable def toricChart (j : Bool) : (ℂ × ℂ) → B :=
  if j then affinePlaneBlowUpLowerChart else affinePlaneBlowUpUpperChart

private theorem comparison_chart (j : Bool) (z : ℂ × ℂ) :
    affinePlaneBlowUpIncidenceHomeomorph (toricChart j z) =
      planeBlowUpIncidenceChartMap j z := by
  cases j <;> apply Subtype.ext <;> simp [toricChart]

/-- Each explicit incidence parametrization is an open embedding for the subspace topology. -/
theorem isOpenEmbedding_planeBlowUpIncidenceChartMap (j : Bool) :
    IsOpenEmbedding (planeBlowUpIncidenceChartMap j) := by
  have h : IsOpenEmbedding (toricChart j) := by
    cases j
    · exact isOpenEmbedding_affinePlaneBlowUpUpperChart
    · exact isOpenEmbedding_affinePlaneBlowUpLowerChart
  have heq : (affinePlaneBlowUpIncidenceHomeomorph : B → planeBlowUpIncidence) ∘ toricChart j =
      planeBlowUpIncidenceChartMap j := funext (comparison_chart j)
  rw [← heq]
  exact affinePlaneBlowUpIncidenceHomeomorph.isOpenEmbedding.comp h

/-- The image of an incidence chart is exactly the inverse image of the corresponding
projective coordinate open. In particular these domains do not depend on the toric comparison. -/
@[simp↓]
theorem mem_range_planeBlowUpIncidenceChartMap (j : Bool) (q : planeBlowUpIncidence) :
    q ∈ range (planeBlowUpIncidenceChartMap j) ↔
      q.val.2 ∈ range (if j then projectiveLineNegativeChartMap
        else projectiveLinePositiveChartMap) := by
  constructor
  · rintro ⟨z, rfl⟩
    cases j
    · exact ⟨z.2, rfl⟩
    · exact ⟨z.1, rfl⟩
  · rintro ⟨v, hv⟩
    cases j
    · have hq := ((mem_planeBlowUpIncidence q.val).1 q.property).1 v hv.symm
      refine ⟨(q.val.1.1, v), Subtype.ext ?_⟩
      exact Prod.ext (Prod.ext rfl hq.symm) hv
    · have hq := ((mem_planeBlowUpIncidence q.val).1 q.property).2 v hv.symm
      refine ⟨(v, q.val.1.2), Subtype.ext ?_⟩
      exact Prod.ext (Prod.ext (by simpa [mul_comm] using hq.symm) rfl) hv

/-- The two explicit incidence charts cover the whole incidence locus, also above the origin. -/
theorem exists_planeBlowUpIncidenceChartMap_eq (q : planeBlowUpIncidence) :
    ∃ j z, planeBlowUpIncidenceChartMap j z = q := by
  have hq : q.val.2 ∈ range projectiveLinePositiveChartMap ∪
      range projectiveLineNegativeChartMap := by rw [projectiveLineChartMap_cover]; trivial
  rcases hq with hq | hq
  · obtain ⟨z, hz⟩ := (mem_range_planeBlowUpIncidenceChartMap false q).2 hq
    exact ⟨false, z, hz⟩
  · obtain ⟨z, hz⟩ := (mem_range_planeBlowUpIncidenceChartMap true q).2 hq
    exact ⟨true, z, hz⟩

private theorem incidence_deck (n : ℕ∞ω) (j k : Bool) (x y : ℂ × ℂ)
    (h : planeBlowUpIncidenceChartMap j x = planeBlowUpIncidenceChartMap k y) :
    ∃ T : (ℂ × ℂ) → (ℂ × ℂ), ContMDiffAt I I n T x ∧
      planeBlowUpIncidenceChartMap k ∘ T =ᶠ[𝓝 x] planeBlowUpIncidenceChartMap j := by
  have ht : toricChart j x = toricChart k y :=
    affinePlaneBlowUpIncidenceHomeomorph.injective
      ((comparison_chart j x).trans (h.trans (comparison_chart k y).symm))
  cases j <;> cases k
  · exact ⟨id, contMDiffAt_id, Filter.EventuallyEq.rfl⟩
  · have hx : x ∈ (affinePlaneBlowUpTransition n).source := by
      simpa [toricChart] using
        ((affinePlaneBlowUpUpperChart_eq_lowerChart_iff x y).1 ht).1
    refine ⟨affinePlaneBlowUpTransition n,
      (affinePlaneBlowUpTransition n).contMDiffOn.contMDiffAt
        ((affinePlaneBlowUpTransition n).open_source.mem_nhds hx), ?_⟩
    filter_upwards [(affinePlaneBlowUpTransition n).open_source.mem_nhds hx] with z hz
    rw [Function.comp_apply, ← comparison_chart, ← comparison_chart]
    exact congrArg affinePlaneBlowUpIncidenceHomeomorph
      (affinePlaneBlowUpLowerChart_transition n z hz)
  · have hx : x ∈ (affinePlaneBlowUpTransition n).target := by
      have hm : affinePlaneBlowUpLowerChart x ∈ range affinePlaneBlowUpUpperChart := ⟨y, ht.symm⟩
      simpa using (affinePlaneBlowUpLowerChart_mem_range_upperChart_iff x).1 hm
    refine ⟨(affinePlaneBlowUpTransition n).symm,
      (affinePlaneBlowUpTransition n).symm.contMDiffOn.contMDiffAt
        ((affinePlaneBlowUpTransition n).open_target.mem_nhds hx), ?_⟩
    filter_upwards [(affinePlaneBlowUpTransition n).open_target.mem_nhds hx] with z hz
    rw [Function.comp_apply, ← comparison_chart, ← comparison_chart]
    exact congrArg affinePlaneBlowUpIncidenceHomeomorph
      (affinePlaneBlowUpUpperChart_transition_invFun n z hz)
  · exact ⟨id, contMDiffAt_id, Filter.EventuallyEq.rfl⟩

/-- The incidence atlas given by the two explicit projective-coordinate parametrizations,
on the existing subspace topology. -/
@[instance_reducible]
noncomputable def planeBlowUpIncidenceChartedSpace : ChartedSpace (ℂ × ℂ) planeBlowUpIncidence :=
  chartedSpaceOfIsOpenEmbedding isOpenEmbedding_planeBlowUpIncidenceChartMap
    exists_planeBlowUpIncidenceChartMap_eq

/-- The classical incidence locus is a two-dimensional complex manifold. -/
theorem isManifold_planeBlowUpIncidence (n : ℕ∞ω) :
    letI := planeBlowUpIncidenceChartedSpace
    IsManifold I n planeBlowUpIncidence :=
  isManifold_chartedSpaceOfIsOpenEmbedding isOpenEmbedding_planeBlowUpIncidenceChartMap
    exists_planeBlowUpIncidenceChartMap_eq (incidence_deck n)

/-- Each incidence parametrization is a biholomorphism onto its projective-coordinate open. -/
noncomputable def planeBlowUpIncidencePartialDiffeomorph (j : Bool) (n : ℕ∞ω) :
    letI := planeBlowUpIncidenceChartedSpace
    PartialDiffeomorph I I (ℂ × ℂ) planeBlowUpIncidence n :=
  partialDiffeomorphOfIsOpenEmbedding isOpenEmbedding_planeBlowUpIncidenceChartMap
    exists_planeBlowUpIncidenceChartMap_eq (incidence_deck n) j

@[simp]
theorem planeBlowUpIncidencePartialDiffeomorph_source (j : Bool) (n : ℕ∞ω) :
    (planeBlowUpIncidencePartialDiffeomorph j n).source = univ :=
  partialDiffeomorphOfIsOpenEmbedding_source _ _ _ _

@[simp]
theorem planeBlowUpIncidencePartialDiffeomorph_target (j : Bool) (n : ℕ∞ω) :
    (planeBlowUpIncidencePartialDiffeomorph j n).target =
      range (planeBlowUpIncidenceChartMap j) :=
  partialDiffeomorphOfIsOpenEmbedding_target _ _ _ _

@[simp]
theorem planeBlowUpIncidencePartialDiffeomorph_apply (j : Bool) (n : ℕ∞ω) (z : ℂ × ℂ) :
    planeBlowUpIncidencePartialDiffeomorph j n z = planeBlowUpIncidenceChartMap j z :=
  congrFun (coe_partialDiffeomorphOfIsOpenEmbedding
    isOpenEmbedding_planeBlowUpIncidenceChartMap exists_planeBlowUpIncidenceChartMap_eq
    (incidence_deck n) j) z

@[simp]
theorem planeBlowUpIncidencePartialDiffeomorph_invFun (j : Bool) (n : ℕ∞ω) (z : ℂ × ℂ) :
    (planeBlowUpIncidencePartialDiffeomorph j n).invFun
      (planeBlowUpIncidenceChartMap j z) = z := by
  rw [← planeBlowUpIncidencePartialDiffeomorph_apply j n z]
  exact (planeBlowUpIncidencePartialDiffeomorph j n).left_inv (by simp)

/-- The incidence comparison is a local biholomorphism for the explicit incidence atlas. -/
theorem isLocalDiffeomorph_affinePlaneBlowUpIncidenceHomeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := planeBlowUpIncidenceChartedSpace
    IsLocalDiffeomorph IB I n affinePlaneBlowUpIncidenceHomeomorph := by
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let := planeBlowUpIncidenceChartedSpace
  intro p
  obtain ⟨j, z, hz⟩ : ∃ j z, toricChart j z = p := by
    rcases exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq p
        with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact ⟨false, z, hz⟩
    · exact ⟨true, z, hz⟩
  rw [← hz]
  have hc := (planeBlowUpIncidencePartialDiffeomorph j n).isLocalDiffeomorphAt
    I I n (x := z) (by simp)
  have heq : (affinePlaneBlowUpIncidenceHomeomorph : B → planeBlowUpIncidence) ∘ toricChart j =
      planeBlowUpIncidencePartialDiffeomorph j n := by
    funext w
    simp only [Function.comp_apply, planeBlowUpIncidencePartialDiffeomorph_apply, comparison_chart]
  rw [← heq] at hc
  apply hc.of_comp_right
  cases j
  · have he : (affinePlaneBlowUpUpperPartialDiffeomorph n : (ℂ × ℂ) → B) =
        toricChart false := by funext w; simp [toricChart]
    simpa +instances only [← modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, he] using
      isLocalDiffeomorph_affinePlaneBlowUpUpperPartialDiffeomorph n z
  · have he : (affinePlaneBlowUpLowerPartialDiffeomorph n : (ℂ × ℂ) → B) =
        toricChart true := by funext w; simp [toricChart]
    simpa +instances only [← modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, he] using
      isLocalDiffeomorph_affinePlaneBlowUpLowerPartialDiffeomorph n z

/-- The toric plane blow-up is biholomorphic to the classical incidence model, equipped with
its explicit two-chart complex atlas and its subspace topology. -/
noncomputable def affinePlaneBlowUpIncidenceDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := planeBlowUpIncidenceChartedSpace
    Diffeomorph IB I B planeBlowUpIncidence n := by
  letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  letI := planeBlowUpIncidenceChartedSpace
  exact (isLocalDiffeomorph_affinePlaneBlowUpIncidenceHomeomorph n).diffeomorphOfBijective
    affinePlaneBlowUpIncidenceHomeomorph.bijective

/-- The biholomorphic comparison is the existing blow-down and projective-direction comparison. -/
@[simp]
theorem affinePlaneBlowUpIncidenceDiffeomorph_apply (n : ℕ∞ω) (p : B) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := planeBlowUpIncidenceChartedSpace
    affinePlaneBlowUpIncidenceDiffeomorph n p = affinePlaneBlowUpIncidenceHomeomorph p := by
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let := planeBlowUpIncidenceChartedSpace
  simp [affinePlaneBlowUpIncidenceDiffeomorph]

/-- The inverse biholomorphic comparison is the inverse of the incidence homeomorphism. -/
@[simp]
theorem affinePlaneBlowUpIncidenceDiffeomorph_symm_apply (n : ℕ∞ω)
    (q : planeBlowUpIncidence) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := planeBlowUpIncidenceChartedSpace
    (affinePlaneBlowUpIncidenceDiffeomorph n).symm q =
      affinePlaneBlowUpIncidenceHomeomorph.symm q := by
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let := planeBlowUpIncidenceChartedSpace
  apply affinePlaneBlowUpIncidenceHomeomorph.injective
  rw [← affinePlaneBlowUpIncidenceDiffeomorph_apply n,
    Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- The inclusion of the incidence model in `ℂ² × ℙ¹` is holomorphic for its explicit atlas. -/
theorem contMDiff_planeBlowUpIncidence_val (n : ℕ∞ω) :
    letI := planeBlowUpIncidenceChartedSpace
    letI := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    ContMDiff I ((𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)).prod
      𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)) n
      (Subtype.val : planeBlowUpIncidence → _) := by
  let := planeBlowUpIncidenceChartedSpace
  let := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  exact ((contMDiff_affinePlaneBlowUpIncidenceMap n).comp
    (affinePlaneBlowUpIncidenceDiffeomorph n).symm.contMDiff).congr fun q ↦ by simp

end TauCeti.Toric
