/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffinePlane.ProjectiveDirection
public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Basic
public import TauCeti.Geometry.Toric.Analytic.Examples.ProjectiveLine.OnePoint

/-!
# Projective directions of the toric plane blow-up

The toric morphism induced by `(a, b) ↦ b - a` records the projective direction of a point
of the blow-up. On the upper chart `(u, v)` it is the positive projective-line coordinate `v`;
on the lower chart `(s, t)` it is the negative coordinate `s`. The map is holomorphic,
including along the exceptional fibre.

Paired with blow-down, it maps onto the classical incidence locus in `ℂ² × ℙ¹`: the
points `((x, y), [a : b])` satisfying `x * b = y * a`. We express this equation in the two
standard affine charts of the existing toric projective line. This supplies the canonical
map for comparing the toric blow-up with the incidence model, without asserting injectivity.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Multiplicative Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

local notation "B" => affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan
local notation "P" => projectiveLineFan.analyticRealization isRegular_projectiveLineFan
local notation "gp" => Sigma.snd
  (projectiveLineFan.analyticChartGenerators projectiveLinePositiveCone)
local notation "gn" => Sigma.snd
  (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone)

/-- The holomorphic projective-direction map of the toric plane blow-up. -/
noncomputable abbrev affinePlaneBlowUpDirectionMap : B → P :=
  affinePlaneBlowUpDirectionFanHom.analyticMap
    isRegular_affinePlaneBlowUpFan isRegular_projectiveLineFan

/-- In the upper blow-up chart, the projective direction has positive coordinate `v`. -/
@[simp]
theorem affinePlaneBlowUpDirectionMap_upperChart (z : ℂ × ℂ) :
    affinePlaneBlowUpDirectionMap (affinePlaneBlowUpUpperChart z) =
      projectiveLinePositiveChartMap z.2 := by
  let _ := affinePointTopology gp
  rw [affinePlaneBlowUpDirectionMap, affinePlaneBlowUpUpperChart_def]
  erw [FanHom.analyticMap_analyticAffineChartι_of_mapsTo
    (υ := projectiveLinePositiveCone) _ _ _ mapsTo_affinePlaneBlowUpDirectionFanHom_upper]
  -- The bundled chart lattice is the standard rank-one lattice, with equal lattice proofs.
  erw [← projectiveLinePositiveChartMap_apply_single, FanHom.analyticChartMap_apply,
    AffineSemigroupComplexPoint.comap_apply_single,
    affinePlaneBlowUpUpperPointHomeomorph_symm_apply_single]
  simp

/-- In the lower blow-up chart, the projective direction has negative coordinate `s`. -/
@[simp]
theorem affinePlaneBlowUpDirectionMap_lowerChart (z : ℂ × ℂ) :
    affinePlaneBlowUpDirectionMap (affinePlaneBlowUpLowerChart z) =
      projectiveLineNegativeChartMap z.1 := by
  let _ := affinePointTopology gn
  rw [affinePlaneBlowUpDirectionMap, affinePlaneBlowUpLowerChart_def]
  erw [FanHom.analyticMap_analyticAffineChartι_of_mapsTo
    (υ := projectiveLineNegativeCone) _ _ _ mapsTo_affinePlaneBlowUpDirectionFanHom_lower]
  -- The bundled chart lattice is the standard rank-one lattice, with equal lattice proofs.
  erw [← projectiveLineNegativeChartMap_apply_single, FanHom.analyticChartMap_apply,
    AffineSemigroupComplexPoint.comap_apply_single,
    affinePlaneBlowUpLowerPointHomeomorph_symm_apply_single]
  simp

/-- The direction map is holomorphic on the whole blow-up, not just off the exceptional fibre. -/
theorem contMDiff_affinePlaneBlowUpDirectionMap (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ) n affinePlaneBlowUpDirectionMap :=
  affinePlaneBlowUpDirectionFanHom.contMDiff_analyticMap
    isRegular_affinePlaneBlowUpFan isRegular_projectiveLineFan n

/-- The classical plane blow-up incidence locus `x * b = y * a` in `ℂ² × ℙ¹`, expressed
in the standard projective coordinates `v = b / a` and `s = a / b`. -/
def planeBlowUpIncidence : Set ((ℂ × ℂ) × P) :=
  {q | (∀ v, q.2 = projectiveLinePositiveChartMap v → q.1.2 = q.1.1 * v) ∧
    (∀ s, q.2 = projectiveLineNegativeChartMap s → q.1.1 = q.1.2 * s)}

/-- Membership in the incidence locus is the incidence equation in both projective charts. -/
theorem mem_planeBlowUpIncidence (q : (ℂ × ℂ) × P) :
    q ∈ planeBlowUpIncidence ↔
      (∀ v, q.2 = projectiveLinePositiveChartMap v → q.1.2 = q.1.1 * v) ∧
      (∀ s, q.2 = projectiveLineNegativeChartMap s → q.1.1 = q.1.2 * s) := Iff.rfl

/-- In the positive projective chart the incidence equation is `y = x * v`. -/
@[simp]
theorem mem_planeBlowUpIncidence_positiveChart (x : ℂ × ℂ) (v : ℂ) :
    (x, projectiveLinePositiveChartMap v) ∈ planeBlowUpIncidence ↔ x.2 = x.1 * v := by
  constructor
  · intro h
    exact h.1 v rfl
  · intro h
    constructor
    · intro w hw
      obtain rfl := isOpenEmbedding_projectiveLinePositiveChartMap.injective hw
      exact h
    · intro s hs
      have hv := (projectiveLinePositiveChartMap_eq_negativeChartMap_iff v s).1 hs
      rw [h, mul_assoc, hv, mul_one]

/-- In the negative projective chart the incidence equation is `x = y * s`. -/
@[simp]
theorem mem_planeBlowUpIncidence_negativeChart (x : ℂ × ℂ) (s : ℂ) :
    (x, projectiveLineNegativeChartMap s) ∈ planeBlowUpIncidence ↔ x.1 = x.2 * s := by
  constructor
  · intro h
    exact h.2 s rfl
  · intro h
    constructor
    · intro v hv
      have hs := (projectiveLinePositiveChartMap_eq_negativeChartMap_iff v s).1 hv.symm
      rw [h, mul_assoc, mul_comm s v, hs, mul_one]
    · intro t ht
      obtain rfl := isOpenEmbedding_projectiveLineNegativeChartMap.injective ht
      exact h

/-- The canonical map to the incidence model: blow-down in ordinary plane coordinates paired
with the projective-direction map. -/
noncomputable def affinePlaneBlowUpIncidenceMap (p : B) : (ℂ × ℂ) × P :=
  (affinePlaneDiffeomorph ⊤
    (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
      isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan p),
    affinePlaneBlowUpDirectionMap p)

/-- The incidence map pairs the blow-down coordinate with the projective direction. -/
theorem affinePlaneBlowUpIncidenceMap_def (p : B) :
    affinePlaneBlowUpIncidenceMap p =
      (affinePlaneDiffeomorph ⊤
        (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
          isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan p),
        affinePlaneBlowUpDirectionMap p) := (rfl)

/-- The upper chart maps to `((u, u * v), [1 : v])` in the incidence model. -/
@[simp]
theorem affinePlaneBlowUpIncidenceMap_upperChart (z : ℂ × ℂ) :
    affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpUpperChart z) =
      ((z.1, z.1 * z.2), projectiveLinePositiveChartMap z.2) := by
  rw [affinePlaneBlowUpIncidenceMap_def,
    affinePlaneDiffeomorph_analyticMap_affinePlaneBlowUpUpperChart,
    affinePlaneBlowUpDirectionMap_upperChart]

/-- The lower chart maps to `((s * t, t), [s : 1])` in the incidence model. -/
@[simp]
theorem affinePlaneBlowUpIncidenceMap_lowerChart (z : ℂ × ℂ) :
    affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpLowerChart z) =
      ((z.1 * z.2, z.2), projectiveLineNegativeChartMap z.1) := by
  rw [affinePlaneBlowUpIncidenceMap_def,
    affinePlaneDiffeomorph_analyticMap_affinePlaneBlowUpLowerChart,
    affinePlaneBlowUpDirectionMap_lowerChart]

/-- The canonical map to the incidence model is continuous for the monomial topologies. -/
theorem continuous_affinePlaneBlowUpIncidenceMap : Continuous affinePlaneBlowUpIncidenceMap := by
  let := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
  exact (((affinePlaneDiffeomorph ⊤).continuous.comp
    (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
      isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan).hom.continuous).prodMk
        (affinePlaneBlowUpDirectionFanHom.analyticMap
          isRegular_affinePlaneBlowUpFan isRegular_projectiveLineFan).hom.continuous).congr
            fun p ↦ (affinePlaneBlowUpIncidenceMap_def p).symm

/-- The map to the incidence model is holomorphic for the existing fan manifold structures. -/
theorem contMDiff_affinePlaneBlowUpIncidenceMap (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    letI := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
      ((𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)).prod
        𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)) n
      affinePlaneBlowUpIncidenceMap := by
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
  exact ((((affinePlaneDiffeomorph ⊤).contMDiff.of_le le_top).comp
    (affinePlaneBlowUpFan_isSubdivision.toFanHom.contMDiff_analyticMap
      isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan n)).prodMk
        (contMDiff_affinePlaneBlowUpDirectionMap n)).congr
          fun p ↦ (affinePlaneBlowUpIncidenceMap_def p).symm

/-- The incidence map is proper, since its projection to the plane is the proper blow-down. -/
theorem isProperMap_affinePlaneBlowUpIncidenceMap : IsProperMap affinePlaneBlowUpIncidenceMap := by
  apply isProperMap_of_comp_of_t2 continuous_affinePlaneBlowUpIncidenceMap continuous_fst
  let := affinePlaneFan.analyticChartedSpace isRegular_affinePlaneFan
  have h := (affinePlaneDiffeomorph ⊤).toHomeomorph.isClosedEmbedding.isProperMap.comp
    isProperMap_analyticMap_affinePlaneBlowUpFan
  convert h using 1
  funext p
  simp only [Function.comp_apply, affinePlaneBlowUpIncidenceMap_def, Diffeomorph.coe_toHomeomorph]

/-- Blow-down paired with projective direction maps onto exactly the classical incidence locus.
This includes every projective direction above the origin. -/
theorem range_affinePlaneBlowUpIncidenceMap :
    range affinePlaneBlowUpIncidenceMap = planeBlowUpIncidence := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    rcases exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq p
        with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · simp
    · simp [mul_comm]
  · rintro hq
    obtain ⟨x, p⟩ := q
    have hp : p ∈ range projectiveLinePositiveChartMap ∪
        range projectiveLineNegativeChartMap := by rw [projectiveLineChartMap_cover]; trivial
    rcases hp with ⟨v, rfl⟩ | ⟨s, rfl⟩
    · have hx := (mem_planeBlowUpIncidence_positiveChart x v).1 hq
      refine ⟨affinePlaneBlowUpUpperChart (x.1, v), ?_⟩
      rw [affinePlaneBlowUpIncidenceMap_upperChart]
      exact Prod.ext (Prod.ext rfl hx.symm) rfl
    · have hx := (mem_planeBlowUpIncidence_negativeChart x s).1 hq
      refine ⟨affinePlaneBlowUpLowerChart (s, x.2), ?_⟩
      rw [affinePlaneBlowUpIncidenceMap_lowerChart]
      exact Prod.ext (Prod.ext ((mul_comm _ _).trans hx.symm) rfl) rfl

/-- The classical incidence model is a closed subspace of `ℂ² × ℙ¹`. -/
theorem isClosed_planeBlowUpIncidence : IsClosed planeBlowUpIncidence := by
  rw [← range_affinePlaneBlowUpIncidenceMap]
  exact isProperMap_affinePlaneBlowUpIncidenceMap.isClosed_range

end TauCeti.Toric
