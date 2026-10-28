/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Incidence
public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Holomorphic
public import TauCeti.Geometry.Toric.Analytic.Examples.ProjectiveLine.Holomorphic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# The exceptional projective line of the plane blow-up

Projective direction identifies the exceptional fibre of the toric plane blow-up with the
projective line, with its original subspace topology. The inverse is a closed holomorphic
embedding into the blow-up. In the two affine charts it sends `v` to `(0, v)` and `s` to
`(s, 0)`, respectively. Thus the projective directions above the origin remain distinct.

The construction restricts the incidence comparison to the points `((0, 0), p)`; holomorphy
is checked in the existing affine charts of the blow-up and of the projective line.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric

local notation "B" => affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan
local notation "P" => projectiveLineFan.analyticRealization isRegular_projectiveLineFan
local notation "IB" => 𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
local notation "IP" => 𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)

/-- The exceptional fibre, defined by vanishing of the ordinary blow-down coordinates. -/
def affinePlaneBlowUpExceptionalFiber : Set B :=
  {p | (affinePlaneBlowUpIncidenceMap p).1 = 0}

/-- A blow-up point is exceptional exactly when its blow-down is the origin of `ℂ²`. -/
theorem mem_affinePlaneBlowUpExceptionalFiber_iff (p : B) :
    p ∈ affinePlaneBlowUpExceptionalFiber ↔
      affinePlaneDiffeomorph ⊤
        (affinePlaneBlowUpFan_isSubdivision.toFanHom.analyticMap
          isRegular_affinePlaneBlowUpFan isRegular_affinePlaneFan p) = 0 := by
  rw [affinePlaneBlowUpExceptionalFiber, mem_ofPred_eq, affinePlaneBlowUpIncidenceMap_def]

/-- In the upper chart, the exceptional fibre is the axis `u = 0`. -/
@[simp]
theorem affinePlaneBlowUpUpperChart_mem_exceptionalFiber_iff (z : ℂ × ℂ) :
    affinePlaneBlowUpUpperChart z ∈ affinePlaneBlowUpExceptionalFiber ↔ z.1 = 0 := by
  simp only [affinePlaneBlowUpExceptionalFiber, mem_ofPred_eq,
    affinePlaneBlowUpIncidenceMap_upperChart, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  grind

/-- In the lower chart, the exceptional fibre is the axis `t = 0`. -/
@[simp]
theorem affinePlaneBlowUpLowerChart_mem_exceptionalFiber_iff (z : ℂ × ℂ) :
    affinePlaneBlowUpLowerChart z ∈ affinePlaneBlowUpExceptionalFiber ↔ z.2 = 0 := by
  simp only [affinePlaneBlowUpExceptionalFiber, mem_ofPred_eq,
    affinePlaneBlowUpIncidenceMap_lowerChart, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  grind

/-- Insert a projective direction above the origin in the plane blow-up. -/
noncomputable def affinePlaneBlowUpExceptionalι (p : P) : B :=
  affinePlaneBlowUpIncidenceHomeomorph.symm ⟨(0, p), by
    rw [mem_planeBlowUpIncidence]
    constructor <;> intro z hz <;> simp⟩

/-- The exceptional inclusion has zero blow-down and the specified projective direction. -/
@[simp]
theorem affinePlaneBlowUpIncidenceMap_exceptionalι (p : P) :
    affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpExceptionalι p) = (0, p) :=
  affinePlaneBlowUpIncidenceMap_homeomorph_symm _

/-- Projective direction is a left inverse to the exceptional inclusion. -/
@[simp]
theorem affinePlaneBlowUpDirectionMap_exceptionalι (p : P) :
    affinePlaneBlowUpDirectionMap (affinePlaneBlowUpExceptionalι p) = p := by
  simpa only [affinePlaneBlowUpIncidenceMap_def] using
    congrArg Prod.snd (affinePlaneBlowUpIncidenceMap_exceptionalι p)

/-- The positive projective chart parametrizes the upper exceptional axis. -/
@[simp]
theorem affinePlaneBlowUpExceptionalι_positiveChart (v : ℂ) :
    affinePlaneBlowUpExceptionalι (projectiveLinePositiveChartMap v) =
      affinePlaneBlowUpUpperChart (0, v) := by
  apply injective_affinePlaneBlowUpIncidenceMap
  simp [Prod.zero_eq_mk]

/-- The negative projective chart parametrizes the lower exceptional axis. -/
@[simp]
theorem affinePlaneBlowUpExceptionalι_negativeChart (s : ℂ) :
    affinePlaneBlowUpExceptionalι (projectiveLineNegativeChartMap s) =
      affinePlaneBlowUpLowerChart (s, 0) := by
  apply injective_affinePlaneBlowUpIncidenceMap
  simp [Prod.zero_eq_mk]

/-- The exceptional inclusion is continuous in the existing subspace topologies. -/
theorem continuous_affinePlaneBlowUpExceptionalι : Continuous affinePlaneBlowUpExceptionalι :=
  affinePlaneBlowUpIncidenceHomeomorph.symm.continuous.comp
    ((continuous_const.prodMk continuous_id).subtype_mk _)

/-- Every point above the origin is recovered from its projective direction. -/
theorem affinePlaneBlowUpExceptionalι_directionMap (p : B)
    (hp : p ∈ affinePlaneBlowUpExceptionalFiber) :
    affinePlaneBlowUpExceptionalι (affinePlaneBlowUpDirectionMap p) = p := by
  apply injective_affinePlaneBlowUpIncidenceMap
  rw [affinePlaneBlowUpIncidenceMap_exceptionalι]
  apply Prod.ext hp.symm
  simp only [affinePlaneBlowUpIncidenceMap_def]

/-- The projective line maps onto exactly the exceptional fibre of blow-down. -/
theorem range_affinePlaneBlowUpExceptionalι :
    range affinePlaneBlowUpExceptionalι = affinePlaneBlowUpExceptionalFiber := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp [affinePlaneBlowUpExceptionalFiber]
  · intro hp
    exact ⟨_, affinePlaneBlowUpExceptionalι_directionMap p hp⟩

/-- Projective direction is a homeomorphism from the exceptional fibre to the projective line.
The fibre retains its subspace topology from the blow-up. -/
noncomputable def affinePlaneBlowUpExceptionalHomeomorph :
    affinePlaneBlowUpExceptionalFiber ≃ₜ P where
  toFun p := affinePlaneBlowUpDirectionMap p
  invFun p := ⟨affinePlaneBlowUpExceptionalι p,
    range_affinePlaneBlowUpExceptionalι ▸ mem_range_self p⟩
  left_inv p := Subtype.ext (affinePlaneBlowUpExceptionalι_directionMap p p.2)
  right_inv := affinePlaneBlowUpDirectionMap_exceptionalι
  continuous_toFun :=
    (affinePlaneBlowUpDirectionFanHom.analyticMap
      isRegular_affinePlaneBlowUpFan isRegular_projectiveLineFan).hom.continuous.comp
        continuous_subtype_val
  continuous_invFun := continuous_affinePlaneBlowUpExceptionalι.subtype_mk _

/-- The comparison with the projective line is projective direction. -/
@[simp]
theorem affinePlaneBlowUpExceptionalHomeomorph_apply (p : affinePlaneBlowUpExceptionalFiber) :
    affinePlaneBlowUpExceptionalHomeomorph p = affinePlaneBlowUpDirectionMap p := (rfl)

/-- The inverse comparison is the exceptional inclusion. -/
@[simp]
theorem affinePlaneBlowUpExceptionalHomeomorph_symm_apply (p : P) :
    (affinePlaneBlowUpExceptionalHomeomorph.symm p).val =
      affinePlaneBlowUpExceptionalι p := (rfl)

/-- The exceptional projective line is a closed topological subspace of the blow-up. -/
theorem isClosedEmbedding_affinePlaneBlowUpExceptionalι :
    IsClosedEmbedding affinePlaneBlowUpExceptionalι := by
  let : CompactSpace P := projectiveLineOnePointHomeomorph.symm.compactSpace
  exact continuous_affinePlaneBlowUpExceptionalι.isClosedEmbedding
    (Function.LeftInverse.injective affinePlaneBlowUpDirectionMap_exceptionalι)

/-- The exceptional inclusion is holomorphic, including both ends of its projective line. -/
theorem contMDiff_affinePlaneBlowUpExceptionalι (n : ℕ∞ω) :
    let := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    ContMDiff IP IB n affinePlaneBlowUpExceptionalι := by
  let := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  have hpos : ContMDiff 𝓘(ℂ, ℂ) IB n
      (affinePlaneBlowUpExceptionalι ∘ projectiveLinePositivePartialDiffeomorph n) := by
    have h := (isLocalDiffeomorph_affinePlaneBlowUpUpperPartialDiffeomorph n).contMDiff.comp
      ((contMDiff_const (c := (0 : ℂ))).prodMk (contMDiff_id : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) n id))
    apply h.congr
    intro v
    simp only [Function.comp_apply, id_eq, affinePlaneBlowUpUpperPartialDiffeomorph_apply,
      projectiveLinePositivePartialDiffeomorph_apply]
    rw [← projectiveLinePositiveChartMap_apply_single]
    -- The character evaluation uses the bundled affine-chart topology.
    erw [affineRayPointHomeomorph_symm_apply_single]
    exact affinePlaneBlowUpExceptionalι_positiveChart v
  have hneg : ContMDiff 𝓘(ℂ, ℂ) IB n
      (affinePlaneBlowUpExceptionalι ∘ projectiveLineNegativePartialDiffeomorph n) := by
    have h := (isLocalDiffeomorph_affinePlaneBlowUpLowerPartialDiffeomorph n).contMDiff.comp
      ((contMDiff_id : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) n id).prodMk (contMDiff_const (c := (0 : ℂ))))
    apply h.congr
    intro s
    simp only [Function.comp_apply, id_eq, affinePlaneBlowUpLowerPartialDiffeomorph_apply,
      projectiveLineNegativePartialDiffeomorph_apply]
    rw [← projectiveLineNegativeChartMap_apply_single]
    let _ := affinePointTopology
      (projectiveLineFan.analyticChartGenerators projectiveLineNegativeCone).2
    -- Read the inverse homeomorphism through the bundled affine-chart topology.
    erw [← negativeRayPointHomeomorph_apply, Homeomorph.apply_symm_apply]
    exact affinePlaneBlowUpExceptionalι_negativeChart s
  dsimp only
  intro p
  have hp : p ∈ (projectiveLinePositivePartialDiffeomorph n).target ∪
      (projectiveLineNegativePartialDiffeomorph n).target := by
    rw [projectiveLinePartialDiffeomorph_target_cover]
    trivial
  rcases hp with hp | hp
  · have hlocal := isLocalDiffeomorph_projectiveLinePositivePartialDiffeomorph n
      ((projectiveLinePositivePartialDiffeomorph n).toPartialEquiv.symm p)
    have h := (hlocal.contMDiffAt_comp_iff le_rfl).1
      (hpos ((projectiveLinePositivePartialDiffeomorph n).toPartialEquiv.symm p))
    rwa [(projectiveLinePositivePartialDiffeomorph n).right_inv hp] at h
  · have hlocal := isLocalDiffeomorph_projectiveLineNegativePartialDiffeomorph n
      ((projectiveLineNegativePartialDiffeomorph n).toPartialEquiv.symm p)
    have h := (hlocal.contMDiffAt_comp_iff le_rfl).1
      (hneg ((projectiveLineNegativePartialDiffeomorph n).toPartialEquiv.symm p))
    rwa [(projectiveLineNegativePartialDiffeomorph n).right_inv hp] at h

/-- The exceptional inclusion is a complex analytic smooth embedding. Together with its closed
image and its range formula, this realizes the exceptional fibre as an embedded projective line. -/
theorem isSmoothEmbedding_affinePlaneBlowUpExceptionalι :
    letI := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    Manifold.IsSmoothEmbedding IP IB ω affinePlaneBlowUpExceptionalι := by
  let := projectiveLineFan.analyticChartedSpace isRegular_projectiveLineFan
  let := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  have := projectiveLineFan.isManifold_analyticRealization isRegular_projectiveLineFan ω
  have := affinePlaneBlowUpFan.isManifold_analyticRealization isRegular_affinePlaneBlowUpFan ω
  have hf := contMDiff_affinePlaneBlowUpExceptionalι ω
  have hg := contMDiff_affinePlaneBlowUpDirectionMap ω
  refine ⟨?_, isClosedEmbedding_affinePlaneBlowUpExceptionalι.isEmbedding⟩
  apply isImmersion_iff_forall_isImmersionAt.mpr
  intro p
  apply hf.contMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv isOpen_univ (mem_univ p) (by simp)
  refine ⟨mfderiv IB IP affinePlaneBlowUpDirectionMap (affinePlaneBlowUpExceptionalι p), ?_⟩
  have hcomp : affinePlaneBlowUpDirectionMap ∘ affinePlaneBlowUpExceptionalι = id :=
    funext affinePlaneBlowUpDirectionMap_exceptionalι
  have hderiv := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_id] at hderiv
  intro v
  exact (congrArg (fun L ↦ L v) hderiv).symm

end TauCeti.Toric
