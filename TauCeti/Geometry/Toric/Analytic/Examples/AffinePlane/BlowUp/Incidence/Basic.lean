/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.ProjectiveDirection
public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Transition

/-!
# The toric plane blow-up and the incidence model

Blow-down paired with projective direction identifies the toric plane blow-up homeomorphically
with the incidence locus `x * b = y * a` in `ℂ² × ℙ¹`. Here `ℙ¹` is the existing toric
projective line, with its two standard affine coordinates. The inverse comparison sends
`((x, x * v), [1 : v])` to the upper-chart point `(x, v)` and
`((s * y, y), [s : 1])` to the lower-chart point `(s, y)`, including above the origin.

Injectivity follows from these chart coordinates and their transition on the overlap.
Properness of the incidence map then gives the subspace topology, rather than transporting a
new topology to the incidence locus. No complex structure on that locus is defined here.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Set Topology

namespace TauCeti.Toric

local notation "B" => affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan

private theorem upper_eq_lower_of_incidenceMap_eq (z w : ℂ × ℂ)
    (h : affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpUpperChart z) =
      affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpLowerChart w)) :
    affinePlaneBlowUpUpperChart z = affinePlaneBlowUpLowerChart w := by
  rw [affinePlaneBlowUpIncidenceMap_upperChart,
    affinePlaneBlowUpIncidenceMap_lowerChart] at h
  have hd := (projectiveLinePositiveChartMap_eq_negativeChartMap_iff z.2 w.1).1
    (congrArg Prod.snd h)
  exact (affinePlaneBlowUpUpperChart_eq_lowerChart_iff z w).2
    ⟨left_ne_zero_of_mul_eq_one hd,
      Prod.ext (inv_eq_of_mul_eq_one_right hd).symm (congrArg (fun q ↦ q.1.2) h).symm⟩

/-- Blow-down and projective direction together determine a unique point of the toric blow-up,
including on the exceptional fibre. -/
theorem injective_affinePlaneBlowUpIncidenceMap :
    Function.Injective affinePlaneBlowUpIncidenceMap := by
  intro p q h
  rcases exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq p
      with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
    rcases exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq q
      with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rw [affinePlaneBlowUpIncidenceMap_upperChart,
      affinePlaneBlowUpIncidenceMap_upperChart] at h
    exact congrArg affinePlaneBlowUpUpperChart (Prod.ext
      (congrArg (fun q ↦ q.1.1) h)
      (isOpenEmbedding_projectiveLinePositiveChartMap.injective (congrArg Prod.snd h)))
  · exact upper_eq_lower_of_incidenceMap_eq z w h
  · exact (upper_eq_lower_of_incidenceMap_eq w z h.symm).symm
  · rw [affinePlaneBlowUpIncidenceMap_lowerChart,
      affinePlaneBlowUpIncidenceMap_lowerChart] at h
    exact congrArg affinePlaneBlowUpLowerChart (Prod.ext
      (isOpenEmbedding_projectiveLineNegativeChartMap.injective (congrArg Prod.snd h))
      (congrArg (fun q ↦ q.1.2) h))

/-- The incidence map realizes the toric blow-up as a closed subspace of `ℂ² × ℙ¹`. -/
theorem isClosedEmbedding_affinePlaneBlowUpIncidenceMap :
    IsClosedEmbedding affinePlaneBlowUpIncidenceMap :=
  IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.2
    ⟨continuous_affinePlaneBlowUpIncidenceMap, injective_affinePlaneBlowUpIncidenceMap,
      isProperMap_affinePlaneBlowUpIncidenceMap.isClosedMap⟩

/-- The toric plane blow-up is homeomorphic to the classical incidence locus, with its existing
subspace topology. The comparison is blow-down paired with projective direction. -/
noncomputable def affinePlaneBlowUpIncidenceHomeomorph : B ≃ₜ planeBlowUpIncidence :=
  isClosedEmbedding_affinePlaneBlowUpIncidenceMap.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_affinePlaneBlowUpIncidenceMap)

/-- The underlying incidence point of the comparison is the canonical incidence map. -/
@[simp]
theorem affinePlaneBlowUpIncidenceHomeomorph_apply (p : B) :
    (affinePlaneBlowUpIncidenceHomeomorph p).val = affinePlaneBlowUpIncidenceMap p := (rfl)

/-- Reconstructing an incidence point and applying the incidence map returns that point. -/
@[simp]
theorem affinePlaneBlowUpIncidenceMap_homeomorph_symm (q : planeBlowUpIncidence) :
    affinePlaneBlowUpIncidenceMap (affinePlaneBlowUpIncidenceHomeomorph.symm q) = q.val := by
  simpa only [affinePlaneBlowUpIncidenceHomeomorph_apply] using
    congrArg Subtype.val (affinePlaneBlowUpIncidenceHomeomorph.apply_symm_apply q)

/-- Over the positive projective chart, the inverse comparison retains the first plane coordinate
and the projective coordinate. This formula also holds when the plane point is the origin. -/
@[simp]
theorem affinePlaneBlowUpIncidenceHomeomorph_symm_positiveChart (x v : ℂ) :
    affinePlaneBlowUpIncidenceHomeomorph.symm
      ⟨((x, x * v), projectiveLinePositiveChartMap v), by simp⟩ =
        affinePlaneBlowUpUpperChart (x, v) := by
  apply affinePlaneBlowUpIncidenceHomeomorph.symm_apply_eq.2
  apply Subtype.ext
  simp

/-- Over the negative projective chart, the inverse comparison retains the projective coordinate
and the second plane coordinate, including on the exceptional fibre. -/
@[simp]
theorem affinePlaneBlowUpIncidenceHomeomorph_symm_negativeChart (s y : ℂ) :
    affinePlaneBlowUpIncidenceHomeomorph.symm
      ⟨((s * y, y), projectiveLineNegativeChartMap s), by simp [mul_comm]⟩ =
        affinePlaneBlowUpLowerChart (s, y) := by
  apply affinePlaneBlowUpIncidenceHomeomorph.symm_apply_eq.2
  apply Subtype.ext
  simp

end TauCeti.Toric
