/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Rescaling symplectic forms

A nonzero scalar multiple of a symplectic form is again symplectic. This file records that
pointwise linear-algebra operation and the basic interaction with the tame and compatible
almost-complex predicates used by the analytic Heegaard Floer roadmap.

Positive rescalings preserve the positivity condition `0 < ω(v, J v)` and hence preserve
tameness and compatibility. Negative rescalings do not preserve tameness for the same `J`, but
they do preserve invariance because invariance is linear in the form.

## Main declarations

* `TauCeti.SymplecticForm.rescale`: the symplectic form `c • ω`, for `c ≠ 0`.
* `TauCeti.SymplecticForm.invariant_rescale_iff`: rescaling by a nonzero scalar preserves and
  reflects `J`-invariance.
* `TauCeti.SymplecticForm.tames_rescale_iff_of_pos`: positive rescaling preserves and reflects
  tameness.
* `TauCeti.SymplecticForm.compatible_rescale_iff_of_pos`: positive rescaling preserves and
  reflects compatibility.
* `TauCeti.SymplecticForm.compatible_rescale_neg_iff_of_neg`: negative rescaling preserves and
  reflects compatibility after replacing `J` by `-J`.

The convention is the standard one from symplectic geometry: changing the overall positive scale
of `ω` changes the metric scale but not the compatible almost complex structure.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The nonzero scalar multiple `c • ω` of a symplectic form.

The hypothesis `c ≠ 0` is needed for nondegeneracy. The construction is not an instance because
there is no closed scalar action at `c = 0`. -/
@[expose]
noncomputable def rescale (ω : SymplecticForm V) (c : ℝ) (hc : c ≠ 0) : SymplecticForm V where
  toBilinForm := c • ω.toBilinForm
  isAlt := by
    intro v
    simp
  nondegenerate := by
    constructor
    · intro v hv
      exact ω.separatingLeft v fun w => by
        have h := hv w
        simp only [LinearMap.smul_apply, smul_eq_mul] at h
        exact (mul_eq_zero.mp h).resolve_left hc
    · intro v hv
      exact ω.separatingRight v fun w => by
        have h := hv w
        simp only [LinearMap.smul_apply, smul_eq_mul] at h
        exact (mul_eq_zero.mp h).resolve_left hc

@[simp]
lemma rescale_toBilinForm (ω : SymplecticForm V) (c : ℝ) (hc : c ≠ 0) :
    (ω.rescale c hc).toBilinForm = c • ω.toBilinForm :=
  rfl

/-- Evaluation of a rescaled symplectic form. -/
@[simp]
lemma rescale_apply (ω : SymplecticForm V) (c : ℝ) (hc : c ≠ 0) (v w : V) :
    ω.rescale c hc v w = c * ω v w :=
  rfl

@[simp]
lemma rescale_one (ω : SymplecticForm V) (h : (1 : ℝ) ≠ 0) : ω.rescale 1 h = ω :=
  toBilinForm_injective <| by
    ext v w
    simp

/-- Successive nonzero rescalings multiply the scale factors. -/
@[simp]
lemma rescale_rescale (ω : SymplecticForm V) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (ω.rescale c hc).rescale d hd = ω.rescale (d * c) (mul_ne_zero hd hc) :=
  toBilinForm_injective <| by
    ext v w
    simp [mul_assoc]

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- The associated bilinear form of a rescaled symplectic form is rescaled by the same factor. -/
@[simp]
lemma rescale_associatedBilinForm_apply (c : ℝ) (hc : c ≠ 0) (v w : V) :
    (ω.rescale c hc).associatedBilinForm J v w = c * ω.associatedBilinForm J v w :=
  rfl

/-- Rescaling by a nonzero scalar preserves and reflects `J`-invariance. -/
@[simp]
lemma invariant_rescale_iff (c : ℝ) (hc : c ≠ 0) :
    (ω.rescale c hc).Invariant J ↔ ω.Invariant J := by
  rw [invariant_iff, invariant_iff]
  constructor
  · intro h v w
    have h' := h v w
    simp only [rescale_apply] at h'
    exact mul_left_cancel₀ hc h'
  · intro h v w
    simp [h v w]

/-- `J`-invariance is preserved by any nonzero rescaling of the symplectic form. -/
lemma Invariant.rescale (h : ω.Invariant J) (c : ℝ) (hc : c ≠ 0) :
    (ω.rescale c hc).Invariant J :=
  (invariant_rescale_iff c hc).mpr h

/-- Rescaling by a nonzero scalar and replacing `J` by `-J` preserves and reflects
`J`-invariance. -/
lemma invariant_rescale_neg_iff (c : ℝ) (hc : c ≠ 0) :
    (ω.rescale c hc).Invariant (-J) ↔ ω.Invariant J := by
  rw [invariant_iff, invariant_iff]
  constructor
  · intro h v w
    have h' := h v w
    have h'' : c * ω (J v) (J w) = c * ω v w := by
      simpa using h'
    exact mul_left_cancel₀ hc h''
  · intro h v w
    simp [h v w]

/-- Positive rescaling preserves and reflects tameness. -/
@[simp]
lemma tames_rescale_iff_of_pos {c : ℝ} (hcpos : 0 < c) :
    (ω.rescale c hcpos.ne').Tames J ↔ ω.Tames J := by
  constructor
  · intro h v hv
    have h' := h v hv
    simpa only [rescale_apply] using (mul_pos_iff_of_pos_left hcpos).mp h'
  · intro h v hv
    simpa only [rescale_apply] using mul_pos hcpos (h v hv)

/-- Tameness is preserved by positive rescaling of the symplectic form. -/
lemma Tames.rescale_of_pos (h : ω.Tames J) {c : ℝ} (hcpos : 0 < c) :
    (ω.rescale c hcpos.ne').Tames J :=
  (tames_rescale_iff_of_pos hcpos).mpr h

/-- Negative rescaling preserves and reflects tameness after replacing `J` by `-J`. -/
@[simp]
lemma tames_rescale_neg_iff_of_neg {c : ℝ} (hcneg : c < 0) :
    (ω.rescale c hcneg.ne).Tames (-J) ↔ ω.Tames J := by
  constructor
  · intro h v hv
    have h' := h v hv
    have h'' : 0 < (-c) * ω v (J v) := by
      simpa [mul_neg, neg_mul] using h'
    exact (mul_pos_iff_of_pos_left (neg_pos.mpr hcneg)).mp h''
  · intro h v hv
    have h' : 0 < (-c) * ω v (J v) := mul_pos (neg_pos.mpr hcneg) (h v hv)
    simpa [mul_neg, neg_mul] using h'

/-- Tameness is preserved by negative rescaling if the almost complex structure is negated too. -/
lemma Tames.rescale_neg_of_neg (h : ω.Tames J) {c : ℝ} (hcneg : c < 0) :
    (ω.rescale c hcneg.ne).Tames (-J) :=
  (tames_rescale_neg_iff_of_neg hcneg).mpr h

/-- Positive rescaling preserves and reflects compatibility. -/
@[simp]
lemma compatible_rescale_iff_of_pos {c : ℝ} (hcpos : 0 < c) :
    (ω.rescale c hcpos.ne').Compatible J ↔ ω.Compatible J := by
  rw [(ω.rescale c hcpos.ne').compatible_iff J, ω.compatible_iff J,
    invariant_rescale_iff c hcpos.ne', tames_rescale_iff_of_pos hcpos]

/-- Compatibility is preserved by positive rescaling of the symplectic form. -/
lemma Compatible.rescale_of_pos (h : ω.Compatible J) {c : ℝ} (hcpos : 0 < c) :
    (ω.rescale c hcpos.ne').Compatible J :=
  (compatible_rescale_iff_of_pos hcpos).mpr h

/-- Negative rescaling preserves and reflects compatibility after replacing `J` by `-J`. -/
@[simp]
lemma compatible_rescale_neg_iff_of_neg {c : ℝ} (hcneg : c < 0) :
    (ω.rescale c hcneg.ne).Compatible (-J) ↔ ω.Compatible J := by
  rw [(ω.rescale c hcneg.ne).compatible_iff (-J), ω.compatible_iff J,
    invariant_rescale_neg_iff c hcneg.ne, tames_rescale_neg_iff_of_neg hcneg]

/-- Compatibility is preserved by negative rescaling if the almost complex structure is negated
too. -/
lemma Compatible.rescale_neg_of_neg (h : ω.Compatible J) {c : ℝ} (hcneg : c < 0) :
    (ω.rescale c hcneg.ne).Compatible (-J) :=
  (compatible_rescale_neg_iff_of_neg hcneg).mpr h

end SymplecticForm

end TauCeti
