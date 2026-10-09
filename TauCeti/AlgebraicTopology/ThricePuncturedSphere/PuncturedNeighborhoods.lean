/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Anharmonic

/-!
# Standard punctured neighborhoods of the three punctures

This file fixes pairwise disjoint standard neighborhoods of the punctures `0`, `1`, and `∞` in
the thrice-punctured sphere. In the affine coordinate they are

* `puncturedNeighborhoodZero = {z | ‖z‖ < 1 / 2}`;
* `puncturedNeighborhoodOne = {z | ‖z - 1‖ < 1 / 2}`;
* `puncturedNeighborhoodInf = {z | 2 < ‖z‖}`.

The missing center of each finite disc is already excluded from `ThricePuncturedSphere`. The
anharmonic maps `z ↦ 1 - z` and `z ↦ 1 / z` identify the neighborhoods at `1` and `∞` with the
one at `0`. Thus all three are copies of the same punctured disc, expressed in the standard
local coordinates at the three punctures.

These neighborhoods are the local geometric input for extending a finite cover across the three
punctures: their pairwise disjointness lets the three fillings be performed independently.

## Main definitions

* `puncturedDiscOneHalf`: the punctured complex disc of radius `1 / 2`.
* `puncturedNeighborhoodZero`, `puncturedNeighborhoodOne`, `puncturedNeighborhoodInf`: the
  three standard neighborhoods.
* `puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf`,
  `puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf`, and
  `puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf`: their standard local coordinates.
* `puncturedDiscOneHalfHomeomorphPuncturedDisc`: multiplication by `2`, from the disc of radius
  `1 / 2` to the punctured unit disc `ball 0 1 \ {0}` that carries the power-map covers.
* `Puncture`: the three punctures, with `Puncture.neighborhood` and `Puncture.coord` the standard
  neighborhood of each and its coordinate `z ↦ 2 * z`, `z ↦ 2 * (1 - z)` or `z ↦ 2 / z`, valued in
  the punctured unit disc. These index the three neighborhoods uniformly, so that a construction
  over all three punctures is made once.
-/

public section

open Set

namespace TauCeti

namespace ThricePuncturedSphere

/-! ### The three neighborhoods -/

/-- The complex punctured disc of radius `1 / 2`, used as the common coordinate model for the
three standard punctured neighborhoods. -/
def puncturedDiscOneHalf : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < 1 / 2}

/-- The standard punctured disc of radius `1 / 2` about `0` in the thrice-punctured sphere.
The center is absent because points of `ThricePuncturedSphere` are nonzero. -/
def puncturedNeighborhoodZero : Set ThricePuncturedSphere :=
  {z | ‖(z : ℂ)‖ < 1 / 2}

/-- The standard punctured disc of radius `1 / 2` about `1` in the thrice-punctured sphere.
The center is absent because points of `ThricePuncturedSphere` are not equal to `1`. -/
def puncturedNeighborhoodOne : Set ThricePuncturedSphere :=
  {z | ‖(z : ℂ) - 1‖ < 1 / 2}

/-- The standard punctured neighborhood of `∞`, represented in the affine coordinate by the
exterior of the closed disc of radius `2`. -/
def puncturedNeighborhoodInf : Set ThricePuncturedSphere :=
  {z | 2 < ‖(z : ℂ)‖}

@[simp]
theorem mem_puncturedNeighborhoodZero {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodZero ↔ ‖(z : ℂ)‖ < 1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_puncturedNeighborhoodOne {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodOne ↔ ‖(z : ℂ) - 1‖ < 1 / 2 :=
  Iff.rfl

@[simp]
theorem mem_puncturedNeighborhoodInf {z : ThricePuncturedSphere} :
    z ∈ puncturedNeighborhoodInf ↔ 2 < ‖(z : ℂ)‖ :=
  Iff.rfl

@[simp]
theorem mem_puncturedDiscOneHalf {z : ℂ} :
    z ∈ puncturedDiscOneHalf ↔ 0 < ‖z‖ ∧ ‖z‖ < 1 / 2 :=
  Iff.rfl

/-- The standard punctured neighborhood of `0` is open. -/
theorem isOpen_puncturedNeighborhoodZero : IsOpen puncturedNeighborhoodZero :=
  isOpen_lt continuous_subtype_val.norm continuous_const

/-- The standard punctured neighborhood of `1` is open. -/
theorem isOpen_puncturedNeighborhoodOne : IsOpen puncturedNeighborhoodOne :=
  isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const

/-- The standard punctured neighborhood of `∞` is open. -/
theorem isOpen_puncturedNeighborhoodInf : IsOpen puncturedNeighborhoodInf :=
  isOpen_lt continuous_const continuous_subtype_val.norm

/-! ### Disjointness -/

/-- The standard punctured neighborhoods of `0` and `1` are disjoint. -/
theorem disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodOne :
    Disjoint puncturedNeighborhoodZero puncturedNeighborhoodOne := by
  have hZero : puncturedNeighborhoodZero =
      ((↑) : ThricePuncturedSphere → ℂ) ⁻¹' Metric.ball 0 (1 / 2) := by
    ext z
    simp only [mem_puncturedNeighborhoodZero, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right]
  have hOne : puncturedNeighborhoodOne =
      ((↑) : ThricePuncturedSphere → ℂ) ⁻¹' Metric.ball 1 (1 / 2) := by
    ext z
    simp only [mem_puncturedNeighborhoodOne, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
  rw [hZero, hOne]
  exact (Metric.ball_disjoint_ball (x := (0 : ℂ)) (y := 1) (δ := 1 / 2) (ε := 1 / 2)
    (by norm_num)).preimage ((↑) : ThricePuncturedSphere → ℂ)

/-- The standard punctured neighborhoods of `0` and `∞` are disjoint. -/
theorem disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodInf :
    Disjoint puncturedNeighborhoodZero puncturedNeighborhoodInf := by
  rw [Set.disjoint_left]
  intro z hz hInf
  rw [mem_puncturedNeighborhoodZero] at hz
  rw [mem_puncturedNeighborhoodInf] at hInf
  linarith

/-- The standard punctured neighborhoods of `1` and `∞` are disjoint. -/
theorem disjoint_puncturedNeighborhoodOne_puncturedNeighborhoodInf :
    Disjoint puncturedNeighborhoodOne puncturedNeighborhoodInf := by
  rw [Set.disjoint_left]
  intro z hOne hInf
  have hle : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) - 1‖ + 1 := calc
    ‖(z : ℂ)‖ = ‖((z : ℂ) - 1) + 1‖ := by ring_nf
    _ ≤ ‖(z : ℂ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖(z : ℂ) - 1‖ + 1 := by norm_num
  rw [mem_puncturedNeighborhoodOne] at hOne
  rw [mem_puncturedNeighborhoodInf] at hInf
  linarith

/-! ### Standard local coordinates -/

private theorem puncturedDiscOneHalf_subset_range :
    puncturedDiscOneHalf ⊆ Set.range ((↑) : ThricePuncturedSphere → ℂ) := by
  intro z hz
  rw [mem_puncturedDiscOneHalf] at hz
  refine ⟨⟨z, norm_pos_iff.mp hz.1, ?_⟩, rfl⟩
  intro h
  rw [h, norm_one] at hz
  norm_num at hz

/-- The affine coordinate identifies the standard neighborhood of `0` with the complex
punctured disc of radius `1 / 2`. -/
noncomputable def puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf :
    ↥puncturedNeighborhoodZero ≃ₜ ↥puncturedDiscOneHalf :=
  (Homeomorph.setCongr (by
    ext z
    simp only [mem_puncturedNeighborhoodZero, Set.mem_preimage, mem_puncturedDiscOneHalf]
    exact (and_iff_right (norm_pos_iff.mpr z.ne_zero)).symm)).trans
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      puncturedDiscOneHalf_subset_range)

@[simp]
theorem coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf
    (z : ↥puncturedNeighborhoodZero) :
    (puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf z : ℂ) =
      (z : ThricePuncturedSphere) := by
  unfold puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf
  exact Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
    Topology.IsEmbedding.subtypeVal puncturedDiscOneHalf_subset_range _

/-- The inverse affine coordinate on the punctured disc is `w ↦ w`. -/
@[simp]
theorem coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf_symm_apply
    (w : ↥puncturedDiscOneHalf) :
    ((puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf.symm w :
      ↥puncturedNeighborhoodZero) : ThricePuncturedSphere) = (w : ℂ) := by
  simpa only [coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf] using
    congrArg Subtype.val
      (puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf.apply_symm_apply w)

/-- The local coordinate `z ↦ 1 - z` identifies the punctured neighborhood of `1` with the
punctured neighborhood of `0`. -/
private noncomputable def puncturedNeighborhoodOneHomeomorphZero :
    ↥puncturedNeighborhoodOne ≃ₜ ↥puncturedNeighborhoodZero :=
  mob01.subtype fun z ↦ by
    rw [mem_puncturedNeighborhoodOne, mem_puncturedNeighborhoodZero, coe_mob01]
    rw [norm_sub_rev]

private theorem coe_puncturedNeighborhoodOneHomeomorphZero
    (z : ↥puncturedNeighborhoodOne) :
    (((puncturedNeighborhoodOneHomeomorphZero z : ↥puncturedNeighborhoodZero) :
      ThricePuncturedSphere) : ℂ) = 1 - ((z : ThricePuncturedSphere) : ℂ) := by
  rw [puncturedNeighborhoodOneHomeomorphZero]
  simp only [← Homeomorph.coe_toEquiv, Homeomorph.subtype_toEquiv,
    Equiv.subtypeEquiv_apply]
  exact coe_mob01 (z : ThricePuncturedSphere)

/-- The coordinate `z ↦ 1 - z` identifies the standard neighborhood of `1` with the complex
punctured disc of radius `1 / 2`. -/
noncomputable def puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf :
    ↥puncturedNeighborhoodOne ≃ₜ ↥puncturedDiscOneHalf :=
  puncturedNeighborhoodOneHomeomorphZero.trans
    puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf

@[simp]
theorem coe_puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf
    (z : ↥puncturedNeighborhoodOne) :
    (puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf z : ℂ) =
      1 - (z : ThricePuncturedSphere) := by
  rw [puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf, Homeomorph.trans_apply,
    coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf,
    coe_puncturedNeighborhoodOneHomeomorphZero]

/-- The inverse coordinate at `1` is `w ↦ 1 - w`. -/
@[simp]
theorem coe_puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf_symm_apply
    (w : ↥puncturedDiscOneHalf) :
    ((puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.symm w :
      ↥puncturedNeighborhoodOne) : ThricePuncturedSphere) = 1 - (w : ℂ) := by
  have h := congrArg Subtype.val
    (puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.apply_symm_apply w)
  rw [coe_puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf] at h
  calc
    (((puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.symm w :
        ↥puncturedNeighborhoodOne) : ThricePuncturedSphere) : ℂ) =
        1 - (1 - ((puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.symm w :
          ↥puncturedNeighborhoodOne) : ThricePuncturedSphere)) := by ring
    _ = 1 - (w : ℂ) := congrArg (1 - ·) h

/-- The local coordinate `z ↦ 1 / z` identifies the punctured neighborhood of `∞` with the
punctured neighborhood of `0`. -/
private noncomputable def puncturedNeighborhoodInfHomeomorphZero :
    ↥puncturedNeighborhoodInf ≃ₜ ↥puncturedNeighborhoodZero :=
  mob0Inf.subtype fun z ↦ by
    rw [mem_puncturedNeighborhoodInf, mem_puncturedNeighborhoodZero, coe_mob0Inf,
      norm_div, norm_one]
    have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
    constructor
    · intro h
      rw [div_lt_iff₀ hz]
      nlinarith
    · intro h
      rw [div_lt_iff₀ hz] at h
      nlinarith

private theorem coe_puncturedNeighborhoodInfHomeomorphZero
    (z : ↥puncturedNeighborhoodInf) :
    (((puncturedNeighborhoodInfHomeomorphZero z : ↥puncturedNeighborhoodZero) :
      ThricePuncturedSphere) : ℂ) = 1 / ((z : ThricePuncturedSphere) : ℂ) := by
  rw [puncturedNeighborhoodInfHomeomorphZero]
  simp only [← Homeomorph.coe_toEquiv, Homeomorph.subtype_toEquiv,
    Equiv.subtypeEquiv_apply]
  exact coe_mob0Inf (z : ThricePuncturedSphere)

/-- The coordinate `z ↦ 1 / z` identifies the standard neighborhood of `∞` with the complex
punctured disc of radius `1 / 2`. This is the standard chart at `∞`. -/
noncomputable def puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf :
    ↥puncturedNeighborhoodInf ≃ₜ ↥puncturedDiscOneHalf :=
  puncturedNeighborhoodInfHomeomorphZero.trans
    puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf

@[simp]
theorem coe_puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf
    (z : ↥puncturedNeighborhoodInf) :
    (puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf z : ℂ) =
      1 / (z : ThricePuncturedSphere) := by
  rw [puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf, Homeomorph.trans_apply,
    coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf,
    coe_puncturedNeighborhoodInfHomeomorphZero]

/-- The inverse coordinate at `∞` is `w ↦ 1 / w`. -/
@[simp]
theorem coe_puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf_symm_apply
    (w : ↥puncturedDiscOneHalf) :
    ((puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.symm w :
      ↥puncturedNeighborhoodInf) : ThricePuncturedSphere) = 1 / (w : ℂ) := by
  have h := congrArg Subtype.val
    (puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.apply_symm_apply w)
  rw [coe_puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf] at h
  calc
    (((puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.symm w :
        ↥puncturedNeighborhoodInf) : ThricePuncturedSphere) : ℂ) =
        1 / (1 / ((puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.symm w :
          ↥puncturedNeighborhoodInf) : ThricePuncturedSphere)) := by rw [one_div_one_div]
    _ = 1 / (w : ℂ) := congrArg (1 / ·) h

/-! ### Rescaling to the punctured unit disc -/

/-- Multiplication by `2` identifies the punctured disc of radius `1 / 2` with the punctured unit
disc `ball 0 1 \ {0}`, on which the power-map covers `TauCeti.puncturedDiscPow` live. -/
noncomputable def puncturedDiscOneHalfHomeomorphPuncturedDisc :
    ↥puncturedDiscOneHalf ≃ₜ ↥(Metric.ball (0 : ℂ) 1 \ {0}) :=
  (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).subtype fun z ↦ by
    simp only [mem_puncturedDiscOneHalf, Homeomorph.coe_mulLeft₀, mem_sdiff, Metric.mem_ball,
      dist_zero_right, mem_singleton_iff, norm_mul, Complex.norm_ofNat, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, norm_pos_iff]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨by linarith, h0⟩
    · rintro ⟨h1, h0⟩
      exact ⟨h0, by linarith⟩

@[simp]
theorem coe_puncturedDiscOneHalfHomeomorphPuncturedDisc (w : ↥puncturedDiscOneHalf) :
    (puncturedDiscOneHalfHomeomorphPuncturedDisc w : ℂ) = 2 * (w : ℂ) :=
  (rfl)

@[simp]
theorem coe_puncturedDiscOneHalfHomeomorphPuncturedDisc_symm_apply
    (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    (puncturedDiscOneHalfHomeomorphPuncturedDisc.symm z : ℂ) = (z : ℂ) / 2 := by
  have h := congrArg Subtype.val (puncturedDiscOneHalfHomeomorphPuncturedDisc.apply_symm_apply z)
  rw [coe_puncturedDiscOneHalfHomeomorphPuncturedDisc] at h
  rw [← h]
  ring

/-! ### The three punctures -/

/-- The three punctures `0`, `1` and `∞` of the thrice-punctured sphere, indexing its standard
punctured neighborhoods. -/
inductive Puncture : Type
  | zero
  | one
  | inf

namespace Puncture

/-- The standard punctured neighborhood of a puncture: `puncturedNeighborhoodZero`,
`puncturedNeighborhoodOne` or `puncturedNeighborhoodInf`. The body is exposed so that types over
`p ⁻¹' zero.neighborhood` are those over `p ⁻¹' puncturedNeighborhoodZero`, and likewise at `1` and
`∞`. -/
@[expose] def neighborhood : Puncture → Set ThricePuncturedSphere
  | zero => puncturedNeighborhoodZero
  | one => puncturedNeighborhoodOne
  | inf => puncturedNeighborhoodInf

@[simp]
theorem neighborhood_zero : zero.neighborhood = puncturedNeighborhoodZero :=
  (rfl)

@[simp]
theorem neighborhood_one : one.neighborhood = puncturedNeighborhoodOne :=
  (rfl)

@[simp]
theorem neighborhood_inf : inf.neighborhood = puncturedNeighborhoodInf :=
  (rfl)

/-- The standard punctured neighborhoods are open. -/
theorem isOpen_neighborhood (q : Puncture) : IsOpen q.neighborhood := by
  cases q
  exacts [isOpen_puncturedNeighborhoodZero, isOpen_puncturedNeighborhoodOne,
    isOpen_puncturedNeighborhoodInf]

open Function in
/-- The standard punctured neighborhoods of distinct punctures are disjoint. -/
theorem pairwise_disjoint_neighborhood : Pairwise (Disjoint on neighborhood) := by
  have h01 := disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodOne
  have h0i := disjoint_puncturedNeighborhoodZero_puncturedNeighborhoodInf
  have h1i := disjoint_puncturedNeighborhoodOne_puncturedNeighborhoodInf
  rintro (_ | _ | _) (_ | _ | _) h <;> first | exact absurd rfl h | skip
  exacts [h01, h0i, h01.symm, h1i, h0i.symm, h1i.symm]

/-- The standard coordinate of the punctured neighborhood of a puncture, identifying it with the
punctured unit disc: `z ↦ 2 * z` at `0`, `z ↦ 2 * (1 - z)` at `1` and `z ↦ 2 / z` at `∞`. -/
noncomputable def coord : (q : Puncture) → q.neighborhood ≃ₜ ↥(Metric.ball (0 : ℂ) 1 \ {0})
  | zero => puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf.trans
      puncturedDiscOneHalfHomeomorphPuncturedDisc
  | one => puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf.trans
      puncturedDiscOneHalfHomeomorphPuncturedDisc
  | inf => puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.trans
      puncturedDiscOneHalfHomeomorphPuncturedDisc

@[simp]
theorem coe_coord_zero (z : zero.neighborhood) :
    (zero.coord z : ℂ) = 2 * (z : ThricePuncturedSphere) :=
  congrArg (2 * ·) (coe_puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf z)

@[simp]
theorem coe_coord_one (z : one.neighborhood) :
    (one.coord z : ℂ) = 2 * (1 - (z : ThricePuncturedSphere)) :=
  congrArg (2 * ·) (coe_puncturedNeighborhoodOneHomeomorphPuncturedDiscOneHalf z)

@[simp]
theorem coe_coord_inf (z : inf.neighborhood) :
    (inf.coord z : ℂ) = 2 / (z : ThricePuncturedSphere) :=
  (congrArg (2 * ·) (coe_puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf z)).trans
    (mul_one_div _ _)

end Puncture

end ThricePuncturedSphere

end TauCeti
