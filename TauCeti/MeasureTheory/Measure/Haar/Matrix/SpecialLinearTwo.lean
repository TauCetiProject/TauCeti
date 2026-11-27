/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup

/-!
# Haar measure on `SL(2, ℝ)`

The group `SL(2, ℝ)` acts transitively on the upper half-plane `ℍ`, and the stabilizer `K` of `i`
is compact (it is `SO(2)`). Mathlib's continuous section `UpperHalfPlane.toSL2R` of the orbit map
`g ↦ g • i` splits `SL(2, ℝ)` as `ℍ × K`: every `g` is uniquely `toSL2R z * k` with `z = g • i`
and `k ∈ K`. This file builds a left Haar measure on `SL(2, ℝ)` from this splitting: the
push-forward of the product of the invariant measure `dx dy / y²` on `ℍ` and the normalized Haar
measure of `K`.

Left translation by `g` acts on the coordinates `(z, k)` as the skew product
`(z, k) ↦ (g • z, κ(g, z) * k)`, where `κ(g, z) = toSL2R (g • z)⁻¹ * g * toSL2R z` lies in `K`.
The first coordinate preserves `dx dy / y²`, which is `SL(2, ℝ)`-invariant, and for each `z` the
second is a left translation of `K`, which preserves its Haar measure. So the product measure is
preserved and its push-forward is left invariant. The splitting is a homeomorphism, so the
push-forward is finite on compact sets and positive on open sets: it is a Haar measure.

The normalization makes the orbit map `g ↦ g • i` measure preserving onto `ℍ`: the preimage of a
set `E ⊆ ℍ` has the hyperbolic area of `E` (`Matrix.SpecialLinearGroup.volume_preimage_smul_I`).
This is the Haar measure on `SL(2, ℝ)` used for the lattice `SL(2, ℤ)` and its covolume.

## Main definitions

* `Matrix.SpecialLinearGroup.instMeasurableSpace`, `instBorelSpace`: the Borel measurable
  structure of `SL(n, ℝ)`.
* `UpperHalfPlane.toSL2RMulHomeomorph`: the splitting `ℍ × K ≃ₜ SL(2, ℝ)`,
  `(z, k) ↦ toSL2R z * k`, with `K` the stabilizer of `i`.
* `Matrix.SpecialLinearGroup.instMeasureSpaceSL2R`: the Haar measure on `SL(2, ℝ)` normalized by
  the hyperbolic area of `ℍ` and total mass one on `K`.

## Main results

* `Matrix.SpecialLinearGroup.instLocallyCompactSpace`: over a locally compact `T1` topological
  ring, `SL(n, R)` is locally compact.
* `UpperHalfPlane.isCompact_stabilizer_I`: the stabilizer of `i` in `SL(2, ℝ)` is compact.
* `Matrix.SpecialLinearGroup.instIsHaarMeasureSL2R`: the measure is a left Haar measure.
* `Matrix.SpecialLinearGroup.volume_preimage_smul_I`: the orbit map `g ↦ g • i` pushes it
  forward to the hyperbolic area measure of `ℍ`.

## References

* Frederick M. Goodman, Pierre de la Harpe, Vaughan F. R. Jones, *Coxeter Graphs and Towers of
  Algebras*, Springer, 1989, §3.3.
-/

public section

noncomputable section

open MeasureTheory Measure Set Topology UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]

/-- Over a locally compact `T1` topological ring, `SL(n, R)` is locally compact, as a closed
subset of the locally compact space of matrices. -/
instance instLocallyCompactSpace [IsTopologicalRing R] [T1Space R] [LocallyCompactSpace R] :
    LocallyCompactSpace (SpecialLinearGroup n R) :=
  isClosedEmbedding_val.locallyCompactSpace

/-- The Borel measurable structure of `SL(n, ℝ)`. -/
instance instMeasurableSpace : MeasurableSpace (SpecialLinearGroup n ℝ) := borel _

/-- `SL(n, ℝ)` carries its Borel measurable structure. -/
instance instBorelSpace : BorelSpace (SpecialLinearGroup n ℝ) := ⟨rfl⟩

end Matrix.SpecialLinearGroup

namespace UpperHalfPlane

/-- The stabilizer of `i` in `SL(2, ℝ)` is compact: it is the preimage of a point under the
proper orbit map `g ↦ g • i`. -/
theorem isCompact_stabilizer_I : IsCompact (MulAction.stabilizer SL(2, ℝ) I : Set SL(2, ℝ)) :=
  isProperMap_smul_I.isCompact_preimage (isCompact_singleton (x := I))

/-- The stabilizer of `i` in `SL(2, ℝ)` is a compact space. -/
instance instCompactSpaceStabilizerI : CompactSpace (MulAction.stabilizer SL(2, ℝ) I) :=
  isCompact_iff_compactSpace.mp isCompact_stabilizer_I

/-- `(toSL2R z)⁻¹ * g` fixes `i` when `g • i = z`. -/
theorem toSL2R_inv_mul_mem_stabilizer (g : SL(2, ℝ)) :
    (toSL2R (g • I))⁻¹ * g ∈ MulAction.stabilizer SL(2, ℝ) I := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, toSL2R_smul_I]

/-- **The splitting `SL(2, ℝ) ≃ₜ ℍ × K`.** Every `g ∈ SL(2, ℝ)` is uniquely `toSL2R z * k`, with
`z = g • i` and `k` in the stabilizer `K` of `i`. -/
@[expose] def toSL2RMulHomeomorph : ℍ × MulAction.stabilizer SL(2, ℝ) I ≃ₜ SL(2, ℝ) where
  toFun p := toSL2R p.1 * p.2
  invFun g := (g • I, ⟨(toSL2R (g • I))⁻¹ * g, toSL2R_inv_mul_mem_stabilizer g⟩)
  left_inv p := by
    obtain ⟨z, k, hk⟩ := p
    have hz : (toSL2R z * k) • I = z := by
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp hk, toSL2R_smul_I]
    ext <;> simp [hz]
  right_inv g := by simp
  continuous_toFun :=
    (continuous_toSL2R.comp continuous_fst).mul (continuous_subtypeVal.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_id.smul continuous_const).prodMk (Continuous.subtype_mk ?_ _)
    exact ((continuous_toSL2R.comp (continuous_id.smul continuous_const)).inv).mul continuous_id

@[simp]
theorem toSL2RMulHomeomorph_apply (p : ℍ × MulAction.stabilizer SL(2, ℝ) I) :
    toSL2RMulHomeomorph p = toSL2R p.1 * p.2 :=
  rfl

/-- Right multiplication by an element of the stabilizer of `i` does not move `toSL2R z • i = z`. -/
@[simp]
theorem toSL2R_mul_smul_I (z : ℍ) (k : MulAction.stabilizer SL(2, ℝ) I) :
    (toSL2R z * k) • I = z := by
  rw [mul_smul, MulAction.mem_stabilizer_iff.mp k.property, toSL2R_smul_I]

/-- The orbit map `g ↦ g • i` is the first coordinate of the splitting `ℍ × K ≃ₜ SL(2, ℝ)`. -/
theorem toSL2RMulHomeomorph_apply_smul_I (p : ℍ × MulAction.stabilizer SL(2, ℝ) I) :
    toSL2RMulHomeomorph p • I = p.1 :=
  toSL2R_mul_smul_I p.1 p.2

end UpperHalfPlane

namespace Matrix.SpecialLinearGroup

/-- The normalized Haar measure on the compact stabilizer `K` of `i`, of total mass one. -/
abbrev stabilizerIHaar : Measure (MulAction.stabilizer SL(2, ℝ) I) :=
  haarMeasure ⊤

/-- The normalized Haar measure of the stabilizer of `i` has total mass one. -/
instance instIsProbabilityMeasureStabilizerIHaar : IsProbabilityMeasure stabilizerIHaar :=
  ⟨by rw [← TopologicalSpace.PositiveCompacts.coe_top]; exact haarMeasure_self⟩

/-- **The Haar measure on `SL(2, ℝ)`.** It is the push-forward along the splitting
`ℍ × K ≃ₜ SL(2, ℝ)` of the product of the invariant measure `dx dy / y²` on `ℍ` and the Haar
measure of mass one on the stabilizer `K` of `i`. It is a left Haar measure
(`Matrix.SpecialLinearGroup.instIsHaarMeasureSL2R`), and the orbit map `g ↦ g • i` pushes it
forward to the hyperbolic area (`Matrix.SpecialLinearGroup.volume_preimage_smul_I`). -/
instance instMeasureSpaceSL2R : MeasureSpace SL(2, ℝ) where
  volume := (volume.prod stabilizerIHaar).map toSL2RMulHomeomorph

/-- The Haar measure of `SL(2, ℝ)` is the push-forward of the product measure on `ℍ × K`. -/
theorem volume_sl2r_eq :
    (volume : Measure SL(2, ℝ)) = (volume.prod stabilizerIHaar).map toSL2RMulHomeomorph :=
  rfl

/-- The Haar measure of a set is the product measure of its preimage in `ℍ × K`. -/
theorem volume_sl2r_apply (s : Set SL(2, ℝ)) :
    volume s = volume.prod stabilizerIHaar (toSL2RMulHomeomorph ⁻¹' s) := by
  rw [volume_sl2r_eq, ← toSL2RMulHomeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]

/-- **The orbit map `g ↦ g • i` is measure preserving.** The Haar measure of the preimage in
`SL(2, ℝ)` of a set `E ⊆ ℍ` is the hyperbolic area of `E`. -/
theorem volume_preimage_smul_I (E : Set ℍ) :
    volume ((· • I) ⁻¹' E : Set SL(2, ℝ)) = volume E := by
  have : toSL2RMulHomeomorph ⁻¹' ((· • I) ⁻¹' E : Set SL(2, ℝ)) = E ×ˢ univ := by
    ext p
    simp only [mem_preimage, toSL2RMulHomeomorph_apply_smul_I, mem_prod, mem_univ, and_true]
  rw [volume_sl2r_apply, this, prod_prod, measure_univ, mul_one]

/-- The orbit map `g ↦ g • i` is measure preserving from the Haar measure of `SL(2, ℝ)` to the
hyperbolic area of `ℍ`. -/
theorem measurePreserving_smul_I :
    MeasurePreserving (fun g : SL(2, ℝ) ↦ g • I) volume volume := by
  have hm : Measurable fun g : SL(2, ℝ) ↦ g • I := (continuous_id.smul continuous_const).measurable
  exact ⟨hm, Measure.ext fun E hE ↦ by rw [Measure.map_apply hm hE, volume_preimage_smul_I]⟩

/-- The `K`-coordinate of `g * toSL2R z`: the element `toSL2R (g • z)⁻¹ * g * toSL2R z` of the
stabilizer of `i`. -/
private def kappa (g : SL(2, ℝ)) (z : ℍ) : MulAction.stabilizer SL(2, ℝ) I :=
  ⟨(toSL2R (g • z))⁻¹ * (g * toSL2R z), by
    simpa [mul_smul] using toSL2R_inv_mul_mem_stabilizer (g * toSL2R z)⟩

/-- The `K`-coordinate `κ(g, z)` is continuous in `z`. -/
private theorem continuous_kappa (g : SL(2, ℝ)) : Continuous (kappa g) :=
  Continuous.subtype_mk ((continuous_toSL2R.comp (continuous_const.smul continuous_id)).inv.mul
    (continuous_const.mul continuous_toSL2R)) _

/-- The Haar measure of `SL(2, ℝ)` is left invariant: in the coordinates `ℍ × K` left translation
is a skew product of measure preserving maps. -/
instance instIsMulLeftInvariantSL2R : (volume : Measure SL(2, ℝ)).IsMulLeftInvariant := by
  refine ⟨fun g ↦ ?_⟩
  -- left translation by `g` is the skew product `(z, k) ↦ (g • z, κ(g, z) * k)` in coordinates
  have hskew : MeasurePreserving (fun p : ℍ × MulAction.stabilizer SL(2, ℝ) I ↦
      (g • p.1, kappa g p.1 * p.2)) (volume.prod stabilizerIHaar) (volume.prod stabilizerIHaar) :=
    (measurePreserving_smul g volume).skew_product (g := fun z k ↦ kappa g z * k)
      (((continuous_kappa g).comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun z ↦ map_mul_left_eq_self _ _)
  have hcomm : (g * ·) ∘ toSL2RMulHomeomorph = toSL2RMulHomeomorph ∘
      fun p : ℍ × MulAction.stabilizer SL(2, ℝ) I ↦ (g • p.1, kappa g p.1 * p.2) := by
    ext1 p
    simp [kappa, mul_assoc]
  rw [volume_sl2r_eq, Measure.map_map (measurable_const_mul g) toSL2RMulHomeomorph.measurable,
    hcomm, ← Measure.map_map toSL2RMulHomeomorph.measurable hskew.measurable, hskew.map_eq]

/-- The measure on `SL(2, ℝ)` is a left Haar measure: it is the push-forward along a homeomorphism
of a product measure finite on compact sets and positive on open sets. -/
instance instIsHaarMeasureSL2R : (volume : Measure SL(2, ℝ)).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := by
    rw [volume_sl2r_eq]
    exact IsFiniteMeasureOnCompacts.map _ _
  toIsOpenPosMeasure := by
    rw [volume_sl2r_eq]
    exact toSL2RMulHomeomorph.continuous.isOpenPosMeasure_map toSL2RMulHomeomorph.surjective

end Matrix.SpecialLinearGroup
