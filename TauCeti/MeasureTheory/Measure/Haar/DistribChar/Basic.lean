/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.DistribChar

/-!
# Pushforward and transport of the distributive Haar character

Let a group `G` act distributively and continuously on a locally compact additive group `A`. The
distributive Haar character `MeasureTheory.distribHaarChar A g` is the factor by which `g` scales
images under its action: `μ (g • s) = distribHaarChar A g * μ s` for every regular additive Haar
measure `μ` on `A` (Mathlib's `MeasureTheory.distribHaarChar_mul`). This file records the
consequences used to compute such characters.

* Pushforwards carry the inverse factor
  (`MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul`), so `g` preserves `μ` exactly
  when its character is `1`.
* The character is transported along isomorphisms of topological additive groups intertwining
  two actions, in particular along ring isomorphisms that are homeomorphisms.
* A positive compact set has finite positive mass for every additive Haar measure, which is what
  Mathlib's criterion `MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul` needs to read off a
  character from one set.

## Main results

* `MeasureTheory.Measure.map_smul_eq_self_iff_distribHaarChar_eq_one`: the action of `g` preserves
  a Haar measure exactly when the character of `g` is `1`.
* `MeasureTheory.distribHaarChar_eq_of_continuousAddEquiv`,
  `MeasureTheory.distribHaarChar_map_ringEquiv`: transport of the character.
* `TopologicalSpace.PositiveCompacts.measure_ne_zero`,
  `TopologicalSpace.PositiveCompacts.measure_ne_top`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism, and restricted Haar products).
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) develops the same Haar-character API
  in `FLT/HaarMeasure/HaarChar/`; the transport lemmas correspond to
  `ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv` in `Ring.lean` (by Kevin Buzzard) and
  `mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv` in `AddEquiv.lean`.
-/

public section

open MeasureTheory Measure Set TopologicalSpace
open scoped NNReal ENNReal Pointwise

namespace TopologicalSpace.PositiveCompacts

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (K : PositiveCompacts X)
  (μ : Measure X)

/-- A positive compact set has positive mass for every measure that is positive on open sets. -/
theorem measure_ne_zero [μ.IsOpenPosMeasure] : μ K ≠ 0 :=
  (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'

/-- A positive compact set has finite mass for every measure that is finite on compact sets. -/
theorem measure_ne_top [IsFiniteMeasureOnCompacts μ] : μ K ≠ ∞ :=
  K.isCompact.measure_ne_top

end TopologicalSpace.PositiveCompacts

namespace MeasureTheory

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]

section Pushforward

variable [MeasurableSpace A] [BorelSpace A]

/-- The action of `g` preserves a regular additive Haar measure exactly when the distributive Haar
character of `g` is `1`. -/
theorem Measure.map_smul_eq_self_iff_distribHaarChar_eq_one (μ : Measure A) [μ.IsAddHaarMeasure]
    [μ.Regular] (g : G) :
    μ.map (g • ·) = μ ↔ distribHaarChar A g = 1 := by
  rw [map_smul_eq_inv_distribHaarChar_smul]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, inv_one, one_smul]⟩
  have h1 : addHaarScalarFactor ((distribHaarChar A g)⁻¹ • μ) μ = addHaarScalarFactor μ μ := by
    simp only [h]
  rw [addHaarScalarFactor_smul, addHaarScalarFactor_self, smul_eq_mul, mul_one] at h1
  exact inv_eq_one.mp h1

end Pushforward

section Transport

variable {H B : Type*} [Group H] [AddCommGroup B] [DistribMulAction H B] [TopologicalSpace B]
  [IsTopologicalAddGroup B] [LocallyCompactSpace B] [ContinuousConstSMul H B]

/-- **Transport of the Haar character.** If an isomorphism `f : A ≃ₜ+ B` of topological additive
groups intertwines the action of `g` on `A` with the action of `h` on `B`, then `g` and `h` have
the same distributive Haar character. -/
theorem distribHaarChar_eq_of_continuousAddEquiv (f : A ≃ₜ+ B) {g : G} {h : H}
    (hf : ∀ a, f (g • a) = h • f a) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  let μ : Measure A := addHaar
  have _ : (μ.map f).IsAddHaarMeasure := f.isAddHaarMeasure_map μ
  have _ : (μ.map f).Regular := Regular.map f.toHomeomorph
  have hf' : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  let K : PositiveCompacts A := Classical.arbitrary _
  have himage (t : Set A) : μ.map f (f '' t) = μ t := by
    rw [hf'.map_apply, Set.preimage_image_eq _ f.injective]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map f) (s := f '' K)
    (by rw [himage]; exact K.measure_ne_zero μ) (by rw [himage]; exact K.measure_ne_top μ) ?_
  have hsmul : h • f '' K = f '' (g • (K : Set A)) := by
    rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    simp only [hf]
  rw [hsmul, himage, himage, distribHaarChar_mul]

/-- **Transport of the Haar character along a ring isomorphism.** A ring isomorphism
`e : R ≃+* S` which is a homeomorphism preserves Haar characters. -/
theorem distribHaarChar_map_ringEquiv {R S : Type*} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [Ring S] [TopologicalSpace S]
    [IsTopologicalRing S] [LocallyCompactSpace S] (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (x : Rˣ) :
    distribHaarChar S (Units.map e.toMonoidHom x) = distribHaarChar R x :=
  distribHaarChar_eq_of_continuousAddEquiv
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := he' }
    fun a ↦ by simp [Units.smul_def]

end Transport

end MeasureTheory
