/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.NumberTheory.Modular
public import TauCeti.NumberTheory.Modular.Stabilizer

/-!
# The level-one modular group as a cofinite Fuchsian group

The effective group acting on the upper half-plane at level one is the image of
`PSL(2, ℤ)` in `PSL(2, ℝ)`, not `SL(2, ℤ)`: the latter still contains the central matrix
`-I`, which acts trivially. This file proves that the projective image is a discrete cofinite
subgroup of `PSL(2, ℝ)`.

The standard open modular fundamental domain is transported from the `PSL(2, ℤ)` action to
its image in `PSL(2, ℝ)`. Its finite hyperbolic area then proves cofiniteness. This supplies the
effective level-one input for quotient and compactification constructions.

The elliptic data of the effective group are transported from `PSL(2, ℤ)` in the same way: the
stabilizers of `i` and `ρ` have orders `2` and `3`, and every point outside their two orbits has
trivial stabilizer. So the free locus of the level-one quotient is the complement of exactly two
orbits.

## Main results

* `TauCeti.ModularGroup.isFundamentalDomain_fdo_psl2zToPSL2RRange`: the standard open modular
  domain is a fundamental domain for the projective image in `PSL(2, ℝ)`.
* `TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange`: that image is a cofinite Fuchsian group.
* `TauCeti.ModularGroup.card_stabilizer_psl2zToPSL2RRange_I` and
  `TauCeti.ModularGroup.card_stabilizer_psl2zToPSL2RRange_ρ`: the elliptic orders `2` and `3`.
* `TauCeti.ModularGroup.stabilizer_psl2zToPSL2RRange_eq_bot_iff`: a stabilizer is trivial exactly
  off the orbits of `i` and `ρ`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3–2.4.
* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer,
  1973, Chapter VII.
-/

public section

noncomputable section

open MeasureTheory MulAction UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti.ModularGroup

/-- The standard open modular domain is a fundamental domain for the image of `PSL(2, ℤ)` in
`PSL(2, ℝ)`. It presents the effective level-one quotient and supplies the finite-area domain
used to prove that the projective image is cofinite. -/
theorem isFundamentalDomain_fdo_psl2zToPSL2RRange :
    IsFundamentalDomain psl2zToPSL2R.range (_root_.ModularGroup.fdo : Set ℍ) volume := by
  simpa only [Set.preimage_id] using
    _root_.ModularGroup.isFundamentalDomain_fdo.preimage_of_equiv
      (Measure.QuasiMeasurePreserving.id volume)
      (MonoidHom.ofInjective psl2zToPSL2R_injective).bijective
      fun g τ ↦ by
        simp only [id_eq, MonoidHom.ofInjective_apply, Subgroup.smul_def,
          UpperHalfPlane.psl2zToPSL2R_smul]

/-- The image of `PSL(2, ℤ)` in `PSL(2, ℝ)` is a cofinite Fuchsian group. -/
theorem isCofinite_psl2zToPSL2RRange : psl2zToPSL2R.range.IsCofinite := by
  apply isFundamentalDomain_fdo_psl2zToPSL2RRange.isCofinite_of_volume_ne_top
  exact ne_of_lt <| by
    rw [← measure_congr _root_.ModularGroup.fd_ae_eq_fdo]
    exact _root_.ModularGroup.volume_fd_lt_top

/-! ### Elliptic points -/

/-- The point stabilizers of the effective level-one group are those of `PSL(2, ℤ)`, transported
along the injective homomorphism `psl2zToPSL2R`. -/
theorem card_stabilizer_psl2zToPSL2RRange (z : ℍ) :
    Nat.card (stabilizer psl2zToPSL2R.range z) = Nat.card (stabilizer PSL(2, ℤ) z) :=
  TauCeti.card_stabilizer_congr (f := id) (MonoidHom.ofInjective psl2zToPSL2R_injective) z
    (fun g ↦ by
      rw [id, id, Subgroup.smul_def, MonoidHom.ofInjective_apply, psl2zToPSL2R_smul])
    fun _ h ↦ h

/-- Two points lie in the same orbit of the effective level-one group exactly when they lie in
the same orbit of `SL(2, ℤ)`. -/
theorem orbitRel_psl2zToPSL2RRange_iff {z w : ℍ} :
    orbitRel psl2zToPSL2R.range ℍ z w ↔ orbitRel SL(2, ℤ) ℍ z w := by
  simp only [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, p, rfl⟩, h⟩
    induction p using QuotientGroup.induction_on with
    | H a =>
      exact ⟨a, by simpa [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul] using h⟩
  · rintro ⟨a, h⟩
    exact ⟨⟨psl2zToPSL2R (a : PSL(2, ℤ)), a, rfl⟩,
      by simpa [Subgroup.smul_def, UpperHalfPlane.psl2zToPSL2R_smul] using h⟩

/-- The stabilizer of `i` in the effective level-one group has order `2`. -/
theorem card_stabilizer_psl2zToPSL2RRange_I :
    Nat.card (stabilizer psl2zToPSL2R.range I) = 2 := by
  rw [card_stabilizer_psl2zToPSL2RRange, card_stabilizer_psl_I]

/-- The stabilizer of `ρ` in the effective level-one group has order `3`. -/
theorem card_stabilizer_psl2zToPSL2RRange_ρ :
    Nat.card (stabilizer psl2zToPSL2R.range ρ) = 3 := by
  rw [card_stabilizer_psl2zToPSL2RRange, card_stabilizer_psl_ρ]

/-- **The elliptic points of the level-one group.** The stabilizer of `z` in the effective
level-one group is trivial exactly when `z` lies in neither the orbit of `i` nor that of `ρ`. -/
theorem stabilizer_psl2zToPSL2RRange_eq_bot_iff (z : ℍ) :
    stabilizer psl2zToPSL2R.range z = ⊥ ↔
      Quotient.mk (orbitRel psl2zToPSL2R.range ℍ) z ≠ Quotient.mk _ I ∧
        Quotient.mk (orbitRel psl2zToPSL2R.range ℍ) z ≠ Quotient.mk _ ρ := by
  have hq (w : ℍ) : Quotient.mk (orbitRel psl2zToPSL2R.range ℍ) z = Quotient.mk _ w ↔
      (Quotient.mk'' z : orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' w := by
    rw [Quotient.eq, Quotient.eq'', orbitRel_psl2zToPSL2RRange_iff]
  rw [← Subgroup.card_eq_one, card_stabilizer_psl2zToPSL2RRange, ← ellipticOrder_mk, ne_eq, ne_eq,
    hq, hq]
  refine ⟨fun h ↦ ⟨fun hI ↦ ?_, fun hρ ↦ ?_⟩,
    fun h ↦ ellipticOrder_eq_one_of_orbit_ne_I_of_orbit_ne_ρ h.1 h.2⟩
  · rw [hI, ellipticOrder_I] at h
    omega
  · rw [hρ, ellipticOrder_ρ] at h
    omega

end TauCeti.ModularGroup
