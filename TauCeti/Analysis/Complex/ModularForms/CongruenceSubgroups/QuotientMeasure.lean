/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.MeasureTheory.Group.OrbitQuotient
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The hyperbolic measure on the quotient `Γ \ ℍ`

For a subgroup `Γ ≤ SL(2, ℤ)`, this file puts the hyperbolic area measure on the orbit quotient
`Γ \ ℍ = MulAction.orbitRel.Quotient Γ ℍ` of the upper half-plane by the Möbius action of `Γ`.
It is the push-forward along the quotient map of the invariant measure `dx dy / y²` of `ℍ`,
restricted to a measurable fundamental domain.

A fundamental domain is taken for the *effective* image `Γ.map sl2zToPSL2R` of `Γ` in
`PSL(2, ℝ)`, not for `Γ` itself: when `-I ∈ Γ` the element `-I` acts trivially on `ℍ`, so no set
is a fundamental domain for `Γ`. Both groups have the same orbits
(`Subgroup.orbitRel_map_sl2zToPSL2R_iff`), so the measure lives on the quotient by `Γ` itself,
where `Γ`-invariant functions on `ℍ` descend. The measure does not depend on the choice of
fundamental domain (`Subgroup.quotientVolume_eq_map_restrict`), and its total mass is the
covolume of the effective image (`Subgroup.quotientVolume_univ`). For `Γ` of finite index, in
particular for every congruence subgroup (`CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`),
the total mass is `[SL(2, ℤ) : ±Γ] · π / 3`, counting the index of `Γ` with `-I` adjoined. At
level one this is `π / 3`, and at level two `6 · π / 3 = 2π`.

This measure is the base measure for the `L²` space of `Γ \ ℍ`, on which the hyperbolic
Laplacian of a congruence quotient acts; integrals against it are integrals over a fundamental
domain (`Subgroup.lintegral_quotientVolume`, `Subgroup.integral_quotientVolume`).

## Main declarations

* `Subgroup.quotientVolume`: the hyperbolic measure on `Γ \ ℍ`.
* `Subgroup.quotientVolume_eq_map_restrict`: it is the push-forward of `volume` restricted to any
  fundamental domain of the effective image of `Γ`.
* `Subgroup.quotientVolume_univ`: its total mass is the covolume of the effective image.
* `Subgroup.quotientVolume_univ_eq_withCenter_index_mul`: for `Γ` of finite index, the total mass is
  `[SL(2, ℤ) : ±Γ] · π / 3`, which is `[SL(2, ℤ) : Γ] · π / 3` when `-I ∈ Γ`
  (`Subgroup.quotientVolume_univ_eq_index_mul_of_neg_one_mem`).
* `Subgroup.measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm`: the effective
  projective orbit quotient is measurably equivalent to `Γ \ ℍ`, preserving the measures.
* `Subgroup.quotientVolume_apply_eq_zero_iff`: a set is null exactly when its full preimage
  in `ℍ` is null. In particular `Subgroup.instIsOpenPosMeasureQuotientVolume` gives full support.
* `Subgroup.instIsFiniteMeasureQuotientVolume`, `Subgroup.instNeZeroQuotientVolume`: the
  measure is finite for `Γ` of finite index and nonzero for every `Γ`.
* `Subgroup.quotientVolume_top_univ`, `CongruenceSubgroup.quotientVolume_Gamma_two_univ`: the
  areas `π / 3` of `SL(2, ℤ) \ ℍ` and `2π` of `Γ(2) \ ℍ`.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.1 and 4.1.
* Wenzhi Luo, Zeév Rudnick and Peter Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct.
  Anal. 5 (1995), 387–401, §1.
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace Subgroup

variable (Γ : Subgroup SL(2, ℤ))

/-- **The hyperbolic measure on `Γ \ ℍ`.** The push-forward along the quotient map
`ℍ → Γ \ ℍ` of the invariant measure `dx dy / y²` restricted to a measurable fundamental domain of
the effective image `Γ.map sl2zToPSL2R`. By `Subgroup.quotientVolume_eq_map_restrict` any such
fundamental domain gives the same measure. -/
noncomputable def quotientVolume : Measure (orbitRel.Quotient Γ ℍ) :=
  (volume.restrict (exists_isFundamentalDomain (Γ.map sl2zToPSL2R)).choose).map
    (Quotient.mk (orbitRel Γ ℍ))

/-- The preimage in `ℍ` of a set of `Γ \ ℍ` is invariant under the effective image of `Γ`. -/
private theorem preimage_smul_preimage_quotientMk (U : Set (orbitRel.Quotient Γ ℍ))
    (g : Γ.map sl2zToPSL2R) :
    (fun z : ℍ ↦ g • z) ⁻¹' (Quotient.mk (orbitRel Γ ℍ) ⁻¹' U) =
      Quotient.mk (orbitRel Γ ℍ) ⁻¹' U := by
  obtain ⟨_, γ, hγ, rfl⟩ := g
  ext z
  have : Quotient.mk (orbitRel Γ ℍ) (sl2zToPSL2R γ • z) = Quotient.mk (orbitRel Γ ℍ) z :=
    Quotient.sound ⟨⟨γ, hγ⟩, (sl2zToPSL2R_smul γ z).symm⟩
  simp only [mem_preimage, Subgroup.smul_def, this]

/-- **Independence of the fundamental domain.** The hyperbolic measure on `Γ \ ℍ` is the
push-forward of `volume` restricted to any measurable fundamental domain of the effective image of
`Γ` in `PSL(2, ℝ)`.

The proof adapts Mathlib's `MeasureTheory.IsFundamentalDomain.quotientMeasure_eq` to the quotient
by `Γ` rather than by its effective image. -/
theorem quotientVolume_eq_map_restrict {s : Set ℍ}
    (hs : IsFundamentalDomain (Γ.map sl2zToPSL2R) s) :
    Γ.quotientVolume = (volume.restrict s).map (Quotient.mk (orbitRel Γ ℍ)) := by
  ext U hU
  rw [quotientVolume, measure_map_restrict_apply _ _ hU, measure_map_restrict_apply _ _ hU]
  exact (exists_isFundamentalDomain (Γ.map sl2zToPSL2R)).choose_spec.2.2.measure_set_eq hs
    (measurableSet_quotient.mp hU) (Γ.preimage_smul_preimage_quotientMk U)

/-- The raw and projective orbit spaces of a modular subgroup are measurably equivalent,
with the class of each point sent to the class of that point. -/
noncomputable def orbitRelQuotientMeasurableEquivPSL2R :
    orbitRel.Quotient Γ ℍ ≃ᵐ orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ where
  toEquiv := Quotient.congrRight fun _ _ ↦ by
    simpa only [orbitRel_apply, mem_orbit_iff, Subtype.exists, Subgroup.mk_smul,
      exists_prop] using (Γ.orbitRel_map_sl2zToPSL2R_iff).symm
  measurable_toFun := measurable_from_quotient.mpr measurable_quotient_mk''
  measurable_invFun := measurable_from_quotient.mpr measurable_quotient_mk''

/-- Passing to the projective quotient sends the class of a point to the class of that point. -/
@[simp]
theorem orbitRelQuotientMeasurableEquivPSL2R_mk (z : ℍ) :
    Γ.orbitRelQuotientMeasurableEquivPSL2R (Quotient.mk (orbitRel Γ ℍ) z) =
      Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z := by rfl

/-- The inverse comparison sends the projective class of a point to its raw class. -/
@[simp]
theorem orbitRelQuotientMeasurableEquivPSL2R_symm_mk (z : ℍ) :
    Γ.orbitRelQuotientMeasurableEquivPSL2R.symm
      (Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z) = Quotient.mk (orbitRel Γ ℍ) z :=
  Γ.orbitRelQuotientMeasurableEquivPSL2R.symm_apply_eq.mpr
    (Γ.orbitRelQuotientMeasurableEquivPSL2R_mk z)

/-- The comparison from the projective quotient to the raw quotient preserves hyperbolic area. -/
theorem measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm :
    MeasurePreserving Γ.orbitRelQuotientMeasurableEquivPSL2R.symm
      (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume) Γ.quotientVolume where
  measurable := Γ.orbitRelQuotientMeasurableEquivPSL2R.symm.measurable
  map_eq := by
    obtain ⟨F, -, -, hF⟩ := exists_isFundamentalDomain (Γ.map sl2zToPSL2R)
    rw [hF.projection_respects_measure (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume),
      Γ.quotientVolume_eq_map_restrict hF,
      Measure.map_map Γ.orbitRelQuotientMeasurableEquivPSL2R.symm.measurable
        measurable_quotient_mk'']
    simp only [Function.comp_def, orbitRelQuotientMeasurableEquivPSL2R_symm_mk]

/-- A set in the modular quotient is null exactly when its full preimage in `ℍ` is null. -/
theorem quotientVolume_apply_eq_zero_iff (s : Set (orbitRel.Quotient Γ ℍ)) :
    Γ.quotientVolume s = 0 ↔ (volume : Measure ℍ) (Quotient.mk (orbitRel Γ ℍ) ⁻¹' s) = 0 := by
  rw [← Γ.measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm.map_eq,
    MeasurableEquiv.map_apply, QuotientMeasureEqMeasurePreimage.apply_eq_zero_iff
      (μ := (volume : Measure ℍ)), ← preimage_comp]
  simp only [Function.comp_def, orbitRelQuotientMeasurableEquivPSL2R_symm_mk]

/-- The hyperbolic quotient measure gives positive mass to every nonempty open set. -/
instance instIsOpenPosMeasureQuotientVolume : Γ.quotientVolume.IsOpenPosMeasure := by
  rw [← Γ.measurePreserving_orbitRelQuotientMeasurableEquivPSL2R_symm.map_eq]
  refine QuotientMeasureEqMeasurePreimage.isOpenPosMeasure_map
    (μ := (volume : Measure ℍ)) (orbitQuotientMeasure (Γ.map sl2zToPSL2R) volume)
    Γ.orbitRelQuotientMeasurableEquivPSL2R.symm.measurable ?_
    Γ.orbitRelQuotientMeasurableEquivPSL2R.symm.surjective
  simp only [Function.comp_def, orbitRelQuotientMeasurableEquivPSL2R_symm_mk]
  exact continuous_quotient_mk' (s := orbitRel Γ ℍ)

/-- The hyperbolic measure of a measurable set of `Γ \ ℍ` is the area of the part of a fundamental
domain lying over it. -/
theorem quotientVolume_apply {s : Set ℍ} (hs : IsFundamentalDomain (Γ.map sl2zToPSL2R) s)
    {U : Set (orbitRel.Quotient Γ ℍ)} (hU : MeasurableSet U) :
    Γ.quotientVolume U = volume (Quotient.mk (orbitRel Γ ℍ) ⁻¹' U ∩ s) := by
  rw [Γ.quotientVolume_eq_map_restrict hs, measure_map_restrict_apply _ _ hU]

/-- **The area of `Γ \ ℍ`** is the covolume of the effective image of `Γ` in `PSL(2, ℝ)`. -/
theorem quotientVolume_univ :
    Γ.quotientVolume univ = covolume (Γ.map sl2zToPSL2R) ℍ := by
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain (Γ.map sl2zToPSL2R)
  rw [Γ.quotientVolume_apply hs MeasurableSet.univ, preimage_univ, univ_inter,
    hs.covolume_eq_volume]

/-- **The area of `Γ \ ℍ` for `Γ` of finite index** is `[SL(2, ℤ) : ±Γ] · π / 3`: the index of
`Γ` with `-I` adjoined times the area `π / 3` of the level-one quotient. -/
theorem quotientVolume_univ_eq_withCenter_index_mul [Γ.FiniteIndex] :
    Γ.quotientVolume univ = Γ.withCenter.index * ENNReal.ofReal (Real.pi / 3) := by
  have : (Γ.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
    ⟨by rw [relIndex_map_sl2zToPSL2R]; exact FiniteIndex.index_ne_zero⟩
  rw [quotientVolume_univ, covolume_eq_index_mul_covolume Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R,
    ← relIndex, relIndex_map_sl2zToPSL2R, TauCeti.ModularGroup.covolume_psl2zToPSL2RRange]

/-- For `Γ` of finite index, in particular for a congruence subgroup, the quotient `Γ \ ℍ` has
finite hyperbolic area. -/
instance instIsFiniteMeasureQuotientVolume [Γ.FiniteIndex] : IsFiniteMeasure Γ.quotientVolume :=
  ⟨by
    rw [Γ.quotientVolume_univ_eq_withCenter_index_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top⟩

/-- The hyperbolic measure on `Γ \ ℍ` is nonzero: the quotient has positive area. -/
instance instNeZeroQuotientVolume : NeZero Γ.quotientVolume :=
  ⟨Measure.measure_univ_pos.mp <| by
    rw [quotientVolume_univ]
    exact covolume_pos <| Measure.measure_univ_pos.mp <| isOpen_univ.measure_pos _ univ_nonempty⟩

/-- **Integration over `Γ \ ℍ`** of an almost everywhere measurable nonnegative function is
integration of its lift over any fundamental domain of the effective image of `Γ`. -/
theorem lintegral_quotientVolume {s : Set ℍ} (hs : IsFundamentalDomain (Γ.map sl2zToPSL2R) s)
    {f : orbitRel.Quotient Γ ℍ → ℝ≥0∞} (hf : AEMeasurable f Γ.quotientVolume) :
    ∫⁻ x, f x ∂Γ.quotientVolume = ∫⁻ z in s, f (Quotient.mk (orbitRel Γ ℍ) z) := by
  rw [Γ.quotientVolume_eq_map_restrict hs] at hf ⊢
  exact lintegral_map' hf measurable_quotient_mk''.aemeasurable

/-- **Integration over `Γ \ ℍ`** of an almost everywhere strongly measurable function is
integration of its lift over any fundamental domain of the effective image of `Γ`. -/
theorem integral_quotientVolume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℍ} (hs : IsFundamentalDomain (Γ.map sl2zToPSL2R) s)
    {f : orbitRel.Quotient Γ ℍ → E} (hf : AEStronglyMeasurable f Γ.quotientVolume) :
    ∫ x, f x ∂Γ.quotientVolume = ∫ z in s, f (Quotient.mk (orbitRel Γ ℍ) z) := by
  rw [Γ.quotientVolume_eq_map_restrict hs] at hf ⊢
  exact integral_map measurable_quotient_mk''.aemeasurable hf

/-- **The area of `Γ \ ℍ` for `Γ` of finite index containing `-I`** is `[SL(2, ℤ) : Γ] · π / 3`.
This applies to `SL(2, ℤ)`, `Γ₀(N)` and `Γ(2)`. -/
theorem quotientVolume_univ_eq_index_mul_of_neg_one_mem [Γ.FiniteIndex] (h : -1 ∈ Γ) :
    Γ.quotientVolume univ = Γ.index * ENNReal.ofReal (Real.pi / 3) := by
  rw [quotientVolume_univ_eq_withCenter_index_mul,
    withCenter_eq_self_iff.mpr (Matrix.SpecialLinearGroup.center_le_iff_neg_one_mem.mpr h)]

/-- **The area of the level-one quotient** `SL(2, ℤ) \ ℍ` is `π / 3`. -/
theorem quotientVolume_top_univ :
    (⊤ : Subgroup SL(2, ℤ)).quotientVolume univ = ENNReal.ofReal (Real.pi / 3) := by
  rw [quotientVolume_univ_eq_index_mul_of_neg_one_mem _ (mem_top _), index_top, Nat.cast_one,
    one_mul]

end Subgroup

namespace CongruenceSubgroup

/-- **The area of `Γ(2) \ ℍ`** is `2π`: the group `Γ(2)` contains `-I` and has index
`|SL(2, ℤ/2ℤ)| = 6`. -/
theorem quotientVolume_Gamma_two_univ :
    (Gamma 2).quotientVolume Set.univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [Subgroup.quotientVolume_univ_eq_index_mul_of_neg_one_mem _
    (neg_one_mem_Gamma_iff.mpr dvd_rfl), index_Gamma_two, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by norm_num)]
  ring_nf

end CongruenceSubgroup
