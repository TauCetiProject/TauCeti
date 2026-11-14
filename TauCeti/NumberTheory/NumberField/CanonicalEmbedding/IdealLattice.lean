/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.FractionalIdeal

/-!
# The index of one ideal lattice in another

An invertible fractional ideal `I` of a number field `K` is a full `ℤ`-lattice in `K`, and its
image `mixedEmbedding.idealLattice K I` is a full lattice in the mixed space.  If `J ≤ I` are two
such ideals, the index of `J` in `I` is the ratio of their absolute norms.  This is the
lattice-theoretic meaning of the norm of a fractional ideal: for an integral ideal `𝔞`, the
lattice of `I * 𝔞` has index `N 𝔞` in the lattice of `I`, which is how congruence conditions
modulo `𝔞` are counted among the lattice points of `I`.

The index is computed in `K` by `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`, and
transported to the mixed space along the injective embedding.

## Main definitions

* `Ideal.mixedBasisElem`: the `ν`-th `ℤ`-basis element of a nonzero integral ideal `I` in `K`,
  indexed by `NumberField.mixedEmbedding.index K`.
* `Ideal.mixedLatticeBasis`: an `ℝ`-basis of `mixedSpace K` indexed by `index K` whose `ℤ`-span is
  the mixed-space lattice of `I`.

## Main results

* `NumberField.mixedEmbedding.relIndex_idealLattice`: the index of the lattice of `J` in the
  lattice of `I` is `absNorm J / absNorm I`.
* `NumberField.mixedEmbedding.relIndex_idealLattice_mul_mk0`: the lattice of `I * 𝔞` has index
  `N 𝔞` in the lattice of `I`.
* `NumberField.mixedEmbedding.covolume_idealLattice_mul_mk0`: the covolume of the lattice of
  `I * 𝔞` is `N 𝔞` times the covolume of the lattice of `I`.
* `NumberField.mixedEmbedding.norm_eq_zero_iff_of_mem_idealLattice`: a point of `idealLattice K I`
  has mixed-space norm `0` if and only if it is `0`.
* `Ideal.mixedBasisElem_mem`, `Ideal.linearIndependent_mixedBasisElem`,
  `Ideal.span_int_mixedBasisElem`: `Ideal.mixedBasisElem` lies in `IsLocalization.coeSubmodule K I`,
  is `ℤ`-linearly independent, and spans `IsLocalization.coeSubmodule K I` over `ℤ`.
* `Ideal.mem_coeSubmodule_iff_mem_span_mixedLatticeBasis`,
  `Ideal.isAddFundamentalDomain_mixedLatticeBasis`,
  `Ideal.abs_det_stdBasis_mixedLatticeBasis`: the `ℤ`-span, fundamental domain, and change-of-basis
  determinant (`N(I) * covolume 𝓞_K`) of `Ideal.mixedLatticeBasis`.
-/

public section

open MeasureTheory Module NumberField NumberField.mixedEmbedding Set
open scoped nonZeroDivisors

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The ideal lattice of `I` is the image of `I` under the mixed embedding, as an additive
subgroup. -/
theorem idealLattice_toAddSubgroup (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealLattice K I).toAddSubgroup =
      (I : Submodule (𝓞 K) K).toAddSubgroup.map (mixedEmbedding K).toAddMonoidHom := by
  ext x
  simp [eq_comm]

/-- **The index of one ideal lattice in another is the ratio of the norms.**  For invertible
fractional ideals `J ≤ I` of a number field, the lattice of `J` has index `absNorm J / absNorm I`
in the lattice of `I`. -/
theorem relIndex_idealLattice {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJI : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ I) :
    ((idealLattice K J).toAddSubgroup.relIndex (idealLattice K I).toAddSubgroup : ℚ) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) /
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [idealLattice_toAddSubgroup, idealLattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective K),
    relIndex_fractionalIdeal_eq_absNorm_div_absNorm hJI]

/-- **The index of the lattice of `I * 𝔞`.**  For an integral ideal `𝔞`, the lattice of `I * 𝔞`
has index `N 𝔞` in the lattice of `I`. -/
theorem relIndex_idealLattice_mul_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔞 : (Ideal (𝓞 K))⁰) :
    (idealLattice K (I * FractionalIdeal.mk0 K 𝔞)).toAddSubgroup.relIndex
      (idealLattice K I).toAddSubgroup = Ideal.absNorm (𝔞 : Ideal (𝓞 K)) := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero
  have := relIndex_idealLattice (I := I) (J := I * FractionalIdeal.mk0 K 𝔞)
    (mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one)
  rw [Units.val_mul, map_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    mul_div_cancel_left₀ _ hI] at this
  exact_mod_cast this

open scoped Classical in
/-- **The covolume of the lattice of `I * 𝔞`** is `N 𝔞` times the covolume of the lattice of
`I`. -/
theorem covolume_idealLattice_mul_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔞 : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (idealLattice K (I * FractionalIdeal.mk0 K 𝔞)) =
      Ideal.absNorm (𝔞 : Ideal (𝓞 K)) * ZLattice.covolume (idealLattice K I) := by
  rw [covolume_idealLattice, covolume_idealLattice, Units.val_mul, map_mul,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

/-- A point of `idealLattice K I` has mixed-space norm `0` if and only if it is `0`. -/
theorem norm_eq_zero_iff_of_mem_idealLattice {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : mixedSpace K}
    (hx : x ∈ idealLattice K I) :
    mixedEmbedding.norm x = 0 ↔ x = 0 := by
  obtain ⟨b, -, rfl⟩ := (mem_idealLattice K I).mp hx
  rw [norm_eq_norm, Rat.cast_eq_zero, abs_eq_zero, Algebra.norm_eq_zero_iff,
    ← map_eq_zero_iff (mixedEmbedding K) (mixedEmbedding_injective K)]

end NumberField.mixedEmbedding

noncomputable section

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)}

/-- The nonzero fractional ideal unit attached to a nonzero ideal `I` of `𝓞 K`. -/
private abbrev toFractionalIdealUnit (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

open Classical in
/-- Equivalence between `index K` and the `ℤ`-basis index of `I`. -/
private def indexEquivChooseBasis (hI : I ≠ ⊥) :
    index K ≃ Free.ChooseBasisIndex ℤ (toFractionalIdealUnit hI) :=
  Fintype.equivOfCardEq <| by
    rw [← finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank,
      ← mixedEmbedding.finrank K, ← finrank_eq_card_basis (stdBasis K)]

open Classical in
/-- The `ν`-th `ℤ`-basis element of `I` in `K`, indexed by `index K`. -/
def mixedBasisElem (hI : I ≠ ⊥) (ν : index K) : K :=
  basisOfFractionalIdeal K (toFractionalIdealUnit hI) (indexEquivChooseBasis hI ν)

open Classical in
/-- An `ℝ`-basis of `mixedSpace K` indexed by `index K` whose `ℤ`-span is the mixed-space lattice
of the nonzero ideal `I`. -/
def mixedLatticeBasis (hI : I ≠ ⊥) : Basis (index K) ℝ (mixedSpace K) :=
  (fractionalIdealLatticeBasis K (toFractionalIdealUnit hI)).reindex
    (indexEquivChooseBasis hI).symm

/-- `Ideal.mixedLatticeBasis` embeds `Ideal.mixedBasisElem` via `mixedEmbedding K`. -/
@[simp]
theorem mixedLatticeBasis_apply (hI : I ≠ ⊥) (ν : index K) :
    I.mixedLatticeBasis hI ν = mixedEmbedding K (I.mixedBasisElem hI ν) := by
  classical
  rw [mixedLatticeBasis, Basis.reindex_apply, Equiv.symm_symm,
    fractionalIdealLatticeBasis_apply, mixedBasisElem]

/-- A scalar `x : K` lies in `I` if and only if its mixed embedding lies in the `ℤ`-span of
`I.mixedLatticeBasis hI`. -/
theorem mem_coeSubmodule_iff_mem_span_mixedLatticeBasis (hI : I ≠ ⊥) (x : K) :
    x ∈ IsLocalization.coeSubmodule K I ↔
      mixedEmbedding K x ∈ Submodule.span ℤ (range (I.mixedLatticeBasis hI)) := by
  classical
  rw [mixedLatticeBasis, Basis.coe_reindex, range_comp, Equiv.range_eq_univ, image_univ,
    span_idealLatticeBasis, mem_idealLattice]
  refine ⟨fun hx ↦ ⟨x, ?_, rfl⟩, fun ⟨y, hy, hyx⟩ ↦ ?_⟩
  · simpa [toFractionalIdealUnit] using hx
  · obtain rfl := mixedEmbedding_injective K hyx
    simpa [toFractionalIdealUnit] using hy

/-- The family `I.mixedBasisElem hI` is linearly independent over `ℤ`. -/
theorem linearIndependent_mixedBasisElem (hI : I ≠ ⊥) :
    LinearIndependent ℤ (I.mixedBasisElem hI) :=
  ((basisOfFractionalIdeal K (toFractionalIdealUnit hI)).linearIndependent.restrict_scalars' ℤ).comp
    _ (indexEquivChooseBasis hI).injective

open Classical in
private theorem mixedBasisElem_eq_comp (hI : I ≠ ⊥) :
    I.mixedBasisElem hI =
      basisOfFractionalIdeal K (toFractionalIdealUnit hI) ∘ indexEquivChooseBasis hI :=
  funext fun _ ↦ rfl

/-- The `ℤ`-span of `I.mixedBasisElem hI` in `K` is `IsLocalization.coeSubmodule K I`. -/
@[simp]
theorem span_int_mixedBasisElem (hI : I ≠ ⊥) :
    Submodule.span ℤ (range (I.mixedBasisElem hI)) =
      (IsLocalization.coeSubmodule K I).restrictScalars ℤ := by
  classical
  ext x
  rw [I.mixedBasisElem_eq_comp hI, Submodule.restrictScalars_mem, range_comp, Equiv.range_eq_univ,
    image_univ, mem_span_basisOfFractionalIdeal]
  simp [toFractionalIdealUnit]

/-- Every element `I.mixedBasisElem hI ν` belongs to `IsLocalization.coeSubmodule K I`. -/
theorem mixedBasisElem_mem (hI : I ≠ ⊥) (ν : index K) :
    I.mixedBasisElem hI ν ∈ IsLocalization.coeSubmodule K I := by
  rw [← Submodule.restrictScalars_mem ℤ, ← I.span_int_mixedBasisElem hI]
  exact Submodule.subset_span (mem_range_self ν)

open Classical in
/-- The `ℤ`-fundamental domain of `I.mixedLatticeBasis hI` is a fundamental domain for the
mixed-space lattice of `I`. -/
theorem isAddFundamentalDomain_mixedLatticeBasis (hI : I ≠ ⊥) :
    IsAddFundamentalDomain
      (idealLattice K
        (Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)))
      (ZSpan.fundamentalDomain (I.mixedLatticeBasis hI)) := by
  rw [mixedLatticeBasis, ZSpan.fundamentalDomain_reindex]
  exact fundamentalDomain_idealLattice K (toFractionalIdealUnit hI)

open Classical in
/-- The change-of-basis determinant from `stdBasis K` to `I.mixedLatticeBasis hI` has absolute
value `N(I) * covolume (mixedEmbedding.integerLattice K)`. -/
theorem abs_det_stdBasis_mixedLatticeBasis (hI : I ≠ ⊥) :
    |(stdBasis K).det (I.mixedLatticeBasis hI)| =
      (I.absNorm : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice K) := by
  have hcov : ZLattice.covolume (idealLattice K (toFractionalIdealUnit hI)) =
      |(stdBasis K).det (I.mixedLatticeBasis hI)| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
        (I.isAddFundamentalDomain_mixedLatticeBasis hI), measureReal_def,
      ZSpan.measure_fundamentalDomain (I.mixedLatticeBasis hI) volume (stdBasis K),
      volume_fundamentalDomain_stdBasis, mul_one, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [← hcov, covolume_idealLattice, covolume_integerLattice]
  simp [toFractionalIdealUnit, FractionalIdeal.coeIdeal_absNorm, mul_assoc]

end Ideal

end
