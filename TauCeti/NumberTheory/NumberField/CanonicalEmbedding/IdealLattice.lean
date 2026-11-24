/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
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
* `NumberField.mixedEmbedding.idealToIntegerLattice`: additive embedding of an integral ideal
  into the mixed-space integer lattice `idealLattice K 1`.
* `NumberField.mixedEmbedding.idealEquivIdealLattice` and
  `NumberField.mixedEmbedding.neZeroIdealEquivIdealLattice`: additive and nonzero-point
  equivalences between a nonzero integral ideal `𝔞` and `idealLattice K (FractionalIdeal.mk0 K 𝔞)`.
* `NumberField.mixedEmbedding.fractionalIdealEquivIdealLattice` and
  `NumberField.mixedEmbedding.neZeroFractionalIdealEquivIdealLattice`: additive and nonzero-point
  equivalences between an invertible fractional ideal `I` and `idealLattice K I`.

## Main results

* `NumberField.mixedEmbedding.relIndex_idealLattice`: the index of the lattice of `J` in the
  lattice of `I` is `absNorm J / absNorm I`.
* `NumberField.mixedEmbedding.relIndex_idealLattice_mul_mk0`: the lattice of `I * 𝔞` has index
  `N 𝔞` in the lattice of `I`.
* `NumberField.mixedEmbedding.covolume_idealLattice_mul_mk0`: the covolume of the lattice of
  `I * 𝔞` is `N 𝔞` times the covolume of the lattice of `I`.
* `NumberField.mixedEmbedding.norm_ne_zero_of_mem_idealLattice`: the nonzero points of an ideal
  lattice have nonzero norm.
* `NumberField.mixedEmbedding.mixedEmbedding_mul_mem_idealLattice_iff`: multiplication by the
  image of `a ∈ Kˣ` carries the lattice of `I` onto the lattice of `(a) I`.
* `NumberField.mixedEmbedding.norm_coe_idealLattice_eq_zero_iff`: a point of `idealLattice K I`
  has mixed norm zero iff it is zero.
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

/-- A nonzero point of an ideal lattice has nonzero norm: it is the image of a nonzero element of
`K`, whose norm `|N(a)|` does not vanish. -/
theorem norm_ne_zero_of_mem_idealLattice {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : mixedSpace K}
    (hx : x ∈ idealLattice K I) (h0 : x ≠ 0) : mixedEmbedding.norm x ≠ 0 := by
  obtain ⟨a, -, rfl⟩ := (mem_idealLattice K I).mp hx
  exact fun h ↦ h0 ((norm_eq_zero_iff' (mem_range_self a)).mp h)

/-- Multiplication by the image of `a ∈ Kˣ` carries the lattice of `I` onto the lattice of
`(a) I`. -/
theorem mixedEmbedding_mul_mem_idealLattice_iff (a : Kˣ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {x : mixedSpace K} :
    mixedEmbedding K (a : K) * x ∈ idealLattice K (toPrincipalIdeal (𝓞 K) K a * I) ↔
      x ∈ idealLattice K I := by
  simp only [mem_idealLattice, Units.val_mul, coe_toPrincipalIdeal, SetLike.mem_coe,
    FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
    exact ⟨z, hz, (a.isUnit.map (mixedEmbedding K)).mul_right_injective
      ((map_mul _ _ _).symm.trans h)⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, map_mul _ _ _⟩

/-- A point of `idealLattice K I` has mixed norm zero if and only if it is zero. -/
@[simp]
theorem norm_coe_idealLattice_eq_zero_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : idealLattice K I} :
    mixedEmbedding.norm (x : mixedSpace K) = 0 ↔ x = 0 := by
  obtain ⟨a, _, ha⟩ := (mem_idealLattice K I).mp x.property
  rw [← ha, norm_eq_zero_iff' ⟨a, rfl⟩, ha, Submodule.coe_eq_zero]

omit [NumberField K] in
/-- The `ℤ`-linear embedding of an integral ideal `𝔞` into `mixedSpace K`. -/
private noncomputable def idealToMixedSpace (𝔞 : Ideal (𝓞 K)) : 𝔞 →ₗ[ℤ] mixedSpace K :=
  (mixedEmbedding K).toIntAlgHom.toLinearMap.comp
    (((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).comp (𝔞.subtype.restrictScalars ℤ))

omit [NumberField K] in
@[simp]
private theorem idealToMixedSpace_apply (𝔞 : Ideal (𝓞 K)) (a : 𝔞) :
    idealToMixedSpace (K := K) 𝔞 a = mixedEmbedding K ((a : 𝓞 K) : K) :=
  rfl

private theorem idealToMixedSpace_injective (𝔞 : Ideal (𝓞 K)) :
    Function.Injective (idealToMixedSpace (K := K) 𝔞) := fun _ _ hab ↦
  Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective K hab))

omit [NumberField K] in
/-- Embed an integral ideal `𝔞` of `𝓞 K` into the mixed-space integer lattice `idealLattice K 1`. -/
noncomputable def idealToIntegerLattice (𝔞 : Ideal (𝓞 K)) : 𝔞 →+ idealLattice K 1 :=
  ((idealToMixedSpace (K := K) 𝔞).codRestrict (idealLattice K 1) fun a ↦
    (mem_idealLattice K 1).mpr ⟨((a : 𝓞 K) : K), by
      have h1 : ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
          ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by simp
      change ((a : 𝓞 K) : K) ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      rw [h1]
      exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, trivial, rfl⟩, rfl⟩).toAddMonoidHom

omit [NumberField K] in
/-- The underlying `mixedSpace K` vector of `idealToIntegerLattice 𝔞 a` is `mixedEmbedding K a`. -/
@[simp]
theorem coe_idealToIntegerLattice (𝔞 : Ideal (𝓞 K)) (a : 𝔞) :
    ((idealToIntegerLattice 𝔞 a : idealLattice K 1) : mixedSpace K) =
      mixedEmbedding K ((a : 𝓞 K) : K) := by
  simp [idealToIntegerLattice]

/-- `idealToIntegerLattice 𝔞` is injective. -/
theorem idealToIntegerLattice_injective (𝔞 : Ideal (𝓞 K)) :
    Function.Injective (idealToIntegerLattice (K := K) 𝔞) := fun _ _ hab ↦
  idealToMixedSpace_injective 𝔞 (congrArg Subtype.val hab)

/-- A point of `mixedSpace K` belongs to `idealLattice K (FractionalIdeal.mk0 K 𝔞)` if and only
if it is the mixed embedding of an element of `𝔞`. -/
theorem mem_idealLattice_mk0 {𝔞 : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ idealLattice K (FractionalIdeal.mk0 K 𝔞) ↔
      ∃ a : (𝔞 : Ideal (𝓞 K)), mixedEmbedding K ((a : 𝓞 K) : K) = x := by
  rw [mem_idealLattice]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := hz
    rw [FractionalIdeal.mem_coeIdeal (𝓞 K)⁰] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨((a : 𝓞 K) : K),
      (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, a.property, rfl⟩, rfl⟩

/-- Additive equivalence between a nonzero integral ideal `𝔞` and
`idealLattice K (FractionalIdeal.mk0 K 𝔞)`. -/
noncomputable def idealEquivIdealLattice (𝔞 : (Ideal (𝓞 K))⁰) :
    (𝔞 : Ideal (𝓞 K)) ≃+ idealLattice K (FractionalIdeal.mk0 K 𝔞) :=
  ((LinearEquiv.ofInjective (idealToMixedSpace (K := K) (𝔞 : Ideal (𝓞 K)))
      (idealToMixedSpace_injective (𝔞 : Ideal (𝓞 K)))).trans
    (LinearEquiv.ofEq _ (idealLattice K (FractionalIdeal.mk0 K 𝔞)) (by
      ext x
      rw [LinearMap.mem_range, mem_idealLattice_mk0]
      simp))).toAddEquiv

/-- The underlying `mixedSpace K` vector of `idealEquivIdealLattice 𝔞 a` is `mixedEmbedding K a`. -/
@[simp]
theorem coe_idealEquivIdealLattice (𝔞 : (Ideal (𝓞 K))⁰) (a : (𝔞 : Ideal (𝓞 K))) :
    ((idealEquivIdealLattice 𝔞 a : idealLattice K (FractionalIdeal.mk0 K 𝔞)) : mixedSpace K) =
      mixedEmbedding K ((a : 𝓞 K) : K) := by
  simp [idealEquivIdealLattice]

/-- Equivalence between the nonzero elements of a nonzero integral ideal `𝔞` and the nonzero
points of `idealLattice K (FractionalIdeal.mk0 K 𝔞)`. -/
noncomputable def neZeroIdealEquivIdealLattice (𝔞 : (Ideal (𝓞 K))⁰) :
    {a : (𝔞 : Ideal (𝓞 K)) // a ≠ 0} ≃
      {x : idealLattice K (FractionalIdeal.mk0 K 𝔞) // x ≠ 0} :=
  Equiv.subtypeEquiv (idealEquivIdealLattice 𝔞).toEquiv fun a ↦ by simp

/-- The underlying `mixedSpace K` vector of `neZeroIdealEquivIdealLattice 𝔞 a` is
`mixedEmbedding K a`. -/
@[simp]
theorem coe_neZeroIdealEquivIdealLattice (𝔞 : (Ideal (𝓞 K))⁰)
    (a : {a : (𝔞 : Ideal (𝓞 K)) // a ≠ 0}) :
    ((neZeroIdealEquivIdealLattice 𝔞 a :
      idealLattice K (FractionalIdeal.mk0 K 𝔞)) : mixedSpace K) =
      mixedEmbedding K (((a : (𝔞 : Ideal (𝓞 K))) : 𝓞 K) : K) := by
  simp [neZeroIdealEquivIdealLattice]

/-- Additive equivalence between an invertible fractional ideal `I` and `idealLattice K I`. -/
noncomputable def fractionalIdealEquivIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (I : Submodule (𝓞 K) K) ≃+ idealLattice K I :=
  (LinearEquiv.ofInjective
    ((mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ
      ((I : Submodule (𝓞 K) K).subtype.restrictScalars ℤ))
    (show Function.Injective ((mixedEmbedding K).toIntAlgHom.toLinearMap ∘ₗ
        ((I : Submodule (𝓞 K) K).subtype.restrictScalars ℤ)) from
      fun _ _ hab ↦ Subtype.ext (mixedEmbedding_injective K hab))).toAddEquiv

/-- The underlying `mixedSpace K` vector of `fractionalIdealEquivIdealLattice I a` is
`mixedEmbedding K a`. -/
@[simp]
theorem coe_fractionalIdealEquivIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : (I : Submodule (𝓞 K) K)) :
    ((fractionalIdealEquivIdealLattice I a : idealLattice K I) : mixedSpace K) =
      mixedEmbedding K (a : K) := by
  simp [fractionalIdealEquivIdealLattice]

/-- Equivalence between the nonzero elements of an invertible fractional ideal `I` and the nonzero
points of `idealLattice K I`. -/
noncomputable def neZeroFractionalIdealEquivIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {a : (I : Submodule (𝓞 K) K) // a ≠ 0} ≃
      {x : idealLattice K I // x ≠ 0} :=
  Equiv.subtypeEquiv (fractionalIdealEquivIdealLattice I).toEquiv fun _ ↦ by simp

/-- The underlying `mixedSpace K` vector of `neZeroFractionalIdealEquivIdealLattice I a` is
`mixedEmbedding K a`. -/
@[simp]
theorem coe_neZeroFractionalIdealEquivIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0}) :
    ((neZeroFractionalIdealEquivIdealLattice I a : idealLattice K I) : mixedSpace K) =
      mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K) := by
  simp [neZeroFractionalIdealEquivIdealLattice]

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
