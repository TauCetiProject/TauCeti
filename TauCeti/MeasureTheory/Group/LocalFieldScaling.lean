/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.LocalField.Basic
import TauCeti.LinearAlgebra.FreeModule.CardQuotient
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology

/-!
# Scaling of Haar measure on `ι → K` under integral matrices

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `A` be a
square matrix over `𝒪[K]` whose determinant is associated to `ϖ ^ k` for a uniformizer `ϖ`.
Acting on `ι → K` by `mulVec`, `A` multiplies Haar measure by `q ^ (-k)`. This is the
nonarchimedean analogue of Mathlib's `MeasureTheory.Measure.addHaar_image_linearMap`, where the
factor is `|det|` for a real vector space.

The proof runs through the lattice index. The image under `A` of the integer box
`∏ i, 𝒪[K]` is a subgroup of index `q ^ k` in it
(`Matrix.card_quotient_range_mulVecLin_eq_pow`), so the box is the disjoint union of `q ^ k`
translates of that image, and Mathlib's `MeasureTheory.AddSubgroup.index_mul_measure` turns this
into the measure identity. On a translate of a scaled box — that is, on a ball of `ι → K` — the
same identity holds for every left-invariant measure, with no regularity hypothesis. For a general
set the measure `s ↦ μ (A '' s)` is again a Haar measure, so by uniqueness of Haar measure it is a
constant multiple of `μ`, and the box computes the constant; this needs `μ` to be regular.

Specializing to diagonal matrices gives the volume of a box of ideals: the box whose `i`-th factor
is `𝓂[K] ^ e i` is the image of the integer box under the diagonal matrix with entries `ϖ ^ e i`,
whose determinant is `ϖ ^ ∑ i, e i`, so it has `q ^ (-∑ i, e i)` times the measure of the box.

These volumes are the change of variables in Serre's proof of his mass formula for totally
ramified extensions, where `A` is the matrix of multiplication by an element of the ring of
integers of an extension of `K` in an integral basis and `k` is the valuation of its norm.

## Main definitions

* `TauCeti.integerBox K ι`: the integer box `∏ i, 𝒪[K]` in `ι → K`.

## Main results

* `TauCeti.isOpen_integerBox`, `TauCeti.isCompact_integerBox`: the integer box is open and compact.
* `TauCeti.univ_pi_image_maximalIdeal_pow_subset`,
  `TauCeti.isClosed_univ_pi_image_maximalIdeal_pow`,
  `TauCeti.measurableSet_univ_pi_image_maximalIdeal_pow`: boxes of ideal powers shrink as the
  exponents grow, and are closed and measurable.

* `MeasureTheory.Measure.measure_image_mulVec_integerBox`: for a left-invariant `μ`,
  the image of the integer box has measure `q ^ (-k)` times that of the box.
* `MeasureTheory.Measure.measure_image_mulVec_vadd_smul_integerBox`: the same for every
  ball `x +ᵥ c • ∏ i, 𝒪[K]` with `c ≠ 0`.
* `MeasureTheory.Measure.measure_univ_pi_image_maximalIdeal_pow`: for a left-invariant `μ`
  normalized on the integer box, the box with factors `𝓂[K] ^ e i` has volume `q ^ (-∑ i, e i)`.
* `MeasureTheory.Measure.addHaar_image_mulVec`: for a regular Haar measure `μ`,
  `μ (A '' s) = q ^ (-k) * μ s` for every set `s`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open Set ValuativeRel
open scoped ENNReal Pointwise

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

variable (K) in
/-- The integer box `∏ i, 𝒪[K]` of `ι → K`, on which Haar measure on `ι → K` is normalized. -/
noncomputable def integerBox (ι : Type*) : Set (ι → K) :=
  univ.pi fun _ ↦ (𝒪[K] : Set K)

/-- Membership in the integer box: every coordinate is integral. -/
@[simp]
theorem mem_integerBox {ι : Type*} {a : ι → K} : a ∈ integerBox K ι ↔ ∀ i, a i ∈ 𝒪[K] := by
  simp [integerBox]

/-- The integer box is the product of copies of `𝒪[K]`. -/
theorem integerBox_def {ι : Type*} : integerBox K ι = univ.pi fun _ ↦ (𝒪[K] : Set K) :=
  (rfl)

/-- Boxes of ideal powers shrink as the exponents grow. -/
theorem univ_pi_image_maximalIdeal_pow_subset {ι : Type*} {e e' : ι → ℕ} (h : e' ≤ e) :
    (univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) ⊆
      univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e' i) :=
  pi_mono fun i _ ↦ image_mono <| Ideal.pow_le_pow_right (h i)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] {ι : Type*}

/-- The integer box is open. -/
theorem isOpen_integerBox [Finite ι] : IsOpen (integerBox K ι) := by
  rw [integerBox_def]
  exact isOpen_set_pi finite_univ fun _ _ ↦ Valuation.isOpen_integer

/-- The integer box is compact. -/
theorem isCompact_integerBox : IsCompact (integerBox K ι) := by
  rw [integerBox_def]
  exact isCompact_univ_pi fun _ ↦
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[K]))

/-- A box of ideal powers is closed. -/
theorem isClosed_univ_pi_image_maximalIdeal_pow (e : ι → ℕ) :
    IsClosed (univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) :=
  isClosed_set_pi fun i _ ↦ (isCompact_image_maximalIdeal_pow K (e i)).isClosed

/-- A box of ideal powers is measurable. -/
theorem measurableSet_univ_pi_image_maximalIdeal_pow [MeasurableSpace (ι → K)]
    [OpensMeasurableSpace (ι → K)] (e : ι → ℕ) :
    MeasurableSet (univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) :=
  (isClosed_univ_pi_image_maximalIdeal_pow e).measurableSet

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → K)] [BorelSpace (ι → K)]

/-- **The scaling law on the integer box.** If the determinant of a square matrix `A` over
`𝒪[K]` is associated to `ϖ ^ k` for a uniformizer `ϖ`, then for every left-invariant measure on
`ι → K`, the image of the integer box `∏ i, 𝒪[K]` under `A` has `q ^ (-k)` times the measure of
the box, where `q = Nat.card 𝓀[K]`. -/
theorem measure_image_mulVec_integerBox (μ : Measure (ι → K)) [μ.IsAddLeftInvariant]
    {A : Matrix ι ι 𝒪[K]} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    (hk : Associated A.det (ϖ ^ k)) :
    μ ((A.map (algebraMap 𝒪[K] K)).mulVec '' integerBox K ι) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k * μ (integerBox K ι) := by
  -- Pull `μ` back to the compact group `ι → 𝒪[K]`, whose image in `ι → K` is the box.
  let _ : MeasurableSpace (ι → 𝒪[K]) := borel _
  have _ : BorelSpace (ι → 𝒪[K]) := ⟨rfl⟩
  let j : (ι → 𝒪[K]) →+ (ι → K) := (algebraMap 𝒪[K] K).toAddMonoidHom.compLeft ι
  have hj_apply (a : ι → 𝒪[K]) : j a = algebraMap 𝒪[K] K ∘ a := rfl
  have hj : MeasurableEmbedding j := by
    refine (Continuous.isClosedEmbedding ?_ fun a b hab ↦ ?_).measurableEmbedding
    · refine continuous_pi fun i ↦ ?_
      simp only [hj_apply, Function.comp_apply, Algebra.algebraMap_ofSubsemiring_apply]
      fun_prop
    · funext i
      simpa [hj_apply] using congrFun hab i
  have hrange : range j = integerBox K ι := by
    ext x
    simp only [mem_range, mem_integerBox]
    refine ⟨?_, fun h ↦ ⟨fun i ↦ ⟨x i, h i⟩, ?_⟩⟩
    · rintro ⟨a, rfl⟩ i
      simp [hj_apply, Algebra.algebraMap_ofSubsemiring_apply]
    · funext i
      simp [hj_apply, Algebra.algebraMap_ofSubsemiring_apply]
  -- The image of `A` is a subgroup of `ι → 𝒪[K]` of index `q ^ k`.
  let H := (LinearMap.range A.mulVecLin).toAddSubgroup
  have hindex : H.index = Nat.card 𝓀[K] ^ k := by
    rw [AddSubgroup.index_eq_card]
    -- The quotient by a submodule is by definition the quotient by its additive subgroup.
    exact Matrix.card_quotient_range_mulVecLin_eq_pow hϖ hk
  have _ : H.FiniteIndex := ⟨by rw [hindex]; exact pow_ne_zero _ Nat.card_pos.ne'⟩
  have hH : MeasurableSet (H : Set (ι → 𝒪[K])) :=
    (isCompact_range (by fun_prop : Continuous A.mulVecLin)).isClosed.measurableSet
  have himage : j '' H = (A.map (algebraMap 𝒪[K] K)).mulVec '' range j := by
    simp only [H, Submodule.coe_toAddSubgroup, LinearMap.coe_range, ← range_comp]
    congr 1
    funext a i
    simp [hj_apply, RingHom.map_mulVec]
  have _ := IsAddLeftInvariant.comap μ hj
  have h := MeasureTheory.AddSubgroup.index_mul_measure H hH (μ.comap j)
  rw [hj.comap_apply, hj.comap_apply, image_univ, hindex, himage, hrange] at h
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by simp [Nat.card_pos.ne'])
  rw [← h, Nat.cast_pow, ← mul_assoc, one_div, ENNReal.inv_mul_cancel hq (by simp), one_mul]

omit [DecidableEq ι] in
/-- **The volume of a box of ideals**: for a left-invariant measure on `ι → K` normalized on the
integer box, the box whose `i`-th factor is `𝓂[K] ^ e i` has volume `q ^ (-∑ i, e i)`, where
`q = Nat.card 𝓀[K]`. -/
theorem measure_univ_pi_image_maximalIdeal_pow (μ : Measure (ι → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K ι) = 1) (e : ι → ℕ) :
    μ (univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i)) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ∑ i, e i := by
  classical
  -- The box is the image of the integer box under the diagonal matrix with entries `ϖ ^ e i`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h := measure_image_mulVec_integerBox μ hϖ (k := ∑ i, e i)
    (A := Matrix.diagonal fun i ↦ ϖ ^ e i) (by rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum])
  rw [hμ, mul_one, Matrix.diagonal_map (map_zero _)] at h
  refine Eq.trans (congrArg μ ?_) h
  -- A diagonal matrix acts coordinatewise, so its image of a box is again a box.
  have hdiag : (Matrix.diagonal fun i ↦ algebraMap 𝒪[K] K (ϖ ^ e i)).mulVec =
      Pi.map fun i y ↦ algebraMap 𝒪[K] K (ϖ ^ e i) * y :=
    funext fun _ ↦ funext fun _ ↦ Matrix.mulVec_diagonal ..
  rw [hdiag, integerBox_def, piMap_image_univ_pi]
  refine pi_congr rfl fun i _ ↦ ?_
  rw [image_maximalIdeal_pow_eq_smul hϖ, ← image_smul, Algebra.algebraMap_ofSubsemiring_apply,
    SubmonoidClass.coe_pow]
  simp only [smul_eq_mul]

/-- **The scaling law on balls.** If the determinant of a square matrix `A` over `𝒪[K]` is
associated to `ϖ ^ k` for a uniformizer `ϖ`, then for every left-invariant measure on `ι → K`,
the image under `A` of the ball `x +ᵥ c • ∏ i, 𝒪[K]` (with `c ≠ 0`) has `q ^ (-k)` times the
measure of the ball, where `q = Nat.card 𝓀[K]`. -/
theorem measure_image_mulVec_vadd_smul_integerBox (μ : Measure (ι → K))
    [μ.IsAddLeftInvariant] {A : Matrix ι ι 𝒪[K]} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    (hk : Associated A.det (ϖ ^ k)) (x : ι → K) {c : K} (hc : c ≠ 0) :
    μ ((A.map (algebraMap 𝒪[K] K)).mulVec '' (x +ᵥ c • integerBox K ι)) =
      (1 : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k * μ (x +ᵥ c • integerBox K ι) := by
  -- The measure `T ↦ μ (c • T)` is again left invariant, so the box form applies to it.
  let e : (ι → K) ≃ᵐ (ι → K) := MeasurableEquiv.smul₀ c⁻¹ (inv_ne_zero hc)
  have he (T : Set (ι → K)) : μ.map e T = μ (c • T) := by
    rw [e.map_apply, MeasurableEquiv.coe_smul₀, preimage_smul_inv₀ hc]
  -- `e` is scalar multiplication by `c⁻¹`, an additive endomorphism.
  have _ : (μ.map e).IsAddLeftInvariant :=
    isAddLeftInvariant_map (DistribSMul.toAddMonoidHom (ι → K) c⁻¹).toAddHom e.measurable
      e.surjective
  have h := measure_image_mulVec_integerBox (μ.map e) hϖ hk
  rw [he, he] at h
  rw [← Matrix.coe_mulVecLin, image_vadd_distrib, image_smul_set, measure_vadd, measure_vadd,
    Matrix.coe_mulVecLin, h]

/-- **The scaling law for Haar measure.** If the determinant of a square matrix `A` over `𝒪[K]`
is associated to `ϖ ^ k` for a uniformizer `ϖ`, then for every regular additive Haar measure `μ`
on `ι → K` and every set `s`, `μ (A '' s) = q ^ (-k) * μ s`, where `q = Nat.card 𝓀[K]`. This is
the nonarchimedean analogue of `MeasureTheory.Measure.addHaar_image_linearMap`. -/
theorem addHaar_image_mulVec (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] [μ.Regular]
    {A : Matrix ι ι 𝒪[K]} {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    (hk : Associated A.det (ϖ ^ k)) (s : Set (ι → K)) :
    μ ((A.map (algebraMap 𝒪[K] K)).mulVec '' s) = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k * μ s := by
  have hdet : IsUnit (A.map (algebraMap 𝒪[K] K)).det := by
    rw [isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ne_eq,
      FaithfulSMul.algebraMap_eq_zero_iff]
    exact hk.ne_zero_iff.mpr (pow_ne_zero k hϖ.ne_zero)
  set A' := A.map (algebraMap 𝒪[K] K)
  -- The measure `T ↦ μ (A' '' T)` is the image of `μ` under the inverse of `A'`.
  let f : (ι → K) ≃ₜ (ι → K) :=
    { toFun := A'⁻¹.mulVec
      invFun := A'.mulVec
      left_inv v := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      right_inv v := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      continuous_toFun := continuous_const.matrix_mulVec continuous_id
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  have hf (T : Set (ι → K)) : μ.map f T = μ (A'.mulVec '' T) := by
    rw [← f.toMeasurableEquiv_coe, MeasurableEquiv.map_apply, f.toMeasurableEquiv_coe,
      ← f.image_symm]
    -- `f.symm` is `A'.mulVec` by construction.
    rfl
  -- `f` is the linear map `A'⁻¹.mulVecLin`.
  have _ : (μ.map f).IsAddLeftInvariant :=
    isAddLeftInvariant_map A'⁻¹.mulVecLin.toAddMonoidHom.toAddHom f.continuous.measurable
      f.surjective
  have _ : (μ.map f).Regular := Regular.map f
  have hsmul := isAddLeftInvariant_eq_smul_of_regular (μ.map f) μ
  -- The constant is read off the integer box, which is compact and open.
  have hB0 : μ (integerBox K ι) ≠ 0 :=
    isOpen_integerBox.measure_ne_zero μ ⟨0, mem_integerBox.2 fun _ ↦ zero_mem _⟩
  have hBtop : μ (integerBox K ι) ≠ ∞ := isCompact_integerBox.measure_lt_top.ne
  have hc : (addHaarScalarFactor (μ.map f) μ : ℝ≥0∞) = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
    have h := measure_image_mulVec_integerBox μ hϖ hk
    rw [← hf, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    exact (ENNReal.mul_left_inj hB0 hBtop).1 h
  rw [← hf, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc]

end MeasureTheory.Measure
