/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tate coordinates for the Borel regulator target

The Borel target consists of functions on complex embeddings, valued in a real Tate line and
fixed by simultaneous conjugation of embeddings and values. We index by the Tate exponent `k`
(weight `k + 1`). Dividing by the Tate generator gives one real coordinate at each complex place
and, for even `k`, one at each real place. This is the embedding model of Burgos Gil,
*The Regulators of Beilinson and Borel* (2002), Proposition 9.22 and Corollary 9.23.
-/

public section

open NumberField NumberField.InfinitePlace Submodule
open scoped ComplexConjugate

namespace TauCeti.BorelRegulator

/-- The generator of the Tate line with exponent `k`. -/
noncomputable def tateGenerator (k : ℕ) : ℂ := (2 * (Real.pi : ℂ) * Complex.I) ^ k

/-- The Tate generator uses the standard positive `2π` scale and the chosen complex unit. -/
theorem tateGenerator_def (k : ℕ) : tateGenerator k = (2 * (Real.pi : ℂ) * Complex.I) ^ k :=
  (rfl)

/-- The Tate line generator is nonzero in every exponent. -/
@[simp] theorem tateGenerator_ne_zero (k : ℕ) : tateGenerator k ≠ 0 := by
  simp [tateGenerator, Real.pi_ne_zero]

/-- Conjugation acts on the Tate generator by the sign of its exponent. -/
theorem conj_tateGenerator (k : ℕ) : conj (tateGenerator k) = (-1 : ℝ) ^ k • tateGenerator k := by
  simp only [tateGenerator, map_pow, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  rw [neg_eq_neg_one_mul (2 * (Real.pi : ℂ) * Complex.I), mul_pow]

variable {F : Type*} [Field F] {k : ℕ}

/-- The real regulator target of weight `k + 1`, in its native embedding space. -/
noncomputable def embeddingSpace (F : Type*) [Field F] (k : ℕ) : Submodule ℝ ((F →+* ℂ) → ℂ) where
  carrier := {v | (∀ σ, v σ ∈ ℝ ∙ tateGenerator k) ∧
    ∀ σ, v (ComplexEmbedding.conjugate σ) = conj (v σ)}
  zero_mem' := by simp
  add_mem' := by
    rintro v w ⟨hv, hvc⟩ ⟨hw, hwc⟩
    exact ⟨fun σ ↦ add_mem (hv σ) (hw σ), fun σ ↦ by simp [Pi.add_apply, hvc, hwc]⟩
  smul_mem' := by
    rintro r v ⟨hv, hvc⟩
    exact ⟨fun σ ↦ smul_mem _ r (hv σ), fun σ ↦ by simp [Pi.smul_apply, hvc, Complex.real_smul]⟩

/-- Membership is the Tate line condition and simultaneous conjugation invariance. -/
theorem mem_embeddingSpace {v : (F →+* ℂ) → ℂ} : v ∈ embeddingSpace F k ↔
    (∀ σ, v σ ∈ ℝ ∙ tateGenerator k) ∧
    ∀ σ, v (ComplexEmbedding.conjugate σ) = conj (v σ) := (Iff.rfl)

/-- Vectors in the target are determined by their values at the complex embeddings. -/
@[ext] theorem embeddingSpace_ext {v w : embeddingSpace F k}
    (h : ∀ σ, v.val σ = w.val σ) : v = w := Subtype.ext (funext h)

/-- Conjugating an embedding conjugates its value in the regulator target. -/
@[simp] theorem embeddingSpace_apply_conjugate (v : embeddingSpace F k) (σ : F →+* ℂ) :
    v.val (ComplexEmbedding.conjugate σ) = conj (v.val σ) :=
  (mem_embeddingSpace.mp v.property).2 σ

/-- Multiplying the real divided coordinate by the Tate generator recovers the original value. -/
theorem smul_tateGenerator_eq (v : embeddingSpace F k) (σ : F →+* ℂ) :
    (v.val σ / tateGenerator k).re • tateGenerator k = v.val σ := by
  obtain ⟨r, hr⟩ := mem_span_singleton.mp ((mem_embeddingSpace.mp v.property).1 σ)
  simp only [← hr, Complex.real_smul, mul_div_cancel_right₀ _ (tateGenerator_ne_zero k),
    Complex.ofReal_re]

/-- The surviving coordinate places: all complex places and the real places in odd weight. -/
abbrev CoordinatePlace (F : Type*) [Field F] (k : ℕ) :=
  {w : InfinitePlace F // Even k ∨ w.IsComplex}

/-- The surviving places of a number field form a finite coordinate index. -/
noncomputable instance instFintypeCoordinatePlace [NumberField F] : Fintype (CoordinatePlace F k) :=
  Fintype.ofFinite _

/-- The real embeddings contribute zero in even weight. -/
theorem embeddingSpace_apply_eq_zero_of_isReal (v : embeddingSpace F k) {σ : F →+* ℂ}
    (hσ : ComplexEmbedding.IsReal σ) (hk : Odd k) : v.val σ = 0 := by
  have hv := embeddingSpace_apply_conjugate v σ
  have hσ' : ComplexEmbedding.conjugate σ = σ := hσ
  rw [hσ'] at hv
  have h := calc
    conj (v.val σ) = conj ((v.val σ / tateGenerator k).re • tateGenerator k) :=
      congrArg (conj : ℂ → ℂ) (smul_tateGenerator_eq v σ).symm
    _ = -v.val σ := by
      rw [← Complex.conjCLE_apply, map_smul, Complex.conjCLE_apply, conj_tateGenerator,
        hk.neg_one_pow, neg_one_smul, smul_neg, smul_tateGenerator_eq]
  linear_combination (hv + h) / 2

private theorem apply_eq_zero_of_not_coordinate (v : embeddingSpace F k) (σ : F →+* ℂ)
    (h : ¬ (Even k ∨ (InfinitePlace.mk σ).IsComplex)) : v.val σ = 0 := by
  push Not at h
  exact embeddingSpace_apply_eq_zero_of_isReal v
    (InfinitePlace.isReal_mk_iff.mp (InfinitePlace.not_isComplex_iff_isReal.mp h.2)) h.1

variable (rep : CoordinatePlace F k → F →+* ℂ)
  (hrep : ∀ w, InfinitePlace.mk (rep w) = w.val)

include hrep in
/-- Selected embedding values determine a vector, including when there are no coordinates. -/
theorem embeddingSpace_ext_of_representatives {v w : embeddingSpace F k}
    (h : ∀ i, v.val (rep i) = w.val (rep i)) : v = w := by
  apply embeddingSpace_ext
  intro σ
  by_cases hσ : Even k ∨ (InfinitePlace.mk σ).IsComplex
  · let i : CoordinatePlace F k := ⟨InfinitePlace.mk σ, hσ⟩
    rcases InfinitePlace.mk_eq_iff.mp (hrep i : InfinitePlace.mk (rep i) = InfinitePlace.mk σ)
      with he | he
    · simpa only [he] using h i
    · rw [← he, embeddingSpace_apply_conjugate, embeddingSpace_apply_conjugate, h i]
  · rw [apply_eq_zero_of_not_coordinate v σ hσ, apply_eq_zero_of_not_coordinate w σ hσ]

private noncomputable def extendCoordinates (x : CoordinatePlace F k → ℝ) (σ : F →+* ℂ) : ℂ :=
  open Classical in
  if h : Even k ∨ (InfinitePlace.mk σ).IsComplex then
    if σ = rep ⟨InfinitePlace.mk σ, h⟩ then x ⟨InfinitePlace.mk σ, h⟩ • tateGenerator k
    else conj (x ⟨InfinitePlace.mk σ, h⟩ • tateGenerator k)
  else 0

include hrep in
private theorem extendCoordinates_apply_rep (x : CoordinatePlace F k → ℝ)
    (i : CoordinatePlace F k) : extendCoordinates rep x (rep i) = x i • tateGenerator k := by
  rcases i with ⟨w, hw⟩
  simp [extendCoordinates, hrep ⟨w, hw⟩, hw]

include hrep in
private theorem extendCoordinates_mem (x : CoordinatePlace F k → ℝ) :
    extendCoordinates rep x ∈ embeddingSpace F k := by
  classical
  rw [mem_embeddingSpace]
  constructor
  · intro σ
    unfold extendCoordinates
    split
    · split
      · exact smul_mem _ _ (mem_span_singleton_self _)
      · rw [← Complex.conjCLE_apply, map_smul, Complex.conjCLE_apply, conj_tateGenerator]
        exact smul_mem _ _ (smul_mem _ _ (mem_span_singleton_self _))
    · exact zero_mem _
  · intro σ
    by_cases hσ : Even k ∨ (InfinitePlace.mk σ).IsComplex
    · let i : CoordinatePlace F k := ⟨InfinitePlace.mk σ, hσ⟩
      have horbit : rep i = σ ∨ ComplexEmbedding.conjugate (rep i) = σ :=
        InfinitePlace.mk_eq_iff.mp (hrep i)
      simp only [extendCoordinates, InfinitePlace.mk_conjugate_eq, dite_eq_left hσ]
      by_cases hc : ComplexEmbedding.conjugate σ = σ
      · have hk : Even k := hσ.resolve_right fun hn ↦ InfinitePlace.isComplex_mk_iff.mp hn hc
        have he : rep i = σ := by
          rcases horbit with h | h
          · exact h
          · simpa [hc] using congrArg ComplexEmbedding.conjugate h
        rw [ite_eq_left (hc.trans he.symm), ite_eq_left he.symm]
        simp [Complex.real_smul, conj_tateGenerator, hk.neg_one_pow]
      · rcases horbit with he | he
        · have hn : ComplexEmbedding.conjugate σ ≠ rep i := fun h ↦ hc (h.trans he)
          rw [ite_eq_left he.symm, ite_eq_right hn]
        · have hr : ComplexEmbedding.conjugate σ = rep i := by rw [← he]; simp
          have hn : σ ≠ rep i := fun h ↦ hc (hr.trans h.symm)
          rw [ite_eq_right hn, ite_eq_left hr, starRingEnd_self_apply]
    · simp [extendCoordinates, hσ]

/-- Evaluate at the selected embedding of each surviving place and divide by the Tate generator. -/
noncomputable def coordinates : embeddingSpace F k ≃ₗ[ℝ] (CoordinatePlace F k → ℝ) where
  toFun v i := (v.val (rep i) / tateGenerator k).re
  invFun x := ⟨extendCoordinates rep x, extendCoordinates_mem rep hrep x⟩
  left_inv v := by
    apply embeddingSpace_ext_of_representatives rep hrep
    intro i
    exact (extendCoordinates_apply_rep rep hrep
      (fun j ↦ (v.val (rep j) / tateGenerator k).re) i).trans (smul_tateGenerator_eq v (rep i))
  right_inv x := by
    funext i
    simp only [extendCoordinates_apply_rep rep hrep, Complex.real_smul,
      mul_div_cancel_right₀ _ (tateGenerator_ne_zero k), Complex.ofReal_re]
  map_add' v w := by
    ext i
    simp [add_div]
  map_smul' r v := by
    ext i
    simp [Complex.real_smul, mul_div_assoc, Complex.mul_re]

/-- The forward map evaluates and divides by the Tate generator at each chosen embedding. -/
@[simp] theorem coordinates_apply (v : embeddingSpace F k) (i : CoordinatePlace F k) :
    coordinates rep hrep v i = (v.val (rep i) / tateGenerator k).re := (rfl)

/-- The inverse multiplies each coordinate by the Tate generator at its representative. -/
@[simp] theorem coordinates_symm_apply_rep (x : CoordinatePlace F k → ℝ) (i : CoordinatePlace F k) :
    ((coordinates rep hrep).symm x).val (rep i) = x i • tateGenerator k :=
  extendCoordinates_apply_rep rep hrep x i

/-- Replacing a selected embedding by its conjugate multiplies the divided coordinate by
`(-1)^k`. -/
theorem dividedCoordinate_apply_conjugate (v : embeddingSpace F k) (σ : F →+* ℂ) :
    (v.val (ComplexEmbedding.conjugate σ) / tateGenerator k).re =
      (-1 : ℝ) ^ k * (v.val σ / tateGenerator k).re := by
  conv_lhs =>
    rw [embeddingSpace_apply_conjugate, ← smul_tateGenerator_eq v σ, ← Complex.conjCLE_apply,
      map_smul, Complex.conjCLE_apply, conj_tateGenerator, smul_smul, Complex.real_smul,
      mul_div_cancel_right₀ _ (tateGenerator_ne_zero k), Complex.ofReal_re]
  exact mul_comm _ _

section NumberField

variable [NumberField F]

/-- The Tate-divided coordinates and their inverse are continuous in the native topology. -/
noncomputable def continuousCoordinates : embeddingSpace F k ≃L[ℝ] (CoordinatePlace F k → ℝ) :=
  (coordinates rep hrep).toContinuousLinearEquiv

/-- Forgetting continuity recovers the algebraic coordinate equivalence. -/
@[simp] theorem continuousCoordinates_toLinearEquiv :
    (continuousCoordinates rep hrep).toLinearEquiv = coordinates rep hrep := (rfl)

/-- Evaluation of the continuous coordinate equivalence at a surviving place. -/
@[simp] theorem continuousCoordinates_apply (v : embeddingSpace F k) (i : CoordinatePlace F k) :
    continuousCoordinates rep hrep v i = (v.val (rep i) / tateGenerator k).re :=
  coordinates_apply rep hrep v i

/-- Evaluation of the continuous inverse at a selected embedding. -/
@[simp] theorem continuousCoordinates_symm_apply_rep (x : CoordinatePlace F k → ℝ)
    (i : CoordinatePlace F k) :
    ((continuousCoordinates rep hrep).symm x).val (rep i) = x i • tateGenerator k :=
  coordinates_symm_apply_rep rep hrep x i

/-- The inherited sup norm is the coordinate sup norm times the size of the Tate generator. -/
theorem norm_eq_norm_coordinates_mul (v : embeddingSpace F k) :
    ‖v‖ = ‖continuousCoordinates rep hrep v‖ * ‖tateGenerator k‖ := by
  let x := continuousCoordinates rep hrep v
  have hn (i : CoordinatePlace F k) : ‖v.val (rep i)‖ = ‖x i‖ * ‖tateGenerator k‖ := by
    rw [← smul_tateGenerator_eq v (rep i), norm_smul]
    simp only [x, continuousCoordinates_apply]
  apply le_antisymm
  · -- The submodule inherits the ambient product norm through the subtype inclusion.
    rw [← Submodule.norm_coe]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro σ
    by_cases hσ : Even k ∨ (InfinitePlace.mk σ).IsComplex
    · let i : CoordinatePlace F k := ⟨InfinitePlace.mk σ, hσ⟩
      have hi := mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg (tateGenerator k))
      rcases InfinitePlace.mk_eq_iff.mp (hrep i : InfinitePlace.mk (rep i) = InfinitePlace.mk σ)
        with he | he
      · rwa [← he, hn]
      · rwa [← he, embeddingSpace_apply_conjugate, Complex.norm_conj, hn]
    · simp [apply_eq_zero_of_not_coordinate v σ hσ]
  · rw [← le_div_iff₀ (norm_pos_iff.mpr (tateGenerator_ne_zero k))]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [le_div_iff₀ (norm_pos_iff.mpr (tateGenerator_ne_zero k)), ← hn]
    exact norm_le_pi_norm v.val (rep i)

/-- The dimension is `r₁ + r₂` in odd weight and `r₂` in even weight. -/
theorem finrank_embeddingSpace : Module.finrank ℝ (embeddingSpace F k) =
    (if Even k then nrRealPlaces F + nrComplexPlaces F else nrComplexPlaces F) := by
  classical
  rw [LinearEquiv.finrank_eq (coordinates (fun i ↦ i.val.embedding) (fun i ↦ i.val.mk_embedding)),
    Module.finrank_fintype_fun_eq_card]
  by_cases hk : Even k
  · rw [ite_eq_left hk, ← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_congr ((Equiv.subtypeEquivRight (q := fun _ ↦ True) (by simp [hk])).trans
      (Equiv.subtypeUnivEquiv (fun _ ↦ trivial)))
  · rw [ite_eq_right hk]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [hk]))

end NumberField

/-- The integral regulator target consists of vectors with all values in the integral Tate line. -/
noncomputable def embeddingLattice (F : Type*) [Field F] (k : ℕ) :
    Submodule ℤ (embeddingSpace F k) :=
  (Submodule.pi Set.univ fun _ ↦ ℤ ∙ tateGenerator k).comap
    ((embeddingSpace F k).subtype.restrictScalars ℤ)

/-- Membership in the integral regulator target is tested pointwise on the Tate line. -/
@[simp] theorem mem_embeddingLattice {v : embeddingSpace F k} : v ∈ embeddingLattice F k ↔
    ∀ σ, v.val σ ∈ ℤ ∙ tateGenerator k := by
  simp [embeddingLattice, Submodule.mem_pi]

/-- Integrality can be tested on the divided coordinates of any selected representatives. -/
theorem mem_embeddingLattice_iff_coordinates {v : embeddingSpace F k} :
    v ∈ embeddingLattice F k ↔ ∀ i, ∃ m : ℤ, (m : ℝ) = coordinates rep hrep v i := by
  rw [mem_embeddingLattice]
  constructor
  · intro h i
    obtain ⟨m, hm⟩ := mem_span_singleton.mp (h (rep i))
    exact ⟨m, by simp [← hm, zsmul_eq_mul, tateGenerator_ne_zero]⟩
  · intro h σ
    by_cases hσ : Even k ∨ (InfinitePlace.mk σ).IsComplex
    · let i : CoordinatePlace F k := ⟨InfinitePlace.mk σ, hσ⟩
      obtain ⟨m, hm⟩ := h i
      have hv : m • tateGenerator k = v.val (rep i) := by
        rw [← Int.cast_smul_eq_zsmul ℝ, hm, coordinates_apply, smul_tateGenerator_eq]
      rcases InfinitePlace.mk_eq_iff.mp (hrep i : InfinitePlace.mk (rep i) = InfinitePlace.mk σ)
        with he | he
      · rw [← he, ← hv]
        exact smul_mem _ _ (mem_span_singleton_self _)
      · have hg : conj (tateGenerator k) ∈ ℤ ∙ tateGenerator k := by
          apply mem_span_singleton.mpr
          exact ⟨(-1 : ℤ) ^ k, by
            simpa [Int.cast_smul_eq_zsmul] using (conj_tateGenerator k).symm⟩
        rw [← he, embeddingSpace_apply_conjugate, ← hv, map_zsmul]
        exact smul_mem _ _ hg
    · rw [apply_eq_zero_of_not_coordinate v σ hσ]
      exact zero_mem _

section NumberField

variable [NumberField F]

/-- In the chosen coordinates the regulator lattice is the standard integer lattice. -/
theorem embeddingLattice_eq_comap : embeddingLattice F k =
    ZLattice.comap ℝ (span ℤ (Set.range (Pi.basisFun ℝ (CoordinatePlace F k))))
      (continuousCoordinates rep hrep).toLinearMap := by
  ext v
  rw [mem_embeddingLattice_iff_coordinates rep hrep]
  simpa [ZLattice.comap, mem_comap, continuousCoordinates_toLinearEquiv, Pi.basisFun_repr,
    eq_comm (a := (_ : ℝ))] using
    ((Pi.basisFun ℝ (CoordinatePlace F k)).mem_span_iff_repr_mem ℤ (coordinates rep hrep v)).symm

/-- The integral target has discrete subtype topology. -/
instance instDiscreteTopologyEmbeddingLattice : DiscreteTopology (embeddingLattice F k) := by
  rw [embeddingLattice_eq_comap (fun i ↦ i.val.embedding) (fun i ↦ i.val.mk_embedding)]
  infer_instance

/-- The integral target spans the real regulator target. -/
instance instIsZLatticeEmbeddingLattice : IsZLattice ℝ (embeddingLattice F k) where
  span_top := by
    rw [embeddingLattice_eq_comap (fun i ↦ i.val.embedding) (fun i ↦ i.val.mk_embedding)]
    exact IsZLattice.span_top (K := ℝ)

open MeasureTheory

/-- Coordinate Haar measure, the pullback of product Lebesgue measure. -/
noncomputable def coordinateMeasure : Measure (embeddingSpace F k) :=
  volume.map (continuousCoordinates rep hrep).symm

/-- The transported product measure is additive Haar measure on the target. -/
instance instIsAddHaarMeasureCoordinateMeasure : (coordinateMeasure rep hrep).IsAddHaarMeasure :=
  (continuousCoordinates rep hrep).symm.isAddHaarMeasure_map volume

/-- The coordinate equivalence sends the coordinate Haar measure to product Lebesgue measure. -/
theorem measurePreserving_continuousCoordinates :
    MeasurePreserving (continuousCoordinates rep hrep) (coordinateMeasure rep hrep) volume :=
  ⟨(continuousCoordinates rep hrep).continuous.measurable,
    (continuousCoordinates rep hrep).toHomeomorph.toMeasurableEquiv.map_map_symm⟩

/-- The integral Tate target has covolume one in the coordinate normalization. -/
@[simp] theorem covolume_embeddingLattice :
    ZLattice.covolume (embeddingLattice F k) (coordinateMeasure rep hrep) = 1 := by
  classical
  rw [embeddingLattice_eq_comap rep hrep,
    ZLattice.covolume_comap _ _ _ (measurePreserving_continuousCoordinates rep hrep),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain _ _),
    ZSpan.fundamentalDomain_pi_basisFun]
  simp [Measure.real, volume_pi, Measure.pi_pi, Real.volume_Ico]

/-- The coordinate Haar measure is independent of the choice of embedding representatives. -/
theorem coordinateMeasure_eq (rep' : CoordinatePlace F k → F →+* ℂ)
    (hrep' : ∀ w, InfinitePlace.mk (rep' w) = w.val) :
    coordinateMeasure rep hrep = coordinateMeasure rep' hrep' := by
  classical
  let e := continuousCoordinates rep hrep
  let e' := continuousCoordinates rep' hrep'
  have ht (i : CoordinatePlace F k) :
      MeasurePreserving (fun t : ℝ ↦ if rep i = rep' i then t else (-1 : ℝ) ^ k * t) := by
    by_cases hi : rep i = rep' i
    · simp only [ite_eq_left hi]
      exact MeasurePreserving.id _
    · rcases Nat.even_or_odd k with hk | hk
      · simp only [ite_eq_right hi, hk.neg_one_pow, one_mul]
        exact MeasurePreserving.id _
      · simpa only [ite_eq_right hi, hk.neg_one_pow, neg_one_mul] using
          (Measure.measurePreserving_neg (volume : Measure ℝ))
  have he : MeasurePreserving (e' ∘ e.symm) := by
    convert volume_preserving_pi ht using 1
    funext x i
    have hx := congrFun (e.apply_symm_apply x) i
    dsimp only [e] at hx
    rw [continuousCoordinates_apply] at hx
    simp only [Function.comp_apply, e', continuousCoordinates_apply]
    by_cases h : rep i = rep' i
    · rwa [ite_eq_left h, ← h]
    · have hc := (InfinitePlace.mk_eq_iff.mp ((hrep i).trans (hrep' i).symm)).resolve_left h
      rw [ite_eq_right h, ← hc, dividedCoordinate_apply_conjugate, hx]
  have hm : (coordinateMeasure rep hrep).map e' = volume := by
    rw [coordinateMeasure, Measure.map_map e'.continuous.measurable e.symm.continuous.measurable]
    exact he.map_eq
  exact e'.toHomeomorph.toMeasurableEquiv.map_measurableEquiv_injective
    (hm.trans (measurePreserving_continuousCoordinates rep' hrep').map_eq.symm)

end NumberField

end TauCeti.BorelRegulator
