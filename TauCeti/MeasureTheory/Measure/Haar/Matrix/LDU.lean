/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex
public import TauCeti.MeasureTheory.Integral.Prod
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Lebesgue integration in complex LDU coordinates

For measurable functions on complex `n × n` matrices, this formula converts the Lebesgue integral
into a weighted integral over the diagonal vector `c`, with weight
`∏ i, ‖c i‖ₑ ^ (4 * i.rev.val)`, of integrals over independent strict-upper-triangular coordinates
of the two unitriangular factors. Indicator functions can use it to compute or bound volumes of
matrix sets.

Splitting off the first row and column reduces the formula to two vector scalings and
translation of the trailing block. The diagonal ranges over the whole space; at each step
the zero pivot is discarded only almost everywhere.

## Provenance

The pivot argument follows `lintegral_bruhat_coords` in grh-lean's
`grh-compact/src/Lib/DiscreteSeries/Bessel/UnipotentCoords.lean` at revision
`72fead102f663d5c7a407964a13dc0cf9d977207` (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

open Matrix MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable section

private abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
private abbrev CVec (n : ℕ) := Fin n → ℂ
private abbrev UpperIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
private abbrev UpperEntries (n : ℕ) := UpperIndex n → ℂ

private abbrev upperMatrix {n : ℕ} : UpperEntries n → CMat n :=
  TauCeti.unitDiagonalMatrixOfEntries (fun p : Fin n × Fin n ↦ p.1 < p.2)

@[local fun_prop]
private theorem measurable_upperMatrix {n : ℕ} : Measurable (@upperMatrix n) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  by_cases h : i < j
  · simpa only [upperMatrix, TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem
      (fun p : Fin n × Fin n ↦ p.1 < p.2) _ h.ne h] using
      (measurable_pi_apply (⟨(i, j), h⟩ : UpperIndex n) :
        Measurable fun x : UpperEntries n ↦ x ⟨(i, j), h⟩)
  · by_cases e : i = j
    · subst j
      simp only [upperMatrix, TauCeti.unitDiagonalMatrixOfEntries_apply_self]
      exact measurable_const
    · simp only [upperMatrix, TauCeti.unitDiagonalMatrixOfEntries_apply_of_notMem
        (fun p : Fin n × Fin n ↦ p.1 < p.2) _ e h]
      exact measurable_const

-- The strict upper positions consist of the first row off the diagonal and the trailing positions.
private def headSplit (n : ℕ) : Fin n ⊕ UpperIndex n ≃ UpperIndex (n + 1) :=
  Equiv.ofBijective
    (Sum.elim (fun i ↦ ⟨(0, i.succ), Fin.succ_pos i⟩)
      (fun p ↦ ⟨(p.val.1.succ, p.val.2.succ), Fin.succ_lt_succ_iff.mpr p.prop⟩))
    (by
      constructor
      · intro x y h
        have h₁ := congrArg (fun p : UpperIndex (n + 1) ↦ p.val.1) h
        have h₂ := congrArg (fun p : UpperIndex (n + 1) ↦ p.val.2) h
        cases x <;> cases y
        · exact congrArg Sum.inl (Fin.succ_inj.mp h₂)
        · exact ((Fin.succ_pos _).ne' h₁.symm).elim
        · exact ((Fin.succ_pos _).ne' h₁).elim
        · exact congrArg Sum.inr (Subtype.ext (Prod.ext (Fin.succ_inj.mp h₁) (Fin.succ_inj.mp h₂)))
      · rintro ⟨⟨i, j⟩, h⟩
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact (lt_irrefl _ h).elim
          | succ j => exact ⟨Sum.inl j, rfl⟩
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (Fin.not_lt_zero _ h).elim
          | succ j => exact ⟨Sum.inr ⟨(i, j), Fin.succ_lt_succ_iff.mp h⟩, rfl⟩)

private def splitUpper (n : ℕ) : UpperEntries (n + 1) ≃ᵐ CVec n × UpperEntries n :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℂ) (headSplit n).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℂ))

private theorem measurePreserving_splitUpper (n : ℕ) :
    MeasurePreserving (splitUpper n) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi _).comp
    (volume_measurePreserving_piCongrLeft _ (headSplit n).symm)

private def pivotMatrix (n : ℕ) (p : ℂ × CVec n × CVec n × CMat n) : CMat (n + 1) :=
  Matrix.of (Fin.cons (Fin.cons p.1 p.2.1) fun i ↦ Fin.cons (p.2.2.1 i) (p.2.2.2 i))

private theorem measurePreserving_pivotMatrix (n : ℕ) :
    MeasurePreserving (pivotMatrix n) volume volume := by
  have hcons (α : Type) [MeasureSpace α] [SigmaFinite (volume : Measure α)] :
      MeasurePreserving (fun p : α × (Fin n → α) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → α))
        volume volume := by
    convert (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0).symm _ using 1
    funext p
    exact (Fin.insertNth_zero' p.1 p.2).symm
  have htail := (volume_preserving_pi fun _ : Fin n ↦ hcons ℂ).comp <|
    (volume_measurePreserving_arrowProdEquivProdArrow ℂ (CVec n) (Fin n)).symm _ |>.comp
      ((MeasurePreserving.id (volume : Measure (CVec n))).prod
        ((Matrix.volume_preserving_ofMeasurableEquiv (Fin n) (Fin n) ℂ).symm _))
  exact (Matrix.volume_preserving_ofMeasurableEquiv _ _ _).comp <|
    (hcons (CVec (n + 1))).comp <| ((hcons ℂ).prod htail).comp
      ((measurePreserving_prodAssoc volume volume volume).symm _)

private theorem lintegral_pivotMatrix {n : ℕ} {f : CMat (n + 1) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ A, f A = ∫⁻ a : ℂ, ∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ A : CMat n,
      f (pivotMatrix n (a, v, u, A)) := by
  rw [← (measurePreserving_pivotMatrix n).lintegral_comp hf]
  have hg : Measurable fun p ↦ f (pivotMatrix n p) :=
    hf.comp (measurePreserving_pivotMatrix n).measurable
  rw [volume_eq_prod, lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun a ↦ ?_
  have ha : Measurable fun p : CVec n × CVec n × CMat n ↦ f (pivotMatrix n (a, p)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  rw [volume_eq_prod, lintegral_prod _ ha.aemeasurable]
  refine lintegral_congr fun v ↦ ?_
  have hv : Measurable fun p : CVec n × CMat n ↦ f (pivotMatrix n (a, v, p)) :=
    ha.comp (measurable_const.prodMk measurable_id)
  rw [volume_eq_prod, lintegral_prod _ hv.aemeasurable]

-- The pivot contributes a scaling on each off-diagonal block and a rank-one translation.
private def pivotLDU {n : ℕ} (a : ℂ) (v u : CVec n) (A : CMat n) : CMat (n + 1) :=
  pivotMatrix n (a, a • v, a • (fun i ↦ star (u i)),
    A + Matrix.of fun i j ↦ star (u i) * a * v j)

@[local fun_prop]
private theorem measurable_pivotLDU {n : ℕ} :
    Measurable fun p : ℂ × CVec n × CVec n × CMat n ↦ pivotLDU p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  apply (measurePreserving_pivotMatrix n).measurable.comp
  apply Measurable.prodMk measurable_fst
  apply Measurable.prodMk
  -- Expose scalar operations before `fun_prop` so it sees the entrywise formulas.
  · apply measurable_pi_iff.mpr
    intro i
    change Measurable fun p : ℂ × CVec n × CVec n × CMat n ↦ p.1 * p.2.1 i
    fun_prop
  · apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun i ↦ by
        change Measurable fun p : ℂ × CVec n × CVec n × CMat n ↦ p.1 * star (p.2.2.1 i)
        fun_prop
    · apply Matrix.measurable_iff.mpr
      intro i j
      change Measurable fun p : ℂ × CVec n × CVec n × CMat n ↦
        p.2.2.2 i j + star (p.2.2.1 i) * p.1 * p.2.1 j
      fun_prop

private theorem lintegral_pivotLDU {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    {f : CMat (n + 1) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ A : CMat n, f (pivotMatrix n (a, v, u, A))) =
      ‖a‖ₑ ^ (4 * n) * ∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ A : CMat n,
        f (pivotLDU a v u A) := by
  have hc : MeasurePreserving (fun u : CVec n ↦ fun i ↦ star (u i)) volume volume :=
    volume_preserving_pi fun _ ↦ Complex.conjLIE.measurePreserving
  have hcomp (v : CVec n) : Measurable fun p : CVec n × CMat n ↦
      f (pivotMatrix n (a, a • v, a • p.1, p.2)) := by
    apply hf.comp ((measurePreserving_pivotMatrix n).measurable.comp _)
    -- Scalar multiplication of vectors is measurable coordinate by coordinate.
    exact measurable_const.prodMk (measurable_const.prodMk
      ((measurable_pi_iff.mpr fun i ↦ by
        change Measurable fun p : CVec n × CMat n ↦ a * p.1 i
        fun_prop).prodMk measurable_snd))
  have hscale (g : CVec n → ℝ≥0∞) :
      ∫⁻ u, g u = ‖a‖ₑ ^ (2 * n) * ∫⁻ u : CVec n, g (a • u) := by
    simpa only [Fintype.card_fin] using
      (lintegral_eq_enorm_pow_mul_lintegral_comp_smul (κ := Fin n) ha g)
  have hcol (v : CVec n) :
      (∫⁻ u : CVec n, ∫⁻ A : CMat n, f (pivotMatrix n (a, a • v, u, A))) =
        ‖a‖ₑ ^ (2 * n) * ∫⁻ u : CVec n, ∫⁻ A : CMat n, f (pivotLDU a v u A) := by
    rw [hscale (fun u ↦ ∫⁻ A : CMat n, f (pivotMatrix n (a, a • v, u, A))),
      ← hc.lintegral_comp (hcomp v).lintegral_prod_right']
    congr 1
    exact lintegral_congr fun u ↦ (lintegral_add_right_eq_self
      (fun A : CMat n ↦ f (pivotMatrix n (a, a • v, a • (fun i ↦ star (u i)), A))) _).symm
  rw [hscale (fun v ↦ ∫⁻ u : CVec n, ∫⁻ A : CMat n,
    f (pivotMatrix n (a, v, u, A))), lintegral_congr hcol, lintegral_const_mul' _ _ (by simp),
    ← mul_assoc, ← pow_add, ← add_mul]

private def splitSides (n : ℕ) :
    UpperEntries (n + 1) × UpperEntries (n + 1) ≃ᵐ CVec n × CVec n ×
      (UpperEntries n × UpperEntries n) :=
  ((splitUpper n).prodCongr (splitUpper n)).trans <|
    MeasurableEquiv.prodAssoc.trans <|
    (MeasurableEquiv.refl _).prodCongr
      (MeasurableEquiv.prodAssoc.symm.trans <|
        (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          MeasurableEquiv.prodAssoc) |>.trans <|
    MeasurableEquiv.prodAssoc.symm.trans <|
    (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc

private theorem measurePreserving_splitSides (n : ℕ) :
    MeasurePreserving (splitSides n) volume volume := by
  have hsplit := (measurePreserving_splitUpper n).prod (measurePreserving_splitUpper n)
  have h₁ := (measurePreserving_prodAssoc volume volume volume).comp hsplit
  have h₂ := ((MeasurePreserving.id volume).prod <|
    (measurePreserving_prodAssoc volume volume volume).comp <|
      (measurePreserving_swap.prod (MeasurePreserving.id volume)).comp <|
        (measurePreserving_prodAssoc volume volume volume).symm _).comp h₁
  have h₃ := ((measurePreserving_prodAssoc volume volume volume).symm _).comp h₂
  exact (measurePreserving_prodAssoc volume volume volume).comp <|
    (measurePreserving_swap.prod (MeasurePreserving.id volume)).comp h₃

private theorem splitSides_symm_apply {n : ℕ} (v u : CVec n) (q : UpperEntries n × UpperEntries n) :
    (splitSides n).symm (v, u, q) = ((splitUpper n).symm (u, q.1), (splitUpper n).symm (v, q.2)) :=
  rfl

private theorem lintegral_splitSides {n : ℕ}
    {g : UpperEntries (n + 1) × UpperEntries (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ q, g q = ∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ q : UpperEntries n × UpperEntries n,
      g ((splitSides n).symm (v, u, q)) := by
  have h := (measurePreserving_splitSides n).symm (splitSides n)
  rw [← h.lintegral_comp_emb (splitSides n).symm.measurableEmbedding]
  have h' : Measurable fun p ↦ g ((splitSides n).symm p) := hg.comp (splitSides n).symm.measurable
  rw [volume_eq_prod, lintegral_prod _ h'.aemeasurable]
  refine lintegral_congr fun v ↦ ?_
  have hv : Measurable fun p : CVec n × (UpperEntries n × UpperEntries n) ↦
      g ((splitSides n).symm (v, p)) := h'.comp (measurable_const.prodMk measurable_id)
  rw [volume_eq_prod, lintegral_prod _ hv.aemeasurable]

private def ldu {n : ℕ} (c : CVec n) (q : UpperEntries n × UpperEntries n) : CMat n :=
  (upperMatrix q.1)ᴴ * diagonal c * upperMatrix q.2

@[local fun_prop]
private theorem measurable_ldu {n : ℕ} :
    Measurable fun p : CVec n × (UpperEntries n × UpperEntries n) ↦ ldu p.1 p.2 := by
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [ldu, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fun_prop

private theorem upperMatrix_split {n : ℕ} (v : CVec n) (x : UpperEntries n) :
    upperMatrix ((splitUpper n).symm (v, x)) = pivotMatrix n (1, v, 0, upperMatrix x) := by
  ext i j
  simp only [pivotMatrix, upperMatrix]
  let P (p : Fin (n + 1) × Fin (n + 1)) := p.1 < p.2
  -- At strict upper entries, unfold the reindexing enough to cancel the index equivalence.
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp
    | succ j =>
      rw [TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem P _ (Fin.succ_pos j).ne
        (Fin.succ_pos j)]
      change (Equiv.sumPiEquivProdPi (fun _ ↦ ℂ)).symm (v, x)
        ((headSplit n).symm (headSplit n (.inl j))) = v j
      rw [Equiv.symm_apply_apply]
      rfl
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [TauCeti.unitDiagonalMatrixOfEntries_apply_of_notMem P _ (Fin.succ_pos i).ne'
        (Fin.not_lt_zero _)]
      rfl
    | succ j =>
      simp only [Matrix.of_apply, Fin.cons_succ]
      by_cases e : i = j
      · subst j
        simp
      · by_cases h : i < j
        · rw [TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem P _
            (fun h' ↦ e (Fin.succ_inj.mp h')) (Fin.succ_lt_succ_iff.mpr h),
            TauCeti.unitDiagonalMatrixOfEntries_apply_of_mem
              (fun p : Fin n × Fin n ↦ p.1 < p.2) _ e h]
          change (Equiv.sumPiEquivProdPi (fun _ ↦ ℂ)).symm (v, x)
            ((headSplit n).symm (headSplit n (.inr ⟨(i, j), h⟩))) = x ⟨(i, j), h⟩
          rw [Equiv.symm_apply_apply]
          rfl
        · rw [TauCeti.unitDiagonalMatrixOfEntries_apply_of_notMem P _
            (fun h' ↦ e (Fin.succ_inj.mp h')) (fun h' ↦ h (Fin.succ_lt_succ_iff.mp h')),
            TauCeti.unitDiagonalMatrixOfEntries_apply_of_notMem
              (fun p : Fin n × Fin n ↦ p.1 < p.2) _ e h]

private theorem ldu_split {n : ℕ} (a : ℂ) (c : CVec n) (v u : CVec n)
    (q : UpperEntries n × UpperEntries n) :
    ldu (Fin.cons a c) ((splitSides n).symm (v, u, q)) = pivotLDU a v u (ldu c q) := by
  ext i j
  simp only [splitSides_symm_apply, ldu, upperMatrix_split, pivotLDU, pivotMatrix]
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have h (i j : Fin n) : ((upperMatrix q.1)ᴴ * diagonal c * upperMatrix q.2) i j =
      ∑ k, (star (upperMatrix q.1 k i) * c k) * upperMatrix q.2 k j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [h, add_comm, mul_comm]

private def density {n : ℕ} (c : CVec n) : ℝ≥0∞ := ∏ i : Fin n, ‖c i‖ₑ ^ (4 * i.rev.val)

@[local fun_prop]
private theorem measurable_density {n : ℕ} : Measurable (@density n) := by
  unfold density
  fun_prop

private theorem density_cons {n : ℕ} (a : ℂ) (c : CVec n) :
    density (Fin.cons a c) = ‖a‖ₑ ^ (4 * n) * density c := by
  simp [density, Fin.prod_univ_succ, Fin.rev]

private theorem lintegral_pivot_induction {n : ℕ} (a : ℂ) {f : CMat (n + 1) → ℝ≥0∞}
    (hf : Measurable f) (ih : ∀ {g : CMat n → ℝ≥0∞}, Measurable g →
      (∫⁻ c : CVec n, density c * ∫⁻ q : UpperEntries n × UpperEntries n, g (ldu c q)) =
        ∫⁻ A, g A) :
    (∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ A : CMat n, f (pivotLDU a v u A)) =
      ∫⁻ c : CVec n, density c * ∫⁻ q : UpperEntries (n + 1) × UpperEntries (n + 1),
        f (ldu (Fin.cons a c) q) := by
  let k (c : CVec n) (p : CVec n × CVec n) :=
    ∫⁻ q : UpperEntries n × UpperEntries n, f (pivotLDU a p.1 p.2 (ldu c q))
  have hk : Measurable fun p : CVec n × (CVec n × CVec n) ↦ k p.1 p.2 := by
    have h : Measurable fun p : (CVec n × (CVec n × CVec n)) ×
        (UpperEntries n × UpperEntries n) ↦ f (pivotLDU a p.1.2.1 p.1.2.2 (ldu p.1.1 p.2)) := by
      fun_prop
    exact h.lintegral_prod_right'
  have hweight : Measurable fun p : CVec n × (CVec n × CVec n) ↦ density p.1 * k p.1 p.2 :=
    (measurable_density.comp measurable_fst).mul hk
  -- Keep the Fubini step separate so elaboration does not unfold the weighted pivot integrand.
  calc
    _ = ∫⁻ v : CVec n, ∫⁻ u : CVec n, ∫⁻ c : CVec n, density c * k c (v, u) := by
      refine lintegral_congr fun v ↦ lintegral_congr fun u ↦ ?_
      exact (ih (g := fun A ↦ f (pivotLDU a v u A)) (by fun_prop)).symm
    _ = ∫⁻ c : CVec n, ∫⁻ v : CVec n, ∫⁻ u : CVec n, density c * k c (v, u) :=
      TauCeti.lintegral_lintegral_lintegral_rotate
        (k := fun c p ↦ density c * k c p) hweight
    _ = _ := by
      refine lintegral_congr fun c ↦ ?_
      have ht : density c ≠ ∞ := ENNReal.prod_ne_top fun i _ ↦ by simp
      have h : Measurable fun q : UpperEntries (n + 1) × UpperEntries (n + 1) ↦
          f (ldu (Fin.cons a c) q) := by fun_prop
      rw [lintegral_splitSides h]
      simp only [ldu_split, ← lintegral_const_mul' _ _ ht, k]

private theorem lintegral_ldu_zero (f : CMat 0 → ℝ≥0∞) :
    (∫⁻ c : CVec 0, density c * ∫⁻ q : UpperEntries 0 × UpperEntries 0, f (ldu c q)) =
      ∫⁻ A, f A := by
  have : IsEmpty (UpperIndex 0) := ⟨fun p ↦ Fin.elim0 p.val.1⟩
  have hu : volume (Set.univ : Set (UpperEntries 0 × UpperEntries 0)) = 1 := by
    rw [volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod]
    simp [volume_pi]
  have hA : volume (Set.univ : Set (CMat 0)) = 1 := by
    rw [← (Matrix.volume_preserving_ofMeasurableEquiv (Fin 0) (Fin 0) ℂ).map_eq,
      Measure.map_apply (Matrix.ofMeasurableEquiv _ _ _).measurable MeasurableSet.univ]
    simp [volume_pi]
  have h (A : CMat 0) : f A = f 0 := congrArg f (Subsingleton.elim _ _)
  simp only [h, lintegral_const, hu, hA, mul_one]
  simp [volume_pi, density]

private theorem lintegral_ldu_succ {n : ℕ} {f : CMat (n + 1) → ℝ≥0∞} (hf : Measurable f)
    (ih : ∀ {g : CMat n → ℝ≥0∞}, Measurable g →
      (∫⁻ c : CVec n, density c * ∫⁻ q : UpperEntries n × UpperEntries n, g (ldu c q)) =
        ∫⁻ A, g A) :
    (∫⁻ c : CVec (n + 1), density c * ∫⁻ q : UpperEntries (n + 1) × UpperEntries (n + 1),
        f (ldu c q)) = ∫⁻ A, f A := by
  have hg : Measurable fun c : CVec (n + 1) ↦
      density c * ∫⁻ q : UpperEntries (n + 1) × UpperEntries (n + 1), f (ldu c q) :=
    measurable_density.mul (hf.comp measurable_ldu).lintegral_prod_right'
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm
  have hcons : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm _
  have hg' : Measurable fun p : ℂ × CVec n ↦ density (e p) *
      ∫⁻ q : UpperEntries (n + 1) × UpperEntries (n + 1), f (ldu (e p) q) :=
    hg.comp hcons.measurable
  rw [← hcons.lintegral_comp hg, volume_eq_prod, lintegral_prod _ hg'.aemeasurable,
    lintegral_pivotMatrix hf]
  refine lintegral_congr_ae ((ae_ne volume (0 : ℂ)).mono fun a ha ↦ ?_)
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.insertNth_zero', density_cons, mul_assoc]
  rw [lintegral_const_mul' _ _ (by simp), lintegral_pivotLDU ha hf,
    lintegral_pivot_induction a hf ih]

public section

namespace MeasureTheory

/-- Product Lebesgue measure on complex matrices in LDU (Bruhat) coordinates. The two strict
upper-entry families are independent, and the diagonal integral includes zero entries. -/
theorem lintegral_bruhat_coords {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞}
    (hf : Measurable f) :
    let E := {p : Fin n × Fin n // p.1 < p.2} → ℂ
    let U := TauCeti.unitDiagonalMatrixOfEntries (fun p : Fin n × Fin n ↦ p.1 < p.2)
    (∫⁻ c : Fin n → ℂ, (∏ i : Fin n, ‖c i‖ₑ ^ (4 * i.rev.val)) *
      ∫⁻ q : E × E, f ((U q.1)ᴴ * Matrix.diagonal c * U q.2)) = ∫⁻ M, f M := by
  -- Use the private names in the induction without exposing them in the public statement.
  change (∫⁻ c : CVec n, density c * ∫⁻ q : UpperEntries n × UpperEntries n, f (ldu c q)) = _
  induction n with
  | zero => exact lintegral_ldu_zero f
  | succ n ih => exact lintegral_ldu_succ hf (fun hg ↦ ih hg)

end MeasureTheory
