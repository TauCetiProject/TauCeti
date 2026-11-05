/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Jacobian of the partial-correlation parametrization

Partial correlations in the open cube parametrize positive-definite correlation matrices through
`TauCeti.correlationCoordinatesOfPartialCorrelation`. In column-major order, the derivative of
this map is lower triangular. Its diagonal entry for `(i, j)` is the product of the residual
factors from rows `i` and `j`. Regrouping these factors gives the Jacobian determinant

`\prod_{i > j} (1 - z_{ij}^2) ^ ((p - j - 2) / 2)`,

where indices in the exponent are zero-based. The absolute determinant has the same value because
every factor is nonnegative on the open cube. These formulas provide the change-of-variables input
for the LKJ normalizing integral.

## Main results

* `TauCeti.det_fderiv_correlationCoordinatesOfPartialCorrelation` computes the derivative
  determinant.
* `TauCeti.abs_det_fderiv_correlationCoordinatesOfPartialCorrelation` computes its absolute value.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open scoped BigOperators Matrix
open Set

namespace TauCeti

variable {p : ℕ}

private noncomputable def partialCorrelationResidual (z : strictLowerTriangle p → ℝ)
    (i j : Fin p) : ℝ :=
  ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < j, Real.sqrt (1 - z ij ^ 2)

private theorem partialCorrelationResidual_update_of_le
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ) (i j : Fin p)
    (h : j ≤ a.1.2) :
    partialCorrelationResidual (Function.update z a t) i j =
      partialCorrelationResidual z i j := by
  unfold partialCorrelationResidual
  apply Finset.prod_congr rfl
  intro b hb
  rw [Function.update_apply, ite_eq_right]
  intro hba
  subst a
  exact (not_lt_of_ge h) (Finset.mem_filter.1 hb).2.2

private theorem partialCorrelationResidual_update_of_ne
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ) (i j : Fin p)
    (h : i ≠ a.1.1) :
    partialCorrelationResidual (Function.update z a t) i j =
      partialCorrelationResidual z i j := by
  unfold partialCorrelationResidual
  apply Finset.prod_congr rfl
  intro b hb
  rw [Function.update_apply, ite_eq_right]
  intro hba
  subst a
  exact h (Finset.mem_filter.1 hb).2.1.symm

private theorem partialCorrelationResidual_self (z : strictLowerTriangle p → ℝ) (j : Fin p) :
    partialCorrelationResidual z j j =
      ∏ ij : strictLowerTriangle p with ij.1.1 = j, Real.sqrt (1 - z ij ^ 2) := by
  unfold partialCorrelationResidual
  apply Finset.prod_congr
  · ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hb
      exact ⟨hb, hb ▸ b.2⟩
  · intro _ _
    rfl

private theorem partialCorrelationCholesky_update_of_lt
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ)
    {i j : Fin p} (hja : j < a.1.2) :
    partialCorrelationCholesky (Function.update z a t) i j =
      partialCorrelationCholesky z i j := by
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [partialCorrelationCholesky_apply_of_gt _ hji,
      partialCorrelationCholesky_apply_of_gt _ hji]
    change Function.update z a t _ * partialCorrelationResidual (Function.update z a t) i j =
      z _ * partialCorrelationResidual z i j
    rw [partialCorrelationResidual_update_of_le _ _ _ _ _ hja.le]
    rw [Function.update_apply, ite_eq_right]
    intro h
    exact hja.ne (congrArg (fun b : strictLowerTriangle p ↦ b.1.2) h)
  · rw [partialCorrelationCholesky_apply_self, partialCorrelationCholesky_apply_self,
      ← partialCorrelationResidual_self, ← partialCorrelationResidual_self,
      partialCorrelationResidual_update_of_le _ _ _ _ _ hja.le]
  · rw [partialCorrelationCholesky_apply_of_lt _ hij,
      partialCorrelationCholesky_apply_of_lt _ hij]

private theorem partialCorrelationCholesky_update_of_ne
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ)
    {i j : Fin p} (hia : i ≠ a.1.1) :
    partialCorrelationCholesky (Function.update z a t) i j =
      partialCorrelationCholesky z i j := by
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [partialCorrelationCholesky_apply_of_gt _ hji,
      partialCorrelationCholesky_apply_of_gt _ hji]
    change Function.update z a t _ * partialCorrelationResidual (Function.update z a t) i j =
      z _ * partialCorrelationResidual z i j
    rw [partialCorrelationResidual_update_of_ne _ _ _ _ _ hia,
      Function.update_apply, ite_eq_right]
    intro h
    exact hia (congrArg (fun b : strictLowerTriangle p ↦ b.1.1) h)
  · rw [partialCorrelationCholesky_apply_self, partialCorrelationCholesky_apply_self,
      ← partialCorrelationResidual_self, ← partialCorrelationResidual_self,
      partialCorrelationResidual_update_of_ne _ _ _ _ _ hia]
  · rw [partialCorrelationCholesky_apply_of_lt _ hij,
      partialCorrelationCholesky_apply_of_lt _ hij]

private theorem partialCorrelationCholesky_update_self
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ) :
    partialCorrelationCholesky (Function.update z a t) a.1.1 a.1.2 =
      t * partialCorrelationResidual z a.1.1 a.1.2 := by
  rw [partialCorrelationCholesky_apply_of_gt _ a.2]
  change Function.update z a t a * partialCorrelationResidual (Function.update z a t) _ _ = _
  rw [partialCorrelationResidual_update_of_le _ _ _ _ _ le_rfl]
  simp

private theorem partialCorrelationGram_update_preceding
    (z : strictLowerTriangle p → ℝ) (a b : strictLowerTriangle p) (t : ℝ)
    (h : b.1.2 < a.1.2 ∨ (b.1.2 = a.1.2 ∧ b.1.1 < a.1.1)) :
    partialCorrelationGram (Function.update z a t) b.1.1 b.1.2 =
      partialCorrelationGram z b.1.1 b.1.2 := by
  rw [partialCorrelationGram_def, partialCorrelationGram_def]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  rcases h with hcol | ⟨hcol, hrow⟩
  · by_cases hk : k ≤ b.1.2
    · rw [partialCorrelationCholesky_update_of_lt _ _ _ (hk.trans_lt hcol),
        partialCorrelationCholesky_update_of_lt _ _ _ (hk.trans_lt hcol)]
    · have hbk : b.1.2 < k := lt_of_not_ge hk
      rw [partialCorrelationCholesky_apply_of_lt _ hbk,
        partialCorrelationCholesky_apply_of_lt _ hbk]
      simp
  · rw [partialCorrelationCholesky_update_of_ne _ _ _
        (ne_of_lt hrow),
      partialCorrelationCholesky_update_of_ne _ _ _
        (fun hb ↦ a.2.ne (hcol.symm.trans hb))]

private theorem partialCorrelationGram_update_self
    (z : strictLowerTriangle p → ℝ) (a : strictLowerTriangle p) (t : ℝ) :
    partialCorrelationGram (Function.update z a t) a.1.1 a.1.2 =
    partialCorrelationGram z a.1.1 a.1.2 + (t - z a) *
        (partialCorrelationResidual z a.1.1 a.1.2 *
          partialCorrelationResidual z a.1.2 a.1.2) := by
  rw [partialCorrelationGram_def, partialCorrelationGram_def]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a.1.2),
    ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a.1.2)]
  have herase :
      ∑ k ∈ Finset.univ.erase a.1.2,
          partialCorrelationCholesky (Function.update z a t) a.1.1 k *
            partialCorrelationCholesky (Function.update z a t) a.1.2 k =
        ∑ k ∈ Finset.univ.erase a.1.2,
          partialCorrelationCholesky z a.1.1 k * partialCorrelationCholesky z a.1.2 k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hne : k ≠ a.1.2 := Finset.ne_of_mem_erase hk
    rcases lt_or_gt_of_ne hne with hka | hak
    · rw [partialCorrelationCholesky_update_of_lt _ _ _ hka,
        partialCorrelationCholesky_update_of_lt _ _ _ hka]
    · rw [partialCorrelationCholesky_apply_of_lt _ hak,
        partialCorrelationCholesky_apply_of_lt _ hak]
      simp
  rw [herase, partialCorrelationCholesky_update_self,
    partialCorrelationCholesky_update_of_ne _ _ _ a.2.ne,
    partialCorrelationCholesky_apply_of_gt _ a.2,
    partialCorrelationCholesky_apply_self,
    ← partialCorrelationResidual_self]
  have ha : (⟨(a.1.1, a.1.2), a.2⟩ : strictLowerTriangle p) = a := Subtype.ext rfl
  rw [ha]
  change _ + t * partialCorrelationResidual z _ _ * partialCorrelationResidual z _ _ =
    _ + (z a * partialCorrelationResidual z _ _) * partialCorrelationResidual z _ _ +
      (t - z a) * (partialCorrelationResidual z _ _ * partialCorrelationResidual z _ _)
  ring

private theorem isOpen_partialCorrelationCube :
    IsOpen {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} := by
  rw [isOpen_pi_iff']
  intro z hz
  refine ⟨fun _ ↦ Ioo (-1) 1, fun ij ↦ ⟨isOpen_Ioo, abs_lt.1 (hz ij)⟩, ?_⟩
  intro w hw ij
  exact abs_lt.2 (hw ij trivial)

private theorem hasDerivAt_correlationCoordinatesOfPartialCorrelation_update
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (a b : strictLowerTriangle p) : HasDerivAt
      (fun t ↦ correlationCoordinatesOfPartialCorrelation (p := p) (Function.update z a t) b)
      ((fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)
        (Pi.single a 1) b) (z a) := by
  let F := correlationCoordinatesOfPartialCorrelation (p := p)
  have hdiff : DifferentiableAt ℝ F z :=
    (contDiffOn_correlationCoordinatesOfPartialCorrelation.contDiffAt
      (isOpen_partialCorrelationCube.mem_nhds hz)).differentiableAt (by simp)
  have hu := hasDerivAt_update z a (z a)
  have hupdate : Function.update z a (z a) = z := by
    funext i
    by_cases h : i = a
    · subst i
      simp
    · simp [h]
  have hdiff' : HasFDerivAt F (fderiv ℝ F z) (Function.update z a (z a)) := by
    simpa [hupdate] using hdiff.hasFDerivAt
  have hcomp := hdiff'.comp (z a) hu.hasFDerivAt
  have happ' : HasFDerivAt (fun f : strictLowerTriangle p → ℝ ↦ f b)
      (ContinuousLinearMap.proj (R := ℝ) b) ((F ∘ Function.update z a) (z a)) := by
    simpa [Function.comp_def, hupdate] using hasFDerivAt_apply b (F z)
  have happ := happ'.comp (z a) hcomp
  simpa [F, Function.comp_def] using happ.hasDerivAt

private theorem fderiv_correlationCoordinatesOfPartialCorrelation_eq_zero
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    {a b : strictLowerTriangle p}
    (h : b.1.2 < a.1.2 ∨ (b.1.2 = a.1.2 ∧ b.1.1 < a.1.1)) :
    (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)
        (Pi.single a 1) b = 0 := by
  let F := correlationCoordinatesOfPartialCorrelation (p := p)
  have hchain := hasDerivAt_correlationCoordinatesOfPartialCorrelation_update hz a b
  have hfun : (fun t ↦ F (Function.update z a t) b) = fun _ ↦ F z b := by
    funext t
    simpa only [F, correlationCoordinatesOfPartialCorrelation_apply] using
      partialCorrelationGram_update_preceding z a b t h
  rw [hfun] at hchain
  exact hchain.unique (hasDerivAt_const _ _)

private theorem fderiv_correlationCoordinatesOfPartialCorrelation_self
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (a : strictLowerTriangle p) :
    (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z)
        (Pi.single a 1) a =
      partialCorrelationResidual z a.1.1 a.1.2 *
        partialCorrelationResidual z a.1.2 a.1.2 := by
  let F := correlationCoordinatesOfPartialCorrelation (p := p)
  let c := partialCorrelationResidual z a.1.1 a.1.2 *
    partialCorrelationResidual z a.1.2 a.1.2
  have hchain := hasDerivAt_correlationCoordinatesOfPartialCorrelation_update hz a a
  have haffine : HasDerivAt (fun t : ℝ ↦ F z a + (t - z a) * c) c (z a) := by
    have h := (hasDerivAt_const (z a) (F z a)).add
      (((hasDerivAt_id (z a)).sub_const (z a)).mul_const c)
    convert h using 1
    · funext x
      simp
    · simp
  have hfun : (fun t ↦ F (Function.update z a t) a) =
      fun t ↦ F z a + (t - z a) * c := by
    funext t
    simpa only [F, c, correlationCoordinatesOfPartialCorrelation_apply] using
      partialCorrelationGram_update_self z a t
  rw [hfun] at hchain
  exact hchain.unique haffine

@[instance_reducible]
private def partialCorrelationCoordinateOrder : LinearOrder (strictLowerTriangle p) :=
  LinearOrder.lift' (fun ij ↦ toLex (ij.1.2, ij.1.1)) fun a b h ↦ by
    have hab := congrArg ofLex h
    exact Subtype.ext (Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab))

private theorem det_fderiv_correlationCoordinatesOfPartialCorrelation_residual
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    LinearMap.det
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).toLinearMap =
      ∏ a : strictLowerTriangle p,
        partialCorrelationResidual z a.1.1 a.1.2 *
          partialCorrelationResidual z a.1.2 a.1.2 := by
  let _ : LinearOrder (strictLowerTriangle p) := partialCorrelationCoordinateOrder
  rw [← LinearMap.det_toMatrix', Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_congr rfl
    intro a _
    rw [LinearMap.toMatrix'_apply]
    exact fderiv_correlationCoordinatesOfPartialCorrelation_self hz a
  · intro b a hba
    rw [LinearMap.toMatrix'_apply]
    apply fderiv_correlationCoordinatesOfPartialCorrelation_eq_zero hz
    have hba' : @LT.lt (strictLowerTriangle p) partialCorrelationCoordinateOrder.toLT b a := hba
    change toLex (b.1.2, b.1.1) < toLex (a.1.2, a.1.1) at hba'
    exact Prod.Lex.toLex_lt_toLex.1 hba'

private theorem card_partialCorrelationJacobian_fiber (b : strictLowerTriangle p) :
    ((Finset.univ.filter fun ab : strictLowerTriangle p × strictLowerTriangle p ↦
        (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨
          ab.2.1.1 = ab.1.1.2).filter fun ab ↦ ab.2 = b).card =
      p - b.1.2.val - 2 := by
  let source := (Finset.univ.filter fun ab : strictLowerTriangle p × strictLowerTriangle p ↦
    (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨
      ab.2.1.1 = ab.1.1.2).filter fun ab ↦ ab.2 = b
  let target := (Finset.Ioi b.1.2).erase b.1.1
  have hcard : source.card = target.card := by
    apply Finset.card_bij
      (fun ab _ ↦ if ab.1.1.1 = b.1.1 then ab.1.1.2 else ab.1.1.1)
    · intro ab hab
      simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hab
      rcases hab with ⟨hocc, hsnd⟩
      rw [hsnd] at hocc
      simp only [target, Finset.mem_erase, Finset.mem_Ioi]
      rcases hocc with ⟨hrow, hcol⟩ | hcol
      · rw [ite_eq_left hrow.symm]
        exact ⟨(ab.1.2.trans_eq hrow.symm).ne, hcol⟩
      · have hlt : b.1.1 < ab.1.1.1 := by simpa [hcol] using ab.1.2
        have hrow : ab.1.1.1 ≠ b.1.1 := hlt.ne'
        rw [ite_eq_right hrow]
        exact ⟨hlt.ne', b.2.trans hlt⟩
    · intro ab hab cd hcd heq
      simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hab hcd
      rcases hab with ⟨hab, habb⟩
      rcases hcd with ⟨hcd, hcdb⟩
      rw [habb] at hab
      rw [hcdb] at hcd
      have hsnd : ab.2 = cd.2 := habb.trans hcdb.symm
      apply Prod.ext
      · by_cases ha : ab.1.1.1 = b.1.1
        · by_cases hc : cd.1.1.1 = b.1.1
          · apply Subtype.ext
            apply Prod.ext
            · exact ha.trans hc.symm
            · simpa [ha, hc] using heq
          · rcases hcd with hcd | hcd
            · exact (hc hcd.1.symm).elim
            · exfalso
              have hleft : ab.1.1.2 < b.1.1 := ab.1.2.trans_eq ha
              have hright : b.1.1 < cd.1.1.1 := by simpa [hcd] using cd.1.2
              rw [ite_eq_left ha, ite_eq_right hc] at heq
              exact (heq ▸ hleft).asymm hright
        · by_cases hc : cd.1.1.1 = b.1.1
          · rcases hab with hab | hab
            · exact (ha hab.1.symm).elim
            · exfalso
              have hleft : b.1.1 < ab.1.1.1 := by simpa [hab] using ab.1.2
              have hright : cd.1.1.2 < b.1.1 := cd.1.2.trans_eq hc
              rw [ite_eq_right ha, ite_eq_left hc] at heq
              exact (heq ▸ hleft).asymm hright
          · have habcol : b.1.1 = ab.1.1.2 := by
              rcases hab with hab | hab
              · exact (ha hab.1.symm).elim
              · exact hab
            have hcdcol : b.1.1 = cd.1.1.2 := by
              rcases hcd with hcd | hcd
              · exact (hc hcd.1.symm).elim
              · exact hcd
            apply Subtype.ext
            apply Prod.ext
            · simpa [ha, hc] using heq
            · exact habcol.symm.trans hcdcol
      · exact hsnd
    · intro n hn
      simp only [target, Finset.mem_erase, Finset.mem_Ioi] at hn
      rcases lt_or_gt_of_ne hn.1 with hnr | hrn
      · let a : strictLowerTriangle p := ⟨(b.1.1, n), hnr⟩
        refine ⟨(a, b), ?_, ?_⟩
        · simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Or.inl ⟨rfl, hn.2⟩, trivial⟩
        · simp [a]
      · let a : strictLowerTriangle p := ⟨(n, b.1.1), hrn⟩
        refine ⟨(a, b), ?_, ?_⟩
        · simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Or.inr rfl, trivial⟩
        · simp [a, hn.1]
  change source.card = _
  rw [hcard]
  dsimp only [target]
  rw [Finset.card_erase_of_mem (Finset.mem_Ioi.2 b.2), Fin.card_Ioi]
  omega

open scoped Classical in
private theorem prod_prod_filter_eq {A : Type*} [Fintype A]
    (P : A → A → Prop) [DecidableRel P] (q : A → ℝ) :
    (∏ a : A, ∏ b : A with P a b, q b) =
      ∏ ab : A × A with P ab.1 ab.2, q ab.2 := by
  simp_rw [Finset.prod_filter]
  rw [← Fintype.prod_prod_type']

private theorem prod_partialCorrelationResidual_expand
    (z : strictLowerTriangle p → ℝ) :
    (∏ a : strictLowerTriangle p,
        partialCorrelationResidual z a.1.1 a.1.2 *
          partialCorrelationResidual z a.1.2 a.1.2) =
      (∏ a : strictLowerTriangle p,
          ∏ b : strictLowerTriangle p with
            b.1.1 = a.1.1 ∧ b.1.2 < a.1.2, Real.sqrt (1 - z b ^ 2)) *
        ∏ a : strictLowerTriangle p,
          ∏ b : strictLowerTriangle p with
            b.1.1 = a.1.2, Real.sqrt (1 - z b ^ 2) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact partialCorrelationResidual_self z a.1.2

private theorem prod_partialCorrelationFilters_eq_pairProduct
    (q : strictLowerTriangle p → ℝ) :
    ((∏ a : strictLowerTriangle p,
        ∏ b : strictLowerTriangle p with
          b.1.1 = a.1.1 ∧ b.1.2 < a.1.2, q b) *
      ∏ a : strictLowerTriangle p,
        ∏ b : strictLowerTriangle p with b.1.1 = a.1.2, q b) =
      ∏ ab : strictLowerTriangle p × strictLowerTriangle p with
        (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨
          ab.2.1.1 = ab.1.1.2, q ab.2 := by
  have hfirst :
      (∏ a : strictLowerTriangle p,
          ∏ b : strictLowerTriangle p with b.1.1 = a.1.1 ∧ b.1.2 < a.1.2, q b) =
        ∏ ab : strictLowerTriangle p × strictLowerTriangle p with
          ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2, q ab.2 :=
    prod_prod_filter_eq _ q
  have hsecond' :
      (∏ a : strictLowerTriangle p,
          ∏ b : strictLowerTriangle p with b.1.1 = a.1.2, q b) =
        ∏ ab : strictLowerTriangle p × strictLowerTriangle p with
          ab.2.1.1 = ab.1.1.2, q ab.2 :=
    prod_prod_filter_eq _ q
  rw [hfirst, hsecond']
  have hdisjoint : Disjoint
      (Finset.univ.filter fun ab : strictLowerTriangle p × strictLowerTriangle p ↦
        ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2)
      (Finset.univ.filter fun ab : strictLowerTriangle p × strictLowerTriangle p ↦
        ab.2.1.1 = ab.1.1.2) := by
    rw [Finset.disjoint_left]
    intro ab hab hab'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab hab'
    exact ab.1.2.ne (hab'.symm.trans hab.1)
  rw [← Finset.prod_union hdisjoint, ← Finset.filter_or]

private theorem prod_partialCorrelationResidual_eq_pair_product
    (z : strictLowerTriangle p → ℝ) :
    (∏ a : strictLowerTriangle p,
        partialCorrelationResidual z a.1.1 a.1.2 *
          partialCorrelationResidual z a.1.2 a.1.2) =
      ∏ ab : strictLowerTriangle p × strictLowerTriangle p with
        (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨
          ab.2.1.1 = ab.1.1.2, Real.sqrt (1 - z ab.2 ^ 2) :=
  (prod_partialCorrelationResidual_expand z).trans
    (prod_partialCorrelationFilters_eq_pairProduct _)

private theorem prod_pair_partialCorrelationResidual
    (z : strictLowerTriangle p → ℝ) :
    (∏ ab : strictLowerTriangle p × strictLowerTriangle p with
        (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨
          ab.2.1.1 = ab.1.1.2, Real.sqrt (1 - z ab.2 ^ 2)) =
      ∏ b : strictLowerTriangle p,
        Real.sqrt (1 - z b ^ 2) ^ (p - b.1.2.val - 2) := by
  let q := fun b : strictLowerTriangle p ↦ Real.sqrt (1 - z b ^ 2)
  let s := Finset.univ.filter fun ab : strictLowerTriangle p × strictLowerTriangle p ↦
    (ab.2.1.1 = ab.1.1.1 ∧ ab.2.1.2 < ab.1.1.2) ∨ ab.2.1.1 = ab.1.1.2
  change (∏ ab ∈ s, q ab.2) = _
  rw [← Finset.prod_fiberwise s Prod.snd (fun ab ↦ q ab.2)]
  apply Finset.prod_congr rfl
  intro b _
  calc
    (∏ ab ∈ s with ab.2 = b, q ab.2) =
        ∏ _ab ∈ s.filter (fun ab ↦ ab.2 = b), q b := by
          apply Finset.prod_congr rfl
          intro ab hab
          exact congrArg q (Finset.mem_filter.1 hab).2
    _ = q b ^ (s.filter fun ab ↦ ab.2 = b).card := by
      simpa only using
        (Finset.prod_const (s := s.filter fun ab ↦ ab.2 = b) (q b))
    _ = q b ^ (p - b.1.2.val - 2) := by
      rw [show (s.filter fun ab ↦ ab.2 = b).card = p - b.1.2.val - 2 by
        exact card_partialCorrelationJacobian_fiber b]

private theorem prod_partialCorrelationResidual (z : strictLowerTriangle p → ℝ) :
    (∏ a : strictLowerTriangle p,
        partialCorrelationResidual z a.1.1 a.1.2 *
          partialCorrelationResidual z a.1.2 a.1.2) =
      ∏ b : strictLowerTriangle p,
        Real.sqrt (1 - z b ^ 2) ^ (p - b.1.2.val - 2) :=
  (prod_partialCorrelationResidual_eq_pair_product z).trans
    (prod_pair_partialCorrelationResidual z)

private theorem sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt x ^ n = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The Jacobian determinant of the partial-correlation parametrization on the open cube.
For a coordinate in zero-based column `j`, the residual variance has exponent
`(p - j - 2) / 2`. -/
theorem det_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    LinearMap.det
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).toLinearMap =
      ∏ ij : strictLowerTriangle p,
        (1 - z ij ^ 2) ^ (((p - ij.1.2.val - 2 : ℕ) : ℝ) / 2) := by
  rw [det_fderiv_correlationCoordinatesOfPartialCorrelation_residual hz,
    prod_partialCorrelationResidual]
  apply Finset.prod_congr rfl
  intro ij _
  apply sqrt_pow_eq_rpow
  exact sub_nonneg.2 ((sq_le_one_iff_abs_le_one (z ij)).2 (hz ij).le)

/-- The absolute Jacobian determinant of the partial-correlation parametrization. -/
theorem abs_det_fderiv_correlationCoordinatesOfPartialCorrelation
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    |LinearMap.det
        (fderiv ℝ (correlationCoordinatesOfPartialCorrelation (p := p)) z).toLinearMap| =
      ∏ ij : strictLowerTriangle p,
        (1 - z ij ^ 2) ^ (((p - ij.1.2.val - 2 : ℕ) : ℝ) / 2) := by
  rw [det_fderiv_correlationCoordinatesOfPartialCorrelation hz, abs_of_nonneg]
  exact Finset.prod_nonneg fun ij _ ↦ Real.rpow_nonneg
    (sub_nonneg.2 ((sq_le_one_iff_abs_le_one (z ij)).2 (hz ij).le)) _

end TauCeti
