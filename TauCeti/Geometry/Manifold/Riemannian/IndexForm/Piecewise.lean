/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Piecewise
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The index form on piecewise smooth sections

For a continuous piecewise `C^n` curve `γ` on `[a, b]` with `1 ≤ n`, the Riemannian index form
descends to a symmetric real bilinear form `TauCeti.Manifold.piecewiseIndexForm` on the interval
section module `TauCeti.Manifold.PiecewiseContMDiffSectionAlong`. Because `indexForm` depends only
on values on the open interval `(a, b)`, evaluating `piecewiseIndexForm` on bundled sections agrees
with `indexForm` on any extensions to the real line. Restricting to the fixed-endpoint submodule
`PiecewiseContMDiffSectionAlong.endpointZero` gives `TauCeti.Manifold.endpointZeroIndexForm`.

When `V` is `C²` on each piece `[τᵢ, τᵢ₊₁]` of a partition of `[a, b]` and `W` is continuous and
piecewise `C¹`, integrating by parts on each piece expresses `indexForm I γ V W a b` as the
endpoint boundary terms minus the interior covariant-derivative jump pairings

`∑ j, ⟪D_t⁺ V(τⱼ₊₁) - D_t⁻ V(τⱼ₊₁), W(τⱼ₊₁)⟫`

minus the sum of the piece Jacobi-operator integrals. When `V` is a broken Jacobi field on the
partition, the piece integrals vanish; when `V` is an unbroken Jacobi field on `[a, b]`, the
interior jumps also vanish and the smooth integration-by-parts formula extends to all continuous
piecewise `C¹` test fields `W`.

## Main definitions and results

* `TauCeti.Manifold.IsPiecewiseContMDiffOn.intervalIntegrable_indexFormIntegrand`,
  `TauCeti.Manifold.IsPiecewiseContMDiffOn.indexForm_add_left`, and right/subtraction variants:
  integrability and bilinearity of `indexForm` on continuous piecewise `C¹` fields.
* `TauCeti.Manifold.indexForm_eq_inner_sub_sum_jump_sub_sum_integral` and
  `TauCeti.Manifold.indexForm_eq_inner_sub_sum_jump_of_isJacobiFieldOn`: piecewise integration by
  parts with interior covariant-derivative jumps, and its broken-Jacobi specialization.
* `TauCeti.Manifold.IsJacobiFieldOn.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn` and
  `TauCeti.Manifold.IsJacobiFieldOn.indexForm_eq_zero_of_isPiecewiseContMDiffOn`: pairing an
  unbroken Jacobi field with a continuous piecewise `C¹` field.
* `TauCeti.Manifold.piecewiseIndexForm` and `TauCeti.Manifold.endpointZeroIndexForm`: the symmetric
  bilinear index form on `PiecewiseContMDiffSectionAlong` and on its fixed-endpoint submodule.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §§13–14.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V V' W W' : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {n : ℕ∞ω} {a b : ℝ}

/-! ### Integrability and bilinearity on piecewise `C¹` fields -/

/-- The integrand of the index form is interval integrable on `[a, b]` when both fields are
piecewise `C¹` on `[a, b]`. -/
theorem IsPiecewiseContMDiffOn.intervalIntegrable_indexFormIntegrand
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b) :
    IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume a b :=
  (hV.prodMk hW).induction_on
    (fun _ _ huv hpair ↦ TauCeti.Manifold.intervalIntegrable_indexFormIntegrand
      (uIcc_of_le huv.le ▸ contMDiff_fst.comp_contMDiffOn hpair)
      (uIcc_of_le huv.le ▸ contMDiff_snd.comp_contMDiffOn hpair))
    fun _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂

/-- The index form is additive in its first slot on continuous piecewise `C¹` fields, even when
their witnessing partitions differ. -/
theorem IsPiecewiseContMDiffOn.indexForm_add_left
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hV' : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b) :
    indexForm I γ (V + V') W a b = indexForm I γ V W a b + indexForm I γ V' W a b := by
  refine ((hV.prodMk hV').prodMk hW).induction_on
    (P := fun u v ↦
      IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) u v →
      IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) u v →
      IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) u v →
      indexForm I γ (V + V') W u v = indexForm I γ V W u v + indexForm I γ V' W u v)
    (fun u v huv htriple _ _ _ ↦ ?_) (fun u v w huv hvw ih₁ ih₂ hVuv hV'uv hWuv ↦ ?_) hV hV' hW
  · have hpair := contMDiff_fst.comp_contMDiffOn htriple
    exact TauCeti.Manifold.indexForm_add_left
      (uIcc_of_le huv.le ▸ contMDiff_fst.comp_contMDiffOn hpair)
      (uIcc_of_le huv.le ▸ contMDiff_snd.comp_contMDiffOn hpair)
      (uIcc_of_le huv.le ▸ contMDiff_snd.comp_contMDiffOn htriple)
  · have hsum : IsPiecewiseContMDiffOn I.tangent 1
        (fun r ↦ TotalSpace.mk' E (γ r) ((V + V') r)) u w :=
      hVuv.add_sectionAlong hV'uv
    rw [← indexForm_add_adjacent_intervals
        ((hsum.mono le_rfl huv hvw.le).intervalIntegrable_indexFormIntegrand
          (hWuv.mono le_rfl huv hvw.le))
        ((hsum.mono huv.le hvw le_rfl).intervalIntegrable_indexFormIntegrand
          (hWuv.mono huv.le hvw le_rfl)),
      ← indexForm_add_adjacent_intervals
        ((hVuv.mono le_rfl huv hvw.le).intervalIntegrable_indexFormIntegrand
          (hWuv.mono le_rfl huv hvw.le))
        ((hVuv.mono huv.le hvw le_rfl).intervalIntegrable_indexFormIntegrand
          (hWuv.mono huv.le hvw le_rfl)),
      ← indexForm_add_adjacent_intervals
        ((hV'uv.mono le_rfl huv hvw.le).intervalIntegrable_indexFormIntegrand
          (hWuv.mono le_rfl huv hvw.le))
        ((hV'uv.mono huv.le hvw le_rfl).intervalIntegrable_indexFormIntegrand
          (hWuv.mono huv.le hvw le_rfl)),
      ih₁ (hVuv.mono le_rfl huv hvw.le) (hV'uv.mono le_rfl huv hvw.le)
        (hWuv.mono le_rfl huv hvw.le),
      ih₂ (hVuv.mono huv.le hvw le_rfl) (hV'uv.mono huv.le hvw le_rfl)
        (hWuv.mono huv.le hvw le_rfl)]
    ring

/-- The index form is additive in its second slot on continuous piecewise `C¹` fields. -/
theorem IsPiecewiseContMDiffOn.indexForm_add_right
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hW' : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W' r)) a b) :
    indexForm I γ V (W + W') a b = indexForm I γ V W a b + indexForm I γ V W' a b := by
  rw [indexForm_comm, hW.indexForm_add_left hW' hV, indexForm_comm, indexForm_comm (V := W')]

/-- The index form respects subtraction in its first slot on continuous piecewise `C¹` fields. -/
theorem IsPiecewiseContMDiffOn.indexForm_sub_left
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hV' : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b) :
    indexForm I γ (V - V') W a b = indexForm I γ V W a b - indexForm I γ V' W a b := by
  rw [sub_eq_add_neg, hV.indexForm_add_left (V' := -V') hV'.neg_sectionAlong hW,
    indexForm_neg_left, sub_eq_add_neg]

/-- The index form respects subtraction in its second slot on continuous piecewise `C¹` fields. -/
theorem IsPiecewiseContMDiffOn.indexForm_sub_right
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hW' : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W' r)) a b) :
    indexForm I γ V (W - W') a b = indexForm I γ V W a b - indexForm I γ V W' a b := by
  rw [indexForm_comm, hW.indexForm_sub_left hW' hV, indexForm_comm, indexForm_comm (V := W')]

/-! ### Piecewise integration by parts and covariant-derivative jumps -/

/-- **Piecewise integration by parts.** On a partition `τ₀ ≤ τ₁ ≤ ⋯ ≤ τ_{k+1}` where `V` is `C²`
on each closed piece and `W` is `C¹` on each closed piece, the index form equals the endpoint
boundary pairings minus the interior covariant-derivative jump pairings minus the sum of the piece
Jacobi-operator integrals. -/
theorem indexForm_eq_inner_sub_sum_jump_sub_sum_integral {k : ℕ} (τ : Fin (k + 2) → ℝ)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hV : ∀ i : Fin (k + 1), ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc (τ i.castSucc) (τ i.succ)))
    (hW : ∀ i : Fin (k + 1), ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc (τ i.castSucc) (τ i.succ))) :
    indexForm I γ V W (τ 0) (τ (Fin.last (k + 1))) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ)) (τ (Fin.last (k + 1))))
        (W (τ (Fin.last (k + 1)))) -
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ (0 : Fin (k + 1)).castSucc) (τ (0 : Fin (k + 1)).succ)) (τ 0))
        (W (τ 0)) -
      ∑ j : Fin k, inner ℝ
        (alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ) -
          alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ))
        (W (τ j.castSucc.succ)) -
      ∑ i : Fin (k + 1), ∫ t in (τ i.castSucc)..(τ i.succ),
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V
              (Icc (τ i.castSucc) (τ i.succ))) (Icc (τ i.castSucc) (τ i.succ)) t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)
            (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)) (W t) := by
  have hint (i : Fin (k + 1)) : IntervalIntegrable (indexFormIntegrand I γ V W)
      MeasureTheory.volume (τ i.castSucc) (τ i.succ) :=
    intervalIntegrable_indexFormIntegrand
      (uIcc_of_le (hτ i) ▸ (hV i).of_le one_le_two) (uIcc_of_le (hτ i) ▸ hW i)
  rw [← sum_indexForm_adjacent_intervals τ hint]
  have hpiece (i : Fin (k + 1)) :
      indexForm I γ V W (τ i.castSucc) (τ i.succ) =
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ i.castSucc) (τ i.succ)) (τ i.succ)) (W (τ i.succ)) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ i.castSucc) (τ i.succ)) (τ i.castSucc)) (W (τ i.castSucc)) -
        ∫ t in (τ i.castSucc)..(τ i.succ),
          inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
              (alongCurveWithin (leviCivitaConnection I M) γ V
                (Icc (τ i.castSucc) (τ i.succ))) (Icc (τ i.castSucc) (τ i.succ)) t +
            (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
              (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)
              (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)) (W t) :=
    indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral
      (fun t ht ↦ hV i t (uIcc_of_le (hτ i) ▸ ht))
      (uIcc_of_le (hτ i) ▸ hW i) (uIcc_of_le (hτ i)).le
  simp_rw [hpiece, Finset.sum_sub_distrib]
  congr 1
  let R : Fin (k + 1) → ℝ := fun i ↦
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
      (Icc (τ i.castSucc) (τ i.succ)) (τ i.succ)) (W (τ i.succ))
  let L : Fin (k + 1) → ℝ := fun i ↦
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
      (Icc (τ i.castSucc) (τ i.succ)) (τ i.castSucc)) (W (τ i.castSucc))
  -- Split off the final right-endpoint pairing and the initial left-endpoint pairing; the
  -- remaining interior terms pair up because `(j.castSucc).succ` and `(j.succ).castSucc` are
  -- definitionally the same vertex of `τ`.
  simp_rw [inner_sub_left]
  change (∑ i : Fin (k + 1), R i) - (∑ i : Fin (k + 1), L i) =
    R (Fin.last k) - L 0 - ∑ j : Fin k, (L j.succ - R j.castSucc)
  rw [Fin.sum_univ_castSucc R, Fin.sum_univ_succ L, Finset.sum_sub_distrib]
  ring

/-- **Broken-Jacobi integration by parts.** When `V` is a Jacobi field on each piece
`[τᵢ, τᵢ₊₁]` of a partition and `W` is `C¹` on each piece, the index form reduces to the endpoint
boundary pairings minus the interior covariant-derivative jump pairings. -/
theorem indexForm_eq_inner_sub_sum_jump_of_isJacobiFieldOn {k : ℕ} (τ : Fin (k + 2) → ℝ)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hV : ∀ i : Fin (k + 1), IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)))
    (hW : ∀ i : Fin (k + 1), ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc (τ i.castSucc) (τ i.succ))) :
    indexForm I γ V W (τ 0) (τ (Fin.last (k + 1))) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ)) (τ (Fin.last (k + 1))))
        (W (τ (Fin.last (k + 1)))) -
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ (0 : Fin (k + 1)).castSucc) (τ (0 : Fin (k + 1)).succ)) (τ 0))
        (W (τ 0)) -
      ∑ j : Fin k, inner ℝ
        (alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ) -
          alongCurveWithin (leviCivitaConnection I M) γ V
            (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ))
        (W (τ j.castSucc.succ)) := by
  rw [indexForm_eq_inner_sub_sum_jump_sub_sum_integral τ hτ (fun i ↦ (hV i).contMDiffOn) hW]
  have hzero (i : Fin (k + 1)) :
      (∫ t in (τ i.castSucc)..(τ i.succ),
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V
              (Icc (τ i.castSucc) (τ i.succ))) (Icc (τ i.castSucc) (τ i.succ)) t +
          (leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)
            (curveVelocityWithin I γ (Icc (τ i.castSucc) (τ i.succ)) t)) (W t)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      simp only [(hV i).equation t (uIcc_of_le (hτ i) ▸ ht), inner_zero_left]]
    exact intervalIntegral.integral_zero
  simp only [hzero, Finset.sum_const_zero, sub_zero]

/-- **Jacobi integration by parts against a piecewise `C¹` field.** For an unbroken Jacobi field
`V` on `s ⊇ [a, b]` and a continuous piecewise `C¹` field `W` on `[a, b]`,
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. -/
theorem IsJacobiFieldOn.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn
    (hV : IsJacobiFieldOn I γ V s)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hsub : Icc a b ⊆ s) :
    indexForm I γ V W a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) := by
  refine hW.induction_on
    (P := fun u v ↦ Icc u v ⊆ s →
      IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) u v →
      indexForm I γ V W u v =
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s v) (W v) -
          inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s u) (W u))
    (fun u v huv hWpiece huvs _ ↦ hV.indexForm_eq_inner_sub_inner
      (uIcc_of_le huv.le ▸ hWpiece) (uIcc_of_le huv.le ▸ huvs))
    (fun u v w huv hvw ih₁ ih₂ huws hWuw ↦ ?_) hsub hW
  have hVu : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) u w :=
    .of_contMDiffOn (huv.trans hvw) ((hV.contMDiffOn.mono huws).of_le one_le_two)
  rw [← indexForm_add_adjacent_intervals
      ((hVu.mono le_rfl huv hvw.le).intervalIntegrable_indexFormIntegrand
        (hWuw.mono le_rfl huv hvw.le))
      ((hVu.mono huv.le hvw le_rfl).intervalIntegrable_indexFormIntegrand
        (hWuw.mono huv.le hvw le_rfl)),
    ih₁ ((Icc_subset_Icc_right hvw.le).trans huws) (hWuw.mono le_rfl huv hvw.le),
    ih₂ ((Icc_subset_Icc_left huv.le).trans huws) (hWuw.mono huv.le hvw le_rfl)]
  ring

/-- Every unbroken Jacobi field on `[a, b]` is index-orthogonal to every continuous piecewise `C¹`
field vanishing at `a` and `b`. -/
theorem IsJacobiFieldOn.indexForm_eq_zero_of_isPiecewiseContMDiffOn
    (hV : IsJacobiFieldOn I γ V s)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hsub : Icc a b ⊆ s) (hWa : W a = 0) (hWb : W b = 0) :
    indexForm I γ V W a b = 0 := by
  rw [hV.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn hW hsub, hWa, hWb,
    inner_zero_right, inner_zero_right, sub_self]

/-- Boundary-corrected Jacobi integration by parts for a continuous piecewise `C¹` test field:
if `D_t V(a) + u` is orthogonal to `W(a)`, then `I(V, W) - ⟪u, W(a)⟫ = ⟪D_t V(b), W(b)⟫`. -/
theorem IsJacobiFieldOn.indexForm_sub_inner_eq_inner_of_isPiecewiseContMDiffOn
    (hV : IsJacobiFieldOn I γ V s)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hsub : Icc a b ⊆ s) {u : TangentSpace I (γ a)}
    (hinit : inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a + u) (W a) = 0) :
    indexForm I γ V W a b - inner ℝ u (W a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) := by
  rw [hV.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn hW hsub]
  rw [inner_add_left] at hinit
  linarith

/-! ### The bilinear index form on bundled piecewise smooth sections -/

section Bundled

variable (hγ : IsPiecewiseContMDiffOn I n γ a b) (hn : 1 ≤ n)

/-- The Riemannian index form as a real bilinear form on bundled continuous piecewise `C^n`
tangent sections along `γ` on `[a, b]`, for `1 ≤ n`. -/
def piecewiseIndexForm :
    LinearMap.BilinForm ℝ (PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :=
  LinearMap.mk₂ ℝ (fun V W ↦ indexForm I γ V.extendByZero W.extendByZero a b)
    (fun V₁ V₂ W ↦ by
      rw [map_add]
      exact (V₁.isPiecewiseContMDiffOn_extendByZero.of_le hn).indexForm_add_left
        (V₂.isPiecewiseContMDiffOn_extendByZero.of_le hn)
        (W.isPiecewiseContMDiffOn_extendByZero.of_le hn))
    (fun c _ _ ↦ by rw [map_smul]; exact indexForm_const_smul_left c)
    (fun V W₁ W₂ ↦ by
      rw [map_add]
      exact (V.isPiecewiseContMDiffOn_extendByZero.of_le hn).indexForm_add_right
        (W₁.isPiecewiseContMDiffOn_extendByZero.of_le hn)
        (W₂.isPiecewiseContMDiffOn_extendByZero.of_le hn))
    (fun c _ _ ↦ by rw [map_smul]; exact indexForm_const_smul_right c)

/-- Defining formula for `piecewiseIndexForm` via canonical zero extensions. -/
@[simp] theorem piecewiseIndexForm_apply
    (V W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    piecewiseIndexForm hγ hn V W = indexForm I γ V.extendByZero W.extendByZero a b := (rfl)

/-- `piecewiseIndexForm` equals the unbundled `indexForm` of any two extensions agreeing with the
bundled fields on `(a, b)`. -/
theorem piecewiseIndexForm_eq_indexForm_of_eqOn_Ioo
    (V W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ)
    {U U' : ∀ t, TangentSpace I (γ t)}
    (hU : ∀ t (ht : t ∈ Ioo a b), U t = V.val ⟨t, Ioo_subset_Icc_self ht⟩)
    (hU' : ∀ t (ht : t ∈ Ioo a b), U' t = W.val ⟨t, Ioo_subset_Icc_self ht⟩) :
    piecewiseIndexForm hγ hn V W = indexForm I γ U U' a b := by
  rw [piecewiseIndexForm_apply]
  refine indexForm_congr (fun _ _ ↦ rfl) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · rw [uIoo_of_lt hγ.lt] at ht
    exact heq_of_eq ((V.extendByZero_apply_of_mem (Ioo_subset_Icc_self ht)).trans (hU t ht).symm)
  · rw [uIoo_of_lt hγ.lt] at ht
    exact heq_of_eq ((W.extendByZero_apply_of_mem (Ioo_subset_Icc_self ht)).trans (hU' t ht).symm)

/-- Evaluating `piecewiseIndexForm` on fields from piecewise `C^n` sections recovers `indexForm`. -/
theorem piecewiseIndexForm_ofPiecewise (U U' : ∀ t, TangentSpace I (γ t))
    (hU : IsPiecewiseContMDiffOn I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (U t)) a b)
    (hU' : IsPiecewiseContMDiffOn I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (U' t)) a b) :
    piecewiseIndexForm hγ hn (.ofPiecewise U hU) (.ofPiecewise U' hU') = indexForm I γ U U' a b :=
  piecewiseIndexForm_eq_indexForm_of_eqOn_Ioo hγ hn _ _ (by simp) (by simp)

/-- Evaluating `piecewiseIndexForm` on fields from `C^n` sections on `[a, b]` recovers
`indexForm`. -/
theorem piecewiseIndexForm_ofContMDiffOn (U U' : ∀ t, TangentSpace I (γ t))
    (hU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (U t)) (Icc a b))
    (hU' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (U' t)) (Icc a b)) :
    piecewiseIndexForm hγ hn (.ofContMDiffOn U hU) (.ofContMDiffOn U' hU') =
      indexForm I γ U U' a b :=
  piecewiseIndexForm_eq_indexForm_of_eqOn_Ioo hγ hn _ _ (by simp) (by simp)

/-- The bundled piecewise index form is symmetric in its two arguments. -/
theorem piecewiseIndexForm_comm
    (V W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    piecewiseIndexForm hγ hn V W = piecewiseIndexForm hγ hn W V := indexForm_comm

/-- Symmetry of `piecewiseIndexForm` as `LinearMap.BilinForm.IsSymm`. -/
theorem isSymm_piecewiseIndexForm : (piecewiseIndexForm hγ hn).IsSymm :=
  ⟨piecewiseIndexForm_comm hγ hn⟩

/-- Lowering the differentiability order of bundled sections leaves `piecewiseIndexForm`
unchanged. -/
theorem piecewiseIndexForm_ofLE {m : ℕ∞ω} (hnm : n ≤ m) {hγm : IsPiecewiseContMDiffOn I m γ a b}
    (V W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγm) :
    piecewiseIndexForm (hγm.of_le hnm) hn (.ofLE hnm V) (.ofLE hnm W) =
      piecewiseIndexForm hγm (hn.trans hnm) V W := by
  simp [piecewiseIndexForm_apply]

/-- Splitting `[a, b]` at an interior parameter `c` decomposes `piecewiseIndexForm` as the sum of
the restricted index forms on `[a, c]` and `[c, b]`. -/
theorem piecewiseIndexForm_add_adjacent_intervals {c : ℝ} (hac : a < c) (hcb : c < b)
    (V W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    piecewiseIndexForm (hγ.mono le_rfl hac hcb.le) hn
        (.restrict le_rfl hac hcb.le V) (.restrict le_rfl hac hcb.le W) +
      piecewiseIndexForm (hγ.mono hac.le hcb le_rfl) hn
        (.restrict hac.le hcb le_rfl V) (.restrict hac.le hcb le_rfl W) =
      piecewiseIndexForm hγ hn V W := by
  have hV1 := V.isPiecewiseContMDiffOn_extendByZero.of_le hn
  have hW1 := W.isPiecewiseContMDiffOn_extendByZero.of_le hn
  rw [piecewiseIndexForm_eq_indexForm_of_eqOn_Ioo (hγ.mono le_rfl hac hcb.le) hn _ _
      (U := V.extendByZero) (U' := W.extendByZero)
      (fun _ ht ↦ by simp [ht.1.le, ht.2.le.trans hcb.le])
      (fun _ ht ↦ by simp [ht.1.le, ht.2.le.trans hcb.le]),
    piecewiseIndexForm_eq_indexForm_of_eqOn_Ioo (hγ.mono hac.le hcb le_rfl) hn _ _
      (U := V.extendByZero) (U' := W.extendByZero)
      (fun _ ht ↦ by simp [hac.le.trans ht.1.le, ht.2.le])
      (fun _ ht ↦ by simp [hac.le.trans ht.1.le, ht.2.le]),
    piecewiseIndexForm_apply]
  exact indexForm_add_adjacent_intervals
    ((hV1.mono le_rfl hac hcb.le).intervalIntegrable_indexFormIntegrand
      (hW1.mono le_rfl hac hcb.le))
    ((hV1.mono hac.le hcb le_rfl).intervalIntegrable_indexFormIntegrand
      (hW1.mono hac.le hcb le_rfl))

/-- The Riemannian index form restricted to `PiecewiseContMDiffSectionAlong.endpointZero`. -/
def endpointZeroIndexForm :
    LinearMap.BilinForm ℝ
      (PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ)) :=
  (piecewiseIndexForm hγ hn).restrict _

/-- Evaluating `endpointZeroIndexForm` delegates to `piecewiseIndexForm` on the underlying
interval sections. -/
@[simp] theorem endpointZeroIndexForm_apply
    (V W : PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ)) :
    endpointZeroIndexForm hγ hn V W = piecewiseIndexForm hγ hn V.val W.val := (rfl)

/-- Lowering the differentiability order of fixed-endpoint sections leaves
`endpointZeroIndexForm` unchanged. -/
theorem endpointZeroIndexForm_ofLE {m : ℕ∞ω} (hnm : n ≤ m) {hγm : IsPiecewiseContMDiffOn I m γ a b}
    (V W : PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγm)) :
    endpointZeroIndexForm (hγm.of_le hnm) hn (PiecewiseContMDiffSectionAlong.endpointZeroOfLE hnm V)
      (PiecewiseContMDiffSectionAlong.endpointZeroOfLE hnm W) =
      endpointZeroIndexForm hγm (hn.trans hnm) V W := by
  simp [piecewiseIndexForm_ofLE hn hnm]

/-- The fixed-endpoint index form is symmetric in its two arguments. -/
theorem endpointZeroIndexForm_comm
    (V W : PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ)) :
    endpointZeroIndexForm hγ hn V W = endpointZeroIndexForm hγ hn W V :=
  piecewiseIndexForm_comm hγ hn V.val W.val

/-- Symmetry of `endpointZeroIndexForm` as `LinearMap.BilinForm.IsSymm`. -/
theorem isSymm_endpointZeroIndexForm : (endpointZeroIndexForm hγ hn).IsSymm :=
  (isSymm_piecewiseIndexForm hγ hn).restrict _

end Bundled

end TauCeti.Manifold
