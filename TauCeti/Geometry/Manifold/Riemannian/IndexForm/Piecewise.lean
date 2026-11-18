/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Piecewise

/-!
# The index form on piecewise smooth fields

Let `γ` be a curve in a Riemannian manifold, piecewise `C¹` on `[a, b]`. The continuous piecewise
`C¹` tangent fields along `γ` on `[a, b]` form the real vector space
`TauCeti.Manifold.PiecewiseContMDiffSectionAlong`. This file shows that the index form

`I(V, W) = ∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt`

is a symmetric bilinear form on that space. Its integrand involves derivatives of the
fields, which may fail to exist at their finitely many corners without affecting the integral,
and it is computed on any extensions of the fields from `[a, b]` to the whole parameter line.
Restricting it to the fixed-endpoint subspace
`TauCeti.Manifold.PiecewiseContMDiffSectionAlong.endpointZero` gives the form whose index and
nullity the Morse index theorem computes.

Integration by parts on each smooth piece of a field `W` telescopes, because `W` is continuous at
the corners. So for a Jacobi field `V` the value `I(V, W)` is the boundary term
`⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`, and a Jacobi field is orthogonal for the index form to
every piecewise smooth field vanishing at both ends.

## Main definitions and results

* `TauCeti.Manifold.intervalIntegrable_indexFormIntegrand_of_isPiecewiseContMDiffOn`,
  `TauCeti.Manifold.indexForm_add_left_of_isPiecewiseContMDiffOn`: integrability and additivity
  for fields with piecewise `C¹` lifts and different corners.
* `TauCeti.Manifold.IsJacobiFieldOn.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn`:
  Jacobi integration by parts against a piecewise `C¹` field.
* `TauCeti.Manifold.indexBilinForm`: the index form as a `LinearMap.BilinForm` on continuous
  piecewise `C¹` fields, characterized by `TauCeti.Manifold.indexBilinForm_apply`, and symmetric
  by `TauCeti.Manifold.indexBilinForm_isSymm`.
* `TauCeti.Manifold.indexBilinForm_add_adjacent_intervals`: additivity under restriction to the
  two sides of an interior parameter.
* `TauCeti.Manifold.IsJacobiFieldOn.indexBilinForm_eq_inner_sub_inner` and
  `TauCeti.Manifold.IsJacobiFieldOn.indexBilinForm_eq_zero_of_mem_endpointZero`: a Jacobi field
  pairs with a piecewise smooth field through the boundary term, which vanishes on the
  fixed-endpoint subspace.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press
  (1963), §13, the Hessian of the energy on piecewise smooth vector fields.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10, §2.
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
  {γ : ℝ → M} {V V' W : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a b : ℝ}

/-! ### Fields with piecewise smooth lifts -/

/-- The integrand of the index form is interval integrable when both fields have piecewise `C¹`
lifts on `[a, b]`, possibly with different corners. -/
theorem intervalIntegrable_indexFormIntegrand_of_isPiecewiseContMDiffOn
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b) :
    IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume a b :=
  (hV.prodMk hW).induction_on
    (P := fun u v ↦ IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume u v)
    (fun u v huv h ↦ by
      rw [← uIcc_of_le huv.le] at h
      exact intervalIntegrable_indexFormIntegrand (contMDiff_fst.comp_contMDiffOn h)
        (contMDiff_snd.comp_contMDiffOn h))
    fun _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂

/-- The index form is additive in its first field on fields with piecewise `C¹` lifts on
`[a, b]`, whose corners may differ. -/
theorem indexForm_add_left_of_isPiecewiseContMDiffOn
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hV' : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V' r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b) :
    indexForm I γ (V + V') W a b = indexForm I γ V W a b + indexForm I γ V' W a b := by
  -- integrability on every subinterval of `[a, b]`, from the piecewise regularity there
  have hint {X : ∀ t, TangentSpace I (γ t)}
      (hX : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (X r)) a b)
      {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      IntervalIntegrable (indexFormIntegrand I γ X W) MeasureTheory.volume u v :=
    (intervalIntegrable_indexFormIntegrand_of_isPiecewiseContMDiffOn hX hW).mono_set
      (uIcc_subset_uIcc (mem_uIcc_of_le hau (huv.trans hvb)) (mem_uIcc_of_le (hau.trans huv) hvb))
  refine ((hV.prodMk hV').prodMk hW).induction_on
    (P := fun u v ↦ a ≤ u → v ≤ b →
      indexForm I γ (V + V') W u v = indexForm I γ V W u v + indexForm I γ V' W u v)
    (fun u v huv h _ _ ↦ ?_) (fun u v w huv hvw h₁ h₂ hau hwb ↦ ?_) le_rfl le_rfl
  · rw [← uIcc_of_le huv.le] at h
    have hVV' := contMDiff_fst.comp_contMDiffOn h
    exact indexForm_add_left (contMDiff_fst.comp_contMDiffOn hVV')
      (contMDiff_snd.comp_contMDiffOn hVV') (contMDiff_snd.comp_contMDiffOn h)
  · have hvb := hvw.le.trans hwb
    have hav := hau.trans huv.le
    have hVV' := hV.add_sectionAlong hV'
    rw [← indexForm_add_adjacent_intervals (hint (X := V + V') hVV' hau huv.le hvb)
        (hint (X := V + V') hVV' hav hvw.le hwb),
      ← indexForm_add_adjacent_intervals (hint hV hau huv.le hvb) (hint hV hav hvw.le hwb),
      ← indexForm_add_adjacent_intervals (hint hV' hau huv.le hvb) (hint hV' hav hvw.le hwb),
      h₁ hau hvb, h₂ hav hwb]
    ring

/-- **Jacobi integration by parts against a piecewise smooth field.** For a Jacobi field `V` on a
set containing `[a, b]` and a field `W` with a piecewise `C¹` lift on `[a, b]`,
`I(V, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`: the boundary terms at the corners of `W`
cancel. -/
theorem IsJacobiFieldOn.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn
    (h : IsJacobiFieldOn I γ V s)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hsub : Icc a b ⊆ s) :
    indexForm I γ V W a b =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) := by
  refine (hW.induction_on
    (P := fun u v ↦ Icc u v ⊆ s →
      IntervalIntegrable (indexFormIntegrand I γ V W) MeasureTheory.volume u v ∧
      indexForm I γ V W u v =
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s v) (W v) -
          inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s u) (W u))
    (fun u v huv hWuv hsub ↦ ?_) (fun u v w huv hvw h₁ h₂ hsub ↦ ?_) hsub).2
  · rw [← uIcc_of_le huv.le] at hWuv hsub
    exact ⟨intervalIntegrable_indexFormIntegrand
        ((h.contMDiffOn.mono hsub).of_le one_le_two) hWuv,
      h.indexForm_eq_inner_sub_inner hWuv hsub⟩
  · obtain ⟨hi₁, he₁⟩ := h₁ ((Icc_subset_Icc le_rfl hvw.le).trans hsub)
    obtain ⟨hi₂, he₂⟩ := h₂ ((Icc_subset_Icc huv.le le_rfl).trans hsub)
    refine ⟨hi₁.trans hi₂, ?_⟩
    rw [← indexForm_add_adjacent_intervals hi₁ hi₂, he₁, he₂]
    ring

/-! ### The index form as a bilinear form -/

section Bundled

variable (hγ : IsPiecewiseContMDiffOn I 1 γ a b)

/-- An extension of an interval field to the whole parameter line with a piecewise `C¹` lift,
chosen once and for all. -/
private def extension (U : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    ∀ t, TangentSpace I (γ t) :=
  U.exists_extension.choose

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem isPiecewiseContMDiffOn_extension
    (U : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    IsPiecewiseContMDiffOn I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (extension hγ U r)) a b :=
  U.exists_extension.choose_spec.1

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem extension_apply
    (U : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) (t : Icc a b) :
    extension hγ U t = U.val t :=
  U.exists_extension.choose_spec.2 t

/-- The index form of the chosen extensions agrees with that of any extensions. -/
private theorem indexForm_extension_eq
    {U W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ}
    {P Q : ∀ t, TangentSpace I (γ t)}
    (hP : ∀ t : Icc a b, P t = U.val t) (hQ : ∀ t : Icc a b, Q t = W.val t) :
    indexForm I γ (extension hγ U) (extension hγ W) a b = indexForm I γ P Q a b := by
  have hIoo : uIoo a b ⊆ Icc a b := by
    rw [uIoo_of_le hγ.lt.le]
    exact Ioo_subset_Icc_self
  exact indexForm_congr (fun _ _ ↦ rfl)
    (fun t ht ↦ heq_of_eq ((extension_apply hγ U ⟨t, hIoo ht⟩).trans (hP ⟨t, hIoo ht⟩).symm))
    (fun t ht ↦ heq_of_eq ((extension_apply hγ W ⟨t, hIoo ht⟩).trans (hQ ⟨t, hIoo ht⟩).symm))

private theorem indexForm_extension_add_left
    (U U' W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    indexForm I γ (extension hγ (U + U')) (extension hγ W) a b =
      indexForm I γ (extension hγ U) (extension hγ W) a b +
        indexForm I γ (extension hγ U') (extension hγ W) a b := by
  rw [indexForm_extension_eq hγ (P := extension hγ U + extension hγ U') (Q := extension hγ W)
    (fun t ↦ by simp [extension_apply]) (extension_apply hγ W)]
  exact indexForm_add_left_of_isPiecewiseContMDiffOn (isPiecewiseContMDiffOn_extension hγ U)
    (isPiecewiseContMDiffOn_extension hγ U') (isPiecewiseContMDiffOn_extension hγ W)

private theorem indexForm_extension_smul_left (c : ℝ)
    (U W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    indexForm I γ (extension hγ (c • U)) (extension hγ W) a b =
      c * indexForm I γ (extension hγ U) (extension hγ W) a b := by
  rw [indexForm_extension_eq hγ (P := c • extension hγ U) (Q := extension hγ W)
    (fun t ↦ by simp [extension_apply]) (extension_apply hγ W), indexForm_const_smul_left]

/-- **The index form on piecewise smooth fields.** For a piecewise `C¹` curve `γ` on `[a, b]`,
the bilinear form `I(V, W) = ∫_a^b ⟪D_t V, D_t W⟫ - ⟪R(V, γ') γ', W⟫ dt` on the real vector space of
continuous piecewise `C¹` tangent fields along `γ` on `[a, b]`. It is computed on any extensions
of the fields to the whole parameter line (`TauCeti.Manifold.indexBilinForm_apply`). -/
def indexBilinForm :
    LinearMap.BilinForm ℝ (PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :=
  LinearMap.mk₂ ℝ (fun U W ↦ indexForm I γ (extension hγ U) (extension hγ W) a b)
    (indexForm_extension_add_left hγ) (indexForm_extension_smul_left hγ)
    (fun U W W' ↦ by
      simp only [indexForm_comm (V := extension hγ U)]
      exact indexForm_extension_add_left hγ W W' U)
    (fun c U W ↦ by
      simp only [indexForm_comm (V := extension hγ U)]
      exact indexForm_extension_smul_left hγ c W U)

variable {hγ}

/-- The index form of two piecewise smooth fields is the index form of any of their extensions
to the whole parameter line. -/
theorem indexBilinForm_apply
    {U W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ}
    {P Q : ∀ t, TangentSpace I (γ t)}
    (hP : ∀ t : Icc a b, P t = U.val t) (hQ : ∀ t : Icc a b, Q t = W.val t) :
    indexBilinForm hγ U W = indexForm I γ P Q a b :=
  indexForm_extension_eq hγ hP hQ

/-- The index form of fields given by piecewise smooth fields on the whole parameter line. -/
@[simp]
theorem indexBilinForm_ofPiecewise {P Q : ∀ t, TangentSpace I (γ t)}
    (hP : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (P r)) a b)
    (hQ : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (Q r)) a b) :
    indexBilinForm hγ (.ofPiecewise P hP) (.ofPiecewise Q hQ) = indexForm I γ P Q a b :=
  indexBilinForm_apply (fun _ ↦ (PiecewiseContMDiffSectionAlong.ofPiecewise_apply P hP _).symm)
    (fun _ ↦ (PiecewiseContMDiffSectionAlong.ofPiecewise_apply Q hQ _).symm)

/-- The index form on piecewise smooth fields is symmetric. -/
theorem indexBilinForm_isSymm : (indexBilinForm hγ).IsSymm :=
  ⟨fun U W ↦ by
    rw [indexBilinForm_apply (extension_apply hγ U) (extension_apply hγ W),
      indexBilinForm_apply (extension_apply hγ W) (extension_apply hγ U), indexForm_comm]⟩

/-- The index form on piecewise smooth fields is additive over the two sides of an interior
parameter `c`, on the restrictions of the fields to `[a, c]` and `[c, b]`. -/
theorem indexBilinForm_add_adjacent_intervals {c : ℝ} (hac : a < c) (hcb : c < b)
    (U W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    indexBilinForm (hγ.mono le_rfl hac hcb.le)
        (PiecewiseContMDiffSectionAlong.restrict le_rfl hac hcb.le U)
        (PiecewiseContMDiffSectionAlong.restrict le_rfl hac hcb.le W) +
      indexBilinForm (hγ.mono hac.le hcb le_rfl)
        (PiecewiseContMDiffSectionAlong.restrict hac.le hcb le_rfl U)
        (PiecewiseContMDiffSectionAlong.restrict hac.le hcb le_rfl W) =
      indexBilinForm hγ U W := by
  obtain ⟨P, hP, hPU⟩ := U.exists_extension
  obtain ⟨Q, hQ, hQW⟩ := W.exists_extension
  have h₁ : indexBilinForm (hγ.mono le_rfl hac hcb.le)
      (PiecewiseContMDiffSectionAlong.restrict le_rfl hac hcb.le U)
      (PiecewiseContMDiffSectionAlong.restrict le_rfl hac hcb.le W) = indexForm I γ P Q a c :=
    indexBilinForm_apply
      (fun t ↦ by rw [PiecewiseContMDiffSectionAlong.restrict_apply]; exact hPU ⟨t, _⟩)
      (fun t ↦ by rw [PiecewiseContMDiffSectionAlong.restrict_apply]; exact hQW ⟨t, _⟩)
  have h₂ : indexBilinForm (hγ.mono hac.le hcb le_rfl)
      (PiecewiseContMDiffSectionAlong.restrict hac.le hcb le_rfl U)
      (PiecewiseContMDiffSectionAlong.restrict hac.le hcb le_rfl W) = indexForm I γ P Q c b :=
    indexBilinForm_apply
      (fun t ↦ by rw [PiecewiseContMDiffSectionAlong.restrict_apply]; exact hPU ⟨t, _⟩)
      (fun t ↦ by rw [PiecewiseContMDiffSectionAlong.restrict_apply]; exact hQW ⟨t, _⟩)
  rw [h₁, h₂, indexBilinForm_apply hPU hQW]
  exact indexForm_add_adjacent_intervals
    (intervalIntegrable_indexFormIntegrand_of_isPiecewiseContMDiffOn
      (hP.mono le_rfl hac hcb.le) (hQ.mono le_rfl hac hcb.le))
    (intervalIntegrable_indexFormIntegrand_of_isPiecewiseContMDiffOn
      (hP.mono hac.le hcb le_rfl) (hQ.mono hac.le hcb le_rfl))

/-- **Jacobi integration by parts on piecewise smooth fields.** If the piecewise smooth field `U`
is given on `[a, b]` by a Jacobi field `V` on a set containing `[a, b]`, then for every piecewise
smooth field `W`, `I(U, W) = ⟪D_t V(b), W(b)⟫ - ⟪D_t V(a), W(a)⟫`. -/
theorem IsJacobiFieldOn.indexBilinForm_eq_inner_sub_inner (h : IsJacobiFieldOn I γ V s)
    (hsub : Icc a b ⊆ s) {U : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ}
    (hU : ∀ t : Icc a b, V t = U.val t)
    (W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ) :
    indexBilinForm hγ U W =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b)
          (W.val ⟨b, hγ.lt.le, le_rfl⟩) -
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a)
          (W.val ⟨a, le_rfl, hγ.lt.le⟩) := by
  obtain ⟨Q, hQ, hQW⟩ := W.exists_extension
  rw [indexBilinForm_apply hU hQW,
    h.indexForm_eq_inner_sub_inner_of_isPiecewiseContMDiffOn hQ hsub]
  simp only [← hQW]

/-- **Jacobi fields are orthogonal to the fixed-endpoint fields.** If the piecewise smooth field
`U` is given on `[a, b]` by a Jacobi field on a set containing `[a, b]`, then `I(U, W) = 0` for
every piecewise smooth field `W` vanishing at `a` and `b`. -/
theorem IsJacobiFieldOn.indexBilinForm_eq_zero_of_mem_endpointZero (h : IsJacobiFieldOn I γ V s)
    (hsub : Icc a b ⊆ s) {U W : PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ}
    (hU : ∀ t : Icc a b, V t = U.val t) (hW : W ∈ PiecewiseContMDiffSectionAlong.endpointZero) :
    indexBilinForm hγ U W = 0 := by
  rw [PiecewiseContMDiffSectionAlong.mem_endpointZero_iff] at hW
  rw [h.indexBilinForm_eq_inner_sub_inner hsub hU, hW.1, hW.2, inner_zero_right,
    inner_zero_right, sub_zero]

end Bundled

end TauCeti.Manifold
