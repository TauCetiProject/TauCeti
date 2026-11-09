/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Change of variables in local Sobolev classes on planar sets

Let `Φ` be a `C¹` map on an open set `Ω ⊆ ℂ`, injective with invertible derivative on a set
`U ⊆ Ω` and mapping `U` into `V`. Precomposition with `Φ` preserves the local classes
`TauCeti.MemWkpLoc p U k` of orders `k ≤ 1`, for arbitrary sets `U` and `V` reaching their
boundary provided `Φ` maps `interior U` into `interior V`. On each compact subset of `U` the
derivative of `Φ` is bounded and its Jacobian is bounded below
(`MeasureTheory.exists_det_bounds_of_isCompact`), which controls the local `Lᵖ` norms of `u ∘ Φ`
and of its weak derivative `Du(Φ z) ∘ DΦ(z)` (`MeasureTheory.MemLp.comp_restrict_of_isCompact`,
`MeasureTheory.MemLp.comp_fderiv_restrict_of_isCompact`); the weak derivative itself comes from
the chain rule `TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo` on `interior U`.

In particular a `C¹` diffeomorphism preserving the real axis and the upper half-plane preserves
the half-disc classes. For real-affine maps `z ↦ A z + b` every order is preserved: the
derivative of `u (A z + b)` is `Du (A z + b) ∘ A`, and induction places `A` in each slot of the
higher derivatives. The dilation `z ↦ 2 z` scales the first derivative by `2`, the reflection
`z ↦ -conj z` preserves the half-disc classes, and the rotation `z ↦ I z` does not preserve the
real axis.

Higher orders for nonlinear `Φ` need the multiplication of local Sobolev maps by smooth
coefficients and are not treated here.

## Main declarations

* `TauCeti.MemLpLoc.comp_contDiffOn_diffeo`, `TauCeti.MemLpLoc.comp_fderiv_contDiffOn_diffeo`:
  invariance of local `Lᵖ` membership.
* `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo`: invariance of the local classes of order at most one.
* `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo_halfPlane`: the half-disc version.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`: invariance of every order under real-affine
  maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ComplexConjugate

namespace TauCeti

/-! ### Local Sobolev classes on planar sets -/

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ENNReal} {Φ : ℂ → ℂ} {Ω U V : Set ℂ} {k : ℕ}

omit [NormedSpace ℝ F] in
/-- Precomposition with a map that is `C¹` on an open set containing `U`, injective with invertible
derivative on `U` and mapping `U` into `V`, preserves local `Lᵖ` membership. -/
theorem MemLpLoc.comp_contDiffOn_diffeo {u : ℂ → F} (hu : MemLpLoc p V u) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ U) (hdet : ∀ z ∈ U, (fderiv ℝ Φ z).det ≠ 0)
    (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V) : MemLpLoc p U (fun z => u (Φ z)) :=
  memLpLoc_iff.2 fun _ hKU hK =>
    (memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset) (hK.image_of_continuousOn
      (hΦ.continuousOn.mono (hKU.trans hUΩ)))).comp_restrict_of_isCompact hΩ hΦ (hinj.mono hKU)
        (fun z hz => hdet z (hKU hz)) hK (hKU.trans hUΩ)

/-- The transformed derivative `z ↦ D(Φ z) ∘ DΦ(z)` of a locally `Lᵖ` field `D` is locally `Lᵖ`,
under the hypotheses of `TauCeti.MemLpLoc.comp_contDiffOn_diffeo`. -/
theorem MemLpLoc.comp_fderiv_contDiffOn_diffeo {D : ℂ → ℂ →L[ℝ] F} (hD : MemLpLoc p V D)
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ U)
    (hdet : ∀ z ∈ U, (fderiv ℝ Φ z).det ≠ 0) (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V) :
    MemLpLoc p U (fun z => (D (Φ z)).comp (fderiv ℝ Φ z)) :=
  memLpLoc_iff.2 fun _ hKU hK =>
    (memLpLoc_iff.1 hD _ ((image_mono hKU).trans hmaps.image_subset) (hK.image_of_continuousOn
      (hΦ.continuousOn.mono (hKU.trans hUΩ)))).comp_fderiv_restrict_of_isCompact hΩ hΦ
        (hinj.mono hKU) (fun z hz => hdet z (hKU hz)) hK (hKU.trans hUΩ)

/-- **Change of variables in local Sobolev classes of order at most one.** Let `Φ` be `C¹` on an
open set `Ω ⊇ U`, injective with invertible derivative on `U`, mapping `U` into `V` and
`interior U` into `interior V`. Then precomposition with `Φ` maps `MemWkpLoc p V k` into
`MemWkpLoc p U k` for `k ≤ 1`. The sets `U` and `V` may reach their boundaries, as half-discs do.
The weak derivative of `u ∘ Φ` is `Du(Φ z) ∘ DΦ(z)`
(`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`) and its local `Lᵖ` norms are controlled by
`MeasureTheory.eLpNorm_comp_fderiv_restrict_le`. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo {u : ℂ → F} (hk : k ≤ 1) (hu : MemWkpLoc p V k u)
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω) (hinj : InjOn Φ U)
    (hdet : ∀ z ∈ U, (fderiv ℝ Φ z).det ≠ 0) (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V)
    (hint : MapsTo Φ (interior U) (interior V)) : MemWkpLoc p U k (fun z => u (Φ z)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLoc_zero_iff.2
      (MemLpLoc.comp_contDiffOn_diffeo (memWkpLoc_zero_iff.1 hu) hΩ hΦ hinj hdet hUΩ hmaps)
  · obtain ⟨hLp, D, hD, hD0⟩ := memWkpLoc_succ_iff.1 hu
    refine memWkpLoc_succ_iff.2 ⟨hLp.comp_contDiffOn_diffeo hΩ hΦ hinj hdet hUΩ hmaps, _, ?_,
      memWkpLoc_zero_iff.2 (MemLpLoc.comp_fderiv_contDiffOn_diffeo (memWkpLoc_zero_iff.1 hD0)
        hΩ hΦ hinj hdet hUΩ hmaps)⟩
    exact hD.comp_contDiffOn_diffeo (hΦ.mono (interior_subset.trans hUΩ))
      (hinj.mono interior_subset) (fun z hz => hdet z (interior_subset hz)) (by simpa using hint)

/-- **Change of variables between open planar domains.** For open `U` and `V`, a `C¹` map
injective with invertible derivative on `U` and mapping `U` into `V` preserves the local classes
of order at most one. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo_of_isOpen {U V : Opens ℂ} {u : ℂ → F} (hk : k ≤ 1)
    (hu : MemWkpLoc p V k u) (hΦ : ContDiffOn ℝ 1 Φ U) (hinj : InjOn Φ U)
    (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0) (hmaps : MapsTo Φ U V) :
    MemWkpLoc p U k (fun z => u (Φ z)) :=
  hu.comp_contDiffOn_diffeo hk U.isOpen hΦ hinj hdet subset_rfl hmaps
    (by simpa only [U.isOpen.interior_eq, V.isOpen.interior_eq] using hmaps)

/-- **Change of variables on half-discs.** Let `Φ` be `C¹` and injective with invertible
derivative on an open set `U'`, mapping `U'` into an open set `V'`, the real axis into itself and
the upper half-plane into itself. Then precomposition with `Φ` maps the half-disc class
`MemWkpLoc p (V' ∩ {0 ≤ im}) k` into `MemWkpLoc p (U' ∩ {0 ≤ im}) k` for `k ≤ 1`. -/
theorem MemWkpLoc.comp_contDiffOn_diffeo_halfPlane {U' V' : Set ℂ} {u : ℂ → F} (hk : k ≤ 1)
    (hu : MemWkpLoc p (V' ∩ {z | 0 ≤ z.im}) k u) (hU' : IsOpen U') (hV' : IsOpen V')
    (hΦ : ContDiffOn ℝ 1 Φ U') (hinj : InjOn Φ U') (hdet : ∀ z ∈ U', (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ U' V') (hreal : ∀ z ∈ U', z.im = 0 → (Φ z).im = 0)
    (hupper : ∀ z ∈ U', 0 < z.im → 0 < (Φ z).im) :
    MemWkpLoc p (U' ∩ {z | 0 ≤ z.im}) k (fun z => u (Φ z)) := by
  have hint : ∀ W : Set ℂ, IsOpen W → interior (W ∩ {z | 0 ≤ z.im}) = W ∩ {z | 0 < z.im} :=
    fun W hW => by rw [interior_inter, hW.interior_eq, Complex.interior_setOfPred_le_im]
  refine hu.comp_contDiffOn_diffeo hk hU' hΦ (hinj.mono inter_subset_left)
    (fun z hz => hdet z hz.1) inter_subset_left ?_ ?_
  · rintro z ⟨hzU, hz⟩
    rw [mem_ofPred_eq] at hz
    refine ⟨hmaps hzU, ?_⟩
    rcases hz.lt_or_eq with h | h
    · exact (hupper z hzU h).le
    · exact (hreal z hzU h.symm).ge
  · rw [hint U' hU', hint V' hV']
    exact fun z ⟨hzU, hz⟩ => ⟨hmaps hzU, hupper z hzU hz⟩

/-- **Real-affine changes of variables preserve every order.** For `A : ℂ ≃L[ℝ] ℂ`, `b : ℂ` and
`z ↦ A z + b` mapping `U` into `V`, precomposition maps `MemWkpLoc p V k` into
`MemWkpLoc p U k`. The weak derivative of `u (A z + b)` is `Du (A z + b) ∘ A`, so the `i`-th
derivative is the `i`-th derivative of `u` at `A z + b` with `A` applied in each slot. -/
theorem MemWkpLoc.comp_continuousLinearEquiv_add {u : ℂ → F} (hu : MemWkpLoc p V k u)
    (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) (hmaps : MapsTo (fun z => A z + b) U V) :
    MemWkpLoc p U k (fun z => u (A z + b)) := by
  set Φ : ℂ → ℂ := fun z => A z + b
  have hΦ : ContDiffOn ℝ 1 Φ univ := (A.contDiff.add contDiff_const).contDiffOn
  have hinj : InjOn Φ U := ((add_left_injective b).comp A.injective).injOn
  have hdet : ∀ z ∈ U, (fderiv ℝ Φ z).det ≠ 0 := fun z _ => A.det_fderiv_add_const_ne_zero b z
  -- `Φ` is a homeomorphism, so it maps `interior U` into `interior V`.
  have hint : MapsTo Φ (interior U) (interior V) := by
    have hh := (A.toHomeomorph.trans (Homeomorph.addRight b)).image_interior U
    intro z hz
    have : Φ z ∈ interior (Φ '' U) := hh ▸ ⟨z, hz, rfl⟩
    exact interior_mono hmaps.image_subset this
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 (MemLpLoc.comp_contDiffOn_diffeo
      (memWkpLoc_zero_iff.1 hu) isOpen_univ hΦ hinj hdet (subset_univ _) hmaps)
  | succ k ih =>
    obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    refine memWkpLoc_succ_iff.2
      ⟨hLp.comp_contDiffOn_diffeo isOpen_univ hΦ hinj hdet (subset_univ _) hmaps,
      fun z => ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (A : ℂ →L[ℝ] ℂ)) (D (Φ z)), ?_,
      (ih hk).clm_comp _⟩
    exact hD.comp_continuousLinearEquiv_add (U := Opens.interior U) A b (by simpa using hint)

/-! ### Checks -/

/-- The dilation `z ↦ 2 z` carries `MemWkpLoc p (ball 0 2) k` to `MemWkpLoc p (ball 0 1) k`. -/
theorem memWkpLoc_ball_one_comp_two_mul {u : ℂ → F}
    (hu : MemWkpLoc p (Metric.ball 0 2) k u) :
    MemWkpLoc p (Metric.ball 0 1) k (fun z => u (2 * z)) := by
  convert hu.comp_continuousLinearEquiv_add
    (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv 0 ?_ using 2 with z
  · simp [Complex.real_smul]
  · intro z hz
    simp only [Metric.mem_ball, dist_zero_right, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.smulOfNeZero_apply, add_zero, norm_smul, Real.norm_ofNat] at hz ⊢
    linarith

/-- The dilation `z ↦ 2 z` scales the first weak derivative by `2`: if `Du` is a weak derivative
of `u` on `ball 0 2`, then `z ↦ 2 • Du (2 z)` is a weak derivative of `z ↦ u (2 z)` on
`ball 0 1`. -/
theorem HasWeakFDerivOn.ball_one_comp_two_mul {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ⟨Metric.ball 0 2, Metric.isOpen_ball⟩ u Du) :
    HasWeakFDerivOn volume ⟨Metric.ball 0 1, Metric.isOpen_ball⟩ (fun z => u (2 * z))
      (fun z => (2 : ℝ) • Du (2 * z)) := by
  set A : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv
  have hA : ∀ z, A z = 2 * z := fun z => by simp [A, Complex.real_smul]
  have h := hu.comp_continuousLinearEquiv_add (U := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩) A 0
    (fun z hz => by
      simp only [SetLike.mem_coe, Opens.mem_mk, Metric.mem_ball, dist_zero_right, hA, add_zero,
        norm_mul, Complex.norm_ofNat] at hz ⊢
      linarith)
  convert h using 2 with z
  · simp [hA]
  · ext v
    simp [hA, Complex.real_smul, ← map_smul]

/-- Complex conjugation preserves every local Sobolev class on sets it maps into one another. -/
theorem memWkpLoc_comp_conj {u : ℂ → F} (hu : MemWkpLoc p V k u)
    (hmaps : MapsTo (conj ·) U V) : MemWkpLoc p U k (fun z => u (conj z)) := by
  simpa using hu.comp_continuousLinearEquiv_add Complex.conjCLE 0 (by simpa using hmaps)

/-- Complex conjugation maps the real axis into itself. -/
theorem mapsTo_conj_setOf_im_eq_zero :
    MapsTo (conj ·) {z : ℂ | z.im = 0} {z : ℂ | z.im = 0} := fun z hz => by
  simpa using hz

/-- The reflection `z ↦ -conj z` across the imaginary axis preserves the real axis and the upper
half-plane, hence the half-disc classes on the unit half-disc, at every order. -/
theorem memWkpLoc_halfDisc_comp_neg_conj {u : ℂ → F}
    (hu : MemWkpLoc p (Metric.ball 0 1 ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p (Metric.ball 0 1 ∩ {z | 0 ≤ z.im}) k (fun z => u (-conj z)) := by
  simpa using hu.comp_continuousLinearEquiv_add (Complex.conjCLE.trans
    (ContinuousLinearEquiv.neg ℝ)) 0 (fun z hz => by simpa using hz)

/-- The rotation `z ↦ I z` does not preserve the real axis, so it is not admissible on
half-discs. -/
theorem not_mapsTo_I_mul_setOf_im_eq_zero :
    ¬ MapsTo (fun z : ℂ => Complex.I * z) {z | z.im = 0} {z | z.im = 0} := fun h => by
  simpa using h (show (1 : ℂ) ∈ {z : ℂ | z.im = 0} by simp)

end Planar

end TauCeti
