/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Calculus.FDeriv.ClosedCover
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Topology.ContinuousOn.ClosedCover

/-!
# Even reflection across the real axis

The even reflection `TauCeti.evenReflection w` of a function `w : ℂ → F` agrees with `w` on the
closed upper half-plane `0 ≤ im z` and with `w ∘ conj` on the lower one. It is the standard way
to turn a boundary problem on a half-disc centred on the real axis into an interior problem on
the whole disc.

The even reflection of a `C²` function is in general only Lipschitz across the real axis. It is
`C²` exactly when the odd-order normal derivatives match, and for a function that is `C²` up to
the axis this is the *Neumann condition* `∂ₜ w = 0` on the axis: the first normal derivative
changes sign under reflection, the second does not, and the mixed derivative `∂ₛ ∂ₜ w` vanishes
on the axis because `∂ₜ w` does. So if `w` is `C²` on `{0 ≤ im z} ∩ U`, for an open set `U`
invariant under conjugation, and `∂ₜ w = 0` on `U ∩ ℝ`, then `evenReflection w` is `C²` on `U`
(`TauCeti.contDiffOn_evenReflection`). Its Laplacian is that of `w` above the axis and that of `w`
at the mirror point below it, because conjugation is an isometry.

This is the reflection step in the boundary regularity theory of `J`-holomorphic curves with
totally real boundary conditions. For a suitable metric the energy density of such a curve
satisfies the Neumann condition on the boundary, and its even reflection reduces the boundary
mean-value inequality to the interior one
(`TauCeti.Analysis.InnerProductSpace.Laplacian.BoundaryMeanValueInequality`).

## Main definitions

* `TauCeti.evenReflection w`: the function `z ↦ w (re z + i |im z|)`.

## Main results

* `TauCeti.evenReflection_of_nonneg`, `TauCeti.evenReflection_of_nonpos`: the reflection is `w`
  on the closed upper half-plane and `w ∘ conj` on the closed lower half-plane.
* `TauCeti.continuousOn_evenReflection`: the reflection of a function continuous up to the axis
  is continuous.
* `TauCeti.contDiffOn_evenReflection`: the reflection of a function that is `C²` up to the axis
  and satisfies the Neumann condition there is `C²`.
* `TauCeti.laplacian_evenReflection_of_pos`, `TauCeti.laplacian_evenReflection_of_neg`: the
  Laplacian of the reflection off the axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the boundary version of the mean-value
  inequality, proved by reflecting the energy density).
-/

public section

namespace TauCeti

open Complex ComplexConjugate Filter InnerProductSpace Laplacian Set Topology

variable {F : Type*} {w : ℂ → F} {z : ℂ}

/-- The even reflection of `w : ℂ → F` across the real axis: `w` on the closed upper half-plane
and `w ∘ conj` on the lower half-plane, written as the single formula `w (re z + i |im z|)`. -/
def evenReflection (w : ℂ → F) (z : ℂ) : F :=
  w ⟨z.re, |z.im|⟩

/-- On the closed upper half-plane the even reflection of `w` is `w`. -/
@[simp]
theorem evenReflection_of_nonneg (hz : 0 ≤ z.im) : evenReflection w z = w z := by
  simp [evenReflection, abs_of_nonneg hz]

/-- On the closed lower half-plane the even reflection of `w` is `w ∘ conj`. -/
@[simp]
theorem evenReflection_of_nonpos (hz : z.im ≤ 0) : evenReflection w z = w (conj z) := by
  rw [evenReflection, abs_of_nonpos hz]
  congr 1

/-- The even reflection is invariant under conjugation. -/
@[simp]
theorem evenReflection_conj : evenReflection w (conj z) = evenReflection w z := by
  simp [evenReflection]

/-- The even reflection of a function continuous up to the real axis is continuous, on any set
invariant under conjugation. -/
theorem continuousOn_evenReflection [TopologicalSpace F] {s : Set ℂ} (hs : ∀ z ∈ s, conj z ∈ s)
    (hw : ContinuousOn w ({z | 0 ≤ z.im} ∩ s)) : ContinuousOn (evenReflection w) s := by
  have hfold : Continuous fun z : ℂ ↦ (⟨z.re, |z.im|⟩ : ℂ) :=
    equivRealProdCLM.symm.continuous.comp (by fun_prop : Continuous fun z : ℂ ↦ (z.re, |z.im|))
  refine hw.comp hfold.continuousOn fun z hz ↦ ⟨abs_nonneg z.im, ?_⟩
  rcases le_total 0 z.im with h | h
  · simpa [abs_of_nonneg h] using hz
  · convert hs z hz using 1
    apply Complex.ext <;> simp [abs_of_nonpos h]

/-! ### `C²` regularity of the even reflection -/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition with conjugation, `L ↦ L ∘ conj`, on real-linear maps out of `ℂ`. -/
private noncomputable abbrev conjPrecomp (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (conjCLE : ℂ →L[ℝ] ℂ)

private theorem conjPrecomp_apply (L : ℂ →L[ℝ] F) (v : ℂ) : conjPrecomp F L v = L (conj v) := by
  simp [conjPrecomp]

/-- **`C²` regularity of the even reflection.** Let `U` be an open set invariant under
conjugation, and let `w` be `C²` on `{0 ≤ im z} ∩ U`, up to the real axis, with vanishing normal
derivative `∂ₜ w = 0` at the points of `U` on the axis. Then the even reflection of `w` is `C²`
on `U`. -/
theorem contDiffOn_evenReflection {U : Set ℂ} (hU : IsOpen U) (hUc : ∀ z ∈ U, conj z ∈ U)
    (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ U))
    (hN : ∀ x ∈ U, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U) x I = 0) :
    ContDiffOn ℝ 2 (evenReflection w) U := by
  -- Write `D₁`, `D₂` for the one-sided first and second derivatives of `w`. The derivatives of
  -- the reflection are `D₁`, `D₂` above the axis and their conjugates below it; we show that the
  -- two descriptions agree on the axis, then glue.
  set S := {z : ℂ | 0 ≤ z.im} ∩ U
  set D₁ := fderivWithin ℝ w S
  set D₂ := fderivWithin ℝ D₁ S
  have hS : UniqueDiffOn ℝ S :=
    (uniqueDiffOn_convex (convex_halfSpace_im_ge 0)
      ⟨I, by rw [interior_setOfPred_le_im]; simp⟩).inter hU
  have hD₁ : ContDiffOn ℝ 1 D₁ S := hw.fderivWithin hS (by norm_num)
  have hD₂ : ContinuousOn D₂ S := hD₁.continuousOn_fderivWithin hS le_rfl
  have hwS : ∀ z ∈ S, HasFDerivWithinAt w (D₁ z) S z := fun z hz ↦
    ((hw.differentiableOn (by norm_num)) z hz).hasFDerivWithinAt
  have hD₁S : ∀ z ∈ S, HasFDerivWithinAt D₁ (D₂ z) S z := fun z hz ↦
    ((hD₁.differentiableOn (by norm_num)) z hz).hasFDerivWithinAt
  have hconjS : ∀ z ∈ U, z.im ≤ 0 → conj z ∈ S := fun z hz hz' ↦
    ⟨by simpa using hz', hUc z hz⟩
  have hmaps : MapsTo conj ({z : ℂ | z.im ≤ 0} ∩ U) S := fun z hz ↦ hconjS z hz.2 hz.1
  have hupper : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hlower : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_le continuous_im continuous_const
  have hcover : {z : ℂ | 0 ≤ z.im} ∪ {z | z.im ≤ 0} = univ :=
    eq_univ_of_forall fun z ↦ le_total 0 z.im
  -- On the axis, precomposing the first two derivatives with `conj` changes nothing.
  have hedge₁ : ∀ x ∈ U, x.im = 0 → conjPrecomp F (D₁ x) = D₁ x := fun x hx hx0 ↦ by
    ext v
    rw [conjPrecomp_apply]
    exact (D₁ x).toLinearMap.apply_conj_of_apply_I_eq_zero (hN x hx hx0) v
  have hedge₂ : ∀ x ∈ U, x.im = 0 →
      (conjPrecomp F).comp ((D₂ x).comp (conjCLE : ℂ →L[ℝ] ℂ)) = D₂ x := by
    intro x hx hx0
    have hxS : x ∈ S := ⟨hx0.ge, hx⟩
    -- The mixed derivative `∂ₛ ∂ₜ w` vanishes along the axis, where `∂ₜ w` does.
    have hmixed : D₂ x 1 I = 0 := by
      have hU' : ∀ᶠ t : ℝ in 𝓝 0, x + t • (1 : ℂ) ∈ U :=
        (Continuous.tendsto' (by fun_prop) 0 x (by simp)).eventually (hU.mem_nhds hx)
      have hline := (((ContinuousLinearMap.apply ℝ F I).hasFDerivAt.comp_hasFDerivWithinAt x
        (hD₁S x hxS)).hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt'
          (hU'.mono fun t ht ↦ ⟨by simp [hx0], ht⟩)
      refine hline.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq ?_)
      filter_upwards [hU'] with t ht
      exact hN _ ht (by simp [hx0])
    have hcl : x ∈ closure (interior S) := by
      rw [interior_inter, hU.interior_eq, interior_setOfPred_le_im, inter_comm]
      exact hU.inter_closure ⟨hx, by rw [closure_setOfPred_lt_im]; exact hx0.ge⟩
    have hsymm : D₂ x I 1 = D₂ x 1 I :=
      (hw x hxS).isSymmSndFDerivWithinAt (by simp) hS hcl hxS I 1
    ext v e
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
      conjPrecomp_apply]
    exact (D₂ x).toLinearMap₁₂.apply_conj_apply_conj_of_apply_one_I_eq_zero_of_apply_I_one_eq_zero
      hmixed (hsymm.trans hmixed) v e
  -- The first and second derivatives of the reflection, glued along the axis.
  let G₁ : ℂ → ℂ →L[ℝ] F := fun z ↦ if 0 ≤ z.im then D₁ z else conjPrecomp F (D₁ (conj z))
  let G₂ : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] F := fun z ↦
    if 0 ≤ z.im then D₂ z else (conjPrecomp F).comp ((D₂ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))
  have hG₁_lower : ∀ z ∈ U, z.im ≤ 0 → G₁ z = conjPrecomp F (D₁ (conj z)) := by
    intro z hz hz'
    by_cases h : 0 ≤ z.im
    · have h0 : z.im = 0 := le_antisymm hz' h
      simp only [G₁, ite_eq_left h, (conj_eq_iff_im.2 h0), hedge₁ z hz h0]
    · simp only [G₁, ite_eq_right h]
  have hG₂_lower : ∀ z ∈ U, z.im ≤ 0 →
      G₂ z = (conjPrecomp F).comp ((D₂ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ)) := by
    intro z hz hz'
    by_cases h : 0 ≤ z.im
    · have h0 : z.im = 0 := le_antisymm hz' h
      simp only [G₂, ite_eq_left h, (conj_eq_iff_im.2 h0), hedge₂ z hz h0]
    · simp only [G₂, ite_eq_right h]
  -- Derivatives within the two closed half-planes.
  have hlower₁ : ∀ z ∈ U, z.im ≤ 0 → HasFDerivWithinAt (fun z ↦ w (conj z))
      (conjPrecomp F (D₁ (conj z))) {z | z.im ≤ 0} z := by
    intro z hz hz'
    rw [← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
    have heq : conjPrecomp F (D₁ (conj z)) = (D₁ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ) := by
      ext v
      simp
    rw [heq]
    exact (hwS (conj z) (hconjS z hz hz')).comp z (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivWithinAt hmaps
  have hlower₂ : ∀ z ∈ U, z.im ≤ 0 → HasFDerivWithinAt (fun z ↦ conjPrecomp F (D₁ (conj z)))
      ((conjPrecomp F).comp ((D₂ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))) {z | z.im ≤ 0} z := by
    intro z hz hz'
    rw [← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
    exact (conjPrecomp F).hasFDerivAt.comp_hasFDerivWithinAt z
      ((hD₁S (conj z) (hconjS z hz hz')).comp z (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivWithinAt hmaps)
  have hderiv₁ : ∀ z ∈ U, HasFDerivAt (evenReflection w) (G₁ z) z := by
    intro z hz
    refine hasFDerivAt_of_isClosed_of_union_eq_univ hupper hlower hcover
      (fun (hz' : 0 ≤ z.im) ↦ ?_) fun (hz' : z.im ≤ 0) ↦ ?_
    · refine (((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hwS z ⟨hz', hz⟩)).congr
        (fun y hy ↦ evenReflection_of_nonneg hy) (evenReflection_of_nonneg hz')).congr_fderiv ?_
      simp only [G₁, ite_eq_left hz']
    · rw [hG₁_lower z hz hz']
      exact (hlower₁ z hz hz').congr (fun y hy ↦ evenReflection_of_nonpos hy)
        (evenReflection_of_nonpos hz')
  have hderiv₂ : ∀ z ∈ U, HasFDerivAt G₁ (G₂ z) z := by
    intro z hz
    refine hasFDerivAt_of_isClosed_of_union_eq_univ hupper hlower hcover
      (fun (hz' : 0 ≤ z.im) ↦ ?_) fun (hz' : z.im ≤ 0) ↦ ?_
    · refine (((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hD₁S z ⟨hz', hz⟩)).congr
        (fun y hy ↦ ite_eq_left hy) (ite_eq_left hz')).congr_fderiv ?_
      simp only [G₂, ite_eq_left hz']
    · rw [hG₂_lower z hz hz', ← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
      refine ((hasFDerivWithinAt_inter (hU.mem_nhds hz)).2 (hlower₂ z hz hz')).congr
        (fun y hy ↦ hG₁_lower y hy.2 hy.1) (hG₁_lower z hz hz')
  have hcont₂ : ContinuousOn G₂ U := by
    intro z hz
    refine (continuousAt_of_isClosed_of_union_eq_univ (f := G₂) hupper hlower hcover
      (fun (hz' : 0 ≤ z.im) ↦ ?_) fun (hz' : z.im ≤ 0) ↦ ?_).continuousWithinAt
    · rw [← continuousWithinAt_inter (hU.mem_nhds hz)]
      refine (hD₂ z ⟨hz', hz⟩).congr
        (fun y hy ↦ ite_eq_left hy.1) (ite_eq_left hz')
    · rw [← continuousWithinAt_inter (hU.mem_nhds hz)]
      have hc : ContinuousWithinAt (fun y ↦ D₂ (conj y)) ({z : ℂ | z.im ≤ 0} ∩ U) z :=
        (hD₂ (conj z) (hconjS z hz hz')).comp continuous_conj.continuousWithinAt hmaps
      have hΦ : Continuous fun B : ℂ →L[ℝ] ℂ →L[ℝ] F ↦
          (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ)) := by
        fun_prop
      refine (hΦ.continuousAt.comp_continuousWithinAt hc).congr
        (fun y hy ↦ hG₂_lower y hy.2 hy.1) (hG₂_lower z hz hz')
  have hG₁ : ContDiffOn ℝ 1 G₁ U := by
    have := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn
      (n := 0) (f := G₁)).2
      ⟨by simp, G₂, contDiffOn_zero.2 hcont₂, fun z hz ↦ (hderiv₂ z hz).hasFDerivWithinAt⟩
    simpa using this
  have := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn
    (n := 1) (f := evenReflection w)).2
    ⟨by simp, G₁, hG₁, fun z hz ↦ (hderiv₁ z hz).hasFDerivWithinAt⟩
  simpa [one_add_one_eq_two] using this

/-! ### The Laplacian of the even reflection -/

/-- Above the real axis the even reflection has the Laplacian of `w`. -/
theorem laplacian_evenReflection_of_pos (hz : 0 < z.im) : Δ (evenReflection w) z = Δ w z := by
  refine (laplacian_congr_nhds ?_).eq_of_nhds
  filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with y hy
  exact evenReflection_of_nonneg (le_of_lt hy)

/-- Below the real axis the even reflection has the Laplacian of `w` at the mirror point. -/
theorem laplacian_evenReflection_of_neg (hz : z.im < 0) :
    Δ (evenReflection w) z = Δ w (conj z) := by
  have h : evenReflection w =ᶠ[𝓝 z] w ∘ conjLIE := by
    filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hz] with y hy
    exact evenReflection_of_nonpos (le_of_lt hy)
  rw [(laplacian_congr_nhds h).eq_of_nhds, laplacian_comp_linearIsometryEquiv_right]
  rfl

end TauCeti
