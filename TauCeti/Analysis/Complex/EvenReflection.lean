/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Calculus.FDeriv.ClosedCover
import TauCeti.Analysis.Calculus.TangentCone.Basic
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
* `TauCeti.isSymmSndFDerivWithinAt_setOfPred_le_im_inter`: the second derivative within
  `{0 ≤ im z} ∩ U` of a function that is `C²` there is symmetric, also on the real axis.
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

/-! ### The closed upper half-plane near an open set -/

/-- Horizontal lines stay in `{0 ≤ im z} ∩ U` near any of its points, for `U` open. -/
theorem eventually_add_smul_one_mem_setOfPred_le_im_inter {U : Set ℂ} (hU : IsOpen U) {x : ℂ}
    (hx : x ∈ {z : ℂ | 0 ≤ z.im} ∩ U) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • (1 : ℂ) ∈ {z : ℂ | 0 ≤ z.im} ∩ U :=
  ((Continuous.tendsto' (by fun_prop) 0 x (by simp)).eventually (hU.mem_nhds hx.2)).mono
    fun t ht ↦ ⟨by simpa using hx.1, ht⟩

/-- For `U` open, every point of `{0 ≤ im z} ∩ U`, including the points on the real axis, lies in
the closure of its interior. -/
theorem subset_closure_interior_setOfPred_le_im_inter {U : Set ℂ} (hU : IsOpen U) :
    {z : ℂ | 0 ≤ z.im} ∩ U ⊆ closure (interior ({z : ℂ | 0 ≤ z.im} ∩ U)) := by
  intro x hx
  rw [interior_inter, hU.interior_eq, interior_setOfPred_le_im, inter_comm]
  exact hU.inter_closure ⟨hx.2, by rw [closure_setOfPred_lt_im]; exact hx.1⟩

/-! ### `C²` regularity of the even reflection -/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second derivative within `{0 ≤ im z} ∩ U` of a function that is `C²` there is symmetric,
also at the points on the real axis. -/
theorem isSymmSndFDerivWithinAt_setOfPred_le_im_inter {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ U)) {x : ℂ} (hx : x ∈ {z : ℂ | 0 ≤ z.im} ∩ U) :
    IsSymmSndFDerivWithinAt ℝ w ({z | 0 ≤ z.im} ∩ U) x :=
  (hw x hx).isSymmSndFDerivWithinAt (by simp) ((uniqueDiffOn_setOfPred_le_im 0).inter hU)
    (subset_closure_interior_setOfPred_le_im_inter hU hx) hx

/-- Precomposition with conjugation, `L ↦ L ∘ conj`, on real-linear maps out of `ℂ`. -/
private noncomputable abbrev conjPrecomp (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (conjCLE : ℂ →L[ℝ] ℂ)

private theorem conjPrecomp_apply (L : ℂ →L[ℝ] F) (v : ℂ) : conjPrecomp F L v = L (conj v) := by
  simp [conjPrecomp]

/-- A map with derivative `f'` within each closed half-plane containing `z` has derivative `f'`
at `z`. -/
private theorem hasFDerivAt_of_im_nonneg_of_im_nonpos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {f' : ℂ →L[ℝ] E}
    (h₁ : 0 ≤ z.im → HasFDerivWithinAt f f' {z | 0 ≤ z.im} z)
    (h₂ : z.im ≤ 0 → HasFDerivWithinAt f f' {z | z.im ≤ 0} z) : HasFDerivAt f f' z :=
  hasFDerivAt_of_isClosed_of_union_eq_univ (isClosed_le continuous_const continuous_im)
    (isClosed_le continuous_im continuous_const)
    (eq_univ_of_forall fun z ↦ le_total 0 z.im) h₁ h₂

/-- A map continuous within each closed half-plane containing `z` is continuous at `z`. -/
private theorem continuousAt_of_im_nonneg_of_im_nonpos {E : Type*} [TopologicalSpace E]
    {f : ℂ → E} (h₁ : 0 ≤ z.im → ContinuousWithinAt f {z | 0 ≤ z.im} z)
    (h₂ : z.im ≤ 0 → ContinuousWithinAt f {z | z.im ≤ 0} z) : ContinuousAt f z :=
  continuousAt_of_isClosed_of_union_eq_univ (isClosed_le continuous_const continuous_im)
    (isClosed_le continuous_im continuous_const)
    (eq_univ_of_forall fun z ↦ le_total 0 z.im) h₁ h₂

/-- On the closed lower half-plane, the function glued from `D` above the axis and `Φ (D (conj z))`
below it agrees with its lower branch as soon as `Φ (D z) = D z` at points of the axis. -/
private theorem ite_im_eq_of_im_nonpos {α : Type*} {D : ℂ → α} {Φ : α → α} (hz : z.im ≤ 0)
    (hedge : z.im = 0 → Φ (D z) = D z) :
    (if 0 ≤ z.im then D z else Φ (D (conj z))) = Φ (D (conj z)) := by
  by_cases h0 : 0 ≤ z.im
  · rw [ite_eq_left h0]
    have h := le_antisymm hz h0
    rw [conj_eq_iff_im.2 h]
    exact (hedge h).symm
  · rw [ite_eq_right h0]

/-- Conjugation maps the closed lower half-plane in `U` into the closed upper half-plane in `U`,
for `U` invariant under conjugation. -/
private theorem mapsTo_conj_lower_inter {U : Set ℂ} (hUc : ∀ z ∈ U, conj z ∈ U) :
    MapsTo conj ({y : ℂ | y.im ≤ 0} ∩ U) ({z : ℂ | 0 ≤ z.im} ∩ U) := fun y hy ↦
  ⟨by simpa using hy.1, hUc y hy.2⟩

/-- The chain rule for `g ∘ conj` at a point of the closed lower half-plane in `U`, from
derivatives of `g` within the upper half-plane in `U`. -/
private theorem hasFDerivWithinAt_comp_conj_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} (hU : IsOpen U) (hUc : ∀ z ∈ U, conj z ∈ U) {g : ℂ → E}
    {g' : ℂ → ℂ →L[ℝ] E}
    (hg : ∀ y ∈ {z : ℂ | 0 ≤ z.im} ∩ U, HasFDerivWithinAt g (g' y) ({z | 0 ≤ z.im} ∩ U) y)
    (hz : z ∈ U) (hz' : z.im ≤ 0) :
    HasFDerivWithinAt (fun y ↦ g (conj y)) ((g' (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))
      {y | y.im ≤ 0} z := by
  rw [← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
  exact (hg _ ⟨by simpa using hz', hUc z hz⟩).comp z
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivWithinAt (mapsTo_conj_lower_inter hUc)

/-- The second derivative of the even reflection is continuous across the axis once the second
derivative `D` of `w` is continuous up to the axis and invariant on it under precomposing both
arguments with conjugation, `D (conj u) (conj v) = D u v`. -/
private theorem continuousOn_ite_conjPrecomp_comp {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, conj z ∈ U) {D : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] F}
    (hD : ContinuousOn D ({z : ℂ | 0 ≤ z.im} ∩ U))
    (hedge : ∀ x ∈ U, x.im = 0 →
      (conjPrecomp F).comp ((D x).comp (conjCLE : ℂ →L[ℝ] ℂ)) = D x) :
    ContinuousOn (fun z ↦ if 0 ≤ z.im then D z
      else (conjPrecomp F).comp ((D (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))) U := by
  intro z hz
  refine (continuousAt_of_im_nonneg_of_im_nonpos (f := fun z ↦ if 0 ≤ z.im then D z
      else (conjPrecomp F).comp ((D (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ)))
      (fun hz' ↦ ?_) fun hz' ↦ ?_).continuousWithinAt
  · rw [← continuousWithinAt_inter (hU.mem_nhds hz)]
    exact (hD z ⟨hz', hz⟩).congr (fun y hy ↦ ite_eq_left hy.1) (ite_eq_left hz')
  · rw [← continuousWithinAt_inter (hU.mem_nhds hz)]
    have hc : ContinuousWithinAt (fun y ↦ D (conj y)) ({y : ℂ | y.im ≤ 0} ∩ U) z :=
      (hD (conj z) ⟨by simpa using hz', hUc z hz⟩).comp continuous_conj.continuousWithinAt
        (mapsTo_conj_lower_inter hUc)
    have hΦ : Continuous fun B : ℂ →L[ℝ] ℂ →L[ℝ] F ↦
        (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ)) := by
      fun_prop
    exact (hΦ.continuousAt.comp_continuousWithinAt hc).congr
      (fun y hy ↦ ite_im_eq_of_im_nonpos (D := D)
        (Φ := fun B ↦ (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ))) hy.1 (hedge y hy.2))
      (ite_im_eq_of_im_nonpos (D := D)
        (Φ := fun B ↦ (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ))) hz' (hedge z hz))

/-- At a point `x ∈ U` of the real axis where `∂ₜ w = 0`, the second derivative of `w` within the
upper half-plane is unchanged by precomposing both arguments with conjugation: the mixed
derivative `∂ₛ ∂ₜ w` vanishes along the axis, where `∂ₜ w` does. -/
private theorem conjPrecomp_comp_fderivWithin_fderivWithin_of_im_eq_zero {U : Set ℂ}
    (hU : IsOpen U) {w : ℂ → F} (hw : ContDiffOn ℝ 2 w ({z | 0 ≤ z.im} ∩ U))
    (hN : ∀ x ∈ U, x.im = 0 → fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U) x I = 0)
    (hD₁S : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ U,
      HasFDerivWithinAt (fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U))
        (fderivWithin ℝ (fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U)) ({z | 0 ≤ z.im} ∩ U) z)
        ({z | 0 ≤ z.im} ∩ U) z)
    {x : ℂ} (hx : x ∈ U) (hx0 : x.im = 0) :
    (conjPrecomp F).comp ((fderivWithin ℝ (fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U))
      ({z | 0 ≤ z.im} ∩ U) x).comp (conjCLE : ℂ →L[ℝ] ℂ)) =
      fderivWithin ℝ (fderivWithin ℝ w ({z | 0 ≤ z.im} ∩ U)) ({z | 0 ≤ z.im} ∩ U) x := by
  set S := {z : ℂ | 0 ≤ z.im} ∩ U
  set D₁ := fderivWithin ℝ w S
  set D₂ := fderivWithin ℝ D₁ S
  have hxS : x ∈ S := ⟨hx0.ge, hx⟩
  have hmixed : D₂ x 1 I = 0 := by
    have hS' := eventually_add_smul_one_mem_setOfPred_le_im_inter hU hxS
    have hline := (((ContinuousLinearMap.apply ℝ F I).hasFDerivAt.comp_hasFDerivWithinAt x
      (hD₁S x hxS)).hasLineDerivWithinAt (1 : ℂ)).hasLineDerivAt' hS'
    refine hline.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq ?_)
    filter_upwards [hS'] with t ht
    exact hN _ ht.2 (by simp [hx0])
  have hsymm : D₂ x I 1 = D₂ x 1 I := isSymmSndFDerivWithinAt_setOfPred_le_im_inter hU hw hxS I 1
  ext v e
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
    conjPrecomp_apply]
  exact (D₂ x).toLinearMap₁₂.apply_conj_apply_conj_of_apply_one_I_eq_zero_of_apply_I_one_eq_zero
    hmixed (hsymm.trans hmixed) v e

/-- The first derivative of the even reflection, glued from the derivative `D₁` of `w` within the
upper half-plane, exists at every point of `U` once `D₁` is invariant on the axis under
precomposition with conjugation. -/
private theorem hasFDerivAt_evenReflection {U : Set ℂ} (hU : IsOpen U) (hUc : ∀ z ∈ U, conj z ∈ U)
    {w : ℂ → F} {D₁ : ℂ → ℂ →L[ℝ] F}
    (hwS : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ U, HasFDerivWithinAt w (D₁ z) ({z | 0 ≤ z.im} ∩ U) z)
    (hedge₁ : ∀ x ∈ U, x.im = 0 → conjPrecomp F (D₁ x) = D₁ x) {z : ℂ} (hz : z ∈ U) :
    HasFDerivAt (evenReflection w)
      (if 0 ≤ z.im then D₁ z else conjPrecomp F (D₁ (conj z))) z := by
  refine hasFDerivAt_of_im_nonneg_of_im_nonpos (fun hz' ↦ ?_) fun hz' ↦ ?_
  · rw [ite_eq_left hz']
    exact (((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hwS z ⟨hz', hz⟩)).congr
      (fun y hy ↦ evenReflection_of_nonneg hy) (evenReflection_of_nonneg hz'))
  · rw [ite_im_eq_of_im_nonpos (D := D₁) (Φ := conjPrecomp F) hz' (hedge₁ z hz)]
    have heq : conjPrecomp F (D₁ (conj z)) = (D₁ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ) := by
      ext v
      simp
    rw [heq]
    exact (hasFDerivWithinAt_comp_conj_lower hU hUc hwS hz hz').congr
      (fun y hy ↦ evenReflection_of_nonpos hy) (evenReflection_of_nonpos hz')

/-- The derivative of the glued first derivative of the even reflection, glued from the derivative
`D₂` of `D₁` within the upper half-plane. -/
private theorem hasFDerivAt_ite_conjPrecomp {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ z ∈ U, conj z ∈ U) {D₁ : ℂ → ℂ →L[ℝ] F} {D₂ : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] F}
    (hD₁S : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ U,
      HasFDerivWithinAt D₁ (D₂ z) ({z | 0 ≤ z.im} ∩ U) z)
    (hedge₁ : ∀ x ∈ U, x.im = 0 → conjPrecomp F (D₁ x) = D₁ x)
    (hedge₂ : ∀ x ∈ U, x.im = 0 →
      (conjPrecomp F).comp ((D₂ x).comp (conjCLE : ℂ →L[ℝ] ℂ)) = D₂ x) {z : ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun z ↦ if 0 ≤ z.im then D₁ z else conjPrecomp F (D₁ (conj z)))
      (if 0 ≤ z.im then D₂ z
        else (conjPrecomp F).comp ((D₂ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))) z := by
  have hG₁ : ∀ y ∈ U, y.im ≤ 0 →
      (if 0 ≤ y.im then D₁ y else conjPrecomp F (D₁ (conj y))) = conjPrecomp F (D₁ (conj y)) :=
    fun y hy hy' ↦ ite_im_eq_of_im_nonpos (D := D₁) (Φ := conjPrecomp F) hy' (hedge₁ y hy)
  refine hasFDerivAt_of_im_nonneg_of_im_nonpos (fun hz' ↦ ?_) fun hz' ↦ ?_
  · rw [ite_eq_left hz']
    exact ((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hD₁S z ⟨hz', hz⟩)).congr
      (fun y hy ↦ ite_eq_left hy) (ite_eq_left hz')
  · rw [ite_im_eq_of_im_nonpos (D := D₂)
    (Φ := fun B ↦ (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ))) hz' (hedge₂ z hz)]
    rw [← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
    exact (((conjPrecomp F).hasFDerivAt.comp_hasFDerivWithinAt z
      (hasFDerivWithinAt_comp_conj_lower hU hUc hD₁S hz hz')).mono inter_subset_left).congr
      (fun y hy ↦ hG₁ y hy.2 hy.1) (hG₁ z hz hz')

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
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_setOfPred_le_im 0).inter hU
  have hD₁ : ContDiffOn ℝ 1 D₁ S := hw.fderivWithin hS (by norm_num)
  have hD₂ : ContinuousOn D₂ S := hD₁.continuousOn_fderivWithin hS le_rfl
  have hwS : ∀ z ∈ S, HasFDerivWithinAt w (D₁ z) S z := fun z hz ↦
    ((hw.differentiableOn (by norm_num)) z hz).hasFDerivWithinAt
  have hD₁S : ∀ z ∈ S, HasFDerivWithinAt D₁ (D₂ z) S z := fun z hz ↦
    ((hD₁.differentiableOn (by norm_num)) z hz).hasFDerivWithinAt
  -- On the axis, precomposing the first two derivatives with `conj` changes nothing.
  have hedge₁ : ∀ x ∈ U, x.im = 0 → conjPrecomp F (D₁ x) = D₁ x := fun x hx hx0 ↦ by
    ext v
    rw [conjPrecomp_apply]
    exact (D₁ x).toLinearMap.apply_conj_of_apply_I_eq_zero (hN x hx hx0) v
  have hedge₂ : ∀ x ∈ U, x.im = 0 →
      (conjPrecomp F).comp ((D₂ x).comp (conjCLE : ℂ →L[ℝ] ℂ)) = D₂ x := fun x hx hx0 ↦
    conjPrecomp_comp_fderivWithin_fderivWithin_of_im_eq_zero hU hw hN hD₁S hx hx0
  -- The first and second derivatives of the reflection, glued along the axis.
  set G₁ : ℂ → ℂ →L[ℝ] F := fun z ↦ if 0 ≤ z.im then D₁ z else conjPrecomp F (D₁ (conj z))
  have hG₁ : ContDiffOn ℝ 1 G₁ U := by
    have := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn
      (n := 0) (f := G₁)).2
      ⟨by simp, _, contDiffOn_zero.2 (continuousOn_ite_conjPrecomp_comp hU hUc hD₂ hedge₂),
        fun z hz ↦ (hasFDerivAt_ite_conjPrecomp hU hUc hD₁S hedge₁ hedge₂ hz).hasFDerivWithinAt⟩
    simpa using this
  have := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn
    (n := 1) (f := evenReflection w)).2
    ⟨by simp, _, hG₁,
      fun z hz ↦ (hasFDerivAt_evenReflection hU hUc hwS hedge₁ hz).hasFDerivWithinAt⟩
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
