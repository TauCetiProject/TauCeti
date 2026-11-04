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
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.ReImTopology
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.LinearAlgebra.Complex.Module

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
theorem evenReflection_of_nonneg (hz : 0 ≤ z.im) : evenReflection w z = w z := by
  simp [evenReflection, abs_of_nonneg hz]

/-- On the closed lower half-plane the even reflection of `w` is `w ∘ conj`. -/
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

/-! ### Gluing along the real axis -/

section Gluing

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem closure_setOf_im_nonneg : closure {z : ℂ | 0 ≤ z.im} = {z | 0 ≤ z.im} :=
  (isClosed_le continuous_const continuous_im).closure_eq

private theorem closure_setOf_im_nonpos : closure {z : ℂ | z.im ≤ 0} = {z | z.im ≤ 0} :=
  (isClosed_le continuous_im continuous_const).closure_eq

private theorem setOf_im_nonneg_union : {z : ℂ | 0 ≤ z.im} ∪ {z | z.im ≤ 0} = univ :=
  eq_univ_of_forall fun z ↦ le_total 0 z.im

/-- A map with the same derivative within both closed half-planes at `z` is differentiable
at `z`. -/
private theorem hasFDerivAt_of_halfPlanes {f : ℂ → G} {f' : ℂ →L[ℝ] G}
    (h₁ : 0 ≤ z.im → HasFDerivWithinAt f f' {z | 0 ≤ z.im} z)
    (h₂ : z.im ≤ 0 → HasFDerivWithinAt f f' {z | z.im ≤ 0} z) : HasFDerivAt f f' z := by
  have hP : HasFDerivWithinAt f f' {z | 0 ≤ z.im} z := by
    by_cases hz : 0 ≤ z.im
    · exact h₁ hz
    · exact .of_notMem_closure (by rwa [closure_setOf_im_nonneg])
  have hQ : HasFDerivWithinAt f f' {z | z.im ≤ 0} z := by
    by_cases hz : z.im ≤ 0
    · exact h₂ hz
    · exact .of_notMem_closure (by rwa [closure_setOf_im_nonpos])
  simpa [setOf_im_nonneg_union] using hP.union hQ

omit [NormedSpace ℝ G] in
/-- A map continuous within both closed half-planes at `z` is continuous at `z`. -/
private theorem continuousAt_of_halfPlanes {f : ℂ → G}
    (h₁ : 0 ≤ z.im → ContinuousWithinAt f {z | 0 ≤ z.im} z)
    (h₂ : z.im ≤ 0 → ContinuousWithinAt f {z | z.im ≤ 0} z) : ContinuousAt f z := by
  have hP : ContinuousWithinAt f {z | 0 ≤ z.im} z := by
    by_cases hz : 0 ≤ z.im
    · exact h₁ hz
    · exact continuousWithinAt_of_notMem_closure (by rwa [closure_setOf_im_nonneg])
  have hQ : ContinuousWithinAt f {z | z.im ≤ 0} z := by
    by_cases hz : z.im ≤ 0
    · exact h₂ hz
    · exact continuousWithinAt_of_notMem_closure (by rwa [closure_setOf_im_nonpos])
  have h := hP.union hQ
  rwa [setOf_im_nonneg_union, continuousWithinAt_univ] at h

end Gluing

/-! ### `C²` regularity of the even reflection -/

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition with conjugation, `L ↦ L ∘ conj`, on real-linear maps out of `ℂ`. -/
private noncomputable abbrev conjPrecomp (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (conjCLE : ℂ →L[ℝ] ℂ)

private theorem conjPrecomp_apply (L : ℂ →L[ℝ] F) (v : ℂ) : conjPrecomp F L v = L (conj v) := by
  simp [conjPrecomp]

/-- A real-linear map vanishing at `I` is unchanged by precomposition with `conj`. -/
private theorem conjPrecomp_eq_self {L : ℂ →L[ℝ] F} (hL : L I = 0) : conjPrecomp F L = L := by
  have hdec : ∀ v : ℂ, L v = v.re • L 1 + v.im • L I :=
    L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I
  ext v
  rw [conjPrecomp_apply, hdec (conj v), hdec v]
  simp [hL]

/-- A bilinear map on `ℂ` with `B I 1 = B 1 I = 0` is unchanged by conjugating both
arguments. -/
private theorem conjPrecomp_comp_comp_conjCLE_eq_self {B : ℂ →L[ℝ] ℂ →L[ℝ] F}
    (h₁ : B 1 I = 0) (h₂ : B I 1 = 0) :
    (conjPrecomp F).comp (B.comp (conjCLE : ℂ →L[ℝ] ℂ)) = B := by
  have hdec : ∀ (L : ℂ →L[ℝ] F) (v : ℂ), L v = v.re • L 1 + v.im • L I := fun L v ↦
    L.toLinearMap.apply_eq_re_smul_one_add_im_smul_I v
  have hdec₂ : ∀ v : ℂ, B v = v.re • B 1 + v.im • B I :=
    B.toLinearMap.apply_eq_re_smul_one_add_im_smul_I
  ext v e
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
    conjPrecomp_apply]
  rw [hdec₂ (conj v), hdec₂ v]
  simp only [add_apply, smul_apply]
  rw [hdec (B 1) (conj e), hdec (B I) (conj e), hdec (B 1) e, hdec (B I) e, h₁, h₂]
  simp

/-- If `t ↦ D (x + t) I` vanishes for real `t` near `0`, along a set `S` containing the nearby
points of the real axis, then a derivative `D'` of `D` within `S` at `x` has `D' 1 I = 0`. -/
private theorem apply_one_apply_I_eq_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {D : ℂ → ℂ →L[ℝ] G} {D' : ℂ →L[ℝ] ℂ →L[ℝ] G} {S : Set ℂ} {x : ℂ}
    (hD : HasFDerivWithinAt D D' S x) (hS : ∀ᶠ t : ℝ in 𝓝 0, x + t ∈ S ∧ D (x + t) I = 0) :
    D' 1 I = 0 := by
  have hpath : HasDerivAt (fun t : ℝ ↦ x + t) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add x
  have hcomp : HasDerivWithinAt (fun t : ℝ ↦ D (x + t) I) (D' 1 I)
      ((fun t : ℝ ↦ x + t) ⁻¹' S) 0 := by
    have h := hD.comp_hasDerivWithinAt_of_eq (0 : ℝ)
      (hpath.hasDerivWithinAt (s := (fun t : ℝ ↦ x + t) ⁻¹' S)) (fun t ht ↦ ht) (by simp)
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ G I).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h
  have hzero : (fun t : ℝ ↦ D (x + t) I) =ᶠ[𝓝 0] fun _ ↦ 0 := hS.mono fun _ ht ↦ ht.2
  exact (hcomp.hasDerivAt (hS.mono fun _ ht ↦ ht.1)).unique
    ((hasDerivAt_const (0 : ℝ) (0 : G)).congr_of_eventuallyEq hzero)

/-- A point of an open set `U` on the real axis is a limit of interior points of
`{0 ≤ im z} ∩ U`. -/
private theorem mem_closure_interior_inter {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (hx0 : x.im = 0) : x ∈ closure (interior ({z : ℂ | 0 ≤ z.im} ∩ U)) := by
  rw [interior_inter, hU.interior_eq, interior_setOfPred_le_im]
  have hlim : Tendsto (fun t : ℝ ↦ x + t * I) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ x + t * I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin, hlim (hU.mem_nhds hx)] with t ht htU
  exact ⟨by simpa [hx0] using ht, htU⟩

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
  -- On the axis, precomposing the first two derivatives with `conj` changes nothing.
  have hedge₁ : ∀ x ∈ U, x.im = 0 → conjPrecomp F (D₁ x) = D₁ x := fun x hx hx0 ↦
    conjPrecomp_eq_self (hN x hx hx0)
  have hedge₂ : ∀ x ∈ U, x.im = 0 →
      (conjPrecomp F).comp ((D₂ x).comp (conjCLE : ℂ →L[ℝ] ℂ)) = D₂ x := by
    intro x hx hx0
    have hxS : x ∈ S := ⟨hx0.ge, hx⟩
    -- The mixed derivative `∂ₛ ∂ₜ w` vanishes along the axis, where `∂ₜ w` does.
    have hmixed : D₂ x 1 I = 0 := by
      refine apply_one_apply_I_eq_zero (hD₁S x hxS) ?_
      have hU' : (fun t : ℝ ↦ x + t) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
        (continuous_const.add continuous_ofReal).continuousAt.preimage_mem_nhds
          (by simpa using hU.mem_nhds hx)
      filter_upwards [hU'] with t ht
      exact ⟨⟨by simp [hx0], ht⟩, hN _ ht (by simp [hx0])⟩
    have hsymm : D₂ x I 1 = D₂ x 1 I :=
      (hw x hxS).isSymmSndFDerivWithinAt (by simp) hS (mem_closure_interior_inter hU hx hx0)
        hxS I 1
    exact conjPrecomp_comp_comp_conjCLE_eq_self hmixed (hsymm.trans hmixed)
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
    refine hasFDerivAt_of_halfPlanes (fun hz' ↦ ?_) fun hz' ↦ ?_
    · refine (((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hwS z ⟨hz', hz⟩)).congr
        (fun y hy ↦ evenReflection_of_nonneg hy) (evenReflection_of_nonneg hz')).congr_fderiv ?_
      simp only [G₁, ite_eq_left hz']
    · rw [hG₁_lower z hz hz']
      exact (hlower₁ z hz hz').congr (fun y hy ↦ evenReflection_of_nonpos hy)
        (evenReflection_of_nonpos hz')
  have hderiv₂ : ∀ z ∈ U, HasFDerivAt G₁ (G₂ z) z := by
    intro z hz
    refine hasFDerivAt_of_halfPlanes (fun hz' ↦ ?_) fun hz' ↦ ?_
    · refine (((hasFDerivWithinAt_inter (hU.mem_nhds hz)).1 (hD₁S z ⟨hz', hz⟩)).congr
        (fun y hy ↦ ite_eq_left hy) (ite_eq_left hz')).congr_fderiv ?_
      simp only [G₂, ite_eq_left hz']
    · rw [hG₂_lower z hz hz', ← hasFDerivWithinAt_inter (hU.mem_nhds hz)]
      refine ((hasFDerivWithinAt_inter (hU.mem_nhds hz)).2 (hlower₂ z hz hz')).congr
        (fun y hy ↦ hG₁_lower y hy.2 hy.1) (hG₁_lower z hz hz')
  have hcont₂ : ContinuousOn G₂ U := by
    intro z hz
    refine (continuousAt_of_halfPlanes (f := G₂) (fun hz' ↦ ?_) fun hz' ↦ ?_).continuousWithinAt
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
