/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Calculus.SecondDerivative

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.BilinearForm.Properties

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Necessary and strict derivative tests

This file records necessary versions of Mathlib's sufficient second-derivative tests. At a local
maximum of a continuous real-valued function, the value `deriv (deriv g) t₀` is nonpositive; at a
local minimum it is nonnegative. On a real normed space the same holds for every diagonal entry
`fderiv ℝ (fderiv ℝ f) x w w` of the Hessian of a function differentiable near a local extremum.
At either kind of extremum,
a direction with zero diagonal Hessian value lies in the kernel of the Hessian.

It also strengthens the conclusion of Mathlib's sufficient second-derivative test: at a critical
point `x₀` with `deriv (deriv f) x₀ > 0` the function has a *strict* local minimum,
`f x₀ < f x` for `x ≠ x₀` near `x₀`, and dually for `deriv (deriv f) x₀ < 0`. Strictness is what
the stability of an equilibrium at a minimum of the energy needs. This goes through a strict
version of Mathlib's first-derivative test `isLocalMin_of_sign_deriv`.

It also records the one-sided first-derivative tests at an endpoint: a function with a local
maximum on `Iic a` at `a` (a maximum *from the left*) has nonnegative left derivative there, and
dually for minima and for maxima and minima from the right on `Ici a`. The maximum from the left
is the time-direction step of the parabolic maximum principle, where the maximum may sit on the
top of the space-time cylinder. The same test along the inward ray `t ↦ x - t • e` turns a lower
bound on difference quotients into a lower bound on a directional derivative, which is the last
step of Hopf's boundary-point lemma.

## Main declarations

* `IsLocalMaxOn.hasDerivWithinAt_Iic_nonneg`: the left derivative at a maximum from the left is
  nonnegative.
* `IsLocalMinOn.hasDerivWithinAt_Iic_nonpos`, `IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos`,
  `IsLocalMinOn.hasDerivWithinAt_Ici_nonneg`: the dual endpoint tests.
* `TauCeti.eventually_lt_of_sign_deriv`: the strict first-derivative test.
* `TauCeti.eventually_nhdsGT_lt_of_deriv_pos`: its right-hand half, for a function with positive
  derivative just to the right of `x₀`.
* `TauCeti.eventually_lt_of_deriv_deriv_pos`, `TauCeti.eventually_gt_of_deriv_deriv_neg`: the
  strict second-derivative tests.
* `TauCeti.deriv_deriv_nonpos_of_isLocalMax`: the local-maximum version.
* `TauCeti.deriv_deriv_nonneg_of_isLocalMin`: the local-minimum version.
* `TauCeti.fderiv_fderiv_self_nonpos_of_isLocalMax` /
  `TauCeti.fderiv_fderiv_self_nonneg_of_isLocalMin`: the Hessian is negative (resp. positive)
  semidefinite on the diagonal at a local maximum (resp. minimum).
* `IsLocalMin.isPosSemidef_fderiv_fderiv`: the Hessian is positive semidefinite.
* `IsLocalExtr.fderiv_fderiv_apply_self_eq_zero_iff`: zero diagonal directions are precisely
  the kernel directions at either kind of local extremum.
* `TauCeti.hasDerivAt_zero_of_isLocalExtr_of_fderiv_eq`: a vanishing derivative from
  coupled partial-derivative identities at a local extremum.
* `TauCeti.le_fderiv_of_le_sub`: a lower bound `g t ≤ f x - f (x - t • e)` for small `t > 0`
  bounds the directional derivative `fderiv ℝ f x e` below by the right derivative of `g` at `0`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Proposition 6.30.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

namespace TauCeti

open Topology

/-- **Necessary second-derivative test.** At a local maximum of a continuous function
`g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonpositive. -/
theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmax : IsLocalMax g t₀) :
    deriv (deriv g) t₀ ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have hd : deriv g t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g t₀ := isLocalMin_of_deriv_deriv_pos h hd hg
  -- Being both a local minimum and a local maximum, `g` is eventually constant near `t₀`.
  have hconst : g =ᶠ[𝓝 t₀] fun _ => g t₀ := by
    filter_upwards [hmax, hmin] with y hy hy' using le_antisymm hy hy'
  have hderiv : deriv g =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.deriv] with y hy
    simpa using hy
  have hzero : deriv (deriv g) t₀ = 0 := by
    rw [hderiv.deriv_eq]; simp
  linarith

/-- **Necessary second-derivative test, minimum version.** At a local minimum of a continuous
function `g : ℝ → ℝ`, the value `deriv (deriv g) t₀` is nonnegative. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousAt g t₀) (hmin : IsLocalMin g t₀) :
    0 ≤ deriv (deriv g) t₀ := by
  have := deriv_deriv_nonpos_of_isLocalMax (g := -g) hg.neg hmin.neg
  simpa using this

/-- **One-sided first-derivative test.** If `f : ℝ → ℝ` has a local maximum on `Iic a` at `a`,
that is a maximum from the left, then its left derivative at `a` is nonnegative. -/
theorem _root_.IsLocalMaxOn.hasDerivWithinAt_Iic_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMaxOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : 0 ≤ f' := by
  have hy : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a :=
    mem_posTangentConeAt_of_segment_subset <| by
      rw [segment_symm, segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Iic_self
  simpa using h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy

/-- **One-sided first-derivative test, minimum version.** If `f : ℝ → ℝ` has a local minimum on
`Iic a` at `a`, then its left derivative at `a` is nonpositive. -/
theorem _root_.IsLocalMinOn.hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 := by
  simpa using h.neg.hasDerivWithinAt_Iic_nonneg hf.neg

/-- **One-sided first-derivative test on the right.** If `f : ℝ → ℝ` has a local maximum on
`Ici a` at `a`, that is a maximum from the right, then its right derivative at `a` is
nonpositive. -/
theorem _root_.IsLocalMaxOn.hasDerivWithinAt_Ici_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMaxOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : f' ≤ 0 := by
  have hy : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a :=
    mem_posTangentConeAt_of_segment_subset <| by
      rw [segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Ici_self
  simpa using h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy

/-- **One-sided first-derivative test on the right, minimum version.** If `f : ℝ → ℝ` has a
local minimum on `Ici a` at `a`, then its right derivative at `a` is nonnegative. -/
theorem _root_.IsLocalMinOn.hasDerivWithinAt_Ici_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by
  simpa using h.neg.hasDerivWithinAt_Ici_nonpos hf.neg

/-- **Strict first-derivative test, right-hand half.** If `f : ℝ → ℝ` is continuous at `x₀`
and has positive derivative just to the right of `x₀`, then `f x₀ < f x` just to the right of
`x₀`. -/
theorem eventually_nhdsGT_lt_of_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[>] x₀, 0 < deriv f x) : ∀ᶠ x in 𝓝[>] x₀, f x₀ < f x := by
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hf
  -- `f` is strictly increasing on `[x₀, b)`: continuous there, with positive derivative inside.
  have hmono : StrictMonoOn f (Set.Ico x₀ b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rcases hx.1.eq_or_lt with rfl | hlt
      · exact hc.continuousWithinAt
      · exact (differentiableAt_of_deriv_ne_zero (hsub ⟨hlt, hx.2⟩).ne').continuousAt
          |>.continuousWithinAt
    · rw [interior_Ico] at hx
      exact hsub hx
  filter_upwards [Ioo_mem_nhdsGT hb] with x hx
  exact hmono ⟨le_rfl, hb⟩ ⟨hx.1.le, hx.2⟩ hx.1

/-- **Strict first-derivative test.** If `f : ℝ → ℝ` is continuous at `x₀` and, near `x₀`, the
derivative of `f` has the sign of `x - x₀`, then `x₀` is a strict local minimum of `f`:
`f x₀ < f x` for every `x ≠ x₀` close to `x₀`. This strengthens Mathlib's
`isLocalMin_of_sign_deriv`. -/
theorem eventually_lt_of_sign_deriv {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hf : ∀ᶠ x in 𝓝[≠] x₀, SignType.sign (deriv f x) = SignType.sign (x - x₀)) :
    ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x := by
  rw [← nhdsLT_sup_nhdsGT, Filter.eventually_sup]
  refine ⟨?_, eventually_nhdsGT_lt_of_deriv_pos hc (deriv_pos_right_of_sign_deriv hf)⟩
  -- To the left of `x₀`, apply the right-hand half to the reflection `x ↦ f (-x)` at `-x₀`.
  have hderiv : ∀ᶠ x in 𝓝[>] (-x₀), 0 < deriv (fun x ↦ f (-x)) x := by
    filter_upwards [tendsto_neg_nhdsGT_neg.eventually (deriv_neg_left_of_sign_deriv hf)]
      with x hx
    rw [deriv_comp_neg]
    exact neg_pos.2 hx
  have hc' : ContinuousAt (fun x ↦ f (-x)) (-x₀) :=
    (by rwa [neg_neg] : ContinuousAt f (-(-x₀))).comp continuousAt_neg
  filter_upwards [tendsto_neg_nhdsLT.eventually (eventually_nhdsGT_lt_of_deriv_pos hc' hderiv)]
    with x hx
  simpa using hx

/-- **Strict second-derivative test.** If `deriv f x₀ = 0` and `deriv (deriv f) x₀ > 0` for a
function `f : ℝ → ℝ` continuous at `x₀`, then `x₀` is a strict local minimum of `f`:
`f x₀ < f x` for every `x ≠ x₀` close to `x₀`. -/
theorem eventually_lt_of_deriv_deriv_pos {f : ℝ → ℝ} {x₀ : ℝ} (hf : 0 < deriv (deriv f) x₀)
    (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : ∀ᶠ x in 𝓝[≠] x₀, f x₀ < f x :=
  eventually_lt_of_sign_deriv hc <| nhdsWithin_le_nhds <|
    eventually_nhdsWithin_sign_eq_of_deriv_pos hf hd

/-- **Strict second-derivative test, maximum version.** If `deriv f x₀ = 0` and
`deriv (deriv f) x₀ < 0` for a function `f : ℝ → ℝ` continuous at `x₀`, then `x₀` is a strict
local maximum of `f`. -/
theorem eventually_gt_of_deriv_deriv_neg {f : ℝ → ℝ} {x₀ : ℝ} (hf : deriv (deriv f) x₀ < 0)
    (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) : ∀ᶠ x in 𝓝[≠] x₀, f x < f x₀ := by
  simpa using eventually_lt_of_deriv_deriv_pos (f := (-f ·)) (by simpa) (by simpa) hc.neg

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}

/-- At a local minimum of a function differentiable near `x`, every diagonal Hessian entry
is nonnegative. If the first derivative is not differentiable at `x`, the Hessian is zero by
Mathlib's convention for the totalized derivative. -/
theorem fderiv_fderiv_self_nonneg_of_isLocalMin
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hmin : IsLocalMin f x)
    (w : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x w w := by
  by_cases hD : DifferentiableAt ℝ (fderiv ℝ f) x
  · let a : ℝ → E := fun t ↦ x + t • w
    have ha (t : ℝ) : HasDerivAt a w t := by
      simpa only [a, id_eq, one_smul] using ((hasDerivAt_id t).smul_const w).const_add x
    have ha0 : a 0 = x := by simp only [a, zero_smul, add_zero]
    have hsecond : deriv (deriv (f ∘ a)) 0 = fderiv ℝ (fderiv ℝ f) x w w := by
      simpa only [a, Function.comp_def, zero_smul, add_zero] using
        (DifferentiableAt.hasDerivAt_deriv_comp_add_smul
          (x := x) (t := (0 : ℝ)) (y := w) (by simpa using hD)
          (by simpa using hf)).deriv
    have hminA : IsLocalMin f (a 0) := ha0.symm ▸ hmin
    have hc : ContinuousAt f (a 0) := ha0.symm ▸ hf.self_of_nhds.continuousAt
    have h := deriv_deriv_nonneg_of_isLocalMin (hc.comp (ha 0).continuousAt)
      (hminA.comp_continuous (ha 0).continuousAt)
    rwa [hsecond] at h
  · simp [fderiv_zero_of_not_differentiableAt hD]

/-- At a local maximum of a function differentiable near `x`, every diagonal Hessian entry
is nonpositive. -/
theorem fderiv_fderiv_self_nonpos_of_isLocalMax
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hmax : IsLocalMax f x)
    (w : E) : fderiv ℝ (fderiv ℝ f) x w w ≤ 0 := by
  have h := fderiv_fderiv_self_nonneg_of_isLocalMin (hf.mono fun _ hy ↦ hy.neg) hmax.neg w
  rw [fderiv_fderiv_neg] at h
  simpa only [neg_apply, neg_nonneg] using h

/-- The Hessian at a local minimum is a positive semidefinite bilinear form, assuming
only differentiability of the function near the minimum. -/
theorem _root_.IsLocalMin.isPosSemidef_fderiv_fderiv (hmin : IsLocalMin f x)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) :
    (fderiv ℝ (fderiv ℝ f) x).toBilinForm.IsPosSemidef := by
  refine ⟨⟨fun v w ↦ ?_⟩, ⟨fderiv_fderiv_self_nonneg_of_isLocalMin hf hmin⟩⟩
  by_cases hD : DifferentiableAt ℝ (fderiv ℝ f) x
  · exact second_derivative_symmetric_of_eventually_of_real
      (hf.mono fun _ hy ↦ hy.hasFDerivAt) hD.hasFDerivAt v w
  · simp [fderiv_zero_of_not_differentiableAt hD]

/-- At a local extremum of a function differentiable nearby, a Hessian direction has zero
diagonal value exactly when it lies in the kernel of the Hessian. This eliminates mixed
second-variation terms without assuming continuity of the second derivative. -/
theorem _root_.IsLocalExtr.fderiv_fderiv_apply_self_eq_zero_iff (hextr : IsLocalExtr f x)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) {v : E} :
    fderiv ℝ (fderiv ℝ f) x v v = 0 ↔ fderiv ℝ (fderiv ℝ f) x v = 0 := by
  have hmin {g : E → ℝ} (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
      (h : IsLocalMin g x) :
      fderiv ℝ (fderiv ℝ g) x v v = 0 ↔ fderiv ℝ (fderiv ℝ g) x v = 0 := by
    have hB := h.isPosSemidef_fderiv_fderiv hg
    have heq := (fderiv ℝ (fderiv ℝ g) x).toBilinForm.apply_apply_same_eq_zero_iff
      hB.isNonneg.nonneg (LinearMap.BilinForm.isSymm_iff.mp hB.isSymm) (x := v)
    constructor
    · intro hv
      have hker := heq.mp hv
      ext w
      exact congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L w) hker
    · intro hv
      simp [hv]
  rcases hextr with h | h
  · exact hmin hf h
  · have heq := hmin (hf.mono fun _ hy ↦ hy.neg) h.neg
    rw [fderiv_fderiv_neg] at heq
    simpa only [neg_apply, neg_eq_zero] using heq

/-- **Difference quotients bound the directional derivative.** Let `f` be differentiable at `x`,
and let `g` vanish at `0` and have right derivative `κ` there. If `g t ≤ f x - f (x - t • e)` for
`0 < t ≤ δ`, then `κ ≤ fderiv ℝ f x e`. -/
theorem le_fderiv_of_le_sub {g : ℝ → ℝ} {e : E} {κ δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableAt ℝ f x) (hg : HasDerivWithinAt g κ (Set.Ici 0) 0) (hg0 : g 0 = 0)
    (hle : ∀ t ∈ Set.Ioc 0 δ, g t ≤ f x - f (x - t • e)) :
    κ ≤ fderiv ℝ f x e := by
  have hline : HasDerivAt (fun t : ℝ ↦ x - t • e) (-e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x
  have hray : HasDerivAt (fun t : ℝ ↦ f (x - t • e)) (-fderiv ℝ f x e) 0 := by
    have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline (by simp)
    rwa [map_neg] at h
  -- The difference `f x - f (x - t • e) - g t` has a minimum from the right at `t = 0`.
  have hmin : IsLocalMinOn (fun t ↦ f x - f (x - t • e) - g t) (Set.Ici 0) 0 := by
    filter_upwards [Icc_mem_nhdsGE hδ] with t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · exact le_rfl
    · simp only [zero_smul, sub_zero, sub_self, hg0]
      linarith [hle t ⟨ht0, ht.2⟩]
  have h := hmin.hasDerivWithinAt_Ici_nonneg ((hray.const_sub (f x)).hasDerivWithinAt.sub hg)
  linarith

end NormedSpace

section Variation

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a local extremum `(r, x)` of `C`, suppose its horizontal partial is `R t (u t)`
and its vertical partial is `R t` near `r`. If `u t → 0`, differentiability of the first
derivative of `C` implies that `R` has derivative zero at `r`. -/
theorem hasDerivAt_zero_of_isLocalExtr_of_fderiv_eq
    {C : ℝ × E → ℝ} {u : ℝ → E} {R : ℝ → E →L[ℝ] ℝ} {r : ℝ} {x : E}
    (hC : ∀ᶠ p in 𝓝 (r, x), DifferentiableAt ℝ C p)
    (hDC : DifferentiableAt ℝ (fderiv ℝ C) (r, x)) (hextr : IsLocalExtr C (r, x))
    (hu : Tendsto u (𝓝[≠] r) (𝓝 0))
    (hfirst : ∀ᶠ t in 𝓝 r, fderiv ℝ C (t, x) (1, 0) = R t (u t))
    (hsecond : ∀ᶠ t in 𝓝 r, ∀ v, fderiv ℝ C (t, x) (0, v) = R t v) :
    HasDerivAt R 0 r := by
  have hR0 : R r = 0 := by
    ext v
    have h := hsecond.self_of_nhds v
    rw [hextr.fderiv_eq_zero] at h
    exact h.symm
  let B := (fderiv ℝ (fderiv ℝ C) (r, x) (1, 0)).comp
    (ContinuousLinearMap.inr ℝ ℝ E)
  have hR : HasDerivAt R B r := by
    have h := (hasDerivAt_slice_left hDC).clm_comp
      (hasDerivAt_const r (ContinuousLinearMap.inr ℝ ℝ E))
    simp only [ContinuousLinearMap.comp_zero, add_zero] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hsecond] with t ht
    ext v
    exact (ht v).symm
  have hproduct : HasDerivAt (fun t ↦ R t (u t)) 0 r := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hcont := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous
    have hlim := (hcont.tendsto (B, 0)).comp
        (hR.tendsto_slope.prodMk_nhds hu)
    -- Evaluation of the bounded bilinear map is pointwise application.
    change Tendsto (fun t ↦ slope R r t (u t)) (𝓝[≠] r) (𝓝 (B 0)) at hlim
    rw [map_zero] at hlim
    -- Expand the slope as a function so the public scalar-action law applies pointwise.
    change Tendsto (fun t ↦ (t - r)⁻¹ • (R t (u t) - R r (u r))) (𝓝[≠] r) (𝓝 0)
    apply hlim.congr'
    exact Eventually.of_forall fun t ↦ by
      simp only [slope_def_module, hR0, sub_zero, zero_apply, smul_apply]
  have hdiag : fderiv ℝ (fderiv ℝ C) (r, x) (1, 0) (1, 0) = 0 :=
    (hasDerivAt_fderiv_apply_fst hDC (1, 0)).unique
      (hproduct.congr_of_eventuallyEq hfirst)
  have hkernel := (hextr.fderiv_fderiv_apply_self_eq_zero_iff hC).mp hdiag
  have hB : B = 0 := by simp only [B, hkernel, ContinuousLinearMap.zero_comp]
  exact hB ▸ hR

end Variation

end TauCeti
