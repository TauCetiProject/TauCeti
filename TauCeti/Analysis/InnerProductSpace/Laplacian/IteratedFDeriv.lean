/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Laplacian commutes with derivatives

On a finite-dimensional real inner product space `E`, the Laplacian of a function `f : E → F`
commutes with differentiation: for `f` of class `C³` at `x`,

`Δ (Df) x = D (Δ f) x`,

and for `f` of class `Cⁿ⁺²` on an open set `s`, the same holds for the `n`-th iterated derivative
in fixed directions `m`: `Δ (Dⁿ f · m) x = Dⁿ (Δ f) x m` for `x ∈ s`. Here `Df` and `Dⁿ f` are the
functions `fderiv ℝ f` and `iteratedFDeriv ℝ n f`.

Both sides of the first identity are traces of the third derivative `D³f x`, contracted in
different slots: `Δ (Df) x v = ∑ᵢ D³f x (eᵢ, eᵢ, v)` and `D (Δ f) x v = ∑ᵢ D³f x (v, eᵢ, eᵢ)`. They
agree because the third derivative of a `C³` function is symmetric. This is the identity behind
elliptic estimates for derivatives: if `f` solves `Δ f = g`, then each derivative of `f` solves the
differentiated equation `Δ (Dⁿ f) = Dⁿ g`.

## Main results

* `ContDiffAt.laplacian_fderiv`: `Δ (Df) x = D (Δ f) x` for `f` of class `C³` at `x`.
* `ContDiffAt.laplacian_fderiv_apply`: the same for a directional derivative `y ↦ Df y v`.
* `TauCeti.laplacian_iteratedFDeriv_apply`: `Δ (Dⁿ f · m) x = Dⁿ (Δ f) x m` for `f` of class
  `Cⁿ⁺²` on an open set containing `x`.
-/

public section

namespace TauCeti

open Filter Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Laplacian commutes with the derivative.** For `f` of class `C³` at `x`,
`Δ (Df) x = D (Δ f) x`, where `Df = fderiv ℝ f`. -/
theorem _root_.ContDiffAt.laplacian_fderiv {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    Δ (fderiv ℝ f) x = fderiv ℝ (Δ f) x := by
  set D₂ := fderiv ℝ (fderiv ℝ f)
  set b := stdOrthonormalBasis ℝ E
  have hD₁ : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hD₂ : DifferentiableAt ℝ D₂ x :=
    (hD₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Each entry `y ↦ D²f y p q` of the second derivative has derivative `r ↦ D³f x r p q` at `x`.
  have hd : ∀ p q, HasFDerivAt (fun y ↦ D₂ y p q) (((fderiv ℝ D₂ x).flip p).flip q) x :=
    fun p q ↦ by
      convert (hD₂.hasFDerivAt.clm_apply (hasFDerivAt_const p x)).clm_apply
        (hasFDerivAt_const q x) using 1
      ext r
      simp
  -- The third derivative is symmetric in its first two slots, since `Df` is `C²` at `x` ...
  have hS₁ : IsSymmSndFDerivAt ℝ (fderiv ℝ f) x :=
    hD₁.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  -- ... and in its last two slots, since `D²f` is symmetric at every point near `x`.
  have hS₂ : ∀ r p q, fderiv ℝ D₂ x r p q = fderiv ℝ D₂ x r q p := fun r p q ↦ by
    have heq : (fun y ↦ D₂ y p q) =ᶠ[𝓝 x] fun y ↦ D₂ y q p := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact (hy.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)) p q
    simpa using congrArg (· r) ((hd p q).unique ((hd q p).congr_of_eventuallyEq heq))
  have hΔ : HasFDerivAt (Δ f) (∑ i, ((fderiv ℝ D₂ x).flip (b i)).flip (b i)) x := by
    have h : Δ f = fun y ↦ ∑ i, D₂ y (b i) (b i) :=
      funext fun y ↦ by rw [laplacian_eq_traceL, traceL_apply]
    rw [h]
    exact HasFDerivAt.fun_sum fun i _ ↦ hd (b i) (b i)
  rw [hΔ.fderiv, laplacian_eq_traceL, traceL_apply]
  ext v
  simp only [sum_apply, ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hS₂, hS₁]

/-- **The Laplacian commutes with directional derivatives.** For `f` of class `C³` at `x` and a
direction `v`, `Δ (∂ᵥ f) x = ∂ᵥ (Δ f) x`, where `∂ᵥ f = fun y ↦ Df y v`. -/
theorem _root_.ContDiffAt.laplacian_fderiv_apply {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x)
    (v : E) : Δ (fun y ↦ fderiv ℝ f y v) x = fderiv ℝ (Δ f) x v := by
  rw [← hf.laplacian_fderiv]
  exact (hf.fderiv_right (m := 2) (by norm_num)).laplacian_CLM_comp_left
    (l := ContinuousLinearMap.apply ℝ F v)

/-- **The Laplacian commutes with iterated derivatives.** For `f` of class `Cⁿ⁺²` on an open set
`s`, `x ∈ s` and directions `m`, `Δ (Dⁿ f · m) x = Dⁿ (Δ f) x m`, where
`Dⁿ f = iteratedFDeriv ℝ n f`. -/
theorem laplacian_iteratedFDeriv_apply {f : E → F} {s : Set E} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℝ (n + 2) f s) (m : Fin n → E) {x : E} (hx : x ∈ s) :
    Δ (fun y ↦ iteratedFDeriv ℝ n f y m) x = iteratedFDeriv ℝ n (Δ f) x m := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcd : ∀ y ∈ s, ContDiffAt ℝ 3 (iteratedFDeriv ℝ n f) y := fun y hy ↦
      (hf.contDiffAt (hs.mem_nhds hy)).iteratedFDeriv_right (by norm_cast; omega)
    -- Near `x`, the `(n + 1)`-st derivative in direction `m` is a derivative of an `n`-th one.
    have hsucc : (fun y ↦ iteratedFDeriv ℝ (n + 1) f y m) =ᶠ[𝓝 x]
        fun y ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) y (m 0) :=
      Filter.eventually_of_mem (hs.mem_nhds hx) fun y hy ↦
        ((hcd y hy).differentiableAt (by norm_num)).iteratedFDeriv_succ_apply_left'
    have hg : ContDiffAt ℝ 3 (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F
        (Fin.tail m)).contDiff.contDiffAt.comp x (hcd x hx)
    have heq : Δ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) =ᶠ[𝓝 x]
        fun z ↦ iteratedFDeriv ℝ n (Δ f) z (Fin.tail m) :=
      Filter.eventually_of_mem (hs.mem_nhds hx) fun y hy ↦
        ih (hf.of_le (by norm_cast; omega)) (Fin.tail m) hy
    have hΔ : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Δ f)) x :=
      (((hf.contDiffAt (hs.mem_nhds hx)).laplacian (m := n + 1) (by norm_cast)
        ).iteratedFDeriv_right (m := 1) (add_comm _ _).le).differentiableAt
        (by norm_num)
    rw [(laplacian_congr_nhds hsucc).eq_of_nhds, hg.laplacian_fderiv_apply, heq.fderiv_eq,
      hΔ.iteratedFDeriv_succ_apply_left']

end TauCeti
