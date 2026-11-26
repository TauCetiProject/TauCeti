/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Parameter derivatives of families of holomorphic functions

Let `H : X × ℂ → G` be a map from the product of a real normed space `X` of parameters and the
complex plane into a complex normed space `G`. Suppose that `H` is jointly `C^n` on an open
product `W ×ˢ V`, and that `z ↦ H (x, z)` is holomorphic on `V` for every `x ∈ W`. Then every
parameter derivative of order `k < n` is again holomorphic in `z`:
`z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x` is complex differentiable on `V`, with values in
the complex normed space of continuous real-multilinear maps
(`ContDiffOn.differentiableOn_iteratedFDeriv_partial`).

The first-order case (`ContDiffOn.differentiableOn_fderiv_partial`) is the symmetry of the second
derivative of a `C²` map: the Cauchy–Riemann equation `DH(p) (0, I) = I • DH(p) (0, 1)` for the
real derivative `DH(p)` of `H` holds at every point `p` of `W ×ˢ V`, and differentiating it in a
parameter direction gives the Cauchy–Riemann equation for the parameter derivative. Higher
orders follow by induction, since the parameter derivatives are again jointly smooth
(`ContDiffOn.contDiffOn_iteratedFDeriv_partial`).

Holomorphy of parameter derivatives is what lets estimates for holomorphic functions of `z`,
such as Runge approximation (`TauCeti.Analysis.Complex.Runge.Parameter`), be applied to every
parameter derivative of a family.

The approach follows the mixed-derivative calculus of Tau Ceti pull request 43183.
-/

public section

open Complex Filter Set Topology TauCeti

namespace ContDiffOn

variable {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup G]
  [NormedSpace ℂ G] {W : Set X} {V : Set ℂ} {H : X × ℂ → G}

/-- **Holomorphy of the parameter derivative.** If `H : X × ℂ → G` is `C²` on an open product
`W ×ˢ V` and holomorphic in its complex variable on `V`, then the parameter derivative
`z ↦ fderiv ℝ (fun x' ↦ H (x', z)) x` is holomorphic on `V` for every `x ∈ W`. -/
theorem differentiableOn_fderiv_partial (hH : ContDiffOn ℝ 2 H (W ×ˢ V)) (hW : IsOpen W)
    (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X}
    (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun x' ↦ H (x', z)) x) V := by
  intro z hz
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hH2 : ContDiffAt ℝ 2 H (x, z) := hH.contDiffAt (hU.mem_nhds ⟨hx, hz⟩)
  have hDH : DifferentiableAt ℝ (fderiv ℝ H) (x, z) :=
    (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  -- Near `z`, the parameter derivative is the total derivative restricted to `X × {0}`.
  have hloc : (fun z' ↦ fderiv ℝ (fun x' ↦ H (x', z')) x) =ᶠ[𝓝 z]
      fun z' ↦ (fderiv ℝ H (x, z')).comp (ContinuousLinearMap.inl ℝ X ℂ) := by
    filter_upwards [hV.mem_nhds hz] with z' hz'
    exact fderiv_slice_left
      ((hH.contDiffAt (hU.mem_nhds ⟨hx, hz'⟩)).differentiableAt (by norm_num))
  have hslice : HasFDerivAt (fun z' ↦ fderiv ℝ H (x, z'))
      ((fderiv ℝ (fderiv ℝ H) (x, z)).comp (ContinuousLinearMap.inr ℝ X ℂ)) z :=
    hDH.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)
  have hderiv := (hslice.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inl ℝ X ℂ) z))
    |>.congr_of_eventuallyEq hloc
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
    hderiv.differentiableAt).2 ?_).differentiableWithinAt
  -- The Cauchy–Riemann expression `DH(p)(0, 1) + I • DH(p)(0, I)` vanishes near `(x, z)`.
  have hcr : (fun p : X × ℂ ↦ fderiv ℝ H p (0, 1) + I • fderiv ℝ H p (0, I)) =ᶠ[𝓝 (x, z)]
      fun _ ↦ (0 : G) := by
    filter_upwards [hU.mem_nhds ⟨hx, hz⟩] with p hp
    have hpd : DifferentiableAt ℝ H p :=
      (hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
    have hphol : DifferentiableAt ℂ (fun w ↦ H (p.1, w)) p.2 :=
      (hhol p.1 hp.1).differentiableAt (hV.mem_nhds hp.2)
    have hsr (w : ℂ) : fderiv ℝ H p (0, w) = w • deriv (fun w' ↦ H (p.1, w')) p.2 := by
      have := congrArg (fun L : ℂ →L[ℝ] G ↦ L w) (fderiv_slice_right (a := p.1) (b := p.2) hpd)
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inr_apply] at this
      rw [← this, (hphol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
      simp
    rw [hsr, hsr, smul_smul, I_mul_I, neg_one_smul, one_smul, add_neg_cancel]
  -- Differentiating it in the direction `(u, 0)` and using symmetry of `D²H` gives the claim.
  have hDcr := ((ContinuousLinearMap.apply ℝ G ((0 : X), (1 : ℂ))).hasFDerivAt.comp (x, z)
    hDH.hasFDerivAt).add (((ContinuousLinearMap.apply ℝ G ((0 : X), I)).hasFDerivAt.comp (x, z)
      hDH.hasFDerivAt).const_smul I)
  have h0 := (hDcr.congr_of_eventuallyEq hcr.symm).unique (hasFDerivAt_const (0 : G) (x, z))
  have hsymm := hH2.isSymmSndFDerivAt (by simp)
  rw [conjWirtingerDeriv_apply, hderiv.fderiv]
  ext u
  have hu := congrArg (fun L : X × ℂ →L[ℝ] G ↦ L (u, 0)) h0
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, smul_apply, zero_apply] at hu
  simpa [hsymm (0, 1) (u, 0), hsymm (0, I) (u, 0)] using congrArg ((2 : ℂ)⁻¹ • ·) hu

/-- **Holomorphy of iterated parameter derivatives.** If `H : X × ℂ → G` is `C^n` on an open
product `W ×ˢ V` and holomorphic in its complex variable on `V`, then for `k + 1 ≤ n` the `k`-th
parameter derivative `z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x` is holomorphic on `V` for
every `x ∈ W`. -/
theorem differentiableOn_iteratedFDeriv_partial {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H (W ×ˢ V)) (hW : IsOpen W) (hV : IsOpen V)
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {k : ℕ} (hk : k + 1 ≤ n) {x : X}
    (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x) V := by
  induction k generalizing x with
  | zero =>
    -- The zeroth derivative is `H` itself, read as a multilinear map in no variables.
    refine (((continuousMultilinearCurryFin0 ℝ X G).symm.toContinuousLinearEquiv : G →L[ℝ] _)
      |>.comp_differentiableOn_of_map_smul (fun c y ↦ by ext; simp) (hhol x hx)).congr
      fun z _ ↦ ?_
    ext
    simp
  | succ k ih =>
    -- The `(k+1)`-th derivative uncurries the parameter derivative of the `k`-th one, which is
    -- holomorphic since the `k`-th derivative is a `C²` family of holomorphic functions.
    have hHk := hH.contDiffOn_iteratedFDeriv_partial (hW.prod hV) (k := k) (m := 2)
      (by push_cast at hk; rwa [add_assoc, one_add_one_eq_two] at hk)
    have hD := differentiableOn_fderiv_partial hHk hW hV
      (fun x' hx' ↦ ih (le_trans (by norm_cast; omega) hk) hx') hx
    refine (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) G).symm
      |>.toContinuousLinearEquiv : _ →L[ℝ] _).comp_differentiableOn_of_map_smul
      (fun c f ↦ by ext; simp) hD).congr fun z _ ↦ ?_
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]

end ContDiffOn
