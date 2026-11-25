/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.ContDiff.ULift
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# Mixed derivatives and Cauchy estimates for holomorphic slices

Let `H : X × ℂ → G` be a map from the product of a real normed space `X` of parameters and the
complex plane into a complex normed space `G`. Suppose that `H` is jointly `C^n` on an open
product `W ×ˢ V`, and that `z ↦ H (x, z)` is holomorphic on `V` for every `x ∈ W`.

At any point `(x, z)` where `H` is real differentiable and `w ↦ H (x, w)` is complex
differentiable, the real Fréchet derivative `fderiv ℝ H (x, z)` evaluates on `(0, w)` to
`w • deriv (H (x, ·)) z` (`TauCeti.fderiv_apply_mk_zero_eq_smul_deriv`,
`TauCeti.fderiv_apply_zero_one_eq_deriv`) and splits along the standard coordinate projections into
its parameter derivative and complex slice derivative
(`TauCeti.fderiv_eq_comp_fst_add_lsmul_comp_snd`,
`TauCeti.fderiv_apply_eq_fderiv_slice_left_add_smul_deriv`).

The first-order holomorphy result (`ContDiffOn.differentiableOn_fderiv_partial`) is the symmetry of
the second derivative of a `C²` map: the Cauchy–Riemann equation
`DH(p) (0, I) = I • DH(p) (0, 1)` for the real derivative `DH(p)` of `H` holds at every point `p`
of `W ×ˢ V`, and differentiating it in a parameter direction gives the Cauchy–Riemann equation for
the parameter derivative. Higher orders follow by induction
(`ContDiffOn.differentiableOn_iteratedFDeriv_partial`), since the parameter derivatives are again
jointly smooth (`ContDiffOn.contDiffOn_iteratedFDeriv_partial`). Complex differentiation in the
second variable also commutes with real differentiation in the first variable
(`TauCeti.fderiv_prod_left_deriv_snd`, `TauCeti.iteratedFDeriv_prod_left_deriv_snd`) while shifting
joint regularity by one order (`TauCeti.contDiffOn_deriv_prod_snd`).

In parametric complex analysis, slicewise holomorphic approximation operators (such as finite-rank
Runge operators acting in `ℂ`, `TauCeti.Analysis.Complex.Runge.Parameter`) naturally yield uniform
bounds on parameter-only derivatives `iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x` rather than on
mixed `(X × ℂ)` derivatives. Combining the commutation identity with the first-order Cauchy estimate
on circles upgrades those parameter-only bounds on a closed disc `closedBall z r ⊆ V` into a
zero-loss quantitative bound for the total `m`-th real derivative of a `C^m` map `H`:

`‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B`

(`TauCeti.norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le`),
giving joint `C^m` convergence bounds for series of holomorphic corrections. Neither
finite-dimensionality of `X` nor completeness of `G` is required.

The approach to parameter-derivative holomorphy follows the mixed-derivative calculus of Tau Ceti
pull request 43183.

## Main results

* `ContDiffOn.differentiableOn_fderiv_partial`: the first parameter derivative of a `C²` map `H`
  is holomorphic in the complex variable.
* `ContDiffOn.differentiableOn_iteratedFDeriv_partial`: the `k`-th iterated parameter derivative
  of a `C^n` map `H` (`k + 1 ≤ n`) is holomorphic in the complex variable.
* `TauCeti.fderiv_apply_mk_zero_eq_smul_deriv` and `TauCeti.fderiv_apply_zero_one_eq_deriv`:
  evaluation of `fderiv ℝ H (x, z)` on `(0, w)` and `(0, 1)` in terms of the complex slice
  derivative.
* `TauCeti.fderiv_eq_comp_fst_add_lsmul_comp_snd` and
  `TauCeti.fderiv_apply_eq_fderiv_slice_left_add_smul_deriv`: splitting of `fderiv ℝ H (x, z)`
  into its parameter derivative and complex slice derivative along standard projections.
* `TauCeti.contDiffOn_deriv_prod_snd`: the complex derivative in the second variable of a `C^n`
  map `H` is `C^m` whenever `m + 1 ≤ n`.
* `TauCeti.fderiv_prod_left_deriv_snd` and `TauCeti.iteratedFDeriv_prod_left_deriv_snd`:
  commutation of real parameter derivatives with complex differentiation in the second variable.
* `TauCeti.norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le`: total
  `C^m` Cauchy bound from parameter-only derivative bounds on a closed disc.
-/

public section

open Complex Filter Metric Set Topology TauCeti

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

universe u v

namespace TauCeti

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

section HolomorphicDerivatives

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {W : Set X} {V : Set ℂ} {H : X × ℂ → G}

/-! ### Splitting of the total derivative and regularity of the slice derivative -/

/-- For a map `H` that is real differentiable at `(x, z)` and complex differentiable in `z`, its
real derivative applied to `(0, w)` is `w` times its complex derivative in the second variable. -/
theorem fderiv_apply_mk_zero_eq_smul_deriv {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z)
    (w : ℂ) :
    fderiv ℝ H (x, z) (0, w) = w • deriv (fun w' ↦ H (x, w')) z := by
  have h1 : fderiv ℝ (fun w' ↦ H (x, w')) z w = fderiv ℝ H (x, z) (0, w) := by
    rw [fderiv_slice_right hH]
    rfl
  rw [← h1, (hhol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp

/-- For a map `H` that is real differentiable at `(x, z)` and complex differentiable in `z`, its
real derivative applied to `(0, 1)` is its complex derivative in the second variable. -/
theorem fderiv_apply_zero_one_eq_deriv {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z) :
    fderiv ℝ H (x, z) (0, 1) = deriv (fun w ↦ H (x, w)) z := by
  simpa using fderiv_apply_mk_zero_eq_smul_deriv hH hhol 1

/-- Splitting of the total real derivative of `H` at `(x, z)` along the standard coordinate
projections into its parameter derivative and complex derivative in the second variable. -/
theorem fderiv_eq_comp_fst_add_lsmul_comp_snd {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z) :
    fderiv ℝ H (x, z) =
      (fderiv ℝ (fun y ↦ H (y, z)) x).comp (ContinuousLinearMap.fst ℝ X ℂ) +
        ((ContinuousLinearMap.lsmul ℝ ℂ (E := G)).flip (deriv (fun w ↦ H (x, w)) z)).comp
          (ContinuousLinearMap.snd ℝ X ℂ) := by
  refine ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hH (u, v)]
  have hv : fderiv ℝ (fun w ↦ H (x, w)) z v = v • deriv (fun w ↦ H (x, w)) z := by
    rw [(hhol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  simp [hv]

/-- Evaluation of the total real derivative of `H` at `(x, z)` on `v : X × ℂ` as the parameter
derivative on `v.1` plus `v.2` times the complex slice derivative. -/
theorem fderiv_apply_eq_fderiv_slice_left_add_smul_deriv {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z)
    (v : X × ℂ) :
    fderiv ℝ H (x, z) v =
      fderiv ℝ (fun y ↦ H (y, z)) x v.1 + v.2 • deriv (fun w ↦ H (x, w)) z := by
  simpa using congrArg (fun L : X × ℂ →L[ℝ] G ↦ L v)
    (fderiv_eq_comp_fst_add_lsmul_comp_snd hH hhol)

/-- If `H : X × ℂ → G` is `C^n` on an open product `W ×ˢ V` with `m + 1 ≤ n` and holomorphic in
its complex variable on `V`, then its complex derivative `(x, z) ↦ deriv (H (x, ·)) z` is `C^m` on
`W ×ˢ V`. -/
theorem contDiffOn_deriv_prod_snd {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n) (hW : IsOpen W)
    (hV : IsOpen V) (hH : ContDiffOn ℝ n H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) :
    ContDiffOn ℝ m (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (W ×ˢ V) := by
  intro p hp
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have h1 : ContDiffAt ℝ m (fun q : X × ℂ ↦ fderiv ℝ (fun w ↦ H (q.1, w)) q.2 1) p :=
    (hH.contDiffAt (hU.mem_nhds hp)).fderiv_snd_apply hmn (1 : ℂ)
  refine (h1.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hp] with q hq
  have hhd := (hhol q.1 hq.1).differentiableAt (hV.mem_nhds hq.2)
  rw [(hhd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp

/-! ### Commutation of real parameter derivatives with complex differentiation -/

/-- **First-order commutation of parameter and complex derivatives.** If `H : X × ℂ → G` is `C²`
on an open product `W ×ˢ V` and holomorphic in its complex variable on `V`, then for every
`x ∈ W` and `z ∈ V`,
`fderiv ℝ (fun y ↦ deriv (H (y, ·)) z) x = deriv (fun w ↦ fderiv ℝ (H (·, w)) x) z`. -/
theorem fderiv_prod_left_deriv_snd (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ 2 H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    (hz : z ∈ V) :
    fderiv ℝ (fun y ↦ deriv (fun w ↦ H (y, w)) z) x =
      deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x) z := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hH2 : ContDiffAt ℝ 2 H (x, z) := hH.contDiffAt (hU.mem_nhds ⟨hx, hz⟩)
  have hDfd : DifferentiableAt ℝ (fderiv ℝ H) (x, z) :=
    (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hholD : DifferentiableAt ℂ (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x) z :=
    (hH.differentiableOn_fderiv_partial hW hV hhol hx).differentiableAt (hV.mem_nhds hz)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hL_eq : (fun y ↦ deriv (fun w ↦ H (y, w)) z) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ H (y, z) (0, 1) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (fderiv_apply_zero_one_eq_deriv
      ((hH.contDiffAt (hU.mem_nhds ⟨hy, hz⟩)).differentiableAt (by norm_num))
      ((hhol y hy).differentiableAt (hV.mem_nhds hz))).symm
  have hL_deriv := (ContinuousLinearMap.apply ℝ G ((0 : X), (1 : ℂ))).hasFDerivAt.comp x
    (hDfd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z))
  have hLHS : fderiv ℝ (fun y ↦ deriv (fun w ↦ H (y, w)) z) x v =
      fderiv ℝ (fderiv ℝ H) (x, z) (v, 0) (0, 1) :=
    congrArg (fun L ↦ L v) (hL_eq.fderiv_eq.trans hL_deriv.fderiv)
  have hR_eq : (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x v) =ᶠ[𝓝 z]
      fun w ↦ fderiv ℝ H (x, w) (v, 0) := by
    filter_upwards [hV.mem_nhds hz] with w hw
    have hHd : DifferentiableAt ℝ H (x, w) :=
      (hH.contDiffAt (hU.mem_nhds ⟨hx, hw⟩)).differentiableAt (by norm_num)
    rw [fderiv_slice_left hHd]; rfl
  have hR_comp : (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x v) =
      (ContinuousLinearMap.applyMixed ℝ ℂ G v) ∘ fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x :=
    funext fun _ ↦ (ContinuousLinearMap.applyMixed_apply v _).symm
  have hR_eval : deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x) z v =
      deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x v) z := by
    rw [hR_comp, ← ContinuousLinearMap.applyMixed_apply (𝕜 := ℝ) (𝕜' := ℂ) v]
    exact ((ContinuousLinearMap.applyMixed ℝ ℂ G v).hasFDerivAt.comp_hasDerivAt z
      hholD.hasDerivAt).deriv.symm
  have hR_real := (ContinuousLinearMap.apply ℝ G (v, (0 : ℂ))).hasFDerivAt.comp z
    (hDfd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z))
  have hR_hol : DifferentiableAt ℂ (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x v) z := by
    rw [hR_comp]
    exact (ContinuousLinearMap.applyMixed ℝ ℂ G v).differentiableAt.comp z hholD
  have hRHS : deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x) z v =
      fderiv ℝ (fderiv ℝ H) (x, z) (0, 1) (v, 0) := by
    rw [hR_eval]
    have h1 := ((hR_hol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).congr_of_eventuallyEq
      hR_eq.symm).unique hR_real
    simpa using congrArg (fun L : ℂ →L[ℝ] G ↦ L 1) h1
  rw [hLHS, hRHS, (hH2.isSymmSndFDerivAt (by norm_num)) (v, 0) (0, 1)]

private theorem deriv_comp_of_map_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    (L : E →L[ℝ] F) (hL : ∀ (c : ℂ) (y : E), L (c • y) = c • L y)
    {f : ℂ → E} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    deriv (fun w ↦ L (f w)) z = L (deriv f z) :=
  ({ toFun := L, map_add' := L.map_add, map_smul' := hL, cont := L.continuous } :
    E →L[ℂ] F).hasFDerivAt.comp_hasDerivAt z hf.hasDerivAt |>.deriv

/-- **Commutation of parameter derivatives with complex differentiation.** If `H : X × ℂ → G` is
`C^(k+1)` on an open product `W ×ˢ V` and holomorphic in its complex variable on `V`, then for
every `x ∈ W` and `z ∈ V`, taking the `k`-th real derivative in `x` commutes with complex
differentiation in `z`. -/
theorem iteratedFDeriv_prod_left_deriv_snd (k : ℕ) (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ (k + 1 : ℕ) H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    (hz : z ∈ V) :
    iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ H (x', w)) z) x =
      deriv (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x) z := by
  induction k generalizing x with
  | zero =>
    let e0 : G →L[ℝ] (X [×0]→L[ℝ] G) :=
      (continuousMultilinearCurryFin0 ℝ X G).symm.toContinuousLinearEquiv
    have he0 : ∀ (c : ℂ) (y : G), e0 (c • y) = c • e0 y := fun c y ↦ by ext; simp [e0]
    have hfun : (fun w ↦ iteratedFDeriv ℝ 0 (fun x' ↦ H (x', w)) x) = fun w ↦ e0 (H (x, w)) := by
      ext w _
      simp [e0, iteratedFDeriv_zero_eq_comp]
    rw [hfun, deriv_comp_of_map_smul e0 he0 ((hhol x hx).differentiableAt (hV.mem_nhds hz))]
    ext _
    simp [e0, iteratedFDeriv_zero_eq_comp]
  | succ k ih =>
    have hHk : ContDiffOn ℝ 2 (fun p : X × ℂ ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', p.2)) p.1)
        (W ×ˢ V) :=
      hH.contDiffOn_iteratedFDeriv_partial (hW.prod hV) (k := k) (m := 2) (by norm_cast)
    have hHk_hol : ∀ x' ∈ W,
        DifferentiableOn ℂ (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x') V :=
      fun x' hx' ↦ hH.differentiableOn_iteratedFDeriv_partial hW hV hhol (by norm_cast; omega) hx'
    let eL : (X →L[ℝ] X [×k]→L[ℝ] G) →L[ℝ] (X [×k + 1]→L[ℝ] G) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) G).symm
        |>.toContinuousLinearEquiv
    have heL : ∀ (c : ℂ) (L : X →L[ℝ] X [×k]→L[ℝ] G), eL (c • L) = c • eL L :=
      fun c L ↦ by ext m; rfl
    have hev : iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ H (x', w)) z) =ᶠ[𝓝 x]
        fun x' ↦ deriv (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x') z := by
      filter_upwards [hW.mem_nhds hx] with y hy
      exact ih (hH.of_le (by norm_cast; omega)) hy
    have hLHS : iteratedFDeriv ℝ (k + 1) (fun x' ↦ deriv (fun w ↦ H (x', w)) z) x =
        eL (deriv (fun w ↦ fderiv ℝ (fun x' ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x') x) z) := by
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq,
        fderiv_prod_left_deriv_snd hW hV hHk hHk_hol hx hz]
      rfl
    have hfun : (fun w ↦ iteratedFDeriv ℝ (k + 1) (fun x' ↦ H (x', w)) x) =
        fun w ↦ eL (fderiv ℝ (fun x' ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x') x) := by
      ext w : 1
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      rfl
    rw [hLHS, hfun, deriv_comp_of_map_smul eL heL
      ((hHk.differentiableOn_fderiv_partial hW hV hHk_hol hx).differentiableAt (hV.mem_nhds hz))]

/-! ### Joint `C^m` Cauchy bound from parameter-only derivatives -/

/-- Splitting the `(m + 1)`-th total derivative norm of `H` at `(x, z)` into the `m`-th total
derivative norms of its first-order parameter and complex derivatives. -/
private theorem norm_iteratedFDeriv_succ_prod_le {m : ℕ} (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ (m + 1 : ℕ) H (W ×ˢ V))
    (hhol : ∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ H (x', w)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ (m + 1) H (x, z)‖ ≤
      ‖iteratedFDeriv ℝ m (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1) (x, z)‖ +
        ‖iteratedFDeriv ℝ m (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (x, z)‖ := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  let precompFst := (ContinuousLinearMap.compL ℝ (X × ℂ) X G).flip (ContinuousLinearMap.fst ℝ X ℂ)
  let sndSmul := ((ContinuousLinearMap.compL ℝ (X × ℂ) ℂ G).flip
    (ContinuousLinearMap.snd ℝ X ℂ)).comp (ContinuousLinearMap.lsmul ℝ ℂ (E := G)).flip
  let H₁ : X × ℂ → (X →L[ℝ] G) := fun p ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1
  let H₂ : X × ℂ → G := fun p ↦ deriv (fun w ↦ H (p.1, w)) p.2
  have hH₁at : ContDiffAt ℝ m H₁ (x, z) :=
    (ContDiffOn.fderiv_partial_of_isOpen (m := (m : ℕ)) (by exact_mod_cast hH) hU).contDiffAt
      (hU.mem_nhds ⟨hx, hz⟩)
  have hH₂at : ContDiffAt ℝ m H₂ (x, z) :=
    (contDiffOn_deriv_prod_snd (by norm_cast) hW hV hH hhol).contDiffAt (hU.mem_nhds ⟨hx, hz⟩)
  have hfeq : fderiv ℝ H =ᶠ[𝓝 (x, z)] fun p ↦ precompFst (H₁ p) + sndSmul (H₂ p) := by
    filter_upwards [hU.mem_nhds ⟨hx, hz⟩] with ⟨y, w⟩ hp
    rw [fderiv_eq_comp_fst_add_lsmul_comp_snd
      ((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      ((hhol y hp.1).differentiableAt (hV.mem_nhds hp.2))]
    exact ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ by
      simp [precompFst, sndSmul, H₁, H₂, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.lsmul_apply]
  have hcd1 : ContDiffAt ℝ m (fun p ↦ precompFst (H₁ p)) (x, z) :=
    precompFst.contDiff.contDiffAt.comp _ hH₁at
  have hcd2 : ContDiffAt ℝ m (fun p ↦ sndSmul (H₂ p)) (x, z) :=
    sndSmul.contDiff.contDiffAt.comp _ hH₂at
  rw [← norm_iteratedFDeriv_fderiv, (hfeq.iteratedFDeriv ℝ m).self_of_nhds,
    fun_iteratedFDeriv_add_apply hcd1 hcd2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h1 := precompFst.iteratedFDeriv_comp_left hH₁at le_rfl
    exact (congrArg norm h1).le.trans
      ((precompFst.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_of_le_one_left (norm_nonneg _)
          (ContinuousLinearMap.norm_compL_flip_fst_le (𝕜 := ℝ) (E := X) (F := ℂ) (G := G))))
  · have h2 := sndSmul.iteratedFDeriv_comp_left hH₂at le_rfl
    exact (congrArg norm h2).le.trans
      ((sndSmul.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_of_le_one_left (norm_nonneg _)
          (ContinuousLinearMap.norm_compL_flip_snd_comp_lsmul_le
            (𝕜 := ℝ) (E := X) (R := ℂ) (G := G))))

/-- Inductive step from order `m + 1` to order `m + 2` in the total `C^m` Cauchy bound, applying
the induction hypothesis on the half-radius disc `closedBall z (r / 2)` to both `fderiv_x H` and
`deriv_z H`. -/
private theorem norm_iteratedFDeriv_prod_le_step {m : ℕ}
    (ih : ∀ {G' : Type max u v} [NormedAddCommGroup G'] [NormedSpace ℂ G'] {H' : X × ℂ → G'}
      {x : X} {z : ℂ} {r B : ℝ},
      IsOpen W → IsOpen V → ContDiffOn ℝ (m + 1 : ℕ) H' (W ×ˢ V) →
      (∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ H' (x', w)) V) →
      x ∈ W → 0 < r → closedBall z r ⊆ V →
      (∀ k ≤ m + 1, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun x' ↦ H' (x', w)) x‖ ≤ B) →
      ‖iteratedFDeriv ℝ (m + 1) H' (x, z)‖ ≤ (1 + (2 : ℝ) ^ (m + 1) / r) ^ (m + 1) * B)
    {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℂ G] {H : X × ℂ → G}
    {x : X} {z : ℂ} {r B : ℝ} (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ (m + 2 : ℕ) H (W ×ˢ V))
    (hhol : ∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ H (x', w)) V)
    (hx : x ∈ W) (hr : 0 < r) (hball : closedBall z r ⊆ V)
    (hB : ∀ k ≤ m + 2, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ (m + 2) H (x, z)‖ ≤ (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 2) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) z (mem_closedBall_self hr.le))
  have hH2 : ContDiffOn ℝ 2 H (W ×ˢ V) := hH.of_le (by norm_cast; omega)
  have hH₁ : ContDiffOn ℝ (m + 1 : ℕ)
      (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1) (W ×ˢ V) :=
    ContDiffOn.fderiv_partial_of_isOpen (m := (m + 1 : ℕ)) (by exact_mod_cast hH) (hW.prod hV)
  have hH₂ : ContDiffOn ℝ (m + 1 : ℕ)
      (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (W ×ˢ V) :=
    contDiffOn_deriv_prod_snd (by norm_cast) hW hV hH hhol
  have hhalf : closedBall z (r / 2) ⊆ V :=
    (closedBall_subset_closedBall (half_le_self hr.le)).trans hball
  have hbound₁ : ‖iteratedFDeriv ℝ (m + 1)
      (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1) (x, z)‖ ≤
      (1 + (2 : ℝ) ^ (m + 1) / (r / 2)) ^ (m + 1) * B := by
    refine ih hW hV hH₁ (fun x' hx' ↦ hH2.differentiableOn_fderiv_partial hW hV hhol hx')
      hx (half_pos hr) hhalf fun k hk w hw ↦ ?_
    simpa [norm_iteratedFDeriv_fderiv] using hB (k + 1) (Nat.add_le_add_right hk 1) w
      (closedBall_subset_closedBall (half_le_self hr.le) hw)
  have hbound₂ : ‖iteratedFDeriv ℝ (m + 1)
      (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (x, z)‖ ≤
      (1 + (2 : ℝ) ^ (m + 1) / (r / 2)) ^ (m + 1) * ((2 / r) * B) := by
    refine ih hW hV hH₂ (fun x' hx' ↦
      (hH2.comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw ↦ ⟨hx', hw⟩
        ).differentiableOn_complex_deriv hV (hhol x' hx'))
      hx (half_pos hr) hhalf fun k hk w hw ↦ ?_
    have hHk : ContDiffOn ℝ (k + 1 : ℕ) H (W ×ˢ V) := hH.of_le (by norm_cast; omega)
    rw [iteratedFDeriv_prod_left_deriv_snd k hW hV hHk hhol hx (hhalf hw)]
    have hsub : closedBall w (r / 2) ⊆ closedBall z r :=
      closedBall_subset_closedBall' (by linarith [mem_closedBall.1 hw])
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      ((hHk.differentiableOn_iteratedFDeriv_partial hW hV hhol le_rfl hx).mono
        (closure_ball_subset_closedBall.trans (hsub.trans hball))).diffContOnCl
      fun ζ hζ ↦ hB k (by omega) ζ (hsub (sphere_subset_closedBall hζ))
    exact hc.trans_eq (by ring)
  have hpow : (2 : ℝ) ^ (m + 1) / (r / 2) = (2 : ℝ) ^ (m + 2) / r := by field_simp; ring
  have h2le : (2 : ℝ) / r ≤ (2 : ℝ) ^ (m + 2) / r := by
    refine div_le_div_of_nonneg_right ?_ hr.le
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 2)
  have hsplit := norm_iteratedFDeriv_succ_prod_le hW hV hH hhol hx
    (hball (mem_closedBall_self hr.le))
  calc
    ‖iteratedFDeriv ℝ (m + 2) H (x, z)‖
        ≤ (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 1) * B +
          (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 1) * ((2 / r) * B) := by
      rw [← hpow]
      exact hsplit.trans (add_le_add hbound₁ hbound₂)
    _ = (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 1) * (1 + 2 / r) * B := by ring
    _ ≤ (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 1) * (1 + (2 : ℝ) ^ (m + 2) / r) * B := by gcongr
    _ = (1 + (2 : ℝ) ^ (m + 2) / r) ^ (m + 2) * B := by ring

private theorem norm_iteratedFDeriv_prod_le_aux (m : ℕ) :
    ∀ {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℂ G] {H : X × ℂ → G}
      {x : X} {z : ℂ} {r B : ℝ},
      IsOpen W → IsOpen V → ContDiffOn ℝ m H (W ×ˢ V) →
      (∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ H (x', w)) V) →
      x ∈ W → 0 < r → closedBall z r ⊆ V →
      (∀ k ≤ m, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x‖ ≤ B) →
      ‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + (2 : ℝ) ^ m / r) ^ m * B := by
  induction m with
  | zero =>
    intro G _ _ H x z r B _ _ _ _ _ hr _ hB
    simpa [norm_iteratedFDeriv_zero] using hB 0 le_rfl z (mem_closedBall_self hr.le)
  | succ m ih =>
    intro G _ _ H x z r B hW hV hH hhol hx hr hball hB
    rcases m with _ | m
    · have hB0 : 0 ≤ B :=
        (norm_nonneg _).trans (hB 0 (Nat.zero_le _) z (mem_closedBall_self hr.le))
      have hsplit := norm_iteratedFDeriv_succ_prod_le hW hV hH hhol hx
        (hball (mem_closedBall_self hr.le))
      have h1 : ‖iteratedFDeriv ℝ 0 (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1) (x, z)‖
          ≤ B := by
        simpa [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] using
          hB 1 le_rfl z (mem_closedBall_self hr.le)
      have h2 : ‖iteratedFDeriv ℝ 0 (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (x, z)‖
          ≤ (2 / r) * B := by
        rw [norm_iteratedFDeriv_zero]
        have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
          ((hhol x hx).mono (closure_ball_subset_closedBall.trans hball)).diffContOnCl
          fun w hw ↦ by
            simpa [norm_iteratedFDeriv_zero] using
              hB 0 (Nat.zero_le _) w (sphere_subset_closedBall hw)
        calc
          ‖deriv (fun w ↦ H (x, w)) z‖ ≤ B / r := hc
          _ ≤ (2 / r) * B := by
            rw [div_mul_eq_mul_div, mul_comm]
            exact div_le_div_of_nonneg_right (by linarith) hr.le
      calc
        ‖iteratedFDeriv ℝ 1 H (x, z)‖ ≤ B + (2 / r) * B := hsplit.trans (add_le_add h1 h2)
        _ = (1 + (2 : ℝ) ^ 1 / r) ^ 1 * B := by ring
    · exact norm_iteratedFDeriv_prod_le_step ih hW hV hH hhol hx hr hball hB

/-- **Total `C^m` Cauchy bound from parameter-only derivatives.** Let `H : X × ℂ → G` be `C^m` on
an open product `W ×ˢ V` and holomorphic in its complex variable on `V`. For `x ∈ W`, if
`closedBall z r ⊆ V` with `0 < r` and all parameter derivatives
`iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x` (`k ≤ m`) are bounded by `B` on `closedBall z r`, then
the total `m`-th real derivative of `H` at `(x, z)` satisfies
`‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B`. -/
theorem norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le
    (m : ℕ) (hW : IsOpen W) (hV : IsOpen V) (hH : ContDiffOn ℝ m H (W ×ˢ V))
    (hhol : ∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ H (x', w)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    {r B : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ V)
    (hB : ∀ k ≤ m, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + (2 : ℝ) ^ m / r) ^ m * B := by
  have haux := norm_iteratedFDeriv_prod_le_aux.{u, v} m hW hV (contDiffOn_ulift_up_iff.mpr hH)
    (fun x' hx' ↦ differentiableOn_ulift_up_iff.mpr (hhol x' hx')) hx hr hball
    fun k hk w hw ↦ by
      rw [norm_iteratedFDeriv_ulift_up]
      exact hB k hk w hw
  rwa [norm_iteratedFDeriv_ulift_up] at haux

end HolomorphicDerivatives

end TauCeti
