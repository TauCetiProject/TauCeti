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
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.ContDiff.ULift
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import TauCeti.Analysis.Normed.Operator.Bilinear

/-!
# Mixed derivatives and Cauchy estimates for holomorphic slices

Let `H : X × ℂ → G` be a map from the product of a real normed space `X` and the complex plane
into a complex normed space `G`, with finite-order real differentiability (`C²`, `C^(k+1)`, `C^n`
with `m + 1 ≤ n`, or `C^m`) on an open product `W ×ˢ V` and holomorphic in its complex variable on
`V` for every `x ∈ W`.

By symmetry of the second real Fréchet derivative, for `C²` maps `H` the total derivative
`z ↦ fderiv ℝ H (x, z)` is holomorphic on `V` (`TauCeti.differentiableOn_fderiv_comp_prodMk_right`),
and hence so is the first parameter derivative `z ↦ fderiv ℝ (fun x' ↦ H (x', z)) x`
(`TauCeti.differentiableOn_fderiv_prod_left`). Inductively, for `C^(k+1)` maps `H`, every iterated
parameter derivative `z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x` is holomorphic on `V`
(`TauCeti.differentiableOn_iteratedFDeriv_prod_left`), and complex differentiation in the second
variable commutes with real differentiation in the first variable
(`TauCeti.fderiv_prod_left_deriv_snd`, `TauCeti.iteratedFDeriv_prod_left_deriv_snd`) while shifting
joint regularity by one order (`TauCeti.contDiffOn_deriv_prod_snd`).

In parametric complex analysis, slicewise holomorphic approximation operators (such as finite-rank
Runge operators acting in `ℂ`) naturally yield uniform bounds on parameter-only derivatives
`iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x` rather than on mixed `(X × ℂ)` derivatives. Combining
the commutation identity with the first-order Cauchy estimate on circles upgrades those
parameter-only bounds on a closed disc `closedBall z r ⊆ V` into a zero-loss quantitative bound
for the total `m`-th real derivative of a `C^m` map `H`:

`‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B`

(`TauCeti.norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le`),
giving joint `C^m` convergence bounds for series of holomorphic corrections. Neither
finite-dimensionality of `X` nor completeness of `G` is required.

## Main results

* `TauCeti.differentiableOn_fderiv_comp_prodMk_right`: the total real derivative of a `C²` map
  `H` is holomorphic in the complex variable.
* `TauCeti.differentiableOn_fderiv_prod_left`: the first parameter derivative of a `C²` map `H`
  is holomorphic in the complex variable.
* `TauCeti.contDiffOn_deriv_prod_snd`: the complex derivative in the second variable of a `C^n`
  map `H` is `C^m` whenever `m + 1 ≤ n`.
* `TauCeti.differentiableOn_iteratedFDeriv_prod_left`: the `k`-th iterated parameter derivative
  of a `C^(k+1)` map `H` is holomorphic in the complex variable.
* `TauCeti.fderiv_prod_left_deriv_snd`: first-order commutation of the real parameter derivative
  with complex differentiation in the second variable.
* `TauCeti.iteratedFDeriv_prod_left_deriv_snd`: higher-order commutation of iterated real
  parameter derivatives with complex differentiation in the second variable.
* `TauCeti.norm_iteratedFDeriv_le_of_differentiableOn_of_norm_iteratedFDeriv_prod_left_le`: total
  `C^m` Cauchy bound from parameter-only derivative bounds on a closed disc.
-/

public section

open Complex Filter Metric Set Topology

universe u v

namespace TauCeti

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Auxiliary operator norm bounds -/

private theorem norm_compL_flip_fst_le (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ‖(ContinuousLinearMap.compL ℝ (X × ℂ) X G).flip (ContinuousLinearMap.fst ℝ X ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    simpa [ContinuousLinearMap.compL_apply] using
      (ContinuousLinearMap.opNorm_comp_le L (ContinuousLinearMap.fst ℝ X ℂ)).trans
        (mul_le_of_le_one_right (norm_nonneg L) (ContinuousLinearMap.norm_fst_le ℝ X ℂ))

private theorem norm_compL_flip_snd_comp_lsmul_le (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℂ G] :
    ‖((ContinuousLinearMap.compL ℝ (X × ℂ) ℂ G).flip (ContinuousLinearMap.snd ℝ X ℂ)).comp
        (ContinuousLinearMap.lsmul ℝ ℂ (E := G)).flip‖ ≤ 1 := by
  have h1 :
      ‖(ContinuousLinearMap.compL ℝ (X × ℂ) ℂ G).flip (ContinuousLinearMap.snd ℝ X ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
      simpa [ContinuousLinearMap.compL_apply] using
        (ContinuousLinearMap.opNorm_comp_le L (ContinuousLinearMap.snd ℝ X ℂ)).trans
          (mul_le_of_le_one_right (norm_nonneg L) (ContinuousLinearMap.norm_snd_le ℝ X ℂ))
  have h2 : ‖(ContinuousLinearMap.lsmul ℝ ℂ (E := G)).flip‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul h1 h2 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-! ### Holomorphy of derivatives in the complex variable -/

section HolomorphicDerivatives

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {W : Set X} {V : Set ℂ} {H : X × ℂ → G}

/-- For a map `H` that is `C¹` at `(x, z)` and complex differentiable in `z`, its real derivative
applied to `(0, 1)` is its complex derivative in the second variable. -/
private theorem fderiv_apply_zero_one_eq_deriv {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z) :
    fderiv ℝ H (x, z) (0, 1) = deriv (fun w ↦ H (x, w)) z := by
  have h1 : fderiv ℝ (fun w ↦ H (x, w)) z 1 = fderiv ℝ H (x, z) (0, 1) := by
    rw [fderiv_slice_right hH]
    rfl
  rw [← h1, (hhol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp

/-- **Holomorphy of the total derivative in a complex variable.** If `H : X × ℂ → G` is `C²` on an
open product `W ×ˢ V` and holomorphic in its complex variable on `V`, then `z ↦ fderiv ℝ H (x, z)`
is holomorphic on `V` for every `x ∈ W`. -/
theorem differentiableOn_fderiv_comp_prodMk_right (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ 2 H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ H (x, z)) V := by
  intro z hz
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hH2 : ContDiffAt ℝ 2 H (x, z) := hH.contDiffAt (hU.mem_nhds ⟨hx, hz⟩)
  have hDfd : DifferentiableAt ℝ (fderiv ℝ H) (x, z) :=
    (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hslice : DifferentiableAt ℝ (fun z' ↦ fderiv ℝ H (x, z')) z :=
    hDfd.comp z (hasFDerivAt_prodMk_right x z).differentiableAt
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hslice).2
    ?_).differentiableWithinAt
  refine ContinuousLinearMap.ext fun v ↦ ?_
  -- Differentiate the Cauchy–Riemann identity `p ↦ 2⁻¹ • (DH(p)(0, 1) + I • DH(p)(0, I)) = 0`.
  have h1 := (ContinuousLinearMap.apply ℝ G ((0 : X), (1 : ℂ))).hasFDerivAt.comp (x, z)
    hDfd.hasFDerivAt
  have hI := (ContinuousLinearMap.apply ℝ G ((0 : X), I)).hasFDerivAt.comp (x, z)
    hDfd.hasFDerivAt
  have hcr := (h1.add (hI.const_smul I)).const_smul (2 : ℂ)⁻¹
  have hzero : (fun p : X × ℂ ↦ (2 : ℂ)⁻¹ • (fderiv ℝ H p (0, 1) + I • fderiv ℝ H p (0, I))) =ᶠ[
      𝓝 (x, z)] fun _ ↦ (0 : G) := by
    filter_upwards [hU.mem_nhds ⟨hx, hz⟩] with p hp
    have hpd : DifferentiableAt ℝ H p :=
      (hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)
    have hphol : DifferentiableAt ℂ (fun w ↦ H (p.1, w)) p.2 :=
      (hhol p.1 hp.1).differentiableAt (hV.mem_nhds hp.2)
    have hsr (w : ℂ) : fderiv ℝ H p (0, w) = fderiv ℝ (fun ζ ↦ H (p.1, ζ)) p.2 w := by
      rw [fderiv_slice_right hpd]; rfl
    rw [hsr 1, hsr I]
    simpa [conjWirtingerDeriv_apply] using
      congrArg (fun L ↦ L 1) hphol.conjWirtingerDeriv_eq_zero
  have h0eq := (hasFDerivAt_const (0 : G) (x, z)).unique (hcr.congr_of_eventuallyEq hzero.symm)
  have hv0 := congrArg (fun L : X × ℂ →L[ℝ] G ↦ L v) h0eq
  have hsymm := hH2.isSymmSndFDerivAt (by norm_num)
  have hfs (w : ℂ) : fderiv ℝ (fun z' ↦ fderiv ℝ H (x, z')) z w =
      fderiv ℝ (fderiv ℝ H) (x, z) (0, w) :=
    congrArg (fun L ↦ L w) (hDfd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)).fderiv
  simp only [conjWirtingerDeriv_apply, smul_apply, add_apply, zero_apply, smul_eq_mul, mul_one,
    hfs, hsymm (0, 1) v, hsymm (0, I) v]
  simpa using hv0.symm

/-- If `H : X × ℂ → G` is `C²` on an open product `W ×ˢ V` and holomorphic in the second variable
on `V`, then its parameter derivative `z ↦ fderiv ℝ (fun x' ↦ H (x', z)) x` is holomorphic on `V`
for every `x ∈ W`. -/
theorem differentiableOn_fderiv_prod_left (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ 2 H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun x' ↦ H (x', z)) x) V := by
  have hcomp := ((ContinuousLinearMap.coprodEquivL ℂ).symm.differentiable.comp_differentiableOn
    (differentiableOn_fderiv_comp_prodMk_right hW hV hH hhol hx)).fst
  refine hcomp.congr fun z hz ↦ ?_
  have hHd : DifferentiableAt ℝ H (x, z) :=
    (hH.contDiffAt ((hW.prod hV).mem_nhds ⟨hx, hz⟩)).differentiableAt (by norm_num)
  rw [Function.comp_apply, ContinuousLinearMap.coprodEquivL_symm_apply]
  exact fderiv_slice_left hHd

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

private theorem differentiableOn_iteratedFDeriv_prod_left_aux (k : ℕ) :
    ∀ {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℂ G] {H : X × ℂ → G},
      IsOpen W → IsOpen V → ContDiffOn ℝ (k + 1 : ℕ) H (W ×ˢ V) →
      (∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) →
      ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x) V := by
  induction k with
  | zero =>
    intro G _ _ H _ _ _ hhol x hx
    have hcomp := (ContinuousMultilinearMap.uncurry0L ℝ ℂ X G).differentiable.comp_differentiableOn
      (hhol x hx)
    exact hcomp.congr fun z _ ↦ by
      rw [Function.comp_apply, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        ContinuousMultilinearMap.uncurry0L_apply]
      rfl
  | succ k ih =>
    intro G _ _ H hW hV hH hhol x hx
    have hH2 : ContDiffOn ℝ 2 H (W ×ˢ V) := hH.of_le (by norm_cast; omega)
    have hH1 : ContDiffOn ℝ (k + 1 : ℕ) (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1)
        (W ×ˢ V) :=
      ContDiffOn.fderiv_partial_of_isOpen (m := (k + 1 : ℕ)) (by exact_mod_cast hH) (hW.prod hV)
    have hH1hol : ∀ x' ∈ W,
        DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun y ↦ H (y, z)) x') V :=
      fun x' hx' ↦ differentiableOn_fderiv_prod_left hW hV hH2 hhol hx'
    have hrec := ih hW hV hH1 hH1hol x hx
    have hcomp :=
      (ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G).differentiable.comp_differentiableOn hrec
    exact hcomp.congr fun z _ ↦ by
      rw [Function.comp_apply, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        ContinuousMultilinearMap.uncurryRightL'_apply]

/-- **Holomorphy of iterated parameter derivatives.** If `H : X × ℂ → G` is `C^(k+1)` on an open
product `W ×ˢ V` and holomorphic in its complex variable on `V`, then
`z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x` is holomorphic on `V` for every `x ∈ W`. -/
theorem differentiableOn_iteratedFDeriv_prod_left (k : ℕ) (hW : IsOpen W) (hV : IsOpen V)
    (hH : ContDiffOn ℝ (k + 1 : ℕ) H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', z)) x) V := by
  have haux := differentiableOn_iteratedFDeriv_prod_left_aux.{u, v} k hW hV
    (contDiffOn_ulift_up_iff.mpr hH)
    (fun x' hx' ↦ differentiableOn_ulift_up_iff.mpr (hhol x' hx')) x hx
  let post := ContinuousLinearMap.compContinuousMultilinearMapMixedL ℝ ℂ
    (fun _ : Fin k ↦ X) (ULift.{u} G) G
    (ContinuousLinearEquiv.ulift : ULift.{u} G ≃L[ℂ] G).toContinuousLinearMap
  exact (post.differentiable.comp_differentiableOn haux).congr fun z _ ↦ by
    rw [Function.comp_apply, ContinuousLinearMap.compContinuousMultilinearMapMixedL_apply]
    exact (compContinuousMultilinearMap_ulift_iteratedFDeriv k (fun x' ↦ H (x', z)) x).symm

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
    (differentiableOn_fderiv_prod_left hW hV hH hhol hx).differentiableAt (hV.mem_nhds hz)
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

private theorem iteratedFDeriv_prod_left_deriv_snd_aux (k : ℕ) :
    ∀ {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℂ G] {H : X × ℂ → G},
      IsOpen W → IsOpen V → ContDiffOn ℝ (k + 1 : ℕ) H (W ×ˢ V) →
      (∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) →
      ∀ x ∈ W, ∀ z ∈ V,
        iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ H (x', w)) z) x =
          deriv (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x) z := by
  induction k with
  | zero =>
    intro G _ _ H _ hV _ hhol x hx z hz
    have hhd : HasDerivAt (fun w ↦ H (x, w)) (deriv (fun w ↦ H (x, w)) z) z :=
      ((hhol x hx).differentiableAt (hV.mem_nhds hz)).hasDerivAt
    have hfun : (fun w ↦ iteratedFDeriv ℝ 0 (fun x' ↦ H (x', w)) x) =
        (ContinuousMultilinearMap.uncurry0L ℝ ℂ X G) ∘ fun w ↦ H (x, w) := by
      ext w _
      simp [iteratedFDeriv_zero_eq_comp]
    rw [hfun, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    have h0 : (continuousMultilinearCurryFin0 ℝ X G).symm (deriv (fun w ↦ H (x, w)) z) =
        ContinuousMultilinearMap.uncurry0L ℝ ℂ X G (deriv (fun w ↦ H (x, w)) z) := by
      rw [ContinuousMultilinearMap.uncurry0L_apply]
      rfl
    rw [h0]
    exact ((ContinuousMultilinearMap.uncurry0L ℝ ℂ X G).hasFDerivAt.comp_hasDerivAt z
      hhd).deriv.symm
  | succ k ih =>
    intro G _ _ H hW hV hH hhol x hx z hz
    have hH2 : ContDiffOn ℝ 2 H (W ×ˢ V) := hH.of_le (by norm_cast; omega)
    have hH1 : ContDiffOn ℝ (k + 1 : ℕ) (fun p : X × ℂ ↦ fderiv ℝ (fun y ↦ H (y, p.2)) p.1)
        (W ×ˢ V) :=
      ContDiffOn.fderiv_partial_of_isOpen (m := (k + 1 : ℕ)) (by exact_mod_cast hH) (hW.prod hV)
    have hH1hol : ∀ x' ∈ W,
        DifferentiableOn ℂ (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x') V :=
      fun x' hx' ↦ differentiableOn_fderiv_prod_left hW hV hH2 hhol hx'
    have hhd : DifferentiableAt ℂ
        (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ fderiv ℝ (fun y ↦ H (y, w)) x') x) z :=
      (differentiableOn_iteratedFDeriv_prod_left k hW hV hH1 hH1hol hx).differentiableAt
        (hV.mem_nhds hz)
    have hL : iteratedFDeriv ℝ (k + 1) (fun x' ↦ deriv (fun w ↦ H (x', w)) z) x =
        ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G
          (iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x') z) x) := by
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        ← ContinuousMultilinearMap.uncurryRightL'_apply (𝕜 := ℝ) (𝕜' := ℂ)]
      refine congrArg (ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G)
        (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ k).self_of_nhds
      filter_upwards [hW.mem_nhds hx] with y hy
      exact fderiv_prod_left_deriv_snd hW hV hH2 hhol hy hz
    have hR : deriv (fun w ↦ iteratedFDeriv ℝ (k + 1) (fun x' ↦ H (x', w)) x) z =
        ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G
          (deriv (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ fderiv ℝ (fun y ↦ H (y, w)) x') x) z) := by
      have hfun : (fun w ↦ iteratedFDeriv ℝ (k + 1) (fun x' ↦ H (x', w)) x) =
          (ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G) ∘
            fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ fderiv ℝ (fun y ↦ H (y, w)) x') x := by
        ext w m; simp [iteratedFDeriv_succ_eq_comp_right]
      rw [hfun]
      exact ((ContinuousMultilinearMap.uncurryRightL' ℝ ℂ k X G).hasFDerivAt.comp_hasDerivAt z
        hhd.hasDerivAt).deriv
    rw [hL, hR, ih hW hV hH1 hH1hol x hx z hz]

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
  have hH' := contDiffOn_ulift_up_iff.mpr hH
  have hhol' : ∀ x' ∈ W, DifferentiableOn ℂ (fun w ↦ ULift.up.{u} (H (x', w))) V :=
    fun x' hx' ↦ differentiableOn_ulift_up_iff.mpr (hhol x' hx')
  have haux := iteratedFDeriv_prod_left_deriv_snd_aux.{u, v} k hW hV hH' hhol' x hx z hz
  let eC : ULift.{u} G ≃L[ℂ] G := ContinuousLinearEquiv.ulift
  let post := ContinuousLinearMap.compContinuousMultilinearMapMixedL ℝ ℂ
    (fun _ : Fin k ↦ X) (ULift.{u} G) G eC.toContinuousLinearMap
  have hL : post (iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ ULift.up.{u} (H (x', w))) z) x) =
      iteratedFDeriv ℝ k (fun x' ↦ deriv (fun w ↦ H (x', w)) z) x := by
    have heq : (fun x' ↦ deriv (fun w ↦ ULift.up.{u} (H (x', w))) z) =ᶠ[𝓝 x]
        fun x' ↦ ULift.up.{u} (deriv (fun w ↦ H (x', w)) z) := by
      filter_upwards [hW.mem_nhds hx] with y hy
      have hhd := (hhol y hy).differentiableAt (hV.mem_nhds hz)
      have hmap := (eC.symm.hasFDerivAt.comp_hasDerivAt z hhd.hasDerivAt).deriv
      have hcomp : (eC.symm : G → ULift.{u} G) ∘ (fun w ↦ H (y, w)) =
          fun w ↦ ULift.up.{u} (H (y, w)) := funext fun _ ↦ rfl
      rw [hcomp] at hmap
      exact hmap
    rw [(heq.iteratedFDeriv ℝ k).self_of_nhds]
    simp only [post, ContinuousLinearMap.compContinuousMultilinearMapMixedL_apply]
    exact compContinuousMultilinearMap_ulift_iteratedFDeriv (𝕜 := ℝ) k _ x
  have hR : post (deriv (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ ULift.up.{u} (H (x', w))) x) z) =
      deriv (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x) z := by
    have hhd := (differentiableOn_iteratedFDeriv_prod_left k hW hV hH' hhol' hx).differentiableAt
      (hV.mem_nhds hz)
    have hmap := (post.hasFDerivAt.comp_hasDerivAt z hhd.hasDerivAt).deriv
    have hcomp : (post : _ → _) ∘
        (fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ ULift.up.{u} (H (x', w))) x) =
        fun w ↦ iteratedFDeriv ℝ k (fun x' ↦ H (x', w)) x := funext fun w ↦ by
      simp only [Function.comp_apply, post,
        ContinuousLinearMap.compContinuousMultilinearMapMixedL_apply]
      exact compContinuousMultilinearMap_ulift_iteratedFDeriv (𝕜 := ℝ) k (fun x' ↦ H (x', w)) x
    rw [hcomp] at hmap
    exact hmap.symm
  rw [← hL, ← hR, haux]

/-! ### Joint `C^m` Cauchy bound from parameter-only derivatives -/

/-- Decomposition of the total real derivative of `H` on `W ×ˢ V` into its parameter derivative
and its complex derivative in the second variable. -/
private theorem fderiv_prod_eq_compL_fst_add_snd_lsmul {x : X} {z : ℂ}
    (hH : DifferentiableAt ℝ H (x, z)) (hhol : DifferentiableAt ℂ (fun w ↦ H (x, w)) z) :
    fderiv ℝ H (x, z) =
      (ContinuousLinearMap.compL ℝ (X × ℂ) X G).flip (ContinuousLinearMap.fst ℝ X ℂ)
          (fderiv ℝ (fun y ↦ H (y, z)) x) +
        ((ContinuousLinearMap.compL ℝ (X × ℂ) ℂ G).flip (ContinuousLinearMap.snd ℝ X ℂ)).comp
          (ContinuousLinearMap.lsmul ℝ ℂ (E := G)).flip (deriv (fun w ↦ H (x, w)) z) := by
  refine ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hH (u, v)]
  have hv : fderiv ℝ (fun w ↦ H (x, w)) z v = v • deriv (fun w ↦ H (x, w)) z := by
    rw [(hhol.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  rw [hv]
  simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.lsmul_apply]

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
    filter_upwards [hU.mem_nhds ⟨hx, hz⟩] with p hp
    exact fderiv_prod_eq_compL_fst_add_snd_lsmul
      ((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      ((hhol p.1 hp.1).differentiableAt (hV.mem_nhds hp.2))
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
        (mul_le_of_le_one_left (norm_nonneg _) (norm_compL_flip_fst_le (X := X) G)))
  · have h2 := sndSmul.iteratedFDeriv_comp_left hH₂at le_rfl
    exact (congrArg norm h2).le.trans
      ((sndSmul.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (norm_compL_flip_snd_comp_lsmul_le (X := X) G)))

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
    refine ih hW hV hH₁ (fun x' hx' ↦ differentiableOn_fderiv_prod_left hW hV hH2 hhol hx')
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
      ((differentiableOn_iteratedFDeriv_prod_left k hW hV hHk hhol hx).mono
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
