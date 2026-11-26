/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Complex.Parameter.Deriv
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Parameter derivatives of families of holomorphic functions

Let `H : X × ℂ → G` be a map from the product of a real normed space `X` of parameters and the
complex plane into a complex normed space `G`. Suppose that `H` is jointly `C^n` on an open
product `W ×ˢ V`, and that `z ↦ H (x, z)` is holomorphic on `V` for every `x ∈ W`.

If `H` is `C²`, then its total real derivative `z ↦ fderiv ℝ H (x, z)` is holomorphic on `V`
(`ContDiffOn.differentiableOn_fderiv_comp_prodMk`). This is the symmetry of the second derivative:
the Cauchy–Riemann equation `DH(p) (0, I) = I • DH(p) (0, 1)` holds at every point `p` of
`W ×ˢ V`, and differentiating it in any direction gives the Cauchy–Riemann equation for
`z ↦ DH(x, z)`. Restricting `DH` to the second factor, the complex derivative `deriv (H (x, ·))`
is holomorphic in `z` as well (`ContDiffOn.differentiableOn_deriv_snd`), and it is jointly `C^m`
for `m + 1 ≤ n` (`ContDiffOn.contDiffOn_deriv_snd`). For a
single function, the complex derivative of a real `C²` holomorphic function is holomorphic without
any completeness of `G` (`ContDiffOn.differentiableOn_deriv`).

Every parameter derivative of order `k < n` is again holomorphic in `z`
(`ContDiffOn.differentiableOn_iteratedFDeriv_slice`), and it commutes with the complex derivative
(`ContDiffOn.iteratedFDeriv_deriv_comm`).

Holomorphy of parameter derivatives is what lets estimates for holomorphic functions of `z`,
such as Runge approximation (`TauCeti.Analysis.Complex.Runge.Parameter`), be applied to every
parameter derivative of a family. Such estimates bound parameter derivatives only. The Cauchy
estimates recover from them every mixed derivative in `(x, z)`: if `H` is `C^m`, `0 < r`,
`closedBall z r ⊆ V` and the parameter derivatives of order at most `m` at `x` are bounded by `B`
on `closedBall z r`, then
`‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B`
(`ContDiffOn.norm_iteratedFDeriv_le_of_norm_iteratedFDeriv_partial_le`). Neither
finite-dimensionality of `X` nor completeness of `G` is needed. The proof splits off one
derivative at a time: the derivative of `(x, z) ↦ ∂ₓʲ H (x, z)` consists of `∂ₓʲ⁺¹ H` and
`∂_z ∂ₓʲ H = ∂ₓʲ ∂_z H`, and the Cauchy estimate on a circle of radius `r / 2` bounds the
parameter derivatives of `∂_z H` on `closedBall z (r / 2)` by `2 / r` times those of `H` on
`closedBall z r`.

Such bounds give convergence of all derivatives of series of holomorphic corrections with
parameters, as in the construction of solutions of the inhomogeneous Cauchy–Riemann equation
depending smoothly or holomorphically on parameters by exhaustion.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I, Section 1.2 (the Cauchy inequalities) and Theorem 1.4.4 (the
  inhomogeneous Cauchy–Riemann equation on an open subset of the plane).

The approach follows the mixed-derivative calculus of Tau Ceti pull request 43183.
-/

public section

open Complex Filter Metric Set Topology TauCeti

namespace ContDiffOn

variable {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup G]
  [NormedSpace ℂ G] {W : Set X} {V : Set ℂ} {H : X × ℂ → G}

/-! ### Holomorphy of derivatives in the parameters and in the complex variable -/

/-- **Holomorphy of the total derivative.** If `H : X × ℂ → G` is `C²` on an open product
`W ×ˢ V` and holomorphic in its complex variable on `V`, then its total real derivative
`z ↦ fderiv ℝ H (x, z)` is holomorphic on `V` for every `x ∈ W`. -/
theorem differentiableOn_fderiv_comp_prodMk (hH : ContDiffOn ℝ 2 H (W ×ˢ V)) (hW : IsOpen W)
    (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X}
    (hx : x ∈ W) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ H (x, z)) V := by
  intro z hz
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hH2 : ContDiffAt ℝ 2 H (x, z) := hH.contDiffAt (hU.mem_nhds ⟨hx, hz⟩)
  have hDH : DifferentiableAt ℝ (fderiv ℝ H) (x, z) :=
    (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hslice : HasFDerivAt (fun z' ↦ fderiv ℝ H (x, z'))
      ((fderiv ℝ (fderiv ℝ H) (x, z)).comp (ContinuousLinearMap.inr ℝ X ℂ)) z :=
    hDH.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
    hslice.differentiableAt).2 ?_).differentiableWithinAt
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
      rw [← this, hphol.fderiv_restrictScalars_eq_smul_deriv ℝ]
    rw [hsr, hsr, smul_smul, I_mul_I, neg_one_smul, one_smul, add_neg_cancel]
  -- Differentiating it in a direction `v` and using symmetry of `D²H` gives the claim.
  have hDcr := ((ContinuousLinearMap.apply ℝ G ((0 : X), (1 : ℂ))).hasFDerivAt.comp (x, z)
    hDH.hasFDerivAt).add (((ContinuousLinearMap.apply ℝ G ((0 : X), I)).hasFDerivAt.comp (x, z)
      hDH.hasFDerivAt).const_smul I)
  have h0 := (hDcr.congr_of_eventuallyEq hcr.symm).unique (hasFDerivAt_const (0 : G) (x, z))
  have hsymm := hH2.isSymmSndFDerivAt (by simp)
  rw [conjWirtingerDeriv_apply, hslice.fderiv]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv := congrArg (fun L : X × ℂ →L[ℝ] G ↦ L v) h0
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, smul_apply, zero_apply] at hv
  simpa [hsymm (0, 1) v, hsymm (0, I) v] using congrArg ((2 : ℂ)⁻¹ • ·) hv

/-- **Holomorphy of the complex derivative.** If `f : ℂ → G` is real `C²` and holomorphic on an
open set `V`, then its complex derivative `deriv f` is holomorphic on `V`. Unlike
`DifferentiableOn.deriv`, this needs no completeness of `G`. -/
theorem differentiableOn_deriv {f : ℂ → G} (hf : ContDiffOn ℝ 2 f V) (hV : IsOpen V)
    (hhol : DifferentiableOn ℂ f V) : DifferentiableOn ℂ (deriv f) V := by
  -- View `f` as a family over the parameter space `ℝ`, constant in the parameter.
  have hH : ContDiffOn ℝ 2 (fun p : ℝ × ℂ ↦ f p.2) (univ ×ˢ V) :=
    hf.comp contDiffOn_snd fun p hp ↦ hp.2
  refine ((ContinuousLinearMap.apply ℝ G ((0 : ℝ), (1 : ℂ))).comp_differentiableOn_of_map_smul
    (fun c L ↦ by simp) (differentiableOn_fderiv_comp_prodMk hH isOpen_univ hV
      (fun _ _ ↦ hhol) (mem_univ 0))).congr fun z hz ↦ ?_
  exact deriv_slice_right_eq_fderiv_apply_zero_one (f := fun p : ℝ × ℂ ↦ f p.2)
    ((hH.contDiffAt ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _, hz⟩)).differentiableAt
      (by norm_num)) (hhol.differentiableAt (hV.mem_nhds hz))

/-- **Holomorphy of the complex derivative of a family.** If `H : X × ℂ → G` is `C²` on
`W ×ˢ V` with `V` open, and `x ∈ W` is such that `z ↦ H (x, z)` is holomorphic on `V`, then the
complex derivative `deriv (fun w ↦ H (x, w))` is holomorphic on `V`. This needs no completeness of
`G`. -/
theorem differentiableOn_deriv_snd (hH : ContDiffOn ℝ 2 H (W ×ˢ V)) (hV : IsOpen V) {x : X}
    (hx : x ∈ W) (hhol : DifferentiableOn ℂ (fun z ↦ H (x, z)) V) :
    DifferentiableOn ℂ (deriv fun w ↦ H (x, w)) V :=
  (hH.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hz ↦ ⟨hx, hz⟩).differentiableOn_deriv
    hV hhol

/-- **Regularity of the complex derivative.** If `H : X × ℂ → G` is `C^n` on an open product
`W ×ˢ V` and holomorphic in its complex variable on `V`, then for `m + 1 ≤ n` its complex
derivative `(x, z) ↦ deriv (fun w ↦ H (x, w)) z` is `C^m` on `W ×ˢ V`. -/
theorem contDiffOn_deriv_snd {m n : WithTop ℕ∞} (hH : ContDiffOn ℝ n H (W ×ˢ V))
    (hW : IsOpen W) (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V)
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (fun p : X × ℂ ↦ deriv (fun w ↦ H (p.1, w)) p.2) (W ×ˢ V) := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  refine ((hH.fderiv_of_isOpen hU hmn).clm_apply
    (contDiffOn_const (c := ((0 : X), (1 : ℂ))))).congr fun p hp ↦ ?_
  exact deriv_slice_right_eq_fderiv_apply_zero_one
    ((hH.contDiffAt (hU.mem_nhds hp)).differentiableAt
      (zero_lt_one.trans_le (le_add_self.trans hmn)).ne')
    ((hhol p.1 hp.1).differentiableAt (hV.mem_nhds hp.2))

/-! ### Commutation of parameter derivatives with the complex derivative -/

/-- First-order commutation of the parameter derivative with the complex derivative: both are
the second derivative of `H` in the directions `(v, 0)` and `(0, 1)`. -/
private theorem fderiv_deriv_comm (hH : ContDiffOn ℝ 2 H (W ×ˢ V)) (hW : IsOpen W)
    (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X}
    (hx : x ∈ W) {z : ℂ} (hz : z ∈ V) :
    fderiv ℝ (fun y ↦ deriv (fun w ↦ H (y, w)) z) x =
      deriv (fun w ↦ fderiv ℝ (fun y ↦ H (y, w)) x) z := by
  have hH2 : ContDiffAt ℝ 2 H (x, z) := hH.contDiffAt ((hW.prod hV).mem_nhds ⟨hx, hz⟩)
  have hholx : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (fun w ↦ H (y, w)) z :=
    eventually_of_mem (hW.mem_nhds hx) fun y hy ↦ (hhol y hy).differentiableAt (hV.mem_nhds hz)
  -- In `y`, the complex derivative is the real derivative of the slice applied to `1`, whose
  -- parameter derivative is given by the mixed-derivative identity.
  have hF : ContDiffAt ℝ (minSmoothness ℝ 2) H (x, z) := by
    rwa [minSmoothness_of_isRCLikeNormedField]
  have hD := ((ContinuousLinearMap.apply ℝ G (1 : ℂ)).hasFDerivAt.comp x
    (hasFDerivAt_spatialFDeriv hF)).congr_of_eventuallyEq
    (f₁ := fun y ↦ deriv (fun w ↦ H (y, w)) z) (by
      filter_upwards [hholx] with y hy
      simp [hy.fderiv_restrictScalars_eq_smul_deriv ℝ])
  rw [hD.fderiv, ← one_smul ℂ (deriv _ z), ← (differentiableAt_fderiv_slice
    (h := fun y w ↦ H (y, w)) hH2 hholx).fderiv_restrictScalars_eq_smul_deriv ℝ]
  ext v
  simp

/-- **Commutation of parameter derivatives with the complex derivative.** If `H : X × ℂ → G` is
`C^n` on an open product `W ×ˢ V` and holomorphic in its complex variable on `V`, then for
`k + 1 ≤ n`, `x ∈ W` and `z ∈ V`, the `k`-th parameter derivative of the complex derivative of
`H` is the complex derivative of its `k`-th parameter derivative. -/
theorem iteratedFDeriv_deriv_comm {n : WithTop ℕ∞} (hH : ContDiffOn ℝ n H (W ×ˢ V))
    (hW : IsOpen W) (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V)
    {k : ℕ} (hk : k + 1 ≤ n) {x : X} (hx : x ∈ W) {z : ℂ} (hz : z ∈ V) :
    iteratedFDeriv ℝ k (fun y ↦ deriv (fun w ↦ H (y, w)) z) x =
      deriv (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x) z := by
  induction k generalizing x with
  | zero =>
    -- The zeroth derivative is the value, read as a multilinear map in no variables.
    let e : G →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ X) G :=
      (continuousMultilinearCurryFin0 ℝ X G).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have he : ∀ y, iteratedFDeriv ℝ 0 (fun x' ↦ H (x', y)) x = e (H (x, y)) := fun y ↦ by
      ext; simp [e]
    simp_rw [he]
    rw [e.deriv_comp_of_map_smul (fun c y ↦ by ext; simp [e])
      ((hhol x hx).differentiableAt (hV.mem_nhds hz))]
    ext
    simp [e]
  | succ k ih =>
    -- Uncurry the parameter derivative of the `k`-th derivative, commute it with `deriv` by the
    -- first-order case applied to the `k`-th derivative, and commute `deriv` with uncurrying.
    have hk' : (k : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_cast; omega) hk
    have hHk := hH.contDiffOn_iteratedFDeriv_partial (hW.prod hV) (k := k) (m := 2)
      (by push_cast at hk; rwa [add_assoc, one_add_one_eq_two] at hk)
    let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) G).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap
    have he : ∀ (f : X → G) y,
        iteratedFDeriv ℝ (k + 1) f y = e (fderiv ℝ (iteratedFDeriv ℝ k f) y) := fun f y ↦ by
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [e, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    have hev : iteratedFDeriv ℝ k (fun y ↦ deriv (fun w ↦ H (y, w)) z) =ᶠ[𝓝 x]
        fun y ↦ deriv (fun w ↦ iteratedFDeriv ℝ k (fun y' ↦ H (y', w)) y) z := by
      filter_upwards [hW.mem_nhds hx] with y hy using ih hk' hy
    simp_rw [he]
    have hholk (x' : X) (hx' : x' ∈ W) :
        DifferentiableOn ℂ (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x') V :=
      hH.differentiableOn_iteratedFDeriv_slice (h := fun y w ↦ H (y, w)) hW hV hhol hk' hx'
    rw [hev.fderiv_eq, fderiv_deriv_comm hHk hW hV hholk hx hz,
      e.deriv_comp_of_map_smul (fun c f ↦ by ext; simp [e])
        (differentiableAt_fderiv_slice (h := fun y w ↦ iteratedFDeriv ℝ k (fun y' ↦ H (y', w)) y)
          (hHk.contDiffAt ((hW.prod hV).mem_nhds ⟨hx, hz⟩))
          (eventually_of_mem (hW.mem_nhds hx) fun y hy ↦
            (hholk y hy).differentiableAt (hV.mem_nhds hz)))]

/-! ### Mixed derivatives from parameter derivatives -/

/-- **Cauchy estimate for parameter derivatives of the complex derivative.** If the `k`-th
parameter derivatives of `H` at `x` are bounded by `B` on the circle `sphere w ρ`, then the
`k`-th parameter derivative at `x` of the complex derivative of `H` at `w` has norm at most
`B / ρ`. -/
private theorem norm_iteratedFDeriv_deriv_le {n : WithTop ℕ∞} (hH : ContDiffOn ℝ n H (W ×ˢ V))
    (hW : IsOpen W) (hV : IsOpen V) (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V)
    {k : ℕ} (hk : k + 1 ≤ n) {x : X} (hx : x ∈ W) {w : ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hball : closedBall w ρ ⊆ V)
    (hB : ∀ ζ ∈ sphere w ρ, ‖iteratedFDeriv ℝ k (fun y ↦ H (y, ζ)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y ↦ deriv (fun w' ↦ H (y, w')) w) x‖ ≤ B / ρ := by
  rw [hH.iteratedFDeriv_deriv_comm hW hV hhol hk hx (hball (mem_closedBall_self hρ.le))]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    ((hH.differentiableOn_iteratedFDeriv_slice (h := fun y w ↦ H (y, w)) hW hV hhol hk hx).mono
      (closure_ball_subset_closedBall.trans hball)).diffContOnCl hB

/-- Near a point of `W ×ˢ V`, the derivative of `(x, z) ↦ ∂ₓʲ H (x, z)` sends `(a, b)` to
`∂ₓʲ⁺¹ H (x, z) (a, ·) + b • ∂ₓʲ ∂_z H (x, z)`. -/
private theorem fderiv_iteratedFDeriv_partial_apply (hW : IsOpen W) (hV : IsOpen V) {j : ℕ}
    {n : WithTop ℕ∞} (hH : ContDiffOn ℝ n H (W ×ˢ V)) (hjn : (j : WithTop ℕ∞) + 1 ≤ n)
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {p : X × ℂ} (hp : p ∈ W ×ˢ V)
    (a : X) (b : ℂ) :
    fderiv ℝ (fun q : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, q.2)) q.1) p (a, b) =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) G
          (iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1) a +
        b • iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1 := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hFd : DifferentiableAt ℝ
      (fun q : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, q.2)) q.1) p :=
    ((hH.contDiffOn_iteratedFDeriv_partial hU (m := 1) hjn).contDiffAt
      (hU.mem_nhds hp)).differentiableAt one_ne_zero
  have hhol' := (hH.differentiableOn_iteratedFDeriv_slice (h := fun y w ↦ H (y, w)) hW hV hhol
    hjn hp.1).differentiableAt (hV.mem_nhds hp.2)
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hFd,
    hhol'.fderiv_restrictScalars_eq_smul_deriv ℝ,
    ← hH.iteratedFDeriv_deriv_comm hW hV hhol hjn hp.1 hp.2, iteratedFDeriv_succ_eq_comp_left]
  simp

/-- The `m`-th derivative of the derivative of `(x, z) ↦ ∂ₓʲ H (x, z)` in a fixed direction `u`
is bounded by `‖u‖` times the sum of the `m`-th derivatives of `∂ₓʲ⁺¹ H` and of `∂ₓʲ ∂_z H`. -/
private theorem norm_iteratedFDeriv_fderiv_apply_le (hW : IsOpen W) (hV : IsOpen V) {m j : ℕ}
    (hH : ContDiffOn ℝ (m + 1 + j : ℕ) H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    (hz : z ∈ V) (u : X × ℂ) :
    ‖iteratedFDeriv ℝ m (fun p ↦
        fderiv ℝ (fun q : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, q.2)) q.1) p u) (x, z)‖ ≤
      ‖u‖ * (‖iteratedFDeriv ℝ m
          (fun p : X × ℂ ↦ iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1) (x, z)‖ +
        ‖iteratedFDeriv ℝ m (fun p : X × ℂ ↦
          iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1) (x, z)‖) := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hxz : W ×ˢ V ∈ 𝓝 (x, z) := hU.mem_nhds ⟨hx, hz⟩
  have h₁ : ContDiffAt ℝ m
      (fun p : X × ℂ ↦ iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1) (x, z) :=
    (hH.contDiffOn_iteratedFDeriv_partial hU (by norm_cast; omega)).contDiffAt hxz
  have h₂ : ContDiffAt ℝ m (fun p : X × ℂ ↦
      iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1) (x, z) :=
    ((hH.contDiffOn_deriv_snd hW hV hhol (m := (m + j : ℕ)) (by norm_cast; omega)
      ).contDiffOn_iteratedFDeriv_partial hU (by norm_cast; omega)).contDiffAt hxz
  -- Near `(x, z)`, the derivative in the direction `u` is `T (∂ₓʲ⁺¹ H) + u.2 • ∂ₓʲ ∂_z H`.
  let T := (ContinuousLinearMap.apply ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ X) G) u.1).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) G
      |>.toContinuousLinearEquiv.toContinuousLinearMap)
  have hT : ‖T‖ ≤ ‖u.1‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c ↦ by
    have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) G c).le_opNorm u.1
    rw [LinearIsometryEquiv.norm_map] at h
    simpa [T, mul_comm] using h
  have heq : (fun p : X × ℂ ↦
      fderiv ℝ (fun q : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, q.2)) q.1) p u) =ᶠ[𝓝 (x, z)]
      fun p ↦ T (iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1) +
        u.2 • iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1 := by
    filter_upwards [hxz] with p hp
    rw [fderiv_iteratedFDeriv_partial_apply hW hV hH (by norm_cast; omega) hhol hp]
    simp [T]
  have h₁' : ContDiffAt ℝ m
      (fun p : X × ℂ ↦ T (iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1)) (x, z) :=
    T.contDiff.contDiffAt.comp _ h₁
  rw [(heq.iteratedFDeriv ℝ m).self_of_nhds, fun_iteratedFDeriv_add_apply h₁' (h₂.const_smul u.2),
    iteratedFDeriv_const_smul_apply' h₂]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, mul_add]
  gcongr
  · exact (T.norm_iteratedFDeriv_comp_left h₁ le_rfl).trans
      (mul_le_mul_of_nonneg_right (hT.trans (norm_fst_le u)) (norm_nonneg _))
  · exact norm_snd_le u

/-- Splitting off one derivative: the `(m + 1)`-th derivative of `(x, z) ↦ ∂ₓʲ H (x, z)` is
bounded by the `m`-th derivatives of `∂ₓʲ⁺¹ H` and of `∂ₓʲ ∂_z H`. -/
private theorem norm_iteratedFDeriv_succ_le (hW : IsOpen W) (hV : IsOpen V) {m j : ℕ}
    (hH : ContDiffOn ℝ (m + 1 + j : ℕ) H (W ×ˢ V))
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ (m + 1)
        (fun p : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, p.2)) p.1) (x, z)‖ ≤
      ‖iteratedFDeriv ℝ m
          (fun p : X × ℂ ↦ iteratedFDeriv ℝ (j + 1) (fun y ↦ H (y, p.2)) p.1) (x, z)‖ +
        ‖iteratedFDeriv ℝ m (fun p : X × ℂ ↦
          iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1) (x, z)‖ := by
  have hU : IsOpen (W ×ˢ V) := hW.prod hV
  have hF : ContDiffOn ℝ (m + 1 : ℕ)
      (fun p : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, p.2)) p.1) (W ×ˢ V) :=
    hH.contDiffOn_iteratedFDeriv_partial hU (by norm_cast; omega)
  rw [← norm_iteratedFDeriv_fderiv]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  -- Evaluating the derivative at the direction `u` commutes with the `m`-th derivative.
  have hev := iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn
    (hF.fderiv_of_isOpen hU (m := m) (by push_cast; rfl)) le_rfl (x := (x, z)) ⟨hx, hz⟩ (u := u)
    (m := v)
  rw [iteratedFDerivWithin_of_isOpen _ hU (x := (x, z)) ⟨hx, hz⟩,
    iteratedFDerivWithin_of_isOpen _ hU (x := (x, z)) ⟨hx, hz⟩] at hev
  rw [← hev]
  refine ((ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_iteratedFDeriv_fderiv_apply_le hW hV hH hhol hx hz u) (by positivity))).trans_eq ?_
  ring

/-- The mixed-derivative bound for `(x, z) ↦ ∂ₓʲ H (x, z)`, by induction on the order `m`. -/
private theorem norm_iteratedFDeriv_iteratedFDeriv_partial_le (hW : IsOpen W) (hV : IsOpen V)
    (m : ℕ) : ∀ (j : ℕ) {H : X × ℂ → G} {x : X} {z : ℂ} {r B : ℝ},
      ContDiffOn ℝ (m + j : ℕ) H (W ×ˢ V) →
      (∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) → x ∈ W → 0 < r →
      closedBall z r ⊆ V →
      (∀ k ≤ m + j, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x‖ ≤ B) →
      ‖iteratedFDeriv ℝ m
          (fun p : X × ℂ ↦ iteratedFDeriv ℝ j (fun y ↦ H (y, p.2)) p.1) (x, z)‖ ≤
        (1 + 2 ^ m / r) ^ m * B := by
  induction m with
  | zero =>
    intro j H x z r B _ _ _ hr _ hB
    simpa using hB j (by omega) z (mem_closedBall_self hr.le)
  | succ m ih =>
    intro j H x z r B hH hhol hx hr hball hB
    have hz : z ∈ V := hball (mem_closedBall_self hr.le)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) z (mem_closedBall_self hr.le))
    have hhalf : closedBall z (r / 2) ⊆ V :=
      (closedBall_subset_closedBall (half_le_self hr.le)).trans hball
    -- The parameter part, by the induction hypothesis at order `j + 1`.
    have h₁ := ih (j + 1) (H := H) (hH.of_le (by norm_cast; omega)) hhol hx hr hball
      fun k hk w hw ↦ hB k (by omega) w hw
    -- The complex part: the Cauchy estimate on circles of radius `r / 2` bounds the parameter
    -- derivatives of `∂_z H` on `closedBall z (r / 2)` by `2 / r * B`.
    have hcauchy : ∀ k ≤ m + j, ∀ w ∈ closedBall z (r / 2),
        ‖iteratedFDeriv ℝ k (fun y ↦ deriv (fun w' ↦ H (y, w')) w) x‖ ≤ 2 / r * B := by
      intro k hk w hw
      have hsub : closedBall w (r / 2) ⊆ closedBall z r :=
        closedBall_subset_closedBall' (by linarith [mem_closedBall.1 hw])
      have := norm_iteratedFDeriv_deriv_le hH hW hV hhol (by norm_cast; omega) hx (half_pos hr)
        (hsub.trans hball) fun ζ hζ ↦ hB k (by omega) ζ (hsub (sphere_subset_closedBall hζ))
      exact this.trans_eq (by field_simp)
    have h₂ : ‖iteratedFDeriv ℝ m (fun p : X × ℂ ↦
        iteratedFDeriv ℝ j (fun y ↦ deriv (fun w ↦ H (y, w)) p.2) p.1) (x, z)‖ ≤
          (1 + 2 ^ m / (r / 2)) ^ m * (2 / r * B) := by
      rcases m with _ | m
      · simpa using hcauchy j (by omega) z (mem_closedBall_self (half_pos hr).le)
      · exact ih j (H := fun p ↦ deriv (fun w ↦ H (p.1, w)) p.2)
          (hH.contDiffOn_deriv_snd hW hV hhol (by norm_cast; omega))
          (fun x' hx' ↦ (hH.of_le (by norm_cast; omega)).differentiableOn_deriv_snd hV hx'
            (hhol x' hx'))
          hx (half_pos hr) hhalf fun k hk w hw ↦ hcauchy k (by omega) w hw
    have hpow : (2 : ℝ) ^ m / (r / 2) = 2 ^ (m + 1) / r := by field_simp; ring
    rw [hpow] at h₂
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ≤ 2 ^ (m + 1) := le_self_pow₀ (by norm_num) (by omega)
    calc _ ≤ (1 + 2 ^ m / r) ^ m * B + (1 + 2 ^ (m + 1) / r) ^ m * (2 / r * B) :=
          (norm_iteratedFDeriv_succ_le hW hV hH hhol hx hz).trans (add_le_add h₁ h₂)
      _ ≤ (1 + 2 ^ (m + 1) / r) ^ m * B + (1 + 2 ^ (m + 1) / r) ^ m * (2 ^ (m + 1) / r * B) := by
          gcongr
      _ = (1 + 2 ^ (m + 1) / r) ^ (m + 1) * B := by ring

/-- **Cauchy estimates for mixed derivatives.** Let `H : X × ℂ → G` be `C^m` on an open product
`W ×ˢ V` and holomorphic in its complex variable on `V`. Let `x ∈ W`, `0 < r` and
`closedBall z r ⊆ V`. If the parameter derivatives `iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x` of
order `k ≤ m` are bounded by `B` for `w ∈ closedBall z r`, then the total `m`-th derivative of `H`
at `(x, z)` satisfies `‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B`. -/
theorem norm_iteratedFDeriv_le_of_norm_iteratedFDeriv_partial_le {m : ℕ}
    (hH : ContDiffOn ℝ m H (W ×ˢ V)) (hW : IsOpen W) (hV : IsOpen V)
    (hhol : ∀ x ∈ W, DifferentiableOn ℂ (fun z ↦ H (x, z)) V) {x : X} (hx : x ∈ W) {z : ℂ}
    {r B : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ V)
    (hB : ∀ k ≤ m, ∀ w ∈ closedBall z r, ‖iteratedFDeriv ℝ k (fun y ↦ H (y, w)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m H (x, z)‖ ≤ (1 + 2 ^ m / r) ^ m * B := by
  have h := norm_iteratedFDeriv_iteratedFDeriv_partial_le hW hV m 0 hH hhol hx hr hball hB
  have e : (fun p : X × ℂ ↦ iteratedFDeriv ℝ 0 (fun y ↦ H (y, p.2)) p.1) =
      (continuousMultilinearCurryFin0 ℝ X G).symm ∘ H := by
    ext p
    simp
  rwa [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] at h

end ContDiffOn
