/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Calculus.Bifurcation
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.MetricSpace.Pseudo.Prod

/-!
# Fold bifurcations of the zeros of a one-parameter family of maps

Let `f t : E → E` be a one-parameter family of maps of a finite-dimensional real normed space,
jointly `C²`, and let `x` be a zero of `f t` at which the derivative `D = D(f t)_x` has a
one-dimensional kernel spanned by `v`. Let `φ` be a functional vanishing on the range of `D`, so
that `φ` spans the cokernel. The point `(t, x)` is a *fold point* (a saddle-node) when

`b = φ (D²(f t)_x (v, v)) · φ (∂ₜ f (t, x)) ≠ 0`.

The second factor is the transversality of the family, the first the nondegeneracy of the fold.
The sign of `b` depends neither on `v` nor on `φ`, which are determined up to scalar factors that
multiply `b` by squares. This file proves that near a fold point a pair of zeros of opposite
Jacobian signs is born or dies (`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_eq_pair`): there is
a neighbourhood `U` of `x` in which `x` is the only zero of `f t`, and for `s` near `t`

* if `b (s - t) > 0`, then `f s` has no zero in `U`;
* if `b (s - t) < 0`, then `f s` has exactly two zeros `y₁`, `y₂` in `U`, and
  `det D(f s)_{y₁} · det D(f s)_{y₂} < 0`.

Consequently the signed count `∑ sign det D(f s)_y` of the zeros of `f s` in `U` vanishes for all
`s` near `t` (`TauCeti.exists_mem_nhds_finsum_sign_det_fderiv_eq_zero`), at `s = t` because the
degenerate zero `x` counts `0`.

In Taubes's count of pseudoholomorphic curves along a generic path of almost complex structures,
the deformation problem near a degenerate curve reduces to a finite-dimensional obstruction map,
and the Lyapunov–Schmidt reduction of `TauCeti.Analysis.Fredholm.NormalForm.Determinant` keeps the
Jacobian signs of its zeros up to one common sign. An ordinary birth or death of curves is a fold
point of that map, and the opposite signs of the two zeros are what makes such a pair cancel in
the weighted count.

The proof follows the zero locus. Choose a functional `ℓ` with `ℓ v = 1`. The map
`Φ (s, y) = (f s y, ℓ y)` has an invertible derivative at `(t, x)`, because `φ` separates `∂ₜ f`
from the range of `D` and `ℓ` separates `v` from `0`. By the inverse function theorem the zeros
of the family near `(t, x)` form the `C²` curve `c(σ) = Φ⁻¹ (0, ℓ x + σ)`
(`TauCeti.exists_curve_apply_eq_zero`), with `c(0) = (t, x)` and `c'(0) = (0, v)`. Writing
`c = (τ, ξ)` and differentiating `f τ ξ = 0` twice, then applying `φ`, gives
`τ''(0) = -φ (D²(f t)_x (v, v)) / φ (∂ₜ f)`, so the parameter `τ` folds at `0`
(`TauCeti.eventually_fold_curve_fst`, from `TauCeti.eventually_setOf_eq_of_deriv_eq_zero`), and
the zeros of `f s` near `x` are the points `ξ(σ)` with `τ(σ) = s`, one on each side of `0`, where
`τ'` has opposite signs. These two steps hold more generally for families of maps `E → F` between
finite-dimensional spaces of the same dimension; for instance, the critical points of a family of
functions are the zeros of its family of differentials `E → E*`, which is how
`TauCeti.Analysis.Calculus.Morse.Cerf.Fold` uses them. Along the curve, with
`Ψ (ξ, a) = (DF (a, ξ), ℓ ξ)` for the derivative `DF` of `(s, y) ↦ f s y`, the identity
`DF(c') = 0` and the block determinant computation `LinearMap.det_comp_inr_eq_det_prod_mul` give

`det D(f τ)_ξ = det Ψ · τ'`,

and `det Ψ` has a constant sign near `0`. So the Jacobian signs at the two zeros are opposite.

## Main results

* `TauCeti.exists_curve_apply_eq_zero`: the zeros of a family of maps `E → F` near a fold point
  form a `C²` curve through it, with velocity `(0, v)`.
* `TauCeti.eventually_fold_curve_fst`: the parameter folds back along that curve.
* `TauCeti.exists_mem_nhds_setOf_apply_eq_zero_eq_pair`: the birth or death of two zeros of
  opposite Jacobian signs at a fold point.
* `TauCeti.exists_mem_nhds_finsum_sign_det_fderiv_eq_zero`: the signed count of the zeros near a
  fold point vanishes on both sides.

The lemmas `TauCeti.setOf_eq_image_of_forall_eq_curve` and
`TauCeti.setOf_eq_pair_of_forall_eq_curve` locate the solutions near a point on such a curve.

## References

* J. Sotomayor, *Generic bifurcations of dynamical systems*, in *Dynamical Systems* (Proc.
  Sympos., Univ. Bahia, Salvador, 1971), Academic Press, 1973, 561–582.
* J. Guckenheimer and P. Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of
  Vector Fields*, Applied Mathematical Sciences 42, Springer, 1983, §3.4.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

open Function Module Set Filter Metric
open scoped Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {t : ℝ} {x : E}

/-! ### Zeros along a curve -/

/-- **The solutions over a parameter value along a curve.** Let `c` be a curve in `ℝ × X` whose
points over `I` satisfy `Z`, and suppose that every `y ∈ U` with `Z s y` is the point `c (π y)` of
the curve, with `π y ∈ I`. If the parameter component of `c` takes the value `s` on `I` exactly on
`S`, and `c` lies over `U` on `S`, then the points `y ∈ U` with `Z s y` are the space components of
the points `c σ`, `σ ∈ S`. -/
theorem setOf_eq_image_of_forall_eq_curve {X : Type*} {Z : ℝ → X → Prop} {c : ℝ → ℝ × X}
    {π : X → ℝ} {I S : Set ℝ} {U : Set X} {s : ℝ} (hcZ : ∀ σ ∈ I, Z (c σ).1 (c σ).2)
    (hZ : ∀ y ∈ U, Z s y → π y ∈ I ∧ c (π y) = (s, y)) (hS : {σ ∈ I | (c σ).1 = s} = S)
    (hSU : ∀ σ ∈ S, (c σ).2 ∈ U) :
    {y ∈ U | Z s y} = (fun σ ↦ (c σ).2) '' S := by
  ext y
  refine ⟨fun ⟨hy, hy0⟩ ↦ ?_, ?_⟩
  · obtain ⟨hσ, hcσ⟩ := hZ y hy hy0
    exact ⟨π y, hS ▸ ⟨hσ, by simp [hcσ]⟩, by simp [hcσ]⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hσI, hσs⟩ := hS.symm ▸ hσ
    exact ⟨hSU σ hσ, hσs ▸ hcZ σ hσI⟩

/-- **Two solutions over a parameter value after a fold of the curve.** In the setting of
`TauCeti.setOf_eq_image_of_forall_eq_curve` with `I = (-δ₀, δ₀)`, suppose that the parameter
component of `c` takes the value `s` exactly twice on `(-δ₀, δ₀)` and exactly at `σ₁ < 0 < σ₂` on
the smaller interval `(-δ₁, δ₁)`, over which `c` stays over `U`. Then the points `y ∈ U` with
`Z s y` are the space components of `c σ₁` and `c σ₂`. -/
theorem setOf_eq_pair_of_forall_eq_curve {X : Type*} {Z : ℝ → X → Prop} {c : ℝ → ℝ × X}
    {π : X → ℝ} {U : Set X} {s δ₀ δ₁ x₁ x₂ σ₁ σ₂ : ℝ} (hδ : δ₁ ≤ δ₀)
    (hcZ : ∀ σ ∈ Ioo (-δ₀) δ₀, Z (c σ).1 (c σ).2)
    (hZ : ∀ y ∈ U, Z s y → π y ∈ Ioo (-δ₀) δ₀ ∧ c (π y) = (s, y))
    (hU : ∀ σ ∈ Ioo (-δ₁) δ₁, (c σ).2 ∈ U) (hx₁ : x₁ < 0) (hx₂ : 0 < x₂)
    (h₀ : {σ ∈ Ioo (-δ₀) δ₀ | (c σ).1 = s} = {x₁, x₂}) (hσ₁ : σ₁ ∈ Ioo (-δ₁) 0)
    (hσ₂ : σ₂ ∈ Ioo 0 δ₁) (h₁ : {σ ∈ Ioo (-δ₁) δ₁ | (c σ).1 = s} = {σ₁, σ₂}) :
    {y ∈ U | Z s y} = {(c σ₁).2, (c σ₂).2} := by
  -- The two solutions in `(-δ₁, δ₁)` are the two solutions in `(-δ₀, δ₀)`.
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_setOf_eq_pair hδ hx₁ hx₂ h₀ hσ₁.2 hσ₂.1 h₁
  rw [setOf_eq_image_of_forall_eq_curve hcZ hZ h₀ ?_, image_pair]
  rintro σ (rfl | rfl)
  · exact hU _ ⟨hσ₁.1, (hσ₁.2.trans hσ₂.1).trans hσ₂.2⟩
  · exact hU _ ⟨(neg_neg_of_pos (hσ₂.1.trans hσ₂.2)).trans hσ₂.1, hσ₂.2⟩

section Family

variable {f : ℝ → E → F}

/-! ### The derivative of the family -/

/-- **The derivative of `(s, y) ↦ (f s y, ℓ y)` at a fold point is injective.** If the kernel of
`D = D(f t)_x` is the line through `v`, `φ` vanishes on the range of `D` but not on `∂ₜ f`, and
`ℓ v = 1`, then `(τ, ξ) ↦ (τ ∂ₜ f + D ξ, ℓ ξ)` is injective. -/
private theorem injective_fderiv_prod (hf : DifferentiableAt ℝ (uncurry f) (t, x)) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] F) = ℝ ∙ v) {φ : StrongDual ℝ F}
    (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0) (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    Injective ((fderiv ℝ (uncurry f) (t, x)).prod (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨τ, ξ⟩ h ↦ ?_
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero, fderiv_uncurry_apply hf] at h
  -- Applying `φ` kills `D ξ`, so `τ = 0`; then `ξ` is a multiple of `v` on which `ℓ` vanishes.
  have hτ : τ = 0 := by simpa [hφ, ha] using congrArg φ h.1
  subst hτ
  have hξ : ξ ∈ LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] F) := by simpa using h.1
  rw [hker, Submodule.mem_span_singleton] at hξ
  obtain ⟨c, rfl⟩ := hξ
  simp_all

/-- **The velocity of a curve of zeros lies in the kernel of the derivative.** Along a `C²` curve
of zeros through a point where the family is jointly `C²`, near `0` the family is `C²` at the
points of the curve, the curve has a velocity, and the derivative of `(s, y) ↦ f s y` kills it. -/
private theorem eventually_fderiv_apply_deriv_eq_zero (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hzero : ∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0) :
    ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 2 (uncurry f) (c s) ∧ HasDerivAt c (deriv c s) s ∧
      fderiv ℝ (uncurry f) (c s) (deriv c s) = 0 := by
  filter_upwards [hzero.eventually_nhds, hcd.eventually (by simp),
    hcd.continuousAt.tendsto.eventually ((hc0 ▸ hf).eventually (by simp))] with s hs hsd hsf
  have hcs : HasDerivAt c (deriv c s) s := (hsd.differentiableAt two_ne_zero).hasDerivAt
  refine ⟨hsf, hcs, ?_⟩
  rw [← ((hsf.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt s hcs).deriv]
  have hev : uncurry f ∘ c =ᶠ[𝓝 s] fun _ ↦ 0 := hs.mono fun _ h ↦ by simpa [uncurry_def] using h
  exact hev.deriv_eq.trans (deriv_const _ _)

/-! ### The fold of the parameter along a curve of zeros -/

/-- **The parameter folds along the curve of zeros.** Let `c = (τ, ξ)` be a `C²` curve of zeros
through `(t, x)` with velocity `(0, v)`, where `v` is a kernel vector of `D(f t)_x` and `φ`
vanishes on the range of `D(f t)_x` but not on `∂ₜ f`. Then
`τ''(0) = -φ (D²(f t)_x (v, v)) / φ (∂ₜ f)`. -/
private theorem hasDerivAt_deriv_fst (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) {v : E}
    {φ : StrongDual ℝ F} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
    (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0) {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x))
    (hcd : ContDiffAt ℝ 2 c 0) (hc' : HasDerivAt c (0, v) 0)
    (hzero : ∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0) :
    HasDerivAt (fun s ↦ (deriv c s).1)
      (-φ (fderiv ℝ (fderiv ℝ (f t)) x v v) / φ (deriv (fun r ↦ f r x) t)) 0 := by
  set G : ℝ × E → E →L[ℝ] F := fun w ↦ fderiv ℝ (f w.1) w.2
  have hG : ContDiffAt ℝ 1 G (t, x) := hf.fderiv_slice (m := 1) le_rfl
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ (uncurry f)) (t, x) := hf.fderiv_right (m := 1) le_rfl
  have hcurve := eventually_fderiv_apply_deriv_eq_zero hf hc0 hcd hzero
  -- `∂ₜ f` at a point where the family is differentiable is its derivative applied to `(1, 0)`.
  have hdt {p : ℝ × E} (hp : DifferentiableAt ℝ (uncurry f) p) :
      fderiv ℝ (uncurry f) p (1, 0) = deriv (fun r ↦ f r p.2) p.1 := by
    simp [fderiv_uncurry_apply hp]
  -- Differentiating `f τ ξ = 0` once: `τ' φ (∂ₜ f (c s)) + φ (D(f τ)_ξ ξ') = 0` near `0`.
  have hid : ∀ᶠ s in 𝓝 0, (deriv c s).1 * φ (fderiv ℝ (uncurry f) (c s) (1, 0)) +
      φ (G (c s) (deriv c s).2) = 0 := by
    filter_upwards [hcurve] with s hs
    obtain ⟨hsf, -, h0⟩ := hs
    have hsd := hsf.differentiableAt two_ne_zero
    rw [fderiv_uncurry_apply hsd, ← hdt hsd] at h0
    simpa [G, mul_comm] using congrArg φ h0
  -- `q s = φ (D(f τ)_ξ ξ')` vanishes at `0` with derivative `φ (D²(f t)_x (v, v))` there.
  have hc'd : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 :=
    (((hcd.fderiv_right (m := 1) le_rfl).clm_apply contDiffAt_const).differentiableAt
      one_ne_zero).hasDerivAt
  set w : ℝ → E := fun s ↦ (deriv c s).2
  have hw : HasDerivAt w (deriv (deriv c) 0).2 0 :=
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt _ hc'd
  have hw0 : w 0 = v := by simp [w, hc'.deriv]
  have hq : HasDerivAt (fun s ↦ φ (G (c s) (w s))) (φ (fderiv ℝ (fderiv ℝ (f t)) x v v)) 0 := by
    have hG' : HasFDerivAt G (fderiv ℝ G (t, x)) (c 0) :=
      hc0 ▸ (hG.differentiableAt one_ne_zero).hasFDerivAt
    have hGc : HasDerivAt (G ∘ c) (fderiv ℝ G (t, x) (0, v)) 0 := by
      simpa using (hG'.comp 0 hc'.hasFDerivAt).hasDerivAt
    have hκ : fderiv ℝ G (t, x) (0, v) = fderiv ℝ (fderiv ℝ (f t)) x v := by
      rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right
        (hG.differentiableAt one_ne_zero)]
      simp [G]
    simpa [comp_def, G, hw0, hc0, hκ, hφ] using
      φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hGc.clm_apply hw)
  -- `d s = φ (∂ₜ f (c s))` tends to `φ (∂ₜ f (t, x))`.
  have hd : Tendsto (fun s ↦ φ (fderiv ℝ (uncurry f) (c s) (1, 0))) (𝓝 0)
      (𝓝 (φ (deriv (fun r ↦ f r x) t))) := by
    rw [← hdt (hf.differentiableAt two_ne_zero)]
    have hFc : ContinuousAt (fun s ↦ fderiv ℝ (uncurry f) (c s)) 0 :=
      (hc0 ▸ hF1.continuousAt).comp hcd.continuousAt
    refine (φ.continuous.tendsto _).comp ?_
    simpa [hc0] using (hFc.clm_apply continuousAt_const).tendsto
  exact hasDerivAt_neg_div_of_mul_add_eq_zero hid (by simp [hc'.deriv]) hq hd ha

/-- **The parameter folds back along the curve of zeros.** Let `c = (τ, ξ)` be a `C²` curve of
zeros through `(t, x)` with velocity `(0, v)`, and let `φ` vanish on the range of `D(f t)_x`, with
`b = φ (D²(f t)_x (v, v)) · φ (∂ₜ f) ≠ 0`. Then for every small `δ > 0` and every `s` near `t`,
the parameter `τ` on `(-δ, δ)` avoids `s` if `b (s - t) > 0`, takes the value `t` only at `0`, and
takes the value `s` exactly twice, once on each side of `0` and with `τ'` of opposite signs there,
if `b (s - t) < 0`. -/
theorem eventually_fold_curve_fst (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) {v : E}
    {φ : StrongDual ℝ F} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
    (hb : φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) ≠ 0)
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hc' : HasDerivAt c (0, v) 0) (hzero : ∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ᶠ s in 𝓝 t,
      (0 < φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) * (s - t) →
        ∀ σ ∈ Ioo (-δ) δ, (c σ).1 ≠ s) ∧
      (s = t → {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {0}) ∧
      (φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) * (s - t) < 0 →
        ∃ σ₁ ∈ Ioo (-δ) 0, ∃ σ₂ ∈ Ioo 0 δ, {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = {σ₁, σ₂} ∧
          deriv (fun σ ↦ (c σ).1) σ₁ * deriv (fun σ ↦ (c σ).1) σ₂ < 0) := by
  set κ := φ (fderiv ℝ (fderiv ℝ (f t)) x v v)
  set a := φ (deriv (fun r ↦ f r x) t)
  have ha : a ≠ 0 := right_ne_zero_of_mul hb
  have hd : ∀ᶠ σ in 𝓝 0, HasDerivAt (fun σ ↦ (c σ).1) (deriv c σ).1 σ := by
    filter_upwards [hcd.eventually (by simp)] with σ hσ
    exact (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt σ
      (hσ.differentiableAt two_ne_zero).hasDerivAt
  have hev : deriv (fun σ ↦ (c σ).1) =ᶠ[𝓝 0] fun σ ↦ (deriv c σ).1 := hd.mono fun _ h ↦ h.deriv
  have h₂ : iteratedDeriv 2 (fun σ ↦ (c σ).1) 0 = -κ / a := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hev.deriv_eq]
    exact (hasDerivAt_deriv_fst hf hφ ha hc0 hcd hc' hzero).deriv
  have hfold := eventually_setOf_eq_of_deriv_eq_zero hcd.fst
    (by simp [hev.self_of_nhds, hc'.deriv]) (by
      rw [h₂]
      exact div_ne_zero (neg_ne_zero.2 (left_ne_zero_of_mul hb)) ha)
  rw [hc0] at hfold
  -- `τ'' (0) (s - t)` and `b (s - t)` have opposite signs.
  have hsign (u : ℝ) : iteratedDeriv 2 (fun σ ↦ (c σ).1) 0 * u = -(κ * a * u) / a ^ 2 := by
    rw [h₂]
    field_simp
  filter_upwards [hfold] with δ hδ
  filter_upwards [hδ] with s ⟨hlt, heq, hgt⟩
  refine ⟨fun h ↦ hlt ?_, heq, fun h ↦ hgt ?_⟩
  · rw [hsign]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos h) (by positivity)
  · rw [hsign]
    exact div_pos (neg_pos.2 h) (by positivity)

/-! ### The curve of zeros through a fold point -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The curve of zeros through a fold point.** Let `f s : E → F` be a family of maps between
finite-dimensional spaces of the same dimension, jointly `C²` at `(t, x)`, with `f t x = 0`, let
the kernel of `D(f t)_x` be the line through `v`, and let `φ` vanish on the range of `D(f t)_x` but
not on `∂ₜ f (t, x)`. For a functional `ℓ` with `ℓ v = 1` there is a `C²` curve `c` through
`(t, x)` with velocity `(0, v)`, made of zeros of the family, along which `ℓ` of the space
component increases at unit rate, and which passes through every zero of the family near `(t, x)`.
It is the image of the line `{0} × ℝ` under the local inverse of `(s, y) ↦ (f s y, ℓ y)`. -/
theorem exists_curve_apply_eq_zero (hdim : finrank ℝ F = finrank ℝ E)
    (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) (h0 : f t x = 0) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] F) = ℝ ∙ v) {φ : StrongDual ℝ F}
    (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0) (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∃ c : ℝ → ℝ × E, ∃ N ∈ 𝓝 (t, x), c 0 = (t, x) ∧ ContDiffAt ℝ 2 c 0 ∧
      HasDerivAt c (0, v) 0 ∧ (∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0 ∧ ℓ (c s).2 = ℓ x + s) ∧
      ∀ z ∈ N, f z.1 z.2 = 0 → c (ℓ z.2 - ℓ x) = z := by
  have hfd : DifferentiableAt ℝ (uncurry f) (t, x) := hf.differentiableAt two_ne_zero
  set Φ : ℝ × E → F × ℝ := fun w ↦ (uncurry f w, ℓ w.2)
  have hΦ : ContDiffAt ℝ 2 Φ (t, x) := hf.prodMk (ℓ.contDiff.contDiffAt.comp _ contDiffAt_snd)
  set D := (fderiv ℝ (uncurry f) (t, x)).prod (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))
  have hdim' : finrank ℝ (ℝ × E) = finrank ℝ (F × ℝ) := by simp [hdim, add_comm]
  set e : (ℝ × E) ≃L[ℝ] F × ℝ := (LinearMap.linearEquivOfInjective D.toLinearMap
    (injective_fderiv_prod hfd hker hφ ha hℓ) hdim').toContinuousLinearEquiv
  have hΦ' : HasFDerivAt Φ (e : ℝ × E →L[ℝ] F × ℝ) (t, x) :=
    hfd.hasFDerivAt.prodMk (ℓ.hasFDerivAt.comp _ hasFDerivAt_snd)
  have hv : fderiv ℝ (f t) x v = 0 := by
    have : v ∈ LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] F) :=
      hker ▸ Submodule.mem_span_singleton_self v
    simpa using this
  have hD : D (0, v) = (0, 1) := by
    rw [ContinuousLinearMap.prod_apply, fderiv_uncurry_apply hfd]
    simp [hv, hℓ]
  have hev : (0, v) = e.symm (0, 1) := e.eq_symm_apply.2 hD
  set P := hΦ.toOpenPartialHomeomorph Φ hΦ' two_ne_zero
  have hΦp : Φ (t, x) = (0, ℓ x) := by simp [Φ, h0]
  -- The curve `c s = Φ⁻¹ (0, ℓ x + s)`.
  set L : ℝ → F × ℝ := fun s ↦ (0, ℓ x + s)
  have hL : HasDerivAt L (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : F)).prodMk ((hasDerivAt_id (0 : ℝ)).const_add _)
  have hL0 : L 0 = Φ (t, x) := by simp [L, hΦp]
  have hinv : ContDiffAt ℝ 2 P.symm (L 0) := hL0 ▸ hΦ.to_localInverse hΦ' two_ne_zero
  have hinv' : HasFDerivAt P.symm (e.symm : F × ℝ →L[ℝ] ℝ × E) (L 0) :=
    hL0 ▸ ((hΦ.hasStrictFDerivAt hΦ' two_ne_zero).to_localInverse).hasFDerivAt
  have htarget : L 0 ∈ P.target := hL0 ▸ hΦ.image_mem_toOpenPartialHomeomorph_target hΦ' _
  refine ⟨P.symm ∘ L, P.source, P.open_source.mem_nhds
    (hΦ.mem_toOpenPartialHomeomorph_source hΦ' _), ?_, hinv.comp 0 (contDiff_const.prodMk
      (contDiff_const.add contDiff_id)).contDiffAt, ?_, ?_, fun z hz hz₀ ↦ ?_⟩
  · rw [comp_apply, hL0]
    exact P.left_inv (hΦ.mem_toOpenPartialHomeomorph_source hΦ' _)
  · simpa [hev] using hinv'.comp_hasDerivAt (0 : ℝ) hL
  · filter_upwards [hL.continuousAt.preimage_mem_nhds (P.open_target.mem_nhds htarget)] with s hs
    have h := P.right_inv hs
    rw [hΦ.toOpenPartialHomeomorph_coe] at h
    simpa [Φ, L, uncurry_def, Prod.ext_iff] using h
  · have hΦz : L (ℓ z.2 - ℓ x) = Φ z := by simp [L, Φ, uncurry_def, hz₀]
    rw [comp_apply, hΦz]
    exact P.left_inv hz

end Family

/-! ### The Jacobian sign along a curve of zeros -/

section Square

variable {f : ℝ → E → E}

/-- The kernel vector `v` of a fold point is nonzero: the fold coefficient vanishes at `v = 0`. -/
private theorem ne_zero_of_fold_coeff_ne_zero {v : E} {φ : StrongDual ℝ E} {a : ℝ}
    (hb : φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * a ≠ 0) : v ≠ 0 := by
  rintro rfl
  simp at hb

variable [FiniteDimensional ℝ E]

/-- **The Jacobian sign along the curve of zeros.** Let `c = (τ, ξ)` be a `C²` curve of zeros
through `(t, x)` along which `ℓ ξ` increases at unit rate. If the derivative of
`(s, y) ↦ (f s y, ℓ y)` at `(t, x)` is injective, then near `0` the sign of `det D(f τ)_ξ` is a
fixed nonzero sign times the sign of `τ'`. -/
private theorem exists_eventually_sign_det_fderiv_eq (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    {ℓ : StrongDual ℝ E}
    (hinj : Injective ((fderiv ℝ (uncurry f) (t, x)).prod (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))))
    {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hcd : ContDiffAt ℝ 2 c 0)
    (hcurve : ∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0 ∧ ℓ (c s).2 = ℓ x + s) :
    ∃ ε : SignType, ε ≠ 0 ∧ ∀ᶠ σ in 𝓝 0,
      SignType.sign (LinearMap.det (fderiv ℝ (f (c σ).1) (c σ).2 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (deriv (fun σ ↦ (c σ).1) σ) := by
  set P : E × ℝ →L[ℝ] ℝ × E := (ContinuousLinearEquiv.prodComm ℝ E ℝ : E × ℝ →L[ℝ] ℝ × E)
  set Ψ : (ℝ × E →L[ℝ] E) → E × ℝ →L[ℝ] E × ℝ :=
    fun A ↦ (A.comp P).prod (ℓ.comp (ContinuousLinearMap.fst ℝ E ℝ))
  have hΨ : Continuous Ψ := (ContinuousLinearMap.prodL ℝ).continuous.comp
    ((continuous_id.clm_comp continuous_const).prodMk continuous_const)
  -- As a linear map, `Ψ A` is `(ξ, a) ↦ (A (a, ξ), ℓ ξ)`.
  have hΨdet (A : ℝ × E →L[ℝ] E) : (Ψ A).det = LinearMap.det
      (((A : ℝ × E →ₗ[ℝ] E) ∘ₗ (LinearEquiv.prodComm ℝ E ℝ).toLinearMap).prod
        ((ℓ : E →ₗ[ℝ] ℝ) ∘ₗ LinearMap.fst ℝ E ℝ)) :=
    congrArg LinearMap.det (LinearMap.ext fun z ↦ by simp [Ψ, P])
  set h : ℝ → ℝ := fun σ ↦ (Ψ (fderiv ℝ (uncurry f) (c σ))).det
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ (uncurry f)) (c 0) :=
    hc0 ▸ hf.fderiv_right (m := 1) le_rfl
  have hh : ContinuousAt h 0 := ContinuousLinearMap.continuous_det.continuousAt.comp
    (hΨ.continuousAt.comp (hF1.continuousAt.comp hcd.continuousAt))
  -- At `0`, `Ψ` is the injective derivative of `(s, y) ↦ (f s y, ℓ y)` after a swap of factors.
  have hh0 : h 0 ≠ 0 := by
    have hinjΨ : Injective (Ψ (fderiv ℝ (uncurry f) (c 0))) := by
      rw [hc0]
      exact hinj.comp (ContinuousLinearEquiv.prodComm ℝ E ℝ).injective
    exact (LinearMap.isUnit_det _ ((LinearMap.isUnit_iff_ker_eq_bot _).2
      (LinearMap.ker_eq_bot.2 hinjΨ))).ne_zero
  have hsgn : ∀ᶠ σ in 𝓝 0, SignType.sign (h σ) = SignType.sign (h 0) := by
    rcases hh0.lt_or_gt with hneg | hpos
    · filter_upwards [hh.eventually (gt_mem_nhds hneg)] with σ hσ
      rw [sign_neg hσ, sign_neg hneg]
    · filter_upwards [hh.eventually (lt_mem_nhds hpos)] with σ hσ
      rw [sign_pos hσ, sign_pos hpos]
  refine ⟨SignType.sign (h 0), sign_ne_zero.2 hh0, ?_⟩
  filter_upwards [hsgn, hcurve.eventually_nhds,
    eventually_fderiv_apply_deriv_eq_zero hf hc0 hcd (hcurve.mono fun _ h ↦ h.1)]
    with σ hσsgn hσc hσ
  obtain ⟨hσf, hcσ, hw⟩ := hσ
  -- The velocity of the curve lies in the kernel of the derivative, and `ℓ ξ' = 1` since `ℓ ξ`
  -- increases at unit rate.
  have hℓw : ℓ (deriv c σ).2 = 1 := by
    have h₁ : HasDerivAt (fun s ↦ ℓ (c s).2) (ℓ (deriv c σ).2) σ :=
      (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E)).hasFDerivAt.comp_hasDerivAt σ hcσ
    have h₂ : HasDerivAt (fun s ↦ ℓ (c s).2) 1 σ :=
      ((hasDerivAt_id σ).const_add (ℓ x)).congr_of_eventuallyEq (hσc.mono fun _ h ↦ h.2)
    exact h₁.unique h₂
  have hslice : (fderiv ℝ (f (c σ).1) (c σ).2 : E →ₗ[ℝ] E) =
      (fderiv ℝ (uncurry f) (c σ) : ℝ × E →ₗ[ℝ] E) ∘ₗ LinearMap.inr ℝ ℝ E := by
    exact congrArg (fun L : E →L[ℝ] E ↦ (L : E →ₗ[ℝ] E))
      (fderiv_slice_right (f := uncurry f) (hσf.differentiableAt two_ne_zero))
  have hτ : deriv (fun σ ↦ (c σ).1) σ = (deriv c σ).1 :=
    ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt σ hcσ).deriv
  rw [hslice, LinearMap.det_comp_inr_eq_det_prod_mul _ ℓ.toLinearMap hw hℓw, ← hΨdet, hτ,
    sign_mul, hσsgn]

/-! ### Births and deaths of zeros -/

/-- Two reals whose signs are a common nonzero sign `ε` times the signs of two reals of opposite
signs have opposite signs. -/
private theorem mul_neg_of_sign_eq_mul_sign {ε : SignType} (hε : ε ≠ 0) {d₁ d₂ a₁ a₂ : ℝ}
    (h₁ : SignType.sign d₁ = ε * SignType.sign a₁) (h₂ : SignType.sign d₂ = ε * SignType.sign a₂)
    (ha : a₁ * a₂ < 0) : d₁ * d₂ < 0 := by
  rw [← sign_eq_neg_one_iff, sign_mul, h₁, h₂, mul_mul_mul_comm, ← sign_mul, sign_neg ha]
  revert hε
  cases ε <;> decide

/-- **A pair of zeros of opposite signs is born or dies at a fold point.** Let `f t` be a family
of maps of a finite-dimensional real normed space, jointly `C²` at `(t, x)`, where `x` is a zero
of `f t`. Let the kernel of `D(f t)_x` be the line through `v`, and let `φ` vanish on the range of
`D(f t)_x`, with `b = φ (D²(f t)_x (v, v)) · φ (∂ₜ f (t, x)) ≠ 0`. Then `x` has a neighbourhood
`U` in which `x` is the only zero of `f t`, and for `s` near `t`: if `b (s - t) > 0`, then `f s`
has no zero in `U`; if `b (s - t) < 0`, then `f s` has exactly two zeros `y₁` and `y₂` in `U`,
with `det D(f s)_{y₁} · det D(f s)_{y₂} < 0`, so that both are nondegenerate, of opposite
signs. -/
theorem exists_mem_nhds_setOf_apply_eq_zero_eq_pair (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    (h0 : f t x = 0) {v : E} (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) = ℝ ∙ v)
    {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
    (hb : φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) ≠ 0) :
    ∃ U ∈ 𝓝 x, {y ∈ U | f t y = 0} = {x} ∧ ∀ᶠ s in 𝓝 t,
      (0 < φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) * (s - t) →
        ∀ y ∈ U, f s y ≠ 0) ∧
      (φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) * (s - t) < 0 →
        ∃ y₁ y₂, {y ∈ U | f s y = 0} = {y₁, y₂} ∧
          LinearMap.det (fderiv ℝ (f s) y₁ : E →ₗ[ℝ] E) *
            LinearMap.det (fderiv ℝ (f s) y₂ : E →ₗ[ℝ] E) < 0) := by
  have ha : φ (deriv (fun r ↦ f r x) t) ≠ 0 := right_ne_zero_of_mul hb
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) (ne_zero_of_fold_coeff_ne_zero hb)
  obtain ⟨c, N, hN, hc0, hcd, hc', hcurve, hcN⟩ :=
    exists_curve_apply_eq_zero rfl hf h0 hker hφ ha hℓ
  have hfold := eventually_fold_curve_fst hf hφ hb hc0 hcd hc' (hcurve.mono fun _ h ↦ h.1)
  obtain ⟨ε, hε, hsign⟩ := exists_eventually_sign_det_fderiv_eq hf
    (injective_fderiv_prod (hf.differentiableAt two_ne_zero) hker hφ ha hℓ) hc0 hcd hcurve
  -- On `(-δ₀, δ₀)` the curve consists of zeros and carries the sign identity; the zeros in
  -- `ball x r` lie on it, and on `(-δ₁, δ₁)` it stays over `ball x r`.
  obtain ⟨ρ, hρ, hρc⟩ := Metric.eventually_nhds_iff.1 (hcurve.and hsign)
  obtain ⟨δ₀, hfold₀, hδ₀⟩ := (hfold.and (Ioo_mem_nhdsGT hρ)).exists
  have hρI : ∀ σ ∈ Ioo (-δ₀) δ₀, dist σ 0 < ρ := fun σ hσ ↦
    (Real.dist_0_eq_abs σ).trans_lt ((abs_lt.2 hσ).trans hδ₀.2)
  obtain ⟨r, hr, hrN⟩ := exists_pos_forall_mem_of_mem_nhds hN ℓ.continuous.continuousAt hδ₀.1
  have hzero (s : ℝ) (hs : dist s t < r) (y : E) (hy : y ∈ ball x r) (hy0 : f s y = 0) :
      ℓ y - ℓ x ∈ Ioo (-δ₀) δ₀ ∧ c (ℓ y - ℓ x) = (s, y) :=
    ⟨(hrN s y hs hy).2, hcN (s, y) (hrN s y hs hy).1 hy0⟩
  have hξ : Tendsto (fun σ ↦ (c σ).2) (𝓝 0) (𝓝 x) := by
    simpa [hc0] using hcd.continuousAt.snd.tendsto
  obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.eventually_nhds_iff.1 (hξ.eventually (ball_mem_nhds x hr))
  obtain ⟨δ₁, hfold₁, hδ₁⟩ := (hfold.and (Ioo_mem_nhdsGT (lt_min hδ₀.1 hε₁))).exists
  have hcz : ∀ σ ∈ Ioo (-δ₀) δ₀, f (c σ).1 (c σ).2 = 0 := fun σ hσ ↦ (hρc (hρI σ hσ)).1.1
  have hU : ∀ σ ∈ Ioo (-δ₁) δ₁, (c σ).2 ∈ ball x r := fun σ hσ ↦
    hε₁U ((Real.dist_0_eq_abs σ).trans_lt
      ((abs_lt.2 hσ).trans (hδ₁.2.trans_le (min_le_right _ _))))
  refine ⟨ball x r, ball_mem_nhds x hr, ?_, ?_⟩
  · -- At `t` the only zero in the ball is `x`, the point of the curve at `σ = 0`.
    rw [setOf_eq_image_of_forall_eq_curve (Z := fun s y ↦ f s y = 0) hcz
      (hzero t (by simpa using hr)) (hfold₀.self_of_nhds.2.1 rfl) (fun σ hσ ↦ by
        rw [mem_singleton_iff.1 hσ, hc0]
        exact mem_ball_self hr), image_singleton,
      hc0]
  filter_upwards [hfold₀, hfold₁, ball_mem_nhds t hr] with s h₀ h₁ hst
  refine ⟨fun hpos y hy hy0 ↦ ?_, fun hneg ↦ ?_⟩
  · obtain ⟨hσ, hcσ⟩ := hzero s hst y hy hy0
    exact h₀.1 hpos _ hσ (by simp [hcσ])
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hset₁, hd⟩ := h₁.2.2 hneg
  obtain ⟨x₁, hx₁, x₂, hx₂, hset₀, -⟩ := h₀.2.2 hneg
  have hδ : δ₁ ≤ δ₀ := hδ₁.2.le.trans (min_le_left _ _)
  have hval : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ),
      SignType.sign (LinearMap.det (fderiv ℝ (f s) (c σ).2 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (deriv (fun σ ↦ (c σ).1) σ) := fun σ hσ ↦ by
    rw [← hset₁] at hσ
    rw [← hσ.2]
    exact (hρc (hρI σ (Ioo_subset_Ioo (neg_le_neg hδ) hδ hσ.1))).2
  -- The Jacobian signs are `ε` times the signs of `τ'`, which are opposite.
  exact ⟨(c σ₁).2, (c σ₂).2, setOf_eq_pair_of_forall_eq_curve (Z := fun s y ↦ f s y = 0) hδ hcz
    (hzero s hst) hU hx₁.2 hx₂.1 hset₀ hσ₁ hσ₂ hset₁,
    mul_neg_of_sign_eq_mul_sign hε (hval σ₁ (by simp)) (hval σ₂ (by simp)) hd⟩

/-- **The signed count of zeros vanishes across a fold point.** Under the hypotheses of
`TauCeti.exists_mem_nhds_setOf_apply_eq_zero_eq_pair`, `x` has a neighbourhood `U` such that for
every `s` near `t` the zeros `y` of `f s` in `U`, counted with the signs of `det D(f s)_y`, add up
to `0`: there are none, or only the degenerate zero `x` at `s = t`, or two of opposite signs. -/
theorem exists_mem_nhds_finsum_sign_det_fderiv_eq_zero (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    (h0 : f t x = 0) {v : E} (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) = ℝ ∙ v)
    {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
    (hb : φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ᶠ s in 𝓝 t, ∑ᶠ y ∈ U ∩ f s ⁻¹' {0},
      (SignType.sign (LinearMap.det (fderiv ℝ (f s) y : E →ₗ[ℝ] E)) : ℤ) = 0 := by
  obtain ⟨U, hU, h₀, h⟩ := exists_mem_nhds_setOf_apply_eq_zero_eq_pair hf h0 hker hφ hb
  refine ⟨U, hU, ?_⟩
  filter_upwards [h] with s ⟨hpos, hneg⟩
  have hS : U ∩ f s ⁻¹' {0} = {y ∈ U | f s y = 0} := by
    ext
    simp
  rcases lt_trichotomy (φ (fderiv ℝ (fderiv ℝ (f t)) x v v) * φ (deriv (fun r ↦ f r x) t) *
    (s - t)) 0 with hlt | heq | hgt
  · obtain ⟨y₁, y₂, hset, hdet⟩ := hneg hlt
    have hne : y₁ ≠ y₂ := by
      rintro rfl
      exact (mul_self_nonneg _).not_gt hdet
    rw [hS, hset, finsum_mem_pair hne]
    rcases mul_neg_iff.1 hdet with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp [sign_pos h₁, sign_neg h₂]
    · simp [sign_neg h₁, sign_pos h₂]
  · -- At `s = t` the only zero is `x`, which is degenerate.
    obtain rfl : s = t := by
      rcases mul_eq_zero.1 heq with h | h
      · exact absurd h hb
      · linarith
    have hdet : LinearMap.det (fderiv ℝ (f s) x : E →ₗ[ℝ] E) = 0 := by
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot, hker]
      simpa using ne_zero_of_fold_coeff_ne_zero hb
    rw [hS, h₀, finsum_mem_singleton, hdet, sign_zero, SignType.coe_zero]
  · have hempty : {y ∈ U | f s y = 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy ↦ hpos hgt y hy.1 hy.2
    rw [hS, hempty, finsum_mem_empty]

end Square

end TauCeti
