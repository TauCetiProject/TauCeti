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
(`TauCeti.eventually_setOf_eq_of_deriv_eq_zero`), and the zeros of `f s` near `x` are the points
`ξ(σ)` with `τ(σ) = s`, one on each side of `0`, where `τ'` has opposite signs. Along the curve,
with `Ψ (ξ, a) = (DF (a, ξ), ℓ ξ)` for the derivative `DF` of `(s, y) ↦ f s y`, the identity
`DF(c') = 0` and a block determinant computation give

`det D(f τ)_ξ = det Ψ · τ'`,

and `det Ψ` has a constant sign near `0`. So the Jacobian signs at the two zeros are opposite.

## Main results

* `TauCeti.exists_curve_apply_eq_zero`: the zeros of the family near a fold point form a `C²`
  curve through it, with velocity `(0, v)`.
* `TauCeti.exists_mem_nhds_setOf_apply_eq_zero_eq_pair`: the birth or death of two zeros of
  opposite Jacobian signs at a fold point.
* `TauCeti.exists_mem_nhds_finsum_sign_det_fderiv_eq_zero`: the signed count of the zeros near a
  fold point vanishes on both sides.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E} {t : ℝ} {x : E}

/-! ### The derivative of the family at a fold point -/

/-- The derivative of `(s, y) ↦ f s y` splits along the two factors: its value at `(τ, ξ)` is
`τ` times its value at `(1, 0)` plus `D(f s)_y ξ`. -/
private theorem fderiv_uncurry_apply {p : ℝ × E} (hf : DifferentiableAt ℝ (uncurry f) p)
    (w : ℝ × E) :
    fderiv ℝ (uncurry f) p w = w.1 • fderiv ℝ (uncurry f) p (1, 0) + fderiv ℝ (f p.1) p.2 w.2 := by
  have hslice : fderiv ℝ (f p.1) p.2 = (fderiv ℝ (uncurry f) p).comp
      (ContinuousLinearMap.inr ℝ ℝ E) := fderiv_slice_right (f := uncurry f) hf
  rw [hslice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- **The derivative of `(s, y) ↦ (f s y, ℓ y)` at a fold point is injective.** If the kernel of
`D = D(f t)_x` is the line through `v`, `φ` vanishes on the range of `D` but not on `∂ₜ f`, and
`ℓ v = 1`, then `(τ, ξ) ↦ (τ ∂ₜ f + D ξ, ℓ ξ)` is injective. -/
private theorem injective_fderiv_prod (hf : DifferentiableAt ℝ (uncurry f) (t, x)) {v : E}
    (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) = ℝ ∙ v) {φ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0) (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    Injective ((fderiv ℝ (uncurry f) (t, x)).prod (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))) := by
  have hdt : fderiv ℝ (uncurry f) (t, x) (1, 0) = deriv (fun r ↦ f r x) t := by
    exact (DFunLike.congr_fun (fderiv_slice_left (f := uncurry f) hf) 1).symm
  refine (injective_iff_map_eq_zero _).2 fun ⟨τ, ξ⟩ h ↦ ?_
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero, fderiv_uncurry_apply hf, hdt] at h
  -- Applying `φ` kills `D ξ`, so `τ = 0`; then `ξ` is a multiple of `v` on which `ℓ` vanishes.
  have hτ : τ = 0 := by
    have := congrArg φ h.1
    rw [map_add, map_smul, hφ, smul_eq_mul, add_zero, map_zero, mul_eq_zero] at this
    exact this.resolve_right ha
  subst hτ
  have hξ : ξ ∈ LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) := by simpa using h.1
  rw [hker, Submodule.mem_span_singleton] at hξ
  obtain ⟨c, rfl⟩ := hξ
  simp_all

/-! ### The fold of the parameter along a curve of zeros -/

/-- **The parameter folds along the curve of zeros.** Let `c = (τ, ξ)` be a `C²` curve of zeros
through `(t, x)` with velocity `(0, v)`, where `v` is a kernel vector of `D(f t)_x` and `φ`
vanishes on the range of `D(f t)_x` but not on `∂ₜ f`. Then
`τ''(0) = -φ (D²(f t)_x (v, v)) / φ (∂ₜ f)`. -/
private theorem hasDerivAt_deriv_fst (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) {v : E}
    {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
    (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0) {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x))
    (hcd : ContDiffAt ℝ 2 c 0) (hc' : HasDerivAt c (0, v) 0)
    (hzero : ∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0) :
    HasDerivAt (fun s ↦ (deriv c s).1)
      (-φ (fderiv ℝ (fderiv ℝ (f t)) x v v) / φ (deriv (fun r ↦ f r x) t)) 0 := by
  set G : ℝ × E → E →L[ℝ] E := fun w ↦ fderiv ℝ (f w.1) w.2
  have hG : ContDiffAt ℝ 1 G (t, x) := hf.fderiv_slice (m := 1) le_rfl
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ (uncurry f)) (t, x) := hf.fderiv_right (m := 1) le_rfl
  have hfd : DifferentiableAt ℝ (uncurry f) (t, x) := hf.differentiableAt two_ne_zero
  -- Differentiating `f τ ξ = 0` once: `τ' φ (∂ₜ f (c s)) + φ (D(f τ)_ξ ξ') = 0` near `0`.
  have hfc : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 2 (uncurry f) (c s) :=
    hcd.continuousAt.tendsto.eventually ((hc0 ▸ hf).eventually (by simp))
  have hid : ∀ᶠ s in 𝓝 0, (deriv c s).1 * φ (fderiv ℝ (uncurry f) (c s) (1, 0)) +
      φ (G (c s) (deriv c s).2) = 0 := by
    filter_upwards [hzero.eventually_nhds, hcd.eventually (by simp), hfc] with s hs hsd hsf
    have hFd : DifferentiableAt ℝ (uncurry f) (c s) := hsf.differentiableAt two_ne_zero
    have h0 : fderiv ℝ (uncurry f) (c s) (deriv c s) = 0 := by
      rw [← (hFd.hasFDerivAt.comp_hasDerivAt s (hsd.differentiableAt two_ne_zero).hasDerivAt).deriv]
      have hev : uncurry f ∘ c =ᶠ[𝓝 s] fun _ ↦ 0 := hs.mono fun _ h ↦ h
      exact hev.deriv_eq.trans (deriv_const _ _)
    rw [fderiv_uncurry_apply hFd] at h0
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
    have h := φ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hGc.clm_apply hw)
    rw [comp_apply, hw0, hc0, hκ, map_add, hφ, add_zero] at h
    exact h
  -- `d s = φ (∂ₜ f (c s))` tends to `φ (∂ₜ f (t, x))`.
  have hd : Tendsto (fun s ↦ φ (fderiv ℝ (uncurry f) (c s) (1, 0))) (𝓝 0)
      (𝓝 (φ (deriv (fun r ↦ f r x) t))) := by
    have hdt : fderiv ℝ (uncurry f) (t, x) (1, 0) = deriv (fun r ↦ f r x) t := by
      exact (DFunLike.congr_fun (fderiv_slice_left (f := uncurry f) hfd) 1).symm
    rw [← hdt]
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
private theorem eventually_fold_curve_fst (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) {v : E}
    {φ : StrongDual ℝ E} (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0)
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

variable [FiniteDimensional ℝ E]

/-! ### The curve of zeros through a fold point -/

/-- **The curve of zeros through a fold point.** Let the family `f` be jointly `C²` at `(t, x)`,
with `f t x = 0`, let the kernel of `D(f t)_x` be the line through `v`, and let `φ` vanish on the
range of `D(f t)_x` but not on `∂ₜ f (t, x)`. For a functional `ℓ` with `ℓ v = 1` there is a `C²`
curve `c` through `(t, x)` with velocity `(0, v)`, made of zeros of the family, along which `ℓ`
of the space component increases at unit rate, and which passes through every zero of the family
near `(t, x)`. It is the image of the line `{0} × ℝ` under the local inverse of
`(s, y) ↦ (f s y, ℓ y)`. -/
theorem exists_curve_apply_eq_zero (hf : ContDiffAt ℝ 2 (uncurry f) (t, x)) (h0 : f t x = 0)
    {v : E} (hker : LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) = ℝ ∙ v) {φ : StrongDual ℝ E}
    (hφ : ∀ y, φ (fderiv ℝ (f t) x y) = 0) (ha : φ (deriv (fun r ↦ f r x) t) ≠ 0)
    {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∃ c : ℝ → ℝ × E, ∃ N ∈ 𝓝 (t, x), c 0 = (t, x) ∧ ContDiffAt ℝ 2 c 0 ∧
      HasDerivAt c (0, v) 0 ∧ (∀ᶠ s in 𝓝 0, f (c s).1 (c s).2 = 0 ∧ ℓ (c s).2 = ℓ x + s) ∧
      ∀ z ∈ N, f z.1 z.2 = 0 → c (ℓ z.2 - ℓ x) = z := by
  have hfd : DifferentiableAt ℝ (uncurry f) (t, x) := hf.differentiableAt two_ne_zero
  set Φ : ℝ × E → E × ℝ := fun w ↦ (uncurry f w, ℓ w.2)
  have hΦ : ContDiffAt ℝ 2 Φ (t, x) := hf.prodMk (ℓ.contDiff.contDiffAt.comp _ contDiffAt_snd)
  set D := (fderiv ℝ (uncurry f) (t, x)).prod (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E))
  have hdim : finrank ℝ (ℝ × E) = finrank ℝ (E × ℝ) := by simp [add_comm]
  set e : (ℝ × E) ≃L[ℝ] E × ℝ := (LinearMap.linearEquivOfInjective D.toLinearMap
    (injective_fderiv_prod hfd hker hφ ha hℓ) hdim).toContinuousLinearEquiv
  have hΦ' : HasFDerivAt Φ (e : ℝ × E →L[ℝ] E × ℝ) (t, x) :=
    hfd.hasFDerivAt.prodMk (ℓ.hasFDerivAt.comp _ hasFDerivAt_snd)
  have hv : fderiv ℝ (f t) x v = 0 := by
    have : v ∈ LinearMap.ker (fderiv ℝ (f t) x : E →ₗ[ℝ] E) :=
      hker ▸ Submodule.mem_span_singleton_self v
    simpa using this
  have hD : D (0, v) = (0, 1) := by
    rw [ContinuousLinearMap.prod_apply, fderiv_uncurry_apply hfd]
    simp [hv, hℓ]
  have hev : (0, v) = e.symm (0, 1) := e.eq_symm_apply.2 hD
  set P := hΦ.toOpenPartialHomeomorph Φ hΦ' two_ne_zero
  have hΦp : Φ (t, x) = (0, ℓ x) := by simp [Φ, h0]
  -- The curve `c s = Φ⁻¹ (0, ℓ x + s)`.
  set L : ℝ → E × ℝ := fun s ↦ (0, ℓ x + s)
  have hL : HasDerivAt L (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : E)).prodMk ((hasDerivAt_id (0 : ℝ)).const_add _)
  have hL0 : L 0 = Φ (t, x) := by simp [L, hΦp]
  have hinv : ContDiffAt ℝ 2 P.symm (L 0) := hL0 ▸ hΦ.to_localInverse hΦ' two_ne_zero
  have hinv' : HasFDerivAt P.symm (e.symm : E × ℝ →L[ℝ] ℝ × E) (L 0) :=
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
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · have hFz : uncurry f z = 0 := hz₀
    have hΦz : L (ℓ z.2 - ℓ x) = Φ z := by simp [L, Φ, hFz]
    rw [comp_apply, hΦz]
    exact P.left_inv hz

/-! ### The Jacobian sign along a curve of zeros -/

/-- **The Jacobian along a curve of zeros.** Let `A : ℝ × E → E` be linear, `w` a vector in its
kernel and `ℓ` a functional with `ℓ w.2 = 1`. Then the restriction of `A` to `E` has determinant
`det Ψ · w.1`, where `Ψ (ξ, a) = (A (a, ξ), ℓ ξ)`. With `A` the derivative of `(s, y) ↦ f s y` at a
zero and `w` the velocity of a curve of zeros, this compares the Jacobian of `f s` with the
parameter velocity of the curve. -/
private theorem det_comp_inr_eq (A : ℝ × E →ₗ[ℝ] E) (ℓ : E →ₗ[ℝ] ℝ)
    {w : ℝ × E} (hw : A w = 0) (hℓ : ℓ w.2 = 1) :
    LinearMap.det (A ∘ₗ LinearMap.inr ℝ ℝ E) =
      LinearMap.det ((A ∘ₗ (LinearEquiv.prodComm ℝ E ℝ).toLinearMap).prod
        (ℓ ∘ₗ LinearMap.fst ℝ E ℝ)) * w.1 := by
  set Ψ := (A ∘ₗ (LinearEquiv.prodComm ℝ E ℝ).toLinearMap).prod (ℓ ∘ₗ LinearMap.fst ℝ E ℝ)
  -- `K (ξ, a) = (ξ + a w.2, a w.1)`, so that `Ψ ∘ K (ξ, a) = (A (0, ξ), ℓ ξ + a)`.
  set K : Module.End ℝ (E × ℝ) := (LinearMap.fst ℝ E ℝ + (LinearMap.snd ℝ E ℝ).smulRight w.2).prod
    ((LinearMap.snd ℝ E ℝ).smulRight w.1)
  have hAw (ξ : E) (a : ℝ) : A (a • w.1, ξ + a • w.2) = A (0, ξ) := by
    rw [show ((a • w.1, ξ + a • w.2) : ℝ × E) = (0, ξ) + a • w by ext <;> simp [add_comm],
      map_add, map_smul, hw, smul_zero, add_zero]
  have hA0 (a : ℝ) : A (a • w.1, a • w.2) = 0 := by
    simpa only [zero_add, Prod.mk_zero_zero, map_zero] using hAw 0 a
  have hΨK : LinearMap.det (Ψ ∘ₗ K) = LinearMap.det (A ∘ₗ LinearMap.inr ℝ ℝ E) := by
    rw [LinearMap.det_eq_det_mul_det_of_fst_apply_inr fun a ↦ by simpa [Ψ, K] using hA0 a]
    have h₁ : LinearMap.fst ℝ E ℝ ∘ₗ (Ψ ∘ₗ K) ∘ₗ LinearMap.inl ℝ E ℝ = A ∘ₗ LinearMap.inr ℝ ℝ E :=
      LinearMap.ext fun ξ ↦ by simp [Ψ, K]
    have h₂ : LinearMap.snd ℝ E ℝ ∘ₗ (Ψ ∘ₗ K) ∘ₗ LinearMap.inr ℝ E ℝ = LinearMap.id :=
      LinearMap.ext fun a ↦ by simp [Ψ, K, hℓ]
    rw [h₁, h₂, LinearMap.det_id, mul_one]
  -- Conjugated by the swap of factors, `K` becomes lower triangular with diagonal `(w.1, 1)`.
  have hK : LinearMap.det K = w.1 := by
    set σ := LinearEquiv.prodComm ℝ E ℝ
    rw [← LinearMap.det_conj K σ,
      LinearMap.det_eq_det_mul_det_of_fst_apply_inr fun ξ ↦ by simp [σ, K]]
    have h₁ : LinearMap.fst ℝ ℝ E ∘ₗ (σ.toLinearMap ∘ₗ K ∘ₗ σ.symm.toLinearMap) ∘ₗ
        LinearMap.inl ℝ ℝ E = w.1 • LinearMap.id :=
      LinearMap.ext fun a ↦ by simp [σ, K, mul_comm]
    have h₂ : LinearMap.snd ℝ ℝ E ∘ₗ (σ.toLinearMap ∘ₗ K ∘ₗ σ.symm.toLinearMap) ∘ₗ
        LinearMap.inr ℝ ℝ E = LinearMap.id :=
      LinearMap.ext fun ξ ↦ by simp [σ, K]
    rw [h₁, h₂, LinearMap.det_id, mul_one, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Module.finrank_self, pow_one]
  rw [← hΨK, LinearMap.det_comp, hK]

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
  have hfc : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 2 (uncurry f) (c s) :=
    hcd.continuousAt.tendsto.eventually ((hc0 ▸ hf).eventually (by simp))
  refine ⟨SignType.sign (h 0), sign_ne_zero.2 hh0, ?_⟩
  filter_upwards [hsgn, hcurve.eventually_nhds, hcd.eventually (by simp), hfc]
    with σ hσsgn hσc hσd hσf
  have hFd : DifferentiableAt ℝ (uncurry f) (c σ) := hσf.differentiableAt two_ne_zero
  have hcσ : HasDerivAt c (deriv c σ) σ := (hσd.differentiableAt two_ne_zero).hasDerivAt
  -- The velocity of the curve lies in the kernel of the derivative, and `ℓ ξ' = 1`.
  have hw : fderiv ℝ (uncurry f) (c σ) (deriv c σ) = 0 := by
    rw [← (hFd.hasFDerivAt.comp_hasDerivAt σ hcσ).deriv]
    have hev : uncurry f ∘ c =ᶠ[𝓝 σ] fun _ ↦ 0 := hσc.mono fun _ h ↦ h.1
    exact hev.deriv_eq.trans (deriv_const _ _)
  have hℓw : ℓ (deriv c σ).2 = 1 := by
    have h₁ : HasDerivAt (fun s ↦ ℓ (c s).2) (ℓ (deriv c σ).2) σ :=
      (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E)).hasFDerivAt.comp_hasDerivAt σ hcσ
    have h₂ : HasDerivAt (fun s ↦ ℓ (c s).2) 1 σ :=
      ((hasDerivAt_id σ).const_add (ℓ x)).congr_of_eventuallyEq (hσc.mono fun _ h ↦ h.2)
    exact h₁.unique h₂
  have hslice : (fderiv ℝ (f (c σ).1) (c σ).2 : E →ₗ[ℝ] E) =
      (fderiv ℝ (uncurry f) (c σ) : ℝ × E →ₗ[ℝ] E) ∘ₗ LinearMap.inr ℝ ℝ E := by
    exact congrArg (fun L : E →L[ℝ] E ↦ (L : E →ₗ[ℝ] E)) (fderiv_slice_right (f := uncurry f) hFd)
  have hτ : deriv (fun σ ↦ (c σ).1) σ = (deriv c σ).1 :=
    ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt σ hcσ).deriv
  rw [hslice, det_comp_inr_eq _ ℓ.toLinearMap hw hℓw, hτ, sign_mul, ← hσsgn]
  rfl

/-! ### Births and deaths of zeros -/

omit [FiniteDimensional ℝ E] in
/-- **Zeros near `(t, x)` lie on the curve.** If every zero `z` of the family in a neighbourhood
`N` of `(t, x)` is the point `c (ℓ z.2 - ℓ x)` of a curve `c`, then for some `r > 0` every zero
`y` of `f s` with `|s - t| < r` and `y ∈ ball x r` is `c σ` for `σ = ℓ y - ℓ x ∈ (-δ, δ)`. -/
private theorem exists_pos_forall_mem_ball {c : ℝ → ℝ × E} {ℓ : StrongDual ℝ E}
    {N : Set (ℝ × E)} (hN : N ∈ 𝓝 (t, x)) (hcN : ∀ z ∈ N, f z.1 z.2 = 0 → c (ℓ z.2 - ℓ x) = z)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ s y, dist s t < r → y ∈ ball x r → f s y = 0 →
      ℓ y - ℓ x ∈ Ioo (-δ) δ ∧ c (ℓ y - ℓ x) = (s, y) := by
  obtain ⟨r₁, hr₁, hr₁N⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨r₂, hr₂, hr₂ℓ⟩ := Metric.eventually_nhds_iff.1
    (Metric.tendsto_nhds.1 (ℓ.continuous.tendsto x) δ hδ)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun s y hs hy hy0 ↦ ⟨?_, hcN (s, y) (hr₁N ?_) hy0⟩⟩
  · have := hr₂ℓ ((mem_ball.1 hy).trans_le (min_le_right _ _))
    rw [Real.dist_eq] at this
    exact mem_Ioo.2 (abs_lt.1 this)
  · rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hs.trans_le (min_le_left _ _), (mem_ball.1 hy).trans_le (min_le_left _ _)⟩

omit [FiniteDimensional ℝ E] in
/-- **The zeros over a set of parameters.** Let `c` be a curve of zeros on `(-δ, δ)` such that every
zero `y ∈ U` of `f s` is `c σ` for `σ = ℓ y - ℓ x ∈ (-δ, δ)`. If the parameter component of `c`
takes the value `s` on `(-δ, δ)` exactly on `S`, and `c` lies over `U` on `S`, then the zeros of
`f s` in `U` are the space components of the points `c σ`, `σ ∈ S`. -/
private theorem setOf_apply_eq_zero_eq_image {c : ℝ → ℝ × E} {ℓ : StrongDual ℝ E} {U : Set E}
    {S : Set ℝ} {s δ : ℝ} (hcz : ∀ σ ∈ Ioo (-δ) δ, f (c σ).1 (c σ).2 = 0)
    (hzero : ∀ y ∈ U, f s y = 0 → ℓ y - ℓ x ∈ Ioo (-δ) δ ∧ c (ℓ y - ℓ x) = (s, y))
    (hset : {σ ∈ Ioo (-δ) δ | (c σ).1 = s} = S) (hSU : ∀ σ ∈ S, (c σ).2 ∈ U) :
    {y ∈ U | f s y = 0} = (fun σ ↦ (c σ).2) '' S := by
  ext y
  refine ⟨fun ⟨hy, hy0⟩ ↦ ?_, ?_⟩
  · obtain ⟨hσ, hcσ⟩ := hzero y hy hy0
    exact ⟨ℓ y - ℓ x, hset ▸ ⟨hσ, by simp [hcσ]⟩, by simp [hcσ]⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hσI, hσs⟩ := hset.symm ▸ hσ
    exact ⟨hSU σ hσ, hσs ▸ hcz σ hσI⟩

/-- If `g` takes the value `s` on `(-δ₀, δ₀)` exactly at `x₁ < 0 < x₂`, and on the smaller
interval `(-δ₁, δ₁)` exactly at `σ₁ < 0 < σ₂`, then `σ₁ = x₁` and `σ₂ = x₂`. -/
private theorem eq_and_eq_of_setOf_eq_pair {g : ℝ → ℝ} {s δ₀ δ₁ x₁ x₂ σ₁ σ₂ : ℝ} (hδ : δ₁ ≤ δ₀)
    (hx₁ : x₁ < 0) (hx₂ : 0 < x₂) (h₀ : {σ ∈ Ioo (-δ₀) δ₀ | g σ = s} = {x₁, x₂})
    (hσ₁ : σ₁ < 0) (hσ₂ : 0 < σ₂) (h₁ : {σ ∈ Ioo (-δ₁) δ₁ | g σ = s} = {σ₁, σ₂}) :
    σ₁ = x₁ ∧ σ₂ = x₂ := by
  have hsub : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ), σ ∈ ({x₁, x₂} : Set ℝ) := fun σ hσ ↦ by
    rw [← h₁] at hσ
    rw [← h₀]
    exact ⟨⟨by linarith [hσ.1.1], by linarith [hσ.1.2]⟩, hσ.2⟩
  refine ⟨(hsub σ₁ (by simp)).resolve_right fun h ↦ ?_,
    mem_singleton_iff.1 <| (hsub σ₂ (by simp)).resolve_left fun h ↦ ?_⟩
  · linarith [mem_singleton_iff.1 h]
  · linarith

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
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hb
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  obtain ⟨c, N, hN, hc0, hcd, hc', hcurve, hcN⟩ := exists_curve_apply_eq_zero hf h0 hker hφ ha hℓ
  have hfold := eventually_fold_curve_fst hf hφ hb hc0 hcd hc' (hcurve.mono fun _ h ↦ h.1)
  obtain ⟨ε, hε, hsign⟩ := exists_eventually_sign_det_fderiv_eq hf
    (injective_fderiv_prod (hf.differentiableAt two_ne_zero) hker hφ ha hℓ) hc0 hcd hcurve
  -- On `(-δ₀, δ₀)` the curve consists of zeros and carries the sign identity; the zeros in
  -- `ball x r` lie on it, and on `(-δ₁, δ₁)` it stays over `ball x r`.
  obtain ⟨ρ, hρ, hρc⟩ := Metric.eventually_nhds_iff.1 (hcurve.and hsign)
  obtain ⟨δ₀, hfold₀, hδ₀⟩ := (hfold.and (Ioo_mem_nhdsGT hρ)).exists
  have hρI : ∀ σ ∈ Ioo (-δ₀) δ₀, dist σ 0 < ρ := fun σ hσ ↦
    (Real.dist_0_eq_abs σ).trans_lt ((abs_lt.2 hσ).trans hδ₀.2)
  obtain ⟨r, hr, hzero⟩ := exists_pos_forall_mem_ball hN hcN hδ₀.1
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
    rw [setOf_apply_eq_zero_eq_image hcz (fun y hy hy0 ↦ hzero t y (by simpa using hr) hy hy0)
      (hfold₀.self_of_nhds.2.1 rfl) (fun σ hσ ↦ by
        rw [mem_singleton_iff.1 hσ, hc0]
        exact mem_ball_self hr), image_singleton,
      hc0]
  filter_upwards [hfold₀, hfold₁, ball_mem_nhds t hr] with s h₀ h₁ hst
  refine ⟨fun hpos y hy hy0 ↦ ?_, fun hneg ↦ ?_⟩
  · obtain ⟨hσ, hcσ⟩ := hzero s y hst hy hy0
    exact h₀.1 hpos _ hσ (by simp [hcσ])
  -- The two parameters with value `s` are the same on `(-δ₁, δ₁)` and on `(-δ₀, δ₀)`.
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hset₁, hd⟩ := h₁.2.2 hneg
  obtain ⟨x₁, hx₁, x₂, hx₂, hset₀, -⟩ := h₀.2.2 hneg
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_setOf_eq_pair (hδ₁.2.le.trans (min_le_left _ _)) hx₁.2
    hx₂.1 hset₀ hσ₁.2 hσ₂.1 hset₁
  have hval : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ), (c σ).1 = s ∧
      SignType.sign (LinearMap.det (fderiv ℝ (f s) (c σ).2 : E →ₗ[ℝ] E)) =
        ε * SignType.sign (deriv (fun σ ↦ (c σ).1) σ) := fun σ hσ ↦ by
    rw [← hset₀] at hσ
    rw [← hσ.2]
    exact ⟨rfl, (hρc (hρI σ hσ.1)).2⟩
  -- The Jacobian signs are `ε` times the signs of `τ'`, which are opposite.
  refine ⟨(c σ₁).2, (c σ₂).2, ?_, mul_neg_of_sign_eq_mul_sign hε (hval σ₁ (by simp)).2
    (hval σ₂ (by simp)).2 hd⟩
  rw [setOf_apply_eq_zero_eq_image hcz (fun y hy hy0 ↦ hzero s y hst hy hy0) hset₀ ?_, image_pair]
  rintro σ (rfl | rfl)
  · exact hU _ ⟨hσ₁.1, hσ₁.2.trans hδ₁.1⟩
  · exact hU _ ⟨by linarith [hσ₂.1, hδ₁.1], hσ₂.2⟩

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
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hb
    have hdet : LinearMap.det (fderiv ℝ (f s) x : E →ₗ[ℝ] E) = 0 := by
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot, hker]
      simpa using hv0
    rw [hS, h₀, finsum_mem_singleton, hdet, sign_zero, SignType.coe_zero]
  · have hempty : {y ∈ U | f s y = 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy ↦ hpos hgt y hy.1 hy.2
    rw [hS, hempty, finsum_mem_empty]

end TauCeti
