/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf
public import TauCeti.Analysis.Calculus.Morse.CriticalPointContinuation
public import TauCeti.Analysis.Calculus.Morse.Splitting
-- Private: used only inside proofs.
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The splitting lemma at a degenerate critical point of a family with a one-dimensional kernel

Let `f t : E → ℝ` be a one-parameter family of functions on a finite-dimensional real normed
space, and let `x` be a critical point of `f t₀` whose Hessian has a one-dimensional kernel `ℝ v`,
as at a birth–death point. Choose a functional `ℓ` with `ℓ v = 1`, and write the points near `x` as
`x + a v + w` with `a ∈ ℝ` and `w` in the kernel `K` of `ℓ`. The Hessian of `f t₀` at `x` is
nondegenerate on `K`, so the splitting lemma
`TauCeti.exists_normalized_splitting_chart_of_contDiffOn` applies to the family
`((t, a), w) ↦ f t (x + a v + w)`, with base `(t, a) ∈ ℝ × ℝ` and fibre `K`. It gives a chart
`ψ`, preserving `(t, a)`, in which

`f t (x + a v + w) = g t a - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`,  `y = (ψ ((t, a), w)).2`,

where `λ` is the Morse index of `f t₀` at `x` and `g t a = f t (x + a v + h (t, a))` is the
**reduced family**, obtained by following the section `h` of critical points of `f t` along `K`.
This reduces Cerf's normal form
`x₁³ / 3 - s x₁ - x₂² / 2 - ⋯ - x_{λ+1}² / 2 + x_{λ+2}² / 2 + ⋯` of a birth–death point to a
family of functions of one variable
(`TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton`); the normal form of that
one-variable family is not proved here.

The reduced family keeps the data of the birth–death point. At `(t₀, 0)`:

* `0` is a critical point of `g t₀` with vanishing Hessian;
* its third derivative is `D³(f t₀)_x (v, v, v)`;
* the parameter derivative of its differential, evaluated at `1`, is `∂ₜ (d(f t)_x) v`.

These are the conditions of a birth–death point in one variable, read with the kernel vector `1`:
the cubic condition and the parameter condition of `g` at `(t₀, 0)` are those of `f` at `(t₀, x)`,
and the product `D³(f t₀)_x (v, v, v) · ∂ₜ (d(f t)_x) v` that decides between a birth and a death
in `TauCeti.Analysis.Calculus.Morse.Cerf.Fold` is the same for both. The differential of `g t` at
`a` is that of `f t` at `x + a v + h (t, a)` in the direction `v`, because `f t` is critical along
`K` at the points of the section; differentiating once more, the motion of the section only
contributes values of the Hessian at `x` against `v`, which vanish.

## Main results

* `TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton`: the splitting chart at a
  critical point of `f t₀` whose Hessian has kernel `ℝ v`, together with the values of the
  derivatives of the reduced family at `(t₀, 0)`.

## References

* D. Gromoll and W. Meyer, *On differentiable functions with isolated critical points*, Topology 8
  (1969), 361–369 (the splitting lemma).
* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
-/

public section

open Function Filter Module Set
open scoped Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The reduced family -/

section Reduced

variable {f : ℝ → E → ℝ} {t : ℝ} {x v : E} {ℓ : StrongDual ℝ E}

variable {h : ℝ × ℝ → ℓ.ker} {U : Set (ℝ × ℝ)}

/-- The curve `b ↦ x + b v + h (s, b)` through the section `h` has velocity
`v + ∂_b h (s, a)` at `a`. -/
private theorem hasDerivAt_add_smul_add_section {s a : ℝ} (hh : DifferentiableAt ℝ h (s, a)) :
    HasDerivAt (fun b ↦ x + b • v + (h (s, b) : E)) (v + (fderiv ℝ h (s, a) (0, 1) : E)) a := by
  have hh' : HasDerivAt (fun b ↦ h (s, b)) (fderiv ℝ h (s, a) (0, 1)) a :=
    hh.hasFDerivAt.comp_hasDerivAt a ((hasDerivAt_const a s).prodMk (hasDerivAt_id a))
  convert (((hasDerivAt_id a).smul_const v).const_add x).add
    (ℓ.ker.subtypeL.hasFDerivAt.comp_hasDerivAt a hh') using 1
  · ext b
    simp
  · simp

/-- Along a section `h` of critical points of `f s` in the directions of the kernel of `ℓ`, the
reduced family `a ↦ f s (x + a v + h (s, a))` has derivative `d(f s) v`. -/
private theorem hasDerivAt_reduced (hU : IsOpen U) (hh : ContDiffOn ℝ 1 h U)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 1 (uncurry f) (p.1, x + p.2 • v + h p))
    (hcrit : ∀ p ∈ U, (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0)
    {p : ℝ × ℝ} (hp : p ∈ U) :
    HasDerivAt (fun a ↦ f p.1 (x + a • v + h (p.1, a)))
      (fderiv ℝ (f p.1) (x + p.2 • v + h p) v) p.2 := by
  obtain ⟨s, a⟩ := p
  have hΓ := hasDerivAt_add_smul_add_section (x := x) (v := v)
    ((hh.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp))
  have hfd : DifferentiableAt ℝ (f s) (x + a • v + h (s, a)) :=
    (hf _ hp).uncurry_left.differentiableAt one_ne_zero
  have hzero : fderiv ℝ (f s) (x + a • v + h (s, a)) (fderiv ℝ h (s, a) (0, 1) : E) = 0 :=
    congrArg (fun L : ℓ.ker →L[ℝ] ℝ ↦ L (fderiv ℝ h (s, a) (0, 1))) (hcrit _ hp)
  have hg := hfd.hasFDerivAt.comp_hasDerivAt a hΓ
  rw [map_add, hzero, add_zero] at hg
  exact hg

/-- Near `t`, the points `(t, b)` with `b` near `0` lie in a neighbourhood `U` of `(t, 0)`. -/
private theorem eventually_mk_mem (hU : U ∈ 𝓝 (t, 0)) : ∀ᶠ b in 𝓝 (0 : ℝ), (t, b) ∈ U :=
  (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds hU

/-- A family that is `C^m` along a section `h` through `x` at `(t, 0)` is `C^m` at `(t, x)`. -/
private theorem contDiffAt_uncurry_of_section {m : WithTop ℕ∞} (htU : (t, 0) ∈ U)
    (hht : h (t, 0) = 0) (hf : ∀ p ∈ U, ContDiffAt ℝ m (uncurry f) (p.1, x + p.2 • v + h p)) :
    ContDiffAt ℝ m (uncurry f) (t, x) := by
  simpa [hht] using hf _ htU

/-- The section of critical points does not move to first order in the direction `v` at
`(t, 0)`: its derivative there vanishes on `(0, 1)`, since the Hessian of `f t` at `x` is
nondegenerate on the kernel of `ℓ`. -/
private theorem fderiv_section_apply_zero_one (hU : IsOpen U) (htU : (t, 0) ∈ U)
    (hh : ContDiffOn ℝ 1 h U) (hht : h (t, 0) = 0)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 2 (uncurry f) (p.1, x + p.2 • v + h p))
    (hcrit : ∀ p ∈ U, (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0)
    (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v) (hℓ : ℓ v = 1) :
    fderiv ℝ h (t, 0) (0, 1) = 0 := by
  set H := fderiv ℝ (fderiv ℝ (f t)) x
  set η := fderiv ℝ h (t, 0) (0, 1)
  have hx : x + (0 : ℝ) • v + (h (t, 0) : E) = x := by simp [hht]
  have hft : ContDiffAt ℝ 2 (f t) x := (contDiffAt_uncurry_of_section htU hht hf).uncurry_left
  have hsymm : ∀ u w, H u w = H w u := hft.isSymmSndFDerivAt (by simp)
  have hv : H v = 0 := H.apply_eq_zero_of_ker_eq_span_singleton hker
  have hD : HasFDerivAt (fderiv ℝ (f t)) H (x + (0 : ℝ) • v + (h (t, 0) : E)) := by
    rw [hx]
    exact ((hft.fderiv_right le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hΓ : HasDerivAt (fun b : ℝ ↦ x + b • v + (h (t, b) : E)) (v + (η : E)) 0 :=
    hasDerivAt_add_smul_add_section
      ((hh.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds htU))
  have hd1 : HasDerivAt (fun b : ℝ ↦ fderiv ℝ (f t) (x + b • v + h (t, b))) (H (v + η)) 0 :=
    hD.comp_hasDerivAt (f := fun b : ℝ ↦ x + b • v + (h (t, b) : E)) 0 hΓ
  -- The restriction of `d(f t)` to the kernel of `ℓ` vanishes along the section, so its
  -- derivative `Hess(f t)_x (v + η)` vanishes on the kernel of `ℓ`.
  have hη : ℓ (η : E) = 0 := LinearMap.mem_ker.1 η.property
  have hH (u : E) (hu : ℓ u = 0) : H η u = 0 := by
    have hdu : HasDerivAt (fun b : ℝ ↦ fderiv ℝ (f t) (x + b • v + h (t, b)) u)
        (H (v + η) u) 0 := by
      simpa using hd1.clm_apply (hasDerivAt_const (0 : ℝ) u)
    have hdu0 : HasDerivAt (fun b : ℝ ↦ fderiv ℝ (f t) (x + b • v + h (t, b)) u) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        ((eventually_mk_mem (hU.mem_nhds htU)).mono fun b hb ↦ by
          simpa using congrArg (fun L : ℓ.ker →L[ℝ] ℝ ↦ L ⟨u, hu⟩) (hcrit _ hb))
    simpa [hv] using hdu.unique hdu0
  exact (Submodule.coe_eq_zero).1
    (ContinuousLinearMap.eq_zero_of_forall_apply_eq_zero_of_ker_eq_span_singleton hsymm hker hℓ hη
      hH)

/-- Near `0`, the derivative of `a ↦ d(f t) v` along the curve `Γ a = x + a v + h (t, a)` is
`Hess(f t) (Γ', v)` along `Γ`. -/
private theorem eventuallyEq_deriv_fderiv_reduced (hU : IsOpen U) (htU : (t, 0) ∈ U)
    (hh : ContDiffOn ℝ 3 h U)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 3 (uncurry f) (p.1, x + p.2 • v + h p)) :
    deriv (fun a ↦ fderiv ℝ (f t) (x + a • v + h (t, a)) v) =ᶠ[𝓝 0] fun a ↦
      fderiv ℝ (fderiv ℝ (f t)) (x + a • v + h (t, a))
        (deriv (fun b ↦ x + b • v + (h (t, b) : E)) a) v := by
  filter_upwards [eventually_mk_mem (hU.mem_nhds htU)] with b hb
  have hfb : ContDiffAt ℝ 3 (f t) (x + b • v + h (t, b)) := (hf _ hb).uncurry_left
  have hD := ((hfb.fderiv_right (m := 2) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hΓb : HasDerivAt (fun b ↦ x + b • v + (h (t, b) : E))
      (deriv (fun b ↦ x + b • v + (h (t, b) : E)) b) b :=
    (hasDerivAt_add_smul_add_section ((hh.differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds hb))).differentiableAt.hasDerivAt
  have hc := hD.comp_hasDerivAt (E := E →L[ℝ] ℝ) b hΓb
  exact (hc.clm_apply (hasDerivAt_const b v)).deriv.trans (by simp)

/-- **The second and third derivatives of the reduced function.** Along a `C³` section of critical
points of `f t` in the directions of the kernel of `ℓ`, the reduced function
`a ↦ f t (x + a v + h (t, a))` has vanishing second derivative at `0`, and third derivative
`D³(f t)_x (v, v, v)`. -/
private theorem deriv_deriv_reduced (hU : IsOpen U) (htU : (t, 0) ∈ U)
    (hh : ContDiffOn ℝ 3 h U) (hht : h (t, 0) = 0)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 3 (uncurry f) (p.1, x + p.2 • v + h p))
    (hcrit : ∀ p ∈ U, (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0)
    (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v) (hℓ : ℓ v = 1) :
    deriv (deriv fun a ↦ f t (x + a • v + h (t, a))) 0 = 0 ∧
      deriv (deriv (deriv fun a ↦ f t (x + a • v + h (t, a)))) 0 =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v := by
  set Γ : ℝ → E := fun b ↦ x + b • v + (h (t, b) : E)
  have hΓ0 : Γ 0 = x := by simp [Γ, hht]
  have hUt := eventually_mk_mem (hU.mem_nhds htU)
  have hft : ContDiffAt ℝ 3 (f t) x := (contDiffAt_uncurry_of_section htU hht hf).uncurry_left
  have hsymm : ∀ u w, fderiv ℝ (fderiv ℝ (f t)) x u w = fderiv ℝ (fderiv ℝ (f t)) x w u :=
    hft.isSymmSndFDerivAt (by norm_num)
  have hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_ker_eq_span_singleton hker
  -- The curve `Γ` is `C³` at `0`, with velocity `v` there.
  have hΓC : ContDiffAt ℝ 3 Γ 0 := by
    have hhC : ContDiffAt ℝ 3 (fun b : ℝ ↦ h (t, b)) 0 :=
      (hh.contDiffAt (hU.mem_nhds htU)).comp (0 : ℝ) (contDiffAt_const.prodMk contDiffAt_id)
    exact (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).add
      (ℓ.ker.subtypeL.contDiff.contDiffAt.comp (0 : ℝ) hhC)
  have hΓ' : deriv Γ 0 = v := by
    rw [(hasDerivAt_add_smul_add_section
      ((hh.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds htU))).deriv,
      fderiv_section_apply_zero_one hU htU (hh.of_le (by norm_num)) hht
        (fun p hp ↦ (hf p hp).of_le (by norm_num)) hcrit hker hℓ]
    simp
  have hΓ'' : DifferentiableAt ℝ (deriv Γ) 0 :=
    ((hΓC.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  -- Near `0`, the derivative of the reduced function is `d(f t) v` along `Γ`, whose derivative
  -- is `Hess(f t) (Γ', v)` along `Γ`.
  have hev1 : deriv (fun a ↦ f t (Γ a)) =ᶠ[𝓝 0] fun a ↦ fderiv ℝ (f t) (Γ a) v :=
    hUt.mono fun b hb ↦ (hasDerivAt_reduced hU (hh.of_le (by norm_num))
      (fun p hp ↦ (hf p hp).of_le (by norm_num)) hcrit hb).deriv
  have hev2 : deriv (fun a ↦ fderiv ℝ (f t) (Γ a) v) =ᶠ[𝓝 0]
      fun a ↦ fderiv ℝ (fderiv ℝ (f t)) (Γ a) (deriv Γ a) v :=
    eventuallyEq_deriv_fderiv_reduced hU htU hh hf
  refine ⟨?_, ?_⟩
  · rw [hev1.deriv_eq, hev2.eq_of_nhds, hΓ0, hΓ', hsymm, hv, zero_apply]
  · rw [hev1.deriv.deriv_eq, hev2.deriv_eq]
    have hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (f t))) (Γ 0) := by
      rw [hΓ0]
      exact (hft.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
        |>.differentiableAt (by norm_num)
    have hΓd : HasDerivAt Γ (deriv Γ 0) 0 :=
      (hΓC.differentiableAt (by norm_num)).hasDerivAt
    have hc := hD2.hasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] E →L[ℝ] ℝ) 0 hΓd
    have hcuv := (hc.clm_apply hΓ''.hasDerivAt).clm_apply (hasDerivAt_const (0 : ℝ) v)
    refine hcuv.deriv.trans ?_
    simp [hΓ0, hΓ', hsymm _ v, hv]

/-- **The parameter derivative of the reduced differential.** Along a `C¹` section of critical
points of `f s` in the directions of the kernel of `ℓ`, the derivative at `0` of the reduced
function `a ↦ f s (x + a v + h (s, a))` has derivative `∂ₜ (d(f t)_x) v` in `s` at `t`: the motion
of the section contributes a value of the Hessian of `f t` at `x` against `v`, which vanishes. -/
private theorem deriv_deriv_reduced_param (hU : IsOpen U) (htU : (t, 0) ∈ U)
    (hh : ContDiffOn ℝ 1 h U) (hht : h (t, 0) = 0)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 2 (uncurry f) (p.1, x + p.2 • v + h p))
    (hcrit : ∀ p ∈ U, (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0)
    (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v) :
    deriv (fun s ↦ deriv (fun a ↦ f s (x + a • v + h (s, a))) 0) t =
      deriv (fun s ↦ fderiv ℝ (f s) x) t v := by
  have h1 : ContDiffAt ℝ 2 (uncurry f) (t, x) := contDiffAt_uncurry_of_section htU hht hf
  have hsymm := fderiv_fderiv_apply_comm_of_uncurry h1
  have hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_ker_eq_span_singleton hker
  -- Near `t`, the derivative of the reduced function at `0` is `d(f s) v` along the section.
  have hev : (fun s ↦ deriv (fun a ↦ f s (x + a • v + h (s, a))) 0) =ᶠ[𝓝 t]
      fun s ↦ fderiv ℝ (f s) (x + (0 : ℝ) • v + h (s, 0)) v :=
    Filter.Eventually.mono (p := fun s ↦ (s, (0 : ℝ)) ∈ U)
      ((continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds htU))
      fun s hs ↦ (hasDerivAt_reduced hU (hh.of_le (by norm_num))
        (fun p hp ↦ (hf p hp).of_le (by norm_num)) hcrit hs).deriv
  rw [hev.deriv_eq]
  -- It is the parametrized differential `G (s, y) = d(f s)_y` along `σ s = (s, h (s, 0))`.
  set ζ : E := (fderiv ℝ h (t, 0) (1, 0) : E)
  have hh' : HasDerivAt (fun s ↦ h (s, 0)) (fderiv ℝ h (t, 0) (1, 0)) t :=
    ((hh.differentiableOn one_ne_zero).differentiableAt
      (hU.mem_nhds htU)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk
        (hasDerivAt_const t 0))
  have hσ2 : HasDerivAt (fun s ↦ x + (0 : ℝ) • v + (h (s, 0) : E)) ζ t := by
    convert (ℓ.ker.subtypeL.hasFDerivAt.comp_hasDerivAt t hh').const_add (x + (0 : ℝ) • v)
      using 1
    · ext s
      simp
    · simp [ζ]
  have hσ : HasDerivAt (fun s ↦ (s, x + (0 : ℝ) • v + (h (s, 0) : E))) ((1 : ℝ), ζ) t :=
    (hasDerivAt_id t).prodMk hσ2
  have hpt : (t, x + (0 : ℝ) • v + (h (t, 0) : E)) = (t, x) := by simp [hht]
  have hG : DifferentiableAt ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2)
      (t, x + (0 : ℝ) • v + (h (t, 0) : E)) := by
    rw [hpt]
    exact (h1.fderiv_slice (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc := hG.hasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] ℝ) t hσ
  have hd := hc.clm_apply (hasDerivAt_const t v)
  refine hd.deriv.trans ?_
  simp only [hht, Submodule.coe_zero, zero_smul, add_zero, fderiv_fderiv_apply h1, one_smul,
    add_apply, hsymm _ v, hv, zero_apply, map_zero]

/-- The reduced family `(s, a) ↦ f s (x + a v + h (s, a))` is `C^m` wherever the section `h` and
the family `f` are. -/
private theorem contDiffAt_uncurry_reduced {m : WithTop ℕ∞} (hU : IsOpen U)
    (hh : ContDiffOn ℝ m h U) (hf : ∀ p ∈ U, ContDiffAt ℝ m (uncurry f) (p.1, x + p.2 • v + h p))
    {p : ℝ × ℝ} (hp : p ∈ U) :
    ContDiffAt ℝ m (uncurry fun s a ↦ f s (x + a • v + h (s, a))) p := by
  have hΓ : ContDiffAt ℝ m (fun q : ℝ × ℝ ↦ (q.1, x + q.2 • v + (h q : E))) p :=
    contDiffAt_fst.prodMk ((contDiffAt_const.add (contDiffAt_snd.smul contDiffAt_const)).add
      (ℓ.ker.subtypeL.contDiff.contDiffAt.comp p (hh.contDiffAt (hU.mem_nhds hp))))
  exact (hf p hp).comp p hΓ

/-- **The reduced family at a degenerate critical point with a one-dimensional kernel.** Along a
`C³` section `h` of critical points of `f s` in the directions of the kernel of `ℓ`, through `x` at
`(t, 0)`, the reduced family `g s a = f s (x + a v + h (s, a))` has at `(t, 0)` a critical point
of `g t` with vanishing Hessian, third derivative `D³(f t)_x (v, v, v)`, and parameter derivative
of its differential `∂ₜ (d(f t)_x) v`. -/
private theorem fderiv_reduced (hU : IsOpen U) (htU : (t, 0) ∈ U)
    (hh : ContDiffOn ℝ 3 h U) (hht : h (t, 0) = 0)
    (hf : ∀ p ∈ U, ContDiffAt ℝ 3 (uncurry f) (p.1, x + p.2 • v + h p))
    (hcrit : ∀ p ∈ U, (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0)
    (hc : fderiv ℝ (f t) x = 0) (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v)
    (hℓ : ℓ v = 1) :
    fderiv ℝ (fun a ↦ f t (x + a • v + h (t, a))) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ fun a ↦ f t (x + a • v + h (t, a))) 0 1 = 0 ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ fun a ↦ f t (x + a • v + h (t, a)))) 0 1 1 1 =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ∧
      deriv (fun s ↦ fderiv ℝ (fun a ↦ f s (x + a • v + h (s, a))) 0) t 1 =
        deriv (fun s ↦ fderiv ℝ (f s) x) t v := by
  have hg := contDiffAt_uncurry_reduced hU hh hf htU
  obtain ⟨h2, h3⟩ := deriv_deriv_reduced hU htU hh hht hf hcrit hker hℓ
  refine ⟨ContinuousLinearMap.ext_ring ?_, ContinuousLinearMap.ext_ring ?_, ?_, ?_⟩
  · rw [fderiv_apply_one_eq_deriv, (hasDerivAt_reduced (p := (t, 0)) hU (hh.of_le (by norm_num))
      (fun p hp ↦ (hf p hp).of_le (by norm_num)) hcrit htU).deriv]
    simp [hht, hc]
  · rw [fderiv_fderiv_apply_one_one, h2, zero_apply]
  · rw [fderiv_fderiv_fderiv_apply_one_one_one, h3]
  · have hs : DifferentiableAt ℝ (fun s ↦ fderiv ℝ (fun a ↦ f s (x + a • v + h (s, a))) 0) t :=
      (((hg.fderiv_slice (m := 1) (by norm_num)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num))
    have key := deriv_clm_apply hs (differentiableAt_const (1 : ℝ))
    simp only [deriv_const, map_zero, add_zero, fderiv_apply_one_eq_deriv] at key
    rw [← key]
    exact deriv_deriv_reduced_param hU htU (hh.of_le (by norm_num)) hht
        (fun p hp ↦ (hf p hp).of_le (by norm_num)) hcrit hker

end Reduced

/-! ### The splitting chart -/

/-- In the coordinates `((s, a), w)`, the restriction of the family to `x + ker ℓ` at `(t, 0)` is
`w ↦ f t (x + w)`. -/
private theorem slice_mk_zero_eq (f : ℝ → E → ℝ) (t : ℝ) (x v : E) (ℓ : StrongDual ℝ E) :
    (fun w : ℓ.ker ↦ f (t, (0 : ℝ)).1 (x + (t, (0 : ℝ)).2 • v + w)) =
      fun w : ℓ.ker ↦ f t (x + w) := by
  ext w
  simp

/-- In the coordinates `((s, a), w) ↦ (s, x + a v + w)`, with `w` in the kernel of `ℓ`, a
`C^{n+3}` family `f` with a critical point `x` of `f t` whose Hessian has kernel `ℝ v` is `C^{n+2}`
near `((t, 0), 0)` and has a `C^{n+2}` section `h` of critical points along the kernel of `ℓ`
through `((t, 0), 0)`, along which `f` is `C^{n+2}`. -/
private theorem exists_section_of_ker_eq_span_singleton [FiniteDimensional ℝ E]
    {f : ℝ → E → ℝ} {t : ℝ} {x v : E} {ℓ : StrongDual ℝ E} {n : ℕ∞} {W : Set (ℝ × E)}
    (hW : W ∈ 𝓝 (t, x)) (hf : ContDiffOn ℝ (n + 3) (uncurry f) W) (hft : ContDiffAt ℝ 2 (f t) x)
    (hc : fderiv ℝ (f t) x = 0) (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v)
    (hℓ : ℓ v = 1) :
    ∃ (h : ℝ × ℝ → ℓ.ker) (U : Set (ℝ × ℝ)) (W' : Set ((ℝ × ℝ) × ℓ.ker)), IsOpen U ∧
      (t, 0) ∈ U ∧ h (t, 0) = 0 ∧ ContDiffOn ℝ (n + 2) h U ∧ W' ∈ 𝓝 ((t, 0), 0) ∧
      ContDiffOn ℝ (n + 2) (fun z : (ℝ × ℝ) × ℓ.ker ↦ f z.1.1 (x + z.1.2 • v + z.2)) W' ∧
      (∀ p ∈ U, ContDiffAt ℝ (n + 2) (uncurry f) (p.1, x + p.2 • v + h p)) ∧
      ∀ p ∈ U, fderiv ℝ (fun w : ℓ.ker ↦ f p.1 (x + p.2 • v + w)) (h p) = 0 := by
  set A : (ℝ × ℝ) × ℓ.ker → ℝ × E := fun z ↦ (z.1.1, x + z.1.2 • v + z.2)
  set φ : (ℝ × ℝ) × ℓ.ker → ℝ := fun z ↦ f z.1.1 (x + z.1.2 • v + z.2)
  have hA : ContDiff ℝ (n + 3) A := contDiff_fst.fst.prodMk ((contDiff_const.add
    (contDiff_fst.snd.smul contDiff_const)).add (ℓ.ker.subtypeL.contDiff.comp contDiff_snd))
  have hW' : A ⁻¹' interior W ∈ 𝓝 ((t, 0), (0 : ℓ.ker)) :=
    (isOpen_interior.preimage hA.continuous).mem_nhds (by
      simpa [A] using mem_interior_iff_mem_nhds.2 hW)
  have hφ : ContDiffOn ℝ (n + 2 + 1) φ (A ⁻¹' interior W) := by
    rw [add_assoc, show (2 + 1 : WithTop ℕ∞) = 3 by norm_num]
    exact (hf.mono interior_subset).comp hA.contDiffOn fun _ hz ↦ hz
  have hslice : (fun w : ℓ.ker ↦ φ ((t, 0), w)) = fun w : ℓ.ker ↦ f t (x + w) :=
    slice_mk_zero_eq f t x v ℓ
  have hcrit0 : fderiv ℝ (fun w ↦ φ ((t, 0), w)) 0 = 0 := by
    rw [hslice, fderiv_comp_add_coe (by simpa using hft.differentiableAt two_ne_zero)]
    simp [hc]
  obtain ⟨h, U, hU, htU, hht, hh, hgraph, hcrit, -⟩ :=
    exists_vertical_critical_section_of_contDiffOn hW' hφ hcrit0
      (by rw [hslice]; exact isInvertible_fderiv_fderiv_comp_add_coe_ker hft hker hℓ)
      (by simp)
  exact ⟨h, U, A ⁻¹' interior W, hU, htU, hht, hh, hW', hφ.of_le le_self_add,
    fun p hp ↦ (hf.contDiffAt (mem_interior_iff_mem_nhds.1 (hgraph p hp))).of_le
      (by gcongr; norm_num), hcrit⟩

/-- **The splitting lemma at a critical point whose Hessian has a one-dimensional kernel.** Let
`f t : E → ℝ` be a family on a finite-dimensional space, jointly `C^{n+3}` near `(t₀, x)` for some
`1 ≤ n ≤ ∞` (`t₀` is `t` in the statement), and let `x` be a critical point of `f t₀` whose
Hessian has kernel `ℝ v`. For a
functional `ℓ` with `ℓ v = 1`, write the points near `x` as `x + a v + w` with `w` in the kernel
of `ℓ`. Then there are a **reduced family** `g` of functions of one variable and a `C^n` chart `ψ`
of `(ℝ × ℝ) × ker ℓ` around `((t₀, 0), 0)`, fixed there and preserving `(t, a)` in both
directions, on whose source

`f t (x + a v + w) = g t a - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`,  `y = (ψ ((t, a), w)).2`,

where `λ` is the Morse index of `f t₀` at `x`. The reduced family is jointly `C^{n+2}` at `(t₀, 0)`,
where it has the data of the degenerate critical point of `f`: `0` is a critical point of `g t₀`
with vanishing Hessian, the third derivative of `g t₀` at `0` is `D³(f t₀)_x (v, v, v)`, and the
parameter derivative of the differential of `g t` at `0`, evaluated at `1`, is
`∂ₜ (d(f t)_x) v`. -/
theorem exists_normalized_splitting_chart_of_ker_eq_span_singleton [FiniteDimensional ℝ E]
    {f : ℝ → E → ℝ} {t : ℝ} {x v : E} {ℓ : StrongDual ℝ E} {n : ℕ∞} {W : Set (ℝ × E)}
    (hW : W ∈ 𝓝 (t, x)) (hf : ContDiffOn ℝ (n + 3) (uncurry f) W)
    (hc : fderiv ℝ (f t) x = 0) (hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v)
    (hℓ : ℓ v = 1) (hn : n ≠ 0) :
    ∃ (g : ℝ → ℝ → ℝ) (ψ : OpenPartialHomeomorph ((ℝ × ℝ) × ℓ.ker)
        ((ℝ × ℝ) × EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker)))),
      ((t, 0), 0) ∈ ψ.source ∧ ψ ((t, 0), 0) = ((t, 0), 0) ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      (∀ z ∈ ψ.source, f z.1.1 (x + z.1.2 • v + z.2) = g z.1.1 z.1.2 +
        ∑ i, (if i.val < morseIndex (f t) x then -1 else 1) * (ψ z).2 i ^ 2) ∧
      ContDiffAt ℝ (n + 2) (uncurry g) (t, 0) ∧ fderiv ℝ (g t) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (g t)) 0 1 = 0 ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (g t))) 0 1 1 1 =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ∧
      deriv (fun s ↦ fderiv ℝ (g s) 0) t 1 = deriv (fun s ↦ fderiv ℝ (f s) x) t v := by
  have h3 : (3 : WithTop ℕ∞) ≤ n + 2 := by
    have h1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast Order.one_le_iff_ne_zero.2 hn
    calc (3 : WithTop ℕ∞) = 1 + 2 := by norm_num
      _ ≤ n + 2 := add_le_add_left h1 2
  have hft : ContDiffAt ℝ 2 (f t) x := ContDiffAt.uncurry_left
    ((hf.contDiffAt hW).of_le ((show (2 : WithTop ℕ∞) ≤ 3 by norm_num).trans le_add_self))
  -- The section of critical points along the kernel of `ℓ`, and the splitting chart.
  obtain ⟨h, U, W', hU, htU, hht, hh, hW', hφ, hfU, hcrit⟩ :=
    exists_section_of_ker_eq_span_singleton hW hf hft hc hker hℓ
  obtain ⟨ψ, U', V, -, -, htU', h0V, -, hsrc, -, hψ1, hψh, hψsymm, hψ, hψinv, hψf⟩ :=
    exists_normalized_splitting_chart_of_contDiffOn (n := n) (h := h) (by rwa [hht]) hφ hU htU
      hh hcrit (by
        rw [hht, slice_mk_zero_eq]
        exact isInvertible_fderiv_fderiv_comp_add_coe_ker hft hker hℓ) hn
  -- The critical points of `f` along the kernel of `ℓ`, and the reduced family.
  have hcritU (p : ℝ × ℝ) (hp : p ∈ U) :
      (fderiv ℝ (f p.1) (x + p.2 • v + h p)).comp ℓ.ker.subtypeL = 0 := by
    rw [← fderiv_comp_add_coe ((hfU p hp).uncurry_left.differentiableAt (by simp))]
    exact hcrit p hp
  obtain ⟨hd1, hd2, hd3, hdt⟩ := fderiv_reduced hU htU (hh.of_le h3) hht
    (fun p hp ↦ (hfU p hp).of_le h3) hcritU hc hker hℓ
  refine ⟨fun s a ↦ f s (x + a • v + h (s, a)), ψ, ?_, ?_, hψ1, hψsymm, hψ, hψinv, fun z hz ↦ ?_,
    contDiffAt_uncurry_reduced hU hh hfU htU, hd1, hd2, hd3, hdt⟩
  · rw [hsrc]
    exact ⟨htU', by simpa [hht] using h0V⟩
  · simpa [hht] using hψh (t, 0)
  · have hz' := hψf z hz
    rw [hht, slice_mk_zero_eq, morseIndex_comp_add_coe_ker hft hker hℓ] at hz'
    exact hz'

end TauCeti
