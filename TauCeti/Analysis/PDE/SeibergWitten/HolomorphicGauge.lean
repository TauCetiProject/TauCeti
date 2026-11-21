/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Complex.Wirtinger.WholeSpace
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.Vortex.TransverseRatio
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The holomorphic gauge of a flat abelian Higgs pair

Let `V` be a finite-dimensional complex normed space, such as `ℂ_base × ℂ_normal`, with the complex
structure `J v = i • v`, and let `(a, α)` be an abelian Higgs pair on the trivial line over `V`,
with `a = i b` for a real one-form `b` and a section `α : V → ℂ`. The flat limits of Taubes's
rescaled large-parameter Seiberg–Witten solutions near a pseudoholomorphic curve are such pairs, and
they satisfy

* `∂bar_a α = 0`, the `J`-antilinear part of `∇_a α = dα + i b α`
  (`TauCeti.SeibergWitten.covariantDBar`), and
* `F_a^(0,2) = 0`: the curvature `F = -db` is `J`-invariant,
  `db(J v, J w) = db(v, w)`.

This file shows that such a pair is holomorphic in a complex gauge. The `(0,1)` part of the
connection form is the complex-antilinear form `c(v) = (i b(v) - b(J v)) / 2`
(`TauCeti.SeibergWitten.connectionZeroOneForm`), and `∂bar_a α = ∂bar α + c α`
(`TauCeti.SeibergWitten.covariantDBar_ofComplexModule_apply`). The `J`-invariance of `db` is exactly
what makes `c` a `∂bar`-closed `(0,1)`-form, `∂_v (c w) = ∂_w (c v)` for the conjugate Wirtinger
derivatives (`TauCeti.SeibergWitten.conjWirtingerDeriv_connectionZeroOneForm_apply_comm`): the
difference of the two sides is a combination of `db(J v, J w) - db(v, w)` and
`db(J v, w) + db(v, J w)`. By the `∂bar`-Poincaré lemma on `V`, `c = ∂bar g` for a smooth `g`, and
then `e^g α` is holomorphic (`TauCeti.exists_contDiff_differentiable_exp_smul`). So `α` is a
holomorphic function times the nowhere vanishing factor `e^(-g)`, and its zeros are those of a
holomorphic function, with their multiplicities.

On `V = E × ℂ`, a base `E` times the normal line, a pair whose zeros are confined to a bounded
normal disc is then a smooth nowhere vanishing multiple `α = h α'` of the section `α'` of a plane
vortex,
pulled back along the normal projection, whose divisor is the transverse divisor of `α`
(`TauCeti.SeibergWitten.exists_vortex_contDiff_eq_mul_sectionValue_of_covariantDBar_eq_zero`). This
is the input of the comparison of log-modulus ratios
(`TauCeti.SeibergWitten.norm_eq_one_and_eq_sub_phaseForm_of_tendsto`), which identifies the whole
pair with the pulled-back vortex up to gauge once `log |h|²` is bounded and both sections satisfy
the transverse vacuum condition. That boundedness is not proved here.

## Main results

* `TauCeti.SeibergWitten.covariantDBar_ofComplexModule_apply`: `∂bar_a α = ∂bar α + c α`.
* `TauCeti.SeibergWitten.conjWirtingerDeriv_connectionZeroOneForm_apply_comm`: the `(0,1)` part of
  a connection with `J`-invariant curvature is `∂bar`-closed.
* `TauCeti.SeibergWitten.exists_contDiff_differentiable_exp_mul_of_covariantDBar_eq_zero`: a section
  with `∂bar_a α = 0` for a smooth connection with `J`-invariant curvature is holomorphic in a
  smooth complex gauge.
* `TauCeti.SeibergWitten.exists_vortex_contDiff_eq_mul_sectionValue_of_covariantDBar_eq_zero`: on
  `E × ℂ`, such a section with confined zeros is a smooth nowhere vanishing multiple of the section
  of a plane vortex with the same divisor.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, §2.3.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter
open scoped ContDiff Topology

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The `(0,1)` part `c = (i b)^(0,1)` of the imaginary connection form `a = i b` on a complex
normed space: the complex-antilinear part `c(v) = (i b(v) - b(i v)) / 2` of `v ↦ i b(v)`. -/
def connectionZeroOneForm (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x : V) : V →L⋆[ℂ] ℂ :=
  (I • ofRealCLM.comp ((ofSubsingletonLIE (0 : Fin 1)).symm (b x))).complexAntilinearPart

/-- The `(0,1)` part of the connection form evaluated on a vector. -/
@[simp]
theorem connectionZeroOneForm_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (x v : V) :
    connectionZeroOneForm b x v = (I * b x (fun _ ↦ v) - b x (fun _ ↦ I • v)) / 2 := by
  simp [connectionZeroOneForm, ContinuousLinearMap.complexAntilinearPart_apply,
    ofSubsingletonLIE_symm_apply]
  linear_combination (b x (fun _ ↦ I • v) : ℂ) / 2 * I_mul_I

/-- **The `(0,1)` part of a connection with `J`-invariant curvature is `∂bar`-closed.** If the
connection form `b` is differentiable at `z` and its curvature `db` is invariant under the complex
structure there, `db(i v, i w) = db(v, w)`, so that `F_a` has no `(0,2)` part, then the `(0,1)`
part `c` of `a = i b` satisfies `∂_v (c w) = ∂_w (c v)` at `z` for the conjugate Wirtinger
derivatives `∂_v = ∂bar(·)(v)`. -/
theorem conjWirtingerDeriv_connectionZeroOneForm_apply_comm {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {z : V}
    (hb : DifferentiableAt ℝ b z)
    (hJ : ∀ v w, extDeriv b z ![I • v, I • w] = extDeriv b z ![v, w]) (v w : V) :
    conjWirtingerDeriv (fun y ↦ connectionZeroOneForm b y w) z v =
      conjWirtingerDeriv (fun y ↦ connectionZeroOneForm b y v) z w := by
  -- `L u m = ∂_u b(m)`, a real bilinear form.
  set L : V → V →L[ℝ] ℝ := fun u ↦ (ofSubsingletonLIE (0 : Fin 1)).symm (fderiv ℝ b z u)
    with hLdef
  have hL (u m : V) : fderiv ℝ b z u (fun _ ↦ m) = L u m := by
    simp [hLdef, ofSubsingletonLIE_symm_apply]
  -- The derivative of a coefficient of `c`: `∂_u c(m) = (i L u m - L u (i m)) / 2`.
  have hfd (m u : V) : fderiv ℝ (fun y ↦ connectionZeroOneForm b y m) z u =
      (I * L u m - L u (I • m)) / 2 := by
    have hp (m' : V) : HasFDerivAt (fun y ↦ (b y (fun _ ↦ m') : ℂ))
        (ofRealCLM.comp (fderiv ℝ (fun y ↦ b y (fun _ ↦ m')) z)) z :=
      ofRealCLM.hasFDerivAt.comp z
        (hb.continuousAlternatingMap_apply_const (fun _ ↦ m')).hasFDerivAt
    have heq : (fun y ↦ connectionZeroOneForm b y m) =
        fun y ↦ (2⁻¹ : ℂ) * (I * (b y (fun _ ↦ m) : ℂ) - b y (fun _ ↦ I • m)) := by
      ext y
      rw [connectionZeroOneForm_apply, div_eq_inv_mul]
    have hf : HasFDerivAt
        (fun y ↦ (2⁻¹ : ℂ) * (I * (b y (fun _ ↦ m) : ℂ) - b y (fun _ ↦ I • m))) _ z :=
      (((hp m).const_mul I).sub (hp (I • m))).const_mul (2⁻¹ : ℂ)
    rw [heq, hf.fderiv]
    simp [fderiv_continuousAlternatingMap_apply_const_apply hb, hL, div_eq_inv_mul]
  have hd (u m : V) : extDeriv b z ![u, m] = L u m - L m u := by
    rw [extDeriv_apply_pair, hL, hL]
  -- The two consequences of `J`-invariance used below, with `i • i • w = -w`.
  have h₁ := hJ w v
  have h₂ := hJ v (I • w)
  rw [hd, hd] at h₁ h₂
  have hneg (u m : V) : L (-u) m = -L u m := by simp [hLdef]
  rw [smul_smul, I_mul_I, neg_one_smul, hneg, map_neg] at h₂
  have h₁c := congrArg ((↑) : ℝ → ℂ) h₁
  have h₂c := congrArg ((↑) : ℝ → ℂ) h₂
  push_cast at h₁c h₂c
  rw [conjWirtingerDeriv_apply, conjWirtingerDeriv_apply, hfd, hfd, hfd, hfd, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  linear_combination (I / 4) * h₁c + (1 / 4) * h₂c +
    ((L (I • v) w : ℂ) - L (I • w) v) / 4 * I_sq

variable [FiniteDimensional ℂ V]

/-- **The covariant `∂bar` operator splits into `∂bar` and the `(0,1)` part of the connection.**
For the complex structure `J v = i • v` of a complex space, `∂bar_a α = ∂bar α + c α`, where
`c` is the `(0,1)` part of the connection form `a = i b`. -/
theorem covariantDBar_ofComplexModule_apply (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (α : V → ℂ) (x v : V) :
    covariantDBar (AlmostComplexStructure.ofComplexModule V) b α x v =
      conjWirtingerDeriv α x v + connectionZeroOneForm b x v * α x := by
  simp only [covariantDBar_apply, covariantDeriv_apply,
    AlmostComplexStructure.ofComplexModule_apply, conjWirtingerDeriv_apply,
    connectionZeroOneForm_apply, smul_eq_mul, Complex.real_smul]
  linear_combination (b x (fun _ ↦ I • v) : ℂ) * α x / 2 * I_mul_I

/-- **Holomorphic gauge of a flat pair.** Let `b` be a smooth connection form on a
finite-dimensional complex space whose curvature is invariant under the complex structure,
`db(i v, i w) = db(v, w)`, and let `α` be a real-differentiable section with `∂bar_a α = 0` for
`a = i b`. Then some smooth `g` with `∂bar g = c`, the `(0,1)` part of `a`, makes `e^g α`
holomorphic. -/
theorem exists_contDiff_differentiable_exp_mul_of_covariantDBar_eq_zero
    {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hb : ContDiff ℝ ∞ b)
    (hJ : ∀ x v w, extDeriv b x ![I • v, I • w] = extDeriv b x ![v, w])
    {α : V → ℂ} (hα : Differentiable ℝ α)
    (hdbar : ∀ x, covariantDBar (AlmostComplexStructure.ofComplexModule V) b α x = 0) :
    ∃ g : V → ℂ, ContDiff ℝ ∞ g ∧ (∀ x, conjWirtingerDeriv g x = connectionZeroOneForm b x) ∧
      Differentiable ℂ fun x ↦ cexp (g x) * α x := by
  have hc (v : V) : ContDiff ℝ ∞ fun z ↦ connectionZeroOneForm b z v := by
    have hp (m : V) : ContDiff ℝ ∞ fun z ↦ (b z (fun _ ↦ m) : ℂ) :=
      ofRealCLM.contDiff.comp ((ContinuousAlternatingMap.apply ℝ V ℝ fun _ ↦ m).contDiff.comp hb :)
    simp only [connectionZeroOneForm_apply]
    exact ((contDiff_const.mul (hp v)).sub (hp (I • v))).div_const 2
  obtain ⟨g, hg, hgc, hdiff⟩ := exists_contDiff_differentiable_exp_smul hc
    (fun z v w ↦ conjWirtingerDeriv_connectionZeroOneForm_apply_comm
      (hb.differentiable (by simp) z) (hJ z) v w) hα
    (fun z v ↦ by
      rw [smul_eq_mul, ← covariantDBar_ofComplexModule_apply, hdbar, zero_apply])
  exact ⟨g, hg, hgc, by simpa only [smul_eq_mul] using hdiff⟩

/-- **A flat pair with confined zeros is a multiple of a plane vortex.** On `E × ℂ`, a
finite-dimensional base times the normal line, let `b` be a smooth connection form with curvature
invariant under the complex structure and `α` a real-differentiable section with `∂bar_a α = 0`,
and suppose that `α (y, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there are a multiset `s` of points of norm
less than `K`, a smooth plane vortex `x` with the degree-`card s` end framing whose section vanishes
exactly at the points of `s`, with their multiplicities, and a smooth `h` with no zeros such that
`α (y, w) = h (y, w) * α'(w)`, where `α'` is the section of `x`. -/
theorem exists_vortex_contDiff_eq_mul_sectionValue_of_covariantDBar_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {b : E × ℂ → (E × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} (hb : ContDiff ℝ ∞ b)
    (hJ : ∀ x v w, extDeriv b x ![I • v, I • w] = extDeriv b x ![v, w])
    {α : E × ℂ → ℂ} (hα : Differentiable ℝ α)
    (hdbar : ∀ x, covariantDBar (AlmostComplexStructure.ofComplexModule (E × ℂ)) b α x = 0)
    {K : ℝ} (hK : ∀ y w, K ≤ ‖w‖ → α (y, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ x : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ x ∧ (∀ z, Vortex.equation x z = 0) ∧
      Tendsto (fun z ↦ Vortex.sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card s)⁻¹)
        (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (Vortex.sectionValue x) (fun z ↦ s.count z) ∧
      ∃ h : E × ℂ → ℂ, ContDiff ℝ ∞ h ∧ (∀ p, h p ≠ 0) ∧
        ∀ p, α p = h p * Vortex.sectionValue x p.2 := by
  obtain ⟨g, hg, -, hgα⟩ :=
    exists_contDiff_differentiable_exp_mul_of_covariantDBar_eq_zero hb hJ hα hdbar
  exact Vortex.exists_vortex_contDiff_eq_mul_sectionValue_of_differentiable_exp_mul hg hgα hK

end TauCeti.SeibergWitten
