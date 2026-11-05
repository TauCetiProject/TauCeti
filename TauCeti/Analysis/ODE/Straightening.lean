/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The straightening theorem for vector fields on a normed space

Near a point where a `C^n` vector field `w` on a finite-dimensional real normed space `E` does not
vanish, some `C^n` change of coordinates carries `w` to a constant field. Precisely, there is an
open partial homeomorphism `φ` of `E`, `C^n` with `C^n` inverse, whose domain contains the point
`a` and whose derivative sends `w y` to `w a` at every point `y` of its domain
(`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`). This is the flow-box theorem: in the
coordinates `φ`, the integral curves of `w` become parallel straight lines traversed with constant
velocity `w a`.

Cut `w` off to a globally Lipschitz `C^n` field `g` that agrees with it near `a`, and let `Φ` be the
global flow of `g`, which is `C^n` jointly in the initial condition and time. Choose a continuous
linear functional `ℓ` with `ℓ (w a) = 1` and set

`ψ z = Φ (a + (z - ℓ z • w a)) (ℓ z)`.

The flow law gives `ψ (z + s • w a) = Φ (ψ z) s`, so differentiating in `s` shows that `dψ z`
sends `w a` to `g (ψ z)`. At `z = 0` the derivative of `ψ` is the identity, so by the inverse
function theorem with `C^n` inverse
(`ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq`) `ψ` is a local
diffeomorphism near `0` whose inverse sends `g` to `w a`; restricted to where `g = w`, that inverse
is the required `φ`.

## Main results

* `TauCeti.exists_openPartialHomeomorph_fderiv_eq_const`: a nonvanishing `C^n` vector field is
  constant in suitable `C^n` local coordinates.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.22 (canonical form near a regular point).
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinates `ψ z = Φ (a + (z - ℓ z • u)) (ℓ z)` built from a flow `Φ`: flow for time
`ℓ z` from the point of the hyperplane through `a` with direction `ker ℓ` reached by `z`. -/
private def flowBoxMap (Φ : E → ℝ → E) (a u : E) (ℓ : E →L[ℝ] ℝ) (z : E) : E :=
  Φ (a + (z - ℓ z • u)) (ℓ z)

/-- The flow-box coordinates of a flow intertwine translation along `u` with the flow. -/
private theorem flowBoxMap_add_smul {Φ : E → ℝ → E} (hΦ : ∀ x t s, Φ x (t + s) = Φ (Φ x t) s)
    {a u : E} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ u = 1) (z : E) (s : ℝ) :
    flowBoxMap Φ a u ℓ (z + s • u) = Φ (flowBoxMap Φ a u ℓ z) s := by
  have hz : z + s • u - (ℓ z + s) • u = z - ℓ z • u := by
    rw [add_smul]
    abel
  simp only [flowBoxMap, map_add, map_smul, hℓ, smul_eq_mul, mul_one, hz, hΦ]

/-- The affine map `z ↦ (a + (z - ℓ z • u), ℓ z)` feeding the flow in the flow-box coordinates. -/
private theorem hasFDerivAt_flowBoxArg (a u : E) (ℓ : E →L[ℝ] ℝ) (z : E) :
    HasFDerivAt (fun z : E ↦ (a + (z - ℓ z • u), ℓ z))
      (((ContinuousLinearMap.id ℝ E) - ℓ.smulRight u).prod ℓ) z :=
  (((hasFDerivAt_id z).sub (ℓ.hasFDerivAt.smul_const u)).const_add a).prodMk ℓ.hasFDerivAt

section Flow

variable [CompleteSpace E] {g : E → E} {K : NNReal} (hg : LipschitzWith K g) {a u : E}
  {ℓ : E →L[ℝ] ℝ}
include hg

/-- The derivative of the flow-box coordinates of the flow of `g` in the direction `u` is `g`. -/
private theorem fderiv_flowBoxMap_apply (hℓ : ℓ u = 1) {z : E}
    (hd : DifferentiableAt ℝ (flowBoxMap (ODE.globalSolution g hg) a u ℓ) z) :
    fderiv ℝ (flowBoxMap (ODE.globalSolution g hg) a u ℓ) z u =
      g (flowBoxMap (ODE.globalSolution g hg) a u ℓ z) := by
  set ψ := flowBoxMap (ODE.globalSolution g hg) a u ℓ
  -- Differentiate `s ↦ ψ (z + s • u) = Φ (ψ z) s` at `s = 0` in two ways.
  have h₁ : HasDerivAt (fun s : ℝ ↦ ψ (z + s • u)) (fderiv ℝ ψ z u) 0 := by
    have hline : HasDerivAt (fun s : ℝ ↦ z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    have hdiff : HasFDerivAt ψ (fderiv ℝ ψ z) (z + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hline
  have h₂ : HasDerivAt (fun s : ℝ ↦ ψ (z + s • u)) (g (ψ z)) 0 := by
    have h := ODE.hasDerivAt_globalSolution g hg (ψ z) 0
    rw [ODE.globalSolution_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    exact flowBoxMap_add_smul (ODE.globalSolution_add g hg) hℓ z s
  exact h₁.unique h₂

/-- The flow-box coordinates of the flow of `g` at the base point `a`, with `g a = u`, have the
identity as derivative at `0`. -/
private theorem hasFDerivAt_flowBoxMap_zero (hga : g a = u)
    (hd : DifferentiableAt ℝ (fun p : E × ℝ ↦ ODE.globalSolution g hg p.1 p.2) (a, 0)) :
    HasFDerivAt (flowBoxMap (ODE.globalSolution g hg) a u ℓ) (ContinuousLinearMap.id ℝ E) 0 := by
  set Φ := ODE.globalSolution g hg
  set D := fderiv ℝ (fun p : E × ℝ ↦ Φ p.1 p.2) (a, 0)
  -- `D` restricted to the space directions is the identity, since `Φ x 0 = x`.
  have hDx (h : E) : D (h, 0) = h := by
    have h₁ := hd.hasFDerivAt.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : ℝ))
    have h₂ : HasFDerivAt (fun x : E ↦ Φ x 0) (ContinuousLinearMap.id ℝ E) a := by
      rw [show (fun x : E ↦ Φ x 0) = id from funext (ODE.globalSolution_zero g hg)]
      exact hasFDerivAt_id a
    simpa using congrArg (fun L : E →L[ℝ] E ↦ L h) (h₁.unique h₂)
  -- `D` in the time direction is `g a`, the velocity of the flow line through `a`.
  have hDt : D (0, 1) = u := by
    have h₁ := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) a).prodMk (hasDerivAt_id (0 : ℝ)))
    have h₂ := ODE.hasDerivAt_globalSolution g hg a 0
    rw [ODE.globalSolution_zero, hga] at h₂
    exact h₁.unique h₂
  have hd' : HasFDerivAt (fun p : E × ℝ ↦ Φ p.1 p.2) D (a + (0 - ℓ 0 • u), ℓ 0) := by
    simpa using hd.hasFDerivAt
  unfold flowBoxMap
  refine (hd'.comp (0 : E) (hasFDerivAt_flowBoxArg a u ℓ 0)).congr_fderiv ?_
  ext h
  have hsplit : ((h - ℓ h • u, ℓ h) : E × ℝ) = (h - ℓ h • u, 0) + ℓ h • ((0 : E), (1 : ℝ)) := by
    simp
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, sub_apply, ContinuousLinearMap.smulRight_apply]
  rw [hsplit, map_add, map_smul, hDx, hDt]
  simp

end Flow

variable [FiniteDimensional ℝ E]

/-- **The straightening theorem** (flow-box theorem). A `C^n` vector field `w`, `1 ≤ n`, defined
near a point `a` of a finite-dimensional real normed space, with `w a ≠ 0`, is constant in suitable
`C^n` coordinates: there is an open partial homeomorphism `φ`, `C^n` on its source with `C^n`
inverse on its target, such that `a ∈ φ.source` and `dφ_y (w y) = w a` for every `y ∈ φ.source`. -/
theorem exists_openPartialHomeomorph_fderiv_eq_const {n : ℕ∞} (hn : 1 ≤ n) {w : E → E}
    {s : Set E} {a : E} (hw : ContDiffOn ℝ n w s) (hs : s ∈ 𝓝 a) (ha : w a ≠ 0) :
    ∃ φ : OpenPartialHomeomorph E E, a ∈ φ.source ∧ (∀ y ∈ φ.source, ContDiffAt ℝ n φ y) ∧
      (∀ z ∈ φ.target, ContDiffAt ℝ n φ.symm z) ∧ ∀ y ∈ φ.source, fderiv ℝ φ y (w y) = w a := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  set u := w a
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- A globally Lipschitz `C^n` field `g` agreeing with `w` on an open set `S ∋ a`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ∞, n = k + 1 := ⟨n - 1, (tsub_add_cancel_of_le hn).symm⟩
  have hw' : ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) w s := by
    rw [hk] at hw
    exact_mod_cast hw
  obtain ⟨g, K, hg, hgK, hgw⟩ :=
    hw'.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  obtain ⟨S, hSo, haS, hSg⟩ : ∃ S : Set E, IsOpen S ∧ a ∈ S ∧ ∀ y ∈ S, g y = w y := by
    obtain ⟨S, hS, hSo, haS⟩ := mem_nhds_iff.1 hgw
    exact ⟨S, hSo, haS, hS⟩
  -- The flow `Φ` of `g` and the flow-box coordinates `ψ`.
  set Φ := ODE.globalSolution g hgK with hΦ
  have hΦs : ContDiff ℝ n fun p : E × ℝ ↦ Φ p.1 p.2 := by
    rw [hk]
    exact_mod_cast ODE.contDiff_globalSolution g hgK hg
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) ha
  set ψ := flowBoxMap Φ a u ℓ with hψ
  have hψs : ContDiff ℝ n ψ :=
    hΦs.comp ((contDiff_const.add (contDiff_id.sub (ℓ.contDiff.smul contDiff_const))).prodMk
      ℓ.contDiff)
  have hψ0 : ψ 0 = a := by
    simp [hψ, flowBoxMap, hΦ, ODE.globalSolution_zero]
  have hψu (z : E) : fderiv ℝ ψ z u = g (ψ z) :=
    fderiv_flowBoxMap_apply hgK hℓ (hψs.differentiable hn0 z)
  have hψ0' : HasFDerivAt ψ (ContinuousLinearMap.id ℝ E) 0 :=
    hasFDerivAt_flowBoxMap_zero hgK (hSg a haS) (hΦs.differentiable hn0 _)
  -- Invert `ψ` near `0`, on the open set where `ψ` lands in `S`, where `g = w`.
  obtain ⟨Θ, hΘ, h0Θ, hΘS, hΘs, hΘg⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq hψs.contDiffOn
      (hSo.preimage hψs.continuous) (show ψ 0 ∈ S from hψ0 ▸ haS) (by exact_mod_cast hn)
      (e := ContinuousLinearEquiv.refl ℝ E) (by rw [ContinuousLinearEquiv.coe_refl, hψ0'.fderiv])
      fun z _ ↦ hψu z
  refine ⟨Θ.symm, hψ0 ▸ hΘ ▸ Θ.map_source h0Θ,
    fun y hy ↦ hΘs.contDiffAt (Θ.open_target.mem_nhds hy), fun z _ ↦ ?_, fun y hy ↦ ?_⟩
  · rw [OpenPartialHomeomorph.symm_symm, hΘ]
    exact hψs.contDiffAt
  · have hyS : y ∈ S := by
      rw [← Θ.right_inv hy, hΘ]
      exact hΘS (Θ.map_target hy)
    rw [← hSg y hyS]
    exact hΘg y hy

end TauCeti
