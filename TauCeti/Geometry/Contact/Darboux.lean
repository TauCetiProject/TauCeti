/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The contact Darboux theorem

Let `α` be a one-form on an open subset of a finite-dimensional real normed space `V` which is a
contact form at `x₀`: `α(x₀) ≠ 0` and `dα(x₀)` is nondegenerate on the hyperplane `ker α(x₀)`.
**The contact Darboux theorem**
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`) says that near
`x₀` the hyperplane field `ker α` is the standard one: some `C^r` diffeomorphism `Φ` from `V` to
`ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to a positive
multiple of `α` near `x₀`. Restricted to a neighbourhood of `x₀`, `Φ` is a contact chart which
sends `ker α` to the standard contact structure and preserves the coorientation.

The analytic input is the local contact form of Moser's argument, due to Gray
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq`):
if `α₀` and `α₁` agree to first order at `x₀` and `α₀` is contact there, a `C^r`
diffeomorphism `ψ` fixing `x₀` pulls `α₁` back to a positive multiple of `α₀` near `x₀`. Along
the straight-line family `α_t = (1 - t) α₀ + t α₁` one solves

`α_t(Y_t) = 0`, `ι_{Y_t} dα_t + (α₁ - α₀) = -σ_t α_t`

for a time-dependent vector field `Y_t` and a function `σ_t`. The pair `(σ_t, Y_t)` solves a
single linear equation for the symplectization form
`((s, v), (s', w)) ↦ s α_t(w) - α_t(v) s' + dα_t(v, w)` on `ℝ × V`, which is nondegenerate where
`α_t` is contact (`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`). At `x₀` this form
does not depend on `t`, so it is invertible near `x₀` uniformly for `t ∈ [0, 1]`
(`TauCeti.exists_contDiffOn_moserField`). The field `Y_t` vanishes where `α₀ = α₁`, in
particular at `x₀`, so its flow `ψ_t` exists near `x₀` up to time one
(`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`). By Cartan's formula
`∂ₜ α_t + L_{Y_t} α_t = -σ_t α_t`, so the pullbacks `ψ_t^* α_t` solve a scalar linear equation
(`TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`), and the integrating factor
(`TauCeti.eq_exp_integral_smul_of_hasDerivWithinAt_smul`) gives
`ψ_1^* α₁ = exp (-∫₀¹ σ_t(ψ_t x) dt) α₀` at each point `x` near `x₀`.

For the Darboux theorem, the linear normal form of a contact covector
(`Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`) gives linear coordinates
`L : V ≃ ℝⁿ × ℝⁿ × ℝ` in which `α(x₀) = dz` and `dα(x₀) = Σᵢ dqᵢ ∧ dpᵢ`. These are the values at
the origin of the standard form `TauCeti.innerProductContactForm` and of its exterior derivative,
so the pullback of the standard form along `y ↦ L (y - x₀)` agrees with `α` to first order at
`x₀`, and the Gray–Moser lemma deforms `α` into it.

As in `TauCeti.Geometry.Symplectic.Darboux.Basic`, forms on `V` are Mathlib's continuous
alternating maps with the exterior derivative `extDeriv`, and the pullback of `α` along `ψ` at `x`
is `(α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`. The standard contact form is a smooth form
on the model manifold `ℝⁿ × ℝⁿ × ℝ`, and its pullback is the manifold pullback `TauCeti.mpullback`.

These are statements about contact structures, that is about forms up to a positive factor. The
form-level Darboux theorem, which makes `α` itself standard in suitable coordinates, is not proved
here.

## Main results

* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq`:
  the local contact Gray–Moser lemma.
* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`: the contact
  Darboux theorem.

## References

* J. W. Gray, *Some global properties of contact structures*, Annals of Mathematics 69 (1959),
  421–450.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and Section 2.5 (Darboux's theorem).
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The symplectization form `((s, v), (t, w)) ↦ s a(w) - a(v) t + b v w` on `ℝ × V` of a
covector `a` and a bilinear form `b` (`Module.Dual.symplectizationForm`), as a continuous bilinear
map, so that it depends smoothly on `(a, b)`. -/
private def symplectizationCLM (a : V →L[ℝ] ℝ) (b : V →L[ℝ] V →L[ℝ] ℝ) :
    (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).smulRight (a.comp (ContinuousLinearMap.snd ℝ ℝ V)) -
    (a.comp (ContinuousLinearMap.snd ℝ ℝ V)).smulRight (ContinuousLinearMap.fst ℝ ℝ V) +
    ((ContinuousLinearMap.compL ℝ (ℝ × V) V ℝ).flip (ContinuousLinearMap.snd ℝ ℝ V)).comp
      (b.comp (ContinuousLinearMap.snd ℝ ℝ V))

private theorem symplectizationCLM_apply (a : V →L[ℝ] ℝ) (b : V →L[ℝ] V →L[ℝ] ℝ)
    (p q : ℝ × V) : symplectizationCLM a b p q = p.1 * a q.2 - a p.2 * q.1 + b p.2 q.2 := by
  simp [symplectizationCLM]

private theorem contDiffOn_symplectizationCLM {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {n : WithTop ℕ∞} {s : Set P} {a : P → V →L[ℝ] ℝ}
    {b : P → V →L[ℝ] V →L[ℝ] ℝ} (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) :
    ContDiffOn ℝ n (fun p ↦ symplectizationCLM (a p) (b p)) s := by
  have ha' : ContDiffOn ℝ n (fun p ↦ (a p).comp (ContinuousLinearMap.snd ℝ ℝ V)) s :=
    ha.clm_comp contDiffOn_const
  exact ((contDiffOn_const.smulRight ha').sub (ha'.smulRight contDiffOn_const)).add
    (contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const))

/-- At a covector `a` which is contact for `b`, the symplectization form is injective. -/
private theorem injective_symplectizationCLM {a : V →L[ℝ] ℝ} {b : V →L[ℝ] V →L[ℝ] ℝ}
    (ha : ∃ v, a v ≠ 0) (hb : ∀ v, a v = 0 → (∀ w, a w = 0 → b v w = 0) → v = 0) :
    Function.Injective (symplectizationCLM a b) := by
  have hsep := Module.Dual.separatingLeft_symplectizationForm_iff
    (a := (a : Module.Dual ℝ V)) (B := ContinuousLinearMap.coeLM ℝ ∘ₗ (b : V →ₗ[ℝ] V →L[ℝ] ℝ)) |>.2
      ⟨fun h ↦ ha.elim fun v hv ↦ hv (LinearMap.congr_fun h v),
        fun v hv ↦ Subtype.ext <| hb v v.2 fun w hw ↦ hv ⟨w, hw⟩⟩
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ hsep p fun q ↦ ?_
  have h := congrArg (fun φ ↦ φ q) hp
  simp only [symplectizationCLM_apply, zero_apply] at h
  simp only [Module.Dual.symplectizationForm_apply, ContinuousLinearMap.coe_coe,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coeLM_apply]
  linear_combination h

/-- **The contact Moser identity.** Let `α_t = (1 - t) α₀ + t α₁`, and let `ψ_t` move along a
time-dependent field `Y_t`, with derivative at `x` solving the variational equation. Suppose that
near the orbit `t ↦ ψ_t x`, `t ∈ [0, 1]`, the field `Y_t` lies in `ker α_t`, and that along the
orbit `ι_{Y_t} dα_t + (α₁ - α₀) = -σ_t α_t`. Then `∂ₜ α_t + L_{Y_t} α_t = -σ_t α_t` along the
orbit, so `ψ_1^* α₁ = exp (-∫₀¹ σ_t(ψ_t x) dt) • ψ_0^* α₀` at `x`. -/
private theorem compContinuousLinearMap_fderiv_eq_exp_integral_smul
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ Y : ℝ → V → V} {σ : ℝ → V → ℝ} {x : V}
    (hα₀ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ α₀ (ψ t x))
    (hα₁ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ α₁ (ψ t x))
    (hker : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ᶠ y in 𝓝 (ψ t x), (1 - t) * α₀ y ![Y t y] + t * α₁ y ![Y t y] = 0)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w,
      α₁ (ψ t x) ![w] - α₀ (ψ t x) ![w] + ((1 - t) * extDeriv α₀ (ψ t x) ![Y t (ψ t x), w] +
        t * extDeriv α₁ (ψ t x) ![Y t (ψ t x), w]) =
      -σ t (ψ t x) * ((1 - t) * α₀ (ψ t x) ![w] + t * α₁ (ψ t x) ![w]))
    (hσ : ContinuousOn (fun t ↦ σ t (ψ t x)) (Icc 0 1))
    (hYd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (Y t) (ψ t x))
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ ψ s x) (Y t (ψ t x)) t)
    (hDψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
      (fderiv ℝ (Y t) (ψ t x) ∘L fderiv ℝ (ψ t) x) t) :
    (α₁ (ψ 1 x)).compContinuousLinearMap (fderiv ℝ (ψ 1) x) =
      Real.exp (∫ t in (0 : ℝ)..1, -σ t (ψ t x)) •
        (α₀ (ψ 0 x)).compContinuousLinearMap (fderiv ℝ (ψ 0) x) := by
  -- The pullbacks `P t = ψ_t^* α_t` at `x` solve `P' = -σ_t(ψ_t x) • P`.
  let ω : ℝ → V → V [⋀^Fin 1]→L[ℝ] ℝ := fun t y ↦ (1 - t) • α₀ y + t • α₁ y
  let P : ℝ → V [⋀^Fin 1]→L[ℝ] ℝ := fun t ↦
    (ω t (ψ t x)).compContinuousLinearMap (fderiv ℝ (ψ t) x)
  have hP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt P (-σ t (ψ t x) • P t) (Icc 0 1) t := by
    set y := ψ t x with hy
    have hd₀ := hα₀ t ht
    have hd₁ := hα₁ t ht
    have hω : DifferentiableAt ℝ (fun p : ℝ × V ↦ ω p.1 p.2) (t, y) := by
      have h₀ : DifferentiableAt ℝ (fun p : ℝ × V ↦ α₀ p.2) (t, y) :=
        hd₀.comp (t, y) differentiableAt_snd
      have h₁ : DifferentiableAt ℝ (fun p : ℝ × V ↦ α₁ p.2) (t, y) :=
        hd₁.comp (t, y) differentiableAt_snd
      fun_prop
    have hωt : DifferentiableAt ℝ (ω t) y := (hd₀.const_smul (1 - t)).add (hd₁.const_smul t)
    -- The time derivative of the family is `α₁ - α₀`.
    have hdt : deriv (fun s ↦ ω s y) t = α₁ y - α₀ y := by
      have hd : HasDerivAt (fun s ↦ ω s y) ((-1 : ℝ) • α₀ y + (1 : ℝ) • α₁ y) t :=
        (((hasDerivAt_id t).const_sub 1).smul_const (α₀ y)).add
          ((hasDerivAt_id t).smul_const (α₁ y))
      rw [hd.deriv]
      module
    have hext : extDeriv (ω t) y = (1 - t) • extDeriv α₀ y + t • extDeriv α₁ y := by
      -- Rewrite the family with the pointwise operations on functions, as `extDeriv_add` expects.
      have e' : ω t = (1 - t) • α₀ + t • α₁ := rfl
      rw [e', extDeriv_add (hd₀.const_smul _) (hd₁.const_smul _), extDeriv_smul, extDeriv_smul]
    -- Since `α_t(Y_t) = 0` near `y`, Cartan's formula reduces to `L_{Y_t} α_t = ι_{Y_t} dα_t`.
    have hzero : extDeriv (fun z ↦ (ω t z).curryLeft (Y t z)) y = 0 := by
      have hev0 : (fun z ↦ (ω t z).curryLeft (Y t z)) =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [hker t ht] with z hz
        ext m
        have hm : m = ![] := Subsingleton.elim _ _
        subst hm
        simpa [ω] using hz
      rw [hev0.extDeriv_eq, extDeriv, fderiv_const_apply,
        ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]
    have hrate : deriv (fun s ↦ ω s y) t + lieDerivForm (Y t) (ω t) y = -σ t y • ω t y := by
      rw [hdt, lieDerivForm_eq_curryLeft_extDeriv_add hωt (hYd t ht), hzero, add_zero, hext]
      ext m
      have hm : m = ![m 0] := by
        ext i
        fin_cases i
        rfl
      rw [hm]
      simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
        smul_eq_mul, ω]
      linear_combination hY t ht (m 0)
    have h := hasDerivAt_compContinuousLinearMap_fderiv hω (hψ t ht) (hDψ t ht)
    rw [hrate] at h
    convert h.hasDerivWithinAt using 1
    ext m
    simp [P, ← hy]
  have hint := eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := V [⋀^Fin 1]→L[ℝ] ℝ)
    zero_le_one hσ.neg hP
  simpa [P, ω] using hint

variable [FiniteDimensional ℝ V]

/-- **The contact Gray–Moser lemma**, local form. Let `α₀`, `α₁` be `C^(r+1)` one-forms
(`r ≥ 1`) on an open subset `W` of a finite-dimensional real normed space which agree to first
order at `x₀ ∈ W`: `α₁(x₀) = α₀(x₀)` and `dα₁(x₀) = dα₀(x₀)`. If `α₀` is a contact form at `x₀`,
that is `α₀(x₀) ≠ 0` and `dα₀(x₀)` is nondegenerate on `ker α₀(x₀)`, then some `C^r`
diffeomorphism `ψ` of the space pulls `α₁` back to a positive multiple of `α₀` near `x₀`. In
particular `ψ` maps the contact hyperplanes of `α₀` to those of `α₁`, preserving their
coorientations. Moreover `ψ` fixes, near `x₀`, every point at which `α₀` and `α₁` agree; in
particular `ψ x₀ = x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r)
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα₀ : ContDiffOn ℝ (r + 1) α₀ W)
    (hα₁ : ContDiffOn ℝ (r + 1) α₁ W) (heq : α₁ x₀ = α₀ x₀)
    (hdeq : extDeriv α₁ x₀ = extDeriv α₀ x₀) (hne : ∃ v, α₀ x₀ ![v] ≠ 0)
    (hnd : ∀ v, α₀ x₀ ![v] = 0 → (∀ w, α₀ x₀ ![w] = 0 → extDeriv α₀ x₀ ![v, w] = 0) → v = 0) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (f : V → ℝ), (∀ᶠ x in 𝓝 x₀, α₁ x = α₀ x → ψ x = x) ∧
      ∀ᶠ x in 𝓝 x₀, 0 < f x ∧
        (α₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = f x • α₀ x := by
  have hr0 : ((r : WithTop ℕ∞) + 1) ≠ 0 := by simp
  -- One-forms as covectors and two-forms as bilinear maps.
  let e : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he (a : V [⋀^Fin 1]→L[ℝ] ℝ) (w : V) : e a w = a ![w] := by
    simp only [e, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  have hflat := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r) (E := V [⋀^Fin 2]→L[ℝ] ℝ)
    (F := V →L[ℝ] V →L[ℝ] ℝ) (ContinuousAlternatingMap.flatL ℝ V ℝ)
  have hdα {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) :
      ContDiffOn ℝ r (extDeriv α) W := fun y hy ↦
    (contDiffAt_extDeriv (hα.contDiffAt (hW.mem_nhds hy)) le_rfl).contDiffWithinAt
  -- The symplectization forms of `α₀` and `α₁`, as families on `ℝ × V` constant in the first
  -- coordinate, so that the Moser field construction applies with `ℝ × V` as its parameter space.
  let B : (V → V [⋀^Fin 1]→L[ℝ] ℝ) → ℝ × V → (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ := fun α q ↦
    symplectizationCLM (e (α q.2)) (ContinuousAlternatingMap.flatL ℝ V ℝ (extDeriv α q.2))
  have hB {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) :
      ContDiffOn ℝ r (B α) (univ ×ˢ W) :=
    contDiffOn_symplectizationCLM
      ((e.contDiff.comp_contDiffOn (hα.of_le le_self_add)).comp contDiffOn_snd
        fun q (hq : q ∈ univ ×ˢ W) ↦ hq.2)
      ((hflat.comp_contDiffOn (hdα hα)).comp contDiffOn_snd fun q (hq : q ∈ univ ×ˢ W) ↦ hq.2)
  let γ : ℝ × V → (ℝ × V) →L[ℝ] ℝ := fun q ↦
    (e (α₁ q.2 - α₀ q.2)).comp (ContinuousLinearMap.snd ℝ ℝ V)
  have hγ : ContDiffOn ℝ r γ (univ ×ˢ W) :=
    ((e.contDiff.comp_contDiffOn ((hα₁.of_le le_self_add).sub (hα₀.of_le le_self_add))).comp
      contDiffOn_snd fun q (hq : q ∈ univ ×ˢ W) ↦ hq.2).clm_comp contDiffOn_const
  have hL : (B α₀ (0, x₀)).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_injective <| injective_symplectizationCLM
      (by simpa only [he] using hne)
      (by simpa only [he, ContinuousAlternatingMap.flatL_apply_apply] using hnd)
  have hB₁ : B α₁ (0, x₀) = B α₀ (0, x₀) := by
    simp only [B, heq, hdeq]
  obtain ⟨T, U', X, hT, hU', hTI, hxU', hU'W, hX, hXeq⟩ := exists_contDiffOn_moserField hL
    (isOpen_univ.prod hW) ⟨mem_univ _, hx₀⟩ (hB hα₀) (hB hα₁) rfl hB₁ hγ
  -- The Moser field `Y` and the multiplier `σ` on the slice `{0} × V`.
  let U : Set V := (fun y ↦ ((0 : ℝ), y)) ⁻¹' U'
  have hU : IsOpen U := hU'.preimage (continuous_const.prodMk continuous_id)
  have hxU : x₀ ∈ U := hxU'
  have hUW (y : V) (hy : y ∈ U) : y ∈ W := (hU'W hy).2
  let Y : ℝ → V → V := fun t y ↦ (X (t, (0, y))).2
  let σ : ℝ → V → ℝ := fun t y ↦ (X (t, (0, y))).1
  have hXs : ContDiffOn ℝ r (fun p : ℝ × V ↦ X (p.1, (0, p.2))) (T ×ˢ U) :=
    hX.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
      fun p hp ↦ ⟨hp.1, hp.2⟩
  have hY : ContDiffOn ℝ r (fun p : ℝ × V ↦ Y p.1 p.2) (T ×ˢ U) :=
    (ContinuousLinearMap.snd ℝ ℝ V).contDiff.comp_contDiffOn hXs
  -- The Moser equation, evaluated on `(s', w)`.
  have hmoser (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) (s' : ℝ) (w : V) :
      (1 - t) * (σ t y * α₀ y ![w] - α₀ y ![Y t y] * s' + extDeriv α₀ y ![Y t y, w]) +
        t * (σ t y * α₁ y ![w] - α₁ y ![Y t y] * s' + extDeriv α₁ y ![Y t y, w]) =
      -(α₁ y ![w] - α₀ y ![w]) := by
    have h := (hXeq (t, (0, y)) ⟨ht, hy⟩ (X (t, (0, y)))).2 rfl (s', w)
    simpa [B, γ, symplectizationCLM_apply, he, ContinuousAlternatingMap.flatL_apply_apply] using h
  -- The Moser field is tangent to the kernels: `α_t(Y_t) = 0`.
  have hkerY (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) :
      (1 - t) * α₀ y ![Y t y] + t * α₁ y ![Y t y] = 0 := by
    have h := hmoser t ht y hy 1 0
    simp only [(α₀ y).map_coord_zero (m := ![0]) 0 rfl, (α₁ y).map_coord_zero (m := ![0]) 0 rfl,
      (extDeriv α₀ y).map_coord_zero (m := ![Y t y, 0]) 1 rfl,
      (extDeriv α₁ y).map_coord_zero (m := ![Y t y, 0]) 1 rfl] at h
    linarith
  -- The Moser field vanishes where `α₀` and `α₁` agree, in particular at `x₀`.
  have hY₀ (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) (hαy : α₁ y = α₀ y) : Y t y = 0 := by
    have h := ((hXeq (t, (0, y)) ⟨ht, hy⟩ 0).1 fun w ↦ by simp [γ, hαy]).symm
    simp only [Y, h, Prod.snd_zero]
  -- The time-dependent flow of the Moser field.
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := Y) hr hT hU hTI hxU hY
      fun t ht ↦ hY₀ t ht x₀ hxU heq
  let Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V := ⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩
  -- The diffeomorphism is the time-one map of the flow, by construction.
  have hΦ : ⇑Φ = ψ 1 := rfl
  refine ⟨Φ, fun x ↦ Real.exp (∫ u in (0 : ℝ)..1, -σ u (ψ u x)), ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy hαy
    rw [hΦ]
    exact hψfix y (fun t ht ↦ hY₀ t ht y hy hαy) 1
  filter_upwards [hev] with x hx
  refine ⟨Real.exp_pos _, ?_⟩
  have hd {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ α (ψ t x) :=
    (hα.contDiffAt (hW.mem_nhds (hUW _ (hx t ht).1))).differentiableAt hr0
  have hYd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ (Y t) (ψ t x) :=
    ((hY.contDiffAt ((hT.prod hU).mem_nhds ⟨hTI ht, (hx t ht).1⟩)).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')).comp (ψ t x)
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hσ : ContinuousOn (fun t ↦ σ t (ψ t x)) (Icc 0 1) := by
    have hc : ContinuousOn (fun u : ℝ ↦ (u, ψ u x)) (Icc 0 1) := fun u hu ↦
      (continuousAt_id.prodMk (hx u hu).2.1.continuousAt).continuousWithinAt
    exact continuous_fst.comp_continuousOn
      (hXs.continuousOn.comp hc fun u hu ↦ ⟨hTI hu, (hx u hu).1⟩)
  have h := compContinuousLinearMap_fderiv_eq_exp_integral_smul (hd hα₀) (hd hα₁)
    (fun t ht ↦ Filter.mem_of_superset (hU.mem_nhds (hx t ht).1) fun y hy ↦ hkerY t (hTI ht) y hy)
    (fun t ht w ↦ by linear_combination hmoser t (hTI ht) _ (hx t ht).1 0 w) hσ hYd
    (fun t ht ↦ (hx t ht).2.1) (fun t ht ↦ (hx t ht).2.2)
  rw [hΦ, h, hψ0, fderiv_id]
  ext m
  simp

/-- **The contact Darboux theorem.** Let `α` be a `C^(r+1)` one-form (`r ≥ 1`) on an open subset
`W` of a finite-dimensional real normed space `V`, which is a contact form at `x₀ ∈ W`: `α(x₀) ≠ 0`
and `dα(x₀)` is nondegenerate on `ker α(x₀)`. Then there are `n` and a `C^r` diffeomorphism `Φ`
from `V` to `ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to a positive multiple of `α` near
`x₀`. Thus `Φ` restricts to a contact chart around `x₀`, sending the contact hyperplanes of `α`
to the standard ones and preserving their coorientations. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r)
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hne : ∃ v, α x₀ ![v] ≠ 0)
    (hnd : ∀ v, α x₀ ![v] = 0 → (∀ w, α x₀ ![w] = 0 → extDeriv α x₀ ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (f : V → ℝ),
      Φ x₀ = 0 ∧ ∀ᶠ y in 𝓝 x₀, 0 < f y ∧
        mpullback 𝓘(ℝ, V) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) Φ
          (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 y = f y • α y := by
  -- Linear coordinates `L` put `(α(x₀), dα(x₀))` in normal form; the standard form pulled back
  -- along `y ↦ L (y - x₀)` then agrees with `α` to first order at `x₀`, and the contact
  -- Gray–Moser lemma deforms `α` into it.
  -- The linear normal form of `(α(x₀), dα(x₀))`, in the coordinates `(q, p, z)` of `ℝⁿ × ℝⁿ × ℝ`.
  let a : Module.Dual ℝ V :=
    ((ContinuousAlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1)).symm (α x₀) : V →L[ℝ] ℝ)
  have ha (v : V) : a v = α x₀ ![v] := by
    simp only [a, ContinuousLinearMap.coe_coe,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  let B : LinearMap.BilinForm ℝ V := ContinuousLinearMap.coeLM ℝ ∘ₗ
    (ContinuousAlternatingMap.flatL ℝ V ℝ (extDeriv α x₀) : V →ₗ[ℝ] V →L[ℝ] ℝ)
  have hB (v w : V) : B v w = extDeriv α x₀ ![v, w] := by
    simp [B, ContinuousAlternatingMap.flatL_apply_apply]
  have hBalt : B.IsAlt := fun v ↦ by
    rw [hB]
    exact (extDeriv α x₀).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)
  have hc : a.IsContact B := (Module.Dual.isContact_iff_of_isRefl hBalt.isRefl).2
    ⟨fun h ↦ by
      obtain ⟨v, hv⟩ := hne
      exact hv (by rw [← ha, h, LinearMap.zero_apply]),
      fun v hv hvw ↦ hnd v (by rwa [← ha]) fun w hw ↦ by rw [← hB]; exact hvw w (by rwa [ha])⟩
  obtain ⟨n, e₀, hae, hBe⟩ := hc.exists_linearEquiv_eq_stdContact hBalt
  have hae' (v : V) : (e₀ v).2.2 = α x₀ ![v] := by
    rw [← ha, ← hae]
    simp
  have hBe' (v w : V) :
      (e₀ v).1 ⬝ᵥ (e₀ w).2.1 - (e₀ v).2.1 ⬝ᵥ (e₀ w).1 = extDeriv α x₀ ![v, w] := by
    rw [← hB, ← hBe]
    simp
  -- The same coordinates, landing in `ℝⁿ × ℝⁿ × ℝ` with Euclidean factors.
  set E := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ
  let c : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let L : V ≃L[ℝ] E :=
    (e₀.trans (c.prodCongr (c.prodCongr (LinearEquiv.refl ℝ ℝ)))).toContinuousLinearEquiv
  have hL₁ (v : V) (i : Fin n) : (L v).1 i = (e₀ v).1 i := by simp [L, c]
  have hL₂ (v : V) (i : Fin n) : (L v).2.1 i = (e₀ v).2.1 i := by simp [L, c]
  have hL₃ (v : V) : (L v).2.2 = (e₀ v).2.2 := by simp [L, c]
  -- The standard contact form `σ = dz - ⟪p, dq⟫`, and its pullback `α₁` along `y ↦ L (y - x₀)`.
  let σ : E → E [⋀^Fin 1]→L[ℝ] ℝ := (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1
  have hσ : ContDiff ℝ (⊤ : ℕ∞) σ :=
    isSmoothForm_modelSpace_iff.1 (innerProductContactForm (EuclideanSpace ℝ (Fin n))).isSmoothForm
  let g : V → E := fun y ↦ L (y - x₀)
  have hg : ContDiff ℝ ⊤ g := L.contDiff.comp (contDiff_id.sub contDiff_const)
  have hgd (y : V) : HasFDerivAt g (L : V →L[ℝ] E) y :=
    (L.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  let α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ := fun y ↦ (σ (g y)).compContinuousLinearMap (fderiv ℝ g y)
  have hα₁ : ContDiffOn ℝ (r + 1) α₁ W := fun y _ ↦
    ((hg.contDiffAt.of_le le_top).differentialForm_pullback
      (hσ.contDiffAt.of_le (by exact_mod_cast le_top)) (fun _ ↦ by simp)).contDiffWithinAt
  have hgx₀ : g x₀ = 0 := by simp [g]
  have hσ₀ (z v : E) : σ z ![v] = v.2.2 - ⟪z.2.1, v.1⟫_ℝ := innerProductContactForm_apply _ z v
  have hdσ (z v w : E) : extDeriv σ z ![v, w] = ∑ i, (v.1 i * w.2.1 i - v.2.1 i * w.1 i) := by
    rw [← mextDeriv_eq_extDeriv]
    exact mextDeriv_innerProductContactForm_euclideanSpace_apply z v w
  -- `α₁` agrees with `α` to first order at `x₀`.
  have heq : α₁ x₀ = α x₀ := by
    ext m
    have hm : m = ![m 0] := by
      ext i
      fin_cases i
      rfl
    have hLm : ⇑L ∘ ![m 0] = ![L (m 0)] := by
      funext i
      fin_cases i
      rfl
    rw [hm]
    simp [α₁, (hgd x₀).fderiv, hgx₀, hLm, hσ₀, hL₃, hae']
  have hdeq : extDeriv α₁ x₀ = extDeriv α x₀ := by
    rw [extDeriv_pullback (hσ.differentiable (by simp) _) hg.contDiffAt (by simp)]
    ext m
    have hm : m = ![m 0, m 1] := by
      ext i
      fin_cases i <;> rfl
    have hLm : ⇑L ∘ ![m 0, m 1] = ![L (m 0), L (m 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [hm, ← hBe']
    simp [(hgd x₀).fderiv, hLm, hdσ, hL₁, hL₂, dotProduct, Finset.sum_sub_distrib]
  -- The contact Gray–Moser lemma deforms `α` into the model `α₁`; follow it by the coordinates `g`.
  obtain ⟨ψ, f, hfix, hψ⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq hr hW hx₀
      hα hα₁ heq hdeq hne hnd
  have hψx₀ : ψ x₀ = x₀ := hfix.self_of_nhds heq
  let A : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, E)⟯ E :=
    (Diffeomorph.smulAdd r (1 : ℝ) (-x₀) one_ne_zero).trans (L.toContDiffDiffeomorph r)
  have hA : ⇑A = g := by
    funext y
    simp [A, g, Diffeomorph.smulAdd_apply, sub_eq_add_neg]
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr).ne'
  refine ⟨n, ψ.trans A, f, by simp [hA, hψx₀, hgx₀], ?_⟩
  filter_upwards [hψ] with y ⟨hfy, hy⟩
  refine ⟨hfy, ?_⟩
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
    ((contMDiff_iff_contDiff.1 ψ.contMDiff).differentiable hr0 y).hasFDerivAt
  have hΦ : HasFDerivAt (ψ.trans A) ((L : V →L[ℝ] E).comp (fderiv ℝ ψ y)) y := by
    rw [Diffeomorph.coe_trans, hA]
    exact (hgd (ψ y)).comp y hψd
  ext m
  rw [mpullback_apply, mfderiv_eq_fderiv, hΦ.fderiv, ← hy, Diffeomorph.coe_trans,
    Function.comp_apply, congrFun hA]
  simp only [α₁, (hgd (ψ y)).fderiv]
  -- Both sides evaluate `σ (g (ψ y))` on the vectors `L (Dψ (m i))`.
  rfl

end TauCeti
