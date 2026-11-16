/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
public import TauCeti.Geometry.Symplectic.Liouville.Linear
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Analysis.Normed.Module.Alternating.ContactNormalForm
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Contact.Symplectization.Linear

/-!
# The contact Moser lemma and Darboux's theorem for contact forms

Let `α₀`, `α₁` be `C^(r+1)` one-forms (`r ≥ 1`) on an open subset `W` of a finite-dimensional real
normed space, which agree at a point `x₀` together with their exterior derivatives, and let `α₁`
be a contact form at `x₀` (`TauCeti.IsContactFormAt`). The **contact Moser lemma**
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq`)
gives a `C^r` diffeomorphism `ψ` of the space and a function `g` with

`ψ^* α₁ = g • α₀`, `g > 0`,

on a neighbourhood of `x₀`. So `ψ` carries the contact structure `ker α₀` to `ker α₁` near `x₀`,
preserving the coorientations. Moreover `ψ` fixes, near `x₀`, every point at which `α₀` and `α₁`
agree; in particular `ψ x₀ = x₀`.

Every contact form `α` at `x₀` has the same value and exterior derivative at `x₀` as its
osculating model

`α_lin(x) = α(x₀) + ½ ι_{x - x₀} dα(x₀)`,

a constant plus the radial primitive `ContinuousLinearMap.liouvilleFormCLM` of `dα(x₀)`, so its
exterior derivative is the constant form `dα(x₀)`
(`ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew`). Hence **Darboux's theorem**
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`): some `C^r`
diffeomorphism fixing `x₀` pulls `α` back to a positive multiple of `α_lin` near `x₀`. In linear
coordinates in which `α(x₀)` and `dα(x₀)` are the standard covector `dz` and the standard
symplectic form `Σᵢ dqᵢ ∧ dpᵢ` (`Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`), the
model is `dz + ½ Σᵢ (qᵢ dpᵢ - pᵢ dqᵢ)`.

The proof is Moser's deformation argument along the straight-line family
`αₜ = (1 - t) α₀ + t α₁`, which is contact near `x₀` for all `t ∈ [0, 1]`. The contact Moser field
`Yₜ` and the conformal factor `σₜ` are determined by

`αₜ(Yₜ) = 0`, `ι_{Yₜ} dαₜ + α₁ - α₀ = -σₜ αₜ`.

Pairing the unknown `(σₜ, Yₜ)` with `(s, w) ∈ ℝ × V` turns this system into the Moser contraction
equation for the bilinear form `((s, v), (s', w)) ↦ s αₜ(w) - s' αₜ(v) + dαₜ(v, w)` on `ℝ × V`,
the symplectization form of `αₜ` (`ContinuousAlternatingMap.symplectizationFormCLM`). It is
invertible where `αₜ` is contact (`TauCeti.IsContactFormAt.isInvertible_symplectizationFormCLM`),
so the contraction equation is solved by `TauCeti.exists_contDiffOn_moserField`. The field `Yₜ`
vanishes wherever `α₀` and `α₁` agree, in particular at `x₀`, so its time-dependent flow `ψₜ`
exists near `x₀` up to time one
(`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`). Since `αₜ(Yₜ) = 0`,
Cartan's formula gives `∂ₜ αₜ + L_{Yₜ} αₜ = -σₜ αₜ`, so the pullbacks `Pₜ = ψₜ^* αₜ` at a point
`x` satisfy the linear equation `∂ₜ Pₜ = -σₜ(ψₜ x) Pₜ`. Integrating,
`ψ₁^* α₁ = exp (-∫₀¹ σₜ(ψₜ x) dt) • α₀` at `x`.

Taking for `α₀` instead the standard contact form `dz - Σᵢ pᵢ dqᵢ`
(`TauCeti.innerProductContactForm`), pulled back along affine coordinates centred at `x₀` in which
`α(x₀)` and `dα(x₀)` are standard
(`ContinuousAlternatingMap.exists_continuousLinearEquiv_stdContact`), gives a **Darboux chart**
(`TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`): a `C^r`
diffeomorphism `Φ : V ≃ ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` pulling the standard contact form back to a
positive multiple of `α` near `x₀`. So near `x₀` the contact structure `ker α` is the standard one
in the coordinates `Φ`, with matching coorientations.

## Main results

* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq`:
  the contact Moser lemma.
* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`: Darboux's
  theorem, conformal to the osculating model form.
* `TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`: a Darboux
  chart to the standard contact form, up to a positive factor.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1 (Darboux's theorem by Moser's trick).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The contact Moser lemma -/

/-- The pullbacks `ψₜ^* αₜ` at `x` along a family of maps moving with a contact Moser field `Yₜ`
for the straight-line family `αₜ = (1 - t) α₀ + t α₁`, with conformal factor `σₜ`, solve the
linear equation `∂ₜ (ψₜ^* αₜ) = -σₜ(ψₜ x) ψₜ^* αₜ`. -/
private theorem hasDerivAt_compContinuousLinearMap_fderiv_contactMoser
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ Y : ℝ → V → V} {σ : ℝ → V → ℝ} {U : Set V} {x : V}
    {t : ℝ} (hU : IsOpen U) (hmem : ψ t x ∈ U) (hα₀ : ∀ y ∈ U, DifferentiableAt ℝ α₀ y)
    (hα₁ : ∀ y ∈ U, DifferentiableAt ℝ α₁ y) (hY : DifferentiableAt ℝ (Y t) (ψ t x))
    (hker : ∀ y ∈ U, ((1 - t) • α₀ y + t • α₁ y) ![Y t y] = 0)
    (hYd : ((1 - t) • extDeriv α₀ (ψ t x) + t • extDeriv α₁ (ψ t x)).curryLeft (Y t (ψ t x)) =
      -(α₁ (ψ t x) - α₀ (ψ t x)) - σ t (ψ t x) • ((1 - t) • α₀ (ψ t x) + t • α₁ (ψ t x)))
    (hψ : HasDerivAt (fun s ↦ ψ s x) (Y t (ψ t x)) t)
    (hDψ : HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
      (fderiv ℝ (Y t) (ψ t x) ∘L fderiv ℝ (ψ t) x) t) :
    HasDerivAt (fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
        (fderiv ℝ (ψ s) x))
      (-σ t (ψ t x) • ((1 - t) • α₀ (ψ t x) + t • α₁ (ψ t x)).compContinuousLinearMap
        (fderiv ℝ (ψ t) x)) t := by
  set z := ψ t x
  have h₀ := hα₀ z hmem
  have h₁ := hα₁ z hmem
  have hω : DifferentiableAt ℝ (fun p : ℝ × V ↦ (1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) (t, z) := by
    fun_prop
  have h := hasDerivAt_compContinuousLinearMap_fderiv
    (ω := fun s y ↦ (1 - s) • α₀ y + s • α₁ y) hω hψ hDψ
  refine h.congr_deriv ?_
  -- The time derivative of the straight-line family is `α₁ - α₀`.
  have hdt : deriv (fun s ↦ (1 - s) • α₀ z + s • α₁ z) t = α₁ z - α₀ z := by
    have hd : HasDerivAt (fun s ↦ (1 - s) • α₀ z + s • α₁ z)
        ((-1 : ℝ) • α₀ z + (1 : ℝ) • α₁ z) t :=
      (((hasDerivAt_id t).const_sub 1).smul_const (α₀ z)).add ((hasDerivAt_id t).smul_const (α₁ z))
    rw [hd.deriv]
    module
  -- Cartan's formula: `ι_{Yₜ} αₜ` vanishes near `z`, so `L_{Yₜ} αₜ = ι_{Yₜ} dαₜ`.
  have hι : (fun y ↦ ((1 - t) • α₀ y + t • α₁ y).curryLeft (Y t y)) =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hU.mem_nhds hmem] with y hy
    ext m
    simpa [Subsingleton.elim m ![]] using hker y hy
  have hωt : DifferentiableAt ℝ (fun y ↦ (1 - t) • α₀ y + t • α₁ y) z := by fun_prop
  have hext : extDeriv (fun y ↦ (1 - t) • α₀ y + t • α₁ y) z =
      (1 - t) • extDeriv α₀ z + t • extDeriv α₁ z := by
    -- Rewrite the family with the pointwise operations on functions, as `extDeriv_add` expects.
    have e : (fun y ↦ (1 - t) • α₀ y + t • α₁ y) = (1 - t) • α₀ + t • α₁ := rfl
    rw [e, extDeriv_add (h₀.const_smul _) (h₁.const_smul _), extDeriv_smul, extDeriv_smul]
  rw [hdt, lieDerivForm_eq_curryLeft_extDeriv_add hωt hY, hι.extDeriv_eq,
    ContinuousAlternatingMap.extDeriv_const, Pi.zero_apply, add_zero, hext, hYd]
  have hsum : α₁ z - α₀ z + (-(α₁ z - α₀ z) - σ t z • ((1 - t) • α₀ z + t • α₁ z)) =
      -σ t z • ((1 - t) • α₀ z + t • α₁ z) := by
    module
  rw [hsum]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul]

variable [FiniteDimensional ℝ V]

/-- **The contact Moser field.** For one-forms `α₀`, `α₁` which agree at `x₀` together with their
exterior derivatives, with `α₁` contact there, the straight-line family `αₜ = (1 - t) α₀ + t α₁`
has, on an open time neighbourhood `T` of `[0, 1]` and an open neighbourhood `U` of `x₀`, a jointly
`C^r` field `Yₜ` and a continuous factor `σₜ` with `αₜ(Yₜ) = 0` and
`ι_{Yₜ} dαₜ = -(α₁ - α₀) - σₜ αₜ`. The field vanishes wherever `α₀` and `α₁` agree. -/
private theorem exists_contDiffOn_contactMoserField
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞}
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα₀ : ContDiffOn ℝ (r + 1) α₀ W)
    (hα₁ : ContDiffOn ℝ (r + 1) α₁ W) (heq : α₁ x₀ = α₀ x₀)
    (hdeq : extDeriv α₁ x₀ = extDeriv α₀ x₀) (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α₁ x₀) :
    ∃ (T : Set ℝ) (U : Set V) (σ : ℝ → V → ℝ) (Y : ℝ → V → V), IsOpen T ∧ IsOpen U ∧
      Icc 0 1 ⊆ T ∧ x₀ ∈ U ∧ U ⊆ W ∧ ContDiffOn ℝ r (fun p : ℝ × V ↦ Y p.1 p.2) (T ×ˢ U) ∧
      ContinuousOn (fun p : ℝ × V ↦ σ p.1 p.2) (T ×ˢ U) ∧
      (∀ t ∈ T, ∀ y ∈ U, ((1 - t) • α₀ y + t • α₁ y) ![Y t y] = 0) ∧
      (∀ t ∈ T, ∀ y ∈ U, ((1 - t) • extDeriv α₀ y + t • extDeriv α₁ y).curryLeft (Y t y) =
        -(α₁ y - α₀ y) - σ t y • ((1 - t) • α₀ y + t • α₁ y)) ∧
      (∀ t ∈ T, ∀ y ∈ U, α₁ y = α₀ y → Y t y = 0) := by
  have hrle : (r : WithTop ℕ∞) ≤ r + 1 := le_self_add
  -- The symplectization forms of `α₀` and `α₁`, on `ℝ × V`, and the right-hand side `α₁ - α₀`.
  let B₀ : ℝ × V → ℝ × V →L[ℝ] ℝ × V →L[ℝ] ℝ :=
    fun p ↦ (α₀ p.2).symplectizationFormCLM (extDeriv α₀ p.2)
  let B₁ : ℝ × V → ℝ × V →L[ℝ] ℝ × V →L[ℝ] ℝ :=
    fun p ↦ (α₁ p.2).symplectizationFormCLM (extDeriv α₁ p.2)
  let e : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let β : ℝ × V → ℝ × V →L[ℝ] ℝ :=
    fun p ↦ (e (α₁ p.2 - α₀ p.2)).comp (ContinuousLinearMap.snd ℝ ℝ V)
  have hWp : IsOpen (univ ×ˢ W : Set (ℝ × V)) := isOpen_univ.prod hW
  have hsnd : MapsTo (Prod.snd : ℝ × V → V) (univ ×ˢ W) W := fun p hp ↦ hp.2
  have hB {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) :
      ContDiffOn ℝ r (fun p : ℝ × V ↦ (α p.2).symplectizationFormCLM (extDeriv α p.2))
        (univ ×ˢ W) :=
    ContDiffOn.symplectizationFormCLM ((hα.of_le hrle).comp contDiffOn_snd hsnd)
      ((contDiffOn_extDeriv hα hW le_rfl).comp contDiffOn_snd hsnd)
  have hβ : ContDiffOn ℝ r β (univ ×ˢ W) :=
    ((e.contDiff.comp_contDiffOn
      (((hα₁.of_le hrle).sub (hα₀.of_le hrle)).comp contDiffOn_snd hsnd)).clm_comp
        contDiffOn_const)
  have hL : (B₁ (0, x₀)).IsInvertible := hc.isInvertible_symplectizationFormCLM
  -- Solve the Moser contraction equation for the straight line between the symplectization forms.
  obtain ⟨T, U', X, hT, hU', hTI, hxU', hU'W, hX, hXeq⟩ := exists_contDiffOn_moserField hL hWp
    ⟨mem_univ _, hx₀⟩ (hB hα₀) (hB hα₁) (by simp only [B₁, heq, hdeq]) rfl hβ
  -- Restrict to the slice `{0} × V`: the conformal factor `σ` and the contact Moser field `Y`.
  let U : Set V := {y | ((0 : ℝ), y) ∈ U'}
  have hU : IsOpen U := hU'.preimage (continuous_const.prodMk continuous_id)
  have hxU : x₀ ∈ U := hxU'
  have hUW : U ⊆ W := fun y hy ↦ (hU'W hy).2
  have hj : MapsTo (fun p : ℝ × V ↦ (p.1, ((0 : ℝ), p.2))) (T ×ˢ U) (T ×ˢ U') :=
    fun p hp ↦ ⟨hp.1, hp.2⟩
  have hXj : ContDiffOn ℝ r (fun p : ℝ × V ↦ X (p.1, ((0 : ℝ), p.2))) (T ×ˢ U) :=
    hX.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)).contDiffOn hj
  -- The Moser contraction equation at `(t, (0, y))`, tested against `(s, u)`.
  have hXeq' (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) (s : ℝ) (u : V) :
      (1 - t) * ((X (t, (0, y))).1 * α₀ y ![u] - s * α₀ y ![(X (t, (0, y))).2] +
          extDeriv α₀ y ![(X (t, (0, y))).2, u]) +
        t * ((X (t, (0, y))).1 * α₁ y ![u] - s * α₁ y ![(X (t, (0, y))).2] +
          extDeriv α₁ y ![(X (t, (0, y))).2, u]) = -(α₁ y ![u] - α₀ y ![u]) := by
    have h := (hXeq (t, ((0 : ℝ), y)) ⟨ht, hy⟩ _).2 rfl (s, u)
    simpa [B₀, B₁, β, e, ← Matrix.vec_single_eq_const] using h
  refine ⟨T, U, fun t y ↦ (X (t, (0, y))).1, fun t y ↦ (X (t, (0, y))).2, hT, hU, hTI, hxU, hUW,
    contDiff_snd.comp_contDiffOn hXj, (contDiff_fst.comp_contDiffOn hXj).continuousOn,
    fun t ht y hy ↦ ?_, fun t ht y hy ↦ ?_, fun t ht y hy hαy ↦ ?_⟩
  · -- Testing against `(1, 0)` gives `αₜ(Yₜ) = 0`.
    have h := hXeq' t ht y hy 1 0
    rw [(α₀ y).map_coord_zero (m := ![(0 : V)]) 0 rfl,
      (α₁ y).map_coord_zero (m := ![(0 : V)]) 0 rfl,
      (extDeriv α₀ y).map_coord_zero (m := ![_, (0 : V)]) 1 rfl,
      (extDeriv α₁ y).map_coord_zero (m := ![_, (0 : V)]) 1 rfl] at h
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith
  · -- Testing against `(0, u)` gives `ι_{Yₜ} dαₜ = -(α₁ - α₀) - σₜ αₜ`.
    ext m
    have hm : m = ![m 0] := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    have h := hXeq' t ht y hy 0 (m 0)
    rw [hm]
    simp only [ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.neg_apply, smul_eq_mul]
    linear_combination h
  · -- Where `α₀ = α₁`, the right-hand side vanishes, and so does the solution.
    have h := (hXeq (t, ((0 : ℝ), y)) ⟨ht, hy⟩ 0).1 fun w ↦ by simp [β, hαy]
    dsimp only
    rw [← h, Prod.snd_zero]

/-- **The contact Moser lemma**, local form. Let `α₀`, `α₁` be `C^(r+1)` one-forms (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, which agree at `x₀ ∈ W` together with
their exterior derivatives, and let `α₁` be a contact form at `x₀`. Then some `C^r` diffeomorphism
`ψ` of the space pulls `α₁` back to a positive multiple `g • α₀` of `α₀` on a neighbourhood of
`x₀`. Moreover `ψ` fixes, near `x₀`, every point at which `α₀` and `α₁` agree; in particular
`ψ x₀ = x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r)
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα₀ : ContDiffOn ℝ (r + 1) α₀ W)
    (hα₁ : ContDiffOn ℝ (r + 1) α₁ W) (heq : α₁ x₀ = α₀ x₀)
    (hdeq : extDeriv α₁ x₀ = extDeriv α₀ x₀) (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α₁ x₀) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (g : V → ℝ), (∀ᶠ x in 𝓝 x₀, α₁ x = α₀ x → ψ x = x) ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧
        (α₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = g x • α₀ x := by
  obtain ⟨T, U, σ, Y, hT, hU, hTI, hxU, hUW, hY, hσ, hker, hYd, hY₀⟩ :=
    exists_contDiffOn_contactMoserField hW hx₀ hα₀ hα₁ heq hdeq hc
  have hr0 : (r : WithTop ℕ∞) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr : (1 : WithTop ℕ∞) ≤ r)).ne'
  have hdiff {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) (y : V) (hy : y ∈ U) :
      DifferentiableAt ℝ α y :=
    ((hα.differentiableOn (by simp)).differentiableAt (hW.mem_nhds (hUW hy)))
  -- The time-dependent flow of the contact Moser field, which fixes its zeros.
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn hr hT hU hTI hxU hY
      fun t ht ↦ hY₀ t ht x₀ hxU heq
  refine ⟨⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩,
    fun x ↦ Real.exp (∫ t in (0 : ℝ)..1, -σ t (ψ t x)), ?_, ?_⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy hαy
    exact hψfix y (fun t ht ↦ hY₀ t ht y hy hαy) 1
  filter_upwards [hev] with x hx
  refine ⟨Real.exp_pos _, ?_⟩
  -- The pullbacks `ψₜ^* αₜ` at `x` solve `∂ₜ Pₜ = -σₜ(ψₜ x) Pₜ` on `[0, 1]`.
  have hP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hasDerivAt_compContinuousLinearMap_fderiv_contactMoser
    (α₀ := α₀) (α₁ := α₁) (σ := σ) hU (hx t ht).1 (hdiff hα₀) (hdiff hα₁)
    ((hY.differentiableOn hr0).differentiableAt ((hT.prod hU).mem_nhds ⟨hTI ht, (hx t ht).1⟩)
      |>.comp (ψ t x) ((differentiableAt_const t).prodMk differentiableAt_id))
    (hker t (hTI ht)) (hYd t (hTI ht) _ (hx t ht).1) (hx t ht).2.1 (hx t ht).2.2
  have hcont : ContinuousOn (fun t ↦ -σ t (ψ t x)) (Icc 0 1) := by
    refine (hσ.comp (continuousOn_id.prodMk fun t ht ↦ ?_) fun t ht ↦
      ⟨hTI ht, (hx t ht).1⟩).neg
    exact (hx t ht).2.1.continuousAt.continuousWithinAt
  have h := eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := V [⋀^Fin 1]→L[ℝ] ℝ)
    (P := fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
      (fderiv ℝ (ψ s) x)) ordConnected_Icc hcont (fun t ht ↦ (hP t ht).hasDerivWithinAt)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simp only [hψ0, fderiv_id, sub_zero, one_smul, zero_smul, add_zero, zero_add, sub_self,
    id_eq] at h
  refine h.trans (congrArg _ ?_)
  ext v
  simp

/-- **Darboux's theorem for contact forms.** Let `α` be a `C^(r+1)` one-form (`r ≥ 1`) on an open
subset `W` of a finite-dimensional real normed space, which is a contact form at `x₀ ∈ W`. Then
some `C^r` diffeomorphism `ψ` of the space fixing `x₀` pulls `α` back, on a neighbourhood of
`x₀`, to a positive multiple `g • α_lin` of the osculating model form
`α_lin(x) = α(x₀) + ½ ι_{x - x₀} dα(x₀)`, whose exterior derivative is the constant form
`dα(x₀)`. Its second summand is the radial primitive `ContinuousLinearMap.liouvilleFormCLM` of
`dα(x₀)`, evaluated at `x - x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (g : V → ℝ), ψ x₀ = x₀ ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) =
        g x • (α x₀ + (ContinuousAlternatingMap.flatL ℝ V ℝ (extDeriv α x₀)).liouvilleFormCLM
          (x - x₀)) := by
  set L := (ContinuousAlternatingMap.flatL ℝ V ℝ (extDeriv α x₀)).liouvilleFormCLM
  have hlin : ContDiff ℝ (r + 1) (fun y ↦ α x₀ + L (y - x₀)) :=
    contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))
  -- The model is a constant plus the radial primitive `L` of the constant form `dα(x₀)`.
  have hdeq : extDeriv (fun y ↦ α x₀ + L (y - x₀)) x₀ = extDeriv α x₀ := by
    have e : (fun y ↦ α x₀ + L (y - x₀)) = (fun _ : V ↦ α x₀ - L x₀) + ⇑L := by
      ext y : 1
      simp only [map_sub, Pi.add_apply]
      abel
    rw [e, extDeriv_add (differentiableAt_const _) L.differentiableAt,
      ContinuousAlternatingMap.extDeriv_const, Pi.zero_apply, zero_add]
    ext m
    rw [ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero
      (fun v w ↦ by simpa [ContinuousAlternatingMap.flatL_apply_apply] using
        (extDeriv α x₀).map_swap ![w, v] (i := 0) (j := 1) Fin.zero_ne_one),
      ContinuousAlternatingMap.flatL_apply_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨ψ, g, hfix, hψ⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq hr hW hx₀
      hlin.contDiffOn hα (by simp) hdeq.symm hc
  exact ⟨ψ, g, hfix.self_of_nhds (by simp), hψ⟩

/-! ### Darboux charts to the standard contact form -/

open _root_.ContinuousAlternatingMap in
/-- **The contact Darboux theorem**, local form. Let `α` be a `C^(r+1)` one-form (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, which is a contact form at `x₀ ∈ W`:
`α(x₀) ≠ 0` and `dα(x₀)` is nondegenerate on `ker α(x₀)`. Then there are `n` and a `C^r`
diffeomorphism `Φ` of the space onto `ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which, near `x₀`, pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to a positive multiple `g α` of `α`. So `Φ` is a chart
near `x₀` carrying the contact structure `ker α` to the standard one and preserving
coorientations. -/
theorem exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) :
    ∃ (n : ℕ) (Φ : V ≃ₘ^r⟮𝓘(ℝ, V),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (g : V → ℝ), Φ x₀ = 0 ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ ∀ v : V,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ x) ![fderiv ℝ Φ x v] =
          g x * α x ![v] := by
  obtain ⟨n, e, hae, hωe⟩ := exists_continuousLinearEquiv_stdContact hc.ne_zero
    fun v hv hvw ↦ hc.nondegenerate v (RoughForm.mem_ker.2 hv) fun (w : V) hw ↦
      (congrArg (fun A ↦ A ![v, w]) (mextDeriv_eq_extDeriv (E := V) (F := ℝ) (k := 1) α x₀)).trans
        (hvw w (RoughForm.mem_ker.1 hw))
  set P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ
  set σ : P → P [⋀^Fin 1]→L[ℝ] ℝ := (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ :=
    isSmoothForm_modelSpace_iff.1 (innerProductContactForm (EuclideanSpace ℝ (Fin n))).isSmoothForm
  -- The standard form and its exterior derivative, read on the model space itself.
  have hσapp (x v : P) : σ x ![v] = v.2.2 - inner ℝ x.2.1 v.1 :=
    innerProductContactForm_apply _ x v
  have hdσ (u w : P) : extDeriv σ 0 ![u, w] = ∑ i, (u.1 i * w.2.1 i - u.2.1 i * w.1 i) := by
    have h := mextDeriv_innerProductContactForm_euclideanSpace_apply (0 : P) u w
    rw [mextDeriv_eq_extDeriv] at h
    exact h
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- The linear coordinates centred at `x₀`, and the pullback `α₀` of the standard form.
  set f : V → P := fun x ↦ e (x - x₀) with hf_def
  have hfd (x : V) : HasFDerivAt f (e : V →L[ℝ] P) x := by
    simpa [hf_def, Function.comp_def] using
      (e : V →L[ℝ] P).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
  have htop (k : ℕ∞) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hfs {k : WithTop ℕ∞} : ContDiff ℝ k f := e.contDiff.comp (contDiff_id.sub contDiff_const)
  set α₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ :=
    fun x ↦ (σ (f x)).compContinuousLinearMap (fderiv ℝ f x) with hα₀_def
  have hα₀e : α₀ = fun x ↦ compContinuousLinearMapCLM (e : V →L[ℝ] P) (σ (f x)) := by
    funext x
    simp only [hα₀_def, (hfd x).fderiv, compContinuousLinearMapCLM_apply]
  have hle : (r : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast htop (r + 1)
  have hα₀s : ContDiffOn ℝ (r + 1) α₀ W := by
    rw [hα₀e]
    exact ((compContinuousLinearMapCLM (e : V →L[ℝ] P)).contDiff.comp
      (hσ.comp hfs)).contDiffOn.of_le hle
  have hfx₀ : f x₀ = 0 := by simp [hf_def]
  -- `α₀` has the same value and exterior derivative as `α` at `x₀`.
  have hm1 (m : Fin 1 → V) : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  have hm2 (m : Fin 2 → V) : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  have hvec1 (v : V) : ⇑(e : V →L[ℝ] P) ∘ ![v] = ![e v] := by
    funext i
    fin_cases i
    rfl
  have hvec2 (v w : V) : ⇑(e : V →L[ℝ] P) ∘ ![v, w] = ![e v, e w] := by
    funext i
    fin_cases i <;> rfl
  have hα₀x₀ : α₀ x₀ = α x₀ := by
    ext m
    simp only [hα₀_def]
    rw [hm1 m, compContinuousLinearMap_apply, (hfd x₀).fderiv, hfx₀, hae, hvec1, hσapp]
    simp
  have hdα₀x₀ : extDeriv α₀ x₀ = extDeriv α x₀ := by
    rw [hα₀_def, extDeriv_pullback (hσ.differentiable (by simp)).differentiableAt
      (hfs.contDiffAt : ContDiffAt ℝ 2 f x₀) (by simp)]
    ext m
    rw [hm2 m, compContinuousLinearMap_apply, (hfd x₀).fderiv, hvec2, hfx₀, hωe, hdσ]
  -- The contact Moser lemma deforms `α₀` into a positive multiple of `α`.
  obtain ⟨ψ, g, hfix, hev⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq hr hW hx₀
      hα₀s hα hα₀x₀.symm hdα₀x₀.symm hc
  have hψx₀ : ψ x₀ = x₀ := hfix.self_of_nhds hα₀x₀.symm
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, P)⟯ P, ⇑Φ = f ∘ ψ.symm :=
    ⟨ψ.symm.trans ((Diffeomorph.smulAdd r (1 : ℝ) (-x₀) one_ne_zero).trans
      (e.toContDiffDiffeomorph r)), by funext y; simp [hf_def, sub_eq_add_neg]⟩
  have hψsymm : ψ.symm x₀ = x₀ := ψ.symm_apply_eq.2 hψx₀.symm
  refine ⟨n, Φ, fun y ↦ (g (ψ.symm y))⁻¹, by rw [hΦ, Function.comp_apply, hψsymm, hfx₀], ?_⟩
  have hev' : ∀ᶠ y in 𝓝 x₀, 0 < g (ψ.symm y) ∧
      (α (ψ (ψ.symm y))).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) =
        g (ψ.symm y) • α₀ (ψ.symm y) := by
    have hc : Tendsto ψ.symm (𝓝 x₀) (𝓝 x₀) := by
      simpa [hψsymm] using ψ.symm.continuous.tendsto x₀
    exact hc.eventually hev
  filter_upwards [hev'] with y ⟨hg, hy⟩
  refine ⟨inv_pos.2 hg, fun v ↦ ?_⟩
  rw [ψ.apply_symm_apply] at hy
  -- Unwind `Φ^* σ = (ψ⁻¹)^* α₀ = (g ∘ ψ⁻¹)⁻¹ α`, evaluated on `v`.
  have hΦd : fderiv ℝ Φ y = (e : V →L[ℝ] P) ∘L fderiv ℝ ψ.symm y := by
    rw [hΦ, fderiv_comp y (hfd _).differentiableAt
      ((ψ.symm.differentiable hr0) y), (hfd _).fderiv]
  have hcomp (F : V → V) (z : V) : F ∘ ![z] = ![F z] := by
    funext i
    fin_cases i
    rfl
  have h := congrArg (fun β ↦ β ![fderiv ℝ ψ.symm y v]) hy
  simp only [hα₀_def, compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply, hcomp,
    (hfd _).fderiv, hvec1, ψ.fderiv_apply_fderiv_symm_apply hr0, smul_eq_mul] at h
  have key : σ (Φ y) ![fderiv ℝ Φ y v] = (g (ψ.symm y))⁻¹ * α y ![v] := by
    rw [hΦd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hΦ,
      Function.comp_apply, h, ← mul_assoc,
      inv_mul_cancel₀ hg.ne', one_mul]
  exact key

end TauCeti
