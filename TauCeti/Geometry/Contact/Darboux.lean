/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Topology.Algebra.Module.BilinearForm

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

whose exterior derivative is the constant form `dα(x₀)`. Hence **Darboux's theorem**
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
the symplectization form of `αₜ` (`Module.Dual.symplectizationForm`). It is nondegenerate exactly
where `αₜ` is contact (`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`), so the
contraction equation is solved by `TauCeti.exists_contDiffOn_moserField`. The field `Yₜ` vanishes
wherever `α₀` and `α₁` agree, in particular at `x₀`, so its time-dependent flow `ψₜ` exists near
`x₀` up to time one (`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`). Since
`αₜ(Yₜ) = 0`, Cartan's formula gives `∂ₜ αₜ + L_{Yₜ} αₜ = -σₜ αₜ`, so the pullbacks
`Pₜ = ψₜ^* αₜ` at a point `x` satisfy the linear equation `∂ₜ Pₜ = -σₜ(ψₜ x) Pₜ`. Integrating,
`ψ₁^* α₁ = exp (-∫₀¹ σₜ(ψₜ x) dt) • α₀` at `x`.

## Main results

* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq`:
  the contact Moser lemma.
* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`: Darboux's
  theorem, conformal to the osculating model form.

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

/-! ### The symplectization form of a covector and a two-form -/

section Symplectization

variable [FiniteDimensional ℝ V]

/-- The symplectization form `((s, v), (s', w)) ↦ s a(w) - s' a(v) + b(v, w)` on `ℝ × V` of a
covector `a` and a two-form `b` on `V` (`Module.Dual.symplectizationForm`), as a continuous
bilinear map. -/
private noncomputable def symplectizationCLM (a : V [⋀^Fin 1]→L[ℝ] ℝ)
    (b : V [⋀^Fin 2]→L[ℝ] ℝ) : ℝ × V →L[ℝ] ℝ × V →L[ℝ] ℝ :=
  (Module.Dual.symplectizationForm
    ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm a : V →L[ℝ] ℝ).toLinearMap
    (ContinuousAlternatingMap.flatL ℝ V ℝ b).toBilinForm).toContinuousBilinearMap

private theorem symplectizationCLM_apply (a : V [⋀^Fin 1]→L[ℝ] ℝ) (b : V [⋀^Fin 2]→L[ℝ] ℝ)
    (p q : ℝ × V) :
    symplectizationCLM a b p q = p.1 * a ![q.2] - q.1 * a ![p.2] + b ![p.2, q.2] := by
  simp [symplectizationCLM, ← Matrix.vec_single_eq_const]

/-- The symplectization form depends smoothly on the covector and the two-form. -/
private theorem ContDiffOn.symplectizationCLM {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a : X → V [⋀^Fin 1]→L[ℝ] ℝ} {b : X → V [⋀^Fin 2]→L[ℝ] ℝ} {s : Set X}
    {n : WithTop ℕ∞} (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) :
    ContDiffOn ℝ n (fun x ↦ TauCeti.symplectizationCLM (a x) (b x)) s := by
  refine contDiffOn_clm_apply.2 fun p ↦ contDiffOn_clm_apply.2 fun q ↦ ?_
  simp only [symplectizationCLM_apply]
  have hev {k : ℕ} {f : X → V [⋀^Fin k]→L[ℝ] ℝ} (hf : ContDiffOn ℝ n f s) (m : Fin k → V) :
      ContDiffOn ℝ n (fun x ↦ f x m) s :=
    (ContinuousAlternatingMap.apply ℝ V ℝ m).contDiff.comp_contDiffOn hf
  exact ((contDiffOn_const.mul (hev ha _)).sub (contDiffOn_const.mul (hev ha _))).add (hev hb _)

/-- At a point where a one-form is a contact form, its symplectization form is invertible, by
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`. -/
private theorem IsContactFormAt.isInvertible_symplectizationCLM
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {x : V} (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x) :
    (symplectizationCLM (α x) (extDeriv α x)).IsInvertible := by
  set B := (ContinuousAlternatingMap.flatL ℝ V ℝ (extDeriv α x)).toBilinForm
  have hB : B.IsAlt := fun v ↦ by
    simpa [B] using (extDeriv α x).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl
      Fin.zero_ne_one
  have hcontact : Module.Dual.IsContact
      ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (α x) : V →L[ℝ] ℝ).toLinearMap
      B := by
    rw [Module.Dual.isContact_iff_of_isRefl hB.isRefl]
    simp only [ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, ← Matrix.vec_single_eq_const, B,
      ContinuousLinearMap.toBilinForm_apply, ContinuousAlternatingMap.flatL_apply_apply]
    refine ⟨fun h ↦ hc.ne_zero (ContinuousAlternatingMap.ext fun m ↦ ?_),
      fun v hv hvw ↦ hc.nondegenerate v (RoughForm.mem_ker.2 hv) fun (w : V) hw ↦ ?_⟩
    · have hm : m = ![m 0] := by
        funext i
        rw [Subsingleton.elim i 0]
        rfl
      have h0 : α x ![m 0] = 0 := by
        simpa [← Matrix.vec_single_eq_const] using congrArg (fun f : V →ₗ[ℝ] ℝ ↦ f (m 0)) h
      rw [hm]
      exact h0
    · exact (congrArg (fun A ↦ A ![v, w])
        (mextDeriv_eq_extDeriv (E := V) (F := ℝ) (k := 1) α x)).trans
          (hvw w (RoughForm.mem_ker.1 hw))
  exact isInvertible_toContinuousBilinearMap_iff_separatingLeft.2
    (Module.Dual.isContact_iff_nondegenerate_symplectizationForm.1 hcontact).1

end Symplectization

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
    have h₀' : DifferentiableAt ℝ (fun p : ℝ × V ↦ α₀ p.2) (t, z) :=
      h₀.comp (t, z) differentiableAt_snd
    have h₁' : DifferentiableAt ℝ (fun p : ℝ × V ↦ α₁ p.2) (t, z) :=
      h₁.comp (t, z) differentiableAt_snd
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
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r)
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
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hrle : (r : WithTop ℕ∞) ≤ r + 1 := le_self_add
  -- The forms are `C^r` on `W`, and so are their exterior derivatives.
  have hd {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) :
      ContDiffOn ℝ r (extDeriv α) W := fun y hy ↦
    (contDiffAt_extDeriv ((hα y hy).contDiffAt (hW.mem_nhds hy)) le_rfl).contDiffWithinAt
  -- The symplectization forms of `α₀` and `α₁`, on `ℝ × V`, and the right-hand side `α₁ - α₀`.
  let B₀ : ℝ × V → ℝ × V →L[ℝ] ℝ × V →L[ℝ] ℝ :=
    fun p ↦ symplectizationCLM (α₀ p.2) (extDeriv α₀ p.2)
  let B₁ : ℝ × V → ℝ × V →L[ℝ] ℝ × V →L[ℝ] ℝ :=
    fun p ↦ symplectizationCLM (α₁ p.2) (extDeriv α₁ p.2)
  let e : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let β : ℝ × V → ℝ × V →L[ℝ] ℝ :=
    fun p ↦ (e (α₁ p.2 - α₀ p.2)).comp (ContinuousLinearMap.snd ℝ ℝ V)
  have hWp : IsOpen (univ ×ˢ W : Set (ℝ × V)) := isOpen_univ.prod hW
  have hsnd : MapsTo (Prod.snd : ℝ × V → V) (univ ×ˢ W) W := fun p hp ↦ hp.2
  have hB {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ (r + 1) α W) :
      ContDiffOn ℝ r (fun p : ℝ × V ↦ symplectizationCLM (α p.2) (extDeriv α p.2))
        (univ ×ˢ W) :=
    ContDiffOn.symplectizationCLM ((hα.of_le hrle).comp contDiffOn_snd hsnd)
      ((hd hα).comp contDiffOn_snd hsnd)
  have hβ : ContDiffOn ℝ r β (univ ×ˢ W) :=
    ((e.contDiff.comp_contDiffOn
      (((hα₁.of_le hrle).sub (hα₀.of_le hrle)).comp contDiffOn_snd hsnd)).clm_comp
        contDiffOn_const)
  have hL : (B₁ (0, x₀)).IsInvertible := hc.isInvertible_symplectizationCLM
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
    simpa [B₀, B₁, β, e, symplectizationCLM_apply, ← Matrix.vec_single_eq_const] using h
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
    exists_contDiffOn_contactMoserField hr hW hx₀ hα₀ hα₁ heq hdeq hc
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
  have h := eq_exp_integral_smul_of_hasDerivWithinAt (E := V [⋀^Fin 1]→L[ℝ] ℝ)
    (f := fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
      (fderiv ℝ (ψ s) x)) zero_le_one hcont fun t ht ↦ (hP t ht).hasDerivWithinAt
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
`dα(x₀)`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (g : V → ℝ), ψ x₀ = x₀ ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) =
        g x • (α x₀ + (2⁻¹ : ℝ) • (extDeriv α x₀).curryLeft (x - x₀)) := by
  have hlin : ContDiff ℝ (r + 1)
      (fun y ↦ α x₀ + (2⁻¹ : ℝ) • (extDeriv α x₀).curryLeft (y - x₀)) :=
    contDiff_const.add (((extDeriv α x₀).curryLeft.contDiff.comp
      (contDiff_id.sub contDiff_const)).const_smul _)
  obtain ⟨ψ, g, hfix, hψ⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul_of_extDeriv_eq hr hW hx₀
      hlin.contDiffOn hα (by simp)
      (ContinuousAlternatingMap.extDeriv_const_add_smul_curryLeft_sub _ _ _ _).symm hc
  exact ⟨ψ, g, hfix.self_of_nhds (by simp), hψ⟩

end TauCeti
