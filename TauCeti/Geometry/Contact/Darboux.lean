/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Analysis.Normed.Module.Alternating.ContactFlat
import TauCeti.Geometry.Contact.LocalMoser
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm

/-!
# The contact Darboux theorem

Let `α` be a one-form on an open subset `W` of a finite-dimensional real normed space `V`, of
class `C^(r+1)` with `r ≥ 1`, which is a contact form at `x₀ ∈ W`: `α(x₀) ≠ 0` and `dα(x₀)` is
nondegenerate on the hyperplane `ker α(x₀)`. The **contact Darboux theorem**
(`TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`) gives a
`C^r` diffeomorphism `Φ : V ≃ ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to `g α` near `x₀`, for a positive
function `g`. So near `x₀` the contact structure `ker α` is the standard one in the coordinates
`Φ`, with matching coorientations. This is the Darboux theorem for the contact structure; the
sharper form-level statement, in which the factor `g` is removed by a further change of
coordinates, is not proved here.

The proof is the contact version of Moser's argument. Take affine coordinates centred at `x₀` in
which `α(x₀)` and `dα(x₀)` are the standard `dz` and `Σᵢ dqᵢ ∧ dpᵢ`
(`Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`), and let `α₀` be the standard form
pulled back along them. Then `α₀` and `α` have equal values and exterior derivatives at `x₀`, and
the local **contact Moser lemma**
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`) gives a
diffeomorphism `ψ` fixing `x₀` with `ψ^* α = g α₀` near `x₀` and `g > 0`. The chart is the affine
coordinates composed with `ψ⁻¹`.

Forms are Mathlib's continuous alternating maps, with Mathlib's exterior derivative `extDeriv`,
and the pullback of `α` along `ψ` at `x` is `(α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`.
Nothing is assumed away from a neighbourhood of `x₀`.

## Main results

* `TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`: the contact
  Darboux theorem.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5 (Darboux's theorem).
-/

public section

open Set Filter Topology ContinuousAlternatingMap
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The contact Darboux theorem -/

section Darboux

variable [FiniteDimensional ℝ V]

/-- A covector `a` which is contact for an alternating form `ω` is the standard covector `dz`, and
`ω` the standard form `Σᵢ dqᵢ ∧ dpᵢ`, in suitable linear coordinates `V ≃ ℝⁿ × ℝⁿ × ℝ`. -/
private theorem exists_continuousLinearEquiv_stdContact {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ),
      (∀ v, a ![v] = (e v).2.2) ∧
        ∀ v w, ω ![v, w] = ∑ i, ((e v).1 i * (e w).2.1 i - (e v).2.1 i * (e w).1 i) := by
  let B : LinearMap.BilinForm ℝ V := (flatL ℝ V ℝ ω).toLinearMap₁₂
  have hB (v w : V) : B v w = ω ![v, w] := flatL_apply_apply ω v w
  have hBalt : B.IsAlt := isAlt_toLinearMap₁₂_flatL ω
  have hcon : Module.Dual.IsContact (toDual a : V →ₗ[ℝ] ℝ) B := isContact_toDual hne hnd
  obtain ⟨n, e₁, ha₁, hB₁⟩ := hcon.exists_linearEquiv_eq_stdContact hBalt
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
    e₁.toContinuousLinearEquiv.trans (L.prodCongr (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨n, e, fun v ↦ ?_, fun v w ↦ ?_⟩
  · have h := LinearMap.congr_fun ha₁ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, stdContactCovector_apply,
      ContinuousLinearMap.coe_coe] at h
    rw [← toDual_apply, ← h]
    simp [e]
  · rw [← hB, ← LinearMap.congr_fun₂ hB₁ v w]
    simp [e, L, stdContactBilinForm_apply, dotProduct, Finset.sum_sub_distrib]

/-- **The contact Darboux theorem**, local form. Let `α` be a `C^(r+1)` one-form (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, which is a contact form at `x₀ ∈ W`:
`α(x₀) ≠ 0` and `dα(x₀)` is nondegenerate on `ker α(x₀)`. Then there are `n` and a `C^r`
diffeomorphism `Φ` of the space onto `ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which, near `x₀`, pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to a positive multiple `g α` of `α`. So `Φ` is a chart
near `x₀` carrying the contact structure `ker α` to the standard one and preserving
coorientations. -/
theorem exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hne : α x₀ ≠ 0)
    (hnd : ∀ v, α x₀ ![v] = 0 → (∀ w, α x₀ ![w] = 0 → extDeriv α x₀ ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (Φ : V ≃ₘ^r⟮𝓘(ℝ, V),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (g : V → ℝ), Φ x₀ = 0 ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ ∀ v : V,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ x) ![fderiv ℝ Φ x v] =
          g x * α x ![v] := by
  obtain ⟨n, e, hae, hωe⟩ := exists_continuousLinearEquiv_stdContact hne hnd
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
  have hne₀ : α₀ x₀ ≠ 0 := hα₀x₀ ▸ hne
  have hnd₀ : ∀ v, α₀ x₀ ![v] = 0 → (∀ w, α₀ x₀ ![w] = 0 → extDeriv α₀ x₀ ![v, w] = 0) →
      v = 0 := by
    rw [hα₀x₀, hdα₀x₀]
    exact hnd
  -- The contact Moser lemma deforms `α₀` into a positive multiple of `α`.
  obtain ⟨ψ, g, hψx₀, hev⟩ := exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    hr hW hx₀ hα₀s hα hα₀x₀.symm hdα₀x₀.symm hne₀ hnd₀
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

end Darboux

end TauCeti
