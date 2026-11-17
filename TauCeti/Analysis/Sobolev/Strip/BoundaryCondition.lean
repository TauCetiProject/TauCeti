/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Linear boundary conditions on the strip

Let `Λ₀` and `Λ₁` be subspaces of a real normed space `V`. The maps `ξ : ℝ × ℝ → V` on the strip
`ℝ × [0, 1]` with `ξ (s, 0) ∈ Λ₀` and `ξ (s, 1) ∈ Λ₁` for all `s` form the submodule
`TauCeti.StripSobolev.boundaryCondition Λ₀ Λ₁`, and its `W^{1,2}` completion
`H1 (boundaryCondition Λ₀ Λ₁)` (`TauCeti.StripSobolev.H1`) is the Sobolev space
`W^{1,2}_Λ(ℝ × [0, 1], V)` of maps with these boundary conditions. For `V = ℂⁿ` and totally real
subspaces `Λ₀`, `Λ₁` this is the domain of the linearized operator `∂s + J ∂t + S` along a
holomorphic strip with Lagrangian boundary conditions, the setting of Lagrangian Floer theory.
The boundary conditions are invariant under translation along the strip
(`TauCeti.StripSobolev.comp_add_mem_boundaryCondition`), so `TauCeti.StripSobolev.translateₗᵢ`
acts on this space by linear isometries.

The boundary conditions survive the completion, in the following weak form. For a `C¹` map
`ψ : ℝ × ℝ → V →L[ℝ] ℝ`, Green's formula in the `t` direction
(`TauCeti.StripSobolev.integral_apply_fderiv_add_eq_integral_sub`) reads

`∫_strip ψ (∂t ξ) + (∂t ψ) ξ = ∫_ℝ ψ(s, 1) ξ(s, 1) - ψ(s, 0) ξ(s, 0) ds`

for every test map `ξ`. If `ψ` has compact support and `ψ(s, i)` vanishes on `Λᵢ`, the right side
vanishes on the maps satisfying the boundary conditions, and the left side is a continuous linear
functional of the `L²` jet `(ξ, ∂s ξ, ∂t ξ)`. So the left side vanishes on all of
`H1 (boundaryCondition Λ₀ Λ₁)` (`TauCeti.StripSobolev.integral_apply_add_eq_zero_of_mem_H1`).
Conversely, for finite-dimensional `V`, these identities detect the boundary values: a test map
whose jet lies in `H1 (boundaryCondition Λ₀ Λ₁)` satisfies the boundary conditions
(`TauCeti.StripSobolev.jetₗ_mem_H1_boundaryCondition_iff`). Testing against
`ψ(s, t) = β(s) γ(t) ℓ` with `γ` a bump at one edge and `ℓ` a functional vanishing on the
corresponding `Λᵢ` shows that `ℓ (ξ (s, i))` integrates to zero against every test function `β`,
hence vanishes; and the functionals vanishing on `Λᵢ` cut out `Λᵢ`.

## Main definitions

* `TauCeti.StripSobolev.boundaryCondition Λ₀ Λ₁`: the maps with `ξ (s, 0) ∈ Λ₀` and
  `ξ (s, 1) ∈ Λ₁`.

## Main results

* `TauCeti.StripSobolev.integral_apply_fderiv_add_eq_integral_sub`: Green's formula in `t`.
* `TauCeti.StripSobolev.integral_apply_add_eq_zero_of_mem_H1`: the weak boundary conditions on
  `H1 (boundaryCondition Λ₀ Λ₁)`.
* `TauCeti.StripSobolev.jetₗ_mem_H1_boundaryCondition_iff`: a test map lies in the completion
  exactly when it satisfies the boundary conditions.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  and Section 3.1, on Sobolev spaces with totally real boundary conditions.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section BoundaryCondition

variable (Λ₀ Λ₁ : Submodule ℝ V)

/-- The maps `ξ : ℝ × ℝ → V` on the strip `ℝ × [0, 1]` satisfying the linear boundary conditions
`ξ (s, 0) ∈ Λ₀` and `ξ (s, 1) ∈ Λ₁` for all `s`. -/
def boundaryCondition : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ∀ s, ξ (s, 0) ∈ Λ₀ ∧ ξ (s, 1) ∈ Λ₁}
  zero_mem' _ := ⟨Λ₀.zero_mem, Λ₁.zero_mem⟩
  add_mem' hξ hη s := ⟨Λ₀.add_mem (hξ s).1 (hη s).1, Λ₁.add_mem (hξ s).2 (hη s).2⟩
  smul_mem' c _ hξ s := ⟨Λ₀.smul_mem c (hξ s).1, Λ₁.smul_mem c (hξ s).2⟩

variable {Λ₀ Λ₁}

/-- Membership in `boundaryCondition Λ₀ Λ₁`. -/
theorem mem_boundaryCondition_iff {ξ : ℝ × ℝ → V} :
    ξ ∈ boundaryCondition Λ₀ Λ₁ ↔ ∀ s, ξ (s, 0) ∈ Λ₀ ∧ ξ (s, 1) ∈ Λ₁ :=
  Iff.rfl

/-- Weaker boundary conditions allow more maps. -/
theorem boundaryCondition_mono {Λ₀' Λ₁' : Submodule ℝ V} (h₀ : Λ₀ ≤ Λ₀') (h₁ : Λ₁ ≤ Λ₁') :
    boundaryCondition Λ₀ Λ₁ ≤ boundaryCondition Λ₀' Λ₁' :=
  fun _ hξ s ↦ ⟨h₀ (hξ s).1, h₁ (hξ s).2⟩

/-- The trivial boundary conditions allow every map. -/
@[simp]
theorem boundaryCondition_top : boundaryCondition (⊤ : Submodule ℝ V) ⊤ = ⊤ :=
  eq_top_iff.2 fun _ _ _ ↦ ⟨Submodule.mem_top, Submodule.mem_top⟩

/-- The boundary conditions are invariant under translation along the strip. -/
theorem comp_add_mem_boundaryCondition {ξ : ℝ × ℝ → V} (hξ : ξ ∈ boundaryCondition Λ₀ Λ₁)
    (a : ℝ) : (fun z ↦ ξ (z + (a, 0))) ∈ boundaryCondition Λ₀ Λ₁ := fun s ↦ by
  simpa using hξ (s + a)

end BoundaryCondition

/-! ### Green's formula and the weak boundary conditions -/

section Green

variable {ξ : ℝ × ℝ → V} {ψ : ℝ × ℝ → V →L[ℝ] ℝ}

/-- **Green's formula in the `t` direction on the strip.** For a test map `ξ` and a `C¹` map
`ψ` into the dual of `V`, the integral of `∂t (ψ ξ) = ψ (∂t ξ) + (∂t ψ) ξ` over the strip
`ℝ × [0, 1]` is the integral of the difference of the boundary values of `ψ ξ` on its two
edges. -/
theorem integral_apply_fderiv_add_eq_integral_sub (hψ : ContDiff ℝ 1 ψ) (hξ : ξ ∈ testMap V) :
    ∫ z, (ψ z (fderiv ℝ ξ z (0, 1)) + fderiv ℝ ψ z (0, 1) (ξ z)) ∂stripMeasure =
      ∫ s, (ψ (s, 1) (ξ (s, 1)) - ψ (s, 0) (ξ (s, 0))) := by
  obtain ⟨hξ2, R, hR⟩ := mem_testMap_iff.1 hξ
  have hξ1 : ContDiff ℝ 1 ξ := hξ2.of_le (by norm_num)
  have hF : ∀ z, jet ξ z = 0 → ψ z (fderiv ℝ ξ z (0, 1)) + fderiv ℝ ψ z (0, 1) (ξ z) = 0 :=
    fun z h ↦ by
      simp only [jet_apply, Prod.mk_eq_zero] at h
      simp [h.1, h.2.2]
  have hc : Continuous fun z ↦ ψ z (fderiv ℝ ξ z (0, 1)) + fderiv ℝ ψ z (0, 1) (ξ z) :=
    (hψ.continuous.clm_apply ((hξ1.continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).add
      (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply hξ1.continuous)
  rw [integral_strip_eq_setIntegral_of_jet_eq_zero hR hF,
    setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd (Φ := fun z ↦ ψ z (ξ z)) hc
      (fun s t ↦ ?_) zero_le_one]
  · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_
    have hs' : R ≤ |s| := by
      rw [mem_Icc, ← abs_le, not_le] at hs
      exact hs.le
    simp [hR s 1 hs', hR s 0 hs']
  · have hl : HasDerivAt (fun t : ℝ ↦ ((s, t) : ℝ × ℝ)) (0, 1) t :=
      (hasDerivAt_const t s).prodMk (hasDerivAt_id' t)
    have hψd := ((hψ.differentiable one_ne_zero) (s, t)).hasFDerivAt.comp_hasDerivAt t hl
    have hξd := ((hξ1.differentiable one_ne_zero) (s, t)).hasFDerivAt.comp_hasDerivAt t hl
    simpa [Function.comp_def, add_comm] using hψd.clm_apply hξd

/-- The coefficients `ψ` and `∂t ψ` of Green's formula lie in `L²` when `ψ` is `C¹` with compact
support. -/
private theorem memLp_and_memLp_fderiv_apply (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) :
    MemLp ψ 2 stripMeasure ∧ MemLp (fun z ↦ fderiv ℝ ψ z (0, 1)) 2 stripMeasure :=
  ⟨hψ.continuous.memLp_of_hasCompactSupport hψs,
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψs.fderiv_apply (𝕜 := ℝ) (0, 1))⟩

/-- Green's formula read on the `L²` jet of a test map: for a `C¹` map `ψ` into the dual of `V`
with compact support, `∫ ψ (x_t) + ∫ (∂t ψ) (x₁)` at the jet `x` of a test map `ξ` is the
integral of the difference of the boundary values of `ψ ξ`. -/
private theorem integral_jetₗ_add_eq_integral_sub (hψ : ContDiff ℝ 1 ψ)
    (hψs : HasCompactSupport ψ) (ξ : testMap V) :
    ∫ z, ψ z (jetₗ V ξ z).2.2 ∂stripMeasure +
        ∫ z, fderiv ℝ ψ z (0, 1) (jetₗ V ξ z).1 ∂stripMeasure =
      ∫ s, (ψ (s, 1) ((ξ : ℝ × ℝ → V) (s, 1)) - ψ (s, 0) ((ξ : ℝ × ℝ → V) (s, 0))) := by
  obtain ⟨h₁, h₂⟩ := memLp_and_memLp_fderiv_apply hψ hψs
  have h := integral_jetₗ_add_eq_integral (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ))
    ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))) h₁ h₂ ξ
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', jet_apply] at h
  rw [h, integral_apply_fderiv_add_eq_integral_sub hψ ξ.2]

variable {Λ₀ Λ₁ : Submodule ℝ V}

/-- **The weak boundary conditions.** Let `ψ : ℝ × ℝ → V →L[ℝ] ℝ` be `C¹` with compact support,
with `ψ (s, 0)` vanishing on `Λ₀` and `ψ (s, 1)` vanishing on `Λ₁`. Then every `L²` jet
`x = (x₁, x_s, x_t)` in the completion `H1 (boundaryCondition Λ₀ Λ₁)` satisfies
`∫ ψ (x_t) + ∫ (∂t ψ) (x₁) = 0` over the strip: the boundary terms of Green's formula vanish. -/
theorem integral_apply_add_eq_zero_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure}
    (hx : x ∈ H1 (boundaryCondition Λ₀ Λ₁)) (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ)
    (hψ₀ : ∀ s, ∀ v ∈ Λ₀, ψ (s, 0) v = 0) (hψ₁ : ∀ s, ∀ v ∈ Λ₁, ψ (s, 1) v = 0) :
    ∫ z, ψ z (x z).2.2 ∂stripMeasure + ∫ z, fderiv ℝ ψ z (0, 1) (x z).1 ∂stripMeasure = 0 := by
  obtain ⟨h₁, h₂⟩ := memLp_and_memLp_fderiv_apply hψ hψs
  have h := integral_add_eq_zero_of_mem_H1 (S := boundaryCondition Λ₀ Λ₁)
    (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ))
    ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))) h₁ h₂
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', jet_apply] at h
  refine h (fun ξ hbc ↦ ?_) hx
  -- The boundary terms of Green's formula vanish on the maps satisfying the boundary conditions.
  rw [integral_apply_fderiv_add_eq_integral_sub hψ ξ.2]
  have h0 : ∀ s, ψ (s, 1) ((ξ : ℝ × ℝ → V) (s, 1)) - ψ (s, 0) ((ξ : ℝ × ℝ → V) (s, 0)) = 0 :=
    fun s ↦ by rw [hψ₁ s _ (hbc s).2, hψ₀ s _ (hbc s).1, sub_zero]
  simp [h0]

/-- Testing the weak boundary conditions against `ψ(s, t) = β(s) γ(t) ℓ`: for a test map whose
jet lies in `H1 (boundaryCondition Λ₀ Λ₁)`, a smooth compactly supported `γ` and a functional `ℓ`
such that `γ(i) ℓ` vanishes on `Λᵢ`, the function `s ↦ γ(1) ℓ (ξ (s, 1)) - γ(0) ℓ (ξ (s, 0))`
vanishes. -/
private theorem sub_eq_zero_of_jetₗ_mem_H1 {ξ : testMap V}
    (h : jetₗ V ξ ∈ H1 (boundaryCondition Λ₀ Λ₁)) (ℓ : V →L[ℝ] ℝ) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hγs : HasCompactSupport γ) (h₀ : ∀ v ∈ Λ₀, γ 0 * ℓ v = 0)
    (h₁ : ∀ v ∈ Λ₁, γ 1 * ℓ v = 0) (s : ℝ) :
    γ 1 * ℓ ((ξ : ℝ × ℝ → V) (s, 1)) - γ 0 * ℓ ((ξ : ℝ × ℝ → V) (s, 0)) = 0 := by
  have hξ1 : ContDiff ℝ 1 (ξ : ℝ × ℝ → V) := (mem_testMap_iff.1 ξ.2).1.of_le (by norm_num)
  set g : ℝ → ℝ := fun s ↦ γ 1 * ℓ ((ξ : ℝ × ℝ → V) (s, 1)) - γ 0 * ℓ ((ξ : ℝ × ℝ → V) (s, 0))
  have hg : Continuous g := by
    have h1 := (ℓ.continuous.comp (hξ1.continuous.comp (Continuous.prodMk_left 1)))
    have h0 := (ℓ.continuous.comp (hξ1.continuous.comp (Continuous.prodMk_left 0)))
    exact (continuous_const.mul h1).sub (continuous_const.mul h0)
  -- `g` integrates to zero against every test function `β`.
  have hβ : ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → ∫ s, β s • g s = 0 := by
    intro β hβ hβs
    set ψ : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ (β z.1 * γ z.2) • ℓ
    have hψ : ContDiff ℝ 1 ψ :=
      (((hβ.comp contDiff_fst).mul (hγ.comp contDiff_snd)).smul contDiff_const).of_le (by simp)
    have hψs : HasCompactSupport ψ := by
      refine HasCompactSupport.intro (hβs.isCompact.prod hγs.isCompact) fun z hz ↦ ?_
      rcases not_and_or.1 hz with hz | hz
      · simp [ψ, image_eq_zero_of_notMem_tsupport hz]
      · simp [ψ, image_eq_zero_of_notMem_tsupport hz]
    have hw := integral_apply_add_eq_zero_of_mem_H1 h hψ hψs
      (fun s v hv ↦ by simp [ψ, mul_assoc, h₀ v hv]) (fun s v hv ↦ by simp [ψ, mul_assoc, h₁ v hv])
    rw [integral_jetₗ_add_eq_integral_sub hψ hψs ξ] at hw
    rw [← hw]
    refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
    simp only [ψ, g, smul_eq_mul, smul_apply]
    ring
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrable hβ
  exact congr_fun ((hg.ae_eq_iff_eq volume continuous_const).1 hae) s

variable [FiniteDimensional ℝ V]

/-- **The completion keeps the boundary conditions.** A test map whose `L²` jet lies in the
`W^{1,2}` completion `H1 (boundaryCondition Λ₀ Λ₁)` of the maps with boundary values in `Λ₀`
and `Λ₁` itself has its boundary values in `Λ₀` and `Λ₁`: the completion acquires no test map
violating the boundary conditions. -/
theorem jetₗ_mem_H1_boundaryCondition_iff {ξ : testMap V} :
    jetₗ V ξ ∈ H1 (boundaryCondition Λ₀ Λ₁) ↔ (ξ : ℝ × ℝ → V) ∈ boundaryCondition Λ₀ Λ₁ := by
  refine ⟨fun h s ↦ ?_, jetₗ_mem_H1⟩
  -- A bump at `c` equal to `1` at `c` and to `0` at the other edge.
  have hbump : ∀ c : ℝ, ∃ γ : ℝ → ℝ, ContDiff ℝ ∞ γ ∧ HasCompactSupport γ ∧ γ c = 1 ∧
      ∀ x, 1 ≤ |x - c| → γ x = 0 := fun c ↦ by
    let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
    refine ⟨b, b.contDiff, b.hasCompactSupport, b.one_of_mem_closedBall (by simp [b]),
      fun x hx ↦ b.zero_of_le_dist ?_⟩
    rw [Real.dist_eq]
    exact le_trans (by norm_num [b]) hx
  -- A functional vanishing on `Λ` but not at `v ∉ Λ`.
  have hsep : ∀ (Λ : Submodule ℝ V) (v : V), v ∉ Λ →
      ∃ ℓ : V →L[ℝ] ℝ, (∀ w ∈ Λ, ℓ w = 0) ∧ ℓ v ≠ 0 := fun Λ v hv ↦ by
    obtain ⟨f, hfv, hΛ⟩ := Submodule.exists_le_ker_of_notMem hv
    exact ⟨LinearMap.toContinuousLinearMap f, fun w hw ↦ hΛ hw, hfv⟩
  obtain ⟨γ₀, hγ₀, hγ₀s, hγ₀0, hγ₀1⟩ := hbump 0
  obtain ⟨γ₁, hγ₁, hγ₁s, hγ₁1, hγ₁0⟩ := hbump 1
  have hγ₀1' : γ₀ 1 = 0 := hγ₀1 1 (by norm_num)
  have hγ₁0' : γ₁ 0 = 0 := hγ₁0 0 (by norm_num)
  constructor
  · by_contra hv
    obtain ⟨ℓ, hℓΛ, hℓv⟩ := hsep Λ₀ _ hv
    have := sub_eq_zero_of_jetₗ_mem_H1 h ℓ hγ₀ hγ₀s (fun v hv ↦ by simp [hℓΛ v hv])
      (fun v _ ↦ by simp [hγ₀1']) s
    simp [hγ₀0, hγ₀1', hℓv] at this
  · by_contra hv
    obtain ⟨ℓ, hℓΛ, hℓv⟩ := hsep Λ₁ _ hv
    have := sub_eq_zero_of_jetₗ_mem_H1 h ℓ hγ₁ hγ₁s (fun v _ ↦ by simp [hγ₁0'])
      (fun v hv ↦ by simp [hℓΛ v hv]) s
    simp [hγ₁1, hγ₁0', hℓv] at this

end Green

end TauCeti.StripSobolev
