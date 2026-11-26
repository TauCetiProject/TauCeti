/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Green
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc

/-!
# The nonlinear Cauchy–Riemann equation at a totally real boundary is linear in its solution

Let `Ω ⊆ ℂ` be open, write `z = s + i t` and `U = Ω ∩ {0 ≤ t}`, and let `V` be a
finite-dimensional real inner product space with a real subspace `Λ`, the space of boundary
values. Let `u` be a weak solution on the half-disc set `U` of the nonlinear Cauchy–Riemann
equation

`∂ₛu + J(z, u) ∂ₜu = η(z, u)`

in the sense of `TauCeti.IsWeakCauchyRiemannOn p U J η u`, for finite `p > 2`, satisfying the
totally real boundary condition `⟪Λ, J(s, u s) u s⟫ = 0` on `ℝ ∩ Ω`. This follows from
`u(s) ∈ Λ` when `⟪Λ, J(s, x) Λ⟫ = 0` for `x ∈ Λ`, as for `J(s, x) = i` and `Λ ⊥ iΛ`
(`TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn_of_mem`). This file proves that
`u` is then a weak solution up to the boundary, in the sense of `TauCeti.IsWeakCRSolutionHalf`, of
the linear equation

`∂ₛξ + A ∂ₜξ = f`, `A(z) = J(z, u z)`, `f(z) = η(z, u z)`,

with the boundary condition carried by `Λ` and `DA` a weak derivative of the frozen coefficient
`A`. This is the step of McDuff–Salamon's proof of Theorem B.4.1 that freezes the solution in
the coefficients at the boundary, as `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn` does in the
interior, so that the linear regularity of `TauCeti.IsWeakCRSolutionHalf` up to the boundary
applies to `u`.

The coefficient `A` is in `W^{1,p}` up to the axis when `J` is `C¹` near the graph of `u` over
`U`, by the half-disc composition theorem `TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ_halfPlane`
(which uses `p > 2` and the continuity of `u` up to the axis). The weak equation then follows
from Green's formula up to the axis for Sobolev data,
`TauCeti.isWeakCRSolutionHalf_iff_ae`: the boundary term `∫_ℝ ⟪φ, A u⟫` vanishes because the
admissible test functions take values in `Λ` on `ℝ`. No hypothesis on `η` is needed, since the
equation makes `η(z, u z)` locally integrable up to the axis.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.isWeakCRSolutionHalf`: for any weak derivative `DA` of the
  frozen coefficient, locally `Lᵖ` up to the axis, with `p ≥ 2` (including `p = ∞`), the linear
  weak equation up to the boundary holds.
* `TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn`: for `J` of class `C¹` near the
  graph and `p > 2`, such a weak derivative `DA` exists.
* `TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn_of_mem`: the same for the boundary
  condition `u(s) ∈ Λ` and coefficients with `⟪Λ, J(s, x) Λ⟫ = 0` for `x ∈ Λ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1, Remark B.4.3 and equation (B.4.3)).
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {Λ : Submodule ℝ V} {W : Set (ℂ × V)} {J : ℂ → V → V →L[ℝ] V}
  {η : ℂ → V → V} {u : ℂ → V} {p : ℝ≥0∞}

/-- **The nonlinear equation up to the boundary is linear in its solution.** Let `u` be a weak
solution of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `U = Ω ∩ {0 ≤ t}` for `p ≥ 2`, and let `DA`
be a weak derivative on `Ω ∩ {0 < t}` of the frozen coefficient `A(z) = J(z, u z)`, with `A` and
`DA` locally `Lᵖ` up to the axis. If `A u` is continuous on `U` and `⟪Λ, A(s) u(s)⟫ = 0` on
`ℝ ∩ Ω`, then `u` is a weak solution up to the boundary of `∂ₛξ + A ∂ₜξ = η(z, u z)` with
boundary values in `Λ`. -/
theorem IsWeakCauchyRiemannOn.isWeakCRSolutionHalf
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) (hp : 2 ≤ p)
    {DA : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hA : HasWeakFDerivOn volume Ω.upperHalf (fun z => J z (u z)) DA)
    (hAp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) fun z => J z (u z))
    (hDAp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DA)
    (hAu : ContinuousOn (fun z => J z (u z) (u z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (u s) (u s)⟫_ℝ = 0) :
    IsWeakCRSolutionHalf p Ω Λ (fun z => J z (u z)) DA 0 u (fun z => η z (u z)) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  -- The weak identity does not see the exponent, so `p = ∞` follows from `p = 2`.
  suffices IsWeakCRSolutionHalf 2 Ω Λ (fun z => J z (u z)) DA 0 u (fun z => η z (u z)) from
    isWeakCRSolutionHalf_iff.2 ⟨h.memLpLoc, (isWeakCRSolutionHalf_iff.1 this).2⟩
  obtain ⟨-, hu, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff.1 (h.mono_exponent hp)
  rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hD
  rw [interior_inter_setOf_im_nonneg Ω.isOpen, ← Opens.coe_upperHalf] at hae
  exact (isWeakCRSolutionHalf_iff_ae (by norm_num [ENNReal.inv_two_add_inv_two]) (by simp)
    (by simp) hA (hAp.mono_exponent hp) (hDAp.mono_exponent hp) memLpLoc_zero hD hu hDp hAu
    hΛ).2 (by simpa using hae)

/-- **Freezing the coefficients at the boundary** (McDuff–Salamon, Theorem B.4.1, the linear
step). Let `2 < p < ∞`, let `J` be of class `C¹` jointly in `(z, x)` on `W ∩ {0 ≤ z.im}` for an
open set `W` containing the graph of `u` over `U = Ω ∩ {0 ≤ t}`, and let `u` be a weak solution
of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `U` with `⟪Λ, J(s, u s) u s⟫ = 0` on `ℝ ∩ Ω`. Then the frozen
coefficient `A(z) = J(z, u z)` has a weak derivative `DA` on `Ω ∩ {0 < t}`, locally `Lᵖ` up to
the axis, and `u` is a weak solution up to the boundary of `∂ₛξ + A ∂ₜξ = η(z, u z)` with
boundary values in `Λ`. -/
theorem exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn (hp : 2 < p) (hp' : p ≠ ⊤)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (hΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (u s) (u s)⟫_ℝ = 0)
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    ∃ DA : ℂ → ℂ →L[ℝ] V →L[ℝ] V,
      HasWeakFDerivOn volume Ω.upperHalf (fun z => J z (u z)) DA ∧
        MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DA ∧
        IsWeakCRSolutionHalf p Ω Λ (fun z => J z (u z)) DA 0 u (fun z => η z (u z)) := by
  have hAw : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 fun z => J z (u z) := by
    lift p to ℝ≥0 using hp'
    exact h.memWkpLoc_one.contDiffOn_comp_graph_succ_halfPlane (k := 0)
      (by exact_mod_cast hp) h.continuousOn hW (by simpa using hJ) huW
  obtain ⟨hAp, DA, hDA, hDAp⟩ := memWkpLoc_succ_iff.1 hAw
  rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hDA
  have hAc : ContinuousOn (fun z => J z (u z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    hJ.continuousOn.comp (continuousOn_id.prodMk h.continuousOn) fun z hz => ⟨huW z hz, hz.2⟩
  exact ⟨DA, hDA, memWkpLoc_zero_iff.1 hDAp, h.isWeakCRSolutionHalf hp.le hDA hAp
    (memWkpLoc_zero_iff.1 hDAp) (hAc.clm_apply h.continuousOn) hΛ⟩

/-- **Freezing the coefficients at the boundary, for `u(s) ∈ Λ`.** The case of
`TauCeti.exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn` in which the boundary condition is
`u(s) ∈ Λ` on `ℝ ∩ Ω` and `⟪Λ, J(s, x) Λ⟫ = 0` for real `s ∈ Ω` and `x ∈ Λ`, as for `J(s, x) = i`
and a totally real `Λ` orthogonal to `iΛ`. -/
theorem exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn_of_mem (hp : 2 < p) (hp' : p ≠ ⊤)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 (fun x : ℂ × V => J x.1 x.2) (W ∩ {x | 0 ≤ x.1.im}))
    (huW : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, (z, u z) ∈ W)
    (huΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → u s ∈ Λ)
    (hJΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ x ∈ Λ, ∀ v ∈ Λ, ∀ w ∈ Λ, ⟪v, J s x w⟫_ℝ = 0)
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J η u) :
    ∃ DA : ℂ → ℂ →L[ℝ] V →L[ℝ] V,
      HasWeakFDerivOn volume Ω.upperHalf (fun z => J z (u z)) DA ∧
        MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DA ∧
        IsWeakCRSolutionHalf p Ω Λ (fun z => J z (u z)) DA 0 u (fun z => η z (u z)) :=
  exists_isWeakCRSolutionHalf_of_isWeakCauchyRiemannOn hp hp' hW hJ huW
    (fun s hs v hv => hJΛ s hs _ (huΛ s hs) v hv _ (huΛ s hs)) h

end TauCeti
