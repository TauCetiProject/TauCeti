/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher

/-!
# Freezing the coefficients of the nonlinear Cauchy–Riemann equation

Let `u` be a weak solution of the planar nonlinear Cauchy–Riemann equation
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` on an open `Ω ⊆ ℂ` (`TauCeti.IsWeakCauchyRiemannOn`), for `p > 2`
and coefficients `J`, `η` of class `Cⁿ` with `n ≥ 1` on an open set `W ⊆ ℂ × V` containing the
graph of `u`. Elliptic bootstrapping (McDuff–Salamon, Remark B.4.3) freezes the coefficients along
`u`: with `Jᵤ z = J(z, u z)` and `ηᵤ z = η(z, u z)`, the map `u` solves the *linear* equation
`∂ₛu + Jᵤ ∂ₜu = ηᵤ`, to which the interior regularity of the linear operator with Sobolev
coefficients applies.

This file proves the part of the bootstrap that does not use that regularity theorem:

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_coeff_comp`: if `u ∈ W^{m,p}_loc(Ω)` with
  `1 ≤ m ≤ n`, then `Jᵤ` and `ηᵤ` are in `W^{m,p}_loc(Ω)`. This is the regularity the induction
  feeds back into the linear theorem at each order.
* `TauCeti.IsWeakCauchyRiemannOn.exists_isWeakCRSolution_linearization`: `Jᵤ` has a weak
  derivative `DJᵤ` with `(Jᵤ, DJᵤ, 0)` Sobolev Cauchy–Riemann coefficients
  (`TauCeti.IsSobolevCRCoefficients`), `Jᵤ² = -1` on `Ω` when `J² = -1` on `W`, and `u` is a
  weak solution of `∂ₛu + Jᵤ ∂ₜu = ηᵤ` in the sense of `TauCeti.IsWeakCRSolution`.
* `TauCeti.isWeakCRSolution_linearization_id`: the check `J = i`, `η = 0`, `u = id`.

The weak formulation `TauCeti.IsWeakCRSolution` pairs with the inner product, so the second
statement is for finite-dimensional real inner product spaces `V`. Any finite-dimensional real
normed space carries an inner product whose norm is equivalent to the given one, and equivalent
norms define the same Sobolev spaces `W^{k,p}_loc` and smoothness classes.

The second statement only needs `η` to be continuous on `W`: the frozen forcing `ηᵤ` enters the
linear equation only through its local integrability.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Remark B.4.3 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} {Ω : Opens ℂ} {p : ℝ≥0} {n : WithTop ℕ∞} {W : Set (ℂ × V)}

namespace IsWeakCauchyRiemannOn

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- **The frozen coefficients inherit the regularity of `u`.** Let `p > 2`, let `u` be a weak
solution of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `Ω`, and let `J` and `η` be `Cⁿ` on an open
`W ⊆ ℂ × V` containing the graph of `u` over `Ω`. If `u ∈ W^{k+1,p}_loc(Ω)` with `k + 1 ≤ n`, then
`z ↦ J z (u z)` and `z ↦ η z (u z)` are in `W^{k+1,p}_loc(Ω)`. -/
theorem memWkpLoc_coeff_comp (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ n (fun x : ℂ × V => J x.1 x.2) W)
    (hη : ContDiffOn ℝ n (fun x : ℂ × V => η x.1 x.2) W) (huW : ∀ z ∈ Ω, (z, u z) ∈ W)
    {k : ℕ} (hk : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hu : MemWkpLoc p Ω (k + 1) u) :
    MemWkpLoc p Ω (k + 1) (fun z => J z (u z)) ∧ MemWkpLoc p Ω (k + 1) (fun z => η z (u z)) :=
  ⟨hu.contDiffOn_comp_graph_succ hp h.continuousOn hW (hJ.of_le (by exact_mod_cast hk)) huW,
    hu.contDiffOn_comp_graph_succ hp h.continuousOn hW (hη.of_le (by exact_mod_cast hk)) huW⟩

end Normed

section InnerProduct

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- **The linearized equation.** Let `p > 2`, let `u` be a weak solution of
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `Ω`, and let `J` be `Cⁿ`, `n ≥ 1`, and `η` continuous on an
open `W ⊆ ℂ × V` containing the graph of `u` over `Ω`, with `J(z, x)² = -1` on `W`. Then the frozen
structure `Jᵤ z = J z (u z)` has a weak derivative `DJᵤ` for which `(Jᵤ, DJᵤ, 0)` are Sobolev
Cauchy–Riemann coefficients of class `W^{1,p}`, `Jᵤ² = -1` on `Ω`, and `u` is a weak solution of
the linear equation `∂ₛu + Jᵤ ∂ₜu = ηᵤ` with `ηᵤ z = η z (u z)`.

The weak formulation `TauCeti.IsWeakCRSolution` uses the inner product, so `V` is a
finite-dimensional real inner product space here. -/
theorem exists_isWeakCRSolution_linearization (h : IsWeakCauchyRiemannOn p Ω J η u) (hp : 2 < p)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ n (fun x : ℂ × V => J x.1 x.2) W)
    (hη : ContinuousOn (fun x : ℂ × V => η x.1 x.2) W) (hn : 1 ≤ n)
    (hJ2 : ∀ x ∈ W, J x.1 x.2 * J x.1 x.2 = -1) (huW : ∀ z ∈ Ω, (z, u z) ∈ W) :
    ∃ DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V,
      IsSobolevCRCoefficients p Ω (fun z => J z (u z)) DJ 0 ∧
        (∀ z ∈ (Ω : Set ℂ), J z (u z) * J z (u z) = -1) ∧
        IsWeakCRSolution p Ω (fun z => J z (u z)) DJ 0 u (fun z => η z (u z)) := by
  have hp' : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hJu : MemWkpLoc p Ω (0 + 1) (fun z => J z (u z)) :=
    h.memWkpLoc_one.contDiffOn_comp_graph_succ hp h.continuousOn hW
      (hJ.of_le (by simpa using hn)) huW
  obtain ⟨DJ, hDJ, hDJp⟩ := hJu.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω (fun z => J z (u z)) DJ 0 :=
    { hasWeakFDerivOn := hDJ
      memLpLoc_coeff := hJu.memLpLoc
      memLpLoc_deriv := memWkpLoc_zero_iff.1 hDJp
      memLpLoc_zeroth := memLpLoc_zero }
  have h2 : (p : ℝ≥0∞)⁻¹ ≤ 2⁻¹ := ENNReal.inv_le_inv.2 hp'.le
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ ≤ 1 :=
    (add_le_add h2 h2).trans ENNReal.inv_two_add_inv_two.le
  obtain ⟨-, hup, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff_of_isOpen.1 h
  refine ⟨DJ, hc, fun z hz => hJ2 _ (huW z hz), ?_⟩
  refine (hc.isWeakCRSolution_iff_ae hpp ENNReal.coe_ne_top ENNReal.coe_ne_top hD hup hDp
    ((hη.comp (continuousOn_id.prodMk h.continuousOn) huW).locallyIntegrableOn
      Ω.isOpen.measurableSet)).2 ?_
  filter_upwards [hae] with z hz
  simpa using hz

end InnerProduct

end IsWeakCauchyRiemannOn

/-- **Check: the standard structure.** For `J = i`, `η = 0` and `u = id` on `ℂ`, the linearized
equation is the homogeneous equation `∂ₛu + i ∂ₜu = 0` for the constant structure `i`, and the
identity solves it weakly. -/
theorem isWeakCRSolution_linearization_id (hp : 2 < p) :
    IsWeakCRSolution p Ω (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 id 0 := by
  have hid := isWeakCauchyRiemannOn_id (p := (p : ℝ≥0∞)) (Ω := Ω)
  obtain ⟨DJ, hc, -, hsol⟩ := hid.exists_isWeakCRSolution_linearization (n := ⊤)
    (W := Set.univ) hp isOpen_univ contDiffOn_const continuousOn_const le_top
    (fun x _ => by ext w; simp [← mul_assoc]) fun _ _ => Set.mem_univ _
  have hconst : HasWeakFDerivOn volume Ω (fun _ : ℂ => I • ContinuousLinearMap.id ℝ ℂ) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by
      simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := v)
        (I • ContinuousLinearMap.id ℝ ℂ)
  have hDJ : DJ =ᵐ[volume.restrict Ω] 0 := hc.hasWeakFDerivOn.ae_eq hconst
  have h := (isWeakCRSolution_congr_ae (q := p) (.refl _ _) hDJ (.refl _ _) (.refl _ _)
    (.refl _ _)).1 hsol
  exact h

end TauCeti
