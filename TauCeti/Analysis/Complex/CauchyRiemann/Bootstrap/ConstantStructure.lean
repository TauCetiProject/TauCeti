/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
public import TauCeti.Analysis.Complex.Wirtinger.Regularity
public import TauCeti.Analysis.Sobolev.Local.ChainRule
public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The first bootstrap step for the weak Cauchy–Riemann equation

This file proves the first step of the elliptic bootstrap for the planar weak Cauchy–Riemann
equation `∂ₛu + J(z, u) ∂ₜu = η(z, u)` of `TauCeti.IsWeakCauchyRiemannOn`.

For every structure field `J` and inhomogeneous term `η` that are `C¹` jointly in `(z, x)` near
the graph of a weak solution `u`, the coefficients `z ↦ J(z, u z)` and `z ↦ η(z, u z)` belong to
`W^{1,p}_loc`. This is the composition of the continuous `W^{1,p}_loc` map `u` with a `C¹` map of
the graph, `TauCeti.MemWkpLoc.contDiffOn_comp_graph`; continuity of `u` is part of the predicate.
These are the coefficients to which the linear interior theory with Sobolev coefficients is
applied in the bootstrap.

For the constant structure `J = i` on a finite-dimensional complex inner product space `F`, the
equation says that `\bar∂u = η(z, u)/2` weakly
(`TauCeti.IsWeakCauchyRiemannOn.hasWeakConjWirtingerDerivOn`). If `η` is `C¹` near the graph, the
right-hand side is in `W^{1,p}_loc`, and interior regularity for `\bar∂`
(`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_succ`) gives `u ∈ W^{2,p}_loc` for `1 < p < ∞`.
For `p > 2` the weak derivative of `u` is then in `W^{1,p}_loc`, so it has a continuous
representative by Morrey's embedding, and `u` is `C¹`. This is the interior case `ℓ = 1` of the
bootstrap for constant structures: a `W^{1,p}` solution for a `C¹` term is `W^{2,p}`, not merely
`W^{1,p}`, and hence `C¹`.

The higher orders of the bootstrap need composition in `W^{k,p}_loc` for `k ≥ 2`, and the general
structure needs the interior estimates with Sobolev coefficients; neither is used here.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_one_comp_graph`: for a weak solution `u` and a map `g`
  that is `C¹` on an open set containing the graph of `u`, `z ↦ g(z, u z)` is in `W^{1,p}_loc`.
* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_one_comp_structure` and
  `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_one_comp_inhomogeneous`: the coefficients
  `z ↦ J(z, u z)` and `z ↦ η(z, u z)` are in `W^{1,p}_loc`.
* `TauCeti.memWkpLoc_two_of_isWeakCauchyRiemannOn_I_smul_id`: for `J = i`, `1 < p < ∞` and `η`
  of class `C¹` near the graph, a weak solution is in `W^{2,p}_loc`.
* `TauCeti.contDiffOn_one_of_isWeakCauchyRiemannOn_I_smul_id`: for `J = i`, `2 < p < ∞` and `η`
  of class `C¹` near the graph, a weak solution is `C¹`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Remark B.4.3.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Coefficients along a weak solution -/

section Coefficients

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H]
  [NormedSpace ℝ H] {p : ℝ≥0∞} {U : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V}
  {u : ℂ → V} {W : Set (ℂ × V)}

namespace IsWeakCauchyRiemannOn

/-- **Composition along the graph of a weak solution.** If `u` is a weak solution on `U` and `g`
is `C¹` on an open set `W` containing the graph `{(z, u z) | z ∈ U}`, then `z ↦ g(z, u z)` is in
`W^{1,p}_loc(U)`. No hypothesis on `J`, `η` or the exponent is needed: a weak solution is a
continuous member of `W^{1,p}_loc`. -/
theorem memWkpLoc_one_comp_graph [CompleteSpace H] (h : IsWeakCauchyRiemannOn p U J η u)
    {g : ℂ × V → H} (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W) (huW : ∀ z ∈ U, (z, u z) ∈ W) :
    MemWkpLoc p U 1 (fun z => g (z, u z)) :=
  h.memWkpLoc_one.contDiffOn_comp_graph h.continuousOn hW hg huW

/-- **The structure along a weak solution.** If the structure field `J` is `C¹` jointly in
`(z, x)` on an open set containing the graph of a weak solution `u` on `U`, then
`z ↦ J(z, u z)` is in `W^{1,p}_loc(U)`. The square identity `J² = -1` is not needed. -/
theorem memWkpLoc_one_comp_structure (h : IsWeakCauchyRiemannOn p U J η u) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 (fun q : ℂ × V => J q.1 q.2) W) (huW : ∀ z ∈ U, (z, u z) ∈ W) :
    MemWkpLoc p U 1 (fun z => J z (u z)) :=
  have : CompleteSpace V := h.completeSpace
  h.memWkpLoc_one_comp_graph hW hJ huW

/-- **The inhomogeneous term along a weak solution.** If `η` is `C¹` jointly in `(z, x)` on an
open set containing the graph of a weak solution `u` on `U`, then `z ↦ η(z, u z)` is in
`W^{1,p}_loc(U)`. -/
theorem memWkpLoc_one_comp_inhomogeneous (h : IsWeakCauchyRiemannOn p U J η u) (hW : IsOpen W)
    (hη : ContDiffOn ℝ 1 (fun q : ℂ × V => η q.1 q.2) W) (huW : ∀ z ∈ U, (z, u z) ∈ W) :
    MemWkpLoc p U 1 (fun z => η z (u z)) :=
  have : CompleteSpace V := h.completeSpace
  h.memWkpLoc_one_comp_graph hW hη huW

end IsWeakCauchyRiemannOn

end Coefficients

/-! ### The constant structure `i` -/

section Constant

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {η : ℂ → F → F} {u : ℂ → F} {W : Set (ℂ × F)}

/-- A continuous member of `W^{2,p}_loc` on an open set, with `p > 2` and finite-dimensional
codomain, is `C¹` there: its weak derivative is in `W^{1,p}_loc`, so it agrees almost everywhere
with its continuous precise representative, which is then a continuous weak derivative. -/
private theorem contDiffOn_one_of_memWkpLoc_two_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] {v : ℂ → G} (hp : 2 < p) (hv : MemWkpLoc p Ω 2 v)
    (hc : ContinuousOn v Ω) : ContDiffOn ℝ 1 v Ω := by
  have : CompleteSpace G := FiniteDimensional.complete ℝ G
  obtain ⟨D, hD, hD1⟩ := hv.exists_weakFDeriv_of_isOpen
  have hD' := hD.congr_ae_deriv (hD1.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le))
  simpa using hD'.contDiffOn_succ hc (n := 0)
    (contDiffOn_zero.2 (hD1.continuousOn_preciseRepresentative hp))

/-- **`W^{2,p}` regularity for the constant structure.** Let `F` be a finite-dimensional complex
inner product space, `1 < p < ∞`, and `η` of class `C¹` jointly in `(z, x)` on an open set `W`
containing the graph of `u` over `Ω`. A weak solution `u` on `Ω` of `∂ₛu + i ∂ₜu = η(z, u)` is in
`W^{2,p}_loc(Ω)`: one derivative more than the equation assumes. -/
theorem memWkpLoc_two_of_isWeakCauchyRiemannOn_I_smul_id (hp : 1 < p) (hp_top : p ≠ ⊤)
    (h : IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) η u)
    (hW : IsOpen W) (hη : ContDiffOn ℝ 1 (fun q : ℂ × F => η q.1 q.2) W)
    (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) : MemWkpLoc p Ω 2 u := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hf : MemWkpLoc p Ω 1 (fun z => (2 : ℂ)⁻¹ • η z (u z)) :=
    h.memWkpLoc_one_comp_graph (g := fun q : ℂ × F => (2 : ℂ)⁻¹ • η q.1 q.2) hW
      (hη.const_smul _) huW
  exact h.hasWeakConjWirtingerDerivOn.memWkpLoc_succ hp hp_top h.memLpLoc hf

/-- **`C¹` regularity for the constant structure.** Let `F` be a finite-dimensional complex inner
product space, `2 < p < ∞`, and `η` of class `C¹` jointly in `(z, x)` on an open set `W`
containing the graph of `u` over `Ω`. A weak solution `u` on `Ω` of `∂ₛu + i ∂ₜu = η(z, u)` is
`C¹` on `Ω`. This is the interior case `ℓ = 1` of the bootstrap for `J = i`. -/
theorem contDiffOn_one_of_isWeakCauchyRiemannOn_I_smul_id (hp : 2 < p) (hp_top : p ≠ ⊤)
    (h : IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) η u)
    (hW : IsOpen W) (hη : ContDiffOn ℝ 1 (fun q : ℂ × F => η q.1 q.2) W)
    (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) : ContDiffOn ℝ 1 u Ω :=
  contDiffOn_one_of_memWkpLoc_two_of_continuousOn hp
    (memWkpLoc_two_of_isWeakCauchyRiemannOn_I_smul_id (ENNReal.one_lt_two.trans hp) hp_top h hW
      hη huW) h.continuousOn

end Constant

/-! ### Checks -/

section Checks

variable {p : ℝ≥0∞} {Ω : Opens ℂ}

/-- The identity solves the homogeneous equation for `J = i`, so it satisfies both conclusions,
here with the trivial term `η = 0` on all of `ℂ × ℂ`. -/
example (hp : 2 < p) (hp_top : p ≠ ⊤) :
    MemWkpLoc p Ω 2 (id : ℂ → ℂ) ∧ ContDiffOn ℝ 1 (id : ℂ → ℂ) Ω :=
  ⟨memWkpLoc_two_of_isWeakCauchyRiemannOn_I_smul_id (ENNReal.one_lt_two.trans hp) hp_top
      isWeakCauchyRiemannOn_id isOpen_univ contDiffOn_const fun _ _ => trivial,
    contDiffOn_one_of_isWeakCauchyRiemannOn_I_smul_id hp hp_top isWeakCauchyRiemannOn_id
      isOpen_univ contDiffOn_const fun _ _ => trivial⟩

/-- Conjugation is not a weak solution of the homogeneous equation for `J = i` on a nonempty
open set, so the theorems above say nothing about it. -/
example (hΩ : (Ω : Set ℂ).Nonempty) :
    ¬IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
      (starRingEnd ℂ) :=
  not_isWeakCauchyRiemannOn_conj hΩ

end Checks

end TauCeti
