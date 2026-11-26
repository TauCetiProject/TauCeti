/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.StdComplexLine

/-!
# Unique continuation for the coordinate Floer equation

Let `F` be a normed space, `J : (ℝ × ℝ) × F → (F →L[ℝ] F)` a field of endomorphisms and
`X : (ℝ × ℝ) × F → (ℝ × ℝ →L[ℝ] F)` a one-form. This file proves unique continuation for `C¹`
solutions `v : ℝ × ℝ → F` of the coordinate Floer equation

`∂ₜv - X(z, v) i = J(z, v) (∂ₛv - X(z, v) 1)`,

the form taken by the Floer equation `(du - X_K)^{0,1} = 0` in a chart of a manifold (in the
namespace `TauCeti.SmoothTwoForm`,
`isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub`), with `X`
the Hamiltonian one-form read in the chart. That one-form is not the Hamiltonian one-form of a
constant symplectic form, so the vector-space theorems for `TauCeti.SymplecticForm.floerOperator`
(`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`) do not apply to it. Here `X` and
`J` are arbitrary `C¹` data; the equation is the coordinate form used in the compactness theory
(`TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`):

* the difference `w = u - v` of two solutions satisfies the Cauchy–Riemann inequality
  `‖∂ₛw + J(z, u z) ∂ₜw‖ ≤ M ‖w‖` near every coincidence point
  (`TauCeti.Floer.exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub`), by the local
  Lipschitz bounds of `J` and `X`;
* so, by `TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_fderiv_le`, two solutions on a
  connected open set which agree on a nonempty open subset agree everywhere
  (`TauCeti.Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn`), and by
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_fderiv_le` two solutions
  which differ somewhere agree only on a discrete set
  (`TauCeti.Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub`).

Only the structure `J(z, u z)` along the first solution has to square to `-1`, and the regularity
of the data is only used along the graph of the first solution. The manifold versions are in
`TauCeti.Geometry.Symplectic.Floer.UniqueContinuation.Manifold`.

## Main results

* `TauCeti.Floer.exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub`: the Cauchy–Riemann
  inequality for the difference of two solutions of the coordinate Floer equation.
* `TauCeti.Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn`,
  `TauCeti.Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub`: unique
  continuation and isolated coincidences for the coordinate Floer equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation) and Section 8.1 (the inhomogeneous equation).
-/

public section

open Filter Set Topology

namespace TauCeti.Floer

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : (ℝ × ℝ) × F → F →L[ℝ] F} {X : (ℝ × ℝ) × F → ℝ × ℝ →L[ℝ] F} {u v : ℝ × ℝ → F}
  {Ω : Set (ℝ × ℝ)}

/-- **The difference of two solutions of the coordinate Floer equation obeys a Cauchy–Riemann
inequality.** Let `u` and `v` be `C¹` solutions of `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on
an open set `Ω ⊆ ℝ × ℝ`, with a coincidence `u z₀ = v z₀` at `z₀ ∈ Ω`, let `J` and `X` be `C¹` at
`(z₀, u z₀)`, and let `J(z, u z)² = -1` on `Ω`. Near `z₀`, the difference `w = u - v` satisfies
`‖∂ₛw + J(z, u z) ∂ₜw‖ ≤ M ‖w‖` for some constant `M`. -/
theorem exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub (hΩ : IsOpen Ω)
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (hJ : ContDiffAt ℝ 1 J (z₀, u z₀))
    (hX : ContDiffAt ℝ 1 X (z₀, u z₀))
    (hJJ : ∀ z ∈ Ω, J (z, u z) ∘L J (z, u z) = -ContinuousLinearMap.id ℝ F)
    (hu : ContDiffOn ℝ 1 u Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (hFu : ∀ z ∈ Ω, fderiv ℝ u z stdComplexLineImag - X (z, u z) stdComplexLineImag =
      J (z, u z) (fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal))
    (hFv : ∀ z ∈ Ω, fderiv ℝ v z stdComplexLineImag - X (z, v z) stdComplexLineImag =
      J (z, v z) (fderiv ℝ v z stdComplexLineReal - X (z, v z) stdComplexLineReal))
    (h : u z₀ = v z₀) :
    ∃ M, ∀ᶠ z in 𝓝 z₀, ‖fderiv ℝ (u - v) z stdComplexLineReal +
      J (z, u z) (fderiv ℝ (u - v) z stdComplexLineImag)‖ ≤ M * ‖(u - v) z‖ := by
  have hΩz := hΩ.mem_nhds hz₀
  have huc : ContinuousAt u z₀ := hu.continuousOn.continuousAt hΩz
  have hvc : ContinuousAt v z₀ := hv.continuousOn.continuousAt hΩz
  -- The data differ along the two graphs by at most a multiple of `‖u - v‖`.
  obtain ⟨LJ, hLJ⟩ := hJ.exists_eventually_norm_sub_le huc hvc h
  obtain ⟨LX, hLX⟩ := hX.exists_eventually_norm_sub_le huc hvc h
  -- The structure along `u` and the factor `a = ∂ₛv - X(z, v) 1` are bounded near `z₀`.
  have hJu : ContinuousAt (fun z ↦ J (z, u z)) z₀ :=
    hJ.continuousAt.comp_of_eq (continuousAt_id.prodMk huc) rfl
  set a : ℝ × ℝ → F := fun z ↦ fderiv ℝ v z stdComplexLineReal - X (z, v z) stdComplexLineReal
  have ha : ContinuousAt a z₀ :=
    (((hv.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt hΩz).clm_apply
      continuousAt_const).sub ((hX.continuousAt.comp_of_eq (continuousAt_id.prodMk hvc)
        (by simp [h])).clm_apply continuousAt_const)
  refine ⟨LX * ‖stdComplexLineReal‖ + (‖J (z₀, u z₀)‖ + 1) * (LX * ‖stdComplexLineImag‖) +
    (‖J (z₀, u z₀)‖ + 1) * (LJ * (‖a z₀‖ + 1)), ?_⟩
  filter_upwards [hΩz, hLJ, hLX, hJu.norm.eventually (gt_mem_nhds (lt_add_one _)),
    ha.norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz hJ' hX' hJz haz
  set A := J (z, u z)
  set B := J (z, v z)
  have hA (w : F) : A (A w) = -w := by
    simpa using congrArg (· w) (hJJ z hz)
  have hdu : DifferentiableAt ℝ u z :=
    (hu.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz)
  have hdv : DifferentiableAt ℝ v z :=
    (hv.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hz)
  -- Applying `J(z, u z)` to the equation of `u` gives
  -- `J ∂ₜu - J X(z, u) i = -(∂ₛu - X(z, u) 1)`, since `J(z, u z)² = -1`.
  have hAu : A (fderiv ℝ u z stdComplexLineImag) - A (X (z, u z) stdComplexLineImag) =
      -(fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal) := by
    rw [← map_sub, hFu z hz, hA]
  -- The equation of `v` reads `J(z, v z) (a z) = ∂ₜv - X(z, v) i`.
  have hBv : B (a z) = fderiv ℝ v z stdComplexLineImag - X (z, v z) stdComplexLineImag :=
    (hFv z hz).symm
  -- Subtracting the two equations expresses the operator through differences of the data.
  have hD : fderiv ℝ (u - v) z stdComplexLineReal + A (fderiv ℝ (u - v) z stdComplexLineImag) =
      (X (z, u z) - X (z, v z)) stdComplexLineReal +
        A ((X (z, u z) - X (z, v z)) stdComplexLineImag) + A ((A - B) (a z)) := by
    simp only [fderiv_sub hdu hdv, sub_apply, map_sub, hA, hBv]
    simp only [a]
    linear_combination (norm := module) hAu
  rw [hD, Pi.sub_apply]
  calc _ ≤ ‖X (z, u z) - X (z, v z)‖ * ‖stdComplexLineReal‖ +
          ‖A‖ * (‖X (z, u z) - X (z, v z)‖ * ‖stdComplexLineImag‖) +
          ‖A‖ * (‖A - B‖ * ‖a z‖) :=
        norm_add₃_le.trans (add_le_add_three (ContinuousLinearMap.le_opNorm _ _)
          ((A.le_opNorm _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _))
          ((A.le_opNorm _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)))
    _ ≤ LX * ‖u z - v z‖ * ‖stdComplexLineReal‖ +
          (‖J (z₀, u z₀)‖ + 1) * (LX * ‖u z - v z‖ * ‖stdComplexLineImag‖) +
          (‖J (z₀, u z₀)‖ + 1) * (LJ * ‖u z - v z‖ * (‖a z₀‖ + 1)) := by
        gcongr
    _ = _ := by ring

variable [FiniteDimensional ℝ F]

/-- **Unique continuation for the coordinate Floer equation.** Let `J` and `X` be `C¹` near the
graph of `u` over a connected open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. Two `C¹`
solutions `u`, `v` of `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on `Ω` that agree on a
nonempty open subset of `Ω` agree on `Ω`. -/
theorem eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (z, u z))
    (hJJ : ∀ z ∈ Ω, J (z, u z) ∘L J (z, u z) = -ContinuousLinearMap.id ℝ F)
    (hX : ∀ z ∈ Ω, ContDiffAt ℝ 1 X (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hFu : ∀ z ∈ Ω, fderiv ℝ u z stdComplexLineImag - X (z, u z) stdComplexLineImag =
      J (z, u z) (fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal))
    (hFv : ∀ z ∈ Ω, fderiv ℝ v z stdComplexLineImag - X (z, v z) stdComplexLineImag =
      J (z, v z) (fderiv ℝ v z stdComplexLineReal - X (z, v z) stdComplexLineReal))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn u v U) :
    EqOn u v Ω := by
  have h : EqOn (u - v) 0 Ω :=
    eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_fderiv_le hΩ hΩc
      (contDiffOn_comp_graph (J := fun z x ↦ J (z, x)) hJ hu) hJJ (hu.sub hv)
      (fun z hz h ↦ exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub hΩ hz (hJ z hz)
        (hX z hz) hJJ hu hv hFu hFv (sub_eq_zero.1 h)) hU hUne hUΩ
      fun z hz ↦ sub_eq_zero.2 (h₀ hz)
  exact fun z hz ↦ sub_eq_zero.1 (h hz)

/-- **Isolated coincidences for the coordinate Floer equation.** Let `J` and `X` be `C¹` near the
graph of `u` over a connected open set `Ω ⊆ ℝ × ℝ`, with `J(z, u z)² = -1` on `Ω`. If two `C¹`
solutions `u`, `v` of `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on `Ω` differ somewhere in
`Ω`, the points of `Ω` where they agree form a discrete subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (z, u z))
    (hJJ : ∀ z ∈ Ω, J (z, u z) ∘L J (z, u z) = -ContinuousLinearMap.id ℝ F)
    (hX : ∀ z ∈ Ω, ContDiffAt ℝ 1 X (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hFu : ∀ z ∈ Ω, fderiv ℝ u z stdComplexLineImag - X (z, u z) stdComplexLineImag =
      J (z, u z) (fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal))
    (hFv : ∀ z ∈ Ω, fderiv ℝ v z stdComplexLineImag - X (z, v z) stdComplexLineImag =
      J (z, v z) (fderiv ℝ v z stdComplexLineReal - X (z, v z) stdComplexLineReal))
    (hne : ∃ z ∈ Ω, u z ≠ v z) : {z | u z ≠ v z} ∈ codiscreteWithin Ω := by
  simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using
    setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_fderiv_le hΩ hΩc
      (contDiffOn_comp_graph (J := fun z x ↦ J (z, x)) hJ hu) hJJ (hu.sub hv)
      (fun z hz h ↦ exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub hΩ hz (hJ z hz)
        (hX z hz) hJJ hu hv hFu hFv (sub_eq_zero.1 h))
      (by simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using hne)

end TauCeti.Floer
