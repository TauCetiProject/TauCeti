/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.DifferentialInequality
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Topology.Codiscrete

/-!
# Unique continuation for Floer solutions in a manifold

Let `M` be a boundaryless Hausdorff manifold with a two-form `ω`, such as a closed symplectic
manifold, and let `u, v : ℝ × ℝ → M` be `C¹` solutions of the Floer equation
`(du - X_K)^{0,1} = 0` on a connected open set `Ω` of the domain, for a perturbation
`K = K_s ds + K_t dt` and domain-dependent almost complex structures `J(z, x)` on the tangent
spaces of `M` whose readings in the charts of `M` are `C¹`. If `u` and `v` agree on a nonempty
open subset of `Ω`, they agree on all of `Ω`
(`TauCeti.SmoothTwoForm.eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`); otherwise the points
of `Ω` where they agree form a discrete subset of `Ω`
(`TauCeti.SmoothTwoForm.setOf_ne_mem_codiscreteWithin_of_isComplexLinearMap_perturbedMFDeriv`).

For a symplectic vector space target and Hamiltonian data this is
`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`. In a chart of the atlas of `M`,
however, the Floer equation becomes the coordinate equation

`∂ₜv - X(z, v) i = J(z, v) (∂ₛv - X(z, v) 1)`

(in the namespace `TauCeti.SmoothTwoForm`,
`isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub`), whose
one-form `X` is the Hamiltonian one-form read in the chart
(`TauCeti.SmoothTwoForm.hamiltonianOneFormInChartAt`). It is not the Hamiltonian one-form of a
constant symplectic form, so the local step is proved here for this coordinate equation with an
arbitrary `C¹` one-form `X` and `C¹` field `J`, in the form used by the compactness theory
(`TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`):

* the difference `w = u - v` of two solutions satisfies the Cauchy–Riemann inequality
  `‖∂ₛw + J(z, u z) ∂ₜw‖ ≤ M ‖w‖` near every coincidence point
  (`TauCeti.Floer.exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub`), by the local
  Lipschitz bounds of `J` and `X`;
* so, by `TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le`, two solutions on a connected
  open set which agree on a nonempty open subset agree everywhere
  (`TauCeti.Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn`), and by
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le` two solutions which differ
  somewhere agree only on a discrete set
  (`TauCeti.Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub`).

Only the structure `J(z, u z)` along the first solution has to square to `-1`, and the regularity
of the data is only used along the graph of the first solution.

On the manifold, the points of `Ω` near which `u` and `v` agree form an open set. It is closed in
`Ω`: at a limit point the two maps agree since `M` is Hausdorff, and on a small disc around it
both maps take values in one chart, whose coordinate expressions solve the coordinate equation and
agree on an open subset of the disc. As `Ω` is connected this set is all of `Ω`. Near a
coincidence of two solutions which differ somewhere in `Ω`, the coordinate expressions cannot agree
on the whole disc, so the coincidence is isolated.

For a cylindrical datum `K = H_t dt` and an `s`-independent `J_t`, the translate
`(s, t) ↦ u(s + c, t)` of a Floer trajectory is again one
(`TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_add_right`). So a trajectory in `M` which agrees with
such a translate on a nonempty open set is `(c, 0)`-periodic
(`TauCeti.SmoothTwoForm.periodic_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`). This is the step
of the argument of Floer, Hofer and Salamon for the density of the regular points of a
nonstationary trajectory which excludes a trajectory coinciding with one of its translates on an
open set.

## Main results

* `TauCeti.Floer.exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub`: the Cauchy–Riemann
  inequality for the difference of two solutions of the coordinate Floer equation.
* `TauCeti.Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn`,
  `TauCeti.Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub`: unique
  continuation and isolated coincidences for the coordinate Floer equation.
* `TauCeti.SmoothTwoForm.eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`,
  `TauCeti.SmoothTwoForm.setOf_ne_mem_codiscreteWithin_of_isComplexLinearMap_perturbedMFDeriv`:
  unique continuation and isolated coincidences for Floer solutions in a manifold.
* `TauCeti.SmoothTwoForm.periodic_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`: a Floer
  trajectory in a manifold which agrees with a translate on an open set is periodic.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation) and Section 8.1 (the inhomogeneous equation).
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open Complex Filter Function Set Topology
open scoped Manifold

/-! ### The coordinate Floer equation -/

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
  -- By the equation of `u`, `J ∂ₜu = -(∂ₛu - X(z, u) 1) + J X(z, u) i`.
  have hAu : A (fderiv ℝ u z stdComplexLineImag) =
      -(fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal) +
        A (X (z, u z) stdComplexLineImag) := by
    rw [← hA, ← map_add, ← hFu z hz, sub_add_cancel]
  -- Subtracting the two equations expresses the operator through differences of the data.
  have hD : fderiv ℝ (u - v) z stdComplexLineReal + A (fderiv ℝ (u - v) z stdComplexLineImag) =
      (X (z, u z) - X (z, v z)) stdComplexLineReal +
        A ((X (z, u z) - X (z, v z)) stdComplexLineImag) + A ((A - B) (a z)) := by
    rw [fderiv_sub hdu hdv, sub_apply, sub_apply,
      map_sub, hAu, sub_apply A B, map_sub, hA, ← hFv z hz]
    simp only [a, sub_apply, map_sub]
    abel
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

/-- In the complex coordinate `e = Complex.equivRealProdCLM`, the difference of two solutions of the
coordinate Floer equation on `Ω` obeys the Cauchy–Riemann inequality for the structure
`J(e w, u (e w))` near its zeros in `e ⁻¹' Ω`, with the regularity the unique continuation
theorems for differential inequalities ask for. -/
private theorem complexCoordinate (hΩ : IsOpen Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (z, u z))
    (hJJ : ∀ z ∈ Ω, J (z, u z) ∘L J (z, u z) = -ContinuousLinearMap.id ℝ F)
    (hX : ∀ z ∈ Ω, ContDiffAt ℝ 1 X (z, u z)) (hu : ContDiffOn ℝ 1 u Ω)
    (hv : ContDiffOn ℝ 1 v Ω)
    (hFu : ∀ z ∈ Ω, fderiv ℝ u z stdComplexLineImag - X (z, u z) stdComplexLineImag =
      J (z, u z) (fderiv ℝ u z stdComplexLineReal - X (z, u z) stdComplexLineReal))
    (hFv : ∀ z ∈ Ω, fderiv ℝ v z stdComplexLineImag - X (z, v z) stdComplexLineImag =
      J (z, v z) (fderiv ℝ v z stdComplexLineReal - X (z, v z) stdComplexLineReal)) :
    let e := Complex.equivRealProdCLM
    ContDiffOn ℝ 1 (fun w ↦ J (e w, u (e w))) (e ⁻¹' Ω) ∧
      ContDiffOn ℝ 1 ((u - v) ∘ e) (e ⁻¹' Ω) ∧
      ∀ w ∈ e ⁻¹' Ω, ((u - v) ∘ e) w = 0 → ∃ M, ∀ᶠ w' in 𝓝 w, ‖fderiv ℝ ((u - v) ∘ e) w' 1 +
        J (e w', u (e w')) (fderiv ℝ ((u - v) ∘ e) w' I)‖ ≤ M * ‖((u - v) ∘ e) w'‖ := by
  intro e
  refine ⟨(contDiffOn_comp_graph (J := fun z x ↦ J (z, x)) hJ hu).comp_continuousLinearMap
      (e : ℂ →L[ℝ] ℝ × ℝ), (hu.sub hv).comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ),
    fun w hw h ↦ ?_⟩
  obtain ⟨M, hM⟩ := exists_eventually_norm_le_of_fderiv_stdComplexLineImag_sub hΩ hw
    (hJ _ hw) (hX _ hw) hJJ hu hv hFu hFv (sub_eq_zero.1 h)
  refine ⟨M, (e.continuous.tendsto w).eventually hM |>.mono fun w' hw' ↦ ?_⟩
  rwa [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, comp_apply]

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
  obtain ⟨hJ', hξ', hb⟩ := complexCoordinate hΩ hJ hJJ hX hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  have h : EqOn (u - v) 0 Ω :=
    (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le (hΩ.preimage e.continuous)
      ((e.toHomeomorph.isPreconnected_preimage).2 hΩc) hJ' (fun w hw ↦ hJJ (e w) hw) hξ' hb
      (hU.preimage e.continuous) ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ)
      fun w hw ↦ sub_eq_zero.2 (h₀ hw)).cancel_right e.surjective.surjOn_preimage
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
  obtain ⟨hJ', hξ', hb⟩ := complexCoordinate hΩ hJ hJJ hX hu hv hFu hFv
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, hne₁⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le
    (hΩ.preimage e.continuous) ((e.toHomeomorph.isPreconnected_preimage).2 hΩc) hJ'
    (fun w hw ↦ hJJ (e w) hw) hξ' hb
    ⟨e.symm z₁, by simpa using hz₁, by simpa [sub_eq_zero] using hne₁⟩
  simpa only [Pi.sub_apply, ne_eq, sub_eq_zero] using
    (e.toHomeomorph.preimage_mem_codiscreteWithin (s := {z | (u - v) z ≠ 0})).1 h

end TauCeti.Floer

/-! ### Floer solutions in a manifold -/

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] {ω : SmoothTwoForm I M}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {Ks Kt : ℝ × ℝ → M → ℝ}
  {u : ℝ × ℝ → M} {Ω : Set (ℝ × ℝ)}

/-- A Floer solution in a chart solves the coordinate Floer equation. Let `u` be `C¹` on an
open set `Ω` and solve the Floer equation there, let `J` and the Hamiltonian vector fields of `K_s`
and `K_t` read in the chart at `α` be `C¹` on `Ω × (extChartAt I α).target`, and let `u` map an
open subset `B ⊆ Ω` into the chart source. On `B`, the coordinate expression
`extChartAt I α ∘ u` is `C¹` and solves the coordinate Floer equation for the structure and the
Hamiltonian one-form read in the chart, these data are `C¹` along its graph, and the structure
squares to `-1` along it. -/
private theorem contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub_of_contDiffOn
    (ω : SmoothTwoForm I M) {α : M} (hΩ : IsOpen Ω)
    (hJ : ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α J) (Ω ×ˢ (extChartAt I α).target))
    (hXs : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (Ω ×ˢ (extChartAt I α).target))
    (hXt : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (Ω ×ˢ (extChartAt I α).target))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Ω)
    (hFu : ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap)
    {B : Set (ℝ × ℝ)} (hBΩ : B ⊆ Ω) (huB : MapsTo u B (extChartAt I α).source) :
    ContDiffOn ℝ 1 (extChartAt I α ∘ u) B ∧
      (∀ z ∈ B, ContDiffAt ℝ 1 (Floer.almostComplexInChartAt I α J)
        (z, (extChartAt I α ∘ u) z)) ∧
      (∀ z ∈ B, ContDiffAt ℝ 1 (ω.hamiltonianOneFormInChartAt α Ks Kt)
        (z, (extChartAt I α ∘ u) z)) ∧
      (∀ z ∈ B, Floer.almostComplexInChartAt I α J (z, (extChartAt I α ∘ u) z) ∘L
        Floer.almostComplexInChartAt I α J (z, (extChartAt I α ∘ u) z) =
          -ContinuousLinearMap.id ℝ E) ∧
      ∀ z ∈ B, fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag -
          ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ u) z)
            stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z, (extChartAt I α ∘ u) z)
          (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
            ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ u) z)
              stdComplexLineReal) := by
  have hT : IsOpen (Ω ×ˢ (extChartAt I α).target) := hΩ.prod (isOpen_extChartAt_target α)
  have hmem {z : ℝ × ℝ} (hz : z ∈ B) :
      (z, (extChartAt I α ∘ u) z) ∈ Ω ×ˢ (extChartAt I α).target :=
    ⟨hBΩ hz, (extChartAt I α).map_source (huB hz)⟩
  refine ⟨contMDiffOn_iff_contDiffOn.1 <| (contMDiffOn_extChartAt (n := 1)).comp (hu.mono hBΩ)
      fun z hz ↦ by rw [mem_preimage, ← extChartAt_source I]; exact huB hz,
    fun z hz ↦ hJ.contDiffAt (hT.mem_nhds (hmem hz)),
    fun z hz ↦
      (contDiffOn_hamiltonianOneFormInChartAt hXs hXt).contDiffAt (hT.mem_nhds (hmem hz)),
    fun z hz ↦ ContinuousLinearMap.ext fun w ↦ ?_, fun z hz ↦ ?_⟩
  · simpa using Floer.almostComplexInChartAt_apply_apply (J := J)
      ((extChartAt I α).map_source (huB hz)) z w
  · simpa only [hamiltonianOneFormInChartAt_stdComplexLineReal,
      hamiltonianOneFormInChartAt_stdComplexLineImag, Function.comp_apply] using
      (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
        ((hu.mdifferentiableOn one_ne_zero).mdifferentiableAt (hΩ.mem_nhds (hBΩ hz)))
        (huB hz)).1 (hFu z (hBΩ hz))

variable [T2Space M] {v : ℝ × ℝ → M}

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [T2Space M] in
/-- Around a coincidence `u z₀ = v z₀` of two maps continuous on an open set `Ω`, some disc in `Ω`
is mapped by both into the source of the chart at `u z₀`. -/
private theorem exists_ball_subset_mapsTo_extChartAt_source (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω)
    (h : u z₀ = v z₀) :
    ∃ r > 0, Metric.ball z₀ r ⊆ Ω ∧ MapsTo u (Metric.ball z₀ r) (extChartAt I (u z₀)).source ∧
      MapsTo v (Metric.ball z₀ r) (extChartAt I (u z₀)).source := by
  have hW : IsOpen (Ω ∩ u ⁻¹' (extChartAt I (u z₀)).source ∩ v ⁻¹' (extChartAt I (u z₀)).source) :=
    (hv.mono inter_subset_left).isOpen_inter_preimage
      (hu.isOpen_inter_preimage hΩ (isOpen_extChartAt_source _)) (isOpen_extChartAt_source _)
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW z₀
    ⟨⟨hz₀, mem_extChartAt_source _⟩, by rw [mem_preimage, ← h]; exact mem_extChartAt_source _⟩
  exact ⟨r, hr, fun z hz ↦ (hrW hz).1.1, fun z hz ↦ (hrW hz).1.2, fun z hz ↦ (hrW hz).2⟩

/-- **Unique continuation for Floer solutions in a manifold.** Let `M` be a boundaryless Hausdorff
manifold with a two-form `ω`, and let `J` and the Hamiltonian vector fields of `K_s` and `K_t`, read
in every chart of `M`, be `C¹` over a connected open set `Ω ⊆ ℝ × ℝ`. Two `C¹` solutions `u`, `v`
of the Floer equation `(du - X_K)^{0,1} = 0` on `Ω` which agree on a nonempty open subset of `Ω`
agree on `Ω`. -/
theorem eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ α, ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α J)
      (Ω ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (Ω ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (Ω ×ˢ (extChartAt I α).target))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Ω) (hv : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω)
    (hFu : ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap)
    (hFv : ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
      (ω.perturbedMFDeriv Ks Kt v z).toLinearMap)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn u v U) :
    EqOn u v Ω := by
  -- The set `S` of points near which `u` and `v` agree is open, meets `Ω`, and is closed in `Ω`.
  set S := {z | u =ᶠ[𝓝 z] v}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  obtain ⟨z₁, hz₁⟩ := hUne
  suffices hΩS : Ω ⊆ S from fun z hz ↦ (hΩS hz).eq_of_nhds
  refine hΩc.subset_of_closure_inter_subset hSo
    ⟨z₁, hUΩ hz₁, Filter.mem_of_superset (hU.mem_nhds hz₁) fun _ hz ↦ h₀ hz⟩ ?_
  rintro z₀ ⟨hz₀S, hz₀Ω⟩
  have hΩz₀ := hΩ.mem_nhds hz₀Ω
  -- At a limit point of `S` the two maps agree, since `M` is Hausdorff.
  have heq : u z₀ = v z₀ := by
    have : (𝓝[S] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz₀S
    exact tendsto_nhds_unique
      ((hu.continuousOn.continuousAt hΩz₀).tendsto.mono_left (nhdsWithin_le_nhds (s := S)))
      (((hv.continuousOn.continuousAt hΩz₀).tendsto.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun z (hz : z ∈ S) ↦
          (show u =ᶠ[𝓝 z] v from hz).eq_of_nhds.symm))
  -- On a disc `B` around `z₀` both maps take values in the chart at `u z₀`, and their coordinate
  -- expressions solve the coordinate Floer equation and agree on `B ∩ S`.
  obtain ⟨r, hr, hBΩ, huB, hvB⟩ :=
    exists_ball_subset_mapsTo_extChartAt_source (I := I) hΩ hu.continuousOn hv.continuousOn hz₀Ω heq
  obtain ⟨hu', hJ', hX', hJJ', hFu'⟩ :=
    contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub_of_contDiffOn ω hΩ (hJ _)
      (hXs _) (hXt _) hu hFu hBΩ huB
  obtain ⟨hv', -, -, -, hFv'⟩ :=
    contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub_of_contDiffOn ω hΩ (hJ _)
      (hXs _) (hXt _) hv hFv hBΩ hvB
  have hcoord := Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn Metric.isOpen_ball
    (convex_ball z₀ r).isPreconnected hJ' hJJ' hX' hu' hv' hFu' hFv'
    (Metric.isOpen_ball.inter hSo)
    (mem_closure_iff_nhds.1 hz₀S _ (Metric.ball_mem_nhds z₀ hr)) inter_subset_left
    fun z hz ↦ by simp [(show u =ᶠ[𝓝 z] v from hz.2).eq_of_nhds]
  -- The chart is injective on its source, so `u = v` on `B`.
  exact Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hr) fun z hz ↦
    (extChartAt I (u z₀)).injOn (huB hz) (hvB hz) (hcoord hz)

/-- **Isolated coincidences of Floer solutions in a manifold.** Let `M` be a boundaryless Hausdorff
manifold with a two-form `ω`, and let `J` and the Hamiltonian vector fields of `K_s` and `K_t`, read
in every chart of `M`, be `C¹` over a connected open set `Ω ⊆ ℝ × ℝ`. If two `C¹` solutions `u`,
`v` of the Floer equation `(du - X_K)^{0,1} = 0` on `Ω` differ somewhere in `Ω`, the points of `Ω`
where they agree form a discrete subset of `Ω`. -/
theorem setOf_ne_mem_codiscreteWithin_of_isComplexLinearMap_perturbedMFDeriv (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω)
    (hJ : ∀ α, ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α J)
      (Ω ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (Ω ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (Ω ×ˢ (extChartAt I α).target))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u Ω) (hv : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω)
    (hFu : ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap)
    (hFv : ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
      (ω.perturbedMFDeriv Ks Kt v z).toLinearMap)
    (hne : ∃ z ∈ Ω, u z ≠ v z) : {z | u z ≠ v z} ∈ codiscreteWithin Ω := by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z₀ hz₀ ↦ ?_
  have hΩz₀ := hΩ.mem_nhds hz₀
  by_cases heq : u z₀ = v z₀
  swap
  · -- Away from a coincidence the two maps differ nearby, since `M` is Hausdorff.
    exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
      (((hu.continuousOn.continuousAt hΩz₀).ne_iff_eventually_ne
        (hv.continuousOn.continuousAt hΩz₀)).1 heq)
      fun z hz ↦ Or.inl hz)
  -- On a disc `B` around a coincidence both maps take values in the chart at `u z₀`.
  obtain ⟨r, hr, hBΩ, huB, hvB⟩ :=
    exists_ball_subset_mapsTo_extChartAt_source (I := I) hΩ hu.continuousOn hv.continuousOn hz₀ heq
  obtain ⟨hu', hJ', hX', hJJ', hFu'⟩ :=
    contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub_of_contDiffOn ω hΩ (hJ _)
      (hXs _) (hXt _) hu hFu hBΩ huB
  obtain ⟨hv', -, -, -, hFv'⟩ :=
    contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub_of_contDiffOn ω hΩ (hJ _)
      (hXs _) (hXt _) hv hFv hBΩ hvB
  -- If the coordinate expressions agreed on all of `B`, so would `u` and `v`, and then they would
  -- agree on all of `Ω`.
  have hne' :
      ∃ z ∈ Metric.ball z₀ r, (extChartAt I (u z₀) ∘ u) z ≠ (extChartAt I (u z₀) ∘ v) z := by
    by_contra! h
    obtain ⟨z₁, hz₁, hne₁⟩ := hne
    exact hne₁ (eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn hΩ hΩc hJ hXs hXt hu hv hFu
      hFv Metric.isOpen_ball ⟨z₀, Metric.mem_ball_self hr⟩ hBΩ
      (fun z hz ↦ (extChartAt I (u z₀)).injOn (huB hz) (hvB hz) (h z hz)) hz₁)
  have hcoord := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1
    (Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub Metric.isOpen_ball
      (convex_ball z₀ r).isPreconnected hJ' hJJ' hX' hu' hv' hFu' hFv' hne') z₀
      (Metric.mem_ball_self hr)
  -- Inside `B`, distinct coordinate expressions come from distinct points of `M`.
  filter_upwards [hcoord, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hr)]
    with z hz hzB
  exact Or.inl fun h ↦ (hz.resolve_right (not_not.2 hzB)) (by simp [h])

/-- **A Floer trajectory in a manifold agreeing with a translate on an open set is periodic.** Let
`u` be a `C¹` solution on `ℝ × ℝ` of the Floer equation `(du - X_H)^{0,1} = 0` in a boundaryless
Hausdorff manifold `M`, for the cylindrical perturbation `K = H_t dt` and an `s`-independent family
`J_t`, both `C¹` when read in every chart. If `u(s + c, t) = u(s, t)` on a nonempty open set, then
`u(s + c, t) = u(s, t)` everywhere. -/
theorem periodic_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {H : ℝ → M → ℝ}
    (hJ : ∀ α, ContDiffOn ℝ 1 (Floer.almostComplexInChartAt I α fun z : ℝ × ℝ ↦ J z.2)
      (univ ×ˢ (extChartAt I α).target))
    (hH : ∀ α, ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α fun z : ℝ × ℝ ↦ H z.2)
      (univ ×ˢ (extChartAt I α).target))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hF : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u z))
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun z ↦ H z.2) u z).toLinearMap)
    {c : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUc : EqOn u (fun z ↦ u (z + (c, 0))) U) : Periodic u (c, 0) := by
  -- The translate solves the same equation, because the data do not depend on `s`.
  have hFc (z : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z.2 (u (z + (c, 0)))) (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun z ↦ H z.2)
        (fun w ↦ u (w + (c, 0))) z).toLinearMap := by
    have h := ω.perturbedMFDeriv_comp_add_right (fun _ _ ↦ 0) (fun z ↦ H z.2) u (c, 0) z
    simp only [Prod.snd_add, add_zero] at h
    have hz : (z + (c, 0)).2 = z.2 := by simp
    rw [h, ← hz]
    exact hF (z + (c, 0))
  have hXs (α : M) : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α
      fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) (univ ×ˢ (extChartAt I α).target) := by
    rw [hamiltonianVectorFieldInChartAt_zero]
    exact contDiff_zero_fun.contDiffOn
  intro z
  exact (eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn isOpen_univ isPreconnected_univ hJ
    hXs hH hu.contMDiffOn (hu.comp (contDiff_id.add contDiff_const).contMDiff).contMDiffOn
    (fun z _ ↦ hF z) (fun z _ ↦ hFc z) hU hUne (subset_univ U) hUc (mem_univ z)).symm

end TauCeti.SmoothTwoForm
