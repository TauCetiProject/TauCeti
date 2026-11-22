/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Limit
public import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of Floer solutions in a chart of a manifold

Let `ω` be a nondegenerate two-form on a manifold `M` with finite-dimensional model space `E`,
such as a closed symplectic manifold, and let `u : ℝ × ℝ → M` solve the Floer equation
`(du - X_K)^{0,1} = 0` for a perturbation `K = K_s ds + K_t dt` and domain-dependent almost
complex structures `J(z, x)` on the tangent spaces of `M`. Gromov–Floer compactness for such a
target is local in the target: where the derivatives of a sequence of solutions are bounded, small
pieces of the solutions stay in a single chart, and there they solve a coordinate Floer equation
to which the compactness theorem of `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`
applies. The Floer equation read in the chart at a point `α` is
`TauCeti.Geometry.Symplectic.Floer.Chart`: a solution `u` with values in the chart source has a
coordinate expression `v = extChartAt I α ∘ u` solving `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})`, with
`J` and the Hamiltonian vector fields read in the chart (in the namespace `TauCeti.SmoothTwoForm`,
`isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub`). This file
proves the compactness theorem for solutions with values in one chart, both for a chart of the
atlas, which needs no closedness of `ω` and no inner product on `E`, and for a symplectic chart.

## Charts of the atlas

* The Floer energy density of a solution `u` is `ω(a, J a)` read in the chart, for the chart
  coordinate `a = ∂ₛv - X_{K_s}` of `∂ₛu - X_{K_s}`
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_eq_inChartAt`).
* A `C³` solution on an open set with values in the chart source has a `C³` coordinate expression
  solving the coordinate Floer equation for the Hamiltonian one-form read in the chart
  (`TauCeti.SmoothTwoForm.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub`), and its
  energy density is nonnegative where `J` is tamed by `ω`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_nonneg_of_tames_inChartAt`).
* In the chart, `ω(·, J ·)` is a continuous family of bilinear forms on `E`, positive when `J` is
  tamed by `ω`, hence uniformly coercive and bounded on a compact window: `c ‖ξ‖² ≤ ω(a, J a) ≤
  C ‖ξ‖²` for tangent vectors `a` with tangent coordinate `ξ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_sq_le_eval₂_le_mul_norm_sq`).
  So the intrinsic Floer energy density `ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` controls `‖∂ₛv‖²` up to
  an additive constant
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le`).
  Conversely, `‖∂ₛv‖²` controls the energy density up to constants, without taming
  (`TauCeti.SmoothTwoForm.exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq`).
  With the coordinate Floer equation for `∂ₜv`, a bound on the energy density bounds the whole
  derivative of `v`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_le`).
* **Compactness in a chart** (in the namespace `TauCeti.SmoothTwoForm`,
  `IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_extChartAt_subseq_off_finset`):
  a sequence of `C³` solutions with values in the chart source, chart coordinates in a compact set
  `K` and bounded Floer energy has a subsequence whose coordinate expressions converge locally
  uniformly off a finite set `Z` of bubbling points, with derivatives bounded on compact subsets
  of the complement and Floer energy at least a fixed `δ > 0` concentrating at each point of `Z`.
  The solutions themselves converge pointwise off `Z` in `M`.
* **The energy over a window** (in the namespace `TauCeti.SmoothTwoForm`,
  `integrableOn_and_setIntegral_floerEnergyDensity_le`): a bound on the energy over an open set
  `S` bounds the Bochner integral of a nonnegative energy density over every measurable `Ω ⊆ S`,
  which is the form of an energy bound the compactness theorems take.

The coordinate compactness theorem for a finite-dimensional normed target (in the namespace
`TauCeti.Floer`,
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm_sq_le_of_finiteDimensional`)
applies to the chart coordinates; so no inner product on `E` is needed. The conclusions are stated
in the chart coordinates, where locally uniform convergence and bounds on derivatives have a meaning
without a metric on `M`. Covering a domain by such chart pieces, the bubbles at the points of `Z`
and breaking along cylindrical ends are not treated here.

## Symplectic charts

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `φ : M ⊇ U → V` be a symplectic chart: a smooth partial
diffeomorphism onto an open subset of a finite-dimensional inner product space `V` carrying a
constant symplectic form `ω₀`, with `ω_x(v, w) = ω₀(dφ_x v, dφ_x w)` on its source. Darboux's
theorem (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) supplies such a chart around
every point of a boundaryless symplectic manifold whose model space is an inner product space.

In a symplectic chart, the compactness theorem for Floer solutions of bounded energy in a
symplectic vector space,
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`, transfers
to solutions `u : ℝ × ℝ → M` of the Floer equation `(du - X_K)^{0,1} = 0` in `M` whose image stays
in a compact subset `C` of the source of a symplectic chart, in the namespace
`TauCeti.SmoothTwoForm`:
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`.
The data are read in the chart: the Hamiltonians are `K'(z, y) = K(z, φ⁻¹ y)`, and the almost
complex structures are any family `J'(z, y)` on `V` with `dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x`.
The regularity hypotheses, `C³` for `K'` and `C²` for `J'`, are those of the vector-space theorem
for this coordinate data. If `K` is `C³` on `Ω' × M` for an open set `Ω'` of the domain, then `K'`
is `C³` on `Ω' × φ.target`
(`PartialDiffeomorph.contDiffOn_comp_symm_of_contMDiffOn`). By
`TauCeti.Geometry.Symplectic.Floer.Chart`, the coordinate maps `φ ∘ u` solve the Floer equation
of `(V, ω₀)` for `K'` and `J'`, with the same energy density, and `J'` is tamed by `ω₀` where `J`
is tamed by `ω`. So a sequence of such solutions on an open subset
`Ω` of a compact window `D` of the domain, with Floer energy at most `A`, has a subsequence which
converges off a finite set `Z` of bubbling points: the coordinate maps converge locally uniformly
on `Ω \ Z` with locally bounded derivatives, the maps themselves converge pointwise in `M` to a
continuous limit with values in `C`, `#Z δ ≤ A` for a threshold `δ > 0` depending only on the
data, and at least the energy `δ` concentrates at every point of `Z`.
The theorems take the energy bound as an integrable density with bounded integral over `Ω`;
`TauCeti.SmoothTwoForm.integrableOn_and_setIntegral_floerEnergyDensity_le` derives it from a bound
on the energy over a larger open domain.

The same holds over a compact window `C` of parameters `p` in a real inner product space, for
perturbations `K_p` and structures `J_p` whose chart readings `K_p(z, φ⁻¹ y)` and `J'_p(z, y)` are
`C³` and `C²` jointly in `(p, z, y)`, as for the one-parameter families of Floer data on which the
continuation, unit and comparison homotopies are built. Along the subsequence the parameters
converge to some `p₀ ∈ C`
(`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`, from the
vector-space theorem
`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`).
The theorem for fixed data is the case of a one-point window. For a family of Hamiltonian data
on `X × (ℂ × M)` that is smooth jointly in the parameter, the domain point and the target point,
reparametrized by a `Cⁿ` map `P → X`, the chart reading is `Cⁿ` jointly in `(p, z, y)`
(`TauCeti.Floer.contDiffOn_comp_prodMap_equivRealProdCLM_symm_symm`).

For smooth solutions and fixed data the convergence holds in `C¹`
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`): the
derivatives of the coordinate maps converge locally uniformly on `Ω \ Z` as well, the limit is a
`C¹` solution of the Floer equation `(dv - X_K)^{0,1} = 0` on `Ω \ Z`, and its Floer energy over
`Ω \ Z` is at most `A`. Moreover every bubbling point carries an energy mass of at least `δ`, and
the energy of the limit together with the masses is at most `A`
(`IsNondegenerate.exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset`).
This is the coordinate theorem of `TauCeti.Geometry.Symplectic.Floer.Compactness.Limit` read back
through the chart, and the `C¹` statement is read off from it.

Here the image of the solutions is assumed to stay in a single chart. The mean-value inequality for
solutions in a chart is in `TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue`. Gromov–Floer
compactness on a closed manifold also needs the images of small discs of small energy to be
localized into charts; that step, and the compactness theorem without the single-chart assumption,
are in `TauCeti.Geometry.Symplectic.Floer.Compactness.Bubbling`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (inhomogeneous equations).
-/

public section

noncomputable section

section

open Bundle ContinuousLinearMap Filter MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

namespace SmoothTwoForm

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ} {α : M}

/-- **The symplectic form and the structure read in a chart.** At a coordinate `y` in the target
of the chart at `α`, the coordinate expression of `ω` on a vector `a` and its image under the
structure `J(z, ·)` read in the chart is `ω(a', J(z, x) a')`, at the point
`x = (extChartAt I α).symm y` and for the tangent vector `a'` at `x` with tangent coordinate `a`. -/
theorem inChartAt_apply_almostComplexInChartAt {P : Type*}
    {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)} (ω : SmoothTwoForm I M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (z : P) (a : E) :
    RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α y
        ![a, Floer.almostComplexInChartAt I α J (z, y) a] =
      SmoothBundleForm.eval₂ ω ((extChartAt I α).symm y)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) a)
        (J z ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) a)) :=
  (ω.associatedBilinFormInChartAt_apply_eq_inChartAt J (z, y) a a).symm.trans
    (ω.associatedBilinFormInChartAt_apply J z hy a a)

omit [FiniteDimensional ℝ E] in
/-- **The Floer energy density in a chart, for any differentiable map.** Let `u` be differentiable
at `z`, with `u z` in the source of the chart at `α`. Then its energy density at `z` is the
coordinate expression of `ω` at `extChartAt I α (u z)` on the chart coordinates
`∂ₛv(z) - X_{K_s}` and `∂ₜv(z) - X_{K_t}` of `∂ₛu - X_{K_s}` and `∂ₜu - X_{K_t}`, for
`v = extChartAt I α ∘ u`. No Floer equation is assumed. -/
theorem floerEnergyDensity_eq_inChartAt_sub (ω : SmoothTwoForm I M)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hus : u z ∈ (extChartAt I α).source) :
    ω.floerEnergyDensity Ks Kt u z =
      RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α (extChartAt I α (u z))
        ![fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
            ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)),
          fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag -
            ω.hamiltonianVectorFieldInChartAt α Kt (z, extChartAt I α (u z))] := by
  set T := trivializationAt E (TangentSpace I) α
  have hub : u z ∈ T.baseSet :=
    TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hus
  -- The chart coordinates of `∂ₛu - X_{K_s}` and `∂ₜu - X_{K_t}`.
  have hP (w : ℝ × ℝ) : T.symmL ℝ (u z) (fderiv ℝ (extChartAt I α ∘ u) z w -
      w.1 • ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)) -
      w.2 • ω.hamiltonianVectorFieldInChartAt α Kt (z, extChartAt I α (u z))) =
      ω.perturbedMFDeriv Ks Kt u z w := by
    rw [← ω.continuousLinearMapAt_perturbedMFDeriv_apply hu hus w,
      Trivialization.symmL_continuousLinearMapAt _ hub]
  have hPs := hP stdComplexLineReal
  have hPt := hP stdComplexLineImag
  simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd, zero_smul, one_smul, sub_zero] at hPs hPt
  rw [ω.inChartAt_apply_eq_eval₂ ((extChartAt I α).map_source hus), (extChartAt I α).left_inv hus,
    hPs, hPt, floerEnergyDensity_def]

/-- **The Floer energy density in a chart.** Let `u` be differentiable at `z`, with `u z` in the
source of the chart at `α`, and solve the Floer equation for `J(z, u z)` at `z`. Then its energy
density at `z` is `ω(a, J a)` read in the chart, where `a = ∂ₛv(z) - X_{K_s}` is the chart
coordinate of `∂ₛu - X_{K_s}` for `v = extChartAt I α ∘ u`. -/
theorem floerEnergyDensity_eq_inChartAt (ω : SmoothTwoForm I M)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hus : u z ∈ (extChartAt I α).source)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    ω.floerEnergyDensity Ks Kt u z =
      RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α (extChartAt I α (u z))
        ![fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
            ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)),
          Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z))
            (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
              ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)))] := by
  set T := trivializationAt E (TangentSpace I) α
  have hub : u z ∈ T.baseSet :=
    TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hus
  -- The chart coordinate of `∂ₛu - X_{K_s}`.
  have hPs : T.symmL ℝ (u z) (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
      ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z))) =
      ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal := by
    have hre := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hus
      stdComplexLineReal
    simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, zero_smul, one_smul,
      sub_zero] at hre
    rw [← hre, Trivialization.symmL_continuousLinearMapAt _ hub]
  have hPt := h.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe] at hPt
  rw [ω.inChartAt_apply_almostComplexInChartAt ((extChartAt I α).map_source hus),
    (extChartAt I α).left_inv hus, hPs, floerEnergyDensity_def, hPt]

/-- **Floer solutions in a chart solve the coordinate Floer equation.** Let `u` be `C³` on an open
set `U`, with values in the source of the chart at `α`, and solve the Floer equation for `J(z, u)`
on `U`. Then its coordinate expression `v = extChartAt I α ∘ u` is `C³` on `U` and solves the
coordinate Floer equation `∂ₜv - X(z, v) i = J(z, v) (∂ₛv - X(z, v) 1)` on `U`, for the structure
`J` and the Hamiltonian one-form `X` of `K_s ds + K_t dt` read in the chart. -/
theorem contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub (ω : SmoothTwoForm I M)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hus : MapsTo u U (extChartAt I α).source)
    (hfl : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    ContDiffOn ℝ 3 (extChartAt I α ∘ u) U ∧ ∀ z ∈ U,
      fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag -
          ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ u) z) stdComplexLineImag =
        Floer.almostComplexInChartAt I α J (z, (extChartAt I α ∘ u) z)
          (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
            ω.hamiltonianOneFormInChartAt α Ks Kt (z, (extChartAt I α ∘ u) z)
              stdComplexLineReal) := by
  refine ⟨contMDiffOn_iff_contDiffOn.1 <| (contMDiffOn_extChartAt (n := 3)).comp hu
    fun z hz ↦ by rw [mem_preimage, ← extChartAt_source I]; exact hus hz, fun z hz ↦ ?_⟩
  simpa only [hamiltonianOneFormInChartAt_stdComplexLineReal,
    hamiltonianOneFormInChartAt_stdComplexLineImag, Function.comp_apply] using
    (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
      ((hu.mdifferentiableOn (by norm_num)).mdifferentiableAt (hU.mem_nhds hz)) (hus hz)).1
      (hfl z hz)

omit [FiniteDimensional ℝ E] in
/-- **The Floer energy density is nonnegative where `J` is tamed in a chart.** Let `J(z, x)` be
tamed by `ω` at the points `x` with chart coordinates in `K`, for `z ∈ D`. A solution `u` of the
Floer equation for `J(z, u)` at `z ∈ D`, with `u z` in the source of the chart at `α` and chart
coordinate in `K`, has nonnegative Floer energy density at `z`. -/
theorem IsNondegenerate.floerEnergyDensity_nonneg_of_tames_inChartAt (hω : ω.IsNondegenerate)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {D : Set (ℝ × ℝ)}
    {K : Set E} (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y)))
    (hz : z ∈ D) (hus : u z ∈ (extChartAt I α).source) (huK : extChartAt I α (u z) ∈ K)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z := by
  have hJ := hJt z hz _ huK
  rw [(extChartAt I α).left_inv hus] at hJ
  exact floerEnergyDensity_nonneg hω hJ h

/-- **The energy form is comparable to the chart norm, uniformly on a compact window.** Let the
structures `J(z, x)` be tamed by `ω` and, read in the chart at `α`, continuous on `D × K`, for a
compact set `D` of parameters, such as a compact window of the domain `ℝ × ℝ` or a compact family
of almost complex structures, and a compact set `K` of chart coordinates. There are constants
`c > 0` and `C` such that at every point `x` with chart coordinate `y ∈ K`, and for every `z ∈ D`,
the energy form `ω_x(a, J(z, x) a)` of the tangent vector `a` with tangent coordinate `ξ` in the
chart at `α` satisfies `c ‖ξ‖² ≤ ω_x(a, J(z, x) a) ≤ C ‖ξ‖²`. -/
theorem IsNondegenerate.exists_pos_forall_mul_norm_sq_le_eval₂_le_mul_norm_sq {P : Type*}
    [TopologicalSpace P] {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hω : ω.IsNondegenerate) (α : M) {D : Set P} {K : Set E} (hD : IsCompact D)
    (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (D ×ˢ K))
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) :
    ∃ c > 0, ∃ C, ∀ z ∈ D, ∀ y ∈ K, ∀ ξ : E,
      c * ‖ξ‖ ^ 2 ≤ SmoothBundleForm.eval₂ ω ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) ξ)
          (J z ((extChartAt I α).symm y)
            ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) ξ)) ∧
        SmoothBundleForm.eval₂ ω ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) ξ)
          (J z ((extChartAt I α).symm y)
            ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) ξ)) ≤
          C * ‖ξ‖ ^ 2 := by
  set e := extChartAt I α
  set T := trivializationAt E (TangentSpace I) α
  have hDK : IsCompact (D ×ˢ K) := hD.prod hK
  have hbase {y : E} (hy : y ∈ e.target) : e.symm y ∈ T.baseSet :=
    TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hy
  -- In the chart, `ω(·, J ·)` is the bilinear form `b`, continuous and positive on `D × K`.
  set b := ω.associatedBilinFormInChartAt α J
  have hb : ∀ p ∈ D ×ˢ K, ∀ a, b p a a = SmoothBundleForm.eval₂ ω (e.symm p.2)
      (T.symmL ℝ (e.symm p.2) a) (J p.1 (e.symm p.2) (T.symmL ℝ (e.symm p.2) a)) :=
    fun p hp a ↦ ω.associatedBilinFormInChartAt_apply J p.1 (hKα hp.2) a a
  have hbc : ContinuousOn b (D ×ˢ K) :=
    continuousOn_associatedBilinFormInChartAt (fun p hp ↦ hKα hp.2) hJ
  obtain ⟨c, hc, hcb⟩ := hDK.exists_pos_forall_mul_norm_sq_le hbc fun p hp a ha ↦ by
    rw [hb p hp]
    have hy : p.2 ∈ e.target := hKα hp.2
    have hSa : T.symmL ℝ (e.symm p.2) a ≠ 0 := fun h0 ↦ ha <| by
      rw [← Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ (hbase hy) a, h0, map_zero]
    simpa only [IsNondegenerate.symplecticFormAt_apply] using hJt p.1 hp.1 p.2 hp.2 _ hSa
  obtain ⟨C, hC⟩ := hDK.exists_forall_le_mul_norm_sq hbc
  exact ⟨c, hc, C, fun z hz y hy ξ ↦ ⟨(hb (z, y) ⟨hz, hy⟩ ξ) ▸ hcb _ ⟨hz, hy⟩ ξ,
    (hb (z, y) ⟨hz, hy⟩ ξ) ▸ hC _ ⟨hz, hy⟩ ξ⟩⟩

/-- **The energy density bounds the derivative in a chart, uniformly on a compact window.** Let
the structures `J(z, x)` be tamed by `ω` and, read in the chart at `α`, continuous on `D × K`,
together with the Hamiltonian vector field of `K_s`, for compact `D ⊆ ℝ × ℝ` and a compact set `K`
of chart coordinates. There are constants `A, B ≥ 0` such that every solution `u` of the Floer
equation for `J(z, u)` at a point `z ∈ D`, with `u z` in the chart source and coordinate in `K`,
satisfies `‖∂ₛv(z)‖² ≤ A ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) + B` for its coordinate expression
`v = extChartAt I α ∘ u`. -/
theorem IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le
    (hω : ω.IsNondegenerate) (α : M) {D : Set (ℝ × ℝ)} {K : Set E} (hD : IsCompact D)
    (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (D ×ˢ K))
    (hX : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks) (D ×ˢ K))
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ (extChartAt I α).source →
      extChartAt I α (u z) ∈ K → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 ≤
        A * ω.floerEnergyDensity Ks Kt u z + B := by
  set e := extChartAt I α
  obtain ⟨c, hc, _, hcb⟩ :=
    hω.exists_pos_forall_mul_norm_sq_le_eval₂_le_mul_norm_sq α hD hK hKα hJ hJt
  obtain ⟨B, hB⟩ := (hD.prod hK).exists_bound_of_continuousOn hX
  refine ⟨2 / c, by positivity, 2 * B ^ 2, by positivity, fun u z hz hus huK hu h ↦ ?_⟩
  have hp : (z, e (u z)) ∈ D ×ˢ K := ⟨hz, huK⟩
  -- The coordinate `a` of the perturbed derivative `∂ₛu - X_{K_s}` has `c ‖a‖² ≤ e(u)`.
  set Xs := ω.hamiltonianVectorFieldInChartAt α Ks (z, e (u z))
  set a := fderiv ℝ (e ∘ u) z stdComplexLineReal - Xs
  have hca : c * ‖a‖ ^ 2 ≤ ω.floerEnergyDensity Ks Kt u z := by
    refine (hcb z hz (e (u z)) huK a).1.trans_eq ?_
    rw [← ω.inChartAt_apply_almostComplexInChartAt (hKα huK) z a,
      ω.floerEnergyDensity_eq_inChartAt hu hus h]
  have hXB : ‖Xs‖ ≤ B := by simpa using hB _ hp
  refine (norm_sq_le_of_mul_norm_sub_sq_le hc hca).trans ?_
  gcongr

/-- **The derivative in a chart bounds the energy density, uniformly on a compact window.** Let
the structures `J(z, x)` and the Hamiltonian vector field of `K_s`, read in the chart at `α`, be
continuous on `D × K`, for compact `D ⊆ ℝ × ℝ` and a compact set `K` of chart coordinates. There are
constants `A, B ≥ 0` such that every solution `u` of the Floer equation for `J(z, u)` at a point
`z ∈ D`, with `u z` in the chart source and coordinate in `K`, satisfies
`ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) ≤ A ‖∂ₛv(z)‖² + B` for its coordinate expression
`v = extChartAt I α ∘ u`. This is the converse of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le`; it needs
no taming. -/
theorem exists_forall_floerEnergyDensity_le_norm_fderiv_extChartAt_comp_sq
    (ω : SmoothTwoForm I M) (α : M) {D : Set (ℝ × ℝ)} {K : Set E} (hD : IsCompact D)
    (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (D ×ˢ K))
    (hX : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks) (D ×ˢ K)) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ (extChartAt I α).source →
      extChartAt I α (u z) ∈ K → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ω.floerEnergyDensity Ks Kt u z ≤
        A * ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 + B := by
  have hDK : IsCompact (D ×ˢ K) := hD.prod hK
  -- Bounds for `ω`, `J` and `X_{K_s}` read in the chart, on `D × K`.
  obtain ⟨β₁, hβ₁⟩ := hDK.exists_bound_of_continuousOn
    ((ω.isSmoothForm.continuousOn_inChartAt α).comp continuousOn_snd fun p hp ↦ hKα hp.2)
  obtain ⟨β₂, hβ₂⟩ := hDK.exists_bound_of_continuousOn hJ
  obtain ⟨β₃, hβ₃⟩ := hDK.exists_bound_of_continuousOn hX
  set c := max β₁ 0 * max 1 β₂ ^ 2 with hc
  refine ⟨2 * c, by positivity, 2 * c * β₃ ^ 2, by positivity, fun u z hz hus huK hu h ↦ ?_⟩
  have hp : (z, extChartAt I α (u z)) ∈ D ×ˢ K := ⟨hz, huK⟩
  rw [ω.floerEnergyDensity_eq_inChartAt hu hus h]
  set a := fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
    ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)) with ha
  set f := RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α (extChartAt I α (u z))
  have hm : ‖![a, Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z)) a]‖ ≤
      max 1 β₂ * ‖a‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    fin_cases i
    · simpa using le_mul_of_one_le_left (norm_nonneg a) (le_max_left 1 β₂)
    · simpa using (le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((hβ₂ _ hp).trans (le_max_right _ _)) (norm_nonneg a))
  have hf : ‖f‖ ≤ max β₁ 0 := (hβ₁ _ hp).trans (le_max_left _ _)
  have hXb : ‖ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z))‖ ≤ β₃ := hβ₃ _ hp
  have ha2 : ‖a‖ ^ 2 ≤
      2 * ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 + 2 * β₃ ^ 2 := by
    have h1 := (norm_sub_le (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal)
      (ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)))).trans
      (add_le_add_right hXb _)
    rw [← ha] at h1
    nlinarith [norm_nonneg a, norm_nonneg (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal),
      sq_nonneg (‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ - β₃)]
  calc f ![a, Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z)) a]
      ≤ ‖f ![a, Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z)) a]‖ :=
        Real.le_norm_self _
    _ ≤ ‖f‖ * (max 1 β₂ * ‖a‖) ^ 2 :=
        ContinuousAlternatingMap.le_opNorm_mul_pow_of_le f hm
    _ ≤ max β₁ 0 * (max 1 β₂ * ‖a‖) ^ 2 := by gcongr
    _ = c * ‖a‖ ^ 2 := by rw [hc]; ring
    _ ≤ c * (2 * ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 + 2 * β₃ ^ 2) := by
        gcongr
    _ = 2 * c * ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ^ 2 + 2 * c * β₃ ^ 2 := by
        ring

/-- **A bound on the energy density bounds the derivative in a chart, uniformly on a compact
window.** Let the structures `J(z, x)` be tamed by `ω` and, read in the chart at `α`, continuous on
`D × K`, together with the Hamiltonian vector fields of `K_s` and `K_t`, for compact `D ⊆ ℝ × ℝ`
and a compact set `K` of chart coordinates. For every `A` there is a constant `L` such that every
solution `u` of the Floer equation for `J(z, u)` at a point `z ∈ D`, with `u z` in the chart source
and coordinate in `K`, whose Floer energy density at `z` is at most `A`, satisfies
`‖d(extChartAt I α ∘ u)(z)‖ ≤ L`. -/
theorem IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_le
    (hω : ω.IsNondegenerate) (α : M) {D : Set (ℝ × ℝ)} {K : Set E} (hD : IsCompact D)
    (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) (D ×ˢ K))
    (hXs : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks) (D ×ˢ K))
    (hXt : ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Kt) (D ×ˢ K))
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) (A : ℝ) :
    ∃ L, ∀ ⦃u : ℝ × ℝ → M⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ (extChartAt I α).source →
      extChartAt I α (u z) ∈ K → MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap →
      ω.floerEnergyDensity Ks Kt u z ≤ A → ‖fderiv ℝ (extChartAt I α ∘ u) z‖ ≤ L := by
  obtain ⟨A₁, hA₁, B₁, -, hpt⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α hD hK hKα hJ hXs hJt
  obtain ⟨βJ, hβJ⟩ := (hD.prod hK).exists_bound_of_continuousOn hJ
  obtain ⟨βs, hβs⟩ := (hD.prod hK).exists_bound_of_continuousOn hXs
  obtain ⟨βt, hβt⟩ := (hD.prod hK).exists_bound_of_continuousOn hXt
  set M₁ := 1 + (A₁ * A + B₁)
  refine ⟨M₁ + (βJ * (M₁ + βs) + βt), fun u z hz hus huK hu h hρ ↦ ?_⟩
  have hp : (z, extChartAt I α (u z)) ∈ D ×ˢ K := ⟨hz, huK⟩
  -- The derivative `∂ₛ` in the chart, from the energy density.
  have h1 : ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ ≤ M₁ := by
    have h2 := hpt hz hus huK hu h
    have h3 := mul_le_mul_of_nonneg_left hρ hA₁
    nlinarith [sq_nonneg (‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal‖ - 1)]
  -- The derivative `∂ₜ` in the chart, from the coordinate Floer equation.
  have h2 : ‖fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag‖ ≤ βJ * (M₁ + βs) + βt := by
    have heq :=
      (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp_stdComplexLineImag_sub
        hu hus).1 h
    rw [← sub_add_cancel (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag), heq]
    refine (norm_add_le _ _).trans (add_le_add ((le_opNorm _ _).trans ?_) (hβt _ hp))
    exact mul_le_mul (hβJ _ hp) ((norm_sub_le _ _).trans (add_le_add h1 (hβs _ hp)))
      (norm_nonneg _) ((norm_nonneg _).trans (hβJ _ hp))
  have h := (fderiv ℝ (extChartAt I α ∘ u) z).opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one
  rw [← stdComplexLineReal_eq, ← stdComplexLineImag_eq] at h
  exact h.trans (add_le_add h1 h2)

/-- **Floer solutions in a chart of a manifold converge off finitely many bubbling points.** Let
`ω` be a nondegenerate two-form on `M` and `α` a point of `M`. Let the structures `J(z, x)` and the
Hamiltonian vector fields of `K_s` and `K_t`, read in the chart at `α`, be `C²` on an open set
`W ⊆ (ℝ × ℝ) × E` containing `D × K`, for compact `D ⊆ ℝ × ℝ` and a compact set `K` of chart
coordinates, and let `J(z, x)` be tamed by `ω` on `D × K`. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` solutions of the Floer equation `(du - X_K)^{0,1} = 0` for
`J(z, u)` on an open set `Ω ⊆ D`, with values in the chart source and chart coordinates in `K`,
and with Floer energy `∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E₀`. Then there are a subsequence
`φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E₀`, and a continuous `v : Ω \ Z → K` such that along `φ`
every disc about a point of `Z` eventually carries Floer energy at least `δ`, the derivatives of
the coordinate expressions `extChartAt I α ∘ u_{φ n}` are uniformly bounded on every compact subset
of `Ω \ Z`, these coordinate expressions converge to `v` locally uniformly on `Ω \ Z`, and
`u_{φ n}` converges pointwise on `Ω \ Z` to `(extChartAt I α).symm ∘ v` in `M`. -/
theorem IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_extChartAt_subseq_off_finset
    (hω : ω.IsNondegenerate) (α : M) {W : Set ((ℝ × ℝ) × E)} {D : Set (ℝ × ℝ)} {K : Set E}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J) W)
    (hXs : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks) W)
    (hXt : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt) W)
    (hD : IsCompact D) (hK : IsCompact K) (hKα : K ⊆ (extChartAt I α).target)
    (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ y ∈ K, (hω.symplecticFormAt ((extChartAt I α).symm y)).Tames
      (J z ((extChartAt I α).symm y))) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω ((extChartAt I α).source ∩ extChartAt I α ⁻¹' K)) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → E), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ L, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (extChartAt I α ∘ u (φ n)) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) v atTop (Ω \ ↑Z) ∧
        ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 ((extChartAt I α).symm (v z))) := by
  set e := extChartAt I α
  obtain ⟨A, hA0, B, hB0, hpt⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α
    hD hK hKα (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW) hJt
  -- The coordinate expressions solve the coordinate Floer equation for `J` and `X_K` read in the
  -- chart, with derivatives controlled by the intrinsic energy density.
  open Floer in
  obtain ⟨δ, hδ, hconv⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm_sq_le_of_finiteDimensional
      hW hJ (contDiffOn_hamiltonianOneFormInChartAt hXs hXt) hD hK hDKW
      (fun z _ _ hy ↦ almostComplexInChartAt_apply_apply (hKα hy) z) hA0 hB0
  refine ⟨δ, hδ, fun Ω u E₀ hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  have hus (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : u k z ∈ e.source := (huK k hz).1
  have hdiff (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    ((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hz)
  have hchart (k : ℕ) := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub hΩ (hu k)
    (fun _ hz ↦ hus k hz) (hfl k)
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim⟩ :=
    hconv (u := fun k ↦ e ∘ u k) (f := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)) hΩ hΩD
      (fun k ↦ (hchart k).1) (fun k ↦ (hchart k).2) (fun k z hz ↦ (huK k hz).2)
      (fun k z hz ↦ hω.floerEnergyDensity_nonneg_of_tames_inChartAt hJt (hΩD hz) (hus k hz)
        (huK k hz).2 (hfl k z hz))
      (fun k z hz ↦ hpt (hΩD hz) (hus k hz) (huK k hz).2 (hdiff k hz) (hfl k z hz))
      hint hE
  refine ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim, fun z hz ↦ ?_⟩
  -- Pointwise convergence in `M` follows by applying the continuous inverse chart.
  have hcont := (continuousOn_extChartAt_symm α).continuousWithinAt (hKα (hvK hz))
  have h := hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim.tendsto_at hz,
    Eventually.of_forall fun n ↦ e.map_source (hus (φ n) hz.1)⟩)
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  exact e.left_inv (hus (φ n) hz.1)

omit [FiniteDimensional ℝ E] in
/-- **The Floer energy over a subdomain as a Bochner integral, for a manifold target.** Let `u` be
`C¹` on an open set `S ⊆ ℝ × ℝ`, let the Hamiltonian vector fields of `K = K_s ds + K_t dt` be
continuous on `S × M` as maps into the tangent bundle, and let `Ω ⊆ S` be measurable with Floer
energy density nonnegative on `Ω`. If the energy of `u` over `S` is at most `E ≥ 0`, then the
density is integrable on `Ω` and its integral over `Ω` is at most `E`. The vector-space case is
`TauCeti.SymplecticForm.integrableOn_and_setIntegral_floerEnergyDensity_le`. -/
theorem integrableOn_and_setIntegral_floerEnergyDensity_le (ω : SmoothTwoForm I M)
    {S Ω : Set (ℝ × ℝ)} (hS : IsOpen S) (hΩ : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u S)
    (hXs : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (S ×ˢ univ))
    (hXt : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (S ×ˢ univ))
    (hf0 : ∀ z ∈ Ω, 0 ≤ ω.floerEnergyDensity Ks Kt u z) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) ≤ ENNReal.ofReal E) :
    IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity Ks Kt u z ≤ E :=
  integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le
    (((ω.continuousOn_floerEnergyDensity hS hu hXs hXt).mono hΩS).aestronglyMeasurable hΩ)
    (ae_restrict_of_forall_mem hΩ hf0) hΩS hE0 hE

end SmoothTwoForm

end TauCeti

end

section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.Floer

/-- **Families of data read in a chart.** Let `F` be a family on `X × (ℂ × M)` which is `Cⁿ` at
the points `(a, (z, x))` with `z` in a set `S` (in real coordinates), such as the Hamiltonian data
of a family of Floer problems on `S`, smooth jointly in the family parameter, the domain point and
the target point. Read in a smooth partial diffeomorphism `φ : M ⊇ U → V` and reparametrized by a
`Cⁿ` map `g : P → X`, the family `(p, z, y) ↦ F (g p, (z, φ⁻¹ y))` is `Cⁿ` on `P × S × φ(U)`. -/
theorem contDiffOn_comp_prodMap_equivRealProdCLM_symm_symm {E H M V X P Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ∞} {F : X × (ℂ × M) → Y} {S : Set (ℝ × ℝ)}
    (hF : ∀ a, ∀ z ∈ S, ∀ x,
      ContMDiffAt (𝓘(ℝ, X).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, Y) n F
        (a, (Complex.equivRealProdCLM.symm z, x)))
    {g : P → X} (hg : ContDiff ℝ n g) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) :
    ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × V) ↦
      F (g q.1, (Complex.equivRealProdCLM.symm q.2.1, φ.symm q.2.2)))
      (univ ×ˢ (S ×ˢ φ.target)) := by
  have hm : ContMDiffOn 𝓘(ℝ, P × ((ℝ × ℝ) × V)) (𝓘(ℝ, X).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun q : P × ((ℝ × ℝ) × V) ↦ (g q.1, (Complex.equivRealProdCLM.symm q.2.1, φ.symm q.2.2)))
      (univ ×ˢ (univ ×ˢ φ.target)) :=
    (hg.comp contDiff_fst).contMDiff.contMDiffOn.prodMk
      ((Complex.equivRealProdCLM.symm.contDiff.comp
        (contDiff_fst.comp contDiff_snd)).contMDiff.contMDiffOn.prodMk
          ((φ.symm.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp
            (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn fun _ hq ↦ hq.2.2))
  rintro ⟨p, z, y⟩ ⟨-, hz, hy⟩
  have h := (hF (g p) z hz (φ.symm y)).comp_contMDiffWithinAt (p, (z, y))
    (hm _ ⟨trivial, trivial, hy⟩)
  exact (contMDiffWithinAt_iff_contDiffWithinAt.1 h).mono
    (prod_mono subset_rfl (prod_mono (subset_univ _) subset_rfl))

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {Ks Kt : ℝ × ℝ → M → ℝ}

/-- At a point `z` with `u z` in the source of a smooth partial diffeomorphism `φ` pulling `ω₀`
back to `ω` at `u z`, the coordinate map `φ ∘ u` has the energy density of `u`, and solves the
coordinate Floer equation for the structure `J'` read in the chart if `u` solves the Floer equation
for `J`. -/
private theorem floerEnergyDensity_comp_and_isComplexLinearMap (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hφ : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJJ' : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap)
    (hKs : DifferentiableAt ℝ (fun y ↦ Ks z (φ.symm y)) (φ (u z)))
    (hKt : DifferentiableAt ℝ (fun y ↦ Kt z (φ.symm y)) (φ (u z)))
    (hx : u z ∈ φ.source) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z =
        ω.floerEnergyDensity Ks Kt u z ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u)
          z).toLinearMap := by
  have hφx := φ.mdifferentiableAt (by simp) hx
  have hsurj := (φ.bijective_mvfderiv (by simp) hx).surjective
  -- Near `u z`, each Hamiltonian is its coordinate expression composed with `φ`.
  have hK₁ (K : ℝ × ℝ → M → ℝ) : K z =ᶠ[𝓝 (u z)] (fun y ↦ K z (φ.symm y)) ∘ φ :=
    (φ.toOpenPartialHomeomorph.eventually_left_inverse hx).mono fun y hy ↦
      congrArg (K z) hy.symm
  exact ⟨hω.floerEnergyDensity_comp hu hφx hsurj hφ (hK₁ Ks) (hK₁ Kt) hKs hKt,
    (hω.isComplexLinearMap_perturbedFDeriv_comp_iff hu hφx hsurj hφ (hK₁ Ks) (hK₁ Kt) hKs
      hKt hJJ').2 hfl⟩

variable {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **Floer solutions in a symplectic chart over a compact parameter window converge off finitely
many bubbling points.** Let `φ` be a smooth partial diffeomorphism from `M` onto an open subset of
`V`, and let `D ⊆ ℝ × ℝ` and `K ⊆ φ.source` be compact. Let the perturbations `K_p` and the
structures `J_p(z, x)` depend on a parameter `p` in a real inner product space `P`, and fix a
compact window `C ⊆ P` of parameters. Let `φ` pull the symplectic form `ω₀` back to the
nondegenerate form `ω` at the points of `K`, and let `J'_p` be the family `J_p` read in the chart,
`dφ_x ∘ J_p(z, x) = J'_p(z, φ x) ∘ dφ_x` for `p ∈ C`, `z ∈ D` and `x ∈ K`, with `J_p(z, x)` tamed by
`ω` there. Let the coordinate Hamiltonians `K_p(z, φ⁻¹ y)` be `C³` and `J'_p(z, y)` be `C²` jointly
in `(p, z, y)` on an open set `W` containing `C × D × φ(K)`. There is a threshold `δ > 0` with the
following property. Let `uₖ` be `C³` solutions of the Floer equation
`(du - X_{K_{pₖ}})^{0,1} = 0` for `J_{pₖ}(z, u)` on an open set `Ω ⊆ D`, for parameters `pₖ ∈ C`,
with image in `K` and Floer energy at most `A`. Then there are a subsequence `ψ`, a limit parameter
`p₀ ∈ C` of `p_{ψ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A`, and a map `v`, continuous on
`Ω \ Z` with values in `K`, such that along `ψ` every disc about a point of `Z` eventually carries
Floer energy at least `δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly
bounded on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally
uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (hω : ω.IsNondegenerate) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] {Ks Kt : P → ℝ × ℝ → M → ℝ}
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : P → ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set (P × ((ℝ × ℝ) × V))} {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K,
      IsComplexLinearMap (J p z x) (J' p z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ Ks q.1 q.2.1 (φ.symm q.2.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ Kt q.1 q.2.1 (φ.symm q.2.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hKφ : K ⊆ φ.source)
    (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) → (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ A) →
      ∃ (ψ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (ψ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω.floerEnergyDensity (Ks (p (ψ n))) (Kt (p (ψ n))) (u (ψ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ B, ∀ n, ∀ y ∈ L, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ B) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  have hφK : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hKφ)
  -- In the chart, `J'_p` is tamed by `ω₀` over `C × D × φ(K)`.
  have hJ't : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ φ '' K, ω₀.Tames (J' p z y) := by
    rintro p hp z hz _ ⟨x, hx, rfl⟩
    exact tames_of_isComplexLinearMap_mvfderiv hω
      (φ.bijective_mvfderiv (by simp) (hKφ hx)).surjective (hφ x hx) (hJJ' p hp z hz x hx)
      (hJt p hp z hz x hx)
  obtain ⟨δ, hδ, hconv⟩ := ω₀.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun p z y ↦ Ks p z (φ.symm y)) (Kt := fun p z y ↦ Kt p z (φ.symm y)) hW hKs hKt hJ' hC
    hD hφK hCDKW hJ't
  refine ⟨δ, hδ, fun Ω p u A hΩ hΩD hpC hu hfl huK hint hA ↦ ?_⟩
  -- The coordinate Hamiltonians are differentiable in the target variable on `W`.
  have hdiff {f : P × ((ℝ × ℝ) × V) → ℝ} (hf : ContDiffOn ℝ 3 f W) {q : P} {z : ℝ × ℝ} {y : V}
      (h : (q, (z, y)) ∈ W) : DifferentiableAt ℝ (fun y ↦ f (q, (z, y))) y :=
    DifferentiableAt.comp (g := f) (f := fun y : V ↦ (q, (z, y))) y
      (((hf.differentiableOn (by norm_num)) _ h).differentiableAt (hW.mem_nhds h))
      ((differentiableAt_const q).prodMk ((differentiableAt_const z).prodMk differentiableAt_id))
  -- At each point of `Ω`, the chart transports the Floer equation and the energy density.
  have hpt (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :=
    have hW' : (p k, (z, φ (u k z))) ∈ W := hCDKW ⟨hpC k, hΩD hz, u k z, huK k hz, rfl⟩
    floerEnergyDensity_comp_and_isComplexLinearMap hω φ (hφ _ (huK k hz))
      (hJJ' (p k) (hpC k) z (hΩD hz) _ (huK k hz)) (hdiff hKs hW') (hdiff hKt hW')
      (hKφ (huK k hz))
      (((hu k).contMDiffAt (hΩ.mem_nhds hz)).mdifferentiableAt (by norm_num)) (hfl k z hz)
  have hint_eq (k : ℕ) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
      ∫ y in S, ω₀.floerEnergyDensity (fun z y ↦ Ks (p k) z (φ.symm y))
        (fun z y ↦ Kt (p k) z (φ.symm y)) (φ ∘ u k) y =
        ∫ y in S, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) y :=
    setIntegral_congr_fun hS fun y hy ↦ (hpt k (hSΩ hy)).1
  obtain ⟨ψ, p₀, Z, w, hψ, hp₀, hplim, hZΩ, hcard, hconc, hbd, hwc, hwK, hlim⟩ :=
    hconv (u := fun k ↦ φ ∘ u k) hΩ hΩD hpC (fun k ↦ contMDiffOn_iff_contDiffOn.1 <|
      (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp (hu k)
        ((huK k).mono_right hKφ))
    (fun k z hz ↦ (hpt k hz).2) (fun k z hz ↦ ⟨u k z, huK k hz, rfl⟩)
    (fun k ↦ (hint k).congr_fun (fun y hy ↦ ((hpt k hy).1).symm) hΩ.measurableSet)
    (fun k ↦ (hint_eq k hΩ.measurableSet subset_rfl).trans_le (hA k))
  obtain ⟨hvc, hvK, hvlim, hvpt⟩ :=
    φ.toOpenPartialHomeomorph.tendsto_symm_of_tendstoLocallyUniformlyOn hKφ hwc hwK
      (fun n ↦ (huK (ψ n)).mono_left sdiff_subset) hlim
  refine ⟨ψ, p₀, Z, φ.symm ∘ w, hψ, hp₀, hplim, hZΩ, hcard, fun z hz ε hε ↦ ?_, hbd, hvc, hvK,
    hvlim, hvpt⟩
  filter_upwards [hconc z hz ε hε] with n hn
  rwa [hint_eq _ (measurableSet_ball.inter hΩ.measurableSet) inter_subset_right] at hn

/-- **Floer solutions of bounded energy in a symplectic chart converge off finitely many bubbling
points.** Let `φ` be a smooth partial diffeomorphism from `M` onto an open subset of `V`, and let
`D ⊆ ℝ × ℝ` and `C ⊆ φ.source` be compact. Let `φ` pull the symplectic form `ω₀` back to the
nondegenerate form `ω` at the points of `C`, let `J'` be the family `J` read in the chart,
`dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x` for `z ∈ D` and `x ∈ C`, with `J(z, x)` tamed by `ω` there.
Let the coordinate Hamiltonians `K(z, φ⁻¹ y)` be `C³` and `J'` be `C²` on an open set `W`
containing `D × φ(C)`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of the Floer equation
`(du - X_K)^{0,1} = 0` for `J(z, u)` on an open set `Ω ⊆ D`, with image in `C` and Floer energy
`∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ A`. Then there are a subsequence `ψ`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A`, and a map `v`, continuous on `Ω \ Z` with values in `C`, such that along
`ψ` every disc about a point of `Z` eventually carries Floer energy at least `δ`, the differentials
of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded on every compact subset of `Ω \ Z`, the
coordinate maps converge to `φ ∘ v` locally uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω C) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ A) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (ψ n)) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z →
          ∃ B, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ B) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  -- The case of the constant family over the one-point window `{0} ⊆ ℝ`.
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun _ : ℝ ↦ Ks) (Kt := fun _ ↦ Kt) (J := fun _ ↦ J) (J' := fun _ ↦ J')
    (W := univ ×ˢ W) (C := {0}) hφ (fun _ _ ↦ hJJ') (isOpen_univ.prod hW)
    (hKs.comp contDiffOn_snd fun _ hq ↦ hq.2) (hKt.comp contDiffOn_snd fun _ hq ↦ hq.2)
    (hJ'.comp contDiffOn_snd fun _ hq ↦ hq.2) isCompact_singleton hD hC hCφ
    (prod_mono (subset_univ _) hDCW) fun _ _ ↦ hJt
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu hfl huC hint hA ↦ ?_⟩
  obtain ⟨ψ, -, Z, v, hψ, -, -, h⟩ :=
    hconv (p := fun _ ↦ 0) hΩ hΩD (fun _ ↦ rfl) hu hfl huC hint hA
  exact ⟨ψ, Z, v, hψ, h⟩

/-- At a point `z` with `u z` in the source of a smooth partial diffeomorphism `φ` pulling `ω₀`
back to `ω` at `u z`, the coordinate map `φ ∘ u` has the energy density of `u`, and solves the
coordinate Floer equation for the structure `J'` read in the chart exactly when `u` solves the
Floer equation for `J`. -/
private theorem floerEnergyDensity_comp_and_isComplexLinearMap_iff (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hφ : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJJ' : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap)
    {W : Set ((ℝ × ℝ) × V)} (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hx : u z ∈ φ.source) (hzx : (z, φ (u z)) ∈ W) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z =
        ω.floerEnergyDensity Ks Kt u z ∧
      (IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u)
          z).toLinearMap ↔
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
          (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) := by
  have hφx := φ.mdifferentiableAt (by simp) hx
  have hsurj := (φ.bijective_mvfderiv (by simp) hx).surjective
  -- Near `u z`, each Hamiltonian is its coordinate expression composed with `φ`, and that
  -- expression is differentiable at `φ (u z)`.
  have hK₁ (K : ℝ × ℝ → M → ℝ) : K z =ᶠ[𝓝 (u z)] (fun y ↦ K z (φ.symm y)) ∘ φ :=
    (φ.toOpenPartialHomeomorph.eventually_left_inverse hx).mono fun y hy ↦
      congrArg (K z) hy.symm
  have hK₂ {K : ℝ × ℝ → M → ℝ}
      (hK : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ K p.1 (φ.symm p.2)) W) :
      DifferentiableAt ℝ (fun y ↦ K z (φ.symm y)) (φ (u z)) :=
    (((hK.differentiableOn (by norm_num)) _ hzx).differentiableAt (hW.mem_nhds hzx)).comp _
      ((differentiableAt_const z).prodMk differentiableAt_id)
  exact ⟨hω.floerEnergyDensity_comp hu hφx hsurj hφ (hK₁ Ks) (hK₁ Kt) (hK₂ hKs) (hK₂ hKt),
    hω.isComplexLinearMap_perturbedFDeriv_comp_iff hu hφx hsurj hφ (hK₁ Ks) (hK₁ Kt) (hK₂ hKs)
      (hK₂ hKt) hJJ'⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- If `φ` pulls `ω₀` back to `ω` on `C` and `J'` is the family `J` read in the chart, then `J'` is
tamed by `ω₀` over `D × φ(C)` wherever `J` is tamed by `ω` over `D × C`. -/
private theorem tames_of_mem_image (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap)
    (hCφ : C ⊆ φ.source) (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∀ z ∈ D, ∀ y ∈ φ '' C, ω₀.Tames (J' z y) := by
  rintro z hz _ ⟨x, hx, rfl⟩
  exact tames_of_isComplexLinearMap_mvfderiv hω
    (φ.bijective_mvfderiv (by simp) (hCφ hx)).surjective (hφ x hx) (hJJ' z hz x hx)
    (hJt z hz x hx)

/-- **The energy of the bubbling points in a symplectic chart.** Under the hypotheses of
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`, a further
subsequence `ψ` attaches to every bubbling point `z ∈ Z` a mass `m z ≥ δ`: for every small `ε > 0`
the Floer energy of `u_{ψ n}` over the disc `B_ε(z)` converges to `m z` plus the energy of the
limit `v` over the punctured disc, and the energy of `v` over `Ω \ Z` together with the masses is at
most `A`. This is the coordinate theorem
`SymplecticForm.exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset`
read back through the chart, which preserves the energy densities. -/
theorem exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset
    (hω : ω.IsNondegenerate) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω C) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ A) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M) (m : ℝ × ℝ → ℝ), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (ψ n)) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (φ ∘ u (ψ n))) (fderiv ℝ (φ ∘ v)) atTop
          (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
          (ω.perturbedMFDeriv Ks Kt v z).toLinearMap) ∧
        IntegrableOn (ω.floerEnergyDensity Ks Kt v) (Ω \ ↑Z) ∧
        (∀ z ∈ Z, δ ≤ m z) ∧
        (∀ z ∈ Z, ∀ᶠ ε in 𝓝[>] 0,
          Tendsto (fun n ↦ ∫ y in ball z ε, ω.floerEnergyDensity Ks Kt (u (ψ n)) y) atTop
            (𝓝 (m z + ∫ y in ball z ε \ {z}, ω.floerEnergyDensity Ks Kt v y))) ∧
        (∫ z in Ω \ ↑Z, ω.floerEnergyDensity Ks Kt v z) + ∑ z ∈ Z, m z ≤ A := by
  have hφC : IsCompact (φ '' C) := hC.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hCφ)
  have hJ't := tames_of_mem_image hω φ hφ hJJ' hCφ hJt
  obtain ⟨δ, hδ, hconv⟩ :=
    ω₀.exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset
      (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt hJ' hD hφC
      hDCW hJ't
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu hfl huC hint hA ↦ ?_⟩
  -- At a point of `Ω` where a map is differentiable with a value in `C`, the chart transports the
  -- energy density and the Floer equation.
  have hpt {w : ℝ × ℝ → M} {z : ℝ × ℝ} (hz : z ∈ Ω) (hwC : w z ∈ C)
      (hw : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I w z) :=
    floerEnergyDensity_comp_and_isComplexLinearMap_iff hω φ (hφ _ hwC)
      (hJJ' z (hΩD hz) _ hwC) hW hKs hKt (hCφ hwC) (hDCW ⟨hΩD hz, w z, hwC, rfl⟩) hw
  have hptu (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :=
    hpt hz (huC k hz) (((hu k).contMDiffAt (hΩ.mem_nhds hz)).mdifferentiableAt (by simp))
  obtain ⟨ψ, Z, w, m, hψ, hZΩ, hconc, hw1, hwC, hlim, hdlim, hweq, hwint, hm, hmlim, hmE⟩ :=
    hconv (u := fun k ↦ φ ∘ u k) hΩ hΩD
      (fun k ↦ contMDiffOn_iff_contDiffOn.1 <| φ.contMDiffOn.comp (hu k) ((huC k).mono_right hCφ))
      (fun k z hz ↦ ((hptu k hz).2).2 (hfl k z hz)) (fun k z hz ↦ ⟨u k z, huC k hz, rfl⟩)
      (fun k ↦ (hint k).congr_fun (fun y hy ↦ ((hptu k hy).1).symm) hΩ.measurableSet)
      (fun k ↦ (setIntegral_congr_fun hΩ.measurableSet fun y hy ↦ (hptu k hy).1).trans_le
        (hA k))
  set S := Ω \ (Z : Set (ℝ × ℝ))
  have hS : IsOpen S := hΩ.sdiff Z.finite_toSet.isClosed
  -- The limit in `M` is read back through the inverse of the chart.
  have hwt : MapsTo w S φ.target := hwC.mono_right (φ.mapsTo.mono_left hCφ).image_subset
  set v : ℝ × ℝ → M := φ.symm ∘ w
  have hv1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v S :=
    (φ.symm.contMDiffOn.of_le (by simp)).comp (contMDiffOn_iff_contDiffOn.2 hw1) hwt
  have hvC : MapsTo v S C := ((φ.leftInvOn.mono hCφ).mapsTo (surjOn_image _ _)).comp hwC
  have hφv (y : ℝ × ℝ) (hy : y ∈ S) : φ ∘ v =ᶠ[𝓝 y] w :=
    Filter.eventually_of_mem (hS.mem_nhds hy) fun y' hy' ↦ φ.right_inv (hwt hy')
  have hvpt (y : ℝ × ℝ) (hy : y ∈ S) :=
    hpt hy.1 (hvC hy) ((hv1.contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt one_ne_zero)
  have hvE (y : ℝ × ℝ) (hy : y ∈ S) :
      ω.floerEnergyDensity Ks Kt v y = ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y))
        (fun z y ↦ Kt z (φ.symm y)) w y :=
    ((hvpt y hy).1).symm.trans (ω₀.floerEnergyDensity_congr_of_eventuallyEq _ _ (hφv y hy))
  refine ⟨ψ, Z, v, m, hψ, hZΩ, fun z hz ε hε ↦ ?_, hv1, hvC,
    hlim.congr_right fun y hy ↦ (φ.right_inv (hwt hy)).symm,
    hdlim.congr_right fun y hy ↦ ((hφv y hy).fderiv_eq).symm, fun y hy ↦ ?_,
    hwint.congr_fun (fun y hy ↦ (hvE y hy).symm) hS.measurableSet, hm, fun z hz ↦ ?_,
    by rwa [setIntegral_congr_fun hS.measurableSet hvE]⟩
  · filter_upwards [hconc z hz ε hε] with n hn
    rwa [setIntegral_congr_fun (measurableSet_ball.inter hΩ.measurableSet)
      fun y hy ↦ (hptu (ψ n) hy.2).1] at hn
  · refine ((hvpt y hy).2).1 ?_
    have hvy : φ (v y) = w y := φ.right_inv (hwt hy)
    rw [ω₀.perturbedFDeriv_congr_of_eventuallyEq _ _ (hφv y hy), hvy]
    exact hweq y hy
  · -- The chart transports the energy densities, on `Ω` along the sequence and on `Ω \ Z` in the
    -- limit.
    exact eventually_tendsto_setIntegral_ball_congr hΩ (hZΩ hz)
      (fun n y hy ↦ ((hptu (ψ n) hy).1).symm) hvE (hmlim z hz)

/-- **Floer solutions of bounded energy in a symplectic chart converge in `C¹` off finitely many
bubbling points.** Under the hypotheses of the `C⁰` theorem
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset` for fixed
data, there is a threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions of the
Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on an open set `Ω ⊆ D`, with image in `C` and
Floer energy `∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ A`. Then there are a subsequence `ψ`, a finite
set `Z ⊆ Ω` with `#Z * δ ≤ A`, and a map `v` with values in `C` on `Ω \ Z` such that along `ψ` every
disc about a point of `Z` eventually carries Floer energy at least `δ`, the coordinate maps
`φ ∘ u_{ψ n}` and their derivatives converge to `φ ∘ v` and its derivative locally uniformly on
`Ω \ Z`, `v` is a `C¹` solution of the Floer equation for `J(z, v)` on `Ω \ Z`, and the Floer
energy of `v` over `Ω \ Z` is finite and at most `A`. See also
`IsNondegenerate.exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset`
for the energy masses at the bubbling points. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    (hω : ω.IsNondegenerate) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω C) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ A) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (ψ n)) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (φ ∘ u (ψ n))) (fderiv ℝ (φ ∘ v)) atTop
          (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
          (ω.perturbedMFDeriv Ks Kt v z).toLinearMap) ∧
        IntegrableOn (ω.floerEnergyDensity Ks Kt v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity Ks Kt v z ≤ A := by
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_setIntegral_floerEnergyDensity_ball_subseq_off_finset φ hφ hJJ'
      hW hKs hKt hJ' hD hC hCφ hDCW hJt
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu hfl huC hint hA ↦ ?_⟩
  obtain ⟨ψ, Z, v, m, hψ, hZΩ, hconc, hv1, hvC, hlim, hdlim, hveq, hvint, hm, -, hmA⟩ :=
    hconv hΩ hΩD hu hfl huC hint hA
  have hv0 : 0 ≤ ∫ z in Ω \ ↑Z, ω.floerEnergyDensity Ks Kt v z :=
    setIntegral_nonneg (hΩ.sdiff Z.finite_toSet.isClosed).measurableSet fun z hz ↦
      SmoothTwoForm.floerEnergyDensity_nonneg hω (hJt z (hΩD hz.1) _ (hvC hz)) (hveq z hz)
  have hcard : Z.card * δ ≤ ∑ z ∈ Z, m z := by simpa using Z.card_nsmul_le_sum m δ hm
  have hδ0 : 0 ≤ Z.card * δ := by positivity
  exact ⟨ψ, Z, v, hψ, hZΩ, by linarith, hconc, hv1, hvC, hlim, hdlim, hveq, hvint, by linarith⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end

end
