/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Geometry.Manifold.ExtChartAt.MapsTo
import TauCeti.Geometry.Symplectic.Floer.Rotation
import TauCeti.Geometry.Symplectic.Floer.UniqueContinuation.Coordinate

/-!
# Unique continuation for Floer solutions in a manifold

Let `M` be a boundaryless Hausdorff manifold with a two-form `ω`, such as a closed symplectic
manifold, and let `u, v : ℝ × ℝ → M` be `C¹` solutions of the Floer equation
`(du - X_K)^{0,1} = 0` on a connected open set `Ω` of the domain, for a perturbation
`K = K_s ds + K_t dt` and domain-dependent almost complex structures `J(z, x)` on the tangent
spaces of `M`, such that `J` and the Hamiltonian vector fields of `K_s` and `K_t`, read in every
chart of `M`, are `C¹`. If `u` and `v` agree on a nonempty open subset of `Ω`, they agree on all of
`Ω` (`TauCeti.SmoothTwoForm.eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`); otherwise the
points of `Ω` where they agree form a discrete subset of `Ω`
(`TauCeti.SmoothTwoForm.setOf_ne_mem_codiscreteWithin_of_isComplexLinearMap_perturbedMFDeriv`).

For a symplectic vector space target and Hamiltonian data this is
`TauCeti.SymplecticForm.eqOn_of_floerOperator_eq_zero_of_eqOn`. In a chart of the atlas of `M`,
however, the Floer equation becomes the coordinate equation

`∂ₜv - X(z, v) i = J(z, v) (∂ₛv - X(z, v) 1)`

(`TauCeti.SmoothTwoForm.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub`), whose
one-form `X` is the Hamiltonian one-form read in the chart
(`TauCeti.SmoothTwoForm.hamiltonianOneFormInChartAt`). It is not the Hamiltonian one-form of a
constant symplectic form, so the local step is the unique continuation theorem for this coordinate
equation with an arbitrary `C¹` one-form `X` and `C¹` field `J`
(`TauCeti.Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn` and
`TauCeti.Floer.setOf_ne_mem_codiscreteWithin_of_fderiv_stdComplexLineImag_sub`, in
`TauCeti.Geometry.Symplectic.Floer.UniqueContinuation.Coordinate`).

On the manifold, the points of `Ω` near which `u` and `v` agree form an open set. It is closed in
`Ω`: at a limit point the two maps agree since `M` is Hausdorff, and on a small disc around it
both maps take values in one chart (`TauCeti.exists_ball_subset_mapsTo_extChartAt_source`), whose
coordinate expressions solve the coordinate equation and agree on an open subset of the disc. As
`Ω` is connected this set is all of `Ω`. Near a coincidence of two solutions which differ somewhere
in `Ω`, the coordinate expressions cannot agree on the whole disc, so the coincidence is isolated.

For a cylindrical datum `K = H_t dt` and an `s`-independent `J_t`, the translate
`(s, t) ↦ u(s + c, t)` of a Floer trajectory is again one
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_add_right`). So a trajectory in
`M` which agrees with such a translate on a nonempty open set is `(c, 0)`-periodic
(`TauCeti.SmoothTwoForm.periodic_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn`). This is the step
of the argument of Floer, Hofer and Salamon for the density of the regular points of a
nonstationary trajectory which excludes a trajectory coinciding with one of its translates on an
open set.

## Main results

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

/-! ### Floer solutions in a manifold -/

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] {ω : SmoothTwoForm I M}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {Ks Kt : ℝ × ℝ → M → ℝ}
  {u v : ℝ × ℝ → M} {Ω : Set (ℝ × ℝ)}

/-- **The coordinate equation near a coincidence.** Let `u` and `v` be `C¹` solutions of the Floer
equation on an open set `Ω` which agree at `z₀ ∈ Ω`, and let `J` and the Hamiltonian vector fields
of `K_s` and `K_t`, read in every chart, be `C¹` over `Ω`. On some disc `B ⊆ Ω` around `z₀` both
maps take values in the chart at `u z₀`, and their coordinate expressions are `C¹` solutions of the
coordinate Floer equation. The structure and the Hamiltonian one-form read in that chart are `C¹`
along the graph over `B` of the coordinate expression of `u`, where the structure squares to `-1`.
-/
private theorem exists_ball_and_fderiv_extChartAt_comp_stdComplexLineImag_sub
    (ω : SmoothTwoForm I M) (hΩ : IsOpen Ω)
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
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (heq : u z₀ = v z₀) :
    ∃ r > 0, Metric.ball z₀ r ⊆ Ω ∧
      MapsTo u (Metric.ball z₀ r) (extChartAt I (u z₀)).source ∧
      MapsTo v (Metric.ball z₀ r) (extChartAt I (u z₀)).source ∧
      (∀ z ∈ Metric.ball z₀ r, ContDiffAt ℝ 1 (Floer.almostComplexInChartAt I (u z₀) J)
        (z, (extChartAt I (u z₀) ∘ u) z)) ∧
      (∀ z ∈ Metric.ball z₀ r,
        Floer.almostComplexInChartAt I (u z₀) J (z, (extChartAt I (u z₀) ∘ u) z) ∘L
          Floer.almostComplexInChartAt I (u z₀) J (z, (extChartAt I (u z₀) ∘ u) z) =
            -ContinuousLinearMap.id ℝ E) ∧
      (∀ z ∈ Metric.ball z₀ r, ContDiffAt ℝ 1 (ω.hamiltonianOneFormInChartAt (u z₀) Ks Kt)
        (z, (extChartAt I (u z₀) ∘ u) z)) ∧
      ContDiffOn ℝ 1 (extChartAt I (u z₀) ∘ u) (Metric.ball z₀ r) ∧
      ContDiffOn ℝ 1 (extChartAt I (u z₀) ∘ v) (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, fderiv ℝ (extChartAt I (u z₀) ∘ u) z stdComplexLineImag -
          ω.hamiltonianOneFormInChartAt (u z₀) Ks Kt (z, (extChartAt I (u z₀) ∘ u) z)
            stdComplexLineImag =
        Floer.almostComplexInChartAt I (u z₀) J (z, (extChartAt I (u z₀) ∘ u) z)
          (fderiv ℝ (extChartAt I (u z₀) ∘ u) z stdComplexLineReal -
            ω.hamiltonianOneFormInChartAt (u z₀) Ks Kt (z, (extChartAt I (u z₀) ∘ u) z)
              stdComplexLineReal)) ∧
      ∀ z ∈ Metric.ball z₀ r, fderiv ℝ (extChartAt I (u z₀) ∘ v) z stdComplexLineImag -
          ω.hamiltonianOneFormInChartAt (u z₀) Ks Kt (z, (extChartAt I (u z₀) ∘ v) z)
            stdComplexLineImag =
        Floer.almostComplexInChartAt I (u z₀) J (z, (extChartAt I (u z₀) ∘ v) z)
          (fderiv ℝ (extChartAt I (u z₀) ∘ v) z stdComplexLineReal -
            ω.hamiltonianOneFormInChartAt (u z₀) Ks Kt (z, (extChartAt I (u z₀) ∘ v) z)
              stdComplexLineReal) := by
  have hΩz₀ := hΩ.mem_nhds hz₀
  obtain ⟨r, hr, hBΩ, huB, hvB⟩ := exists_ball_subset_mapsTo_extChartAt_source (I := I) hΩz₀
    (hu.continuousOn.continuousAt hΩz₀) (hv.continuousOn.continuousAt hΩz₀) heq
  obtain ⟨hu', hFu'⟩ := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub
    Metric.isOpen_ball (hu.mono hBΩ) one_ne_zero huB fun z hz ↦ hFu z (hBΩ hz)
  obtain ⟨hv', hFv'⟩ := ω.contDiffOn_extChartAt_comp_and_fderiv_stdComplexLineImag_sub
    Metric.isOpen_ball (hv.mono hBΩ) one_ne_zero hvB fun z hz ↦ hFv z (hBΩ hz)
  -- Along the graph of the coordinate expression of `u`, the data are read at interior points.
  have hT : IsOpen (Ω ×ˢ (extChartAt I (u z₀)).target) :=
    hΩ.prod (isOpen_extChartAt_target (u z₀))
  have hmem {z : ℝ × ℝ} (hz : z ∈ Metric.ball z₀ r) :
      Ω ×ˢ (extChartAt I (u z₀)).target ∈ 𝓝 (z, (extChartAt I (u z₀) ∘ u) z) :=
    hT.mem_nhds ⟨hBΩ hz, (extChartAt I (u z₀)).map_source (huB hz)⟩
  refine ⟨r, hr, hBΩ, huB, hvB, fun z hz ↦ (hJ _).contDiffAt (hmem hz),
    fun z hz ↦ ContinuousLinearMap.ext fun w ↦ ?_,
    fun z hz ↦ (contDiffOn_hamiltonianOneFormInChartAt (hXs _) (hXt _)).contDiffAt (hmem hz),
    hu', hv', hFu', hFv'⟩
  simpa using Floer.almostComplexInChartAt_apply_apply (J := J)
    ((extChartAt I (u z₀)).map_source (huB hz)) z w

variable [T2Space M]

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
  have hS {z : ℝ × ℝ} : z ∈ S ↔ u =ᶠ[𝓝 z] v := Iff.rfl
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
        (eventually_nhdsWithin_of_forall fun z hz ↦ (hS.1 hz).eq_of_nhds.symm))
  -- On a disc `B` around `z₀` both maps take values in the chart at `u z₀`, and their coordinate
  -- expressions solve the coordinate Floer equation and agree on `B ∩ S`.
  obtain ⟨r, hr, -, huB, hvB, hJ', hJJ', hX', hu', hv', hFu', hFv'⟩ :=
    exists_ball_and_fderiv_extChartAt_comp_stdComplexLineImag_sub ω hΩ hJ hXs hXt hu hv hFu hFv
      hz₀Ω heq
  have hcoord := Floer.eqOn_of_fderiv_stdComplexLineImag_sub_of_eqOn Metric.isOpen_ball
    (convex_ball z₀ r).isPreconnected hJ' hJJ' hX' hu' hv' hFu' hFv'
    (Metric.isOpen_ball.inter hSo)
    (mem_closure_iff_nhds.1 hz₀S _ (Metric.ball_mem_nhds z₀ hr)) inter_subset_left
    fun z hz ↦ by simp [(hS.1 hz.2).eq_of_nhds]
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
  -- On a disc `B` around a coincidence both maps take values in the chart at `u z₀`, and their
  -- coordinate expressions solve the coordinate Floer equation.
  obtain ⟨r, hr, hBΩ, huB, hvB, hJ', hJJ', hX', hu', hv', hFu', hFv'⟩ :=
    exists_ball_and_fderiv_extChartAt_comp_stdComplexLineImag_sub ω hΩ hJ hXs hXt hu hv hFu hFv
      hz₀ heq
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
    have hF' := hF (z + (c, 0))
    have hz : (z + (c, 0)).2 = z.2 := by simp
    rw [hz] at hF'
    exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right rfl (by simp) hF'
  have hXs (α : M) : ContDiffOn ℝ 1 (ω.hamiltonianVectorFieldInChartAt α
      fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) (univ ×ˢ (extChartAt I α).target) := by
    rw [hamiltonianVectorFieldInChartAt_zero]
    exact contDiff_zero_fun.contDiffOn
  intro z
  exact (eqOn_of_isComplexLinearMap_perturbedMFDeriv_of_eqOn isOpen_univ isPreconnected_univ hJ
    hXs hH hu.contMDiffOn (hu.comp (contDiff_id.add contDiff_const).contMDiff).contMDiffOn
    (fun z _ ↦ hF z) (fun z _ ↦ hFc z) hU hUne (subset_univ U) hUc (mem_univ z)).symm

end TauCeti.SmoothTwoForm
