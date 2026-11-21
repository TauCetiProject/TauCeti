/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
public import TauCeti.Geometry.Symplectic.Floer.Isolation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Cutoff
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Floer trajectories in a manifold near a nondegenerate orbit in a symplectic chart

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `H : ℝ → M → ℝ` be a `C²` Hamiltonian, `1`-periodic in time. Let
`φ : M ⊇ U → V` be a symplectic chart: a smooth partial diffeomorphism onto an open subset of a
symplectic vector space `(V, ω₀)` with `ω_y(v, w) = ω₀(dφ_y v, dφ_y w)` on its source. Darboux's
theorem (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) supplies such a chart around
every point of a finite-dimensional boundaryless symplectic manifold.

This file proves the manifold counterpart of `TauCeti.SymplecticForm.exists_pos_forall_eq_of_floer`
for a `1`-periodic orbit of `H` whose image lies in the source of the chart. Write `x : ℝ → V` for
the orbit read in the chart: a `1`-periodic orbit of the Hamiltonian `y ↦ H(t, φ⁻¹ y)` with values
in the target of `φ`, so that `φ⁻¹ ∘ x` is the orbit in `M`. If `x` is nondegenerate, then the
stationary cylinder over `φ⁻¹ ∘ x` is isolated among all finite-energy Floer trajectories in `M`,
uniformly in the trajectory. For tameness constants `0 < c` and `C` there is `δ > 0` such that
every `C²` solution `u : ℝ × ℝ → M` of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with
`1`-periodic loops and finite energy, whose image lies in the source of `φ` with
`‖φ(u(s, t)) - x(t)‖ ≤ δ` for all `s` and `t`, is the stationary cylinder: `u(s, t) = φ⁻¹(x(t))`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_eq_of_floer`). The tameness constants
refer to the structures `J(s, t, u(s, t))` read in the chart.

The proof reads the trajectory in the chart and applies the vector-space theorem. The
Hamiltonian read in the chart, `y ↦ H(t, φ⁻¹ y)`, is only defined on the target of `φ`; a cutoff
equal to one near a compact neighbourhood of the orbit globalizes it to a `C²` Hamiltonian on `V`,
`1`-periodic in time, which agrees with it near that neighbourhood
(`PartialDiffeomorph.exists_contDiff_eventuallyEq_comp_symm`). There the two Hamiltonians have
the same Hamiltonian vector fields, so the orbit and its nondegeneracy are those of the globalized
Hamiltonian. A trajectory close enough to the orbit stays in that neighbourhood, so its
coordinate map `φ ∘ u` solves the Floer equation of `(V, ω₀)` for the globalized Hamiltonian and
has the energy density of `u` (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp`,
`TauCeti.SmoothTwoForm.IsNondegenerate.isComplexLinearMap_perturbedFDeriv_comp_iff`).

The orbit is assumed to lie in a single symplectic chart, as constant orbits always do. An orbit
that meets no single chart needs a symplectic chart along the whole loop, which is not treated
here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on Floer trajectories near nondegenerate orbits.
-/

public section

open Function Set Filter Topology MeasureTheory Metric
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {H : ℝ → M → ℝ} {x : ℝ → V} {c : ℝ}

/-- **A Floer trajectory read in a symplectic chart.** Let `H'` agree near every point of a set `K`
with the Hamiltonian `y ↦ H(t, φ⁻¹ y)` read in a symplectic chart `φ`, for all times, and let
`u` be a `C²` solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on
`ℝ × [0, 1]` with values in the source of `φ` and with `φ ∘ u` in `K`. Then the coordinate map
`φ ∘ u` solves the Floer equation of `(V, ω₀)` for `H'` and the structures `J'` read in the
chart, and it has the same Floer energy as `u` over `ℝ × [0, 1]`. -/
private theorem isComplexLinearMap_perturbedFDeriv_comp_and_lintegral_eq (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    (hφ : ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    {H' : ℝ → V → ℝ} (hH' : ContDiff ℝ 2 (uncurry H')) {K : Set V}
    (hH'eq : ∀ y ∈ K, ∀ᶠ y' in 𝓝 y, ∀ t, H' t y' = H t (φ.symm y')) {u : ℝ × ℝ → M}
    {J : ℝ × ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    {J' : ℝ × ℝ → AlmostComplexStructure V} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hsrc : ∀ z, u z ∈ φ.source) (hK : ∀ z, φ (u z) ∈ K)
    (hJJ' : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (J z (u z)) (J' z) (mvfderiv I φ (u z)).toLinearMap)
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap) :
    (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J' z) (ω₀.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z).toLinearMap) ∧
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω₀.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H' w.2) (φ ∘ u) z) =
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  -- Near each point of `u`, the Hamiltonian `H` is `H' ∘ φ`.
  have hHloc (z : ℝ × ℝ) (t : ℝ) : H t =ᶠ[𝓝 (u z)] H' t ∘ φ := by
    filter_upwards [(φ.contMDiffOn.continuousOn.continuousAt
      (φ.open_source.mem_nhds (hsrc z))).eventually (hH'eq _ (hK z)),
      φ.open_source.mem_nhds (hsrc z)] with y hy hys
    rw [comp_apply, hy t]
    exact congrArg (H t) (φ.toPartialEquiv.left_inv hys).symm
  have hH'd (t : ℝ) (y : V) : DifferentiableAt ℝ (H' t) y :=
    ((hH'.differentiable two_ne_zero) _).comp _
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hφz (z : ℝ × ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :=
    (hω.isComplexLinearMap_perturbedFDeriv_comp_iff (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
      (Ks' := fun _ _ ↦ 0) (Kt' := fun w ↦ H' w.2) (hu.mdifferentiable two_ne_zero z)
      (φ.mdifferentiableAt (by simp) (hsrc z)) (φ.bijective_mvfderiv (by simp) (hsrc z)).surjective
      (hφ _ (hsrc z)) EventuallyEq.rfl (hHloc z z.2) (differentiableAt_const _) (hH'd z.2 _)
      (hJJ' z hz)).2 (hfloer z hz)
  have hdens (z : ℝ × ℝ) := hω.floerEnergyDensity_comp (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (Ks' := fun _ _ ↦ 0) (Kt' := fun w ↦ H' w.2)
    (hu.mdifferentiable two_ne_zero z) (φ.mdifferentiableAt (by simp) (hsrc z))
    (φ.bijective_mvfderiv (by simp) (hsrc z)).surjective (hφ _ (hsrc z)) EventuallyEq.rfl
    (hHloc z z.2) (differentiableAt_const _) (hH'd z.2 _)
  exact ⟨hφz, by simp only [hdens]⟩

/-- **Floer trajectories near a nondegenerate orbit in a symplectic chart are stationary.** Let
`ω` be a nondegenerate two-form on `M`, let `φ` be a smooth partial diffeomorphism from `M` onto
an open subset of `V` pulling the symplectic form `ω₀` back to `ω` on its source, and let `H` be a
`C²` Hamiltonian on `M`, `1`-periodic in time. Let `x` be a `1`-periodic orbit of the Hamiltonian
read in the chart, `y ↦ H(t, φ⁻¹ y)`, with values in the target of `φ`, which is nondegenerate: the
propagator of its linearized equation has no nonzero fixed vector at time `1`. Let `0 < c` and `C`
be tameness constants. Then there is `δ > 0` with the following property. Let `u` be a `C²`
solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with
`1`-periodic loops and finite energy, whose structures `J(z, u z)`, read in the chart as `J' z`,
satisfy `c ‖v‖² ≤ ω₀(v, J' z v)` and `‖J' z v‖ ≤ C ‖v‖`. If `u` takes values in the source of `φ`
with `‖φ(u(s, t)) - x(t)‖ ≤ δ` for all `s` and `t`, then `u` is the stationary cylinder over the
orbit: `u(s, t) = φ⁻¹(x(t))`. -/
theorem exists_pos_forall_eq_of_floer (hω : ω.IsNondegenerate)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    (hφ : ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry H)) (hHper : Periodic H 1)
    (hxper : Periodic x 1) (hxφ : ∀ t, x t ∈ φ.target)
    (hx : ∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (fun y ↦ H t (φ.symm y)) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (fun y ↦ H t (φ.symm y))) (x t)) 1 v = v →
        v = 0) (hc : 0 < c) (C : ℝ) :
    ∃ δ > 0, ∀ {u : ℝ × ℝ → M} {J : ℝ × ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
      {J' : ℝ × ℝ → AlmostComplexStructure V},
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u → (∀ s, Periodic (fun t ↦ u (s, t)) 1) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (J z (u z)) (J' z) (mvfderiv I φ (u z)).toLinearMap) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω₀ v (J' z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J' z v‖ ≤ C * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z).toLinearMap) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤ →
      (∀ s t, u (s, t) ∈ φ.source ∧ ‖φ (u (s, t)) - x t‖ ≤ δ) →
      ∀ s t, u (s, t) = φ.symm (x t) := by
  -- A compact neighbourhood `K` of the orbit in the target of the chart, and a `C²` Hamiltonian
  -- `H'` on `V` agreeing near `K` with the Hamiltonian read in the chart.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hKx : IsCompact (range x) := hxper.compact_of_continuous one_ne_zero hxc
  obtain ⟨δ₀, hδ₀, hKφ⟩ :=
    hKx.exists_cthickening_subset_open φ.open_target (range_subset_iff.2 hxφ)
  obtain ⟨H', hH', hH'per, hH'eq⟩ :=
    φ.exists_contDiff_eventuallyEq_comp_symm (WithTop.coe_le_coe.2 le_top) hH hKx.cthickening hKφ
  -- Near the orbit the two Hamiltonians have the same Hamiltonian vector fields, so `x` is a
  -- nondegenerate orbit of `H'`.
  have hX (t : ℝ) : ω₀.hamiltonianVectorField (H' t) =ᶠ[𝓝 (x t)]
      ω₀.hamiltonianVectorField (fun y ↦ H t (φ.symm y)) :=
    (hH'eq (x t) (self_subset_cthickening _ (mem_range_self t))).eventually_nhds.mono
      fun y hy ↦ ω₀.hamiltonianVectorField_congr_of_eventuallyEq (hy.mono fun _ h ↦ h t)
  have hx' (t : ℝ) : HasDerivAt x (ω₀.hamiltonianVectorField (H' t) (x t)) t := by
    rw [(hX t).eq_of_nhds]
    exact hx t
  have hnd' : ∀ v, dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (H' t)) (x t)) 1 v = v → v = 0 := by
    have hfd : (fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (H' t)) (x t)) =
        fun t ↦ fderiv ℝ (ω₀.hamiltonianVectorField (fun y ↦ H t (φ.symm y))) (x t) :=
      funext fun t ↦ (hX t).fderiv_eq
    rw [hfd]
    exact hnd
  obtain ⟨δ₁, hδ₁, hiso⟩ :=
    SymplecticForm.exists_pos_forall_eq_of_floer hH' (hH'per 1 hHper) hxper hx' hnd' hc C
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun {u J J'} hu hper hJJ' hJc hJM hfloer hE hclose ↦ ?_⟩
  have hsrc (z : ℝ × ℝ) : u z ∈ φ.source := (hclose z.1 z.2).1
  -- The trajectory, read in the chart, stays in `K`, where it solves the Floer equation for `H'`.
  have hK (z : ℝ × ℝ) : φ (u z) ∈ cthickening δ₀ (range x) :=
    mem_cthickening_of_dist_le _ (x z.2) _ _ (mem_range_self _) (by
      rw [dist_eq_norm]; exact (hclose z.1 z.2).2.trans (min_le_left _ _))
  obtain ⟨hfloer', hE'⟩ := isComplexLinearMap_perturbedFDeriv_comp_and_lintegral_eq hω φ hφ hH'
    hH'eq hu hsrc hK hJJ' hfloer
  have hu' : ContDiff ℝ 2 (φ ∘ u) :=
    contMDiff_iff_contDiff.1 ((φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp_contMDiff
      hu hsrc)
  intro s t
  have h := hiso hu' (fun s t ↦ congrArg φ (hper s t)) hJc hJM hfloer' (hE' ▸ hE)
    (fun s t ↦ (hclose s t).2.trans (min_le_right _ _)) s t
  rw [← h]
  exact (φ.toPartialEquiv.left_inv (hsrc (s, t))).symm

end TauCeti.SmoothTwoForm.IsNondegenerate
