/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Chart
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Compactness of Floer solutions in a symplectic chart of a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `φ : M ⊇ U → V` be a symplectic chart: a smooth partial
diffeomorphism onto an open subset of a finite-dimensional inner product space `V` carrying a
constant symplectic form `ω₀`, with `ω_x(v, w) = ω₀(dφ_x v, dφ_x w)` on its source. Darboux's
theorem (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) supplies such a chart around
every point of a boundaryless symplectic manifold whose model space is an inner product space.

This file transfers the compactness theorem for Floer solutions of bounded energy in a symplectic
vector space,
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`, to
solutions `u : ℝ × ℝ → M` of the Floer equation `(du - X_K)^{0,1} = 0` in `M` whose image stays in
a compact subset `C` of the source of a symplectic chart, in the namespace
`TauCeti.SmoothTwoForm`:
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`.
The data are read in the chart: the Hamiltonians are `K'(z, y) = K(z, φ⁻¹ y)`, and the almost
complex structures are any family `J'(z, y)` on `V` with `dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x`.
The regularity hypotheses, `C³` for `K'` and `C²` for `J'`, are those of the vector-space theorem
for this coordinate data. By `TauCeti.Geometry.Symplectic.Floer.Chart`, the coordinate maps
`φ ∘ u` solve the Floer equation of `(V, ω₀)` for `K'` and `J'`, with the same energy density, and
`J'` is tamed by `ω₀` where `J` is tamed by `ω`. So a sequence of such solutions on an open subset
`Ω` of a compact window `D` of the domain, with Floer energy at most `A`, has a subsequence which
converges off a finite set `Z` of bubbling points: the coordinate maps converge locally uniformly
on `Ω \ Z` with locally bounded derivatives, the maps themselves converge pointwise in `M` to a
continuous limit with values in `C`, `#Z δ ≤ A` for a threshold `δ > 0` depending only on the
data, and at least the energy `δ` concentrates at every point of `Z`.

Here the image of the solutions is assumed to stay in a single chart. Gromov–Floer compactness on
a closed manifold also needs the mean-value inequality to localize the images of small discs of
small energy into charts; that step is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the inhomogeneous equation).
-/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

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
    {W : Set ((ℝ × ℝ) × V)} (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Ks p.1 (φ.symm p.2)) W)
    (hKt : ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ Kt p.1 (φ.symm p.2)) W)
    (hx : u z ∈ φ.source) (hzx : (z, φ (u z)) ∈ W) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u) z =
        ω.floerEnergyDensity Ks Kt u z ∧
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y)) (φ ∘ u)
          z).toLinearMap := by
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
    (hω.isComplexLinearMap_perturbedFDeriv_comp_iff hu hφx hsurj hφ (hK₁ Ks) (hK₁ Kt) (hK₂ hKs)
      (hK₂ hKt) hJJ').2 hfl⟩

variable {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

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
  have hφC : IsCompact (φ '' C) := hC.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hCφ)
  -- In the chart, `J'` is tamed by `ω₀` over `D × φ(C)`.
  have hJ't : ∀ z ∈ D, ∀ y ∈ φ '' C, ω₀.Tames (J' z y) := by
    rintro z hz _ ⟨x, hx, rfl⟩
    exact tames_of_isComplexLinearMap_mvfderiv hω
      (φ.bijective_mvfderiv (by simp) (hCφ hx)).surjective (hφ x hx) (hJJ' z hz x hx)
      (hJt z hz x hx)
  obtain ⟨δ, hδ, hconv⟩ := ω₀.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun z y ↦ Ks z (φ.symm y)) (Kt := fun z y ↦ Kt z (φ.symm y)) hW hKs hKt hJ' hD hφC
    hDCW hJ't
  refine ⟨δ, hδ, fun Ω u A hΩ hΩD hu hfl huC hint hA ↦ ?_⟩
  -- At each point of `Ω`, the chart transports the Floer equation and the energy density.
  have hpt (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :=
    floerEnergyDensity_comp_and_isComplexLinearMap hω φ (hφ _ (huC k hz))
      (hJJ' z (hΩD hz) _ (huC k hz)) hW hKs hKt (hCφ (huC k hz))
      (hDCW ⟨hΩD hz, u k z, huC k hz, rfl⟩)
      (((hu k).contMDiffAt (hΩ.mem_nhds hz)).mdifferentiableAt (by norm_num)) (hfl k z hz)
  have hint_eq (k : ℕ) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
      ∫ y in S, ω₀.floerEnergyDensity (fun z y ↦ Ks z (φ.symm y)) (fun z y ↦ Kt z (φ.symm y))
        (φ ∘ u k) y = ∫ y in S, ω.floerEnergyDensity Ks Kt (u k) y :=
    setIntegral_congr_fun hS fun y hy ↦ (hpt k (hSΩ hy)).1
  obtain ⟨ψ, Z, w, hψ, hZΩ, hcard, hconc, hbd, hwc, hwC, hlim⟩ := hconv (u := fun k ↦ φ ∘ u k)
    hΩ hΩD (fun k ↦ contMDiffOn_iff_contDiffOn.1 <|
      (φ.contMDiffOn.of_le (WithTop.coe_le_coe.2 le_top)).comp (hu k)
        ((huC k).mono_right hCφ))
    (fun k z hz ↦ (hpt k hz).2) (fun k z hz ↦ ⟨u k z, huC k hz, rfl⟩)
    (fun k ↦ (hint k).congr_fun (fun y hy ↦ ((hpt k hy).1).symm) hΩ.measurableSet)
    (fun k ↦ (hint_eq k hΩ.measurableSet subset_rfl).trans_le (hA k))
  -- The limit in `M` is read back through the inverse of the chart.
  have hwt : ∀ y ∈ Ω \ ↑Z, φ (φ.symm (w y)) = w y ∧ φ.symm (w y) ∈ C := by
    intro y hy
    obtain ⟨x, hx, hxw⟩ := hwC hy
    have h := φ.toPartialEquiv.left_inv (hCφ hx)
    rw [← hxw]
    exact ⟨congrArg φ h, (congrArg (· ∈ C) h).mpr hx⟩
  refine ⟨ψ, Z, φ.symm ∘ w, hψ, hZΩ, hcard, fun z hz ε hε ↦ ?_, hbd, ?_,
    fun y hy ↦ (hwt y hy).2, ?_, fun y hy ↦ ?_⟩
  · filter_upwards [hconc z hz ε hε] with n hn
    rwa [hint_eq _ (measurableSet_ball.inter hΩ.measurableSet) inter_subset_right] at hn
  · refine φ.symm.contMDiffOn.continuousOn.comp hwc fun y hy ↦ ?_
    obtain ⟨x, hx, hxw⟩ := hwC hy
    rw [← hxw]
    exact φ.toPartialEquiv.map_source (hCφ hx)
  · exact hlim.congr_right fun y hy ↦ ((hwt y hy).1).symm
  · obtain ⟨x, hx, hxw⟩ := hwC hy
    have hcont : ContinuousAt φ.symm (w y) := by
      rw [← hxw]
      exact φ.symm.contMDiffOn.continuousOn.continuousAt
        (φ.open_target.mem_nhds (φ.toPartialEquiv.map_source (hCφ hx)))
    refine ((hcont.tendsto.comp (hlim.tendsto_at hy)).congr fun n ↦ ?_)
    exact φ.toPartialEquiv.left_inv (hCφ (huC (ψ n) hy.1))

end TauCeti.SmoothTwoForm.IsNondegenerate
