/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Compactness of Floer solutions in a chart of a manifold

Let `ω` be a nondegenerate two-form on a manifold `M` with finite-dimensional model space `E`,
such as a closed symplectic manifold, and let `u : ℝ × ℝ → M` solve the Floer equation
`(du - X_K)^{0,1} = 0` for a perturbation `K = K_s ds + K_t dt` and domain-dependent almost
complex structures `J(z, x)` on the tangent spaces of `M`. Gromov–Floer compactness for such a
target is local in the target: where the derivatives of a sequence of solutions are bounded, small
pieces of the solutions stay in a single chart, and there they solve a coordinate Floer equation
to which the compactness theorem of `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`
applies. The
Floer equation read in the chart at a point `α` is `TauCeti.Geometry.Symplectic.Floer.Chart`:
a solution `u` with values in the chart source has a coordinate expression
`v = extChartAt I α ∘ u` solving `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})`, with `J` and the
Hamiltonian vector fields read in the chart
(`TauCeti.SmoothTwoForm.fderiv_extChartAt_comp_stdComplexLineImag_sub`). This file proves the
compactness theorem for solutions with values in one chart, both for a chart of the atlas, which
needs no closedness of `ω` and no inner product on `E`, and for a symplectic chart.

## Charts of the atlas

* In the chart, `ω(·, J ·)` is a continuous family of bilinear forms on `E`, positive when `J` is
  tamed by `ω`, hence uniformly coercive on a compact window. So the intrinsic Floer energy
  density `ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` controls `‖∂ₛv‖²` up to an additive constant
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_norm_fderiv_extChartAt_comp_sq_le`).
* **Compactness in a chart** (in the namespace `TauCeti.SmoothTwoForm`,
  `IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_extChartAt_subseq_off_finset`):
  a sequence of `C³` solutions with values in the chart source, chart coordinates in a compact set
  `K` and bounded Floer energy has a subsequence whose coordinate expressions converge locally
  uniformly off a finite set `Z` of bubbling points, with derivatives bounded on compact subsets
  of the complement and Floer energy at least a fixed `δ > 0` concentrating at each point of `Z`.
  The solutions themselves converge pointwise off `Z` in `M`.

The chart coordinates are transported to a Euclidean space by `toEuclidean`, where the coordinate
compactness theorem, which uses the graph construction in a Euclidean product, applies; so no inner
product on `E` is needed. The conclusions are stated in the chart coordinates, where locally
uniform convergence and bounds on derivatives have a meaning without a metric on `M`. Covering a
domain by such chart pieces, the bubbles at the points of `Z` and breaking along cylindrical ends
are not treated here.

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
  set e := extChartAt I α with he
  set T := trivializationAt E (TangentSpace I) α with hT
  set Jc := Floer.almostComplexInChartAt I α J
  have hDK : IsCompact (D ×ˢ K) := hD.prod hK
  have hbase {y : E} (hy : y ∈ e.target) : e.symm y ∈ T.baseSet := by
    simpa only [hT, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using
      e.map_target hy
  -- In the chart, `ω(·, J ·)` is the bilinear form `b`, continuous and positive on `D × K`.
  set b : (ℝ × ℝ) × E → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((compL ℝ E E ℝ).flip (Jc p)).comp
      (ContinuousAlternatingMap.flatL ℝ E ℝ (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α p.2))
    with hb_def
  have hb : ∀ p ∈ D ×ˢ K, ∀ a, b p a a = SmoothBundleForm.eval₂ ω (e.symm p.2)
      (T.symmL ℝ (e.symm p.2) a) (J p.1 (e.symm p.2) (T.symmL ℝ (e.symm p.2) a)) := by
    rintro ⟨z, y⟩ hp a
    have hy : y ∈ e.target := hKα hp.2
    simp only [hb_def, comp_apply, flip_apply, compL_apply,
      ContinuousAlternatingMap.flatL_apply_apply]
    -- The coordinate expression of `ω` feeds it the vectors with the given tangent coordinates.
    have hS := TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) (x₀ := α)
      (by simpa only [he, extChartAt_source] using e.map_target hy)
    rw [(extChartAt I α).right_inv hy] at hS
    rw [RoughForm.inChartAt_apply, SmoothBundleForm.eval₂_apply, ← hS]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact (congrArg (T.symmL ℝ (e.symm y)) (Floer.almostComplexInChartAt_apply z y a)).trans
        (Trivialization.symmL_continuousLinearMapAt _ (hbase hy) _)
  have hbc : ContinuousOn b (D ×ˢ K) :=
    ((compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      ((ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.comp_continuousOn
        ((ω.isSmoothForm.continuousOn_inChartAt α).comp continuousOn_snd
          fun p hp ↦ hKα hp.2))
  obtain ⟨c, hc, hcb⟩ := hDK.exists_pos_forall_mul_norm_sq_le hbc fun p hp a ha ↦ by
    rw [hb p hp]
    have hy : p.2 ∈ e.target := hKα hp.2
    have hSa : T.symmL ℝ (e.symm p.2) a ≠ 0 := fun h0 ↦ ha <| by
      rw [← Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ (hbase hy) a, h0, map_zero]
    simpa only [IsNondegenerate.symplecticFormAt_apply] using hJt p.1 hp.1 p.2 hp.2 _ hSa
  obtain ⟨B, hB⟩ := hDK.exists_bound_of_continuousOn hX
  refine ⟨2 / c, by positivity, 2 * B ^ 2, by positivity, fun u z hz hus huK hu h ↦ ?_⟩
  have hp : (z, e (u z)) ∈ D ×ˢ K := ⟨hz, huK⟩
  have hx : e.symm (e (u z)) = u z := e.left_inv hus
  have hub : u z ∈ T.baseSet := by
    simpa only [hT, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using hus
  -- The coordinate `a` of the perturbed derivative `∂ₛu - X_{K_s}` has `c ‖a‖² ≤ e(u)`.
  set Xs := ω.hamiltonianVectorFieldInChartAt α Ks (z, e (u z)) with hXs
  set a := fderiv ℝ (e ∘ u) z stdComplexLineReal - Xs with ha
  have hPs : T.symmL ℝ (u z) a = ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal := by
    have hre := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hus
      stdComplexLineReal
    simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, zero_smul, one_smul,
      sub_zero] at hre
    rw [ha, hXs, ← hre, Trivialization.symmL_continuousLinearMapAt _ hub]
  have hea : b (z, e (u z)) a a = ω.floerEnergyDensity Ks Kt u z := by
    have hPt := h.apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at hPt
    rw [hb _ hp]
    dsimp only
    rw [hx, hPs, floerEnergyDensity_def, hPt]
  have hca : c * ‖a‖ ^ 2 ≤ ω.floerEnergyDensity Ks Kt u z := hea ▸ hcb _ hp a
  have hXB : ‖Xs‖ ≤ B := by simpa using hB _ hp
  have htri : ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ≤ ‖a‖ + ‖Xs‖ := by
    simpa [ha] using norm_le_norm_sub_add (fderiv ℝ (e ∘ u) z stdComplexLineReal) Xs
  have hsq : ‖fderiv ℝ (e ∘ u) z stdComplexLineReal‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * B ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg Xs, norm_nonneg (fderiv ℝ (e ∘ u) z stdComplexLineReal),
      sq_nonneg (‖a‖ - ‖Xs‖)]
  have hle : 2 * ‖a‖ ^ 2 ≤ 2 / c * ω.floerEnergyDensity Ks Kt u z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  linarith

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
  classical
  set e := extChartAt I α with he
  obtain ⟨A, hA0, B, hB0, hpt⟩ := hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le (Kt := Kt) α
    hD hK hKα (hJ.continuousOn.mono hDKW) (hXs.continuousOn.mono hDKW) hJt
  -- Transport the chart coordinates to a Euclidean space, where the compactness theorem for the
  -- coordinate equation applies.
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] V := toEuclidean
  let g : (ℝ × ℝ) × V → (ℝ × ℝ) × E := fun p ↦ (p.1, L.symm p.2)
  have hgc : ContDiff ℝ 2 g := contDiff_fst.prodMk (L.symm.contDiff.comp contDiff_snd)
  set X : (ℝ × ℝ) × E → ℝ × ℝ →L[ℝ] E := fun p ↦
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorFieldInChartAt α Ks p) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorFieldInChartAt α Kt p)
    with hX_def
  have hX : ContDiffOn ℝ 2 X W :=
    (contDiffOn_const.smulRight hXs).add (contDiffOn_const.smulRight hXt)
  have hXre (p : (ℝ × ℝ) × E) :
      X p stdComplexLineReal = ω.hamiltonianVectorFieldInChartAt α Ks p := by
    simp [hX_def, stdComplexLineReal]
  have hXim (p : (ℝ × ℝ) × E) :
      X p stdComplexLineImag = ω.hamiltonianVectorFieldInChartAt α Kt p := by
    simp [hX_def, stdComplexLineImag]
  let J' : (ℝ × ℝ) × V → V →L[ℝ] V := fun p ↦ (L : E →L[ℝ] V) ∘L
    Floer.almostComplexInChartAt I α J (g p) ∘L (L.symm : V →L[ℝ] E)
  let X' : (ℝ × ℝ) × V → ℝ × ℝ →L[ℝ] V := fun p ↦ (L : E →L[ℝ] V) ∘L X (g p)
  have hJ'c : ContDiffOn ℝ 2 J' (g ⁻¹' W) :=
    contDiffOn_const.clm_comp ((hJ.comp hgc.contDiffOn (mapsTo_preimage g W)).clm_comp
      contDiffOn_const)
  have hX'c : ContDiffOn ℝ 2 X' (g ⁻¹' W) :=
    contDiffOn_const.clm_comp (hX.comp hgc.contDiffOn (mapsTo_preimage g W))
  have hK' : IsCompact (L '' K) := hK.image L.continuous
  have hDKW' : D ×ˢ (L '' K) ⊆ g ⁻¹' W := by
    rintro ⟨z, _⟩ ⟨hz, y, hy, rfl⟩
    simpa [g] using hDKW ⟨hz, hy⟩
  have hJsq : ∀ z ∈ D, ∀ x ∈ L '' K, ∀ v, J' (z, x) (J' (z, x) v) = -v := by
    rintro z - _ ⟨y, hy, rfl⟩ v
    simp [J', g, Floer.almostComplexInChartAt_apply_apply (hKα hy)]
  have hL0 : 0 ≤ ‖(L : E →L[ℝ] V)‖ ^ 2 := by positivity
  obtain ⟨δ, hδ, hconv⟩ :=
    Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm_sq_le
      (hW.preimage hgc.continuous) hJ'c hX'c hD hK' hDKW' hJsq (mul_nonneg hL0 hA0)
      (mul_nonneg hL0 hB0)
  refine ⟨δ, hδ, fun Ω u E₀ hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  have hus (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : u k z ∈ e.source := (huK k hz).1
  have hx (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : e.symm (e (u k z)) = u k z := e.left_inv (hus k hz)
  have hdiff (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    ((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hz)
  have hcd (k : ℕ) : ContDiffOn ℝ 3 (e ∘ u k) Ω := contMDiffOn_iff_contDiffOn.1 <|
    (contMDiffOn_extChartAt (n := 3)).comp (hu k) fun z hz ↦ by
      rw [mem_preimage, ← extChartAt_source I]
      exact hus k hz
  have hderiv (k : ℕ) (z : ℝ × ℝ) (w : ℝ × ℝ) :
      fderiv ℝ (L ∘ e ∘ u k) z w = L (fderiv ℝ (e ∘ u k) z w) := by
    rw [L.comp_fderiv]
    rfl
  obtain ⟨φ, Z, v', hφ, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim⟩ :=
    hconv (u := fun k ↦ L ∘ e ∘ u k) (f := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)) hΩ hΩD
      (fun k ↦ L.contDiff.comp_contDiffOn (hcd k))
      (fun k z hz ↦ by
        have h := ω.fderiv_extChartAt_comp_stdComplexLineImag_sub (hdiff k hz) (hus k hz)
          (hfl k z hz)
        rw [← he] at h
        simp only [hderiv, J', X', g, comp_apply, Function.comp_apply,
          ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, hXre, hXim]
        rw [← map_sub, ← map_sub, L.symm_apply_apply, h])
      (fun k z hz ↦ ⟨e (u k z), (huK k hz).2, rfl⟩)
      (fun k z hz ↦ floerEnergyDensity_nonneg hω (by
        have h := hJt z (hΩD hz) _ (huK k hz).2
        rwa [hx k hz] at h) (hfl k z hz))
      (fun k z hz ↦ by
        rw [hderiv]
        calc ‖L (fderiv ℝ (e ∘ u k) z stdComplexLineReal)‖ ^ 2
            ≤ (‖(L : E →L[ℝ] V)‖ * ‖fderiv ℝ (e ∘ u k) z stdComplexLineReal‖) ^ 2 := by
              gcongr
              exact (L : E →L[ℝ] V).le_opNorm _
          _ ≤ ‖(L : E →L[ℝ] V)‖ ^ 2 * (A * ω.floerEnergyDensity Ks Kt (u k) z + B) := by
              rw [mul_pow]
              gcongr
              exact hpt (hΩD hz) (hus k hz) (huK k hz).2 (hdiff k hz) (hfl k z hz)
          _ = _ := by ring)
      hint hE
  have hback (k : ℕ) : L.symm ∘ (L ∘ e ∘ u k) = e ∘ u k := funext fun z ↦ by simp
  have hlim' : TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (L.symm ∘ v') atTop (Ω \ ↑Z) := by
    simpa only [ContinuousLinearEquiv.coe_coe, hback] using
      (L.symm : V →L[ℝ] E).uniformContinuous.comp_tendstoLocallyUniformlyOn hlim
  have hvK' : MapsTo (L.symm ∘ v') (Ω \ ↑Z) K := fun z hz ↦ by
    obtain ⟨y, hy, hyv⟩ := hvK hz
    simpa [← hyv] using hy
  refine ⟨φ, Z, L.symm ∘ v', hφ, hZΩ, hcard, hconc, fun C hC hCZ ↦ ?_,
    L.symm.continuous.comp_continuousOn hvc, hvK', hlim', fun z hz ↦ ?_⟩
  · obtain ⟨M', hM'⟩ := hbd C hC hCZ
    refine ⟨‖(L.symm : V →L[ℝ] E)‖ * M', fun n y hy ↦ ?_⟩
    have hd : fderiv ℝ (e ∘ u (φ n)) y =
        (L.symm : V →L[ℝ] E) ∘L fderiv ℝ (L ∘ e ∘ u (φ n)) y := by
      rw [← L.symm.comp_fderiv, hback]
    rw [hd]
    exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (hM' n y hy) (norm_nonneg _))
  · have hzΩ : z ∈ Ω := hz.1
    have hcont := (continuousOn_extChartAt_symm α).continuousWithinAt (hKα (hvK' hz))
    have h := hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim'.tendsto_at hz,
      Eventually.of_forall fun n ↦ e.map_source (hus (φ n) hzΩ)⟩)
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    exact hx (φ n) hzΩ

end SmoothTwoForm

end TauCeti

end

section

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

end

end
