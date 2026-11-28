/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
import TauCeti.Geometry.Symplectic.Floer.Rotation
import TauCeti.Geometry.Symplectic.Floer.Tameness
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Integral.Bochner.PeriodicStrip
import TauCeti.MeasureTheory.Measure.BubblingSet
import TauCeti.Topology.Compactness.Compact

/-!
# Compactness of Floer trajectories in a closed manifold off finitely many bubbling points

Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, such as a closed
symplectic manifold. A Floer trajectory in `M` is a map `u : ℝ × ℝ → M` of period one in `t`,
that is, a map on the cylinder `ℝ × S¹`, solving the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt`. Its energy is
the integral of the Floer energy density over the strip `ℝ × [0, 1)`. Floer cylinders are counted
by the Floer differential, and they are the levels that break off along the ends of a pair of pants.

Compactness off finitely many bubbling points in a closed manifold is known on one compact window
of the domain at a time, with a threshold depending on the window
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`, in the
namespace `TauCeti.SmoothTwoForm`).
This file proves it on the whole cylinder with a single threshold `δ`, for data invariant under the
translations of the domain by the integer points `(m, n)`: there is a subsequence converging off
the translates `Z + (0, n)` of a finite set `Z` in the strip with `#Z * δ ≤ E`. As there, sizes in
`M` are measured through an injective differentiable map `e : M → F` into a normed space, such as
the Whitney embedding, with respect to which the structures are uniformly tame and the Hamiltonian
vector fields are bounded; the solutions converge locally uniformly after applying `e`, and
pointwise in `M`. This is the closed-manifold counterpart of
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`
for a symplectic vector space.

The translate `z ↦ u(z + (m, n))` of a solution solves the same equation
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_add_right`) and has the
translated energy density (`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`), so the
threshold of the window theorem on the closed unit disc serves for the open unit disc about every
integer point. The energy over such a disc is at most twice the energy over the strip
(`TauCeti.setIntegral_ball_intCast_le_two_mul_of_periodic`), and the windows are assembled into one
statement on the cylinder by
`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`, which accounts for the
threshold `δ / 2` of the result. The limit is read back in `M` through `e`
(`IsCompact.exists_tendsto_of_tendsto_comp`).

The two results, in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, are:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_periodic`:
  compactness off finitely many bubbling points on the cylinder, for data invariant under integer
  translations, with the tameness and boundedness constants as hypotheses.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_translates_cylindrical`:
  the case of Floer trajectories, `K = H_t dt` with `J_t` depending on `t` only, both of period
  one; the constants then come from the compactness of `M`.

The convergence is locally uniform. Energy may escape along the cylinder as `s → ±∞`, which is how
broken trajectories arise; that, the bubbles at the points of `Z` and the regularity of the limit
are not treated here.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the compactness of spaces of connecting trajectories.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points).
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

omit [FiniteDimensional ℝ E] [CompactSpace M] in
/-- The Floer energy density of a `C¹` map on the plane is continuous when the Hamiltonian vector
fields of `K_s` and `K_t`, read in the charts of `M`, are `C²`. -/
private theorem continuous_floerEnergyDensity_of_contDiffOn_inChartAt {u : ℝ × ℝ → M}
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (univ ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (univ ×ˢ (extChartAt I α).target))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) : Continuous (ω.floerEnergyDensity Ks Kt u) :=
  continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt isOpen_univ
    hu.contMDiffOn (fun α ↦ (hXs α).continuousOn) fun α ↦ (hXt α).continuousOn)

namespace IsNondegenerate

/-- The windows of
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_periodic`:
for data invariant under integer translations, the threshold `δ` of the closed unit disc serves for
the open unit disc about every integer point `c = (m, n)`. Solutions with energy at most `E₀` over
each of these discs have a subsequence and a finite set `Z` in the unit disc `ball 0 1` such that,
off the translate `Z + c` of `Z`, the energy densities are uniformly bounded on compact subsets of
the disc about `c` and the solutions read through `e` converge locally uniformly there, and energy
at least `δ` concentrates at the points of `Z + c`. -/
private theorem exists_pos_forall_subseq_ball_add_int (hω : ω.IsNondegenerate)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (univ ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (univ ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hKsper : ∀ (m n : ℤ) z, Ks (z + ((m : ℝ), (n : ℝ))) = Ks z)
    (hKtper : ∀ (m n : ℤ) z, Kt (z + ((m : ℝ), (n : ℝ))) = Kt z)
    (hJper : ∀ (m n : ℤ) z, J (z + ((m : ℝ), (n : ℝ))) = J z) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k (m : ℤ × ℤ),
        ∫ z in ball ((m.1 : ℝ), (m.2 : ℝ)) 1, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∀ m : ℤ × ℤ, ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → F), StrictMono ψ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in atTop, δ ≤ ∫ y in ball (z + ((m.1 : ℝ), (m.2 : ℝ))) ε,
          ω.floerEnergyDensity Ks Kt (u (ψ k)) y) ∧
        (∀ C, IsCompact C → C ⊆ (· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
          ∃ A, ∀ k, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (ψ k)) y ≤ A) ∧
        TendstoLocallyUniformlyOn (fun k ↦ e ∘ u (ψ k)) v atTop
          ((· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z)) := by
  -- The compactness theorem on the closed unit disc gives the threshold.
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj isOpen_univ (isCompact_closedBall (0 : ℝ × ℝ) 1) (subset_univ _) hJ hXs hXt
    (fun z _ ↦ hJt z) hc (fun z _ ↦ hJc z) (fun z _ ↦ hBs z) fun z _ ↦ hBt z
  refine ⟨δ, hδ, fun u E₀ hu hfl hE m ↦ ?_⟩
  set c : ℝ × ℝ := ((m.1 : ℝ), (m.2 : ℝ))
  -- The window `z ↦ u k (z + c)` solves the Floer equation, and its energy density is a translate.
  have hflw (k : ℕ) (z : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u k (z + c))) (ω.perturbedMFDeriv Ks Kt (fun y ↦ u k (y + c)) z).toLinearMap := by
    have h := hfl k (z + c)
    rw [hJper m.1 m.2 z] at h
    exact ω.isComplexLinearMap_perturbedMFDeriv_comp_add_right (hKsper m.1 m.2 z)
      (hKtper m.1 m.2 z) h
  have hfw (k : ℕ) (z : ℝ × ℝ) : ω.floerEnergyDensity Ks Kt (fun y ↦ u k (y + c)) z =
      ω.floerEnergyDensity Ks Kt (u k) (z + c) := by
    have h := ω.floerEnergyDensity_comp_add_right Ks Kt (u k) c z
    rwa [funext (hKsper m.1 m.2), funext (hKtper m.1 m.2)] at h
  have hint (k : ℕ) (z : ℝ × ℝ) (ε : ℝ) :
      IntegrableOn (fun y ↦ ω.floerEnergyDensity Ks Kt (u k) (y + c)) (ball z ε) :=
    ((continuous_floerEnergyDensity_of_contDiffOn_inChartAt hXs hXt
      ((hu k).of_le (by norm_num))).comp (continuous_id.add continuous_const)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall z ε)).mono_set
        ball_subset_closedBall
  obtain ⟨ψ, hψ, Z, -, -, hconc, hbd, v, -, hlim, -⟩ :=
    hconv (Ω := ball 0 1) (u := fun k y ↦ u k (y + c)) (E₀ := E₀) isOpen_ball
      ball_subset_closedBall
      (fun k ↦ ((hu k).comp (contDiff_id.add contDiff_const).contMDiff).contMDiffOn)
      (fun k z _ ↦ hflw k z)
      (fun k ↦ (hint k 0 1).congr_fun (fun z _ ↦ (hfw k z).symm) isOpen_ball.measurableSet)
      (fun k ↦ by
        rw [setIntegral_congr_fun isOpen_ball.measurableSet fun z _ ↦ hfw k z,
          setIntegral_ball_comp_add_right, zero_add]
        exact hE k m)
  -- Carry the conclusions back from the window to the plane.
  refine ⟨ψ, Z, fun y ↦ e (v (y - c)), hψ, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun k hk ↦ ?_,
    fun C hC hCZ ↦ ?_, (hlim.comp (· - c) (mapsTo_preimage _ _)
      (continuous_sub_right _).continuousOn).congr fun k y _ ↦ ?_⟩
  · rw [setIntegral_congr_fun (measurableSet_ball.inter isOpen_ball.measurableSet)
      fun y _ ↦ hfw (ψ k) y] at hk
    refine (hk.trans (setIntegral_mono_set (hint _ z ε) (Eventually.of_forall fun y ↦
      floerEnergyDensity_nonneg hω (hJt _ _) (hfl _ _))
      inter_subset_left.eventuallySubset)).trans_eq (setIntegral_ball_comp_add_right _ z c ε)
  · obtain ⟨A, hA⟩ := hbd _ (hC.image (continuous_sub_right c)) (image_subset_iff.2 hCZ)
    refine ⟨A, fun k y hy ↦ ?_⟩
    simpa [hfw] using hA k (y - c) (mem_image_of_mem _ hy)
  · simp

/-- **Floer cylinders in a closed manifold with doubly periodic data converge off finitely many
bubbling points.** Let `ω` be a nondegenerate two-form on a compact boundaryless manifold `M`, let
`e : M → F` be an injective differentiable map into a normed space, and let `K = K_s ds + K_t dt`
and `J(z, x)` be invariant under the translations of the domain by the integer points `(m, n)`.
Let `J(z, x)` and the Hamiltonian vector fields of `K_s` and `K_t`, read in the chart at every
point, be `C²`, with `J(z, x)` tamed by `ω`, uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and the pushforwards `d e (X_{K_s})`, `d e (X_{K_t})` at most
`B`. There is a threshold `δ > 0` with the following property. Let `uₖ : ℝ × ℝ → M` be `C³`
solutions of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)`, of period one in `t` (that
is, maps on the cylinder `ℝ × S¹`), with integrable Floer energy density over the strip
`ℝ × [0, 1)` and Floer energy `∫_{ℝ × [0, 1)} ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E₀`. Then there
are a subsequence `φ`, a finite set `Z` in the strip with `#Z * δ ≤ E₀`, and a map `v` of period
one in `t`, continuous off the translates `Z + (0, n)` of `Z`, such that along `φ`

* every disc about a point of `Z` eventually carries Floer energy at least `δ`;
* the energy densities are uniformly bounded on every compact set disjoint from the translates
  of `Z`;
* the solutions converge to `v` off the translates of `Z`, locally uniformly after applying `e`
  and pointwise in `M`.

No condition is put on the images of the solutions. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_periodic
    (hω : ω.IsNondegenerate) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (univ ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Ks)
      (univ ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α Kt)
      (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x)) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Ks z) x)‖ ≤ B)
    (hBt : ∀ z x, ‖mvfderiv I e x (ω.hamiltonianVectorField (Kt z) x)‖ ≤ B)
    (hKsper : ∀ (m n : ℤ) z, Ks (z + ((m : ℝ), (n : ℝ))) = Ks z)
    (hKtper : ∀ (m n : ℤ) z, Kt (z + ((m : ℝ), (n : ℝ))) = Kt z)
    (hJper : ∀ (m n : ℤ) z, J (z + ((m : ℝ), (n : ℝ))) = J z) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (univ ×ˢ Ico 0 1)) →
      (∀ k, ∫ z in univ ×ˢ Ico 0 1, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧
        (Z : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 1 ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} →
          ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ A) ∧
        ContinuousOn v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        (∀ s t, v (s, t + 1) = v (s, t)) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        ∀ z ∈ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z},
          Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  obtain ⟨δ, hδ, hwin⟩ := hω.exists_pos_forall_subseq_ball_add_int he he_inj hJ hXs hXt hJt hc hJc
    hBs hBt hKsper hKtper hJper
  refine ⟨δ / 2, half_pos hδ, fun u E₀ hu hper hfl hint hE ↦ ?_⟩
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)
  have hf0 (k : ℕ) (y : ℝ × ℝ) : 0 ≤ f k y := floerEnergyDensity_nonneg hω (hJt y _) (hfl k y)
  -- The energy densities are `1`-periodic in `t`.
  have hfk (k : ℕ) (s t : ℝ) : f k (s, t + 1) = f k (s, t) := by
    have hu1 : (fun w ↦ u k (w + (((0 : ℤ) : ℝ), ((1 : ℤ) : ℝ)))) = u k :=
      funext fun ⟨s, t⟩ ↦ by simpa using hper k s t
    have h := ω.floerEnergyDensity_comp_add_right Ks Kt (u k) (((0 : ℤ) : ℝ), ((1 : ℤ) : ℝ)) (s, t)
    rw [funext (hKsper 0 1), funext (hKtper 0 1), hu1] at h
    simpa using h.symm
  -- The energy over the unit disc about each integer point is at most `2 * E₀`, so the windows
  -- apply to every subsequence; they are assembled into one subsequence on the cylinder.
  have hE2 (k : ℕ) (m : ℤ × ℤ) : ∫ z in ball ((m.1 : ℝ), (m.2 : ℝ)) 1, f k z ≤ 2 * E₀ :=
    setIntegral_ball_intCast_le_two_mul_of_periodic (μ := volume) (hf0 k) (hfk k) (hint k) (hE k)
      (m.1 : ℝ) m.2
  obtain ⟨φ, Z, w, hφ, hZ, hcard, hconc, hbd, -, hlim⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic (F := fun k ↦ e ∘ u k)
      hδ hf0 hfk hint hE (fun k s t ↦ by simp [hper])
      (fun k ↦ continuous_floerEnergyDensity_of_contDiffOn_inChartAt hXs hXt
        ((hu k).of_le (by norm_num))) fun m ψ _ ↦ by
        obtain ⟨φ, Z, v, hφ, hconc, hbd, hlim⟩ := hwin (u := fun k ↦ u (ψ k)) (fun k ↦ hu _)
          (fun k ↦ hfl _) (fun k ↦ hE2 _) m
        exact ⟨φ, hφ, Z, v, hconc, hbd, hlim⟩
  -- The limit is read back in `M` through `e`; as a pointwise limit it has period one in `t`.
  have hec : Continuous e := continuous_iff_continuousAt.2 fun x ↦ (he x).continuousAt
  have hw : ContinuousOn w {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} :=
    hlim.continuousOn (Frequently.of_forall fun n ↦ (hec.comp (hu (φ n)).continuous).continuousOn)
  obtain ⟨v, hv, -, hev, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp hec.continuousOn
    he_inj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) hw fun z hz ↦ hlim.tendsto_at hz
  have : T2Space M := .of_injective_continuous he_inj hec
  have : Nonempty M := ⟨u 0 0⟩
  have hvv : EqOn (fun y ↦ limUnder atTop fun n ↦ u (φ n) y) v
      {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} := fun y hy ↦ (hpt y hy).limUnder_eq
  refine ⟨φ, Z, fun y ↦ limUnder atTop fun n ↦ u (φ n) y, hφ, hZ, by linarith,
    fun z hz ε hε ↦ (hconc z hz ε hε).mono fun n hn ↦ (half_le_self hδ.le).trans hn, hbd,
    hv.congr hvv, fun s t ↦ by simp only [hper], hlim.congr_right fun y hy ↦ ?_,
    fun y hy ↦ hvv hy ▸ hpt y hy⟩
  simp only [comp_apply, hvv hy]
  exact (hev hy).symm

/-- **Floer trajectories in a closed manifold converge off finitely many bubbling points.** Let `ω`
be a nondegenerate two-form on a compact boundaryless manifold `M`, let `H` be a `C³` Hamiltonian
of period one in time, and let `J_t(x)` be almost complex structures on the tangent spaces of `M`,
of period one in `t`, tamed by `ω` and `C²` in the charts of `M`. Let `e : M → F` be an injective
`C¹` map into a normed space, such as the Whitney embedding. There is a threshold `δ > 0` with the
following property. Let `uₖ : ℝ × ℝ → M` be `C³` solutions of the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0`, of period one in `t` (that is, Floer cylinders
`ℝ × S¹ → M`), with integrable Floer energy density over the strip `ℝ × [0, 1)` and Floer energy
over it at most `E₀`. Then there are a subsequence `φ`, a finite set `Z` in the strip with
`#Z * δ ≤ E₀`, and a map `v` of period one in `t`, continuous off the translates `Z + (0, n)` of
`Z`, such that along `φ` every disc about a point of `Z` eventually carries Floer energy at least
`δ`, the energy densities are uniformly bounded on every compact set disjoint from the translates
of `Z`, and the solutions converge to `v` off the translates of `Z`, locally uniformly after
applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_translates_cylindrical
    (hω : ω.IsNondegenerate) {H : ℝ → M → ℝ}
    {J : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ∀ α, ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α J)
      (univ ×ˢ (extChartAt I α).target))
    (hJper : Periodic J 1) (hJt : ∀ t x, (hω.symplecticFormAt x).Tames (J t x))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄, (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k))
        (univ ×ˢ Ico 0 1)) →
      (∀ k, ∫ z in univ ×ˢ Ico 0 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧
        (Z : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 1 ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤
          ∫ y in ball z ε, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} →
          ∃ A, ∀ n, ∀ y ∈ C,
            ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u (φ n)) y ≤ A) ∧
        ContinuousOn v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        (∀ s t, v (s, t + 1) = v (s, t)) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        ∀ z ∈ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z},
          Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- The data `J_t`, `H_t dt` as functions of `(s, t)`, read in the charts of `M`.
  have hp : ContDiff ℝ 2 fun p : (ℝ × ℝ) × E ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have hJ' (α : M) : ContDiffOn ℝ 2 (Floer.almostComplexInChartAt I α fun z : ℝ × ℝ ↦ J z.2)
      (univ ×ˢ (extChartAt I α).target) := by
    rw [funext (Floer.almostComplexInChartAt_comp (I := I) (α := α) (J := J) Prod.snd)]
    exact (hJ α).comp hp.contDiffOn fun p hp ↦ ⟨mem_univ _, hp.2⟩
  have hX (α : M) : ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α fun z : ℝ × ℝ ↦ H z.2)
      (univ ×ˢ (extChartAt I α).target) :=
    hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (fun _ _ _ ↦ (hH.comp
      ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)).contMDiffAt) α
  -- One tameness constant serves the circle `{0} × [0, 1]`, hence every `t` by periodicity.
  obtain ⟨c, hc, hJc⟩ := hω.exists_pos_forall_mul_norm_mvfderiv_sq_le
    (J := fun z : ℝ × ℝ ↦ J z.2) (isCompact_singleton.prod (isCompact_Icc (a := 0) (b := 1)))
    isCompact_univ (fun α _ ↦ (hJ' α).continuousOn.mono (prod_mono (subset_univ _) subset_rfl))
    (fun z _ x _ ↦ hJt z.2 x) he
  have hJc' (z : ℝ × ℝ) (x : M) (v : TangentSpace I x) :
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z.2 x v) := by
    obtain ⟨t, ht, heq⟩ := hJper.exists_mem_Ico₀ one_pos z.2
    rw [heq]
    exact hJc (0, t) ⟨rfl, Ico_subset_Icc_self ht⟩ x (mem_univ x) v
  obtain ⟨B, hB⟩ := hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
    (hH.of_le (by norm_num)) hHper he
  have hBs (x : M) : ‖mvfderiv I e x (ω.hamiltonianVectorField (fun _ ↦ 0) x)‖ ≤ max B 0 := by
    rw [hamiltonianVectorField_const, Pi.zero_apply, map_zero, norm_zero]
    exact le_max_right B 0
  exact exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_periodic
    (Ks := fun _ _ ↦ 0) (Kt := fun z ↦ H z.2) (J := fun z ↦ J z.2) hω
    (he.mdifferentiable one_ne_zero) he_inj hJ'
    (fun α ↦ by rw [hamiltonianVectorFieldInChartAt_zero]; exact contDiffOn_const) hX
    (fun z ↦ hJt z.2) hc hJc' (B := max B 0) (fun _ ↦ hBs)
    (fun z x ↦ (hB z.2 x).trans (le_max_left _ _)) (fun _ _ _ ↦ rfl)
    (fun _ n z ↦ by simpa using hHper.int_mul n z.2)
    (fun _ n z ↦ by simpa using hJper.int_mul n z.2)

end IsNondegenerate

end TauCeti.SmoothTwoForm
