/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Integral.Bochner.PeriodicStrip
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.MetricSpace.Pseudo.Prod
import TauCeti.Topology.Order.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of Floer trajectories off finitely many bubbling points

A Floer trajectory is a map from the cylinder `ℝ × S¹` to `V`, which we write as a map
`u : ℝ × ℝ → V` that is `1`-periodic in `t`, solving the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt` and almost
complex structures `J_t`, both `1`-periodic in `t`. Its energy is the integral of the Floer energy
density over the fundamental strip `ℝ × [0, 1)`. Such cylinders are counted by the Floer
differential, and they break off at the ends of a pair of pants. The compactness theorem
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` applies on
one compact window `D` of the domain, with an energy threshold `δ` depending on `D`. Applying it on
larger and larger windows gives thresholds that may tend to `0`, and hence no bound on the number of
bubbling points over the whole cylinder. This file proves compactness on the whole cylinder with a
single threshold, for data invariant under the translations of the domain by the integer points
`(m, n)`. The data of a Floer trajectory are such: they do not depend on `s` and are `1`-periodic
in `t`.

The translate `z ↦ u(z + (m, n))` of a solution solves the same equation
(`TauCeti.SymplecticForm.perturbedFDeriv_comp_add_right`), and its energy over the unit disc is at
most twice the energy over the strip (`TauCeti.setIntegral_ball_le_two_mul_of_periodic`), so the
threshold of the closed unit disc serves for each of its integer translates, and the open unit
discs about the integer points cover the plane (`Prod.dist_round_le`). A diagonal extraction
(`TauCeti.extraction_forall_of_antitone`) gives one subsequence that converges on each of these
countably many discs off finitely many bubbling points. Floer energy at least `δ` concentrates at
each bubbling point, and the set of such concentration points is invariant under the period
`(0, 1)` (`TauCeti.forall_eventually_le_setIntegral_ball_toIcoMod_of_periodic`), so it is
determined by its points in the fundamental strip. There are at most `2E / δ` of
them (`TauCeti.card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic`,
`TauCeti.finite_of_forall_eventually_le_setIntegral_ball_of_periodic`), so the theorems state the
threshold `δ / 2`. Off their translates the limit is the pointwise limit, which on each disc is
the limit given by that disc, and which is again `1`-periodic in `t`.

The two results, in the namespace `TauCeti.SymplecticForm`, are:

* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`: compactness off
  finitely many bubbling points on the cylinder, for data invariant under integer translations.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_translates_cylindrical`: the case
  of Floer trajectories, `K = H_t dt` with `J_t` depending on `t` only.

For a single compact window of height at most one, the compactness of Floer cylinders, with a
threshold depending on the window, is
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical`.

The convergence is locally uniform. Energy may escape along the cylinder as `s → ±∞`, which is
how broken trajectories arise; that, the bubbles at the points of the bubbling set, and the
regularity of the limit are not treated here.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the compactness of spaces of connecting trajectories.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points).
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}

/-- The windows of `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`:
for data invariant under integer translations, the threshold `δ` of the closed unit disc serves for
the open unit disc about every integer point `c = (m, n)`. Solutions with energy at most `E` over
each of these discs have a subsequence and a finite set `Z` in the unit disc `ball 0 1` such that,
off the translate `Z + c` of `Z`, the differentials are uniformly bounded on compact subsets of the
disc about `c` and the solutions converge locally uniformly there, and energy at least `δ`
concentrates at the points of `Z + c`. -/
private lemma exists_pos_forall_subseq_ball_add_int (ω : SymplecticForm V) {K : Set V}
    (hKs : ContDiff ℝ 3 (uncurry Ks)) (hKt : ContDiff ℝ 3 (uncurry Kt))
    (hJ : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hK : IsCompact K) (hJt : ∀ z, ∀ x ∈ K, ω.Tames (J z x))
    (hKsper : ∀ (m n : ℤ) z, Ks (z + ((m : ℝ), (n : ℝ))) = Ks z)
    (hKtper : ∀ (m n : ℤ) z, Kt (z + ((m : ℝ), (n : ℝ))) = Kt z)
    (hJper : ∀ (m n : ℤ) z, J (z + ((m : ℝ), (n : ℝ))) = J z) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k z, u k z ∈ K) →
      (∀ k (m n : ℤ), ∫ z in ball ((m : ℝ), (n : ℝ)) 1, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∀ m n : ℤ, ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in atTop, δ ≤
          ∫ y in ball (z + ((m : ℝ), (n : ℝ))) ε, ω.floerEnergyDensity Ks Kt (u (ψ k)) y) ∧
        (∀ C, IsCompact C → C ⊆ (· - ((m : ℝ), (n : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
          ∃ M, ∀ k, ∀ y ∈ C, ‖fderiv ℝ (u (ψ k)) y‖ ≤ M) ∧
        TendstoLocallyUniformlyOn (fun k ↦ u (ψ k)) v atTop
          ((· - ((m : ℝ), (n : ℝ))) ⁻¹' (ball 0 1 \ ↑Z)) := by
  -- The compactness theorem on the closed unit disc gives the threshold.
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    isOpen_univ hKs.contDiffOn hKt.contDiffOn hJ.contDiffOn (isCompact_closedBall 0 1) hK
    (subset_univ _) fun z _ x hx ↦ hJt z x hx
  refine ⟨δ, hδ, fun u E hu hfl huK hE m n ↦ ?_⟩
  set c : ℝ × ℝ := ((m : ℝ), (n : ℝ))
  -- The window `z ↦ u k (z + c)` solves the Floer equation, and its energy density is a translate.
  have hKs' : (fun z ↦ Ks (z + c)) = Ks := funext (hKsper m n)
  have hKt' : (fun z ↦ Kt (z + c)) = Kt := funext (hKtper m n)
  have hflw (k : ℕ) (z : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u k (z + c))) (ω.perturbedFDeriv Ks Kt (fun y ↦ u k (y + c)) z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := ω.perturbedFDeriv_comp_add_right Ks Kt (u k) c z
    rw [hKs', hKt'] at h
    rw [h, ← hJper m n z]
    exact hfl k (z + c)
  have hfw (k : ℕ) (z : ℝ × ℝ) : ω.floerEnergyDensity Ks Kt (fun y ↦ u k (y + c)) z =
      ω.floerEnergyDensity Ks Kt (u k) (z + c) := by
    have h := ω.floerEnergyDensity_comp_add_right Ks Kt (u k) c z
    rwa [hKs', hKt'] at h
  have hint (k : ℕ) (z : ℝ × ℝ) (ε : ℝ) :
      IntegrableOn (fun y ↦ ω.floerEnergyDensity Ks Kt (u k) (y + c)) (ball z ε) :=
    ((continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
      ((hu k).of_le (by norm_num)).contDiffOn (hKs.of_le (by norm_num)).contDiffOn
      (hKt.of_le (by norm_num)).contDiffOn)).comp (continuous_id.add continuous_const)
      |>.continuousOn.integrableOn_compact (isCompact_closedBall z ε)).mono_set
        ball_subset_closedBall
  obtain ⟨ψ, Z, v, hψ, -, -, hconc, hbd, -, -, hlim⟩ :=
    hconv (Ω := ball 0 1) (u := fun k y ↦ u k (y + c)) (E := E) isOpen_ball
      ball_subset_closedBall (fun k ↦ ((hu k).comp (contDiff_id.add contDiff_const)).contDiffOn)
      (fun k z _ ↦ hflw k z) (fun k z _ ↦ huK k _)
      (fun k ↦ (hint k 0 1).congr_fun (fun z _ ↦ (hfw k z).symm) isOpen_ball.measurableSet)
      (fun k ↦ by
        rw [setIntegral_congr_fun isOpen_ball.measurableSet fun z _ ↦ hfw k z,
          setIntegral_ball_comp_add_right, zero_add]
        exact hE k m n)
  -- Carry the conclusions back from the window to the plane.
  refine ⟨ψ, Z, fun y ↦ v (y - c), hψ, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun k hk ↦ ?_,
    fun C hC hCZ ↦ ?_, (hlim.comp (· - c) (mapsTo_preimage _ _)
      (continuous_sub_right _).continuousOn).congr fun k y _ ↦ ?_⟩
  · rw [setIntegral_congr_fun (measurableSet_ball.inter isOpen_ball.measurableSet)
      fun y _ ↦ hfw (ψ k) y] at hk
    refine (hk.trans (setIntegral_mono_set (hint _ z ε) (Eventually.of_forall fun y ↦
      ω.floerEnergyDensity_nonneg (hJt _ _ (huK _ _)) (hfl _ _))
      inter_subset_left.eventuallySubset)).trans_eq (setIntegral_ball_comp_add_right _ z c ε)
  · obtain ⟨M, hM⟩ := hbd _ (hC.image (continuous_sub_right c)) (image_subset_iff.2 hCZ)
    refine ⟨M, fun k y hy ↦ ?_⟩
    simpa [fderiv_comp_add_right] using hM k (y - c) (mem_image_of_mem _ hy)
  · simp

/-- A diagonal extraction over the windows of
`exists_pos_forall_subseq_ball_add_int`: solutions with energy at most `E` over the open unit disc
about every integer point `m` have one subsequence `φ` such that, for every `m`, the conclusions of
that lemma hold eventually along `φ` for some finite set `Z` in `ball 0 1`. -/
private lemma exists_pos_forall_subseq_forall_ball_add_int (ω : SymplecticForm V) {K : Set V}
    (hKs : ContDiff ℝ 3 (uncurry Ks)) (hKt : ContDiff ℝ 3 (uncurry Kt))
    (hJ : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hK : IsCompact K) (hJt : ∀ z, ∀ x ∈ K, ω.Tames (J z x))
    (hKsper : ∀ (m n : ℤ) z, Ks (z + ((m : ℝ), (n : ℝ))) = Ks z)
    (hKtper : ∀ (m n : ℤ) z, Kt (z + ((m : ℝ), (n : ℝ))) = Kt z)
    (hJper : ∀ (m n : ℤ) z, J (z + ((m : ℝ), (n : ℝ))) = J z) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k z, u k z ∈ K) →
      (∀ k (m n : ℤ), ∫ z in ball ((m : ℝ), (n : ℝ)) 1, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℤ × ℤ, ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in map φ atTop, δ ≤
          ∫ y in ball (z + ((m.1 : ℝ), (m.2 : ℝ))) ε, ω.floerEnergyDensity Ks Kt (u k) y) ∧
        (∀ C, IsCompact C → C ⊆ (· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
          ∃ M, ∀ᶠ k in map φ atTop, ∀ y ∈ C, ‖fderiv ℝ (u k) y‖ ≤ M) ∧
        TendstoLocallyUniformlyOn u v (map φ atTop)
          ((· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z)) := by
  obtain ⟨δ, hδ, hwin⟩ :=
    exists_pos_forall_subseq_ball_add_int ω hKs hKt hJ hK hJt hKsper hKtper hJper
  refine ⟨δ, hδ, fun u E hu hfl huK hE ↦ ?_⟩
  -- On each window, every subsequence has a further subsequence converging off finitely many
  -- bubbling points, and these properties pass to finer filters. Enumerate the windows.
  set e : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm
  let P : ℕ → Filter ℕ → Prop := fun j l ↦ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in l, δ ≤
        ∫ y in ball (z + (((e j).1 : ℝ), ((e j).2 : ℝ))) ε, ω.floerEnergyDensity Ks Kt (u k) y) ∧
      (∀ C, IsCompact C → C ⊆ (· - (((e j).1 : ℝ), ((e j).2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
        ∃ M, ∀ᶠ k in l, ∀ y ∈ C, ‖fderiv ℝ (u k) y‖ ≤ M) ∧
      TendstoLocallyUniformlyOn u v l ((· - (((e j).1 : ℝ), ((e j).2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z))
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_antitone (P := P)
    (fun j _ _ hl ⟨Z, v, hconc, hbd, hlim⟩ ↦ ⟨Z, v,
      fun z hz ε hε ↦ (hconc z hz ε hε).filter_mono hl,
      fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hM ↦ hM.filter_mono hl,
      hlim.comp_tendsto (tendsto_id'.2 hl)⟩) fun j ψ _ ↦ by
      obtain ⟨ψ', Z, v, hψ', hconc, hbd, hlim⟩ := hwin (u := fun k ↦ u (ψ k)) (fun k ↦ hu _)
        (fun k ↦ hfl _) (fun k ↦ huK _) (fun k ↦ hE _) (e j).1 (e j).2
      exact ⟨ψ', hψ', Z, v, fun z hz ε hε ↦ eventually_map.2 (hconc z hz ε hε),
        fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hM ↦ eventually_map.2 (Eventually.of_forall hM),
        tendstoLocallyUniformlyOn_map_iff.2 hlim⟩
  refine ⟨φ, hφ, fun m ↦ ?_⟩
  simpa only [P, Equiv.apply_symm_apply] using hP (e.symm m)

/-- **Floer cylinders with doubly periodic data converge off finitely many bubbling points.** Let
`K = K_s ds + K_t dt` be `C³` and `J(z, x)` be `C²` on `(ℝ × ℝ) × V`, invariant under the
translations of the domain by the integer points `(m, n)`, with `J(z, x)` tamed by `ω` for `x` in a
compact set `K`. There is a threshold `δ > 0` with the following property. Let `uₖ : ℝ × ℝ → V` be
`C³` solutions of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)`, `1`-periodic in `t` (that
is, maps on the cylinder `ℝ × S¹`), with image in `K` and Floer energy
`∫_{ℝ × [0, 1)} ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E`. Then there are a subsequence `φ`, a finite
set `Z` in the strip `ℝ × [0, 1)` with `#Z * δ ≤ E`, and a continuous `v`, `1`-periodic in `t` and
with values in `K`, off the translates `Z + (0, n)` of `Z`, such that along `φ` every disc about a
point of `Z` eventually carries Floer energy at least `δ`, the differentials are uniformly bounded
on every compact set disjoint from the translates of `Z`, and `u_{φ n} → v` locally uniformly off
the translates of `Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic
    (ω : SymplecticForm V) {K : Set V}
    (hKs : ContDiff ℝ 3 (uncurry Ks)) (hKt : ContDiff ℝ 3 (uncurry Kt))
    (hJ : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hK : IsCompact K) (hJt : ∀ z, ∀ x ∈ K, ω.Tames (J z x))
    (hKsper : ∀ (m n : ℤ) z, Ks (z + ((m : ℝ), (n : ℝ))) = Ks z)
    (hKtper : ∀ (m n : ℤ) z, Kt (z + ((m : ℝ), (n : ℝ))) = Kt z)
    (hJper : ∀ (m n : ℤ) z, J (z + ((m : ℝ), (n : ℝ))) = J z) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k z, u k z ∈ K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) (univ ×ˢ Ico 0 1)) →
      (∀ k, ∫ z in univ ×ˢ Ico 0 1, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        (Z : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 1 ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        MapsTo v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} K ∧
        (∀ s t, v (s, t + 1) = v (s, t)) ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop
          {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} := by
  obtain ⟨δ, hδ, hdiag⟩ :=
    exists_pos_forall_subseq_forall_ball_add_int ω hKs hKt hJ hK hJt hKsper hKtper hJper
  refine ⟨δ / 2, half_pos hδ, fun u E hu hper hfl huK hint hE ↦ ?_⟩
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)
  set S : Set (ℝ × ℝ) := univ ×ˢ Ico 0 1
  have hf0 (k : ℕ) (y : ℝ × ℝ) : 0 ≤ f k y :=
    ω.floerEnergyDensity_nonneg (hJt y _ (huK k y)) (hfl k y)
  -- The energy densities are `1`-periodic in `t`.
  have hfk (k : ℕ) (s t : ℝ) : f k (s, t + 1) = f k (s, t) := by
    have h : Periodic (f k) (0, 1) := ω.periodic_floerEnergyDensity
      (fun w ↦ by simpa using hKsper 0 1 w) (fun w ↦ by simpa using hKtper 0 1 w)
      fun ⟨s, t⟩ ↦ by simpa using hper k s t
    simpa using h (s, t)
  have hk (k : ℕ) : IntegrableOn (f k) (univ ×ˢ Ico 0 (0 + 1)) := by simpa using hint k
  have hEk (k : ℕ) : ∫ z in univ ×ˢ Ico 0 (0 + 1), f k z ≤ E := by simpa using hE k
  have hS : S ⊆ univ ×ˢ Ico 0 (0 + 1) := by rw [zero_add]
  -- The energy over the unit disc about each integer point is at most `2 * E`, so one subsequence
  -- converges on all of these windows.
  have hE2 (k : ℕ) (m n : ℤ) : ∫ z in ball ((m : ℝ), (n : ℝ)) 1, f k z ≤ 2 * E := by
    have h := setIntegral_ball_le_two_mul_of_periodic (μ := volume) (hf0 k) (hfk k) (hk k) (m : ℝ) n
    rw [zero_add, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hEk k) two_pos.le)
  obtain ⟨φ, hφ, hP⟩ := hdiag hu hfl huK hE2
  choose Z v hconc hbd hlim using hP
  set l : Filter ℕ := map φ atTop
  set c : ℤ × ℤ → ℝ × ℝ := fun m ↦ ((m.1 : ℝ), (m.2 : ℝ))
  -- The bubbling points of all windows, and the good parts of the windows, in the plane.
  set Zall : Set (ℝ × ℝ) := ⋃ m, (· + c m) '' (Z m : Set (ℝ × ℝ))
  set G : ℤ × ℤ → Set (ℝ × ℝ) := fun m ↦ (· - c m) ⁻¹' (ball 0 1 \ ↑(Z m))
  -- The points at which energy at least `δ` concentrates; finitely many lie in the strip `S`.
  set Zc : Set (ℝ × ℝ) := {y | ∀ ε > 0, ∀ᶠ k in l, δ ≤ ∫ y' in ball y ε, f k y'}
  have hfin : (Zc ∩ S).Finite :=
    finite_of_forall_eventually_le_setIntegral_ball_of_periodic (μ := volume) (l := l) hδ hf0
      hfk hk hEk (inter_subset_right.trans hS) fun z hz ↦ hz.1
  -- Each bubbling point is a translate of one of them, since concentration is periodic in `t`.
  have hgood : {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ hfin.toFinset} ⊆ Zallᶜ := by
    intro y hy hyZ
    obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.1 hyZ
    have h := forall_eventually_le_setIntegral_ball_toIcoMod_of_periodic (μ := volume) (a := 0)
      zero_lt_one hfk (hconc m z hz)
    rw [toIcoMod_zero_one] at h
    exact hy (hfin.mem_toFinset.2 ⟨h, mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩)
  -- The good parts of the windows are open and cover the complement of `Zall`: the integer point
  -- nearest to `y` is at distance at most `1 / 2`.
  have hGopen (m : ℤ × ℤ) : IsOpen (G m) :=
    (isOpen_ball.sdiff (Z m).finite_toSet.isClosed).preimage (continuous_sub_right _)
  have hcover (y : ℝ × ℝ) (hy : y ∉ Zall) : ∃ m, y ∈ G m := by
    have hm : y - c (round y.1, round y.2) ∈ ball 0 1 := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact (Prod.dist_round_le y).trans_lt (by norm_num)
    exact ⟨_, hm, fun hZ ↦ hy (mem_iUnion.2 ⟨_, _, hZ, sub_add_cancel _ _⟩)⟩
  -- The limits of the windows glue to the pointwise limit, off the translates of `Zc ∩ S`.
  set v' : ℝ × ℝ → V := fun y ↦ limUnder l fun k ↦ u k y
  have hlimv : TendstoLocallyUniformlyOn u v' l {y | (y.1, Int.fract y.2) ∉ hfin.toFinset} :=
    (tendstoLocallyUniformlyOn_iUnion_limUnder hGopen hlim).mono fun y hy ↦
      mem_iUnion.2 (hcover y (hgood hy))
  refine ⟨φ, hfin.toFinset, v', hφ, fun z hz ↦ (hfin.mem_toFinset.1 hz).2, ?_,
    fun z hz ε hε ↦ (eventually_map.1 ((hfin.mem_toFinset.1 hz).1 ε hε)).mono fun n hn ↦
      (half_le_self hδ.le).trans hn, fun C hC hCZ ↦ ?_,
    hlimv.continuousOn (Frequently.of_forall fun k ↦ (hu k).continuous.continuousOn),
    fun y hy ↦ hK.isClosed.mem_of_tendsto (hlimv.tendsto_at hy)
      (Eventually.of_forall fun k ↦ huK k y),
    fun s t ↦ by simp only [v', hper],
    hlimv.comp_tendsto tendsto_map⟩
  · have h := card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic
      (μ := volume) (l := l) hf0 hfk hk hEk (Z := hfin.toFinset)
      (fun z hz ↦ hS (hfin.mem_toFinset.1 hz).2) fun z hz ↦ (hfin.mem_toFinset.1 hz).1
    linarith
  -- Each point of `C` has a closed disc in the good part of some window, on which the
  -- differentials are eventually bounded.
  refine hC.exists_forall_le_of_eventually_nhds
    (fun n ↦ ((hu (φ n)).continuous_fderiv (by norm_num)).norm.continuousOn) fun x hx ↦ ?_
  obtain ⟨m, hm⟩ := hcover x (hgood (hCZ hx))
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.1 ((hGopen m).mem_nhds hm)
  obtain ⟨M, hM⟩ := hbd m _ (isCompact_closedBall _ _) hsub
  exact ⟨closedBall x r, closedBall_mem_nhds x hr, M, eventually_map.1 hM⟩

/-- **Floer trajectories converge off finitely many bubbling points.** Let `H` be a `C³`
Hamiltonian, `1`-periodic in time, and `J_t(x)` a `C²` family of almost complex structures,
`1`-periodic in `t` and tamed by `ω` on a compact set `K`. There is a threshold `δ > 0` with the
following property. Let `uₖ : ℝ × ℝ → V` be `C³` solutions of the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0`, `1`-periodic in `t` (that is, Floer cylinders
`ℝ × S¹ → V`), with image in `K` and Floer energy over the strip `ℝ × [0, 1)` at most `E`. Then
there are a subsequence `φ`, a finite set `Z` in the strip `ℝ × [0, 1)` with `#Z * δ ≤ E`, and a
continuous `v`, `1`-periodic in `t` and with values in `K`, off the translates `Z + (0, n)` of `Z`,
such that along `φ` every disc about a point of `Z` eventually carries Floer energy at least `δ`,
the differentials are uniformly bounded on every compact set disjoint from the translates of `Z`,
and `u_{φ n} → v` locally uniformly off the translates of `Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_translates_cylindrical
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V} {K : Set V}
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k s t, u k (s, t + 1) = u k (s, t)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k z, u k z ∈ K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k))
        (univ ×ˢ Ico 0 1)) →
      (∀ k, ∫ z in univ ×ˢ Ico 0 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        (Z : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 1 ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤
          ∫ y in ball z ε, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} ∧
        MapsTo v {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} K ∧
        (∀ s t, v (s, t + 1) = v (s, t)) ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop
          {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} :=
  have hp : ContDiff ℝ ⊤ fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic (J := fun z ↦ J z.2)
    contDiff_const (hH.comp (hp.of_le le_top)) (hJ.comp (hp.of_le le_top)) hK
    (fun z ↦ hJt z.2) (fun _ _ _ ↦ rfl) (fun _ n z ↦ by simpa using hHper.int_mul n z.2)
    fun _ n z ↦ by simpa using hJper.int_mul n z.2

end TauCeti.SymplecticForm
