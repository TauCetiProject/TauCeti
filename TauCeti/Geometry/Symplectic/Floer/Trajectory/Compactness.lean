/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Order.Filter.AtTopBot

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
most the energy over two periods of the strip, so the threshold of the closed unit disc serves for
each of its integer translates, and the open unit discs about the integer points cover the plane. A
diagonal extraction (`TauCeti.extraction_forall_of_antitone`) gives one subsequence that converges
on each of these countably many discs off finitely many bubbling points. Floer energy at least `δ`
concentrates at each bubbling point, and the set of such concentration points is invariant under
the period `(0, 1)`, so it is determined by its points in the fundamental strip. There are at most
`2E / δ` of them (`TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`), so the theorems
state the threshold `δ / 2`. Off their translates the limit is the pointwise limit, which on each
disc is the limit given by that disc, and which is again `1`-periodic in `t`.

* `SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`:
  compactness off finitely many bubbling points on the cylinder, for data invariant under integer
  translations.
* `SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical`:
  the case of Floer trajectories, `K = H_t dt` with `J_t` depending on `t` only.

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
  set B : Set (ℝ × ℝ) := ball 0 1 with hB
  -- The compactness theorem on the closed unit disc gives the threshold.
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    isOpen_univ hKs.contDiffOn hKt.contDiffOn hJ.contDiffOn (isCompact_closedBall 0 1) hK
    (subset_univ _) fun z _ x hx ↦ hJt z x hx
  refine ⟨δ / 2, half_pos hδ, fun u E hu hper hfl huK hint hE ↦ ?_⟩
  -- The windows: the translates of `u` by the integer points `c j`, read on the unit disc `B`.
  set e : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm
  set c : ℕ → ℝ × ℝ := fun j ↦ (((e j).1 : ℝ), ((e j).2 : ℝ)) with hc
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)
  set S : Set (ℝ × ℝ) := univ ×ˢ Ico 0 1 with hS
  set W : Set (ℝ × ℝ) := univ ×ˢ Ico (-1) 1 with hW
  have hf0 (k : ℕ) (y : ℝ × ℝ) : 0 ≤ f k y :=
    ω.floerEnergyDensity_nonneg (hJt y _ (huK k y)) (hfl k y)
  have hfc (k : ℕ) : Continuous (f k) :=
    continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
      ((hu k).of_le (by norm_num)).contDiffOn (hKs.of_le (by norm_num)).contDiffOn
      (hKt.of_le (by norm_num)).contDiffOn)
  have hintball {g : ℝ × ℝ → ℝ} (hg : Continuous g) (z : ℝ × ℝ) (ε : ℝ) :
      IntegrableOn g (ball z ε) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall z ε)).mono_set
      ball_subset_closedBall
  have hfa (k : ℕ) (a : ℝ × ℝ) : Continuous fun z ↦ f k (z + a) :=
    (hfc k).comp (continuous_id.add continuous_const)
  have hKsc (j : ℕ) : (fun z ↦ Ks (z + c j)) = Ks := funext fun z ↦ hKsper _ _ z
  have hKtc (j : ℕ) : (fun z ↦ Kt (z + c j)) = Kt := funext fun z ↦ hKtper _ _ z
  have hmp (a : ℝ × ℝ) : MeasurePreserving (· + a) (volume : Measure (ℝ × ℝ)) volume :=
    (measurePreserving_add_right volume a.1).prod (measurePreserving_add_right volume a.2)
  -- The windows solve the Floer equation, and their energy densities are translates.
  have hflw (j k : ℕ) (z : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u k (z + c j)))
      (ω.perturbedFDeriv Ks Kt (fun y ↦ u k (y + c j)) z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := ω.perturbedFDeriv_comp_add_right Ks Kt (u k) (c j) z
    rw [hKsc, hKtc] at h
    rw [h, ← hJper (e j).1 (e j).2 z]
    exact hfl k (z + c j)
  have hfw (j k : ℕ) (z : ℝ × ℝ) :
      ω.floerEnergyDensity Ks Kt (fun y ↦ u k (y + c j)) z = f k (z + c j) := by
    have h := ω.floerEnergyDensity_comp_add_right Ks Kt (u k) (c j) z
    rwa [hKsc, hKtc] at h
  have hintw (j k : ℕ) : IntegrableOn (fun z ↦ f k (z + c j)) B :=
    hintball (hfa k (c j)) 0 1
  -- The energy densities are `1`-periodic in `t`.
  have hfper (k : ℕ) (n : ℤ) (y : ℝ × ℝ) : f k (y + (0, (n : ℝ))) = f k y := by
    have hKs0 : (fun w ↦ Ks (w + (0, (n : ℝ)))) = Ks := funext fun w ↦ by simpa using hKsper 0 n w
    have hKt0 : (fun w ↦ Kt (w + (0, (n : ℝ)))) = Kt := funext fun w ↦ by simpa using hKtper 0 n w
    have hu0 : (fun w ↦ u k (w + (0, (n : ℝ)))) = u k := funext fun w ↦ by
      obtain ⟨s, t⟩ := w
      simpa using (show Periodic (fun t ↦ u k (s, t)) 1 from hper k s).int_mul n t
    have h := ω.floerEnergyDensity_comp_add_right Ks Kt (u k) (0, (n : ℝ)) y
    rw [hKs0, hKt0, hu0] at h
    exact h.symm
  -- Translating a ball does not change the energy over it.
  have hball (a : ℝ × ℝ) (k : ℕ) (z : ℝ × ℝ) (ε : ℝ) :
      ∫ y in ball z ε, f k (y + a) = ∫ y in ball (z + a) ε, f k y := by
    have h : ball z ε = (· + a) ⁻¹' ball (z + a) ε := by
      ext y
      simp
    rw [h]
    exact (hmp a).setIntegral_preimage_emb (measurableEmbedding_addRight a) (f k) _
  -- The energy over two periods of the strip is at most `2 * E`.
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ico
  have hWm : MeasurableSet W := MeasurableSet.univ.prod measurableSet_Ico
  have hWint (k : ℕ) : IntegrableOn (f k) W ∧ ∫ y in W, f k y ≤ 2 * E := by
    have hpre : (· + ((0 : ℝ), (1 : ℝ))) ⁻¹' S = univ ×ˢ Ico (-1) 0 := by
      ext y
      simp only [hS, mem_preimage, mem_prod, mem_univ, mem_Ico, Prod.snd_add, true_and]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hf1 : (fun y ↦ f k (y + ((0 : ℝ), (1 : ℝ)))) = f k :=
      funext fun y ↦ by simpa using hfper k 1 y
    have hemb := measurableEmbedding_addRight ((0 : ℝ), (1 : ℝ))
    have h1 : IntegrableOn (f k) (univ ×ˢ Ico (-1) 0) := by
      rw [← hpre, ← hf1]
      exact ((hmp _).integrableOn_comp_preimage hemb).2 (hint k)
    have h2 : ∫ y in univ ×ˢ Ico (-1) 0, f k y = ∫ y in S, f k y := by
      rw [← hpre, ← (hmp _).setIntegral_preimage_emb hemb (f k) S, hf1]
    have hWu : W = univ ×ˢ Ico (-1) 0 ∪ S := by
      rw [hW, hS, ← prod_union, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
    rw [hWu]
    refine ⟨h1.union (hint k), ?_⟩
    rw [setIntegral_union (disjoint_prod.2 (Or.inr Ico_disjoint_Ico_same)) hSm h1 (hint k), h2]
    linarith [hE k]
  -- So the energy of each window is at most `2 * E`.
  have hwin (j k : ℕ) : ∫ z in B, f k (z + c j) ≤ 2 * E := by
    set a : ℝ × ℝ := (((e j).1 : ℝ), 0)
    have ha (z : ℝ × ℝ) : f k (z + c j) = f k (z + a) := by
      rw [← hfper k (e j).2 (z + a)]
      congr 1
      ext <;> simp [a, hc]
    have haW : ball a 1 ⊆ W := fun y hy ↦ by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hy
      exact ⟨mem_univ _, by simp only [a] at hy; linarith [hy.2.1], by
        simp only [a] at hy; linarith [hy.2.2]⟩
    calc ∫ z in B, f k (z + c j) = ∫ z in B, f k (z + a) := by simp_rw [ha]
      _ = ∫ z in ball a 1, f k z := by rw [hB, hball a k 0 1, zero_add]
      _ ≤ ∫ z in W, f k z := setIntegral_mono_set (hWint k).1
          (Eventually.of_forall fun y ↦ hf0 _ _) haW.eventuallyLE
      _ ≤ 2 * E := (hWint k).2
  -- On each window, every subsequence has a further subsequence converging off finitely many
  -- bubbling points.
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_antitone
    (P := fun j l ↦ ∃ (Z' : Finset (ℝ × ℝ)) (v' : ℝ × ℝ → V), ↑Z' ⊆ B ∧
      (∀ z ∈ Z', ∀ ε > 0, ∀ᶠ k in l, δ ≤ ∫ y in ball z ε ∩ B, f k (y + c j)) ∧
      (∀ C, IsCompact C → C ⊆ B \ ↑Z' →
        ∃ M, ∀ᶠ k in l, ∀ y ∈ C, ‖fderiv ℝ (u k) (y + c j)‖ ≤ M) ∧
      ContinuousOn v' (B \ ↑Z') ∧ MapsTo v' (B \ ↑Z') K ∧
      TendstoLocallyUniformlyOn (fun k y ↦ u k (y + c j)) v' l (B \ ↑Z'))
    (fun j l l' hl ⟨Z', v', hZ', hconc, hbd, hvc, hvK, hlim⟩ ↦ ⟨Z', v', hZ',
      fun z hz ε hε ↦ (hconc z hz ε hε).filter_mono hl,
      fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hM ↦ hM.filter_mono hl, hvc, hvK,
      fun U hU x hx ↦ (hlim U hU x hx).imp fun _ ⟨ht, h⟩ ↦ ⟨ht, h.filter_mono hl⟩⟩)
    (fun j ψ hψ ↦ by
      obtain ⟨ψ', Z', v', hψ', hZ', -, hconc, hbd, hvc, hvK, hlim⟩ :=
        hconv (Ω := B) (u := fun k y ↦ u (ψ k) (y + c j)) (E := 2 * E) isOpen_ball
          ball_subset_closedBall
          (fun k ↦ ((hu (ψ k)).comp (contDiff_id.add contDiff_const)).contDiffOn)
          (fun k z _ ↦ hflw j (ψ k) z) (fun k z _ ↦ huK (ψ k) _)
          (fun k ↦ (hintw j (ψ k)).congr_fun (fun z _ ↦ (hfw j (ψ k) z).symm)
            isOpen_ball.measurableSet)
          (fun k ↦ by
            rw [setIntegral_congr_fun isOpen_ball.measurableSet fun z _ ↦ hfw j (ψ k) z]
            exact hwin j (ψ k))
      refine ⟨ψ', hψ', Z', v', hZ', fun z hz ε hε ↦ ?_, fun C hC hCZ ↦ ?_, hvc, hvK,
        fun U hU x hx ↦ (hlim U hU x hx).imp fun _ ⟨ht, h⟩ ↦ ⟨ht, eventually_map.2 h⟩⟩
      · refine eventually_map.2 ((hconc z hz ε hε).mono fun n hn ↦ ?_)
        rwa [setIntegral_congr_fun (measurableSet_ball.inter isOpen_ball.measurableSet)
          fun y _ ↦ hfw j (ψ (ψ' n)) y] at hn
      · obtain ⟨M, hM⟩ := hbd C hC hCZ
        refine ⟨M, eventually_map.2 (Eventually.of_forall fun n y hy ↦ ?_)⟩
        simpa [fderiv_comp_add_right] using hM n y hy)
  choose Z v hZB hconc hbd hvc hvK hlim using hP
  set l : Filter ℕ := map φ atTop
  -- The bubbling points of all windows, carried back to the plane.
  set Zall : Set (ℝ × ℝ) := ⋃ j, (· + c j) '' (Z j : Set (ℝ × ℝ)) with hZall
  -- The points at which energy at least `δ` concentrates; they include the bubbling points, and
  -- they are invariant under the period `(0, 1)`.
  set Zc : Set (ℝ × ℝ) := {y | ∀ ε > 0, ∀ᶠ k in l, δ ≤ ∫ y' in ball y ε, f k y'} with hZc
  have hZallc : Zall ⊆ Zc := by
    intro y hy ε hε
    obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.1 hy
    filter_upwards [hconc j z hz ε hε] with k hk
    exact (hk.trans (setIntegral_mono_set (hintball (hfa k (c j)) z ε)
      (Eventually.of_forall fun y ↦ hf0 _ _) inter_subset_left.eventuallyLE)).trans_eq
        (hball (c j) k z ε)
  have hZcper (y : ℝ × ℝ) (n : ℤ) (hy : y ∈ Zc) : y + (0, (n : ℝ)) ∈ Zc := by
    intro ε hε
    filter_upwards [hy ε hε] with k hk
    rw [← hball (0, (n : ℝ)) k y ε]
    simpa only [hfper] using hk
  -- Finitely many of them lie in the strip `S`.
  have hcard (F : Finset (ℝ × ℝ)) (hF : ↑F ⊆ Zc ∩ S) : F.card * δ ≤ 2 * E :=
    card_mul_le_of_forall_eventually_le_setIntegral_ball (l := l) hWm
      (fun k y _ ↦ hf0 k y) (fun k ↦ (hWint k).1) (fun k ↦ (hWint k).2) fun z hz ε hε ↦ by
        obtain ⟨hzc, -, hz0, hz1⟩ := hF hz
        filter_upwards [hzc (min ε (1 - z.2)) (lt_min hε (by linarith))] with k hk
        refine hk.trans (setIntegral_mono_set ((hWint k).1.mono_set inter_subset_right)
          (Eventually.of_forall fun y ↦ hf0 _ _)
          (subset_inter (ball_subset_ball (min_le_left _ _)) fun y hy ↦ ?_).eventuallyLE)
        rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hy
        have := min_le_right ε (1 - z.2)
        exact ⟨mem_univ _, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hfin : (Zc ∩ S).Finite := by
    by_contra h
    obtain ⟨F, hF, hFc⟩ := Set.Infinite.exists_subset_card_eq h (⌊2 * E / δ⌋₊ + 1)
    have h1 := hcard F hF
    have h2 : 2 * E / δ < ⌊2 * E / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [hFc] at h1
    push_cast at h1
    rw [div_lt_iff₀ hδ] at h2
    linarith
  -- Off the translates of the points of `Zc ∩ S`, there are no bubbling points.
  have hgood : {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ hfin.toFinset} ⊆ Zallᶜ := by
    intro y hy hyZ
    refine hy (hfin.mem_toFinset.2 ⟨?_, mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩)
    convert hZcper y (-⌊y.2⌋) (hZallc hyZ) using 1
    ext <;> simp [Int.fract, sub_eq_add_neg]
  -- The good parts of the windows, carried back to the plane, cover the complement of `Zall`.
  set G : ℕ → Set (ℝ × ℝ) := fun j ↦ (· - c j) ⁻¹' (B \ ↑(Z j)) with hG
  have hGopen (j : ℕ) : IsOpen (G j) :=
    (isOpen_ball.sdiff (Z j).finite_toSet.isClosed).preimage (continuous_sub_right _)
  have hcover (y : ℝ × ℝ) (hy : y ∉ Zall) : ∃ j, y ∈ G j := by
    -- The integer point nearest to `y` is at distance at most `1 / 2` in each coordinate.
    set m : ℤ × ℤ := (round y.1, round y.2)
    have hm : y - c (e.symm m) ∈ B := by
      rw [hB, mem_ball_zero_iff, Prod.norm_def]
      simp only [hc, Equiv.apply_symm_apply, m, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      exact max_lt ((abs_sub_round _).trans_lt (by norm_num))
        ((abs_sub_round _).trans_lt (by norm_num))
    refine ⟨e.symm m, hm, fun hZ ↦ hy ?_⟩
    rw [hZall, mem_iUnion]
    exact ⟨e.symm m, y - c (e.symm m), hZ, sub_add_cancel _ _⟩
  -- The limit is the pointwise limit, which on each good part is the limit of its window.
  set v' : ℝ × ℝ → V := fun y ↦ limUnder l fun k ↦ u k y
  have hv' (j : ℕ) {y : ℝ × ℝ} (hy : y ∈ G j) : v' y = v j (y - c j) := by
    have h := (hlim j).tendsto_at hy
    simp only [sub_add_cancel] at h
    exact h.limUnder_eq
  have hlimG (j : ℕ) : TendstoLocallyUniformlyOn u v' l (G j) :=
    (((hlim j).comp (· - c j) (mapsTo_preimage _ _) (continuous_sub_right _).continuousOn).congr
      fun k y _ ↦ by simp).congr_right fun y hy ↦ (hv' j hy).symm
  have hcontG (j : ℕ) {y : ℝ × ℝ} (hy : y ∈ G j) : ContinuousAt v' y :=
    (((hvc j).comp (continuous_sub_right _).continuousOn (mapsTo_preimage _ _)).continuousAt
      ((hGopen j).mem_nhds hy)).congr_of_eventuallyEq
        (eventually_of_mem ((hGopen j).mem_nhds hy) fun y' hy' ↦ hv' j hy')
  refine ⟨φ, hfin.toFinset, v', hφ, fun z hz ↦ (hfin.mem_toFinset.1 hz).2, ?_,
    fun z hz ε hε ↦ (eventually_map.1 ((hfin.mem_toFinset.1 hz).1 ε hε)).mono fun n hn ↦
      (half_le_self hδ.le).trans hn, fun C hC hCZ ↦ ?_, ?_, ?_,
    fun s t ↦ by simp only [v', hper], ?_⟩
  · have h := hcard hfin.toFinset (by simp)
    linarith
  · -- Cover `C` by finitely many closed discs, each in a good part of some window.
    replace hCZ := hCZ.trans hgood
    have hloc (x : ℝ × ℝ) (hx : x ∈ C) : ∃ j, ∃ r > 0, closedBall x r ⊆ G j := by
      obtain ⟨j, hj⟩ := hcover x (hCZ hx)
      exact ⟨j, nhds_basis_closedBall.mem_iff.1 ((hGopen j).mem_nhds hj)⟩
    choose! jx rx hrx hsub using hloc
    obtain ⟨T, hTC, hCT⟩ := hC.elim_nhds_subcover (fun x ↦ closedBall x (rx x))
      fun x hx ↦ closedBall_mem_nhds x (hrx x hx)
    have hMx (x : ℝ × ℝ) (hx : x ∈ T) :
        ∃ M, ∀ᶠ k in l, ∀ y ∈ closedBall x (rx x), ‖fderiv ℝ (u k) y‖ ≤ M := by
      have hsub' : closedBall (x - c (jx x)) (rx x) ⊆ B \ ↑(Z (jx x)) := fun y hy ↦ by
        have h := hsub x (hTC x hx) (show y + c (jx x) ∈ closedBall x (rx x) by
          rw [mem_closedBall] at hy ⊢
          rwa [← dist_add_right y (x - c (jx x)) (c (jx x)), sub_add_cancel] at hy)
        simpa [hG] using h
      obtain ⟨M, hM⟩ := hbd (jx x) _ (isCompact_closedBall _ _) hsub'
      refine ⟨M, hM.mono fun k hk y hy ↦ ?_⟩
      have h := hk (y - c (jx x)) (by rwa [mem_closedBall, dist_sub_right])
      rwa [sub_add_cancel] at h
    choose! M hM using hMx
    have hev : ∀ᶠ k in l, ∀ y ∈ C, ‖fderiv ℝ (u k) y‖ ≤ ∑ x ∈ T, |M x| :=
      ((eventually_all_finset T).2 hM).mono fun k hk y hy ↦ by
        obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hCT hy)
        exact (hk x hxT y hyx).trans ((le_abs_self _).trans
          (Finset.single_le_sum (fun i _ ↦ abs_nonneg (M i)) hxT))
    -- The finitely many earlier terms are bounded on `C` one at a time.
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_map.1 hev)
    choose D hD using fun n ↦ hC.exists_bound_of_continuousOn
      ((hu (φ n)).continuous_fderiv (by norm_num)).continuousOn
    refine ⟨max (∑ x ∈ T, |M x|) (∑ n ∈ Finset.range N, |D n|), fun n y hy ↦ ?_⟩
    rcases lt_or_ge n N with hn | hn
    · exact (hD n y hy).trans ((le_abs_self _).trans ((Finset.single_le_sum
        (fun i _ ↦ abs_nonneg (D i)) (Finset.mem_range.2 hn)).trans (le_max_right _ _)))
    · exact (hN n hn y hy).trans (le_max_left _ _)
  · intro y hy
    obtain ⟨j, hj⟩ := hcover y (hgood hy)
    exact (hcontG j hj).continuousWithinAt
  · intro y hy
    obtain ⟨j, hj⟩ := hcover y (hgood hy)
    rw [hv' j hj]
    exact hvK j hj
  · intro U hU x hx
    obtain ⟨j, hj⟩ := hcover x (hgood hx)
    obtain ⟨t, ht, h⟩ := hlimG j U hU x hj
    exact ⟨t, mem_nhdsWithin_of_mem_nhds (by rwa [(hGopen j).nhdsWithin_eq hj] at ht),
      eventually_map.1 h⟩

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
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical
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
