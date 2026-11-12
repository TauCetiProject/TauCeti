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

A Floer trajectory is a solution `u : ℝ × ℝ → V` of the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0`, for the cylindrical perturbation `K = H_t dt` and almost
complex structures `J_t`, both `1`-periodic in `t`. Such cylinders are counted by the Floer
differential, and they break off at the ends of a pair of pants. The compactness theorem
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` applies on
one compact window `D` of the domain, with an energy threshold `δ` depending on `D`. Applying it on
larger and larger windows gives thresholds that may tend to `0`, and hence no bound on the number of
bubbling points over the whole domain. This file proves compactness on the whole plane `ℝ × ℝ`
with a single threshold, for data invariant under the translations of the domain by the integer
points `(m, n)`. The data of a Floer trajectory are such: they do not depend on `s` and are
`1`-periodic in `t`.

The translate `z ↦ u(z + (m, n))` of a solution solves the same equation
(`TauCeti.SymplecticForm.perturbedFDeriv_comp_add_right`), with the same energy over translated
sets, so the threshold of the closed unit disc serves for each of its integer translates, and the
open unit discs about the integer points cover the plane. A diagonal extraction
(`TauCeti.extraction_forall_of_antitone`) gives one subsequence that converges on each of these
countably many discs off finitely many bubbling points. Floer energy at least `δ` concentrates at
each bubbling point, so there are at most `E / δ` of them in all
(`TauCeti.card_mul_le_of_forall_eventually_le_setIntegral_ball`). Off them the limit is the
pointwise limit, which on each disc is the limit given by that disc.

* `SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`:
  compactness off finitely many bubbling points on the plane, for data invariant under integer
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

/-- **Floer solutions with doubly periodic data converge off finitely many bubbling points.** Let
`K = K_s ds + K_t dt` be `C³` and `J(z, x)` be `C²` on `(ℝ × ℝ) × V`, invariant under the
translations of the domain by the integer points `(m, n)`, with `J(z, x)` tamed by `ω` for `x` in a
compact set `K`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
solutions of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on the whole plane, with image
in `K` and Floer energy `∫ ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E`. Then there are a subsequence
`φ`, a finite set `Z` with `#Z * δ ≤ E`, and a continuous `v` off `Z` with values in `K` such that
along `φ` every disc about a point of `Z` eventually carries Floer energy at least `δ`, the
differentials are uniformly bounded on every compact set disjoint from `Z`, and `u_{φ n} → v`
locally uniformly off `Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic
    (ω : SymplecticForm V) {K : Set V}
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
      (∀ k, Integrable (ω.floerEnergyDensity Ks Kt (u k))) →
      (∀ k, ∫ z, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ (↑Z)ᶜ → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (↑Z)ᶜ ∧ MapsTo v (↑Z)ᶜ K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (↑Z)ᶜ := by
  set B : Set (ℝ × ℝ) := ball 0 1 with hB
  -- The compactness theorem on the closed unit disc gives the threshold.
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    isOpen_univ hKs.contDiffOn hKt.contDiffOn hJ.contDiffOn (isCompact_closedBall 0 1) hK
    (subset_univ _) fun z _ x hx ↦ hJt z x hx
  refine ⟨δ, hδ, fun u E hu hfl huK hint hE ↦ ?_⟩
  -- The windows: the translates of `u` by the integer points `c j`, read on the unit disc `B`.
  set e : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm
  set c : ℕ → ℝ × ℝ := fun j ↦ (((e j).1 : ℝ), ((e j).2 : ℝ)) with hc
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity Ks Kt (u k)
  have hf0 (k : ℕ) (y : ℝ × ℝ) : 0 ≤ f k y :=
    ω.floerEnergyDensity_nonneg (hJt y _ (huK k y)) (hfl k y)
  have hKsc (j : ℕ) : (fun z ↦ Ks (z + c j)) = Ks := funext fun z ↦ hKsper _ _ z
  have hKtc (j : ℕ) : (fun z ↦ Kt (z + c j)) = Kt := funext fun z ↦ hKtper _ _ z
  have hmp (j : ℕ) : MeasurePreserving (· + c j) (volume : Measure (ℝ × ℝ)) volume :=
    (measurePreserving_add_right volume (c j).1).prod (measurePreserving_add_right volume (c j).2)
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
  have hintw (j k : ℕ) : Integrable (fun z ↦ f k (z + c j)) :=
    ((hmp j).integrable_comp_emb (measurableEmbedding_addRight (c j))).2 (hint k)
  -- Translating a ball does not change the energy over it.
  have hball (j k : ℕ) (z : ℝ × ℝ) (ε : ℝ) :
      ∫ y in ball z ε, f k (y + c j) = ∫ y in ball (z + c j) ε, f k y := by
    have h : ball z ε = (· + c j) ⁻¹' ball (z + c j) ε := by
      ext y
      simp
    rw [h]
    exact (hmp j).setIntegral_preimage_emb (measurableEmbedding_addRight (c j)) (f k) _
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
        hconv (Ω := B) (u := fun k y ↦ u (ψ k) (y + c j)) (E := E) isOpen_ball
          ball_subset_closedBall
          (fun k ↦ ((hu (ψ k)).comp (contDiff_id.add contDiff_const)).contDiffOn)
          (fun k z _ ↦ hflw j (ψ k) z) (fun k z _ ↦ huK (ψ k) _)
          (fun k ↦ ((hintw j (ψ k)).integrableOn).congr_fun (fun z _ ↦ (hfw j (ψ k) z).symm)
            isOpen_ball.measurableSet)
          (fun k ↦ by
            rw [setIntegral_congr_fun isOpen_ball.measurableSet fun z _ ↦ hfw j (ψ k) z]
            calc ∫ z in B, f (ψ k) (z + c j) ≤ ∫ z, f (ψ k) (z + c j) :=
                  setIntegral_le_integral (hintw j (ψ k)) (Eventually.of_forall fun z ↦ hf0 _ _)
              _ = ∫ z, f (ψ k) z :=
                  (hmp j).integral_comp (measurableEmbedding_addRight (c j)) (f (ψ k))
              _ ≤ E := hE (ψ k))
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
  have hconcAll : ∀ y ∈ Zall, ∀ ε > 0, ∀ᶠ k in l, δ ≤ ∫ y' in ball y ε, f k y' := by
    intro y hy ε hε
    obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.1 hy
    filter_upwards [hconc j z hz ε hε] with k hk
    exact (hk.trans (setIntegral_mono_set (hintw j k).integrableOn
      (Eventually.of_forall fun y ↦ hf0 _ _) inter_subset_left.eventuallyLE)).trans_eq
        (hball j k z ε)
  have hcard (F : Finset (ℝ × ℝ)) (hF : ↑F ⊆ Zall) : F.card * δ ≤ E :=
    card_mul_le_of_forall_eventually_le_setIntegral_ball (l := l) MeasurableSet.univ
      (fun k y _ ↦ hf0 k y) (fun k ↦ (hint k).integrableOn)
      (fun k ↦ (setIntegral_univ (f := f k)).trans_le (hE k))
      fun z hz ε hε ↦ by simpa only [inter_univ] using hconcAll z (hF hz) ε hε
  have hfin : Zall.Finite := by
    by_contra h
    obtain ⟨F, hF, hFc⟩ := Set.Infinite.exists_subset_card_eq h (⌊E / δ⌋₊ + 1)
    have h1 := hcard F hF
    have h2 : E / δ < ⌊E / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [hFc] at h1
    push_cast at h1
    rw [div_lt_iff₀ hδ] at h2
    linarith
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
  have hZ : (↑hfin.toFinset : Set (ℝ × ℝ))ᶜ = Zallᶜ := by rw [Set.Finite.coe_toFinset]
  refine ⟨φ, hfin.toFinset, v', hφ, hcard _ (by simp), fun z hz ε hε ↦
    eventually_map.1 (hconcAll z (by simpa using hz) ε hε), fun C hC hCZ ↦ ?_, ?_, ?_, ?_⟩
  · -- Cover `C` by finitely many closed discs, each in a good part of some window.
    rw [hZ] at hCZ
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
  · rw [hZ]
    intro y hy
    obtain ⟨j, hj⟩ := hcover y hy
    exact (hcontG j hj).continuousWithinAt
  · rw [hZ]
    intro y hy
    obtain ⟨j, hj⟩ := hcover y hy
    rw [hv' j hj]
    exact hvK j hj
  · rw [hZ]
    intro U hU x hx
    obtain ⟨j, hj⟩ := hcover x hx
    obtain ⟨t, ht, h⟩ := hlimG j U hU x hj
    exact ⟨t, mem_nhdsWithin_of_mem_nhds (by rwa [(hGopen j).nhdsWithin_eq hj] at ht),
      eventually_map.1 h⟩

/-- **Floer trajectories converge off finitely many bubbling points.** Let `H` be a `C³`
Hamiltonian, `1`-periodic in time, and `J_t(x)` a `C²` family of almost complex structures,
`1`-periodic in `t` and tamed by `ω` on a compact set `K`. There is a threshold `δ > 0` with the
following property. Let `uₖ : ℝ × ℝ → V` be `C³` solutions of the Floer equation
`∂ₛu + J_t(u) (∂ₜu - X_{H_t}(u)) = 0` with image in `K` and Floer energy at most `E`. Then there are
a subsequence `φ`, a finite set `Z` with `#Z * δ ≤ E`, and a continuous `v` off `Z` with values in
`K` such that along `φ` every disc about a point of `Z` eventually carries Floer energy at least
`δ`, the differentials are uniformly bounded on every compact set disjoint from `Z`, and
`u_{φ n} → v` locally uniformly off `Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cylindrical
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V} {K : Set V}
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hJ : ContDiff ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k z, u k z ∈ K) →
      (∀ k, Integrable (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k))) →
      (∀ k, ∫ z, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤
          ∫ y in ball z ε, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun z ↦ H z.2) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ (↑Z)ᶜ → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (↑Z)ᶜ ∧ MapsTo v (↑Z)ᶜ K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (↑Z)ᶜ :=
  have hp : ContDiff ℝ ⊤ fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic (J := fun z ↦ J z.2)
    contDiff_const (hH.comp (hp.of_le le_top)) (hJ.comp (hp.of_le le_top)) hK
    (fun z ↦ hJt z.2) (fun _ _ _ ↦ rfl) (fun _ n z ↦ by simpa using hHper.int_mul n z.2)
    fun _ n z ↦ by simpa using hJper.int_mul n z.2

end TauCeti.SymplecticForm
