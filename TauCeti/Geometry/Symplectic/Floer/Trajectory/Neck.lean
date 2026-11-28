/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
import TauCeti.Analysis.SpecificLimits.Monotone
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Breaking.Basic
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Necks in breaking sequences of Floer trajectories

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C¹` Hamiltonian, `1`-periodic in
time, and `K ⊆ V` a compact set. Let `u_k` be Floer trajectories, solutions of
`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops in `K`, uniformly tame almost
complex structures and a common Lipschitz constant. When such a sequence breaks, its energy splits
into levels which drift apart in `s`
(`TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`). This file shows that loops of the
trajectories which drift apart in `s` are separated by necks along which the trajectories converge
to stationary cylinders over `1`-periodic orbits, and that these orbits are located by the action;
this is the step that separates levels. Assembling the levels themselves is not done here.

* **Necks are stationary cylinders.** If the translates `(s, t) ↦ u_k(s + σ_k, t)` converge
  locally uniformly to `g` along windows `[a + σ_k, b + σ_k] × [0, 1]` whose energy tends to zero,
  then `g(s, t) = x(t)` for a `1`-periodic orbit `x` of the Hamiltonian vector field with values in
  `K` (`SymplecticForm.exists_periodic_hasDerivAt_of_tendsto_setLIntegral_comp_add`), and the
  actions of the loops `u_k(σ_k, ·)` are asymptotic to the action of `x`
  (`SymplecticForm.tendsto_hamiltonianAction_sub_hamiltonianAction_of_tendstoLocallyUniformly`);
  both are in `TauCeti.Geometry.Symplectic.Floer.Breaking.Basic`.
* **Far apart loops are joined by a neck.** If `σ'_k - σ_k → ∞`, then along a subsequence there
  are shifts `τ_k` with `τ_k - σ_k → ∞` and `σ'_k - τ_k → ∞` such that the translates by `τ_k`
  converge to the stationary cylinder over an orbit `x` in `K`, and the actions of the loops
  `u_k(τ_k, ·)` are asymptotic to the action of `x`
  (`SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop`). Along
  each trajectory the action increases, by at most a constant independent of `k` since the loops
  have bounded speed and lie in `K`; so `[σ_k, σ'_k]` contains long windows across which the
  action increases by an amount tending to zero
  (`TauCeti.exists_tendsto_sub_nhds_zero_of_monotone_of_tendsto_sub_atTop`). The energy of a
  window is the increase of the action across it
  (`SymplecticForm.setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub`), so these are
  windows of vanishing energy
  (`SymplecticForm.tendsto_setLIntegral_floerEnergyDensity_of_tendsto_hamiltonianAction_sub`).
* **The neck orbit lies between the two loops in action.** If moreover the actions of the loops
  `u_k(σ_k, ·)` and `u_k(σ'_k, ·)` tend to `b` and `b'`, the orbit has action in `[b, b']`
  (`SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_hamiltonianAction_mem_Icc`, and
  `SymplecticForm.exists_hamiltonianAction_mem_Icc_of_tendsto_sub_atTop` for the orbit alone).
* **Loops normalized at actions with no orbit between them stay together.** Consequently, if no
  `1`-periodic orbit in `K` has its action in `[b, b']`, the shifts `σ'_k - σ_k` are bounded
  above (`SymplecticForm.isBoundedUnder_le_sub_of_forall_hamiltonianAction_notMem_Icc`). When
  `b ≤ b'`, the theorem with `σ` and `σ'` exchanged, whose hypothesis concerns
  `[b', b] ⊆ [b, b']`, bounds them below, so the loops of actions near `b` and `b'` stay a bounded
  distance apart.

As in `TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`, the uniform bound on the derivatives,
which excludes bubbling, is a hypothesis. The almost complex structures `J_k` may vary with
`k`, and no convergence of the derivatives of the trajectories is used.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on compactness up to breaking.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {K : Set V} {J : ℕ → ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {L : ℝ≥0}

/-- **Windows of vanishing energy.** Let `u k` be `C²` solutions of the Floer equation
`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with `1`-periodic loops and almost
complex structures tamed by `ω`. If `ℓ k → ∞` and the action
increases by an amount tending to zero from the loop at `τ k - ℓ k` to the loop at `τ k + ℓ k`, then
for every window `[a, b]` the energy of `u k` over `[a + τ k, b + τ k] × [0, 1]` tends to zero: for
large `k` the window lies in `[τ k - ℓ k, τ k + ℓ k]`, over which the energy is the increase of the
action. -/
theorem tendsto_setLIntegral_floerEnergyDensity_of_tendsto_hamiltonianAction_sub
    (hH : ContDiff ℝ 1 (uncurry H)) {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (hJ : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J k z))
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    {τ ℓ : ℕ → ℝ} (hℓ : Tendsto ℓ atTop atTop)
    (hinc : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (τ k + ℓ k, t)) -
      ω.hamiltonianAction H (fun t ↦ u k (τ k - ℓ k, t))) atTop (𝓝 0)) (a b : ℝ) :
    Tendsto (fun k ↦ ∫⁻ z in Icc (a + τ k) (b + τ k) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z)) atTop
      (𝓝 0) := by
  have hlim := ENNReal.tendsto_ofReal hinc
  rw [ENNReal.ofReal_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hℓ.eventually_ge_atTop (max |a| |b|)] with k hk
  have hsub : Icc (a + τ k) (b + τ k) ⊆ Icc (τ k - ℓ k) (τ k + ℓ k) :=
    Icc_subset_Icc (by linarith [neg_abs_le a, le_max_left |a| |b|])
      (by linarith [le_abs_self b, le_max_right |a| |b|])
  refine (lintegral_mono_set (prod_mono hsub le_rfl)).trans_eq ?_
  exact ω.setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub
    (J := J k) (fun z hz ↦ hJ k z ⟨mem_univ _, hz.2⟩) hH isOpen_univ (hu k).contDiffOn
    (by linarith [(abs_nonneg a).trans (le_max_left |a| |b|)]) (subset_univ _)
    (fun s _ ↦ by simpa using hper k s 0) fun z hz ↦ hfloer k z ⟨mem_univ _, hz.2⟩

/-- **Far apart loops of Floer trajectories are joined by a neck over an orbit.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, and `K` a compact set. Let `u k` be `C²` solutions of the Floer
equation `∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with `1`-periodic loops in `K`,
uniformly tame almost complex structures, `c ‖v‖² ≤ ω(v, J_k z v)` and `‖J_k z v‖ ≤ M ‖v‖` with
`c > 0`, and a common Lipschitz constant `L`. If `σ' k - σ k → ∞`, there are a subsequence
`u (φ n)`, shifts `τ n` with `τ n - σ (φ n) → ∞` and `σ' (φ n) - τ n → ∞`, and a `1`-periodic
orbit `x` of the Hamiltonian vector field with values in `K`, such that the translates
`(s, t) ↦ u (φ n) (s + τ n, t)` converge locally uniformly to the stationary cylinder
`(s, t) ↦ x(t)` and the actions of the loops `u (φ n) (τ n, ·)` are asymptotic to the action of
`x`. -/
theorem exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ}
    (hσ : Tendsto (fun k ↦ σ' k - σ k) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ τ : ℕ → ℝ, ∃ x : ℝ → V, Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ (∀ t, x t ∈ K) ∧
      Tendsto (fun n ↦ τ n - σ (φ n)) atTop atTop ∧ Tendsto (fun n ↦ σ' (φ n) - τ n) atTop atTop ∧
      TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ n, 0))) (fun z ↦ x z.2) atTop ∧
      Tendsto (fun n ↦ ω.hamiltonianAction H (fun t ↦ u (φ n) (τ n, t)) -
        ω.hamiltonianAction H x) atTop (𝓝 0) := by
  -- The actions of the loops increase along each trajectory by a bounded amount, so `[σ k, σ' k]`
  -- contains windows `[τ k - ℓ k, τ k + ℓ k]` with `ℓ k → ∞` across which the action increases by
  -- an amount tending to zero.
  have hJ (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) : ω.Tames (J k z) :=
    tames_of_mul_norm_sq_le hc (hJc k z hz)
  have hmono (k : ℕ) := ω.monotone_hamiltonianAction_of_floer hH (hu k) (hper k) (hJ k)
    (hfloer k)
  obtain ⟨B, hB⟩ := ω.exists_forall_abs_hamiltonianAction_le hH.continuous hK L
  have hC (k : ℕ) : ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) -
      ω.hamiltonianAction H (fun t ↦ u k (σ k, t)) ≤ 2 * B := by
    have hu1 := (hu k).of_le one_le_two
    linarith [(abs_le.1 (hB hu1 (hper k) (huK k) (hL k) (σ' k))).2,
      (abs_le.1 (hB hu1 (hper k) (huK k) (hL k) (σ k))).1]
  obtain ⟨τ, ℓ, hℓ, hwin, hinc⟩ :=
    exists_tendsto_sub_nhds_zero_of_monotone_of_tendsto_sub_atTop hmono hC hσ
  -- The energy over every window `[a + τ k, b + τ k] × [0, 1]` therefore tends to zero.
  have hen := tendsto_setLIntegral_floerEnergyDensity_of_tendsto_hamiltonianAction_sub hH hu hper
    hJ hfloer hℓ hinc
  -- The translates by `τ k` are uniformly Lipschitz with values in `K`, so a subsequence
  -- converges, and its limit is the stationary cylinder over an orbit.
  have hwL (k : ℕ) : LipschitzWith L fun z ↦ u k (z + (τ k, 0)) := by
    have h := (hL k).comp (IsometryEquiv.addRight ((τ k, 0) : ℝ × ℝ)).isometry.lipschitzWith
    rw [mul_one] at h
    exact h
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith hK
    (R := fun n ↦ (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n ↦ (hwL n).lipschitzOnWith) fun n z _ ↦ huK _ _
  obtain ⟨x, hxper, hxd, hxK, hgx⟩ := exists_periodic_hasDerivAt_of_tendsto_setLIntegral_comp_add
    (J := fun n ↦ J (φ n)) (s := fun n ↦ τ (φ n)) hH hHper hK.isClosed isOpen_univ
    (fun n ↦ ((hu (φ n)).of_le one_le_two).contDiffOn) (fun n r _ ↦ hper (φ n) r)
    (fun n r _ t ↦ huK (φ n) (r, t)) hc (fun n ↦ hJc (φ n)) (fun n ↦ hJM (φ n))
    (fun n ↦ hfloer (φ n)) (fun _ _ ↦ Eventually.of_forall fun _ ↦ subset_univ _)
    (fun a b ↦ (hen a b).comp hφ.tendsto_atTop) hg
  rw [hgx] at hg
  have hτσ : Tendsto (fun k ↦ τ k - σ k) atTop atTop :=
    tendsto_atTop_mono' atTop (hwin.mono fun k hk ↦ by linarith [hk.1]) hℓ
  have hσ'τ : Tendsto (fun k ↦ σ' k - τ k) atTop atTop :=
    tendsto_atTop_mono' atTop (hwin.mono fun k hk ↦ by linarith [hk.2]) hℓ
  refine ⟨φ, hφ, fun n ↦ τ (φ n), x, hxper, hxd, hxK, hτσ.comp hφ.tendsto_atTop,
    hσ'τ.comp hφ.tendsto_atTop, hg, ?_⟩
  -- The loops of the translates at `s = 0` are the loops of the trajectories at `s = τ`.
  simpa using ω.tendsto_hamiltonianAction_sub_hamiltonianAction_of_tendstoLocallyUniformly hH
    (f := fun n z ↦ u (φ n) (z + (τ (φ n), 0)))
    (fun n ↦ ((hu (φ n)).of_le one_le_two).comp (contDiff_id.add contDiff_const))
    (fun n s t ↦ by simpa [add_comm] using hper (φ n) (s + τ (φ n)) t) (fun n ↦ hwL (φ n))
    hxper hxd hg

/-- **The orbit of a neck lies between the two loops in action.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop`, if
`σ' k - σ k → ∞` and the actions of the loops `u k (σ k, ·)` and `u k (σ' k, ·)` tend to `b` and
`b'`, then along a subsequence `u (φ n)` there are shifts `τ n` with `τ n - σ (φ n) → ∞` and
`σ' (φ n) - τ n → ∞` such that the translates `(s, t) ↦ u (φ n) (s + τ n, t)` converge locally
uniformly to the stationary cylinder `(s, t) ↦ x(t)` over a `1`-periodic orbit `x` of the
Hamiltonian vector field with values in `K` whose action lies in `[b, b']`. -/
theorem exists_subseq_tendstoLocallyUniformly_comp_add_hamiltonianAction_mem_Icc
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ}
    (hσ : Tendsto (fun k ↦ σ' k - σ k) atTop atTop) {b b' : ℝ}
    (hb : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ k, t))) atTop (𝓝 b))
    (hb' : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ' k, t))) atTop (𝓝 b')) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ τ : ℕ → ℝ, ∃ x : ℝ → V, Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ (∀ t, x t ∈ K) ∧
      Tendsto (fun n ↦ τ n - σ (φ n)) atTop atTop ∧ Tendsto (fun n ↦ σ' (φ n) - τ n) atTop atTop ∧
      TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ n, 0))) (fun z ↦ x z.2) atTop ∧
      ω.hamiltonianAction H x ∈ Icc b b' := by
  obtain ⟨φ, hφ, τ, x, hxper, hxd, hxK, hτσ, hσ'τ, hux, hA⟩ :=
    exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop hH hHper hK hu hper huK
      hc hJc hJM hfloer hL hσ
  have hmono (k : ℕ) := ω.monotone_hamiltonianAction_of_floer hH (hu k) (hper k)
    (fun z hz ↦ tames_of_mul_norm_sq_le hc (hJc k z hz)) (hfloer k)
  -- The actions of the loops at `τ` tend to the action of `x`, and lie between those at `σ` and
  -- at `σ'`, eventually.
  have hτA : Tendsto (fun n ↦ ω.hamiltonianAction H (fun t ↦ u (φ n) (τ n, t))) atTop
      (𝓝 (ω.hamiltonianAction H x)) := by
    simpa using hA.add_const (ω.hamiltonianAction H x)
  refine ⟨φ, hφ, τ, x, hxper, hxd, hxK, hτσ, hσ'τ, hux,
    le_of_tendsto_of_tendsto (hb.comp hφ.tendsto_atTop) hτA ?_,
    le_of_tendsto_of_tendsto hτA (hb'.comp hφ.tendsto_atTop) ?_⟩
  · filter_upwards [hτσ.eventually_ge_atTop 0] with n hn
    exact hmono (φ n) (by linarith)
  · filter_upwards [hσ'τ.eventually_ge_atTop 0] with n hn
    exact hmono (φ n) (by linarith)

/-- **An orbit lies between two far apart loops in action.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop`, if
`σ' k - σ k → ∞` and the actions of the loops `u k (σ k, ·)` and `u k (σ' k, ·)` tend to `b` and
`b'`, then some `1`-periodic orbit of the Hamiltonian vector field with values in `K` has its action
in `[b, b']`. -/
theorem exists_hamiltonianAction_mem_Icc_of_tendsto_sub_atTop
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ}
    (hσ : Tendsto (fun k ↦ σ' k - σ k) atTop atTop) {b b' : ℝ}
    (hb : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ k, t))) atTop (𝓝 b))
    (hb' : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ' k, t))) atTop (𝓝 b')) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧
      (∀ t, x t ∈ K) ∧ ω.hamiltonianAction H x ∈ Icc b b' := by
  obtain ⟨-, -, -, x, hxper, hxd, hxK, -, -, -, hx⟩ :=
    exists_subseq_tendstoLocallyUniformly_comp_add_hamiltonianAction_mem_Icc hH hHper hK hu hper
      huK hc hJc hJM hfloer hL hσ hb hb'
  exact ⟨x, hxper, hxd, hxK, hx⟩

/-- **Loops normalized at actions with no orbit between them are boundedly far apart in one
direction.** Under the hypotheses of
`TauCeti.SymplecticForm.exists_hamiltonianAction_mem_Icc_of_tendsto_sub_atTop` without
`σ' k - σ k → ∞`, let the actions of the loops `u k (σ k, ·)` and `u k (σ' k, ·)` tend to `b` and
`b'`. If no `1`-periodic orbit of the Hamiltonian vector field with values in `K` has its action
in `[b, b']`, then the shifts `σ' k - σ k` are bounded above. When `b ≤ b'`, applying this theorem
with `σ` and `σ'` exchanged also bounds them below. -/
theorem isBoundedUnder_le_sub_of_forall_hamiltonianAction_notMem_Icc
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ} {b b' : ℝ}
    (hb : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ k, t))) atTop (𝓝 b))
    (hb' : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ' k, t))) atTop (𝓝 b'))
    (hreg : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
        ω.hamiltonianAction H x ∉ Icc b b') :
    IsBoundedUnder (· ≤ ·) atTop fun k ↦ σ' k - σ k := by
  by_contra hbdd
  -- Otherwise a subsequence of the shifts tends to infinity.
  have hfreq (n : ℕ) : ∃ᶠ k in atTop, (n : ℝ) ≤ σ' k - σ k := by
    by_contra hn
    exact hbdd ⟨n, (not_frequently.1 hn).mono fun k hk ↦ (not_le.1 hk).le⟩
  obtain ⟨ψ, hψ, hψn⟩ := extraction_forall_of_frequently hfreq
  obtain ⟨x, hxper, hxd, hxK, hx⟩ := exists_hamiltonianAction_mem_Icc_of_tendsto_sub_atTop
    (J := fun n ↦ J (ψ n)) (u := fun n ↦ u (ψ n)) (σ := fun n ↦ σ (ψ n))
    (σ' := fun n ↦ σ' (ψ n)) hH hHper hK (fun n ↦ hu (ψ n)) (fun n ↦ hper (ψ n))
    (fun n ↦ huK (ψ n)) hc (fun n ↦ hJc (ψ n)) (fun n ↦ hJM (ψ n)) (fun n ↦ hfloer (ψ n))
    (fun n ↦ hL (ψ n)) (tendsto_atTop_mono hψn tendsto_natCast_atTop_atTop)
    (hb.comp hψ.tendsto_atTop) (hb'.comp hψ.tendsto_atTop)
  exact hreg x hxper hxd hxK hx

end TauCeti.SymplecticForm
