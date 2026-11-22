/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.LowEnergyNeck
public import TauCeti.Geometry.Symplectic.Floer.Trajectory.Breaking
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The levels of a breaking sequence of Floer trajectories meet at the neck orbits

Let `(V, ω)` be a finite-dimensional symplectic vector space, `H` a `C³` Hamiltonian, `1`-periodic
in time, and `J_t(x)` a `1`-periodic family of almost complex structures tamed by `ω` on a compact
set `K`, all of whose `1`-periodic orbits are nondegenerate. Let `u_k` be Floer trajectories,
solutions of `∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops in `K` and a common
Lipschitz constant. When such a sequence breaks, its translates at shifts `σ_k` that keep a fixed
action converge to the *levels* of the limit, and between two levels the trajectories run along a
*neck*, at whose middle shifts `τ_k` they converge to the stationary cylinder over a
`1`-periodic orbit `x` (`TauCeti.Geometry.Symplectic.Floer.Trajectory.Breaking`). This file proves
that the two levels on either side of a neck are joined at `x`: the lower level converges to `x` as
`s → ∞`, and the upper level converges to `x` as `s → -∞`, uniformly in `t`. Likewise the first
and the last level converge to the common end orbits of the `u_k`. So the limit of a breaking
sequence is a broken trajectory: a chain of levels, from the start orbit to the end orbit, in which
the end of each level is the start of the next.

**Necks are close to one orbit throughout.** Suppose that the actions of the loops at `σ_k` are at
least `b`, those at `σ'_k` at most `b'`, and that at most one orbit action `c` lies in `[b, b']`. A
Floer trajectory spends a bounded time in a window of actions containing no orbit action
(`TauCeti.SymplecticForm.exists_forall_sub_le_of_floer`), so a bounded time after `σ_k` the action
is already close to `c`, and a bounded time before `σ'_k` it is still close to `c`. The energy of
the window in between is the increase of the action across it, so it is small, and a Floer
cylinder of small energy stays uniformly close to a single orbit
(`TauCeti.SymplecticForm.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt_of_floer`).
Limits of loops in that window are therefore close to each other.

## Main results

* `TauCeti.SymplecticForm.tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop`:
  if `σ'_k - σ_k → ∞`, the translates at `σ_k` and `σ'_k` converge pointwise to `g` and `g'`, and
  the loops at shifts `τ_k` infinitely far from both converge pointwise to `x`, then `g(s, ·) → x`
  uniformly as `s → ∞` and `g'(s, ·) → x` uniformly as `s → -∞`.
* `TauCeti.SymplecticForm.tendstoUniformly_atTop_of_forall_tendstoUniformly_atTop` and
  `TauCeti.SymplecticForm.tendstoUniformly_atBot_of_forall_tendstoUniformly_atBot`: if the loops of
  every `u_k` converge uniformly to the same `x` at `s → ∞` (resp. `s → -∞`), and at most one orbit
  action lies between the normalizing value and the supremum (resp. infimum) of the actions, then
  the level converges to `x` at `s → ∞` (resp. `s → -∞`).
* `SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_tendstoUniformly`:
  combined with the selection of the levels
  (`SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq`),
  a sequence normalized at regular action values `b_0 < ⋯ < b_m` with at most one orbit action in
  each `[b_i, b_{i+1}]` has a subsequence whose consecutive levels are either translates of each
  other or joined at an orbit with action between `b_i` and `b_{i+1}`.

The levels are only continuous limits here; that they are themselves Floer trajectories is not
used. As in `TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`, the uniform bound on the
derivatives excludes bubbling; it is assumed, not proved.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on compactness up to breaking and the behaviour of necks.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology Function MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V}
  {W : Set (ℝ × V)} {K : Set V} {L L' : ℝ≥0} {u : ℕ → ℝ × ℝ → V}

/-- **Trajectories reach a gap quickly.** Let `H` be a `C¹`, `1`-periodic Hamiltonian and `J_t(x)`
a `1`-periodic family of almost complex structures, continuous and tamed by `ω` on `ℝ × K` for a
compact `K`. If `b ≤ b'` and at most one orbit action lies in `[b, b']`, then there are
`c ∈ [b, b']` and, for every `η > 0`, a time `T` with the following property. Along every
`L`-Lipschitz `C²` Floer trajectory with `1`-periodic loops in `K`, the action exceeds `c - η` at
time `T` after any loop of action at least `b`, and is below `c + η` at time `T` before any loop
of action at most `b'`. -/
private theorem exists_forall_lt_hamiltonianAction_add (hH : ContDiff ℝ 1 (uncurry H))
    (hHper : Periodic H 1)
    (hJ : ContinuousOn (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (univ ×ˢ K))
    (hJper : Periodic J 1) (hK : IsCompact K) (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x)) {b b' : ℝ}
    (hbb' : b ≤ b')
    (hgap : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc b b').Subsingleton) :
    ∃ c ∈ Icc b b', ∀ η > 0, ∃ T : ℝ, ∀ v : ℝ × ℝ → V, ContDiff ℝ 2 v →
      (∀ s, Periodic (fun t ↦ v (s, t)) 1) → (∀ z, v z ∈ K) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (v z))
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z : ℝ × ℝ →ₗ[ℝ] V)) →
      LipschitzWith L v →
      (∀ s, b ≤ ω.hamiltonianAction H (fun t ↦ v (s, t)) →
        c - η < ω.hamiltonianAction H (fun t ↦ v (s + T, t))) ∧
      ∀ s, ω.hamiltonianAction H (fun t ↦ v (s, t)) ≤ b' →
        ω.hamiltonianAction H (fun t ↦ v (s - T, t)) < c + η := by
  set Λ := ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
    (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}
  obtain ⟨c₀, hc₀, M₀, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK hJ hJper hJt
  -- The orbit actions in `[b, b']` are at most one value `c ∈ [b, b']`.
  obtain ⟨c, hc, hcΛ⟩ : ∃ c ∈ Icc b b', ∀ a ∈ Λ ∩ Icc b b', a = c := by
    rcases (Λ ∩ Icc b b').eq_empty_or_nonempty with h | ⟨c, hc⟩
    · exact ⟨b, left_mem_Icc.2 hbb', by simp [h]⟩
    · exact ⟨c, hc.2, fun a ha ↦ hgap ha hc⟩
  refine ⟨c, hc, fun η hη ↦ ?_⟩
  -- The windows of actions `[b, c - η]` and `[c + η, b']` contain no orbit action, so the
  -- trajectories leave them within bounded times `T₁` and `T₂`.
  have hreg {a₁ a₂ : ℝ} (h₁ : b ≤ a₁) (h₂ : a₂ ≤ b') (hc' : c ∉ Icc a₁ a₂) :
      Disjoint (Icc a₁ a₂) Λ :=
    disjoint_left.2 fun a ha haΛ ↦ hc' <| hcΛ a ⟨haΛ, h₁.trans ha.1, ha.2.trans h₂⟩ ▸ ha
  obtain ⟨T₁, hT₁⟩ := exists_forall_sub_le_of_floer (M := M₀) (L := L) hH hHper hK hc₀
    (hreg (a₂ := c - η) le_rfl (by linarith [hc.2]) fun h ↦ by linarith [h.2])
  obtain ⟨T₂, hT₂⟩ := exists_forall_sub_le_of_floer (M := M₀) (L := L) hH hHper hK hc₀
    (hreg (a₁ := c + η) (by linarith [hc.1]) le_rfl fun h ↦ by linarith [h.1])
  refine ⟨max T₁ T₂ + 1, fun v hv hper hvK hfloer hL ↦ ?_⟩
  have hc₀v (z : ℝ × ℝ) (_ : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) (w : V) :
      c₀ * ‖w‖ ^ 2 ≤ ω w (J z.2 (v z) w) := (hcM z.2 _ (hvK z) w).1
  have hM₀v (z : ℝ × ℝ) (_ : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) (w : V) :
      ‖J z.2 (v z) w‖ ≤ M₀ * ‖w‖ := (hcM z.2 _ (hvK z) w).2
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · by_contra! h
    linarith [le_max_left T₁ T₂, hT₁ v _ hv hper hvK hc₀v hM₀v hfloer hL s _ hs h]
  · by_contra! h
    linarith [le_max_right T₁ T₂, hT₂ v _ hv hper hvK hc₀v hM₀v hfloer hL _ s h hs]

/-- **A neck stays close to one loop.** Let `u_k` be Lipschitz Floer trajectories with loops in
`K`, for data as in
`TauCeti.SymplecticForm.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt_of_floer`, and
let `σ_k`, `σ'_k` be shifts with `σ'_k - σ_k → ∞`, such that the actions of the loops at `σ_k` are
at least `b`, those at `σ'_k` at most `b'`, and at most one orbit action lies in `[b, b']`. Then for
every `ε > 0` there are `a` and `a'` such that for all large `k` the loops of `u_k` at all
`s ∈ [σ_k + a, σ'_k - a']` are within `ε` of one loop `y`. -/
private theorem exists_forall_eventually_exists_forall_dist_lt
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ} {b b' : ℝ}
    (hσ : ∀ k, b ≤ ω.hamiltonianAction H (fun t ↦ u k (σ k, t)))
    (hσ' : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) ≤ b')
    (hgap : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc b b').Subsingleton)
    (hσσ' : Tendsto (fun k ↦ σ' k - σ k) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ a a' : ℝ, ∀ᶠ k in atTop, ∃ y : ℝ → V,
      ∀ s ∈ Icc (σ k + a) (σ' k - a'), ∀ t, dist (u k (s, t)) (y t) < ε := by
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hu2 (k : ℕ) : ContDiff ℝ 2 (u k) := (hu k).of_le (by norm_num)
  -- The constants of a neck of small energy.
  obtain ⟨δ, hδ, ρ, hρ, hneck⟩ :=
    exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt_of_floer hH hHper hW hJ hJper hK
      hKW hJt hL' hnd hε
  -- The actions increase along the trajectories, so `b ≤ b'`, and a bounded time `T` after `σ k`
  -- and before `σ' k` the action is within `δ / 4` of the only orbit action `c` in `[b, b']`.
  obtain ⟨k₀, hk₀⟩ := (hσσ'.eventually_ge_atTop 0).exists
  have hbb' : b ≤ b' := (hσ k₀).trans <| (ω.monotone_hamiltonianAction_of_floer hH1 (hu2 k₀)
    (hper k₀) (fun z _ ↦ hJt z.2 _ (huK k₀ z)) (hfloer k₀) (sub_nonneg.1 hk₀)).trans (hσ' k₀)
  obtain ⟨c, -, hcT⟩ := exists_forall_lt_hamiltonianAction_add (L := L) hH1 hHper
    (hJ.continuousOn.mono hKW) hJper hK hJt hbb' hgap
  obtain ⟨T, hT⟩ := hcT (δ / 4) (by positivity)
  refine ⟨T + ρ, T + ρ, ?_⟩
  filter_upwards [hσσ'.eventually_ge_atTop (2 * T + 2 * ρ)] with k hk
  obtain ⟨hA₁, hA₂⟩ := hT (u k) (hu2 k) (hper k) (huK k) (hfloer k) (hL k)
  -- So the energy of `u k` over `(σ k + T, σ' k - T) × [0, 1]` is less than `δ`.
  have hE : ∫⁻ z in Ioo (σ k + T) (σ' k - T) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z) <
        ENNReal.ofReal δ := by
    refine (lintegral_mono_set (Set.prod_mono Ioo_subset_Icc_self le_rfl)).trans_lt ?_
    rw [ω.setLIntegral_floerEnergyDensity_eq_ofReal_hamiltonianAction_sub
      (J := fun z ↦ J z.2 (u k z)) (fun z _ ↦ hJt z.2 _ (huK k z)) hH1 isOpen_univ
      (hu2 k).contDiffOn (by linarith) (subset_univ _) (fun s _ ↦ by simpa using hper k s 0)
      fun z hz ↦ hfloer k z ⟨mem_univ _, hz.2⟩]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 (by linarith [hA₁ _ (hσ k), hA₂ _ (hσ' k)])
  obtain ⟨y, -, -, -, hy⟩ := hneck (u := u k) (by linarith) (hu k).contDiffOn
    (fun s _ ↦ hper k s) (fun s _ t ↦ huK k (s, t)) (fun z hz ↦ hfloer k z ⟨mem_univ _, hz.2⟩) hE
  exact ⟨y, fun s hs t ↦ hy s ⟨by linarith [hs.1], by linarith [hs.2]⟩ t⟩

/-- If, for all large `k`, the loops of `v_k` at all `s ∈ I_k` are within `ε / 3` of one loop, and
the loops at two shifts `ς_k, ς'_k ∈ I_k` converge pointwise to `f` and `f'`, then `f` and `f'`
are within `ε` of each other. -/
private theorem dist_lt_of_eventually_mem {X : Type*} [PseudoMetricSpace X] {v : ℕ → ℝ × ℝ → X}
    {ε : ℝ} (hε : 0 < ε) {I : ℕ → Set ℝ}
    (hy : ∀ᶠ k in atTop, ∃ y : ℝ → X, ∀ s ∈ I k, ∀ t, dist (v k (s, t)) (y t) < ε / 3)
    {ς ς' : ℕ → ℝ} (hς : ∀ᶠ k in atTop, ς k ∈ I k) (hς' : ∀ᶠ k in atTop, ς' k ∈ I k)
    {f f' : ℝ → X} (hf : ∀ t, Tendsto (fun k ↦ v k (ς k, t)) atTop (𝓝 (f t)))
    (hf' : ∀ t, Tendsto (fun k ↦ v k (ς' k, t)) atTop (𝓝 (f' t))) (t : ℝ) :
    dist (f t) (f' t) < ε := by
  refine lt_of_le_of_lt (le_of_tendsto ((hf t).dist (hf' t)) ?_) (by linarith : 2 * ε / 3 < ε)
  filter_upwards [hy, hς, hς'] with k ⟨y, hy⟩ hςk hς'k
  calc dist (v k (ς k, t)) (v k (ς' k, t))
      ≤ dist (v k (ς k, t)) (y t) + dist (v k (ς' k, t)) (y t) := dist_triangle_right _ _ _
    _ ≤ 2 * ε / 3 := by linarith [hy _ hςk t, hy _ hς'k t]

/-- Shifts `τ_k` with `τ_k - σ_k → ∞` and `σ'_k - τ_k → ∞` eventually lie in
`[σ_k + a, σ'_k - a']`. -/
private theorem eventually_mem_Icc_of_tendsto_sub_atTop {σ σ' τ : ℕ → ℝ}
    (hτ : Tendsto (fun k ↦ τ k - σ k) atTop atTop) (hτ' : Tendsto (fun k ↦ σ' k - τ k) atTop atTop)
    (a a' : ℝ) : ∀ᶠ k in atTop, τ k ∈ Icc (σ k + a) (σ' k - a') := by
  filter_upwards [hτ.eventually_ge_atTop a, hτ'.eventually_ge_atTop a'] with k h₁ h₂
  exact ⟨by linarith, by linarith⟩

/-- **The levels on both sides of a neck meet at the neck orbit.** Let `H` be a `C³`,
`1`-periodic Hamiltonian and `J_t(x)` a `1`-periodic family of almost complex structures, `C²` on an
open set `W ⊆ ℝ × V` containing `ℝ × K` for a compact `K ⊆ V`, and tamed by `ω` on `ℝ × K`. Suppose
that the suspension of the Hamiltonian vector field is globally Lipschitz and that every
`1`-periodic orbit in `K` is nondegenerate. Let `u_k` be `C³` Floer trajectories,
`∂_s u + J_t(u) (∂_t u - X_{H_t}(u)) = 0`, with `1`-periodic loops in `K` and a common Lipschitz
constant.

Let `σ_k`, `τ_k` and `σ'_k` be shifts with `τ_k - σ_k → ∞` and `σ'_k - τ_k → ∞`, such that the
actions of the loops at `σ_k` are at least `b`, those at `σ'_k` at most `b'`, and at most one orbit
action lies in `[b, b']`. If the translates `(s, t) ↦ u_k(s + σ_k, t)` and
`(s, t) ↦ u_k(s + σ'_k, t)` converge pointwise to `g` and `g'`, and the loops at `τ_k` converge
pointwise to `x`, then `g(s, ·)` converges to `x` uniformly as `s → ∞`, and `g'(s, ·)` converges to
`x` uniformly as `s → -∞`. -/
theorem tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' τ : ℕ → ℝ} {b b' : ℝ}
    (hσ : ∀ k, b ≤ ω.hamiltonianAction H (fun t ↦ u k (σ k, t)))
    (hσ' : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) ≤ b')
    (hgap : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc b b').Subsingleton)
    (hτ : Tendsto (fun k ↦ τ k - σ k) atTop atTop) (hτ' : Tendsto (fun k ↦ σ' k - τ k) atTop atTop)
    {g g' : ℝ × ℝ → V} {x : ℝ → V}
    (hg : ∀ z, Tendsto (fun k ↦ u k (z + (σ k, 0))) atTop (𝓝 (g z)))
    (hg' : ∀ z, Tendsto (fun k ↦ u k (z + (σ' k, 0))) atTop (𝓝 (g' z)))
    (hx : ∀ t, Tendsto (fun k ↦ u k (τ k, t)) atTop (𝓝 (x t))) :
    TendstoUniformly (fun s t ↦ g (s, t)) x atTop ∧
      TendstoUniformly (fun s t ↦ g' (s, t)) x atBot := by
  have hσσ' : Tendsto (fun k ↦ σ' k - σ k) atTop atTop :=
    (hτ'.atTop_add_atTop hτ).congr fun k ↦ by ring
  have hcore {ε : ℝ} (hε : 0 < ε) := exists_forall_eventually_exists_forall_dist_lt hH hHper hW hJ
    hJper hK hKW hJt hL' hnd hu hper huK hfloer hL hσ hσ' hgap hσσ' (ε := ε / 3) (by positivity)
  refine ⟨Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_, Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_⟩
  · -- The loops of `g` beyond `a` are limits of loops in the neck, as are those of `x`.
    obtain ⟨a, a', hy⟩ := hcore hε
    filter_upwards [eventually_ge_atTop a] with s hs t
    have hs' : ∀ᶠ k in atTop, s + σ k ∈ Icc (σ k + a) (σ' k - a') := by
      filter_upwards [hσσ'.eventually_ge_atTop (s + a')] with k hk
      exact ⟨by linarith, by linarith⟩
    exact dist_lt_of_eventually_mem hε hy (eventually_mem_Icc_of_tendsto_sub_atTop hτ hτ' a a')
      hs' hx (fun t ↦ by simpa using hg (s, t)) t
  · -- The loops of `g'` before `-a'` are limits of loops in the neck, as are those of `x`.
    obtain ⟨a, a', hy⟩ := hcore hε
    filter_upwards [eventually_le_atBot (-a')] with s hs t
    have hs' : ∀ᶠ k in atTop, s + σ' k ∈ Icc (σ k + a) (σ' k - a') := by
      filter_upwards [hσσ'.eventually_ge_atTop (a - s)] with k hk
      exact ⟨by linarith, by linarith⟩
    exact dist_lt_of_eventually_mem hε hy (eventually_mem_Icc_of_tendsto_sub_atTop hτ hτ' a a')
      hs' hx (fun t ↦ by simpa using hg' (s, t)) t

/-- Given maps `v_k` whose loops converge uniformly to `x` as `s → ∞`, and shifts `σ_k`, there
are shifts `σ'_k` with `σ'_k - σ_k → ∞` such that the loops of `v_k` at all `s ≥ σ'_k - k` are
within `1 / (k + 1)` of `x`. -/
private theorem exists_tendsto_sub_atTop_forall_dist_lt {X : Type*} [PseudoMetricSpace X]
    {v : ℕ → ℝ × ℝ → X} {x : ℝ → X}
    (hv : ∀ k, TendstoUniformly (fun s t ↦ v k (s, t)) x atTop) (σ : ℕ → ℝ) :
    ∃ σ' : ℕ → ℝ, Tendsto (fun k ↦ σ' k - σ k) atTop atTop ∧
      ∀ k s, σ' k - k ≤ s → ∀ t, dist (x t) (v k (s, t)) < 1 / (k + 1) := by
  choose S hS using fun k : ℕ ↦ eventually_atTop.1
    (Metric.tendstoUniformly_iff.1 (hv k) (1 / (k + 1)) Nat.one_div_pos_of_nat)
  refine ⟨fun k ↦ max (S k) (σ k) + k,
    tendsto_atTop_mono (fun k ↦ ?_) tendsto_natCast_atTop_atTop,
    fun k s hs ↦ hS k s (by linarith [le_max_left (S k) (σ k)])⟩
  linarith [le_max_right (S k) (σ k)]

/-- Given maps `v_k` whose loops converge uniformly to `x` as `s → -∞`, and shifts `σ'_k`, there
are shifts `σ_k` with `σ'_k - σ_k → ∞` such that the loops of `v_k` at all `s ≤ σ_k + k` are
within `1 / (k + 1)` of `x`. -/
private theorem exists_tendsto_sub_atTop_forall_dist_lt' {X : Type*} [PseudoMetricSpace X]
    {v : ℕ → ℝ × ℝ → X} {x : ℝ → X}
    (hv : ∀ k, TendstoUniformly (fun s t ↦ v k (s, t)) x atBot) (σ' : ℕ → ℝ) :
    ∃ σ : ℕ → ℝ, Tendsto (fun k ↦ σ' k - σ k) atTop atTop ∧
      ∀ k s, s ≤ σ k + k → ∀ t, dist (x t) (v k (s, t)) < 1 / (k + 1) := by
  choose S hS using fun k : ℕ ↦ eventually_atBot.1
    (Metric.tendstoUniformly_iff.1 (hv k) (1 / (k + 1)) Nat.one_div_pos_of_nat)
  refine ⟨fun k ↦ min (S k) (σ' k) - k,
    tendsto_atTop_mono (fun k ↦ ?_) tendsto_natCast_atTop_atTop,
    fun k s hs ↦ hS k s (by linarith [min_le_left (S k) (σ' k)])⟩
  linarith [min_le_right (S k) (σ' k)]

/-- If, for all large `k`, the loop of `v_k` at `ς_k` is within `1 / (k + 1)` of `x`, then these
loops converge pointwise to `x`. -/
private theorem tendsto_of_eventually_dist_lt {X : Type*} [PseudoMetricSpace X]
    {v : ℕ → ℝ × ℝ → X} {x : ℝ → X} {ς : ℕ → ℝ}
    (h : ∀ᶠ k in atTop, ∀ t, dist (x t) (v k (ς k, t)) < 1 / (k + 1)) (t : ℝ) :
    Tendsto (fun k ↦ v k (ς k, t)) atTop (𝓝 (x t)) := by
  refine tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero' (Eventually.of_forall fun _ ↦
    dist_nonneg) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [h] with k hk
  exact (dist_comm (v k (ς k, t)) (x t) ▸ hk t).le

/-- **The last level ends at the common end orbit.** Let `H`, `J`, `K` and `u_k` be as in
`TauCeti.SymplecticForm.tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop`,
and suppose that the loops of every `u_k` converge uniformly to the same loop `x` as `s → ∞`. Let
`σ_k` be shifts such that the actions of the loops at `σ_k` are at least `b`, the actions of all
loops of all `u_k` are at most `b'`, and at most one orbit action lies in `[b, b']`. If the
translates `(s, t) ↦ u_k(s + σ_k, t)` converge pointwise to `g`, then `g(s, ·)` converges to `x`
uniformly as `s → ∞`. -/
theorem tendstoUniformly_atTop_of_forall_tendstoUniformly_atTop
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ : ℕ → ℝ} {b b' : ℝ}
    (hσ : ∀ k, b ≤ ω.hamiltonianAction H (fun t ↦ u k (σ k, t)))
    (hA : ∀ k s, ω.hamiltonianAction H (fun t ↦ u k (s, t)) ≤ b')
    (hgap : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc b b').Subsingleton)
    {x : ℝ → V} (hux : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x atTop) {g : ℝ × ℝ → V}
    (hg : ∀ z, Tendsto (fun k ↦ u k (z + (σ k, 0))) atTop (𝓝 (g z))) :
    TendstoUniformly (fun s t ↦ g (s, t)) x atTop := by
  -- Far out along each `u k` its loops are close to `x`; the neck reaches out there.
  obtain ⟨σ', hσσ', hσ'x⟩ := exists_tendsto_sub_atTop_forall_dist_lt hux σ
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  obtain ⟨a, a', hy⟩ := exists_forall_eventually_exists_forall_dist_lt hH hHper hW hJ hJper hK hKW
    hJt hL' hnd hu hper huK hfloer hL hσ (fun k ↦ hA k (σ' k)) hgap hσσ' (ε := ε / 3)
    (by positivity)
  filter_upwards [eventually_ge_atTop a] with s hs t
  have hend : ∀ᶠ k in atTop, σ' k - a' ∈ Icc (σ k + a) (σ' k - a') := by
    filter_upwards [hσσ'.eventually_ge_atTop (a + a')] with k hk
    exact ⟨by linarith, le_rfl⟩
  have hs' : ∀ᶠ k in atTop, s + σ k ∈ Icc (σ k + a) (σ' k - a') := by
    filter_upwards [hσσ'.eventually_ge_atTop (s + a')] with k hk
    exact ⟨by linarith, by linarith⟩
  have hx : ∀ᶠ k in atTop, ∀ t, dist (x t) (u k (σ' k - a', t)) < 1 / (k + 1) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop a'] with k hk
    exact hσ'x k _ (by linarith)
  exact dist_lt_of_eventually_mem hε hy hend hs' (tendsto_of_eventually_dist_lt hx)
    (fun t ↦ by simpa using hg (s, t)) t

/-- **The first level starts at the common start orbit.** Let `H`, `J`, `K` and `u_k` be as in
`TauCeti.SymplecticForm.tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop`,
and suppose that the loops of every `u_k` converge uniformly to the same loop `x` as `s → -∞`.
Let `σ'_k` be shifts such that the actions of the loops at `σ'_k` are at most `b'`, the actions of
all loops of all `u_k` are at least `b`, and at most one orbit action lies in `[b, b']`. If the
translates `(s, t) ↦ u_k(s + σ'_k, t)` converge pointwise to `g'`, then `g'(s, ·)` converges to
`x` uniformly as `s → -∞`. -/
theorem tendstoUniformly_atBot_of_forall_tendstoUniformly_atBot
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ' : ℕ → ℝ} {b b' : ℝ}
    (hσ' : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) ≤ b')
    (hA : ∀ k s, b ≤ ω.hamiltonianAction H (fun t ↦ u k (s, t)))
    (hgap : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc b b').Subsingleton)
    {x : ℝ → V} (hux : ∀ k, TendstoUniformly (fun s t ↦ u k (s, t)) x atBot) {g' : ℝ × ℝ → V}
    (hg' : ∀ z, Tendsto (fun k ↦ u k (z + (σ' k, 0))) atTop (𝓝 (g' z))) :
    TendstoUniformly (fun s t ↦ g' (s, t)) x atBot := by
  -- Far back along each `u k` its loops are close to `x`; the neck reaches back there.
  obtain ⟨σ, hσσ', hσx⟩ := exists_tendsto_sub_atTop_forall_dist_lt' hux σ'
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  obtain ⟨a, a', hy⟩ := exists_forall_eventually_exists_forall_dist_lt hH hHper hW hJ hJper hK hKW
    hJt hL' hnd hu hper huK hfloer hL (fun k ↦ hA k (σ k)) hσ' hgap hσσ' (ε := ε / 3)
    (by positivity)
  filter_upwards [eventually_le_atBot (-a')] with s hs t
  have hstart : ∀ᶠ k in atTop, σ k + a ∈ Icc (σ k + a) (σ' k - a') := by
    filter_upwards [hσσ'.eventually_ge_atTop (a + a')] with k hk
    exact ⟨le_rfl, by linarith⟩
  have hs' : ∀ᶠ k in atTop, s + σ' k ∈ Icc (σ k + a) (σ' k - a') := by
    filter_upwards [hσσ'.eventually_ge_atTop (a - s)] with k hk
    exact ⟨by linarith, by linarith⟩
  have hx : ∀ᶠ k in atTop, ∀ t, dist (x t) (u k (σ k + a, t)) < 1 / (k + 1) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop a] with k hk
    exact hσx k _ (by linarith)
  exact dist_lt_of_eventually_mem hε hy hstart hs' (tendsto_of_eventually_dist_lt hx)
    (fun t ↦ by simpa using hg' (s, t)) t

/-- **Breaking sequences of Floer trajectories converge to broken trajectories.** Let `H`, `J`
and `K` be as in
`TauCeti.SymplecticForm.tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop`,
and let `u_k` be `C³` Floer trajectories with `1`-periodic loops in `K` and a common Lipschitz
constant. Let `b 0 < b 1 < ⋯ < b m` be values none of which is the action of a `1`-periodic
orbit in `K`, with at most one orbit action in each `[b i, b (i + 1)]`, and let `σ i k` be shifts
with `A_H(u k (σ i k, ·)) = b i`. Then there is a subsequence `u (φ n)` such that:

* for every `i`, the translates `(s, t) ↦ u (φ n) (s + σ i (φ n), t)` converge locally uniformly to
  a map `g i` which is not stationary;
* for every `i < m`, either the shifts `σ (i + 1) (φ n) - σ i (φ n)` converge to some `δ` and
  `g (i + 1)` is the translate `z ↦ g i (z + (δ, 0))`, or these shifts tend to infinity and there
  is a `1`-periodic orbit `x` in `K`, with action in `(b i, b (i + 1))`, such that `g i (s, ·)`
  converges to `x` uniformly as `s → ∞` and `g (i + 1) (s, ·)` converges to `x` uniformly as
  `s → -∞`. -/
theorem exists_subseq_forall_tendstoLocallyUniformly_comp_add_and_tendstoUniformly
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJper : Periodic J 1) (hK : IsCompact K) (hKW : univ ×ˢ K ⊆ W)
    (hJt : ∀ t, ∀ x ∈ K, ω.Tames (J t x))
    (hL' : LipschitzWith L' (ω.timeDependentHamiltonianSuspension H))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) → (∀ t, x t ∈ K) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hL' 0 1) (x 0))
    (hu : ∀ k, ContDiff ℝ 3 (u k)) (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1)
    (huK : ∀ k z, u k z ∈ K)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z.2 (u k z))
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {m : ℕ} {b : Fin (m + 1) → ℝ} (hb : StrictMono b)
    (hbreg : ∀ i, b i ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    (hgap : ∀ i : Fin m, (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
        Icc (b i.castSucc) (b i.succ)).Subsingleton)
    {σ : Fin (m + 1) → ℕ → ℝ}
    (hσ : ∀ i k, ω.hamiltonianAction H (fun t ↦ u k (σ i k, t)) = b i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Fin (m + 1) → ℝ × ℝ → V,
      (∀ i, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (σ i (φ n), 0))) (g i) atTop ∧
        ∃ s t, g i (s, t) ≠ g i (0, t)) ∧
      ∀ i : Fin m,
        (∃ δ, Tendsto (fun n ↦ σ i.succ (φ n) - σ i.castSucc (φ n)) atTop (𝓝 δ) ∧
          ∀ z, g i.succ z = g i.castSucc (z + (δ, 0))) ∨
        (Tendsto (fun n ↦ σ i.succ (φ n) - σ i.castSucc (φ n)) atTop atTop ∧
          ∃ x : ℝ → V, Periodic x 1 ∧
            (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ (∀ t, x t ∈ K) ∧
            ω.hamiltonianAction H x ∈ Ioo (b i.castSucc) (b i.succ) ∧
            TendstoUniformly (fun s t ↦ g i.castSucc (s, t)) x atTop ∧
            TendstoUniformly (fun s t ↦ g i.succ (s, t)) x atBot) := by
  obtain ⟨c₀, hc₀, M₀, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hK
    (hJ.continuousOn.mono hKW) hJper hJt
  obtain ⟨φ, hφ, g, hg, hlev⟩ :=
    exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq
      (J := fun k z ↦ J z.2 (u k z)) (hH.of_le (by norm_num)) hHper hK
      (fun k ↦ (hu k).of_le (by norm_num)) hper huK hc₀ (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).1)
      (fun k z _ v ↦ (hcM z.2 _ (huK k z) v).2) hfloer hL hb hbreg hσ
  refine ⟨φ, hφ, g, hg, fun i ↦ (hlev i).imp_right ?_⟩
  rintro ⟨hgap', τ, x, hxper, hxd, hxK, hxA, hτ, hτ', hux⟩
  -- The levels on both sides of the neck converge to the neck orbit.
  refine ⟨hgap', x, hxper, hxd, hxK, hxA,
    tendstoUniformly_atTop_and_tendstoUniformly_atBot_of_tendsto_sub_atTop (u := u ∘ φ) hH hHper
      hW hJ hJper hK hKW hJt hL' hnd (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _)
      (fun _ ↦ hfloer _) (fun _ ↦ hL _) (fun k ↦ (hσ _ _).ge) (fun k ↦ (hσ _ _).le) (hgap i) hτ hτ'
      (fun z ↦ (hg _).1.tendsto_at z) (fun z ↦ (hg _).1.tendsto_at z)
      fun t ↦ by simpa using hux.tendsto_at (0, t)⟩

end TauCeti.SymplecticForm
