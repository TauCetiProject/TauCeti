/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Trajectory.Level
public import TauCeti.Geometry.Symplectic.Floer.Trajectory.Neck
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Instances.Real.SeparatingGrid
import TauCeti.Topology.MetricSpace.Lipschitz.Basic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Selecting the levels of a breaking sequence of Floer trajectories

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C¹` Hamiltonian, `1`-periodic in
time, and `K ⊆ V` a compact set. Let `u_k` be Floer trajectories, solutions of
`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops in `K`, uniformly tame almost
complex structures and a common Lipschitz constant. A *regular action value* is a real number which
is not the action `A_H` of any `1`-periodic orbit of the Hamiltonian vector field with values in
`K`. The action of the loop `u_k(s, ·)` increases with `s`, so normalizing the trajectories at a
regular action value `b` means choosing shifts `σ_k` with `A_H(u_k(σ_k, ·)) = b`. A limit of the
translates `(s, t) ↦ u_k(s + σ_k, t)` is then a nonstationary *level* of the sequence
(`TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`).

This file assembles finitely many such levels into the picture of a breaking sequence. Fix regular
action values `b₀ < b₁ < ⋯ < b_m` and shifts `σ_i k` normalizing `u_k` at `b_i`. After passing to
one subsequence, the main theorem
`SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq`
gives:

* **One level at each value.** For every `i`, the translates of the `u_k` at `σ_i` converge
  locally uniformly to a nonstationary map `g_i`.
* **Consecutive levels are equal or separated by a neck.** For every `i < m`, exactly as in
  Floer's picture of a broken trajectory, one of two things happens. Either the shifts stay a
  bounded distance apart, `σ_{i+1} k - σ_i k → δ`, and then the two levels are the same trajectory
  up to translation, `g_{i+1}(s, t) = g_i(s + δ, t)`. Or the shifts drift apart,
  `σ_{i+1} k - σ_i k → ∞`, and then between them there are shifts `τ_k`, infinitely far from both,
  at which the trajectories converge to the stationary cylinder `(s, t) ↦ x(t)` over a
  `1`-periodic orbit `x` in `K` whose action lies strictly between `b_i` and `b_{i+1}`.

When `[b_i, b_{i+1}]` contains a single orbit action `c`, the second alternative is the breaking of
the sequence at an orbit of action `c`, and the first says that the level `g_i` runs through the
action `c` without breaking there.

Such normalizations exist for every sequence of nonstationary trajectories when the orbit actions
in `K` form a finite set, as they do when the orbits are nondegenerate
(`SymplecticForm.exists_subseq_forall_hamiltonianAction_eq_of_floer`). Along a subsequence the
actions of all the trajectories run from the same orbit action `a₀` to the same `a₁ > a₀`, and
there are values `b_0 < ⋯ < b_m`, none of them an orbit action, with exactly one orbit action in
each `[b_i, b_{i+1}]` and none in `[a₀, b_0]` or `[b_m, a₁]` other than `a₀` and `a₁`
(`Set.Finite.exists_strictMono_notMem_inter_Icc_eq_singleton`). With these values, at each
orbit action strictly between `a₀` and `a₁` either the levels on its two sides coincide up to
translation or the sequence breaks at a neck over an orbit of that action.

As in `TauCeti.Geometry.Symplectic.Floer.Trajectory.Level`, the uniform bound on the derivatives
excludes bubbling; it is assumed, not proved. The levels `g_i` are only continuous limits, so the
identification of the orbits at the ends of each level with the neck orbits is not made here.

## Main results

* `SymplecticForm.exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq`:
  along one subsequence, the trajectories normalized at finitely many regular action values have
  nonstationary limits, and consecutive limits are either translates of each other or separated by
  a neck converging to an orbit with action between the two values.
* `SymplecticForm.exists_subseq_forall_hamiltonianAction_eq_of_floer`: a sequence of nonstationary
  trajectories has a subsequence with common end actions `a₀ < a₁`, normalized at regular action
  values separating the orbit actions in `[a₀, a₁]`.

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547, on the convergence of sequences of trajectories to broken trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on compactness up to breaking.
* M. Audin and M. Damian, *Morse theory and Floer homology*, Springer Universitext (2014),
  Chapter 9, on the compactness of spaces of Floer trajectories.
-/

public section

open Set Filter Topology Function
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {K : Set V} {J : ℕ → ℝ × ℝ → AlmostComplexStructure V}
  {c M : ℝ} {L : ℝ≥0}

variable (ω H K) in
/-- The relation between two consecutive levels of a sequence `u` normalized by shifts `σ` and
`σ'` at action values `b` and `b'`: either the shifts `σ' n - σ n` converge, or they tend to
infinity and between them there are shifts `τ n`, infinitely far from both, at which the
translates of `u n` converge to the stationary cylinder over an orbit in `K` with action in
`(b, b')`. -/
private def IsLevelGap (u : ℕ → ℝ × ℝ → V) (σ σ' : ℕ → ℝ) (b b' : ℝ) : Prop :=
  (∃ δ, Tendsto (fun n ↦ σ' n - σ n) atTop (𝓝 δ)) ∨
    (Tendsto (fun n ↦ σ' n - σ n) atTop atTop ∧
      ∃ τ : ℕ → ℝ, ∃ x : ℝ → V, Periodic x 1 ∧
        (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ (∀ t, x t ∈ K) ∧
        ω.hamiltonianAction H x ∈ Ioo b b' ∧ Tendsto (fun n ↦ τ n - σ n) atTop atTop ∧
        Tendsto (fun n ↦ σ' n - τ n) atTop atTop ∧
        TendstoLocallyUniformly (fun n z ↦ u n (z + (τ n, 0))) (fun z ↦ x z.2) atTop)

/-- The relation between two levels passes to subsequences. -/
private theorem IsLevelGap.comp {u : ℕ → ℝ × ℝ → V} {σ σ' : ℕ → ℝ} {b b' : ℝ}
    (h : IsLevelGap ω H K u σ σ' b b') {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    IsLevelGap ω H K (u ∘ ψ) (σ ∘ ψ) (σ' ∘ ψ) b b' := by
  have hψt := hψ.tendsto_atTop
  rcases h with ⟨δ, hδ⟩ | ⟨hgap, τ, x, hxper, hxd, hxK, hxA, hτ, hτ', hux⟩
  · exact Or.inl ⟨δ, hδ.comp hψt⟩
  · exact Or.inr ⟨hgap.comp hψt, τ ∘ ψ, x, hxper, hxd, hxK, hxA, hτ.comp hψt, hτ'.comp hψt,
      hux.comp_tendsto hψt⟩

/-- **Two levels are equal or separated by a neck.** Let `u k` be Floer trajectories as in
`TauCeti.SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop`,
normalized by shifts `σ k ≤ σ' k` at regular action values `b` and `b'`. Along a subsequence,
either `σ' - σ` converges or the two normalizations are separated by a neck over an orbit with
action in `(b, b')`. -/
private theorem exists_subseq_isLevelGap (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1)
    (hK : IsCompact K) {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ} {b b' : ℝ}
    (hb : b ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    (hb' : b' ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    (hσ : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ k, t)) = b)
    (hσ' : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) = b')
    (hσσ' : ∀ k, σ k ≤ σ' k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsLevelGap ω H K (u ∘ φ) (σ ∘ φ) (σ' ∘ φ) b b' := by
  by_cases hgap : Tendsto (fun k ↦ σ' k - σ k) atTop atTop
  · -- The normalizations drift apart: a neck between them converges to an orbit `x`.
    obtain ⟨φ, hφ, τ, x, hxper, hxd, hxK, hτσ, hσ'τ, hux, hA⟩ :=
      exists_subseq_tendstoLocallyUniformly_comp_add_of_tendsto_sub_atTop hH hHper hK hu hper
        huK hc hJc hJM hfloer hL hgap
    have hmono (k : ℕ) := ω.monotone_hamiltonianAction_of_floer hH (hu k) (hper k)
      (fun z hz ↦ tames_of_mul_norm_sq_le hc (hJc k z hz)) (hfloer k)
    -- The action of `x` is the limit of the actions at `τ`, which lie between `b` and `b'`.
    have hτA : Tendsto (fun n ↦ ω.hamiltonianAction H (fun t ↦ u (φ n) (τ n, t))) atTop
        (𝓝 (ω.hamiltonianAction H x)) := by
      simpa using hA.add_const (ω.hamiltonianAction H x)
    have hle : b ≤ ω.hamiltonianAction H x := ge_of_tendsto hτA <| by
      filter_upwards [hτσ.eventually_ge_atTop 0] with n hn
      exact (hσ (φ n)).symm.trans_le (hmono (φ n) (by linarith))
    have hge : ω.hamiltonianAction H x ≤ b' := le_of_tendsto hτA <| by
      filter_upwards [hσ'τ.eventually_ge_atTop 0] with n hn
      exact (hmono (φ n) (by linarith)).trans_eq (hσ' (φ n))
    -- Neither endpoint is the action of an orbit.
    have hxΛ : ω.hamiltonianAction H x ∈ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
        (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} :=
      ⟨x, ⟨hxper, hxd, hxK⟩, rfl⟩
    exact ⟨φ, hφ, Or.inr ⟨hgap.comp hφ.tendsto_atTop, τ, x, hxper, hxd, hxK,
      ⟨hle.lt_of_ne fun h ↦ hb (h ▸ hxΛ), hge.lt_of_ne fun h ↦ hb' (h ▸ hxΛ)⟩, hτσ, hσ'τ, hux⟩⟩
  · -- Otherwise the nonnegative shifts `σ' - σ` are frequently bounded, so a subsequence of them
    -- converges.
    simp only [tendsto_atTop, not_forall, not_eventually, not_le] at hgap
    obtain ⟨N, hN⟩ := hgap
    obtain ⟨φ₁, hφ₁, hφ₁N⟩ := extraction_of_frequently_atTop hN
    obtain ⟨δ, -, φ₂, hφ₂, hδ⟩ := (isCompact_Icc (a := 0) (b := N)).tendsto_subseq
      (x := fun n ↦ σ' (φ₁ n) - σ (φ₁ n)) fun n ↦ ⟨sub_nonneg.2 (hσσ' _), (hφ₁N n).le⟩
    exact ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, Or.inl ⟨δ, hδ⟩⟩

/-- **The levels of a breaking sequence of Floer trajectories.** Let `H` be a `C¹` Hamiltonian,
`1`-periodic in time, and `K` a compact set. Let `u k` be `C²` solutions of the Floer equation
`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with `1`-periodic loops in `K`, uniformly
tame almost complex structures, `c ‖v‖² ≤ ω(v, J_k z v)` and `‖J_k z v‖ ≤ M ‖v‖` with `c > 0`, and
a common Lipschitz constant `L`. Let `b 0 < b 1 < ⋯ < b m` be values none of which is the action of
a `1`-periodic orbit of the Hamiltonian vector field with values in `K`, and let `σ i k` be shifts
with `A_H(u k (σ i k, ·)) = b i`. Then there is a subsequence `u (φ n)` such that:

* for every `i`, the translates `(s, t) ↦ u (φ n) (s + σ i (φ n), t)` converge locally uniformly to
  a map `g i` which is not stationary: `g i (s, t) ≠ g i (0, t)` for some `s` and `t`;
* for every `i < m`, either the shifts `σ (i + 1) (φ n) - σ i (φ n)` converge to some `δ` and
  `g (i + 1)` is the translate `z ↦ g i (z + (δ, 0))`, or these shifts tend to infinity and there
  are shifts `τ n` with `τ n - σ i (φ n) → ∞` and `σ (i + 1) (φ n) - τ n → ∞` such that the
  translates `(s, t) ↦ u (φ n) (s + τ n, t)` converge locally uniformly to the stationary cylinder
  `(s, t) ↦ x(t)` over a `1`-periodic orbit `x` in `K` with action in `(b i, b (i + 1))`. -/
theorem exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {m : ℕ} {b : Fin (m + 1) → ℝ} (hb : StrictMono b)
    (hbreg : ∀ i, b i ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    {σ : Fin (m + 1) → ℕ → ℝ}
    (hσ : ∀ i k, ω.hamiltonianAction H (fun t ↦ u k (σ i k, t)) = b i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : Fin (m + 1) → ℝ × ℝ → V,
      (∀ i, TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (σ i (φ n), 0))) (g i) atTop ∧
        ∃ s t, g i (s, t) ≠ g i (0, t)) ∧
      ∀ i : Fin m,
        (∃ δ, Tendsto (fun n ↦ σ i.succ (φ n) - σ i.castSucc (φ n)) atTop (𝓝 δ) ∧
          ∀ z, g i.succ z = g i.castSucc (z + (δ, 0))) ∨
        (Tendsto (fun n ↦ σ i.succ (φ n) - σ i.castSucc (φ n)) atTop atTop ∧
          ∃ τ : ℕ → ℝ, ∃ x : ℝ → V, Periodic x 1 ∧
            (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ (∀ t, x t ∈ K) ∧
            ω.hamiltonianAction H x ∈ Ioo (b i.castSucc) (b i.succ) ∧
            Tendsto (fun n ↦ τ n - σ i.castSucc (φ n)) atTop atTop ∧
            Tendsto (fun n ↦ σ i.succ (φ n) - τ n) atTop atTop ∧
            TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (τ n, 0))) (fun z ↦ x z.2) atTop) := by
  -- The action increases along each trajectory, so the shifts increase with the action values.
  have hσσ' (i : Fin m) (k : ℕ) : σ i.castSucc k ≤ σ i.succ k := by
    by_contra! h
    have hmono := ω.monotone_hamiltonianAction_of_floer hH (hu k) (hper k)
      (fun z hz ↦ tames_of_mul_norm_sq_le hc (hJc k z hz)) (hfloer k) h.le
    simp only [hσ] at hmono
    exact (hb Fin.castSucc_lt_succ).not_ge hmono
  -- Along one subsequence the translates at every `σ i` converge.
  obtain ⟨φ₀, hφ₀, hconv⟩ := extraction_forall_mem_finset (s := Finset.univ)
    (P := fun i ψ ↦ ∃ g, TendstoLocallyUniformly (fun n z ↦ u (ψ n) (z + (σ i (ψ n), 0))) g atTop)
    (fun i _ ψ _ ↦ by
      obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith hK
        (u := fun n ↦ u (ψ n)) (fun _ ↦ hL _) (fun _ ↦ huK _) fun n ↦ σ i (ψ n)
      exact ⟨φ, hφ, g, hg⟩)
    fun i _ ψ ψ' hψ' ⟨g, hg⟩ ↦ ⟨g, hg.comp_tendsto hψ'.tendsto_atTop⟩
  choose g hg using fun i ↦ hconv i (Finset.mem_univ i)
  -- Along a further subsequence every pair of consecutive normalizations has converging shifts
  -- or a neck between them.
  obtain ⟨ψ, hψ, hgap⟩ := extraction_forall_mem_finset (s := Finset.univ)
    (P := fun (i : Fin m) ψ ↦ IsLevelGap ω H K (u ∘ φ₀ ∘ ψ) (σ i.castSucc ∘ φ₀ ∘ ψ)
      (σ i.succ ∘ φ₀ ∘ ψ) (b i.castSucc) (b i.succ))
    (fun i _ ψ _ ↦ exists_subseq_isLevelGap (u := u ∘ φ₀ ∘ ψ) (J := J ∘ φ₀ ∘ ψ) hH hHper hK
      (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _) hc (fun _ ↦ hJc _) (fun _ ↦ hJM _)
      (fun _ ↦ hfloer _) (fun _ ↦ hL _) (hbreg _) (hbreg _) (fun _ ↦ hσ _ _) (fun _ ↦ hσ _ _)
      fun _ ↦ hσσ' i _)
    fun i _ ψ ψ' hψ' h ↦ h.comp hψ'
  have hψt := hψ.tendsto_atTop
  refine ⟨φ₀ ∘ ψ, hφ₀.comp hψ, g, fun i ↦ ⟨(hg i).comp_tendsto hψt, ?_⟩, fun i ↦ ?_⟩
  · -- Each limit is normalized at a regular action value, so it is not stationary.
    exact exists_apply_ne_apply_zero_of_tendstoLocallyUniformly_comp_add (u := u ∘ φ₀ ∘ ψ)
      (J := J ∘ φ₀ ∘ ψ) hH hHper hK.isClosed (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _) hc
      (fun _ ↦ hJc _) (fun _ ↦ hJM _) (fun _ ↦ hfloer _) (fun _ ↦ hL _) (hbreg i)
      (by simp [hσ]) ((hg i).comp_tendsto hψt)
  · rcases hgap i (Finset.mem_univ i) with ⟨δ, hδ⟩ | hneck
    · -- Converging shifts: the two limits are translates of each other.
      exact Or.inl ⟨δ, hδ, apply_eq_apply_add_prodMk_zero_of_tendsto_sub
        (u := fun n ↦ u (φ₀ (ψ n))) (fun _ ↦ hL _) (σ := fun n ↦ σ i.castSucc (φ₀ (ψ n)))
        (σ' := fun n ↦ σ i.succ (φ₀ (ψ n))) hδ ((hg _).comp_tendsto hψt).tendsto_at
        ((hg _).comp_tendsto hψt).tendsto_at⟩
    · exact Or.inr hneck

/-- **Normalizing a breaking sequence between consecutive orbit actions.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, and `K` a compact set such that the `1`-periodic orbits of the
Hamiltonian vector field with values in `K` have only finitely many actions. Let `u k` be
nonstationary `C²` solutions of the Floer equation `∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on
`ℝ × [0, 1]`, with `1`-periodic loops in `K`, uniformly tame almost complex structures,
`c ‖v‖² ≤ ω(v, J_k z v)` and `‖J_k z v‖ ≤ M ‖v‖` with `c > 0`, and a common Lipschitz constant
`L`. Then there is a subsequence `u (φ n)` whose actions all run from `a₀` at `s → -∞` to
`a₁ > a₀` at `s → ∞`, together with values `b 0 < ⋯ < b m`, none of them an orbit action, that
separate the orbit actions in `[a₀, a₁]`: `a₀` is the only orbit action in `[a₀, b 0]`, `a₁` the
only one in `[b m, a₁]`, and each `[b i, b (i + 1)]` contains exactly one; and there are shifts
`σ i n` with `A_H(u (φ n) (σ i n, ·)) = b i`. These are normalizations to which
`exists_subseq_forall_tendstoLocallyUniformly_comp_add_of_hamiltonianAction_eq` applies, with one
level for each gap between consecutive orbit actions in `[a₀, a₁]`. -/
theorem exists_subseq_forall_hamiltonianAction_eq_of_floer (hH : ContDiff ℝ 1 (uncurry H))
    (hHper : Periodic H 1) (hK : IsCompact K)
    (hfin : (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}).Finite)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) (hns : ∀ k, ∃ s t, u k (s, t) ≠ u k (0, t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a₀ a₁ : ℝ, a₀ < a₁ ∧
      (∀ n, Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (φ n) (s, t))) atBot (𝓝 a₀) ∧
        Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (φ n) (s, t))) atTop (𝓝 a₁)) ∧
      ∃ m : ℕ, ∃ b : Fin (m + 1) → ℝ, StrictMono b ∧
        (∀ i, b i ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
          (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}) ∧
        ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
          (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
            Icc a₀ (b 0) = {a₀} ∧
        ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
          (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
            Icc (b (Fin.last m)) a₁ = {a₁} ∧
        (∀ i : Fin m, ∃ c', ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
          (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K} ∩
            Icc (b i.castSucc) (b i.succ) = {c'}) ∧
        ∃ σ : Fin (m + 1) → ℕ → ℝ,
          ∀ i n, ω.hamiltonianAction H (fun t ↦ u (φ n) (σ i n, t)) = b i := by
  -- Each trajectory runs from an orbit of action `a₀ k` to an orbit of larger action `a₁ k`.
  choose a₀ ha₀ a₁ ha₁ hlt hbot htop using fun k ↦ exists_lt_tendsto_hamiltonianAction_of_floer hH
    hHper hK hfin (hu k) (hper k) (huK k) hc (hJc k) (hJM k) (hfloer k) (hL k) (hns k)
  -- The pairs of end actions range over a finite set, so one pair `(A₀, A₁)` occurs infinitely
  -- often.
  set Λ := ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
    (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}
  have := (hfin.prod hfin).to_subtype
  obtain ⟨⟨⟨A₀, A₁⟩, hA₀, hA₁⟩, hp⟩ := Finite.exists_infinite_fiber fun k ↦
    (⟨(a₀ k, a₁ k), ha₀ k, ha₁ k⟩ : ↥(Λ ×ˢ Λ))
  obtain ⟨φ, hφ, hφp⟩ := extraction_of_frequently_atTop
    (Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 hp))
  have hends (n : ℕ) : a₀ (φ n) = A₀ ∧ a₁ (φ n) = A₁ :=
    Prod.ext_iff.1 (congrArg Subtype.val (Set.mem_singleton_iff.1 (hφp n)))
  have hA : A₀ < A₁ := (hends 0).1 ▸ (hends 0).2 ▸ hlt (φ 0)
  -- Values separating the orbit actions in `[A₀, A₁]`.
  obtain ⟨m, b, hb, hbC, hb0, hbm, h0, h1, hgaps⟩ :=
    hfin.exists_strictMono_notMem_inter_Icc_eq_singleton hA₀ hA₁ hA
  -- Each trajectory of the subsequence takes each value `b i` as the action of one of its loops.
  have hσ (i : Fin (m + 1)) (n : ℕ) :
      ∃ σ, ω.hamiltonianAction H (fun t ↦ u (φ n) (σ, t)) = b i := by
    have hbi₀ : a₀ (φ n) < b i := (hends n).1 ▸ hb0.trans_le (hb.monotone (Fin.zero_le i))
    have hbi₁ : b i < a₁ (φ n) := (hends n).2 ▸ (hb.monotone (Fin.le_last i)).trans_lt hbm
    exact exists_hamiltonianAction_slice_eq_of_tendsto hH.continuous
      ((hu (φ n)).of_le one_le_two) (hbot (φ n)) (htop (φ n)) ⟨hbi₀, hbi₁⟩
  choose σ hσ using hσ
  exact ⟨φ, hφ, A₀, A₁, hA, fun n ↦ ⟨(hends n).1 ▸ hbot (φ n), (hends n).2 ▸ htop (φ n)⟩,
    m, b, hb, hbC, h0, h1, hgaps, σ, hσ⟩

end TauCeti.SymplecticForm
