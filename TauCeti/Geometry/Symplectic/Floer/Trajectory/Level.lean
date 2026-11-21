/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Trajectory
import TauCeti.Algebra.Order.BigOperators.Sum.SubSumBound
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Breaking
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.MetricSpace.Lipschitz.Basic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Nonstationary levels of sequences of Floer trajectories

Let `(V, ω)` be a symplectic vector space, `H : ℝ → V → ℝ` a `C¹` Hamiltonian, `1`-periodic in
time, and `K ⊆ V` a compact set. A sequence of Floer trajectories `u_k`, solutions of
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with `1`-periodic loops in `K`, can break: its energy may
split into several pieces which drift apart in `s`, so that no translates of the `u_k` converge to
a single trajectory carrying all of it. Their limit is a broken trajectory, a chain of
nonstationary trajectories, its *levels*, joined at `1`-periodic orbits. Translated along a neck
between two levels, the trajectories converge to the stationary cylinder over an orbit
(`exists_subseq_periodic_hasDerivAt_tendstoLocallyUniformly_of_tendsto_setLIntegral` in the
namespace `TauCeti.SymplecticForm`), and loops far apart along the trajectories are joined by such
necks (`TauCeti.Geometry.Symplectic.Floer.Trajectory.Neck`). This file finds nonstationary
levels.

The levels are located by the action `A_H`. Along a Floer trajectory `u` the action
`A_H(u(s, ·))` of the loop at `s` increases from the action of the orbit at `-∞` to the action of
the orbit at `+∞`. Call `a` a *regular action value* if it is not the action of any `1`-periodic
orbit in `K`.

* **A level at each regular action value.** If the loops `u_k(0, ·)` have actions tending to a
  regular action value `a`, the derivatives of the `u_k` are uniformly bounded, and the `u_k`
  converge locally uniformly to `g`, then `g` is not stationary: `g(s, t) ≠ g(0, t)` for some `s`
  and `t` (`SymplecticForm.exists_apply_ne_apply_zero_of_tendstoLocallyUniformly`). Otherwise
  the energy of the `u_k` over every window `[α, β] × [0, 1]`, the difference of the actions of
  its two boundary loops, would tend to zero, so `x(t) = g(0, t)` would be a `1`-periodic orbit
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_of_tendsto_setLIntegral_comp_add`), and the
  actions of the loops `u_k(0, ·)` would tend to the action of `x`, which is not `a`
  (`SymplecticForm.tendsto_hamiltonianAction_sub_hamiltonianAction_of_tendstoLocallyUniformly`).
* **Every sequence of nonstationary trajectories has a nonstationary level.** Suppose that the
  `1`-periodic orbits in `K` have only finitely many actions, as happens when they are all
  nondegenerate, and that the trajectories `u_k` are nonstationary with uniformly bounded
  derivatives. Then there are a subsequence `u_(φ n)` and shifts `σ_n` such that the translates
  `(s, t) ↦ u_(φ n)(s + σ_n, t)` converge locally uniformly to a map `g` which is not stationary
  (`SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_floer`). The ends of
  each `u_k` are orbits whose actions `a₀ < a₁` lie in the finite set of orbit actions
  (`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`), and they
  differ by the energy gap
  (`TauCeti.SymplecticForm.exists_pos_forall_ofReal_le_lintegral_floerEnergyDensity`). Choosing a
  regular action value `b` between them, the shift `σ` puts the loop of action `b` at `s = 0`, by
  the continuity of the action along the trajectory
  (`TauCeti.SymplecticForm.continuous_hamiltonianAction_slice`). The chosen values range over a
  finite set, so along a subsequence they converge to a regular action value, and the
  Arzelà–Ascoli theorem for translates
  (`TauCeti.exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith`) gives a convergent
  subsequence of the translates. No energy bound is assumed: the actions of loops in `K` of
  bounded speed are bounded
  (`TauCeti.SymplecticForm.exists_forall_abs_hamiltonianAction_le`), so each trajectory has finite
  energy and its ends have actions `a₀ < a₁`
  (`TauCeti.SymplecticForm.exists_lt_tendsto_hamiltonianAction_of_floer`).
* **Trajectories spend a bounded time in a regular action window.** If an interval `[a, b]`
  contains no action of a `1`-periodic orbit in `K`, there is a time `T`, depending only on `ω`,
  `H`, `K`, `[a, b]`, the tameness constants and the Lipschitz constant, such that the loops of
  every Floer trajectory with actions in `[a, b]` lie within an interval of `s`-values of length at
  most `T` (`SymplecticForm.exists_forall_sub_le_of_floer`). Otherwise, windows of length tending
  to infinity in which the action stays in `[a, b]` would contain windows of vanishing energy, and
  the translates centred there would converge to a stationary cylinder over an orbit whose action
  lies in `[a, b]`.
* **Translates in a common regular action window have the same limit up to translation.**
  Consequently, if the loops of a sequence of trajectories at shifts `σ k` and `σ' k` have
  actions in a common interval `[a, b]` containing no orbit action, for every `k`, then the limits
  of the translates at `σ k` and at `σ' k` are translates of each other
  (`SymplecticForm.exists_eq_comp_add_of_tendstoLocallyUniformly`). When the orbit actions in `K`
  form a finite set, every regular action value lies in such an interval, so after passing to a
  tail of the sequence, normalizing at regular action values gives, up to translation, at most one
  level for each gap between consecutive orbit actions; this consequence is not stated here.

The uniform bound on the derivatives excludes bubbling; it is assumed, not proved. The limit `g`
is only shown to be continuous here; its regularity is not treated. For smooth solutions with
bounded derivatives, read in the complex coordinate `z = s + i t`, it is the subject of
`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_floer`.

## Main results

* `SymplecticForm.exists_apply_ne_apply_zero_of_tendstoLocallyUniformly`: a limit of Floer
  trajectories normalized at a regular action value is not stationary.
* `SymplecticForm.exists_apply_ne_apply_zero_of_tendstoLocallyUniformly_comp_add`: the same for
  translates normalized at a regular action value.
* `SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_floer`: a sequence of
  nonstationary Floer trajectories with bounded derivatives has translates converging to a
  nonstationary limit.
* `SymplecticForm.exists_forall_sub_le_of_floer`: Floer trajectories spend a uniformly bounded time
  in a regular action window.
* `SymplecticForm.exists_eq_comp_add_of_tendstoLocallyUniformly`: limits of translates at shifts
  whose loops have actions in a common regular action window are translates of each other.

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

/-- The Floer energy over a window `[α, β] × [0, 1]` of a `C²` solution of the Floer equation for
tame almost complex structures is the integral of its energy density, which is continuous and
nonnegative there. -/
private theorem setLIntegral_ofReal_floerEnergyDensity (hH : ContDiff ℝ 1 (uncurry H))
    {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} (hu : ContDiff ℝ 2 u) (hc : 0 < c)
    (hJc : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) (α β : ℝ) :
    ∫⁻ z in Icc α β ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (∫ z in Icc α β ×ˢ Icc 0 1,
        ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  have hsub : Icc α β ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  exact (ofReal_integral_eq_lintegral_ofReal
    ((ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) isOpen_univ
      (hu.of_le one_le_two).contDiffOn contDiffOn_const
      (contDiff_uncurry_cylindrical hH).contDiffOn).mono (subset_univ _) |>.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc))
    (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      ω.floerEnergyDensity_nonneg (tames_of_mul_norm_sq_le hc (hJc z (hsub hz)))
        (hfloer z (hsub hz)))).symm

/-- Along Floer trajectories converging to a stationary limit, the energy over every window
`[α, β] × [0, 1]` tends to zero: it is the difference of the actions of the two boundary loops,
which converge uniformly to the same loop. -/
private theorem tendsto_setLIntegral_floerEnergyDensity_of_forall_eq
    (hH : ContDiff ℝ 1 (uncurry H)) {f : ℕ → ℝ × ℝ → V} (hf : ∀ k, ContDiff ℝ 2 (f k))
    (hper : ∀ k s, Periodic (fun t ↦ f k (s, t)) 1) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (f k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (f k)) {g : ℝ × ℝ → V} (hg : TendstoLocallyUniformly f g atTop)
    (hst : ∀ s t, g (s, t) = g (0, t)) (α β : ℝ) :
    Tendsto (fun k ↦ ∫⁻ z in Icc α β ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (f k) z)) atTop (𝓝 0) := by
  rcases lt_or_ge β α with hβα | hαβ
  · simp [Icc_eq_empty_of_lt hβα]
  have hslice (s : ℝ) :
      TendstoUniformlyOn (fun k t ↦ f k (s, t)) (fun t ↦ g (s, t)) atTop (Icc 0 1) :=
    (hg.tendstoLocallyUniformlyOn (s := univ)).tendstoUniformlyOn_slice_right isCompact_Icc
      fun _ _ ↦ mem_univ _
  have hL' (k : ℕ) (z : ℝ × ℝ) : ‖fderiv ℝ (f k) z‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ (hL k)
  have hE := ω.tendsto_integral_floerEnergyDensity_of_tendstoUniformlyOn hH isOpen_univ
    (Eventually.of_forall fun k ↦ (hf k).contDiffOn) hαβ (subset_univ _)
    (Eventually.of_forall fun k s _ ↦ by simpa using hper k s 0)
    (Eventually.of_forall fun k t _ ↦ ⟨hL' k _, hL' k _⟩) (hslice α)
    ((hslice β).congr_right fun t _ ↦ (hst β t).trans (hst α t).symm)
  rw [← ENNReal.ofReal_zero]
  exact (ENNReal.tendsto_ofReal hE).congr fun k ↦
    (setLIntegral_ofReal_floerEnergyDensity hH (hf k) hc (hJc k) (hfloer k) α β).symm

/-- A stationary limit of Floer trajectories with uniformly bounded derivatives is the stationary
cylinder over a `1`-periodic orbit: `t ↦ g(0, t)` is a `1`-periodic orbit of the Hamiltonian
vector field, with values in `K` when the trajectories have values in the closed set `K`. -/
private theorem periodic_hasDerivAt_of_forall_eq
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsClosed K)
    {f : ℕ → ℝ × ℝ → V} (hf : ∀ k, ContDiff ℝ 2 (f k))
    (hper : ∀ k s, Periodic (fun t ↦ f k (s, t)) 1) (hfK : ∀ k z, f k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (f k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (f k)) {g : ℝ × ℝ → V} (hg : TendstoLocallyUniformly f g atTop)
    (hst : ∀ s t, g (s, t) = g (0, t)) :
    Periodic (fun t ↦ g (0, t)) 1 ∧
      (∀ t, HasDerivAt (fun t ↦ g (0, t)) (ω.hamiltonianVectorField (H t) (g (0, t))) t) ∧
        ∀ t, g (0, t) ∈ K := by
  -- The energy over every window tends to zero, so `g` is the stationary cylinder over an orbit.
  obtain ⟨x, hxper, hxd, hxK, rfl⟩ :=
    exists_periodic_hasDerivAt_of_tendsto_setLIntegral_comp_add (s := fun _ ↦ 0) (v := g) hH
      hHper hK isOpen_univ (fun k ↦ ((hf k).of_le one_le_two).contDiffOn) (fun k r _ ↦ hper k r)
      (fun k r _ t ↦ hfK k (r, t)) hc hJc hJM hfloer
      (fun _ _ ↦ Eventually.of_forall fun _ ↦ subset_univ _)
      (fun α β ↦ by
        simpa using tendsto_setLIntegral_floerEnergyDensity_of_forall_eq hH hf hper hc hJc hfloer
          hL hg hst α β) (by simpa [Prod.mk_zero_zero] using hg)
  exact ⟨hxper, hxd, hxK⟩

/-- **A limit of Floer trajectories normalized at a regular action value is not stationary.**
Let `H` be a `C¹` Hamiltonian, `1`-periodic in time, and `K` a closed set. Let `f k` be `C²`
solutions of the Floer equation `∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with
`1`-periodic loops in `K`, uniformly tame almost complex structures, `c ‖v‖² ≤ ω(v, J_k z v)` and
`‖J_k z v‖ ≤ M ‖v‖` with `c > 0`, and a common Lipschitz constant `L`. Suppose that the actions of
the loops `f k (0, ·)` tend to a value `a` which is not the action of any `1`-periodic orbit of
the Hamiltonian vector field with values in `K`. If the `f k` converge locally uniformly to `g`,
then `g` is not stationary: `g(s, t) ≠ g(0, t)` for some `s` and `t`. -/
theorem exists_apply_ne_apply_zero_of_tendstoLocallyUniformly
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsClosed K)
    {f : ℕ → ℝ × ℝ → V} (hf : ∀ k, ContDiff ℝ 2 (f k))
    (hper : ∀ k s, Periodic (fun t ↦ f k (s, t)) 1) (hfK : ∀ k z, f k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (f k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (f k)) {a : ℝ}
    (ha : a ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    (hfa : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ f k (0, t))) atTop (𝓝 a))
    {g : ℝ × ℝ → V} (hg : TendstoLocallyUniformly f g atTop) :
    ∃ s t, g (s, t) ≠ g (0, t) := by
  by_contra! hst
  obtain ⟨hxper, hxd, hxK⟩ := periodic_hasDerivAt_of_forall_eq hH hHper hK hf hper hfK hc hJc hJM
    hfloer hL hg hst
  set x : ℝ → V := fun t ↦ g (0, t)
  -- The loops `f k (0, ·)` converge to the orbit `x`, so their actions are asymptotically equal.
  have hgx : g = fun z ↦ x z.2 := funext fun z ↦ hst z.1 z.2
  have hlim := tendsto_hamiltonianAction_sub_hamiltonianAction_of_tendstoLocallyUniformly hH
    (fun k ↦ (hf k).of_le one_le_two) hper hL hxper hxd (hgx ▸ hg)
  -- Hence the action of the orbit `x` is `a`, which is not the action of an orbit in `K`.
  have hxa : ω.hamiltonianAction H x = a := by
    have h := tendsto_nhds_unique (hfa.sub_const (ω.hamiltonianAction H x)) hlim
    linarith
  exact ha ⟨x, ⟨hxper, hxd, hxK⟩, hxa⟩

/-- **A limit of translates normalized at a regular action value is not stationary.** Under the
hypotheses of `TauCeti.SymplecticForm.exists_apply_ne_apply_zero_of_tendstoLocallyUniformly`, let
`σ k` be shifts such that the actions of the loops `u k (σ k, ·)` tend to a value `a` which is not
the action of any `1`-periodic orbit with values in `K`. If the translates
`(s, t) ↦ u k (s + σ k, t)` converge locally uniformly to `g`, then `g` is not stationary:
`g(s, t) ≠ g(0, t)` for some `s` and `t`. -/
theorem exists_apply_ne_apply_zero_of_tendstoLocallyUniformly_comp_add
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsClosed K)
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {a : ℝ}
    (ha : a ∉ ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})
    {σ : ℕ → ℝ}
    (hσa : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ k, t))) atTop (𝓝 a))
    {g : ℝ × ℝ → V} (hg : TendstoLocallyUniformly (fun k z ↦ u k (z + (σ k, 0))) g atTop) :
    ∃ s t, g (s, t) ≠ g (0, t) := by
  -- The translates are Floer trajectories for the translated almost complex structures.
  have hzσ (z : ℝ × ℝ) (r : ℝ) : z + (r, 0) = (z.1 + r, z.2) := by ext <;> simp
  have hmem {z : ℝ × ℝ} (r : ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
      z + (r, 0) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 := ⟨mem_univ _, by simpa [hzσ] using hz.2⟩
  refine exists_apply_ne_apply_zero_of_tendstoLocallyUniformly
    (J := fun k z ↦ J k (z + (σ k, 0))) (L := L) hH hHper hK
    (f := fun k z ↦ u k (z + (σ k, 0))) (fun k ↦ (hu k).comp (contDiff_id.add contDiff_const))
    (fun k s t ↦ by simpa [hzσ] using hper k (s + σ k) t)
    (fun k z ↦ huK _ _) hc (fun k z hz ↦ hJc _ _ (hmem _ hz)) (fun k z hz ↦ hJM _ _ (hmem _ hz))
    (fun k z hz ↦ ?_) (fun k ↦ ?_) ha (by simpa using hσa) hg
  · have h := ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) (σ k, 0) z
    simp only [hzσ] at h
    simpa [hzσ, h] using hfloer k _ (hmem (σ k) hz)
  · exact ((hL k).comp (IsometryEquiv.addRight ((σ k, 0) : ℝ × ℝ)).isometry.lipschitzWith).weaken
      (mul_one L).le

/-- **A sequence of nonstationary Floer trajectories has a nonstationary level.** Let `H` be a
`C¹` Hamiltonian, `1`-periodic in time, and `K` a compact set such that the `1`-periodic orbits of
the Hamiltonian vector field with values in `K` have only finitely many actions, for instance
because they are all nondegenerate. Let `u k` be `C²` solutions of the Floer equation
`∂_s u + J_k (∂_t u - X_{H_t}(u)) = 0` on `ℝ × [0, 1]`, with `1`-periodic loops in `K`, uniformly
tame almost complex structures, `c ‖v‖² ≤ ω(v, J_k z v)` and `‖J_k z v‖ ≤ M ‖v‖` with `c > 0`, and
a common Lipschitz constant `L`. If no `u k` is stationary, then there are a subsequence
`u (φ n)` and shifts `σ n` such that the translates `(s, t) ↦ u (φ n) (s + σ n, t)` converge
locally uniformly to a map `g` which is not stationary: `g(s, t) ≠ g(0, t)` for some `s` and
`t`. -/
theorem exists_subseq_tendstoLocallyUniformly_comp_add_of_floer
    (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1) (hK : IsCompact K)
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
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ σ : ℕ → ℝ, ∃ g : ℝ × ℝ → V,
      TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (σ n, 0))) g atTop ∧
        ∃ s t, g (s, t) ≠ g (0, t) := by
  -- Each trajectory runs from an orbit of action `a₀ k` to an orbit of larger action `a₁ k`.
  choose a₀ ha₀ a₁ ha₁ hlt hbot htop using fun k ↦ exists_lt_tendsto_hamiltonianAction_of_floer hH
    hHper hK hfin (hu k) (hper k) (huK k) hc (hJc k) (hJM k) (hfloer k) (hL k) (hns k)
  -- Between the two end actions there is a regular action value `m (a₀ k, a₁ k)`. These values
  -- range over a finite set, so along a subsequence they converge to a regular action value.
  have hreg (p : ℝ × ℝ) (hp : p.1 < p.2) : ∃ b ∈ Ioo p.1 p.2, b ∉ ω.hamiltonianAction H '' _ :=
    (Ioo_infinite hp).exists_notMem_finite hfin
  choose! m hm hmC using hreg
  obtain ⟨_, ⟨p, ⟨-, hp⟩, rfl⟩, φ₁, hφ₁, hbb'⟩ :=
    (((hfin.prod hfin).subset (inter_subset_left (t := {p : ℝ × ℝ | p.1 < p.2}))).image
      m).isCompact.tendsto_subseq
      (x := fun k ↦ m (a₀ k, a₁ k)) fun k ↦ ⟨_, ⟨⟨ha₀ k, ha₁ k⟩, hlt k⟩, rfl⟩
  -- Normalize each trajectory so that its loop at `s = 0` has the action `m (a₀ k, a₁ k)`.
  have hσ (k : ℕ) : ∃ σ, ω.hamiltonianAction H (fun t ↦ u k (σ, t)) = m (a₀ k, a₁ k) :=
    mem_range_of_exists_le_of_exists_ge
      (ω.continuous_hamiltonianAction_slice hH.continuous ((hu k).of_le one_le_two))
      (((hbot k).eventually (gt_mem_nhds (hm (a₀ k, a₁ k) (hlt k)).1)).exists.imp fun _ h ↦ h.le)
      (((htop k).eventually (lt_mem_nhds (hm (a₀ k, a₁ k) (hlt k)).2)).exists.imp fun _ h ↦ h.le)
  choose σ hσ using hσ
  -- The translates are uniformly Lipschitz with values in `K`, so a subsequence converges.
  obtain ⟨φ₂, hφ₂, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith hK
    (u := fun n ↦ u (φ₁ n)) (fun _ ↦ hL _) (fun _ ↦ huK _) fun n ↦ σ (φ₁ n)
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun n ↦ σ (φ₁ (φ₂ n)), g, hg, ?_⟩
  -- The actions of the loops of the translates at `s = 0` tend to the regular action value `m p`.
  exact exists_apply_ne_apply_zero_of_tendstoLocallyUniformly_comp_add
    (u := fun n ↦ u (φ₁ (φ₂ n))) (J := fun n ↦ J (φ₁ (φ₂ n))) hH hHper hK.isClosed
    (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _) hc (fun _ ↦ hJc _) (fun _ ↦ hJM _)
    (fun _ ↦ hfloer _) (fun _ ↦ hL _) (hmC p hp)
    ((hbb'.comp hφ₂.tendsto_atTop).congr fun n ↦ by simp [hσ]) hg

/-- If a monotone function `A` runs from at least `a` at `s₀` to at most `b` at `s₁`, with
`s₁ - s₀ > 2 (n + 1)²`, then there is a centre `σ` with `A σ ∈ [a, b]` around which `A` increases
by at most `(b - a) / (n + 1)` over the window `[σ - (n + 1), σ + (n + 1)]`. -/
private theorem exists_mem_Icc_sub_le_div {A : ℝ → ℝ} (hA : Monotone A) {s₀ s₁ a b : ℝ} (n : ℕ)
    (hlt : 2 * ((n : ℝ) + 1) ^ 2 < s₁ - s₀) (ha : a ≤ A s₀) (hb : A s₁ ≤ b) :
    ∃ σ, A σ ∈ Icc a b ∧ A (σ + (n + 1)) - A (σ - (n + 1)) ≤ (b - a) / (n + 1) := by
  -- Cut `[s₀, s₀ + 2 (n + 1)²]` into `n + 1` windows of length `2 (n + 1)`, and take the centre
  -- of one whose increment is at most the average.
  obtain ⟨j, hj, hjle⟩ := exists_sub_le_div (fun j : ℕ ↦ A (s₀ + j * (2 * ((n : ℝ) + 1))))
    n.succ_ne_zero
  push_cast [zero_mul, add_zero] at hjle
  have hj' : (j : ℝ) + 1 ≤ n + 1 := by exact_mod_cast hj
  have hend : s₀ + ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) ≤ s₁ := by nlinarith
  have hleft : s₀ ≤ s₀ + j * (2 * ((n : ℝ) + 1)) := by
    nlinarith [j.cast_nonneg (α := ℝ)]
  have hright : s₀ + (j + 1) * (2 * ((n : ℝ) + 1)) ≤ s₁ := by
    nlinarith [mul_le_mul_of_nonneg_right hj' (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))]
  refine ⟨s₀ + j * (2 * ((n : ℝ) + 1)) + (n + 1), ⟨(ha.trans (hA ?_)), (hA ?_).trans hb⟩, ?_⟩
  · linarith
  · nlinarith
  · have he : s₀ + j * (2 * ((n : ℝ) + 1)) + (n + 1) + (n + 1) =
        s₀ + (j + 1) * (2 * ((n : ℝ) + 1)) := by ring
    rw [he, add_sub_cancel_right]
    refine hjle.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    linarith [hA hend]

/-- **Translates centred in windows of vanishing energy have stationary limits.** Let `u k` be
`C²` Floer trajectories with `1`-periodic loops and uniformly tame almost complex structures, and
let `σ k` and `r k → ∞` be such that the action of `u k` increases by an amount tending to zero
over `[σ k - r k, σ k + r k]`. If the translates `(s, t) ↦ u k (s + σ k, t)` converge locally
uniformly to `g`, then `g` does not depend on `s`. -/
private theorem forall_apply_eq_apply_zero_of_tendsto_sub (hH : ContDiff ℝ 1 (uncurry H))
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    {σ r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hA : Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u k (σ k + r k, t)) -
      ω.hamiltonianAction H (fun t ↦ u k (σ k - r k, t))) atTop (𝓝 0))
    {g : ℝ × ℝ → V} (hg : TendstoLocallyUniformly (fun k z ↦ u k (z + (σ k, 0))) g atTop) :
    ∀ s t, g (s, t) = g (0, t) := by
  -- The energy over every translated window `[α + σ k, β + σ k]` tends to zero, since the window
  -- eventually lies in `[σ k - r k, σ k + r k]`.
  have hen (α β : ℝ) : Tendsto (fun k ↦ ∫⁻ z in Icc (α + σ k) (β + σ k) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (ENNReal.ofReal_zero ▸ ENNReal.tendsto_ofReal hA) (Eventually.of_forall fun _ ↦ bot_le) ?_
    filter_upwards [hr.eventually_ge_atTop (|α| + |β|)] with k hk
    have hsub : Icc (α + σ k) (β + σ k) ×ˢ Icc (0 : ℝ) 1 ⊆
        Icc (σ k - r k) (σ k + r k) ×ˢ Icc 0 1 :=
      prod_mono (Icc_subset_Icc (by linarith [neg_abs_le α, abs_nonneg β])
        (by linarith [le_abs_self β, abs_nonneg α])) le_rfl
    refine (lintegral_mono_set hsub).trans_eq ?_
    rw [setLIntegral_ofReal_floerEnergyDensity hH (hu k) hc (hJc k) (hfloer k),
      ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH isOpen_univ (hu k).contDiffOn
        (by linarith [abs_nonneg α, abs_nonneg β]) (subset_univ _)
        fun s _ ↦ by simpa using hper k s 0]
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add isOpen_univ
    (fun k ↦ (hu k).contDiffOn.of_le one_le_two) (subset_univ _) hc hJc hJM hfloer
    (fun _ _ ↦ Eventually.of_forall fun _ ↦ prod_mono (subset_univ _) le_rfl) hen
    (hg.tendstoLocallyUniformlyOn (s := univ ×ˢ Icc 0 1))
  -- The limit is `1`-periodic in `t`, so it does not depend on `s` on the whole plane.
  have hgper (s : ℝ) : Periodic (fun t ↦ g (s, t)) 1 := fun t ↦ by
    have hzσ (z : ℝ × ℝ) (r : ℝ) : z + (r, 0) = (z.1 + r, z.2) := by ext <;> simp
    exact tendsto_nhds_unique ((hg.tendsto_at (s, t + 1)).congr fun k ↦ by
      simpa [hzσ] using hper k (s + σ k) t) (hg.tendsto_at (s, t))
  intro s t
  have hfract (s : ℝ) : g (s, t) = g (s, Int.fract t) := by
    rw [Int.fract, ← (hgper s).sub_int_mul_eq ⌊t⌋, mul_one]
  rw [hfract s, hfract 0]
  exact hstat s _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- **Floer trajectories spend a bounded time in a regular action window.** Let `H` be a `C¹`
Hamiltonian, `1`-periodic in time, `K` a compact set, and `[a, b]` an interval containing no
action of a `1`-periodic orbit of the Hamiltonian vector field with values in `K`. Fix tameness
constants `0 < c` and `M` and a Lipschitz constant `L`. Then there is a time `T` such that every
`L`-Lipschitz `C²` solution `u` of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` with
`1`-periodic loops in `K` and almost complex structures satisfying `c ‖v‖² ≤ ω(v, J z v)` and
`‖J z v‖ ≤ M ‖v‖` satisfies `s₁ - s₀ ≤ T` whenever `a ≤ A_H(u(s₀, ·))` and `A_H(u(s₁, ·)) ≤ b`.
Since the action increases along `u`, this says that the loops of `u` with actions in `[a, b]`
form an interval of `s`-values of length at most `T`, uniformly in `u`. -/
theorem exists_forall_sub_le_of_floer (hH : ContDiff ℝ 1 (uncurry H)) (hHper : Periodic H 1)
    (hK : IsCompact K) (hc : 0 < c) {a b : ℝ}
    (hreg : Disjoint (Icc a b) (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K})) :
    ∃ T : ℝ, ∀ (u : ℝ × ℝ → V) (J' : ℝ × ℝ → AlmostComplexStructure V), ContDiff ℝ 2 u →
      (∀ s, Periodic (fun t ↦ u (s, t)) 1) → (∀ z, u z ∈ K) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J' z v)) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J' z v‖ ≤ M * ‖v‖) →
      (∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' z)
          (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      LipschitzWith L u → ∀ s₀ s₁, a ≤ ω.hamiltonianAction H (fun t ↦ u (s₀, t)) →
        ω.hamiltonianAction H (fun t ↦ u (s₁, t)) ≤ b → s₁ - s₀ ≤ T := by
  by_contra! h
  choose u J' hu hper huK hJc hJM hfloer hL s₀ s₁ ha hb hlt using
    fun n : ℕ ↦ h (2 * ((n : ℝ) + 1) ^ 2)
  set A : ℕ → ℝ → ℝ := fun n s ↦ ω.hamiltonianAction H (fun t ↦ u n (s, t))
  have hmono (n : ℕ) : Monotone (A n) := ω.monotone_hamiltonianAction_of_floer hH (hu n)
    (hper n) (fun z hz ↦ tames_of_mul_norm_sq_le hc (hJc n z hz)) (hfloer n)
  -- Each trajectory has a window of length `2 (n + 1)`, centred at a loop with action in
  -- `[a, b]`, over which its action increases by at most `(b - a) / (n + 1)`.
  choose σ hAσ hwin using fun n ↦ exists_mem_Icc_sub_le_div (hmono n) n (hlt n) (ha n) (hb n)
  -- Along a subsequence the actions at the centres converge to some `a' ∈ [a, b]`, and the
  -- translates centred at `σ n` converge locally uniformly.
  obtain ⟨a', ha', φ₁, hφ₁, hA'⟩ := isCompact_Icc.tendsto_subseq (x := fun n ↦ A n (σ n)) hAσ
  obtain ⟨φ₂, hφ₂, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith hK
    (u := fun n ↦ u (φ₁ n)) (fun _ ↦ hL _) (fun _ ↦ huK _) fun n ↦ σ (φ₁ n)
  set ψ : ℕ → ℕ := φ₁ ∘ φ₂
  have hψ : StrictMono ψ := hφ₁.comp hφ₂
  -- The limit is not stationary, since `a'` is a regular action value.
  obtain ⟨s, t, hst⟩ := exists_apply_ne_apply_zero_of_tendstoLocallyUniformly_comp_add
    (u := fun n ↦ u (ψ n)) (J := fun n ↦ J' (ψ n)) (σ := fun n ↦ σ (ψ n)) hH hHper hK.isClosed
    (fun _ ↦ hu _) (fun _ ↦ hper _) (fun _ ↦ huK _) hc (fun _ ↦ hJc _) (fun _ ↦ hJM _)
    (fun _ ↦ hfloer _) (fun _ ↦ hL _) (Set.disjoint_left.1 hreg ha')
    (hA'.comp hφ₂.tendsto_atTop) hg
  -- The limit is stationary, since the action increments over the windows tend to zero.
  refine hst (forall_apply_eq_apply_zero_of_tendsto_sub (u := fun n ↦ u (ψ n))
    (J := fun n ↦ J' (ψ n)) (σ := fun n ↦ σ (ψ n)) (r := fun n ↦ (ψ n : ℝ) + 1) hH
    (fun n ↦ hu _) (fun n ↦ hper _) hc (fun n ↦ hJc _) (fun n ↦ hJM _) (fun n ↦ hfloer _)
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop)) ?_ hg
    s t)
  have hdiv : Tendsto (fun n ↦ (b - a) / ((ψ n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)).comp hψ.tendsto_atTop
    rw [mul_zero] at h
    exact h.congr fun n ↦ (div_eq_mul_one_div _ _).symm
  refine squeeze_zero (fun n ↦ sub_nonneg.2 (hmono _ (by linarith))) (fun n ↦ hwin (ψ n)) hdiv

/-- **Levels at regular action values of a common regular interval are translates of each other.**
Under the hypotheses of `TauCeti.SymplecticForm.exists_forall_sub_le_of_floer`, let `u k` be Floer
trajectories, and let `σ k` and `σ' k` be shifts at which the loops of `u k` have actions in an
interval `[a, b]` containing no action of a `1`-periodic orbit in `K`. If the translates
`(s, t) ↦ u k (s + σ k, t)` converge locally uniformly to `g` and the translates
`(s, t) ↦ u k (s + σ' k, t)` to `g'`, then `g'` is a translate of `g` in `s`. -/
theorem exists_eq_comp_add_of_tendstoLocallyUniformly (hH : ContDiff ℝ 1 (uncurry H))
    (hHper : Periodic H 1) (hK : IsCompact K) {a b : ℝ}
    (hreg : Disjoint (Icc a b) (ω.hamiltonianAction H '' {x : ℝ → V | Periodic x 1 ∧
      (∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) ∧ ∀ t, x t ∈ K}))
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hper : ∀ k s, Periodic (fun t ↦ u k (s, t)) 1) (huK : ∀ k z, u k z ∈ K) (hc : 0 < c)
    (hJc : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J k z v))
    (hJM : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ∀ v, ‖J k z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ k, ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ k, LipschitzWith L (u k)) {σ σ' : ℕ → ℝ}
    (hσ : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ k, t)) ∈ Icc a b)
    (hσ' : ∀ k, ω.hamiltonianAction H (fun t ↦ u k (σ' k, t)) ∈ Icc a b) {g g' : ℝ × ℝ → V}
    (hg : TendstoLocallyUniformly (fun k z ↦ u k (z + (σ k, 0))) g atTop)
    (hg' : TendstoLocallyUniformly (fun k z ↦ u k (z + (σ' k, 0))) g' atTop) :
    ∃ δ : ℝ, ∀ z, g' z = g (z + (δ, 0)) := by
  -- The two normalizations stay a bounded distance apart.
  obtain ⟨T, hT⟩ := exists_forall_sub_le_of_floer (M := M) (L := L) hH hHper hK hc hreg
  have hd (k : ℕ) : σ' k - σ k ∈ Icc (-T) T := by
    have h := hT (u k) (J k) (hu k) (hper k) (huK k) (hJc k) (hJM k) (hfloer k) (hL k)
    exact ⟨by linarith [h _ _ (hσ' k).1 (hσ k).2], h _ _ (hσ k).1 (hσ' k).2⟩
  obtain ⟨δ, -, φ, hφ, hδ⟩ := isCompact_Icc.tendsto_subseq hd
  -- Along the subsequence, the shifts `σ' k - σ k` converge to `δ`.
  exact ⟨δ, apply_eq_apply_add_prodMk_zero_of_tendsto_sub (u := fun k ↦ u (φ k))
    (fun k ↦ hL (φ k)) (σ := fun k ↦ σ (φ k)) (σ' := fun k ↦ σ' (φ k)) hδ
    (hg.comp_tendsto hφ.tendsto_atTop).tendsto_at (hg'.comp_tendsto hφ.tendsto_atTop).tendsto_at⟩

end TauCeti.SymplecticForm
