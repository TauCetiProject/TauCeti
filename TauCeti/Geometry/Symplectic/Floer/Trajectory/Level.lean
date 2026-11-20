/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Trajectory
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Symplectic.Floer.Breaking
import TauCeti.Topology.ContinuousMap.Ascoli
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
namespace `TauCeti.SymplecticForm`). This file finds nonstationary levels.

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
  (`TauCeti.SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`), and the
  actions of the loops `u_k(0, ·)` would tend to the action of `x`
  (`TauCeti.SymplecticForm.tendsto_hamiltonianAction_sub_hamiltonianAction`), which is not `a`.
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
  Arzelà–Ascoli theorem (`TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith`)
  gives a convergent subsequence of the translates. No energy bound is assumed: the actions of
  loops in `K` of bounded speed are bounded
  (`TauCeti.SymplecticForm.exists_forall_abs_hamiltonianAction_le`), so each trajectory has finite
  energy and its ends have actions `a₀ < a₁`
  (`TauCeti.SymplecticForm.exists_lt_tendsto_hamiltonianAction_of_floer`).

The uniform bound on the derivatives excludes bubbling; it is assumed, not proved. The limit `g`
is only shown to be continuous here; its regularity is not treated. For smooth solutions with
bounded derivatives, read in the complex coordinate `z = s + i t`, it is the subject of
`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_floer`.

## Main results

* `SymplecticForm.exists_apply_ne_apply_zero_of_tendstoLocallyUniformly`: a limit of Floer
  trajectories normalized at a regular action value is not stationary.
* `SymplecticForm.exists_subseq_tendstoLocallyUniformly_comp_add_of_floer`: a sequence of
  nonstationary Floer trajectories with bounded derivatives has translates converging to a
  nonstationary limit.

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
  refine (ENNReal.tendsto_ofReal hE).congr fun k ↦ ?_
  -- The energy density is continuous and nonnegative.
  have hsub : Icc α β ×ˢ Icc (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) le_rfl
  exact ofReal_integral_eq_lintegral_ofReal
    ((ω.continuousOn_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) isOpen_univ
      ((hf k).of_le one_le_two).contDiffOn contDiffOn_const
      (contDiff_uncurry_cylindrical hH).contDiffOn).mono (subset_univ _) |>.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc))
    (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      ω.floerEnergyDensity_nonneg (fun v hv ↦
        (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc k z (hsub hz) v))
        (hfloer k z (hsub hz)))

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
  -- On `[0, 1]`, `x(t) = g(0, t)` solves Hamilton's equation, since the energy over every window
  -- tends to zero.
  have hv : TendstoLocallyUniformlyOn (fun k z ↦ f k (z + ((fun _ ↦ (0 : ℝ)) k, 0))) g atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1) := by
    simpa [Prod.mk_zero_zero] using hg.tendstoLocallyUniformlyOn (s := univ ×ˢ Icc 0 1)
  have hder := hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add (s := fun _ ↦ 0) hH
    isOpen_univ (fun k ↦ ((hf k).of_le one_le_two).contDiffOn) (subset_univ _) hc hJc hJM hfloer
    (fun _ _ ↦ Eventually.of_forall fun _ ↦ prod_mono (subset_univ _) le_rfl)
    (fun α β ↦ by
      simpa using tendsto_setLIntegral_floerEnergyDensity_of_forall_eq hH hf hper hc hJc hfloer hL
        hg hst α β) hv
  set x : ℝ → V := fun t ↦ g (0, t)
  have hat (z : ℝ × ℝ) : Tendsto (fun k ↦ f k z) atTop (𝓝 (g z)) :=
    (hg.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ z)
  have hxper : Periodic x 1 := fun t ↦ tendsto_nhds_unique
    ((hat (0, t + 1)).congr fun k ↦ hper k 0 t) (hat (0, t))
  -- By periodicity, `x` solves Hamilton's equation everywhere.
  set Y : ℝ → V := fun t ↦ ω.hamiltonianVectorField (H t) (x t)
  have hYper : Periodic Y 1 := fun t ↦ by simp only [Y, hHper t, hxper t]
  exact ⟨hxper, hasDerivAt_of_periodic_of_hasDerivWithinAt one_pos hxper hYper hder,
    fun t ↦ hK.mem_of_tendsto (hat (0, t)) (Eventually.of_forall fun k ↦ hfK k _)⟩

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
  -- The loops `f k (0, ·)` and the orbit `x` have bounded speed, so their actions are
  -- asymptotically equal.
  have hdf (k : ℕ) (z : ℝ × ℝ) : DifferentiableAt ℝ (f k) z :=
    (hf k).differentiable two_ne_zero z
  have hderiv : deriv x = fun t ↦ ω.hamiltonianVectorField (H t) (x t) :=
    funext fun t ↦ (hxd t).deriv
  have hY : Continuous (deriv x) := hderiv ▸
    (ω.continuous_uncurry_hamiltonianVectorField hH).comp
      (continuous_id.prodMk (continuous_iff_continuousAt.2 fun t ↦ (hxd t).continuousAt))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hY.continuousOn
  have hlim := ω.tendsto_hamiltonianAction_sub_hamiltonianAction (H := H) hH.continuous
    (y := fun _ ↦ x) (L := max L B)
    (Eventually.of_forall fun k t _ ↦ (hasDerivAt_slice_right (hdf k (0, t))).differentiableAt)
    (Eventually.of_forall fun _ t _ ↦ (hxd t).differentiableAt)
    (Eventually.of_forall fun k ↦
      ((hf k).of_le one_le_two).contDiffOn.continuousOn_deriv_slice_right isOpen_univ
        fun _ _ ↦ mem_univ _)
    (Eventually.of_forall fun _ ↦ hY.continuousOn)
    (Eventually.of_forall fun k ↦ by simpa using hper k 0 0)
    (Eventually.of_forall fun _ ↦ by simpa using hxper 0)
    (Eventually.of_forall fun k t _ ↦ (norm_deriv_slice_right_le (hdf k (0, t))).trans
      ((norm_fderiv_le_of_lipschitz ℝ (hL k)).trans (le_max_left _ _)))
    (Eventually.of_forall fun _ t ht ↦ (hB t ht).trans (le_max_right _ _))
    ((hg.tendstoLocallyUniformlyOn (s := univ)).tendstoUniformlyOn_slice_right isCompact_Icc
      fun _ _ ↦ mem_univ _)
    fun _ hu ↦ Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hu
  -- Hence the action of the orbit `x` is `a`, which is not the action of an orbit in `K`.
  have hxa : ω.hamiltonianAction H x = a := by
    have h := tendsto_nhds_unique (hfa.sub_const (ω.hamiltonianAction H x)) hlim
    linarith
  exact ha ⟨x, ⟨hxper, hxd, hxK⟩, hxa⟩

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
  set w : ℕ → ℝ × ℝ → V := fun n z ↦ u (φ₁ n) (z + (σ (φ₁ n), 0))
  have hwL (n : ℕ) : LipschitzWith L (w n) := by
    have h := (hL (φ₁ n)).comp
      (IsometryEquiv.addRight ((σ (φ₁ n), 0) : ℝ × ℝ)).isometry.lipschitzWith
    rw [mul_one] at h
    exact h
  obtain ⟨φ₂, hφ₂, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith hK
    (R := fun n ↦ (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n ↦ (hwL n).lipschitzOnWith) fun n z _ ↦ huK _ _
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun n ↦ σ (φ₁ (φ₂ n)), g, hg, ?_⟩
  -- The translates are Floer trajectories, and the actions of their loops at `s = 0` tend to the
  -- regular action value `m p`.
  have hzσ (z : ℝ × ℝ) (r : ℝ) : z + (r, 0) = (z.1 + r, z.2) := by ext <;> simp
  have hmem {z : ℝ × ℝ} (r : ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
      z + (r, 0) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 := ⟨mem_univ _, by simpa [hzσ] using hz.2⟩
  refine exists_apply_ne_apply_zero_of_tendstoLocallyUniformly
    (J := fun n z ↦ J (φ₁ (φ₂ n)) (z + (σ (φ₁ (φ₂ n)), 0))) hH hHper hK.isClosed
    (f := fun n ↦ w (φ₂ n)) (fun n ↦ (hu _).comp (contDiff_id.add contDiff_const))
    (fun n s t ↦ by simpa [w, hzσ] using hper (φ₁ (φ₂ n)) (s + σ (φ₁ (φ₂ n))) t)
    (fun n z ↦ huK _ _) hc (fun n z hz ↦ hJc _ _ (hmem _ hz)) (fun n z hz ↦ hJM _ _ (hmem _ hz))
    (fun n z hz ↦ ?_) (fun n ↦ hwL (φ₂ n)) (hmC p hp) ?_ hg
  · have h := ω.perturbedFDeriv_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) (u (φ₁ (φ₂ n)))
      (σ (φ₁ (φ₂ n)), 0) z
    simp only [hzσ] at h
    simpa [w, hzσ, h] using hfloer _ _ (hmem (σ (φ₁ (φ₂ n))) hz)
  · refine (hbb'.comp hφ₂.tendsto_atTop).congr fun n ↦ ?_
    simp [w, hσ]

end TauCeti.SymplecticForm
