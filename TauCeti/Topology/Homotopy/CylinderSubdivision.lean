/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.UniformSpace.DiagonalRadius
public import TauCeti.Topology.Order.Interval.Subdivision

/-!
# Locally terminating subdivisions of a cylinder

Given an open neighbourhood `W` of all triples `(x, t, t)` in `X × I × I`, choose a positive
continuous step size `δ` and continuous times `t_n(x,t) = min(t, n δ(x) / 2)`. Every successive
pair of times lies in `W`. Near each base point, one finite number of steps suffices for
**every** endpoint `t` and all nearby base points, even when `X` is noncompact.

For a family of local bundle transports invertible on `W` and equal to the identity on the
diagonal, these times make all later transport factors identities locally. They provide the
subdivision needed to compose local transports without assuming a globally positive step
size. This file does not construct the local bundle transports or their composition.

The construction uses Mathlib's `Set.Icc.addNSMul`, with its endpoint clipping, followed by
minimum with the desired endpoint. Continuous radii come from the parameterized diagonal
neighbourhood theorem in `TauCeti.Topology.UniformSpace.DiagonalRadius`.
-/

public section

open Filter Set Topology unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]

/-- A diagonal neighbourhood admits continuous cylinder subdivisions with the prescribed
clipped-time formula. Successive times stay in the neighbourhood, and the sequence is
stationary at the desired endpoint locally uniformly in both the base and the endpoint. -/
theorem exists_continuous_cylinder_subdivision {W : Set (X × I × I)} (hW : IsOpen W)
    (hdiag : ∀ (x : X) (t : I), (x, t, t) ∈ W) :
    ∃ δ : C(X, ℝ), ∃ τ : ℕ → C(X × I, I),
      (∀ x, δ x ∈ Ioo 0 1) ∧
      (∀ n x t, (τ n (x, t) : ℝ) = min (t : ℝ) (n * δ x / 2)) ∧
      (∀ x t, τ 0 (x, t) = 0) ∧
      (∀ n x t, (x, τ n (x, t), τ (n + 1) (x, t)) ∈ W) ∧
      (∀ x, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, ∀ t : I, τ n (y, t) = t) := by
  obtain ⟨δ, hδ, hδW⟩ := hW.exists_continuous_pos_forall_dist_le hdiag
  let step (x : X) := δ x / 2
  have hstep (x : X) : 0 < step x := half_pos (hδ x).1
  have hcstep : Continuous step := δ.continuous.div_const 2
  let p (n : ℕ) (x : X) : I := Icc.addNSMul zero_le_one (step x) n
  have hcp (n : ℕ) : Continuous (p n) := (Icc.continuous_addNSMul zero_le_one n).comp hcstep
  let τ (n : ℕ) : C(X × I, I) :=
    ⟨fun z ↦ min z.2 (p n z.1), continuous_snd.min ((hcp n).comp continuous_fst)⟩
  have hformula (n : ℕ) (x : X) (t : I) :
      (τ n (x, t) : ℝ) = min (t : ℝ) (n * δ x / 2) := by
    have hn : 0 ≤ (n : ℝ) * step x := mul_nonneg n.cast_nonneg (hstep x).le
    -- Reduce the native endpoint clipping; the minimum with t already clips at 1.
    simp only [τ, p, ContinuousMap.coe_mk, (Set.mono_coe I).map_min, Icc.addNSMul, coe_projIcc,
      zero_add, nsmul_eq_mul, max_eq_right (le_min zero_le_one hn), ← min_assoc,
      min_eq_left t.2.2]
    congr 1
    dsimp [step]
    ring
  refine ⟨δ, τ, hδ, hformula, ?_, ?_, ?_⟩
  · intro x t
    apply Subtype.ext
    simpa [hformula] using min_eq_right t.2.1
  · intro n x t
    have hpn : p n x ≤ p (n + 1) x :=
      Icc.monotone_addNSMul zero_le_one (hstep x).le (Nat.le_succ n)
    have hgap : |(p (n + 1) x : ℝ) - p n x| ≤ step x :=
      Icc.abs_sub_addNSMul_le zero_le_one (hstep x).le n ⟨hpn, le_rfl⟩
    have hmin : |min (t : ℝ) (p n x) - min (t : ℝ) (p (n + 1) x)| ≤ step x := by
      calc
        _ ≤ max |(t : ℝ) - t| |(p n x : ℝ) - p (n + 1) x| :=
          abs_min_sub_min_le_max _ _ _ _
        _ ≤ step x := max_le (by simpa using (hstep x).le) (by
          simpa only [abs_sub_comm] using hgap)
    apply hδW
    -- Subtype distances are the ambient real distances.
    exact (show dist (τ n (x, t)) (τ (n + 1) (x, t)) ≤ step x from by
      simpa only [Subtype.dist_eq, Real.dist_eq, τ, ContinuousMap.coe_mk,
        (Set.mono_coe I).map_min] using hmin).trans (by dsimp [step]; linarith [(hδ x).1])
  · intro x
    obtain ⟨N, hN⟩ := Icc.eventually_addNSMul_eq_right zero_le_one hcstep.continuousAt
      (hstep x)
    refine ⟨N, ?_⟩
    filter_upwards [hN] with y hy n hn t
    have hp : p n y = 1 := Subtype.ext (hy n hn)
    exact (congrArg (min t) hp).trans (min_eq_left (unitInterval.le_one t))

end TauCeti
