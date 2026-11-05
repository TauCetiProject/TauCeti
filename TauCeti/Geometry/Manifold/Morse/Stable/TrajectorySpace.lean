/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.LevelCrossing
public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Spaces of unparametrized trajectories on a compact manifold

Let `f` be a smooth function on a compact boundaryless manifold `M`, `X` an adapted pseudo-gradient
for `f` and `a ≠ b` two critical points. The trajectories of `X` from `a` to `b` are the points of
`W^u(a) ∩ W^s(b)`, and time translation acts on them; the *unparametrized* trajectories are the
classes of the orbit relation `Flow.connectingOrbitSetoid`, with the quotient topology.

Since `f` strictly decreases along every such trajectory, the general results of
`TauCeti.Dynamics.Flow.LevelCrossing` apply:

* the time translation action on `W^u(a) ∩ W^s(b)` is proper
  (`TauCeti.IsAdaptedPseudoGradient.isProperMap_restrict_pair`);
* the space of unparametrized trajectories is homeomorphic to every level slice
  `W^u(a) ∩ W^s(b) ∩ {f = c}` with `f b < c < f a`, independently of `c`
  (`TauCeti.IsAdaptedPseudoGradient.exists_orbitQuotient_homeomorph_levelSlice`);
* under the Morse–Smale condition it is a smooth manifold of dimension `ind a - ind b - 1`, with
  charts transported from a level slice
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isManifold_orbitQuotient`);
* it has as many points as the middle-level slice counted by the mod-two Morse boundary, so the
  boundary coefficient is the number of unparametrized trajectories modulo two
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeff_eq_natCard`).

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of trajectories, represented on a level).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.2 (the translation quotient and its dimension).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b : M} {c : ℝ}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- Some level is met by every trajectory from `a` to `b`. -/
private theorem exists_forall_exists_flow_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) :
    ∃ c, ∀ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b, ∃ t, f (hX.flow t y) = c := by
  rcases (hX.flow.unstableSet a ∩ hX.flow.stableSet b).eq_empty_or_nonempty with hC | ⟨y, hy⟩
  · exact ⟨0, by simp [hC]⟩
  · have hc := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hab hy
    exact ⟨f y, fun z hz ↦
      (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hab hz hc.1 hc.2).exists⟩

/-- **Time translation on trajectories is a proper action.** For distinct points `a` and `b`, the
action map `(t, y) ↦ (φ_t y, y)` of the flow on `W^u(a) ∩ W^s(b)`, with its subspace topology, is
proper. -/
theorem isProperMap_restrict_pair (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hab : a ≠ b) :
    IsProperMap fun ty : ℝ × ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b) ↦
      ((hX.flow.restrict (hX.flow.isInvariant_unstableSet_inter_stableSet a b)) ty.1 ty.2,
        ty.2) := by
  obtain ⟨c, hex⟩ := hX.exists_forall_exists_flow_eq hf hab
  exact Flow.isProperMap_restrict_pair hf.continuous.continuousOn
    (fun _ hy ↦ hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hab hy) hex

/-- **Unparametrized trajectories are a level slice.** For distinct points `a` and `b`, the space of
unparametrized trajectories from `a` to `b` is homeomorphic to its level slice at any value `c`
strictly between `f b` and `f a`, by a homeomorphism sending a point of the slice to its orbit
class. -/
theorem exists_orbitQuotient_homeomorph_levelSlice (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hab : a ≠ b) (hc : f b < c ∧ c < f a) :
    ∃ e : Quotient (Flow.connectingOrbitSetoid hX.flow a b) ≃ₜ
        ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}),
      ∀ y, e.symm y = Quotient.mk _ ⟨y.1, y.2.1⟩ :=
  ⟨_, Flow.orbitQuotientHomeomorphLevelSlice_symm_apply hf.continuous.continuousOn
    (fun _ hy ↦ hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hab hy)
    fun _ hy ↦ (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hab hy hc.1
      hc.2).exists⟩

/-- **Counting unparametrized trajectories.** For distinct points `p` and `q`, the unparametrized
trajectories from `p` to `q` are as many as the points of the middle-level slice
`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice`. -/
theorem natCard_orbitQuotient_eq_ncard_morseTrajectorySlice
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p q : M} (hpq : p ≠ q) :
    Nat.card (Quotient (Flow.connectingOrbitSetoid hX.flow p q)) =
      (hX.morseTrajectorySlice p q).ncard := by
  have hslice : hX.morseTrajectorySlice p q =
      hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {x | f x = (f p + f q) / 2} := by
    ext
    simp [and_assoc]
  rw [hslice]
  by_cases hlt : f q < f p
  · obtain ⟨e, -⟩ := hX.exists_orbitQuotient_homeomorph_levelSlice hf hpq
      (c := (f p + f q) / 2) ⟨by linarith, by linarith⟩
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_coe_set_eq _)
  · -- Without a drop in value there are no trajectories at all.
    have hC : hX.flow.unstableSet p ∩ hX.flow.stableSet q = ∅ :=
      eq_empty_of_forall_notMem fun y hy ↦
        hlt ((hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq hy).1.trans
          (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq hy).2)
    have : IsEmpty ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet q) := by
      rw [hC]
      infer_instance
    rw [Nat.card_of_isEmpty, hC, empty_inter, ncard_empty]

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **The space of unparametrized trajectories is a manifold.** Under the Morse–Smale condition,
the unparametrized trajectories between distinct critical points `a` and `b`, if there are any,
form a smooth manifold of dimension `ind a - ind b - 1`. Its charts are those of a level slice,
transported along `TauCeti.IsAdaptedPseudoGradient.exists_orbitQuotient_homeomorph_levelSlice`.
-/
theorem exists_isManifold_orbitQuotient (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0)
    (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0) (hab : a ≠ b)
    (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b + 1 =
        manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L (Quotient (Flow.connectingOrbitSetoid hX.flow a b)),
        letI := C
        IsManifold 𝓘(ℝ, L) ∞ (Quotient (Flow.connectingOrbitSetoid hX.flow a b)) := by
  have hmd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨y, hy⟩ := hne
  have hc := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hmd hab hy
  obtain ⟨L, hL, C, hC, -⟩ := h.exists_unstableSet_inter_stableSet_level_isManifold hf ha hb hab
    ⟨y, hy, rfl⟩
  obtain ⟨e, -⟩ := hX.exists_orbitQuotient_homeomorph_levelSlice hmd hab hc
  let := C
  exact ⟨L, hL, e.pullbackChartedSpace, Homeomorph.pullback_isManifold _ _ e⟩

/-- **The Morse boundary counts unparametrized trajectories.** For critical points of consecutive
index, the coefficient of `q` in the mod-two Morse boundary of `p` is the number of unparametrized
trajectories from `p` to `q`, modulo two. -/
theorem morseBoundaryCoeff_eq_natCard {p q : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    h.morseBoundaryCoeff hf p q =
      (Nat.card (Quotient (Flow.connectingOrbitSetoid hX.flow p q)) : ZMod 2) := by
  have hpq : (p : M) ≠ q := fun hpq ↦ by simp [hpq] at hind
  rw [h.morseBoundaryCoeff_eq_ncard hf hind,
    hX.natCard_orbitQuotient_eq_ncard_morseTrajectorySlice
      (hf.contMDiff.mdifferentiable (by simp)) hpq]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
