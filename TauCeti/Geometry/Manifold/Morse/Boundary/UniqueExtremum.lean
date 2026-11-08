/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The mod-two Morse boundary at a unique maximum and a unique minimum

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n` and `X` a
pseudo-gradient field adapted to `f` satisfying the Morse–Smale condition. Let `q` be a critical
point of index `n - 1`. Its stable manifold `W^s(q)` is a line, so `W^s(q) - {q}` consists of
exactly two trajectories, one on each side of `q`. Each of them comes from a critical point of
index `n`, since the Morse index strictly drops along every trajectory. If `f` has a single
critical point `p` of index `n`, both trajectories come from `p`, so there are exactly two
trajectories from `p` to `q`, and the coefficient of `q` in the mod-two Morse boundary of `p` is
zero. Reversing the flow, if `f` has a single critical point `m` of index `0`, every critical point
of index `1` has exactly two trajectories to `m`.

On a surface every coefficient of the Morse boundary joins a critical point of index `2` to one of
index `1`, or a critical point of index `1` to one of index `0`. So the mod-two Morse boundary of a
Morse–Smale pair on a compact surface vanishes as soon as `f` has at most one critical point of
index `2` and at most one of index `0`. The standard Morse function on the torus is such a function
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_sphereHeight_comp_fst_add_comp_snd`),
with two trajectories from the maximum to each saddle and from each saddle to the minimum.
Classically, so are the standard Morse functions on the closed orientable surfaces of higher genus
and on the real projective plane; in each case the homology of the complex with zero differential
is the mod-two homology of the surface.

The two trajectories in `W^s(q) - {q}` are read off the parametrization `ι` of `W^s(q)` by its
one-dimensional tangent space `L` at `q` (`TauCeti.IsAdaptedPseudoGradient.exists_stableParam`),
which intertwines the scaling `v ↦ e^{-s} v` of `L` with the flow. The two half-lines of `L - {0}`
are the two trajectories, and each crosses an intermediate level exactly once
(`TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `ncard_unstableSet_inter_stableSet_inter_level_eq_two`: if the stable manifold of a critical
  point `q` of index `n - 1` lies, away from `q`, in the unstable manifold of `p`, then each
  intermediate level meets `W^u(p) ∩ W^s(q)` in exactly two points.
* `IsMorseSmale.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank` and
  `IsMorseSmale.ncard_morseTrajectorySlice_eq_two_of_unique_index_zero`: there are exactly two
  trajectories from the only critical point of index `n` to a critical point of index `n - 1`, and
  from a critical point of index `1` to the only critical point of index `0`.
* `IsMorseSmale.morseBoundary_single_eq_zero_of_unique_index_finrank` and
  `IsMorseSmale.morseBoundary_apply_eq_zero_of_unique_index_zero`: the mod-two Morse boundary
  vanishes on the only critical point of index `n`, and the only critical point of index `0` has
  coefficient zero in every boundary.
* `IsMorseSmale.morseBoundary_eq_zero_of_finrank_eq_two`: on a surface, the mod-two Morse boundary
  vanishes when `f` has at most one critical point of index `2` and at most one of index `0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus and the real projective plane).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **Two trajectories into a critical point of index `n - 1`.** Let `q` be a critical point of
index `n - 1`, so that `W^s(q)` is a line, and suppose that every point of `W^s(q)` other than `q`
lies in the unstable manifold of `p`. Then each level `c` with `f q < c < f p` meets
`W^u(p) ∩ W^s(q)` in exactly two points, one on each of the two trajectories making up
`W^s(q) - {q}`. -/
theorem ncard_unstableSet_inter_stableSet_inter_level_eq_two
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p q : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (hW : ∀ y ∈ hX.flow.stableSet q, y ≠ q → y ∈ hX.flow.unstableSet p) {c : ℝ}
    (hqc : f q < c) (hcp : c < f p) :
    (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}).ncard = 2 := by
  obtain ⟨φ, δ, hemb, hrange, h0, -, hsmul⟩ := hX.exists_stableParam hf hq
  set ι := hX.stableParam φ δ
  have hinj : Function.Injective ι := hemb.isEmbedding.injective
  have hL : Module.finrank ℝ φ.stableSubspace = 1 := by
    have := φ.finrank_stableSubspace_add_manifoldMorseIndex
    omega
  obtain ⟨u, hu⟩ : ∃ u : φ.stableSubspace, u ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := φ.stableSubspace)).1 (by omega)
  have hpq : p ≠ q := by
    rintro rfl
    exact (hqc.trans hcp).false
  have hmem (v : φ.stableSubspace) (hv : v ≠ 0) :
      ι v ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨hW _ (hrange ▸ mem_range_self v) fun h ↦ hv (hinj (h.trans h0.symm)),
      hrange ▸ mem_range_self v⟩
  -- The half-line through a nonzero `v` is one trajectory, and it crosses the level `c` once.
  have key (v : φ.stableSubspace) (hv : v ≠ 0) : ∃ s : ℝ, f (ι (Real.exp (-s) • v)) = c ∧
      ∀ a : ℝ, 0 < a → f (ι (a • v)) = c → a • v = Real.exp (-s) • v := by
    obtain ⟨s, hs, huniq⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hpq (hmem v hv) hqc hcp
    refine ⟨s, by rwa [hsmul], fun a ha hfa ↦ ?_⟩
    have hfa' : f (hX.flow (-Real.log a) (ι v)) = c := by
      rwa [← hsmul, neg_neg, Real.exp_log ha]
    rw [← huniq _ hfa', neg_neg, Real.exp_log ha]
  obtain ⟨s₁, hs₁, hu₁⟩ := key u hu
  obtain ⟨s₂, hs₂, hu₂⟩ := key (-u) (neg_ne_zero.2 hu)
  have hne (s : ℝ) {v : φ.stableSubspace} (hv : v ≠ 0) : Real.exp (-s) • v ≠ 0 :=
    smul_ne_zero (Real.exp_pos _).ne' hv
  refine ncard_eq_two.2 ⟨ι (Real.exp (-s₁) • u), ι (Real.exp (-s₂) • -u), fun h ↦ ?_, ?_⟩
  · -- The two trajectories are the two opposite half-lines of the stable line.
    have h' := hinj h
    rw [smul_neg, eq_neg_iff_add_eq_zero, ← add_smul] at h'
    exact hu ((smul_eq_zero.1 h').resolve_left (by positivity))
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨-, hys⟩, hyc⟩
    obtain ⟨v, rfl⟩ := hrange ▸ hys
    obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu).1 hL v
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · right
      rw [show a • u = (-a) • -u by rw [smul_neg, neg_smul, neg_neg]] at hyc ⊢
      rw [hu₂ (-a) (neg_pos.2 ha) hyc]
    · rw [zero_smul, h0] at hyc
      exact absurd hyc hqc.ne
    · left
      rw [hu₁ a ha hyc]
  · rintro (rfl | rfl)
    · exact ⟨hmem _ (hne s₁ hu), hs₁⟩
    · exact ⟨hmem _ (hne s₂ (neg_ne_zero.2 hu)), hs₂⟩

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **Two trajectories from the only critical point of top index.** Under the Morse–Smale
condition, if `p` is the only critical point of index `n`, then there are exactly two
trajectories from `p` to each critical point `q` of index `n - 1`: the two halves of `W^s(q) - {q}`
both come from a critical point of index `n`. -/
theorem ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank {p q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p) :
    (hX.morseTrajectorySlice p q).ncard = 2 := by
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Every trajectory into `q` comes from a critical point of index `n`, hence from `p`.
  have hW (y : M) (hys : y ∈ hX.flow.stableSet q) (hyq : y ≠ q) : y ∈ hX.flow.unstableSet p := by
    obtain ⟨p', hp', hyp'⟩ := mem_iUnion₂.1 ((hX.iUnion_unstableSet hf).symm ▸ mem_univ y :
      y ∈ ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.unstableSet x)
    have hp'q : p' ≠ q := by
      rintro rfl
      exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet hfd ⟨hyp', hys⟩)
    have hlt := h.manifoldMorseIndex_lt hf hp' hq hp'q ⟨y, hyp', hys⟩
    have hle : manifoldMorseIndex 𝓘(ℝ, E) f p' ≤ Module.finrank ℝ E :=
      manifoldMorseIndex_le_finrank
    rwa [← huniq p' hp' (by omega)]
  -- Some trajectory runs from `p` to `q`, so the middle level lies strictly between their values.
  obtain ⟨y, hys, hyq⟩ := hX.exists_mem_stableSet_ne hfd hq (by omega)
  have hpq : p ≠ q := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet hfd ⟨hW y hys hyq, hys⟩)
  have hy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq ⟨hW y hys hyq, hys⟩
  have heq : hX.morseTrajectorySlice p q =
      hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = (f p + f q) / 2} := by
    ext z
    simp only [mem_morseTrajectorySlice, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [heq]
  exact hX.ncard_unstableSet_inter_stableSet_inter_level_eq_two hfd hq hind hW
    (by linarith [hy.1, hy.2]) (by linarith [hy.1, hy.2])

/-- **Two trajectories to the only critical point of index zero.** Under the Morse–Smale
condition, if `m` is the only critical point of index `0`, then there are exactly two
trajectories to `m` from each critical point `q` of index `1`: the two halves of `W^u(q) - {q}`
both go to a critical point of index `0`. -/
theorem ncard_morseTrajectorySlice_eq_two_of_unique_index_zero {q m : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f q = 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m) :
    (hX.morseTrajectorySlice q m).ncard = 2 := by
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Reverse the flow: `-X` is adapted to `-f`, for which `q` has index `n - 1`.
  set hXn := hX.neg hf
  have hfn : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) (-f) := hf.neg.contMDiff.mdifferentiable (by simp)
  have hqn : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (-f) q = 0 := mfderiv_neg_eq_zero_iff.2 hq
  have hindn : manifoldMorseIndex 𝓘(ℝ, E) (-f) q + 1 = Module.finrank ℝ E := by
    have := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
      ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  have hu (x : M) : hX.flow.unstableSet x = hXn.flow.stableSet x :=
    hX.unstableSet_eq_stableSet_neg hf x
  have hs (x : M) : hX.flow.stableSet x = hXn.flow.unstableSet x := by
    rw [hX.neg_flow hf, Flow.unstableSet_reverse]
  -- Every trajectory out of `q` goes to a critical point of index `0`, hence to `m`.
  have hW (y : M) (hyu : y ∈ hXn.flow.stableSet q) (hyq : y ≠ q) :
      y ∈ hXn.flow.unstableSet m := by
    rw [← hu] at hyu
    rw [← hs]
    obtain ⟨m', hm', hym'⟩ := mem_iUnion₂.1 ((hX.iUnion_stableSet hf).symm ▸ mem_univ y :
      y ∈ ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.stableSet x)
    have hqm' : q ≠ m' := by
      rintro rfl
      exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet hfd ⟨hyu, hym'⟩)
    have hlt := h.manifoldMorseIndex_lt hf hq hm' hqm' ⟨y, hyu, hym'⟩
    rwa [← huniq m' hm' (by omega)]
  -- Some trajectory runs from `q` to `m`, so the middle level lies strictly between their values.
  obtain ⟨y, hys, hyq⟩ := hXn.exists_mem_stableSet_ne hfn hqn (by omega)
  have hym := hW y hys hyq
  rw [← hu] at hys
  rw [← hs] at hym
  have hqm : q ≠ m := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet hfd ⟨hys, hym⟩)
  have hy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqm ⟨hys, hym⟩
  have heq : hX.morseTrajectorySlice q m = hXn.flow.unstableSet m ∩ hXn.flow.stableSet q ∩
      {z | (-f) z = -((f q + f m) / 2)} := by
    ext z
    simp only [mem_morseTrajectorySlice, mem_inter_iff, mem_ofPred_eq, hu, hs, Pi.neg_apply,
      neg_inj]
    tauto
  rw [heq]
  exact hXn.ncard_unstableSet_inter_stableSet_inter_level_eq_two hfn hqn hindn hW
    (by simp only [Pi.neg_apply]; linarith [hy.1, hy.2])
    (by simp only [Pi.neg_apply]; linarith [hy.1, hy.2])

/-- At the only critical point `p` of index `n`, every coefficient of the mod-two Morse boundary
vanishes. -/
theorem morseBoundaryCoeff_eq_zero_of_unique_index_finrank {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p)
    (q : criticalPoints 𝓘(ℝ, E) f) : h.morseBoundaryCoeff hf p q = 0 := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [h.morseBoundaryCoeff_eq_ncard hf hind,
      h.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) (by omega) huniq]
    exact ZMod.natCast_self 2
  · exact h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind

/-- **The mod-two Morse boundary vanishes at a unique critical point of top index.** If `p` is the
only critical point of index `n`, then `∂ p = 0`. -/
theorem morseBoundary_single_eq_zero_of_unique_index_finrank {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p) (a : ZMod 2) :
    h.morseBoundary hf (Finsupp.single p a) = 0 := by
  ext q
  simp [h.morseBoundaryCoeff_eq_zero_of_unique_index_finrank hf hp huniq q]

/-- **No boundary reaches a unique critical point of index zero.** If `m` is the only critical
point of index `0`, then its coefficient in the mod-two Morse boundary of every critical point
vanishes. -/
theorem morseBoundaryCoeff_eq_zero_of_unique_index_zero {m : criticalPoints 𝓘(ℝ, E) f}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (q : criticalPoints 𝓘(ℝ, E) f) : h.morseBoundaryCoeff hf q m = 0 := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1
  · rw [h.morseBoundaryCoeff_eq_ncard hf hind,
      h.ncard_morseTrajectorySlice_eq_two_of_unique_index_zero hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) (by omega) huniq]
    exact ZMod.natCast_self 2
  · exact h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind

/-- **A unique critical point of index zero is not hit by the boundary.** If `m` is the only
critical point of index `0`, then the coefficient of `m` in `∂ c` vanishes for every mod-two
chain `c`. -/
theorem morseBoundary_apply_eq_zero_of_unique_index_zero {m : criticalPoints 𝓘(ℝ, E) f}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) : h.morseBoundary hf c m = 0 := by
  simp [h.morseBoundary_apply hf, h.morseBoundaryCoeff_eq_zero_of_unique_index_zero hf hm huniq]

/-- **The mod-two Morse boundary of a surface with one maximum and one minimum vanishes.** On a
compact surface, if `f` has at most one critical point of index `2` and at most one of index `0`,
then the mod-two Morse boundary of every Morse–Smale adapted pseudo-gradient is zero. This applies,
for instance, to the standard Morse function on the torus. -/
theorem morseBoundary_eq_zero_of_finrank_eq_two (hE : Module.finrank ℝ E = 2)
    (hmax : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 2}.Subsingleton)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton) :
    h.morseBoundary hf = 0 := by
  have hcoeff (p q : criticalPoints 𝓘(ℝ, E) f) : h.morseBoundaryCoeff hf p q = 0 := by
    by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
    · have hle : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ Module.finrank ℝ E :=
        manifoldMorseIndex_le_finrank
      have hp := mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2
      have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2
      -- On a surface, the indices of `p` and `q` are `2` and `1`, or `1` and `0`.
      rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f p = 2 ∨
          manifoldMorseIndex 𝓘(ℝ, E) f q = 0) with hp2 | hq0
      · exact h.morseBoundaryCoeff_eq_zero_of_unique_index_finrank hf (hE ▸ hp2)
          (fun y hy hy2 ↦ hmax ⟨hy, hE ▸ hy2⟩ ⟨hp, hp2⟩) q
      · exact h.morseBoundaryCoeff_eq_zero_of_unique_index_zero hf hq0
          (fun y hy hy0 ↦ hmin ⟨hy, hy0⟩ ⟨hq, hq0⟩) p
    · exact h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind
  ext p q
  simp [hcoeff]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
