/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.IndexOne
public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.Geometry.Manifold.Orientation.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.Morse.Stable.Orientation
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Morse trajectories and boundaries at a unique maximum and a unique minimum

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n` and `X` a
pseudo-gradient field adapted to `f` satisfying the Morse–Smale condition. Let `q` be a critical
point of index `n - 1`. Its stable manifold `W^s(q)` is a line, so `W^s(q) - {q}` consists of
exactly two trajectories, one on each side of `q`. Each of them comes from a critical point of
index `n`, since the Morse index strictly drops along every trajectory. If `f` has a single
critical point `p` of index `n`, both trajectories come from `p`, so there are exactly two
trajectories from `p` to `q`, and the coefficient of `q` in the mod-two Morse boundary of `p` is
zero. Reversing the flow, if `f` has a single critical point `m` of index `0`, every critical point
of index `1` has exactly two trajectories to `m`.

With orientations of the unstable manifolds (`TauCeti.IsAdaptedPseudoGradient.trajectorySign`), the
signs of these two trajectories behave asymmetrically with respect to orientability of `M`:

* From a critical point `q` of index `1` to a critical point `m` of index `0` into which both
  branches of `W^u(q) - {q}` flow, the two trajectories **always** carry opposite signs `+1` and
  `-1`, on any compact manifold (orientable or not)
  (`exists_trajectorySign_eq_one_and_eq_neg_one_of_unstableSet`), so `signedTrajectoryCount`
  vanishes (`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_eq_zero_of_mem_stableSet`,
  `IsMorseSmale.signedTrajectoryCount_eq_zero_of_unique_index_zero`). Near `q`, the unstable frame
  fixes a tangent direction along the one-dimensional unstable manifold `W^u(q)`, whereas the flow
  velocity `X` points away from `q` in opposite directions on the two branches. This applies both
  on a sphere with multiple maxima, one saddle, and one minimum, and for the saddle-to-minimum
  differential on the non-orientable real projective plane `ℝℙ²`.
* From a critical point `p` of top index `n` to a critical point `q` of index `n - 1` whose two
  stable branches `W^s(q) - {q}` both come from `p`, the two trajectories carry opposite signs `+1`
  and `-1` when `M` is **orientable**, so `signedTrajectoryCount` vanishes
  (`signedTrajectoryCount_eq_zero_of_stableSet`,
  `IsMorseSmale.signedTrajectoryCount_eq_zero_of_unique_index_finrank`). An orientation of `M`
  compares the orientations induced by the top-dimensional unstable frame `W^u(p)` on the two sides
  of `q` along the orientation-preserving flow; the two incoming velocities approach `q` from
  opposite halves of the one-dimensional stable subspace while the normal coordinates agree,
  reversing the sign. Orientability is essential here: on `ℝℙ²`, the two trajectories from the
  maximum to the saddle carry the same sign.

On a surface every coefficient of the Morse boundary joins a critical point of index `2` to one of
index `1`, or a critical point of index `1` to one of index `0`. So the mod-two Morse boundary of a
Morse–Smale pair on a compact surface vanishes as soon as `f` has at most one critical point of
index `2` and at most one of index `0`, and on an orientable compact surface every pair of
consecutive-index critical points has opposite-sign trajectories and vanishing signed count
(`IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two`,
`IsMorseSmale.signedTrajectoryCount_eq_zero_of_finrank_eq_two`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `ncard_unstableSet_inter_stableSet_inter_level_eq_two`,
  `ncard_morseTrajectorySlice_eq_two_of_stableSet`, and
  `ncard_morseTrajectorySlice_eq_two_of_unstableSet`: two trajectories when `W^s(q) - {q} ⊆ W^u(p)`
  at index `n - 1`, or `W^u(q) - {q} ⊆ W^s(m)` at index `1`.
* `IsMorseSmale.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank` and
  `IsMorseSmale.ncard_morseTrajectorySlice_eq_two_of_unique_index_zero`: two trajectories from a
  unique critical point of index `n`, or to a unique critical point of index `0`.
* `IsMorseSmale.morseBoundary_single_eq_zero_of_unique_index_finrank`,
  `IsMorseSmale.morseBoundary_apply_eq_zero_of_unique_index_zero`, and
  `IsMorseSmale.morseBoundary_eq_zero_of_finrank_eq_two`: vanishing of the mod-two Morse boundary.
* `exists_trajectorySign_eq_one_and_eq_neg_one_of_unstableSet`,
  `IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_zero`, and
  `IsMorseSmale.signedTrajectoryCount_eq_zero_of_unique_index_zero`: opposite signs and vanishing
  signed count into an index-zero critical point, without orientability of `M`.
* `exists_trajectorySign_eq_one_and_eq_neg_one_of_stableSet`,
  `signedTrajectoryCount_eq_zero_of_stableSet`,
  `IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_finrank`,
  `IsMorseSmale.signedTrajectoryCount_eq_zero_of_unique_index_finrank`,
  `IsMorseSmale.exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two`, and
  `IsMorseSmale.signedTrajectoryCount_eq_zero_of_finrank_eq_two`: opposite signs and vanishing
  signed count from a top-index critical point on an orientable manifold, and on orientable
  surfaces with at most one maximum and one minimum.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus and the real projective plane).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of descending manifolds and opposite-sign
  cancellation).
-/

public section

open Filter Function Set Topology
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
    {p q : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (hW : ∀ y ∈ hX.flow.stableSet q, y ≠ q → y ∈ hX.flow.unstableSet p) {c : ℝ}
    (hqc : f q < c) (hcp : c < f p) :
    (hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = c}).ncard = 2 := by
  obtain ⟨φ, δ, hemb, hrange, h0, -, hsmul⟩ := hX.exists_stableParam hq
  set ι := hX.stableParam φ δ
  have hinj : Injective ι := hemb.isEmbedding.injective
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
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpq (hmem v hv) hqc hcp
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
      have haneg : a • u = (-a) • -u := by rw [smul_neg, neg_smul, neg_neg]
      rw [haneg] at hyc ⊢
      rw [hu₂ (-a) (neg_pos.2 ha) hyc]
    · rw [zero_smul, h0] at hyc
      exact absurd hyc hqc.ne
    · left
      rw [hu₁ a ha hyc]
  · rintro (rfl | rfl)
    · exact ⟨hmem _ (hne s₁ hu), hs₁⟩
    · exact ⟨hmem _ (hne s₂ (neg_ne_zero.2 hu)), hs₂⟩

/-- **Two trajectories on the middle level into a critical point of index `n - 1`.** If every point
of `W^s(q)` other than `q` lies in `W^u(p)` and `ind q = n - 1`, then the middle-level slice of
trajectories from `p` to `q` consists of two points. -/
theorem ncard_morseTrajectorySlice_eq_two_of_stableSet {p q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (hW : ∀ y ∈ hX.flow.stableSet q, y ≠ q → y ∈ hX.flow.unstableSet p) :
    (hX.morseTrajectorySlice p q).ncard = 2 := by
  obtain ⟨y, hys, hyq⟩ := hX.exists_mem_stableSet_ne hq (by omega)
  have hpq : p ≠ q := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hW y hys hyq, hys⟩)
  have hy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq ⟨hW y hys hyq, hys⟩
  have heq : hX.morseTrajectorySlice p q =
      hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = (f p + f q) / 2} := by
    ext z
    simp only [mem_morseTrajectorySlice, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [heq]
  exact hX.ncard_unstableSet_inter_stableSet_inter_level_eq_two hq hind hW
    (by linarith [hy.1, hy.2]) (by linarith [hy.1, hy.2])

/-- **Two trajectories on the middle level out of a critical point of index `1`.** If every point
of `W^u(q)` other than `q` lies in `W^s(m)` and `ind q = 1`, then the middle-level slice of
trajectories from `q` to `m` consists of two points. -/
theorem ncard_morseTrajectorySlice_eq_two_of_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) {q m : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f q = 1)
    (hW : ∀ y ∈ hX.flow.unstableSet q, y ≠ q → y ∈ hX.flow.stableSet m) :
    (hX.morseTrajectorySlice q m).ncard = 2 := by
  set hXn := hX.neg hf
  have hqn : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (-f) q = 0 := mfderiv_neg_eq_zero_iff.2 hq
  have hindn : manifoldMorseIndex 𝓘(ℝ, E) (-f) q + 1 = Module.finrank ℝ E := by
    have := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
      ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  have hWn (y : M) (hys : y ∈ hXn.flow.stableSet q) (hyq : y ≠ q) :
      y ∈ hXn.flow.unstableSet m := by
    rw [← hX.unstableSet_eq_stableSet_neg hf] at hys
    rw [hX.neg_flow hf, Flow.unstableSet_reverse]
    exact hW y hys hyq
  rw [← hX.neg_morseTrajectorySlice hf]
  exact hXn.ncard_morseTrajectorySlice_eq_two_of_stableSet hqn hindn hWn

/-! ### Opposite trajectory signs at extrema -/

section Signed

variable {hX}

/-- **Opposite trajectory signs into an index-zero critical point.** Let `q` have Morse index `1`,
`m` have Morse index `0`, and suppose that every point of `W^u(q) - {q}` lies in `W^s(m)`. Then for
any Morse charts at `q` and `m` in which `X` is linear and any orientations `oq` and `om`, the two
trajectories from `q` to `m` carry opposite signs `+1` and `-1`. No orientability of `M` is
needed. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_unstableSet {q m : M}
    {φq : MorseChart E f q} {φm : MorseChart E f m}
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hφm : ∀ y ∈ φm.toChart.source,
      φm.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φm.toChart y (X y)) =
        fun i ↦ -(φm.weight i * φm.coord (φm.toChart y) i))
    (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (om : Orientation ℝ ({i // φm.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f m)))
    (hm0 : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (hqm : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1)
    (hW : ∀ y ∈ hX.flow.unstableSet q, y ≠ q → y ∈ hX.flow.stableSet m) :
    ∃ y₁ ∈ hX.morseTrajectorySlice q m, ∃ y₂ ∈ hX.morseTrajectorySlice q m,
      hX.trajectorySign φq φm oq om hqm y₁ = 1 ∧ hX.trajectorySign φq φm oq om hqm y₂ = -1 := by
  have hqne : q ≠ m := by rintro rfl; omega
  have hqcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := (φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl
  -- The middle-level slice consists of two distinct points, which lie on different orbits.
  obtain ⟨y₁, y₂, hne, hslice⟩ := Set.ncard_eq_two.1
    (hX.ncard_morseTrajectorySlice_eq_two_of_unstableSet hf hqcrit (by omega) hW)
  have hy₁ : y₁ ∈ hX.morseTrajectorySlice q m := hslice ▸ mem_insert _ _
  have hy₂ : y₂ ∈ hX.morseTrajectorySlice q m := hslice ▸ mem_insert_of_mem _ (mem_singleton _)
  have hy₁m := hX.mem_morseTrajectorySlice.1 hy₁
  have hy₂m := hX.mem_morseTrajectorySlice.1 hy₂
  have hnot : y₂ ∉ hX.flow.orbit y₁ := by
    intro hmem
    obtain ⟨t, ht⟩ := hX.flow.mem_orbit_iff.1 hmem
    exact hne (hX.eq_of_flow_eq_of_value_eq hqne ⟨hy₁m.1, hy₁m.2.1⟩ (t' := 0)
      (ht.trans (Flow.map_zero_apply _ _).symm) (hy₁m.2.2.trans hy₂m.2.2.symm))
  -- Distinct trajectories from index `1` to index `0` carry opposite signs `±1`.
  have hneg := hX.trajectorySign_eq_neg_of_mem_stableSet (φ := φq) (φq := φm) (op := oq)
    (oq := om) (hpq := hqm) hφq hf (by omega) ⟨hy₁m.1, hy₁m.2.1⟩ ⟨hy₂m.1, hy₂m.2.1⟩ hnot
  rcases hX.trajectorySign_eq_one_or_eq_neg_one (op := oq) (oq := om) (hpq := hqm) hφq hφm hMS hf
      ⟨hy₁m.1, hy₁m.2.1⟩ with h₁ | h₁
  · exact ⟨y₁, hy₁, y₂, hy₂, h₁, hneg.trans (by rw [h₁])⟩
  · exact ⟨y₂, hy₂, y₁, hy₁, hneg.trans (by rw [h₁]; ring), h₁⟩

/-- On an orientable manifold, at a critical point `p` of top index `dim M`, some orientation `oM`
of `M` agrees with the image of `op` under the unstable frame at every point of `W^u(p)`. -/
private theorem exists_orientation_forall_map_unstableFrame_eq [Orientable 𝓘(ℝ, E) M]
    {p : M} {φp : MorseChart E f p}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    ∃ oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)),
      ∀ y ∈ hX.flow.unstableSet p, ∀ (hby : Bijective (hX.unstableFrame φp y)),
        Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φp y).toLinearMap hby)
            (op.reindex ℝ _ (finCongr hp)) =
          oM.orientationAt y := by
  obtain ⟨o₀⟩ := Orientable.nonempty_orientation (I := 𝓘(ℝ, E)) (M := M)
  have hpcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 := (φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl
  have hbp := bijective_unstableFrame (hX := hX) hφp hp (mem_linearBackwardTimes_self hpcrit 0)
  set op' := op.reindex ℝ _ (finCongr hp)
  -- Pick `o₀` or `-o₀` to match `op'` at `p`, then transport along `W^u(p)`.
  obtain ⟨oM, hoMp⟩ : ∃ oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)),
      Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φp p).toLinearMap hbp) op' =
        oM.orientationAt p := by
    rcases (Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φp p).toLinearMap hbp)
        op').eq_or_eq_neg (o₀.orientationAt p) (Nat.card_fin _) with hpos | hneg
    · exact ⟨o₀, hpos⟩
    · exact ⟨-o₀, hneg.trans (Manifold.Orientation.orientationAt_neg o₀ p).symm⟩
  exact ⟨oM, fun y hy hby ↦
    (hX.map_unstableFrame_eq_orientationAt_iff hf hφp hpcrit oM op' hy hby hbp).2 hoMp⟩

/-- Choose a model orientation `oE` on `E`, a nonzero stable vector `u₀` at `q`, and two opposite
points `z₁`, `z₂` along the ray `ℝ • u₀` with linear forward flow at time `0` at which
`φq.toChart` preserves `oM` and `oE`. -/
private theorem exists_stableRay_pair {q : M} (φq : MorseChart E f q)
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q < Module.finrank ℝ E)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E))) :
    ∃ (oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (Module.finrank ℝ E)))
      (u₀ : φq.stableSubspace) (z₁ z₂ : M) (δ : ℝ),
      0 < δ ∧
      0 ∈ hX.linearForwardTimes φq z₁ ∧ 0 ∈ hX.linearForwardTimes φq z₂ ∧
      z₁ ∈ hX.flow.stableSet q ∧ z₂ ∈ hX.flow.stableSet q ∧ z₁ ≠ q ∧ z₂ ≠ q ∧
      φq.toChart z₁ = δ • (u₀ : E) ∧ φq.toChart z₂ = (-δ) • (u₀ : E) ∧
      oM.IsOrientationPreservingAt oE φq.toChart z₁ ∧
      oM.IsOrientationPreservingAt oE φq.toChart z₂ := by
  obtain ⟨oE, hpres_ev⟩ := Manifold.Orientation.exists_eventually_isOrientationPreservingAt
    (contMDiffAt_of_mem_maximalAtlas φq.mem_maximalAtlas_one φq.mem_source)
    (isInvertible_mfderiv_chart φq.mem_maximalAtlas_one φq.mem_source) oM
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : φq.stableSubspace, u₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := φq.stableSubspace)).1
      (by have := φq.finrank_stableSubspace_add_manifoldMorseIndex; omega)
  obtain ⟨r, hr, hrT⟩ := φq.exists_pos_forall_norm_lt_mem_target
  have hγt : Tendsto (fun a : ℝ ↦ φq.toChart.symm (a • (u₀ : E))) (𝓝 0) (𝓝 q) := by
    have hγ : ContinuousAt (fun a : ℝ ↦ φq.toChart.symm (a • (u₀ : E))) 0 :=
      (φq.toChart.continuousAt_symm (by
          rw [zero_smul, ← φq.apply_self]
          exact φq.toChart.map_source φq.mem_source)).comp
        (continuous_id.smul continuous_const).continuousAt
    have hγ0 : φq.toChart.symm ((0 : ℝ) • (u₀ : E)) = q := by
      rw [zero_smul, ← φq.apply_self, φq.toChart.left_inv φq.mem_source]
    simpa [hγ0] using hγ.tendsto
  have hnorm_ev : ∀ᶠ a : ℝ in 𝓝 0, ‖φq.coord (a • (u₀ : E))‖ < r :=
    ((φq.continuous_coord.norm.comp (continuous_id.smul continuous_const)).continuousAt
      ).eventually (gt_mem_nhds (by simp [hr]))
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (hnorm_ev.and (hγt.eventually hpres_ev))
  set δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hpt (a : ℝ) (ha : a ≠ 0) (hab : |a| = δ) :
      let z := φq.toChart.symm (a • (u₀ : E))
      0 ∈ hX.linearForwardTimes φq z ∧ z ∈ hX.flow.stableSet q ∧ z ≠ q ∧
        φq.toChart z = a • (u₀ : E) ∧ oM.IsOrientationPreservingAt oE φq.toChart z := by
    obtain ⟨har, hpres⟩ := hball a (by
      simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hab, δ] using half_lt_self hε)
    set z := φq.toChart.symm (a • (u₀ : E))
    have hzapp : φq.toChart z = a • (u₀ : E) :=
      φq.toChart.right_inv (φq.coord.symm_apply_apply (a • (u₀ : E)) ▸ hrT _ har)
    have hu : a • (u₀ : E) ∈ φq.stableSubspace := φq.stableSubspace.smul_mem a u₀.property
    have h0 := hX.zero_mem_linearForwardTimes_toChart_symm hrT hu har
    refine ⟨h0, hX.mem_stableSet_of_zero_mem_linearForwardTimes hφq h0 (hzapp.symm ▸ hu),
      fun hzq ↦ hu₀ (Subtype.ext ((smul_eq_zero.1
        (by rw [← hzapp, hzq, φq.apply_self])).resolve_left ha)),
      hzapp, hpres⟩
  obtain ⟨h0₁, hzs₁, hzne₁, hto₁, hpres₁⟩ := hpt δ hδ.ne' (abs_of_pos hδ)
  obtain ⟨h0₂, hzs₂, hzne₂, hto₂, hpres₂⟩ := hpt (-δ) (neg_ne_zero.2 hδ.ne')
    (by rw [abs_neg, abs_of_pos hδ])
  exact ⟨oE, u₀, _, _, δ, hδ, h0₁, h0₂, hzs₁, hzs₂, hzne₁, hzne₂, hto₁, hto₂, hpres₁, hpres₂⟩

/-- **Opposite trajectory signs from a top-index critical point.** On an orientable compact
manifold `M` of dimension `n`, let `p` have index `n`, `q` have index `n - 1`, and suppose that
every point of `W^s(q) - {q}` lies in `W^u(p)`. Then for any Morse charts at `p` and `q` in which
`X` is linear and any orientations `op` and `oq`, the two trajectories from `p` to `q` carry
opposite signs `+1` and `-1`. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_stableSet [Orientable 𝓘(ℝ, E) M]
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hW : ∀ y ∈ hX.flow.stableSet q, y ≠ q → y ∈ hX.flow.unstableSet p) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 := by
  have hne : p ≠ q := by rintro rfl; omega
  -- Stage 1: match `op` to an orientation `oM` of `M`, and pick opposite points on a stable ray.
  obtain ⟨oM, hoM⟩ := hX.exists_orientation_forall_map_unstableFrame_eq hφp hf hp op
  obtain ⟨oE, u₀, z₁, z₂, δ, hδ, h0₁, h0₂, hzs₁, hzs₂, hzne₁, hzne₂, hto₁, hto₂, hpres₁, hpres₂⟩ :=
    hX.exists_stableRay_pair φq hφq (by omega) oM
  have hz₁ : z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨hW z₁ hzs₁ hzne₁, hzs₁⟩
  have hz₂ : z₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨hW z₂ hzs₂ hzne₂, hzs₂⟩
  -- Stage 2: the stable comparison maps flip `oM` between `z₁` and `z₂`, hence flip `op`.
  have hC₁ := bijective_trajectoryComparison hφp hφq hMS hf hpq hz₁
  have hC₂ := bijective_trajectoryComparison hφp hφq hMS hf hpq hz₂
  have hA₁ := bijective_mvfderiv_prod_stableNormal hMS hf hφp hφq hp hpq hz₁
  have hA₂ := bijective_mvfderiv_prod_stableNormal hMS hf hφp hφq hp hpq hz₂
  have hoE (x : E) : oE.orientationAt x = oE.orientationAt 0 :=
    Manifold.Orientation.orientationAt_eq_orientationAt oE x 0
  have hflip := hX.map_stableComparison_eq_neg hφq (by omega) u₀.property hoE h0₁ h0₂ hto₁ hto₂
    (mul_neg_of_pos_of_neg hδ (neg_lt_zero.2 hδ))
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hz₁)
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hz₂) hpres₁ hpres₂ hA₁ hA₂
  have hcomp (z : M) (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
      (hC : Bijective (hX.trajectoryComparison φp φq z))
      (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z))) :
      Orientation.map _
          (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)).toLinearMap
            hA) (oM.orientationAt z) =
        (Orientation.map _ (LinearEquiv.ofBijective
            (hX.trajectoryComparison φp φq z).toLinearMap hC) op).reindex
          ℝ _ (finCongr hp) := by
    obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hz.1).exists
    have hF := bijective_unstableFrame hφp hp hT
    have hCF : (LinearEquiv.ofBijective (hX.unstableFrame φp z).toLinearMap hF).trans
        (LinearEquiv.ofBijective
          ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)).toLinearMap hA) =
        LinearEquiv.ofBijective (hX.trajectoryComparison φp φq z).toLinearMap hC :=
      LinearEquiv.ext fun _ ↦ by simp
    rw [← hoM z hz.1 hF, ← Orientation.map_trans, hCF, Orientation.map_reindex]
  rw [hcomp z₁ hz₁ hC₁ hA₁, hcomp z₂ hz₂ hC₂ hA₂, ← Orientation.reindex_neg] at hflip
  have hmap := (Orientation.reindex ℝ _ (finCongr hp)).injective hflip
  -- Stage 3: flow the opposite-signed trajectories to the middle level.
  exact hX.exists_trajectorySign_eq_one_and_eq_neg_one_of_trajectorySign_eq_neg
    hφp hφq hMS hf hz₁ hz₂ (hX.trajectorySign_eq_neg_of_map_eq_neg hC₁ hC₂ hmap)

/-- **Vanishing of the signed trajectory count from a top-index critical point.** On an orientable
compact manifold `M` of dimension `n`, if `p` has index `n`, `q` has index `n - 1`, and every point
of `W^s(q) - {q}` lies in `W^u(p)`, then the signed count of trajectories from `p` to `q`
vanishes. -/
theorem signedTrajectoryCount_eq_zero_of_stableSet [Orientable 𝓘(ℝ, E) M]
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hW : ∀ y ∈ hX.flow.stableSet q, y ≠ q → y ∈ hX.flow.unstableSet p) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 :=
  hX.signedTrajectoryCount_eq_zero_of_exists_trajectorySign
    (hX.ncard_morseTrajectorySlice_eq_two_of_stableSet
      ((φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl) (by omega) hW)
    (exists_trajectorySign_eq_one_and_eq_neg_one_of_stableSet hφp hφq hMS hf op oq hp hpq hW)

end Signed

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **Trajectories out of index one go to the only critical point of index zero.** Under the
Morse–Smale condition, if `m` is the only critical point of index `0`, then every point of the
unstable manifold of a critical point `q` of index `1`, other than `q`, flows to `m`: its
trajectory ends at a critical point of smaller index. -/
theorem mem_stableSet_of_unique_index_zero {q m : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q = 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    {y : M} (hyu : y ∈ hX.flow.unstableSet q) (hyq : y ≠ q) : y ∈ hX.flow.stableSet m := by
  obtain ⟨m', hm', hym'⟩ := hX.exists_mem_stableSet hf y
  have hqm' : q ≠ m' := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hyu, hym'⟩)
  have hlt := h.manifoldMorseIndex_lt hf hqm' ⟨y, hyu, hym'⟩
  rwa [← huniq m' hm' (by omega)]

/-- Every point of `W^s(q) - {q}` at a critical point `q` of index `n - 1` comes from the unique
critical point of index `n`. -/
private theorem mem_unstableSet_of_unique_index_finrank {p q : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p)
    {y : M} (hys : y ∈ hX.flow.stableSet q) (hyq : y ≠ q) :
    y ∈ hX.flow.unstableSet p := by
  have hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := hX.mfderiv_eq_zero_of_mem_stableSet hys
  have hqn : manifoldMorseIndex 𝓘(ℝ, E) (-f) q = 1 := by
    have := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
      ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    omega
  have huniqn (z : M) (hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (-f) z = 0)
      (hz0 : manifoldMorseIndex 𝓘(ℝ, E) (-f) z = 0) : z = p := by
    have hz' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 := mfderiv_neg_eq_zero_iff.1 hz
    have := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hz'
      ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    exact huniq z hz' (by omega)
  rw [hX.unstableSet_eq_stableSet_neg hf]
  exact (h.neg hf).mem_stableSet_of_unique_index_zero hf.neg hqn huniqn
    ((hX.stableSet_eq_unstableSet_neg hf q).subset hys) hyq

/-- **Two trajectories from the only critical point of top index.** Under the Morse–Smale
condition, if `p` is the only critical point of index `n`, then there are exactly two
trajectories from `p` to each critical point `q` of index `n - 1`: the two halves of `W^s(q) - {q}`
both come from a critical point of index `n`. -/
theorem ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank {p q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p) :
    (hX.morseTrajectorySlice p q).ncard = 2 :=
  hX.ncard_morseTrajectorySlice_eq_two_of_stableSet hq hind fun _ ↦
    h.mem_unstableSet_of_unique_index_finrank hf hind huniq

/-- **Two trajectories to the only critical point of index zero.** Under the Morse–Smale
condition, if `m` is the only critical point of index `0`, then there are exactly two
trajectories to `m` from each critical point `q` of index `1`: the two halves of `W^u(q) - {q}`
both go to a critical point of index `0`. -/
theorem ncard_morseTrajectorySlice_eq_two_of_unique_index_zero {q m : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f q = 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m) :
    (hX.morseTrajectorySlice q m).ncard = 2 :=
  hX.ncard_morseTrajectorySlice_eq_two_of_unstableSet hf hq hind fun _ ↦
    h.mem_stableSet_of_unique_index_zero hf hind huniq

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
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) (by omega) huniq]
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
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) (by omega) huniq]
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
      have hp := mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property
      have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property
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

/-- **Opposite trajectory signs to a unique index-zero critical point.** Under the Morse–Smale
condition, if `m` is the only critical point of index `0`, then for every critical point `q` of
index `1`, the two trajectories from `q` to `m` carry opposite signs `+1` and `-1`, without any
orientability assumption on `M`. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_zero {q m : M}
    {φq : MorseChart E f q} {φm : MorseChart E f m}
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hφm : ∀ y ∈ φm.toChart.source,
      φm.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φm.toChart y (X y)) =
        fun i ↦ -(φm.weight i * φm.coord (φm.toChart y) i))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (om : Orientation ℝ ({i // φm.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f m)))
    (hm0 : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (hqm : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m) :
    ∃ y₁ ∈ hX.morseTrajectorySlice q m, ∃ y₂ ∈ hX.morseTrajectorySlice q m,
      hX.trajectorySign φq φm oq om hqm y₁ = 1 ∧ hX.trajectorySign φq φm oq om hqm y₂ = -1 :=
  exists_trajectorySign_eq_one_and_eq_neg_one_of_unstableSet hφq hφm h hf oq om hm0 hqm fun _ ↦
    h.mem_stableSet_of_unique_index_zero hf (by omega) huniq

/-- **The signed trajectory count to a unique index-zero critical point vanishes.** Under the
Morse–Smale condition, if `m` is the only critical point of index `0`, then the signed count of
trajectories from any index-one critical point `q` to `m` vanishes, without any orientability
assumption on `M`. -/
theorem signedTrajectoryCount_eq_zero_of_unique_index_zero {q m : M}
    {φq : MorseChart E f q} {φm : MorseChart E f m}
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (om : Orientation ℝ ({i // φm.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f m)))
    (hm0 : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (hqm : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m) :
    hX.signedTrajectoryCount φq φm oq om hqm = 0 :=
  hX.signedTrajectoryCount_eq_zero_of_mem_stableSet (φ := φq) (φq := φm) (op := oq) (oq := om)
    (hpq := hqm) hφq hf (by omega) fun _ ↦
    h.mem_stableSet_of_unique_index_zero hf (by omega) huniq

/-- **Opposite trajectory signs from a unique top-index critical point.** On an orientable compact
manifold `M` of dimension `n`, if `p` is the only critical point of index `n`, then for every
critical point `q` of index `n - 1`, the two trajectories from `p` to `q` carry opposite signs
`+1` and `-1`. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_finrank [Orientable 𝓘(ℝ, E) M]
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 :=
  exists_trajectorySign_eq_one_and_eq_neg_one_of_stableSet hφp hφq h hf op oq hp hpq fun _ ↦
    h.mem_unstableSet_of_unique_index_finrank hf (by omega) huniq

/-- **The signed trajectory count from a unique top-index critical point vanishes.** On an
orientable compact manifold `M` of dimension `n`, if `p` is the only critical point of index `n`,
then the signed count of trajectories from `p` to any critical point `q` of index `n - 1`
vanishes. -/
theorem signedTrajectoryCount_eq_zero_of_unique_index_finrank [Orientable 𝓘(ℝ, E) M]
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 :=
  signedTrajectoryCount_eq_zero_of_stableSet hφp hφq h hf op oq hp hpq fun _ ↦
    h.mem_unstableSet_of_unique_index_finrank hf (by omega) huniq

/-- **Opposite trajectory signs on an orientable surface with at most one maximum and one
minimum.** On an orientable compact surface, if `f` has at most one critical point of index `2` and
at most one of index `0`, then for any critical points `p`, `q` of consecutive index with Morse
charts in which `X` is linear and any orientations `op` and `oq`, the two trajectories from `p` to
`q` carry opposite signs `+1` and `-1`. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_finrank_eq_two [Orientable 𝓘(ℝ, E) M]
    (hE : Module.finrank ℝ E = 2)
    (hmax : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 2}.Subsingleton)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton)
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 := by
  have hle : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ Module.finrank ℝ E := manifoldMorseIndex_le_finrank
  have hpcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 := (φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl
  have hqcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := (φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f p = 2 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f q = 0) with hp2 | hq0
  · exact h.exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_finrank hf hφp hφq op oq
      (hE ▸ hp2) hpq fun y hy hy2 ↦ hmax ⟨hy, hE ▸ hy2⟩ ⟨hpcrit, hp2⟩
  · exact h.exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_zero hf hφp hφq op oq
      hq0 hpq fun y hy hy0 ↦ hmin ⟨hy, hy0⟩ ⟨hqcrit, hq0⟩

/-- **Signed trajectory counts vanish on an orientable surface with at most one maximum and one
minimum.** On an orientable compact surface, if `f` has at most one critical point of index `2` and
at most one of index `0`, then for any critical points `p`, `q` of consecutive index with Morse
charts in which `X` is linear and any orientations `op` and `oq`, the signed trajectory count from
`p` to `q` vanishes. -/
theorem signedTrajectoryCount_eq_zero_of_finrank_eq_two [Orientable 𝓘(ℝ, E) M]
    (hE : Module.finrank ℝ E = 2)
    (hmax : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 2}.Subsingleton)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton)
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 := by
  have hle : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ Module.finrank ℝ E := manifoldMorseIndex_le_finrank
  have hpcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 := (φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl
  have hqcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := (φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl
  rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f p = 2 ∨
      manifoldMorseIndex 𝓘(ℝ, E) f q = 0) with hp2 | hq0
  · exact h.signedTrajectoryCount_eq_zero_of_unique_index_finrank hf hφp hφq op oq (hE ▸ hp2) hpq
      fun y hy hy2 ↦ hmax ⟨hy, hE ▸ hy2⟩ ⟨hpcrit, hp2⟩
  · exact h.signedTrajectoryCount_eq_zero_of_unique_index_zero hf hφp op oq hq0 hpq
      fun y hy hy0 ↦ hmin ⟨hy, hy0⟩ ⟨hqcrit, hq0⟩

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
