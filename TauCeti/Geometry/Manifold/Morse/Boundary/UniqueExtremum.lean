/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.Geometry.Manifold.Orientation.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.Orientation.Flow
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
  `-1`, on any compact manifold (orientable or not), so `signedTrajectoryCount` vanishes
  (`signedTrajectoryCount_eq_zero_of_unstableSet`,
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
  `signedTrajectoryCount_eq_zero_of_unstableSet`,
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
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : {i // φq.weight i < 0} → ℝ, v₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).1
      (by rw [φq.finrank_negativeWeight_fun]; omega)
  obtain ⟨r, hr, hrT⟩ := φq.exists_pos_forall_norm_lt_mem_target
  set δ := r / (2 * (‖φq.coord (φq.negativeExtend v₀)‖ + 1))
  have hδ : 0 < δ := by positivity
  have hnorm (a : ℝ) (ha : |a| = δ) : ‖φq.coord (φq.negativeExtend (a • v₀))‖ < r := by
    rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs, ha]
    have hpos : 0 < 2 * (‖φq.coord (φq.negativeExtend v₀)‖ + 1) := by positivity
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [norm_nonneg (φq.coord (φq.negativeExtend v₀))]
  have hpt (a : ℝ) (ha : a ≠ 0) (har : ‖φq.coord (φq.negativeExtend (a • v₀))‖ < r) :
      let y := φq.toChart.symm (φq.negativeExtend (a • v₀))
      y ∈ hX.flow.unstableSet q ∧ y ≠ q ∧ X y = a • hX.unstableFrame φq y v₀ := by
    set y := φq.toChart.symm (φq.negativeExtend (a • v₀))
    have htar : φq.negativeExtend (a • v₀) ∈ φq.toChart.target :=
      φq.coord.symm_apply_apply (φq.negativeExtend (a • v₀)) ▸ hrT _ har
    have hyapp : φq.toChart y = φq.negativeExtend (a • v₀) := φq.toChart.right_inv htar
    have h0 : 0 ∈ hX.linearBackwardTimes φq y :=
      hX.zero_mem_linearBackwardTimes_toChart_symm_negativeExtend hrT har
    have hyu : y ∈ hX.flow.unstableSet q :=
      hX.mem_unstableSet_of_zero_mem_linearBackwardTimes hφq h0 fun i hi ↦ by
        rw [hyapp, φq.coord_negativeExtend_of_not_weight_neg _ hi]
    have hyne : y ≠ q := fun hyq ↦
      hv₀ ((smul_eq_zero.1 (φq.injective_negativeExtend
        (by rw [← hyapp, hyq, φq.apply_self, map_zero]))).resolve_left ha)
    have hXeq : X y = a • hX.unstableFrame φq y v₀ := by
      rw [← map_smul, hX.unstableFrame_eq_of_zero_mem_linearBackwardTimes hφq h0 hyapp]
    exact ⟨hyu, hyne, hXeq⟩
  obtain ⟨hz₁u, hz₁ne, hXz₁⟩ := hpt (-δ) (neg_ne_zero.2 hδ.ne')
    (hnorm (-δ) (by rw [abs_neg, abs_of_pos hδ]))
  obtain ⟨hz₂u, hz₂ne, hXz₂⟩ := hpt δ hδ.ne' (hnorm δ (abs_of_pos hδ))
  set z₁ := φq.toChart.symm (φq.negativeExtend ((-δ) • v₀))
  set z₂ := φq.toChart.symm (φq.negativeExtend (δ • v₀))
  have hz₁ : z₁ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet m := ⟨hz₁u, hW z₁ hz₁u hz₁ne⟩
  have hz₂ : z₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet m := ⟨hz₂u, hW z₂ hz₂u hz₂ne⟩
  have hC₁ := bijective_trajectoryComparison hφq hφm hMS hf hqm hz₁
  have hC₂ := bijective_trajectoryComparison hφq hφm hMS hf hqm hz₂
  have hempty : {i | φm.weight i < 0} = ∅ :=
    (Set.ncard_eq_zero (hs := toFinite _)).1 (φm.ncard_weight_neg.trans hm0)
  have hsub (v w : {i // φm.weight i < 0} → ℝ) : v = w :=
    funext fun ⟨i, hi⟩ ↦ False.elim ((Set.eq_empty_iff_forall_notMem.1 hempty i) hi)
  have hneg₁ := hX.mvfderiv_apply_lt_zero z₁
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hqne hz₁)
  have hneg₂ := hX.mvfderiv_apply_lt_zero z₂
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hqne hz₂)
  rw [hXz₁, map_smul, smul_eq_mul] at hneg₁
  rw [hXz₂, map_smul, smul_eq_mul] at hneg₂
  have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)) =
      Module.finrank ℝ (ℝ × ({i // φm.weight i < 0} → ℝ)) := by
    rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_self, φm.finrank_negativeWeight_fun]
    omega
  have hmap := oq.map_eq_neg_map_of_snd_eq_of_fst_mul_neg hcard
    (e₁ := LinearEquiv.ofBijective (hX.trajectoryComparison φq φm z₁).toLinearMap hC₁)
    (e₂ := LinearEquiv.ofBijective (hX.trajectoryComparison φq φm z₂).toLinearMap hC₂)
    (fun _ ↦ hsub _ _) (hsub _ _)
    (by
      simp only [LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
        trajectoryComparison_apply]
      exact mul_neg_of_pos_of_neg
        (neg_lt_zero.1 (by nlinarith : -mvfderiv 𝓘(ℝ, E) f z₁ (hX.unstableFrame φq z₁ v₀) < 0))
        (by nlinarith : mvfderiv 𝓘(ℝ, E) f z₂ (hX.unstableFrame φq z₂ v₀) < 0))
  exact hX.exists_trajectorySign_eq_one_and_eq_neg_one_of_trajectorySign_eq_neg
    hφq hφm hMS hf hz₁ hz₂ (hX.trajectorySign_eq_neg_of_map_eq_neg hC₁ hC₂ hmap)

/-- **Vanishing of the signed trajectory count into an index-zero critical point.** If `q` has
index `1`, `m` has index `0`, and every point of `W^u(q) - {q}` lies in `W^s(m)`, then the signed
count of trajectories from `q` to `m` vanishes, without any orientability assumption on `M`. -/
theorem signedTrajectoryCount_eq_zero_of_unstableSet {q m : M}
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
    hX.signedTrajectoryCount φq φm oq om hqm = 0 :=
  hX.signedTrajectoryCount_eq_zero_of_exists_trajectorySign
    (hX.ncard_morseTrajectorySlice_eq_two_of_unstableSet hf
      ((φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl) (by omega) hW)
    (exists_trajectorySign_eq_one_and_eq_neg_one_of_unstableSet hφq hφm hMS hf oq om hm0 hqm hW)

/-- Moving backwards along the flow preserves whether the top-index unstable frame carries `op` to
a manifold orientation `oM`. -/
private theorem map_unstableFrameEquiv_flow_neg_eq_iff {p : M} {φp : MorseChart E f p}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    {y : M} (hy : y ∈ hX.flow.unstableSet p) (T : ℝ) :
    Orientation.map _ (hX.unstableFrameEquiv hφp hf hp
        ((Flow.apply_mem_unstableSet_iff _ (-T)).2 hy)) op =
      oM.orientationAt (hX.flow (-T) y) ↔
    Orientation.map _ (hX.unstableFrameEquiv hφp hf hp hy) op = oM.orientationAt y := by
  have hflow_eq : (hX.flow (-T) : M → M) =
      globalFlow X (hX.contMDiff.of_le (by simp)) hX.isCompleteVectorField (-T) :=
    funext fun z ↦ by simp [hX.flow_apply]
  have hpres : Manifold.Orientation.IsOrientationPreservingAt oM oM (hX.flow (-T)) y := by
    rw [hflow_eq]
    exact Manifold.Orientation.isOrientationPreservingAt_globalFlow oM
      (hX.contMDiff.of_le (by simp)) hX.isCompleteVectorField (-T) y
  obtain ⟨Φe, hΦe, hΦo⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 hpres
  obtain ⟨T₀, hT₀⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hy).exists
  set eₛ := LinearEquiv.smulOfNeZero ℝ ({i // φp.weight i < 0} → ℝ) (Real.exp T)
    (Real.exp_ne_zero T)
  have heq : hX.unstableFrameEquiv hφp hf hp ((Flow.apply_mem_unstableSet_iff _ (-T)).2 hy) =
      (eₛ.trans (hX.unstableFrameEquiv hφp hf hp hy)).trans Φe.toLinearEquiv := by
    refine LinearEquiv.ext fun c ↦ ?_
    simp only [unstableFrameEquiv_apply, LinearEquiv.trans_apply, eₛ,
      LinearEquiv.smulOfNeZero_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    have hΦev : Φe (hX.unstableFrame φp y c) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow (-T)) y (hX.unstableFrame φp y c) :=
      DFunLike.congr_fun hΦe _
    rw [map_smul, map_smul, hΦev, hX.unstableFrame_flow hφp hT₀ (-T) c, neg_neg]
  have hsop : Orientation.map _ eₛ op = op :=
    (op.map_eq_iff_det_pos eₛ (by rw [Fintype.card_fin, φp.finrank_negativeWeight_fun])).2 <| by
      have hsmul : eₛ.toLinearMap = Real.exp T • LinearMap.id :=
        LinearMap.ext fun _ ↦ by simp [eₛ]
      rw [hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one]
      exact pow_pos (Real.exp_pos T) _
  rw [heq, Orientation.map_trans, Orientation.map_trans, hsop, ← hΦo]
  exact (Orientation.map _ Φe.toLinearEquiv).injective.eq_iff

/-- On an orientable manifold, at a critical point `p` of top index `dim M`, some orientation `oM`
of `M` agrees with the image of `op` under `unstableFrameEquiv` at every point of `W^u(p)`. -/
private theorem exists_orientation_forall_map_unstableFrameEquiv_eq [Orientable 𝓘(ℝ, E) M]
    {p : M} {φp : MorseChart E f p}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    ∃ oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)),
      ∀ y (hy : y ∈ hX.flow.unstableSet p),
        Orientation.map _ (hX.unstableFrameEquiv hφp hf hp hy) op = oM.orientationAt y := by
  obtain ⟨o₀⟩ := Orientable.nonempty_orientation (I := 𝓘(ℝ, E)) (M := M)
  set o₁ := o₀.reindex (finCongr hp.symm)
  set eExt : ({i // φp.weight i < 0} → ℝ) ≃ₗ[ℝ] E :=
    LinearEquiv.ofBijective φp.negativeExtend
      ⟨φp.injective_negativeExtend, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [φp.finrank_negativeWeight_fun, hp])).1 φp.injective_negativeExtend⟩
  set oExt := Manifold.Orientation.model (I := 𝓘(ℝ, E)) (Orientation.map _ eExt op)
    (by rw [Fintype.card_fin, hp])
  obtain ⟨Dp, hDp⟩ := isInvertible_mfderiv_chart φp.mem_maximalAtlas_one φp.mem_source
  obtain ⟨oM, hoMp⟩ :
      ∃ oM, Manifold.Orientation.IsOrientationPreservingAt oM oExt φp.toChart p := by
    rcases Manifold.Orientation.isOrientationPreservingAt_or_isOrientationReversingAt
        o₁ oExt φp.toChart p Dp hDp with hpos | hneg
    · exact ⟨o₁, hpos⟩
    · exact ⟨-o₁, (Manifold.Orientation.isOrientationPreservingAt_neg_left
        o₁ oExt φp.toChart p).2 hneg⟩
  refine ⟨oM, fun y hy ↦ ?_⟩
  have hchart_smooth : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 φp.toChart p :=
    ((contMDiffOn_of_mem_maximalAtlas φp.mem_maximalAtlas).contMDiffAt
      (φp.toChart.open_source.mem_nhds φp.mem_source)).of_le (by simp)
  have hnear :=
    (hX.eventually_zero_mem_linearBackwardTimes_of_manifoldMorseIndex_eq_finrank φp hp).and
      (Manifold.Orientation.eventually_isOrientationPreservingAt hchart_smooth hoMp)
  have htend : Tendsto (fun T : ℝ ↦ hX.flow (-T) y) atTop (𝓝 p) :=
    (Flow.mem_unstableSet.1 hy).comp tendsto_neg_atTop_atBot
  obtain ⟨T, hT0, hTpres⟩ := (htend.eventually hnear).exists
  rw [← hX.map_unstableFrameEquiv_flow_neg_eq_iff hφp hf hp op oM hy T]
  obtain ⟨Dz, hDz, hDzo⟩ :=
    (Manifold.Orientation.isOrientationPreservingAt_model_iff _ _ _ _ _).1 hTpres
  have hDzv (v : TangentSpace 𝓘(ℝ, E) (hX.flow (-T) y)) :
      Dz v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart (hX.flow (-T) y) v := by
    simpa [NormedSpace.fromTangentSpace_apply] using DFunLike.congr_fun hDz v
  have hcomp : φp.toChart ∘ hX.flow (-0) = φp.toChart := funext fun _ ↦ by simp
  have heq : (hX.unstableFrameEquiv hφp hf hp
      ((Flow.apply_mem_unstableSet_iff _ (-T)).2 hy)).trans Dz.toLinearEquiv = eExt := by
    refine LinearEquiv.ext fun c ↦ ?_
    simp only [LinearEquiv.trans_apply, unstableFrameEquiv_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, eExt]
    have hfr := hX.mfderiv_unstableFrame hφp hT0 c
    rw [hcomp, neg_zero, Real.exp_zero, one_smul] at hfr
    exact (hDzv _).trans hfr
  apply (Orientation.map _ Dz.toLinearEquiv).injective
  rw [← Orientation.map_trans, heq, hDzo]

omit [CompactSpace M] [T2Space M] in
/-- Choose a model orientation on `E`, a nonzero stable vector `u₀` at `q`, and a small radius `δ`
so that both `±δ • u₀` lie in the linear ball of `φq` and `φq.toChart` preserves orientation at
`φq.toChart.symm (±δ • u₀)`. -/
private theorem exists_localStable_ray_param {p q : M} (φq : MorseChart E f q)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    ∃ (o₁ : Orientation ℝ E (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
      (u₀ : φq.stableSubspace) (r δ : ℝ),
      u₀ ≠ 0 ∧ 0 < δ ∧ (∀ z, ‖z‖ < r → φq.coord.symm z ∈ φq.toChart.target) ∧
      ∀ a : ℝ, |a| = δ → ‖φq.coord (a • (u₀ : E))‖ < r ∧
        Manifold.Orientation.IsOrientationPreservingAt oM
          (Manifold.Orientation.model (I := 𝓘(ℝ, E)) o₁ (by rw [Fintype.card_fin, hp]))
          φq.toChart (φq.toChart.symm (a • (u₀ : E))) := by
  set o₀ := (Module.finBasisOfFinrankEq ℝ E hp.symm).orientation
  set oEq₀ := Manifold.Orientation.model (I := 𝓘(ℝ, E)) o₀ (by rw [Fintype.card_fin, hp])
  obtain ⟨Dq₀, hDq₀⟩ := isInvertible_mfderiv_chart φq.mem_maximalAtlas_one φq.mem_source
  obtain ⟨o₁, hoMq⟩ : ∃ o₁ : Orientation ℝ E (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)),
      Manifold.Orientation.IsOrientationPreservingAt oM
        (Manifold.Orientation.model (I := 𝓘(ℝ, E)) o₁ (by rw [Fintype.card_fin, hp]))
        φq.toChart q := by
    rcases Manifold.Orientation.isOrientationPreservingAt_or_isOrientationReversingAt
        oM oEq₀ φq.toChart q Dq₀ hDq₀ with hpos | hneg
    · exact ⟨o₀, hpos⟩
    · refine ⟨-o₀, ?_⟩
      rw [Manifold.Orientation.model_neg]
      exact (Manifold.Orientation.isOrientationPreservingAt_neg_right oM oEq₀ φq.toChart q).2 hneg
  set oEq := Manifold.Orientation.model (I := 𝓘(ℝ, E)) o₁ (by rw [Fintype.card_fin, hp])
  have hchart_smooth : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 φq.toChart q :=
    ((contMDiffOn_of_mem_maximalAtlas φq.mem_maximalAtlas).contMDiffAt
      (φq.toChart.open_source.mem_nhds φq.mem_source)).of_le (by simp)
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : φq.stableSubspace, u₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := φq.stableSubspace)).1
      (by have := φq.finrank_stableSubspace_add_manifoldMorseIndex; omega)
  obtain ⟨r, hr, hrT⟩ := φq.exists_pos_forall_norm_lt_mem_target
  have hγ : ContinuousAt (fun a : ℝ ↦ φq.toChart.symm (a • (u₀ : E))) 0 := by
    refine (φq.toChart.continuousAt_symm ?_).comp
      (continuous_id.smul continuous_const).continuousAt
    rw [zero_smul, ← φq.apply_self]
    exact φq.toChart.map_source φq.mem_source
  have hev : ∀ᶠ a : ℝ in 𝓝 0, ‖φq.coord (a • (u₀ : E))‖ < r ∧
      Manifold.Orientation.IsOrientationPreservingAt oM oEq φq.toChart
        (φq.toChart.symm (a • (u₀ : E))) := by
    have hnorm_ev : ∀ᶠ a : ℝ in 𝓝 0, ‖φq.coord (a • (u₀ : E))‖ < r :=
      ((φq.continuous_coord.norm.comp (continuous_id.smul continuous_const)).continuousAt
        ).eventually (gt_mem_nhds (by simp [hr]))
    have hpres_ev := Manifold.Orientation.eventually_isOrientationPreservingAt hchart_smooth hoMq
    have hγt : Tendsto (fun a : ℝ ↦ φq.toChart.symm (a • (u₀ : E))) (𝓝 0) (𝓝 q) := by
      simpa using hγ.tendsto
    exact hnorm_ev.and (hγt.eventually hpres_ev)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨o₁, u₀, r, ε / 2, hu₀, half_pos hε, hrT, fun a ha ↦
    hball a (by simp [ha, half_lt_self hε])⟩

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
  obtain ⟨oM, hoM⟩ := hX.exists_orientation_forall_map_unstableFrameEquiv_eq hφp hf hp op
  obtain ⟨o₁, u₀, r, δ, hu₀, hδ, hrT, hray⟩ := exists_localStable_ray_param φq hp hpq oM
  obtain ⟨har₁, hpres₁⟩ := hray δ (abs_of_pos hδ)
  obtain ⟨har₂, hpres₂⟩ := hray (-δ) (by rw [abs_neg, abs_of_pos hδ])
  have hpt (a : ℝ) (ha : a ≠ 0) (har : ‖φq.coord (a • (u₀ : E))‖ < r) :
      let y := φq.toChart.symm (a • (u₀ : E))
      0 ∈ hX.linearForwardTimes φq y ∧ y ∈ hX.flow.stableSet q ∧ y ≠ q ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y) = (-a) • (u₀ : E) := by
    set y := φq.toChart.symm (a • (u₀ : E))
    have htar : a • (u₀ : E) ∈ φq.toChart.target :=
      φq.coord.symm_apply_apply (a • (u₀ : E)) ▸ hrT _ har
    have hysrc : y ∈ φq.toChart.source := φq.toChart.map_target htar
    have hyapp : φq.toChart y = a • (u₀ : E) := φq.toChart.right_inv htar
    have hu : a • (u₀ : E) ∈ φq.stableSubspace := φq.stableSubspace.smul_mem a u₀.property
    have h0 : 0 ∈ hX.linearForwardTimes φq y :=
      hX.zero_mem_linearForwardTimes_toChart_symm hrT hu har
    have hys : y ∈ hX.flow.stableSet q :=
      hX.mem_stableSet_of_zero_mem_linearForwardTimes hφq h0 (hyapp.symm ▸ hu)
    have hyne : y ≠ q := fun hyq ↦
      hu₀ (Subtype.ext ((smul_eq_zero.1 (by rw [← hyapp, hyq, φq.apply_self])).resolve_left ha))
    have hXeq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y) = (-a) • (u₀ : E) := by
      rw [φq.mfderiv_toChart_apply_of_mem_stableSubspace hφq hysrc (hyapp.symm ▸ hu), hyapp,
        neg_smul]
    exact ⟨h0, hys, hyne, hXeq⟩
  obtain ⟨h0₁, hzs₁, hzne₁, hXz₁⟩ := hpt δ hδ.ne' har₁
  obtain ⟨h0₂, hzs₂, hzne₂, hXz₂⟩ := hpt (-δ) (neg_ne_zero.2 hδ.ne') har₂
  set z₁ := φq.toChart.symm (δ • (u₀ : E))
  set z₂ := φq.toChart.symm ((-δ) • (u₀ : E))
  have hz₁ : z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨hW z₁ hzs₁ hzne₁, hzs₁⟩
  have hz₂ : z₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨hW z₂ hzs₂ hzne₂, hzs₂⟩
  have hC₁ := bijective_trajectoryComparison hφp hφq hMS hf hpq hz₁
  have hC₂ := bijective_trajectoryComparison hφp hφq hMS hf hpq hz₂
  obtain ⟨D₁, hD₁, hD₁o⟩ :=
    (Manifold.Orientation.isOrientationPreservingAt_model_iff _ _ _ _ _).1 hpres₁
  obtain ⟨D₂, hD₂, hD₂o⟩ :=
    (Manifold.Orientation.isOrientationPreservingAt_model_iff _ _ _ _ _).1 hpres₂
  have hD₁v (v : TangentSpace 𝓘(ℝ, E) z₁) :
      D₁ v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart z₁ v := by
    simpa [NormedSpace.fromTangentSpace_apply] using DFunLike.congr_fun hD₁ v
  have hD₂v (v : TangentSpace 𝓘(ℝ, E) z₂) :
      D₂ v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart z₂ v := by
    simpa [NormedSpace.fromTangentSpace_apply] using DFunLike.congr_fun hD₂ v
  set G₁ := (hX.unstableFrameEquiv hφp hf hp hz₁.1).trans D₁.toLinearEquiv
  set G₂ := (hX.unstableFrameEquiv hφp hf hp hz₂.1).trans D₂.toLinearEquiv
  set e₁ := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq z₁).toLinearMap hC₁
  set e₂ := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq z₂).toLinearMap hC₂
  have hne : p ≠ q := by rintro rfl; omega
  have hDsymm₁ : D₁.symm (u₀ : E) = (-δ)⁻¹ • X z₁ :=
    D₁.symm_apply_eq.2 (by rw [map_smul, hD₁v _, hXz₁, smul_smul,
      inv_mul_cancel₀ (neg_ne_zero.2 hδ.ne'), one_smul])
  have hDsymm₂ : D₂.symm (u₀ : E) = δ⁻¹ • X z₂ :=
    D₂.symm_apply_eq.2 (by rw [map_smul, hD₂v _, hXz₂, neg_neg,
      smul_smul, inv_mul_cancel₀ hδ.ne', one_smul])
  have hneg₁ := hX.mvfderiv_apply_lt_zero z₁
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hz₁)
  have hneg₂ := hX.mvfderiv_apply_lt_zero z₂
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hz₂)
  have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
      Module.finrank ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)) := by
    rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_self, φq.finrank_negativeWeight_fun]
    omega
  have hΨ₁ := hX.unstableFrameEquiv_symm_trans_trajectoryComparison_apply hφp hφq hf hp hz₁.1 h0₁
    D₁ hD₁v hC₁
  have hΨ₂ := hX.unstableFrameEquiv_symm_trans_trajectoryComparison_apply hφp hφq hf hp hz₂.1 h0₂
    D₂ hD₂v hC₂
  have hGo₁ : Orientation.map _ G₁ op = o₁ := by
    rw [Orientation.map_trans, hoM z₁ hz₁.1, hD₁o]
  have hGo₂ : Orientation.map _ G₂ op = o₁ := by
    rw [Orientation.map_trans, hoM z₂ hz₂.1, hD₂o]
  have hmap₁ : Orientation.map _ e₁ op = Orientation.map _ (G₁.symm.trans e₁) o₁ := by
    rw [← hGo₁, ← Orientation.map_trans]
    exact congrArg (Orientation.map _ · op) (LinearEquiv.ext fun _ ↦ by simp)
  have hmap₂ : Orientation.map _ e₂ op = Orientation.map _ (G₂.symm.trans e₂) o₁ := by
    rw [← hGo₂, ← Orientation.map_trans]
    exact congrArg (Orientation.map _ · op) (LinearEquiv.ext fun _ ↦ by simp)
  have hmap : Orientation.map _ e₂ op = -Orientation.map _ e₁ op := by
    rw [hmap₂, hmap₁]
    exact o₁.map_eq_neg_map_of_snd_eq_of_fst_mul_neg hcard
      (fun w ↦ by rw [hΨ₁ w, hΨ₂ w])
      (by rw [hΨ₁]; exact φq.mem_stableSubspace_iff_negativeCoord_eq_zero.1 u₀.property)
      (by
        rw [hΨ₁, hΨ₂, hDsymm₁, hDsymm₂, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_neg_of_pos_of_neg
          (mul_pos_of_neg_of_neg (inv_lt_zero.2 (neg_lt_zero.2 hδ)) hneg₁)
          (mul_neg_of_pos_of_neg (inv_pos.2 hδ) hneg₂))
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

/-- Every point of `W^s(q) - {q}` at a critical point `q` of index `n - 1` comes from the unique
critical point of index `n`. -/
private theorem mem_unstableSet_of_unique_index_finrank {p q : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = Module.finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = Module.finrank ℝ E → y = p)
    {y : M} (hys : y ∈ hX.flow.stableSet q) (hyq : y ≠ q) :
    y ∈ hX.flow.unstableSet p := by
  obtain ⟨p', hp', hyp'⟩ := hX.exists_mem_unstableSet hf y
  have hp'q : p' ≠ q := by
    rintro rfl
    exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hyp', hys⟩)
  have hlt := h.manifoldMorseIndex_lt hf hp'q ⟨y, hyp', hys⟩
  have hle : manifoldMorseIndex 𝓘(ℝ, E) f p' ≤ Module.finrank ℝ E := manifoldMorseIndex_le_finrank
  rwa [← huniq p' hp' (by omega)]

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
    (hφm : ∀ y ∈ φm.toChart.source,
      φm.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φm.toChart y (X y)) =
        fun i ↦ -(φm.weight i * φm.coord (φm.toChart y) i))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (om : Orientation ℝ ({i // φm.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f m)))
    (hm0 : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (hqm : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m) :
    hX.signedTrajectoryCount φq φm oq om hqm = 0 :=
  signedTrajectoryCount_eq_zero_of_unstableSet hφq hφm h hf oq om hm0 hqm fun _ ↦
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
  · exact h.signedTrajectoryCount_eq_zero_of_unique_index_zero hf hφp hφq op oq hq0 hpq
      fun y hy hy0 ↦ hmin ⟨hy, hy0⟩ ⟨hqcrit, hq0⟩

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
