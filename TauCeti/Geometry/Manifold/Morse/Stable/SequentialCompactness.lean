/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Breaking
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Data.Fin.Basic
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# Sequential compactness of trajectories on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M`, and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. This file proves that spaces of trajectories
of `X` are sequentially compact up to breaking.

For any critical points `p` and `r`, every sequence of points of trajectories from `p` to `r` has a
subsequence converging to a *broken trajectory*: a chain of critical points
`p = x 0, x 1, …, x k = r` of strictly decreasing Morse index, together with points `z i` on
trajectories from `x i` to `x (i + 1)`, which are the limits of the points of the orbits of the
subsequence at times `s i`. The time shifts are ordered, `s i' - s i` tending to `+∞` whenever
`i < i'`, so the components appear in order and move apart. Convergence of these points gives
convergence of the orbits on compact time windows, locally uniformly in time for any compatible
uniform structure, by `Flow.tendstoLocallyUniformly_orbit`. When each trajectory is represented by
its point on a level `c` containing no critical point, the representatives themselves converge to
the point of the level `c` on the component crossing it.

When `ind p = ind r + 2`, the broken trajectories at a regular level are described more explicitly:
the subsequence converges either to a trajectory from `p` to `r`, or to a trajectory broken once,
at a critical point `q` with `ind p = ind q + 1 = ind r + 2`. In the broken case, the
representatives converge to a point of the component crossing the level `c`, and time translates of
the same subsequence converge to a point of the other component, at times tending to `+∞` when the
level is crossed by the component from `p` to `q`, and to `-∞` when it is crossed by the component
from `q` to `r`. This is the compactness half of the classical proof that the Morse boundary
squares to zero: the broken index-two trajectories counted by
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_morseBoundary_single_apply` are the
only possible limits of unbroken ones.

None of this constructs a topology on the compactified trajectory spaces, and it does not prove
gluing, the converse statement that every broken trajectory is such a limit. The index-two result
is the manifold form of `TauCeti.exists_subseq_unbroken_or_broken_of_morseIndex_eq_add_two`, for a
negative-gradient flow on a vector space with compact sublevels.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_subseq_tendsto_broken_of_tendsto_mem_stableSet`: a sequence in `W^s(r)`
  converging to a point of `W^s(b)` converges, after time shifts tending to `+∞`, to a broken
  trajectory from `b` to `r`.
* `IsMorseSmale.exists_subseq_tendsto_broken`: sequential compactness of the trajectories from
  `p` to `r`, with broken limits and ordered time shifts.
* `IsMorseSmale.exists_subseq_tendsto_broken_of_mem_level`: the same for representatives on a
  regular level, which converge to the level point of the component crossing it.
* `IsMorseSmale.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two`: index-two
  sequential compactness at a regular intermediate level.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X}

/-- **Forward broken limits.** Let `v` be a sequence of points of the stable manifold `W^s(r)`
converging to a point `y` of the stable manifold `W^s(b)` of a critical point `b`. Then a
subsequence of `v` converges, after time shifts tending to `+∞`, to a trajectory broken along a
chain of critical points `b = x 0, x 1, …, x k = r` of strictly decreasing Morse index. The
component from `x i` to `x (i + 1)` passes through the point `z i`, which is the limit of the
points of the orbits of the subsequence at the times `s i`. The time shifts are ordered:
`s i' - s i` tends to `+∞` whenever `i < i'`. When `b = r` the chain is the single point `r`. -/
theorem exists_subseq_tendsto_broken_of_tendsto_mem_stableSet (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {b r y : M} (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hy : y ∈ hX.flow.stableSet b) {v : ℕ → M}
    (hv : Tendsto v atTop (𝓝 y)) (hvr : ∀ j, v j ∈ hX.flow.stableSet r) :
    ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M) (s : Fin k → ℕ → ℝ) (n : ℕ → ℕ),
      StrictMono n ∧ x 0 = b ∧ x (Fin.last k) = r ∧
      (∀ i, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x i) = 0) ∧
      StrictAnti (fun i ↦ manifoldMorseIndex 𝓘(ℝ, E) f (x i)) ∧
      (∀ i, z i ∈ hX.flow.unstableSet (x i.castSucc) ∩ hX.flow.stableSet (x i.succ)) ∧
      (∀ i, Tendsto (s i) atTop atTop) ∧
      (∀ i i', i < i' → Tendsto (fun j ↦ s i' j - s i j) atTop atTop) ∧
      ∀ i, Tendsto (fun j ↦ hX.flow (s i j) (v (n j))) atTop (𝓝 (z i)) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Break the limit at `b`, follow the outgoing orbit to the next critical point `b'`, of smaller
  -- index, and continue from there by induction on the index of `b`.
  induction hm : manifoldMorseIndex 𝓘(ℝ, E) f b using Nat.strong_induction_on
    generalizing b y v with
  | _ m ih =>
    by_cases hbr : b = r
    · subst hbr
      exact ⟨0, fun _ ↦ b, Fin.elim0, Fin.elim0, id, strictMono_id, rfl, rfl, fun _ ↦ hb,
        fun i j hij ↦ (hij.ne (Subsingleton.elim (α := Fin 1) i j)).elim, fun i ↦ i.elim0,
        fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    obtain ⟨w, hwU, hwb, n₁, t, hn₁, ht, hlim⟩ :=
      hX.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hf hy hv
        (Frequently.of_forall fun j ↦ (Flow.disjoint_stableSet hbr).notMem_of_mem_right (hvr j))
    obtain ⟨ψ, hψ, hn₁ψ⟩ := strictMono_subseq_of_tendsto_atTop hn₁
    obtain ⟨b', hb', hwb'⟩ := hX.exists_tendsto_atTop hf w
    have hwb' : w ∈ hX.flow.stableSet b' := Flow.mem_stableSet.2 hwb'
    have hbb' : b ≠ b' := by
      rintro rfl
      exact hwb (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hwU, hwb'⟩)
    have hlt := h.manifoldMorseIndex_lt hf hbb' ⟨w, hwU, hwb'⟩
    obtain ⟨k, x, z, s, n, hn, hx0, hxk, hxc, hxi, hz, hs, hss, hzlim⟩ :=
      ih _ (hm ▸ hlt) hb' hwb' (hlim.comp hψ.tendsto_atTop)
        (fun j ↦ Flow.isInvariant_stableSet _ r _ (hvr _)) rfl
    have hT : Tendsto (fun j ↦ t (ψ (n j))) atTop atTop :=
      ht.comp (hψ.tendsto_atTop.comp hn.tendsto_atTop)
    refine ⟨k + 1, Fin.cons b x, Fin.cons w z,
      Fin.cons (fun j ↦ t (ψ (n j))) (fun i j ↦ s i j + t (ψ (n j))), n₁ ∘ ψ ∘ n,
      hn₁ψ.comp hn, rfl, by rw [← Fin.succ_last, Fin.cons_succ, hxk],
      Fin.forall_fin_succ.2 ⟨hb, hxc⟩, ?_, Fin.forall_fin_succ.2 ⟨?_, fun i ↦ ?_⟩,
      Fin.forall_fin_succ.2 ⟨hT, fun i ↦ (hs i).atTop_add_atTop hT⟩, ?_,
      Fin.forall_fin_succ.2 ⟨(hlim.comp hψ.tendsto_atTop).comp hn.tendsto_atTop, fun i ↦ ?_⟩⟩
    · rw [Fin.strictAnti_iff_succ_lt] at hxi ⊢
      refine Fin.forall_fin_succ.2 ⟨by simpa [hx0] using hm ▸ hlt, fun i ↦ ?_⟩
      simpa [← Fin.succ_castSucc] using hxi i
    · simpa [hx0] using And.intro hwU hwb'
    · simpa [← Fin.succ_castSucc] using hz i
    · intro i i' hii'
      induction i' using Fin.cases with
      | zero => exact absurd hii' (Fin.not_lt_zero i)
      | succ i' =>
        induction i using Fin.cases with
        | zero => simpa using hs i'
        | succ i => simpa using hss i i' (Fin.succ_lt_succ_iff.1 hii')
    · simpa [Flow.map_add] using hzlim i

/-- **Sequential compactness of trajectories, with broken limits.** Let `p` and `r` be critical
points, and `u` a sequence of points of trajectories from `p` to `r`. Then a subsequence of `u`
converges, after time shifts, to a trajectory broken along a chain of critical points
`p = x 0, x 1, …, x k = r` of strictly decreasing Morse index. The component from `x i` to
`x (i + 1)` passes through the point `z i`, which is the limit of the points of the orbits of the
subsequence at the times `s i`, and the time shifts are ordered: `s i' - s i` tends to `+∞`
whenever `i < i'`. By `Flow.tendstoLocallyUniformly_orbit`, the orbits of the shifted subsequence
then converge to the components on compact time windows, for any compatible uniform structure.

Since the chain runs from `p` to `r`, it has at least one component when `p ≠ r`, and the strict
decrease of the index bounds the number `k` of components by `ind p - ind r`. -/
theorem exists_subseq_tendsto_broken (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (u : ℕ → M)
    (hu : ∀ j, u j ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r) :
    ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M) (s : Fin k → ℕ → ℝ) (n : ℕ → ℕ),
      StrictMono n ∧ x 0 = p ∧ x (Fin.last k) = r ∧
      (∀ i, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x i) = 0) ∧
      StrictAnti (fun i ↦ manifoldMorseIndex 𝓘(ℝ, E) f (x i)) ∧
      (∀ i, z i ∈ hX.flow.unstableSet (x i.castSucc) ∩ hX.flow.stableSet (x i.succ)) ∧
      (∀ i i', i < i' → Tendsto (fun j ↦ s i' j - s i j) atTop atTop) ∧
      ∀ i, Tendsto (fun j ↦ hX.flow (s i j) (u (n j))) atTop (𝓝 (z i)) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  -- Flow each `u j` backward until it lies in the `j`-th set of a countable basis at `p`. The
  -- resulting points converge to `p`, a point of `W^s(p)`, and break forward along the chain.
  obtain ⟨B, hB⟩ := (𝓝 p).exists_antitone_basis
  choose τ hτ using fun j ↦ ((Flow.mem_unstableSet.1 (hu j).1).eventually_mem (hB.mem j)).exists
  have hpp : p ∈ hX.flow.stableSet p := by
    simp only [Flow.mem_stableSet, hX.flow_apply_of_mfderiv_eq_zero hp]
    exact tendsto_const_nhds
  obtain ⟨k, x, z, s, n, hn, hx0, hxk, hxc, hxi, hz, -, hss, hzlim⟩ :=
    exists_subseq_tendsto_broken_of_tendsto_mem_stableSet h hf hp hr hpp (hB.tendsto hτ)
      fun j ↦ Flow.isInvariant_stableSet _ r _ (hu j).2
  refine ⟨k, x, z, fun i j ↦ s i j + τ (n j), n, hn, hx0, hxk, hxc, hxi, hz,
    fun i i' hii' ↦ ?_, fun i ↦ ?_⟩
  · simpa only [add_sub_add_right_eq_sub] using hss i i' hii'
  · simpa only [Flow.map_add] using hzlim i

/-- **Sequential compactness of trajectories at a regular level.** Let `p` and `r` be critical
points, `c` a level containing no critical point, and `u` a sequence of points of trajectories from
`p` to `r` on the level `c`, each representing its unparametrized trajectory. Then a subsequence of
`u` converges, after ordered time shifts, to a trajectory broken along a chain of critical points
`p = x 0, x 1, …, x k = r` of strictly decreasing Morse index, as in `exists_subseq_tendsto_broken`.
Moreover, for the component crossing the level `c`, the point `z i` lies on the level `c`, its
time shift `s i` tends to `0`, and the representatives of the subsequence themselves converge to
`z i`. -/
theorem exists_subseq_tendsto_broken_of_mem_level (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) {c : ℝ}
    (hreg : ∀ y, f y = c → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0) (u : ℕ → M)
    (hu : ∀ j, u j ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {z | f z = c}) :
    ∃ (k : ℕ) (x : Fin (k + 1) → M) (z : Fin k → M) (s : Fin k → ℕ → ℝ) (n : ℕ → ℕ),
      StrictMono n ∧ x 0 = p ∧ x (Fin.last k) = r ∧
      (∀ i, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x i) = 0) ∧
      StrictAnti (fun i ↦ manifoldMorseIndex 𝓘(ℝ, E) f (x i)) ∧
      (∀ i, z i ∈ hX.flow.unstableSet (x i.castSucc) ∩ hX.flow.stableSet (x i.succ)) ∧
      (∀ i i', i < i' → Tendsto (fun j ↦ s i' j - s i j) atTop atTop) ∧
      (∀ i, Tendsto (fun j ↦ hX.flow (s i j) (u (n j))) atTop (𝓝 (z i))) ∧
      ∃ i : Fin k, f (z i) = c ∧ Tendsto (s i) atTop (𝓝 0) ∧
        Tendsto (fun j ↦ u (n j)) atTop (𝓝 (z i)) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨k, x, z, s, n, hn, hx0, hxk, hxc, hxi, hz, hss, hzlim⟩ :=
    exists_subseq_tendsto_broken h hf hp hr u fun j ↦ (hu j).1
  -- The critical values decrease strictly along the chain, from above `c` to below `c`, so some
  -- component crosses the level `c`.
  have hne : ∀ i : Fin k, x i.castSucc ≠ x i.succ := fun i he ↦
    (hxi (Fin.castSucc_lt_succ : i.castSucc < i.succ)).ne (congrArg _ he.symm)
  have hxc' : ∀ i, f (x i) ≠ c := fun i he ↦ hreg _ he (hxc i)
  have hcp : c < f (x 0) := by
    refine lt_of_le_of_ne ?_ (hxc' 0).symm
    rw [hx0, ← (hu 0).2]
    exact Flow.le_of_mem_unstableSet_of_antitone (hu 0).1.1 hdf.continuous.continuousAt
      (hX.antitone_flow hdf _)
  have hcr : f (x (Fin.last k)) < c := by
    refine lt_of_le_of_ne ?_ (hxc' _)
    rw [hxk, ← (hu 0).2]
    exact Flow.le_of_mem_stableSet_of_antitone (hu 0).1.2 hdf.continuous.continuousAt
      (hX.antitone_flow hdf _)
  obtain ⟨i, hlo, hhi⟩ := Fin.exists_succ_lt_lt_castSucc (g := fun i ↦ f (x i)) hxc' hcp hcr
  -- The point `y` where this component crosses the level `c`. Shifting every time by `τ` moves
  -- the points `z i'` along their orbits, and makes `y` the point of this component.
  obtain ⟨τ, hτ, -⟩ :=
    hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf (hne i) (hz i) hlo hhi
  set y := hX.flow τ (z i)
  have hy : y ∈ hX.flow.unstableSet (x i.castSucc) ∩ hX.flow.stableSet (x i.succ) :=
    ⟨Flow.isInvariant_unstableSet _ _ τ (hz i).1, Flow.isInvariant_stableSet _ _ τ (hz i).2⟩
  have hzlim' : ∀ i', Tendsto (fun j ↦ hX.flow (s i' j + τ) (u (n j))) atTop
      (𝓝 (hX.flow τ (z i'))) := fun i' ↦
    (((hX.contMDiff_flow_apply τ).continuous.tendsto _).comp (hzlim i')).congr fun j ↦ by
      simp only [Function.comp_apply, ← Flow.map_add, add_comm]
  -- The points `w j` of the orbits of the subsequence at the times `σ j = s i j + τ` converge to
  -- `y`, and their orbits cross the level `c` at the times `-σ j`, which therefore tend to `0`.
  set σ : ℕ → ℝ := fun j ↦ s i j + τ
  set w : ℕ → M := fun j ↦ hX.flow (σ j) (u (n j))
  have hw : Tendsto w atTop (𝓝 y) := hzlim' i
  have huw : ∀ j, hX.flow (-σ j) (w j) = u (n j) := fun j ↦ by
    simp only [w, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have hσ := hX.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet hdf (hne i) hy hw
    (σ := fun j ↦ -σ j) fun j ↦ by rw [huw, (hu (n j)).2, hτ]
  have hlim := hX.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet hdf (hne i) hy
    (σ := 0) (by rw [Flow.map_zero_apply, hτ]) hw (s := fun j ↦ -σ j)
    fun j ↦ by rw [huw, (hu (n j)).2]
  rw [Flow.map_zero_apply] at hlim
  refine ⟨k, x, fun i' ↦ hX.flow τ (z i'), fun i' j ↦ s i' j + τ, n, hn, hx0, hxk, hxc, hxi,
    fun i' ↦ ⟨Flow.isInvariant_unstableSet _ _ τ (hz i').1,
      Flow.isInvariant_stableSet _ _ τ (hz i').2⟩,
    fun i₁ i₂ h₁₂ ↦ ?_, hzlim', i, hτ, by simpa using hσ.neg, hlim.congr fun j ↦ huw j⟩
  simpa only [add_sub_add_right_eq_sub] using hss i₁ i₂ h₁₂

/-- **Index-two sequential compactness at a regular intermediate level.** Let `p` and `r` be
critical points with `ind p = ind r + 2`, and `c` a level containing no critical point. Every
sequence `u` of points of trajectories from `p` to `r` on the level `c` has a subsequence
converging to a point `y` of the level `c`, which lies either on a trajectory from `p` to `r`, or
on one component of a trajectory broken at a critical point `q` of the intermediate index. In the
latter case, time translates of the same subsequence converge to a point `z` of the other
component: the times tend to `+∞` if `y` runs from `p` to `q`, and to `-∞` if `y` runs from `q`
to `r`. -/
theorem exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c : ℝ}
    (hreg : ∀ y, f y = c → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0) (u : ℕ → M)
    (hu : ∀ n, u n ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {z | f z = c}) :
    ∃ (n : ℕ → ℕ) (y : M), StrictMono n ∧ f y = c ∧ Tendsto (fun k ↦ u (n k)) atTop (𝓝 y) ∧
      (y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∨
        ∃ (q z : M) (t : ℕ → ℝ), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
          manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
          manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
          Tendsto (fun k ↦ hX.flow (t k) (u (n k))) atTop (𝓝 z) ∧
          ((y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧
              z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ Tendsto t atTop atTop) ∨
            (y ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧
              z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ Tendsto t atTop atBot))) := by
  obtain ⟨k, x, z, s, n, hn, hx0, hxk, hxc, hxi, hz, hss, hzlim, i, hzi, hsi, hlim⟩ :=
    exists_subseq_tendsto_broken_of_mem_level h hf hp hr hreg u hu
  -- The index drops strictly along the chain, by `2` in total, so it has one or two components.
  have hk : k = 1 ∨ k = 2 := by
    rcases k with _ | _ | _ | k
    · exact absurd (hx0.symm.trans hxk ▸ hind) (by omega)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have h2 : 2 % (k + 4) = 2 := Nat.mod_eq_of_lt (by omega)
      have h₁ := hxi (show (0 : Fin (k + 4)) < 1 by simp)
      have h₂ := hxi (show (1 : Fin (k + 4)) < 2 by simp [Fin.lt_def, h2])
      have h₃ := hxi (show (2 : Fin (k + 4)) < Fin.last _ by simp [Fin.lt_def, h2])
      dsimp only at h₁ h₂ h₃
      rw [hx0] at h₁
      rw [hxk] at h₃
      omega
  rcases hk with rfl | rfl
  · obtain rfl := Subsingleton.elim i 0
    exact ⟨n, z 0, hn, hzi, hlim, Or.inl (by simpa [hx0, ← hxk] using hz 0)⟩
  have h₁ := hxi (show (0 : Fin 3) < 1 by decide)
  have h₂ := hxi (show (1 : Fin 3) < 2 by decide)
  dsimp only at h₁ h₂
  rw [hx0] at h₁
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, hxk] at h₂
  have hz₀ := hz 0
  have hz₁ := hz 1
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hx0] at hz₀
  simp only [Fin.castSucc_one, Fin.succ_one_eq_two, show (2 : Fin 3) = Fin.last 2 from rfl,
    hxk] at hz₁
  have hs := hss 0 1 (by decide)
  fin_cases i
  · -- The level is crossed by the component from `p` to `x 1`.
    refine ⟨n, z 0, hn, hzi, hlim, Or.inr ⟨x 1, z 1, s 1, hxc 1, by omega, by omega, hzlim 1,
      Or.inl ⟨hz₀, hz₁, ?_⟩⟩⟩
    simpa using hs.atTop_add hsi
  · -- The level is crossed by the component from `x 1` to `r`.
    refine ⟨n, z 1, hn, hzi, hlim, Or.inr ⟨x 1, z 0, s 0, hxc 1, by omega, by omega, hzlim 0,
      Or.inr ⟨hz₁, hz₀, ?_⟩⟩⟩
    simpa using (tendsto_neg_atTop_atBot.comp hs).atBot_add hsi

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
