/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Breaking
import Mathlib.Geometry.Manifold.Metrizable

/-!
# Sequential compactness of index-two trajectories on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M`, and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. Let `p` and `r` be critical points with
`ind p = ind r + 2`, and represent each trajectory from `p` to `r` by its point on a level `c`
containing no critical point. This file proves that every sequence of such trajectories has a
subsequence converging either to a trajectory from `p` to `r`, or to a trajectory broken once, at a
critical point `q` with `ind p = ind q + 1 = ind r + 2`.

In the broken case, the representatives converge to a point of the component crossing the level
`c`, and time translates of the same subsequence converge to a point of the other component. The
times tend to `+∞` when the level is crossed by the component from `p` to `q`, and to `-∞` when it
is crossed by the component from `q` to `r`. Convergence of the representatives gives convergence
of the whole orbits, locally uniformly in time for any compatible uniform structure, by
`Flow.tendstoLocallyUniformly_orbit`.

This is the compactness half of the classical proof that the Morse boundary squares to zero: the
broken index-two trajectories counted by
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_morseBoundary_single_apply` are the
only possible limits of unbroken ones. It does not construct a topology on the compactified
trajectory space, and it does not prove gluing, the converse statement that every broken
trajectory is such a limit.

This is the manifold form of `TauCeti.exists_subseq_unbroken_or_broken_of_morseIndex_eq_add_two`,
for a negative-gradient flow on a vector space with compact sublevels.

## Main results

* `IsMorseSmale.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two`, in the
  namespace `TauCeti.IsAdaptedPseudoGradient`: index-two sequential compactness at a regular
  intermediate level.

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

/-- A forward break of a sequence of points of `W^s(r)` at a critical point `q` with
`ind q = ind r + 1` continues along a trajectory from `q` to `r`, which is the limit of time
translates of a subsequence. -/
private theorem exists_forward_break_of_index_one (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {q r y : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hqr : q ≠ r) (hind : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (hy : y ∈ hX.flow.stableSet q) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 y))
    (hur : ∀ n, u n ∈ hX.flow.stableSet r) :
    ∃ z ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r, ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      StrictMono n ∧ Tendsto t atTop atTop ∧
        Tendsto (fun k ↦ hX.flow (t k) (u (n k))) atTop (𝓝 z) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨z, hzU, hzq, n, t, hn, ht, hlim⟩ :=
    hX.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hf hy hu
      (Frequently.of_forall fun n ↦ (Flow.disjoint_stableSet hqr.symm).notMem_of_mem_left (hur n))
  have hzS : z ∈ closure (hX.flow.stableSet r) := mem_closure_of_tendsto hlim
    (Eventually.of_forall fun k ↦ Flow.isInvariant_stableSet _ r (t k) (hur (n k)))
  -- The limit `z` runs from `q` to some critical point `b`; index counting forces `b = r`.
  obtain ⟨b, hb, hzb⟩ := hX.exists_tendsto_atTop hf z
  have hzb : z ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hzb
  have hqb : q ≠ b := by
    rintro rfl
    exact hzq (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hzU, hzb⟩)
  have hbq := h.manifoldMorseIndex_lt hf hq hb hqb ⟨z, hzU, hzb⟩
  obtain rfl : b = r := by
    by_contra hbr
    have := h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hb hr hbr
      ⟨z, hzS, hzb⟩
    omega
  obtain ⟨ψ, hψ, hnψ⟩ := strictMono_subseq_of_tendsto_atTop hn
  exact ⟨z, ⟨hzU, hzb⟩, n ∘ ψ, t ∘ ψ, hnψ, ht.comp hψ.tendsto_atTop,
    hlim.comp hψ.tendsto_atTop⟩

/-- A backward break of a sequence of points of `W^u(p)` at a critical point `q` with
`ind p = ind q + 1` continues along a trajectory from `p` to `q`, which is the limit of time
translates of a subsequence. -/
private theorem exists_backward_break_of_index_one (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q y : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hpq : p ≠ q) (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hy : y ∈ hX.flow.unstableSet q) {u : ℕ → M} (hu : Tendsto u atTop (𝓝 y))
    (hup : ∀ n, u n ∈ hX.flow.unstableSet p) :
    ∃ z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q, ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      StrictMono n ∧ Tendsto t atTop atBot ∧
        Tendsto (fun k ↦ hX.flow (t k) (u (n k))) atTop (𝓝 z) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨z, hzS, hzq, n, t, hn, ht, hlim⟩ :=
    hX.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet hf hy hu
      (Frequently.of_forall fun n ↦ (Flow.disjoint_unstableSet hpq).notMem_of_mem_left (hup n))
  have hzU : z ∈ closure (hX.flow.unstableSet p) := mem_closure_of_tendsto hlim
    (Eventually.of_forall fun k ↦ Flow.isInvariant_unstableSet _ p (t k) (hup (n k)))
  -- The limit `z` runs from some critical point `a` to `q`; index counting forces `a = p`.
  obtain ⟨a, ha, hza⟩ := hX.exists_tendsto_atBot hf z
  have hza : z ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 hza
  have haq : a ≠ q := by
    rintro rfl
    exact hzq (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hza, hzS⟩)
  have hqa := h.manifoldMorseIndex_lt hf ha hq haq ⟨z, hza, hzS⟩
  obtain rfl : a = p := by
    by_contra hap
    have := h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf ha hp hap
      ⟨z, hzU, hza⟩
    omega
  obtain ⟨ψ, hψ, hnψ⟩ := strictMono_subseq_of_tendsto_atTop hn
  exact ⟨z, ⟨hza, hzS⟩, n ∘ ψ, t ∘ ψ, hnψ, ht.comp hψ.tendsto_atTop,
    hlim.comp hψ.tendsto_atTop⟩

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
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  -- Extract a convergent subsequence of representatives, and the critical endpoints `a` and `b`
  -- of the trajectory through its limit `y`.
  obtain ⟨y, -, n, hn, hlim⟩ := isCompact_univ.tendsto_subseq (x := u) fun _ ↦ mem_univ _
  have hyc : f y = c := (isClosed_eq hdf.continuous continuous_const).mem_of_tendsto hlim
    (Eventually.of_forall fun k ↦ (hu (n k)).2)
  have hyU : y ∈ closure (hX.flow.unstableSet p) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ (hu (n k)).1.1)
  have hyS : y ∈ closure (hX.flow.stableSet r) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ (hu (n k)).1.2)
  obtain ⟨a, ha, hya⟩ := hX.exists_tendsto_atBot hf y
  obtain ⟨b, hb, hyb⟩ := hX.exists_tendsto_atTop hf y
  have hya : y ∈ hX.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : y ∈ hX.flow.stableSet b := Flow.mem_stableSet.2 hyb
  -- The level `c` is regular, so the trajectory through `y` is not constant.
  have hab : a ≠ b := by
    rintro rfl
    exact hreg y hyc (hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hya, hyb⟩ ▸ ha)
  have hba := h.manifoldMorseIndex_lt hf ha hb hab ⟨y, hya, hyb⟩
  have hpa : a ≠ p → manifoldMorseIndex 𝓘(ℝ, E) f a < manifoldMorseIndex 𝓘(ℝ, E) f p :=
    fun hap ↦ h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf ha hp hap
      ⟨y, hyU, hya⟩
  have hrb : b ≠ r → manifoldMorseIndex 𝓘(ℝ, E) f r < manifoldMorseIndex 𝓘(ℝ, E) f b :=
    fun hbr ↦ h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hb hr hbr
      ⟨y, hyS, hyb⟩
  -- Three nonconstant components would force an index drop of at least three.
  have hends : a = p ∨ b = r := by
    by_contra! hne
    have := hpa hne.1
    have := hrb hne.2
    omega
  rcases hends with rfl | rfl
  · by_cases hbr : b = r
    · subst hbr
      exact ⟨n, y, hn, hyc, hlim, Or.inl ⟨hya, hyb⟩⟩
    -- The trajectory through `y` runs from `p` to `b` and breaks forward at `b`.
    have := hrb hbr
    have hbr' : manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 := by omega
    obtain ⟨z, hz, m, t, hm, ht, hzlim⟩ := exists_forward_break_of_index_one h hf hb hr hbr hbr'
      hyb hlim fun k ↦ (hu (n k)).1.2
    exact ⟨n ∘ m, y, hn.comp hm, hyc, hlim.comp hm.tendsto_atTop,
      Or.inr ⟨b, z, t, hb, by omega, hbr', hzlim, Or.inl ⟨⟨hya, hyb⟩, hz, ht⟩⟩⟩
  · by_cases hap : a = p
    · subst hap
      exact ⟨n, y, hn, hyc, hlim, Or.inl ⟨hya, hyb⟩⟩
    -- The trajectory through `y` runs from `a` to `r` and breaks backward at `a`.
    have := hpa hap
    have hpa' : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f a + 1 := by omega
    obtain ⟨z, hz, m, t, hm, ht, hzlim⟩ := exists_backward_break_of_index_one h hf hp ha
      (Ne.symm hap) hpa' hya hlim fun k ↦ (hu (n k)).1.1
    exact ⟨n ∘ m, y, hn.comp hm, hyc, hlim.comp hm.tendsto_atTop,
      Or.inr ⟨a, z, t, ha, hpa', by omega, hzlim, Or.inr ⟨⟨hya, hyb⟩, hz, ht⟩⟩⟩

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
