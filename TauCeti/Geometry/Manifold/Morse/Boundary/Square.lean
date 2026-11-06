/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Stable.Compactification

/-!
# The square of the mod-two Morse boundary on a compact manifold counts broken trajectories

Let `f` be a Morse function on a compact boundaryless manifold and `X` an adapted pseudo-gradient
satisfying the Morse–Smale condition. For critical points `p` and `r` whose Morse indices differ by
two, a *broken trajectory* from `p` to `r` is a pair of trajectories, from `p` to a critical point
`q` of the intermediate index and from `q` to `r`. Representing each component by its point on the
middle level between its ends, the broken trajectories form the set
`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet` of triples `(q, z₁, z₂)`.

This set is finite, and the `r`-coefficient of `∂ (∂ p)` is its cardinality modulo two.
Consequently `∂ ∘ ∂ = 0` holds exactly when every set of broken index-two trajectories has even
cardinality. This is the algebraic half of `∂² = 0`.

The geometric half is that broken trajectories are the boundary points of a compact
one-dimensional manifold of trajectories and therefore come in pairs. Recording broken trajectories
on two levels `b < a` instead of the middle levels gives the broken trajectory pairs of
`TauCeti.Geometry.Manifold.Morse.Stable.Compactification`, with the same count. That file
compactifies the space of unbroken index-two trajectories and charts it away from the broken pairs.
So `∂ ∘ ∂ = 0` follows once each broken pair has a half-open neighbourhood `[0, ε)` in the
compactified space. Producing those neighbourhoods by gluing is not done here.

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Square`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseBrokenTrajectorySet`: the broken index-two trajectories from `p` to `r`.
* `IsMorseSmale.finite_morseBrokenTrajectorySet`: there are finitely many.
* `IsMorseSmale.morseBoundary_morseBoundary_single_apply`: the coefficients of `∂ (∂ p)` count
  broken trajectories modulo two.
* `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`: `∂ ∘ ∂ = 0` exactly when every set
  of broken trajectories has even cardinality.
* `ncard_morseBrokenTrajectoryPairs`: broken trajectory pairs on two separating levels are counted
  by `morseBrokenTrajectorySet`.
* `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_of_forall_exists_homeomorph_Ico`:
  `∂ ∘ ∂ = 0`, given half-open neighbourhoods of the broken pairs in the compactified spaces of
  index-two trajectories.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex): the proof that `∂ ∘ ∂ = 0` counts the coefficient of `r` in
  `∂ (∂ p)` as the number of broken trajectories from `p` to `r`.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The broken index-two trajectories from `p` to `r`: triples `(q, z₁, z₂)` of a critical point
`q` whose Morse index lies one below that of `p` and one above that of `r`, a point `z₁` on the
middle-level slice of trajectories from `p` to `q`, and a point `z₂` on the middle-level slice of
trajectories from `q` to `r`. -/
def morseBrokenTrajectorySet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    x.2.1 ∈ hX.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ hX.morseTrajectorySlice x.1 r}

/-- Membership in the set of broken index-two trajectories. -/
@[simp]
theorem mem_morseBrokenTrajectorySet {p r : M} {x : criticalPoints 𝓘(ℝ, E) f × M × M} :
    x ∈ hX.morseBrokenTrajectorySet p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
          x.2.1 ∈ hX.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ hX.morseTrajectorySlice x.1 r :=
  Iff.rfl

/-- A point of a trajectory joining distinct critical points is the only point of its orbit on its
level. -/
private theorem flow_eq_self_of_apply_eq {hX : IsAdaptedPseudoGradient f X}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {c d y : M} (hcd : c ≠ d)
    (hy : y ∈ hX.flow.unstableSet c ∩ hX.flow.stableSet d) {t : ℝ}
    (ht : f (hX.flow t y) = f y) : hX.flow t y = y := by
  have h0 : t = 0 := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hcd hy).injective
    (by simpa only [Flow.map_zero_apply] using ht)
  rw [h0, Flow.map_zero_apply]

/-- **Broken pairs count broken trajectories.** Let `b < a` be levels with `f r < b` and `a < f p`
such that every critical value strictly between `f r` and `f p` lies strictly between `b` and `a`.
Flowing the two components of a broken trajectory from their middle levels to the levels `a` and
`b` matches the broken trajectories `morseBrokenTrajectorySet p r` with the broken trajectory pairs
`morseBrokenTrajectoryPairs p r a b`. -/
theorem ncard_morseBrokenTrajectoryPairs (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M}
    {a b : ℝ} (hrb : f r < b) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a) :
    (hX.morseBrokenTrajectoryPairs p r a b).ncard = (hX.morseBrokenTrajectorySet p r).ncard := by
  -- Along a broken trajectory through `q`, the critical value `f q` lies between `b` and `a`.
  have hval : ∀ {q z₁ z₂ : M}, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 →
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 →
      z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q →
      z₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r →
      p ≠ q ∧ q ≠ r ∧ b < f q ∧ f q < a := by
    intro q z₁ z₂ hq hpq hqr hz₁ hz₂
    have hpq' : p ≠ q := by rintro rfl; omega
    have hqr' : q ≠ r := by rintro rfl; omega
    have h₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq' hz₁
    have h₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hqr' hz₂
    exact ⟨hpq', hqr', hcrit q hq (h₂.1.trans h₂.2) (h₁.1.trans h₁.2)⟩
  have hq (x : criticalPoints 𝓘(ℝ, E) f × M × M) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x.1 = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1 x.1.2
  -- The times at which the two components of a broken trajectory cross the levels `a` and `b`.
  have hcross (x : criticalPoints 𝓘(ℝ, E) f × M × M) (hx : x ∈ hX.morseBrokenTrajectorySet p r) :
      (∃ t, f (hX.flow t x.2.1) = a) ∧ ∃ t, f (hX.flow t x.2.2) = b := by
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hx
    rw [mem_morseTrajectorySlice] at hz₁ hz₂
    obtain ⟨hpq', hqr', hbq, hqa⟩ := hval (hq x) hpq hqr ⟨hz₁.1, hz₁.2.1⟩ ⟨hz₂.1, hz₂.2.1⟩
    exact ⟨(hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hpq'
      ⟨hz₁.1, hz₁.2.1⟩ hqa hap).exists, (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet
      hf hqr' ⟨hz₂.1, hz₂.2.1⟩ hrb hbq).exists⟩
  symm
  refine ncard_congr (fun x hx ↦ (hX.flow (hcross x hx).1.choose x.2.1,
      hX.flow (hcross x hx).2.choose x.2.2)) (fun x hx ↦ ?_) (fun x x' hx hx' hxx' ↦ ?_)
    fun y hy ↦ ?_
  · obtain ⟨hpq, hqr, hz₁, hz₂⟩ := id hx
    rw [mem_morseTrajectorySlice] at hz₁ hz₂
    exact (mem_morseBrokenTrajectoryPairs hX).2 ⟨x.1, hq x, hpq, hqr,
      hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ ⟨hz₁.1, hz₁.2.1⟩,
      (hcross x hx).1.choose_spec,
      hX.flow.isInvariant_unstableSet_inter_stableSet _ _ _ ⟨hz₂.1, hz₂.2.1⟩,
      (hcross x hx).2.choose_spec⟩
  · -- The intermediate critical point is the forward limit of the first component, and each
    -- component is the point of its orbit on its middle level.
    obtain ⟨hpq, hqr, hz₁, hz₂⟩ := id hx
    obtain ⟨-, -, hz₁', hz₂'⟩ := id hx'
    rw [mem_morseTrajectorySlice] at hz₁ hz₂ hz₁' hz₂'
    obtain ⟨hpq', hqr', -⟩ := hval (hq x) hpq hqr ⟨hz₁.1, hz₁.2.1⟩ ⟨hz₂.1, hz₂.2.1⟩
    simp only [Prod.mk.injEq] at hxx'
    have hqq : x.1 = x'.1 := by
      by_contra hne
      have h₁ : hX.flow (hcross x hx).1.choose x.2.1 ∈ hX.flow.stableSet x.1 :=
        (Flow.apply_mem_stableSet_iff _ _).2 hz₁.2.1
      have h₂ : hX.flow (hcross x' hx').1.choose x'.2.1 ∈ hX.flow.stableSet x'.1 :=
        (Flow.apply_mem_stableSet_iff _ _).2 hz₁'.2.1
      rw [hxx'.1] at h₁
      exact (Flow.disjoint_stableSet (Subtype.coe_ne_coe.2 hne)).notMem_of_mem_left h₁ h₂
    have hsame {z z' : M} {t t' : ℝ} {c d : M} (hcd : c ≠ d)
        (hz' : z' ∈ hX.flow.unstableSet c ∩ hX.flow.stableSet d) (hzz : f z = f z')
        (heq : hX.flow t z = hX.flow t' z') : z = z' := by
      have hz : z = hX.flow (t' - t) z' := by
        rw [sub_eq_add_neg, add_comm, Flow.map_add, ← heq, ← Flow.map_add, neg_add_cancel,
          Flow.map_zero_apply]
      rw [hz] at hzz ⊢
      exact flow_eq_self_of_apply_eq hf hcd hz' hzz
    refine Prod.ext hqq (Prod.ext ?_ ?_)
    · exact hsame hpq' ⟨hz₁'.1, hqq ▸ hz₁'.2.1⟩ (by rw [hz₁.2.2, hz₁'.2.2, hqq]) hxx'.1
    · exact hsame hqr' ⟨hqq ▸ hz₂'.1, hz₂'.2.1⟩ (by rw [hz₂.2.2, hz₂'.2.2, hqq]) hxx'.2
  · -- Flow the two points of a broken pair to the middle levels.
    obtain ⟨q, hq', hpq, hqr, hy₁, hya, hy₂, hyb⟩ := (mem_morseBrokenTrajectoryPairs hX).1 hy
    obtain ⟨hpq', hqr', -⟩ := hval hq' hpq hqr hy₁ hy₂
    have hm₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq' hy₁
    have hm₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hqr' hy₂
    obtain ⟨s₁, hs₁, -⟩ := hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hf
      hpq' hy₁
    obtain ⟨s₂, hs₂, -⟩ := hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hf
      hqr' hy₂
    have hx : (⟨q, mem_criticalPoints_iff_mfderiv_eq_zero.2 hq'⟩, hX.flow s₁ y.1,
        hX.flow s₂ y.2) ∈ hX.morseBrokenTrajectorySet p r :=
      ⟨hpq, hqr, (mem_morseTrajectorySlice hX).2
        ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hy₁.1, (Flow.apply_mem_stableSet_iff _ _).2 hy₁.2,
          hs₁⟩, (mem_morseTrajectorySlice hX).2
        ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hy₂.1, (Flow.apply_mem_stableSet_iff _ _).2 hy₂.2,
          hs₂⟩⟩
    refine ⟨_, hx, Prod.ext ?_ ?_⟩ <;> dsimp only
    · rw [← Flow.map_add]
      exact flow_eq_self_of_apply_eq hf hpq' hy₁
        (by rw [Flow.map_add, (hcross _ hx).1.choose_spec, hya])
    · rw [← Flow.map_add]
      exact flow_eq_self_of_apply_eq hf hqr' hy₂
        (by rw [Flow.map_add, (hcross _ hx).2.choose_spec, hyb])

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Finitely many broken trajectories.** Under the Morse–Smale condition, there are finitely
many broken index-two trajectories between two critical points. -/
theorem finite_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseBrokenTrajectorySet p r).Finite := by
  have := hf.finite_criticalPoints.to_subtype
  have hcrit := fun a : criticalPoints 𝓘(ℝ, E) f ↦ mem_criticalPoints_iff_mfderiv_eq_zero.1 a.2
  -- Sort the broken trajectories by their intermediate critical point `q`.
  refine ((toFinite {q : criticalPoints 𝓘(ℝ, E) f |
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1}).biUnion
    fun q hq ↦ ((h.finite_morseTrajectorySlice hf (hcrit p) (hcrit q) hq.1).prod
      (h.finite_morseTrajectorySlice hf (hcrit q) (hcrit r) hq.2)).image (Prod.mk q)).subset
    fun x hx ↦ mem_biUnion ⟨hx.1, hx.2.1⟩ ⟨x.2, ⟨hx.2.2.1, hx.2.2.2⟩, rfl⟩

/-- **`∂ ∘ ∂` counts broken trajectories.** The `r`-coefficient of the boundary of the boundary
of a critical point `p` is the number of broken index-two trajectories from `p` to `r`, modulo
two. -/
theorem morseBoundary_morseBoundary_single_apply (p r : criticalPoints 𝓘(ℝ, E) f) :
    h.morseBoundary hf (h.morseBoundary hf (Finsupp.single p 1)) r =
      ((hX.morseBrokenTrajectorySet p r).ncard : ZMod 2) := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  have hfin := h.finite_morseBrokenTrajectorySet hf p r
  -- Sort the broken trajectories by their intermediate critical point `q`.
  rw [morseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise fun x _ ↦ Finset.mem_univ x.1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The fiber over `q` is a copy of the pairs of trajectories through `q`.
  rw [morseBoundary_single_apply, one_mul, ← ncard_coe_finset, Finset.coe_filter,
    ← ncard_preimage_of_injective_subset_range (Prod.mk_right_injective q) ?_]
  swap
  · rintro ⟨_, z⟩ ⟨-, rfl⟩
    exact ⟨z, rfl⟩
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1
  · rw [h.morseBoundaryCoeff_eq_ncard hf hind.1, h.morseBoundaryCoeff_eq_ncard hf hind.2,
      ← Nat.cast_mul, ← ncard_prod]
    congr 2
    ext
    simp [hind]
  · rcases not_and_or.mp hind with hpq | hqr
    · simp [hpq]
    · simp [hqr]

/-- **`∂² = 0` reduces to counting broken trajectories.** The mod-two Morse boundary squares to
zero exactly when, between any two critical points, the number of broken index-two trajectories
is even. -/
theorem morseBoundary_comp_morseBoundary_eq_zero_iff :
    h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 ↔
      ∀ p r : criticalPoints 𝓘(ℝ, E) f, Even (hX.morseBrokenTrajectorySet p r).ncard := by
  simp_rw [← ZMod.natCast_eq_zero_iff_even, ← h.morseBoundary_morseBoundary_single_apply hf]
  constructor
  · intro h0 p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- Over `ZMod 2`, the boundary of `a • p` is `a` times the boundary of `p`.
    rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul]
    simp [h0]

/-- **`∂² = 0` from gluing charts.** Suppose that for all critical points `p` and `r` with
`ind p = ind r + 2` there are levels `f r < b < a < f p` enclosing every critical value strictly
between `f r` and `f p`, such that each broken trajectory pair on these levels lies in the closure
of the unbroken pairs, with a neighbourhood there homeomorphic to a half-open interval `[0, ε)` by a
homeomorphism sending `0` to it. Then the mod-two Morse boundary squares to zero: the compactified
spaces of index-two trajectories are compact one-manifolds whose boundary points are the broken
trajectories, which therefore come in pairs. -/
theorem morseBoundary_comp_morseBoundary_eq_zero_of_forall_exists_homeomorph_Ico
    (hglue : ∀ p r : M, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2 →
      ∃ a b : ℝ, f r < b ∧ b < a ∧ a < f p ∧
        (∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a) ∧
        ∀ y ∈ hX.morseBrokenTrajectoryPairs p r a b,
          ∃ hy : y ∈ closure (hX.morseTrajectoryPairs p r a b),
            ∃ N ∈ 𝓝 (⟨y, hy⟩ : closure (hX.morseTrajectoryPairs p r a b)),
              ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
                (e ⟨0, left_mem_Ico.2 hε⟩ : closure (hX.morseTrajectoryPairs p r a b)) =
                  ⟨y, hy⟩) :
    h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  refine (h.morseBoundary_comp_morseBoundary_eq_zero_iff hf).2 fun p r ↦ ?_
  have hp := mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2
  have hr := mem_criticalPoints_iff_mfderiv_eq_zero.1 r.2
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2
  · obtain ⟨a, b, hrb, hba, hap, hcrit, hgl⟩ := hglue p r hp hr hind
    rw [← ncard_morseBrokenTrajectoryPairs hX hdf hrb hap hcrit]
    exact h.even_ncard_morseBrokenTrajectoryPairs hf hp hr hind hrb hba hap hcrit hgl
  · -- Broken trajectories only join critical points whose indices differ by two.
    have hempty : hX.morseBrokenTrajectorySet p r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ hind (by rw [hx.1, hx.2.1])
    simp [hempty]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
