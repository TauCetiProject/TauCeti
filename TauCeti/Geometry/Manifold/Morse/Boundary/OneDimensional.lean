/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation
import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional

/-!
# The Morse boundary on a one-dimensional manifold

Let `f` be a Morse function on a compact connected boundaryless manifold `M` of dimension `1`, and
`X` a pseudo-gradient adapted to `f`. Every critical point has index `0` or `1`, so `X` is
Morse–Smale (`TauCeti.IsAdaptedPseudoGradient.isMorseSmale_of_finrank_eq_one`), and the Morse
boundary only sends critical points of index `1` to combinations of critical points of index `0`.
The unstable manifold of a critical point `p` of index `1` is `p` together with two trajectories,
each ending at a critical point of index `0`. This file shows that the two ends are different as
soon as `f` has a third critical point.

Indeed, suppose that both trajectories leaving `p` end at the same critical point `q`. In dimension
one the stable manifold of `q` is also `q` together with two trajectories, which must be these two,
so `W^u(p) ∪ W^s(q)` consists of `p`, `q` and the two trajectories between them. This set is open,
since `W^u(p)` and `W^s(q)` are open in dimension one. Its complement is the union of the open
unstable manifolds of the other critical points of index `1` and the open stable manifolds of the
other critical points of index `0`, so it is closed. On a connected manifold it is everything, and
`p` and `q` are the only critical points
(`TauCeti.IsAdaptedPseudoGradient.eq_or_eq_of_mem_unstableSet_inter_stableSet`).

Consequently, when `f` has a critical point other than `p` and the ends of its trajectories, there
is exactly one trajectory from `p` to each of two distinct critical points `q₀` and `q₁` of index
`0`, and none to any other critical point. So the mod-two Morse boundary of `p` is `q₀ + q₁`, and
the integral Morse boundary of `p` has coefficients `±1` at `q₀` and `q₁`, opposite once weighted by
the augmentation signs, and `0` elsewhere. On the circle with two maxima and two minima this
determines the Morse differential up to the orientations of the unstable manifolds.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_of_finrank_eq_one`: on a one-dimensional manifold every adapted pseudo-gradient is
  Morse–Smale.
* `eq_or_eq_of_mem_unstableSet_inter_stableSet`: if two different trajectories leaving a critical
  point `p` of index `1` both end at `q`, then `p` and `q` are the only critical points.
* `exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one`: otherwise there is exactly one
  trajectory from `p` to each of two distinct critical points of index `0`, and none to any other
  point.
* `IsMorseSmale.exists_ne_morseBoundary_single_of_finrank_eq_one`: the mod-two Morse boundary of
  `p` is the sum of these two critical points.
* `exists_ne_signedMorseBoundaryCoeff_of_finrank_eq_one`: the integral Morse boundary of `p` has
  coefficients `±1` at these two critical points, cancelling under the augmentation, and `0`
  elsewhere.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (the Morse complex of the circle in the continuation
  examples).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the circle).
-/

public section

open Function Module Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **Pseudo-gradients on a one-dimensional manifold are Morse–Smale.** On a manifold of dimension
`1` every critical point has index `0` or `1`, so the Morse–Smale condition holds for every
adapted pseudo-gradient. -/
theorem isMorseSmale_of_finrank_eq_one (hf : IsMorse 𝓘(ℝ, E) f) (hE : finrank ℝ E = 1) :
    hX.IsMorseSmale :=
  IsMorseSmale.of_manifoldMorseIndex_eq_zero_or_eq_finrank hf fun x _ ↦ by
    have : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℝ E := manifoldMorseIndex_le_finrank
    omega

/-- The **other basins** of a pair of critical points `p` and `q`: the union of the unstable
manifolds of the critical points of index `1` other than `p` and the stable manifolds of the
critical points of index `0` other than `q`. -/
private noncomputable def otherBasins (p q : M) : Set M :=
  (⋃ a ∈ {a | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f a = 1 ∧ a ≠ p},
    hX.flow.unstableSet a) ∪
  ⋃ b ∈ {b | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f b = 0 ∧ b ≠ q},
    hX.flow.stableSet b

/-- In dimension one, the other basins are open. -/
private theorem isOpen_otherBasins (hf : IsMorse 𝓘(ℝ, E) f) (hE : finrank ℝ E = 1) (p q : M) :
    IsOpen (hX.otherBasins p q) := by
  refine (isOpen_biUnion ?_).union (isOpen_biUnion ?_)
  · rintro a ⟨ha, ha1, -⟩
    exact hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf ha (ha1.trans hE.symm)
  · rintro b ⟨hb, hb0, -⟩
    exact hX.isOpen_stableSet_of_manifoldMorseIndex_eq_zero hb hb0

/-- In dimension one, every point lies on `W^u(p)`, on `W^s(q)` or in the other basins: it lies on
a trajectory from a critical point `a` to a critical point `b`, and no trajectory runs from a
critical point of index `0` to a different one of index `1`. -/
private theorem mem_or_mem_otherBasins (hf : IsMorse 𝓘(ℝ, E) f) (hE : finrank ℝ E = 1)
    (p q z : M) :
    z ∈ hX.flow.unstableSet p ∪ hX.flow.stableSet q ∨ z ∈ hX.otherBasins p q := by
  obtain ⟨a, ha, hza⟩ := hX.exists_tendsto_atBot hf z
  obtain ⟨b, hb, hzb⟩ := hX.exists_tendsto_atTop hf z
  have hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b :=
    ⟨Flow.mem_unstableSet.2 hza, Flow.mem_stableSet.2 hzb⟩
  have hale : manifoldMorseIndex 𝓘(ℝ, E) f a ≤ 1 := hE ▸ manifoldMorseIndex_le_finrank
  have hble : manifoldMorseIndex 𝓘(ℝ, E) f b ≤ 1 := hE ▸ manifoldMorseIndex_le_finrank
  by_cases hap : a = p
  · exact Or.inl (Or.inl (hap ▸ hz.1))
  by_cases hbq : b = q
  · exact Or.inl (Or.inr (hbq ▸ hz.2))
  by_cases ha1 : manifoldMorseIndex 𝓘(ℝ, E) f a = 1
  · exact Or.inr (Or.inl (mem_biUnion ⟨ha, ha1, hap⟩ hz.1))
  by_cases hb0 : manifoldMorseIndex 𝓘(ℝ, E) f b = 0
  · exact Or.inr (Or.inr (mem_biUnion ⟨hb, hb0, hbq⟩ hz.2))
  -- Otherwise `a` has index `0` and `b` index `1`, which no trajectory joins.
  have hab : a ≠ b := fun h ↦ by rw [h] at ha1; exact ha1 (by omega)
  have := hX.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet hf hab hz
    ((hX.isMorseSmale_of_finrank_eq_one hf hE).span_mtangentConeAt_sup_eq_top hz)
  omega

/-- If `W^u(p) - {p}` and `W^s(q) - {q}` are the same set `O` of points, for critical points `p`
of index `1` and `q` of index `0`, then `W^u(p) ∪ W^s(q)` does not meet the other basins: a point
of the unstable manifold of another critical point of index `1` cannot lie on `O`, nor be `q`, and
likewise on the stable side. -/
private theorem disjoint_otherBasins {p q : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hqi : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) {O : Set M}
    (hWu : hX.flow.unstableSet p = insert p O) (hWs : hX.flow.stableSet q = insert q O) :
    Disjoint (hX.flow.unstableSet p ∪ hX.flow.stableSet q) (hX.otherBasins p q) := by
  refine Set.disjoint_left.2 fun z hzS hzT ↦ ?_
  rcases hzT with hzT | hzT
  · obtain ⟨a, ⟨-, ha1, hap⟩, hza⟩ := mem_iUnion₂.1 hzT
    have hzu : z ∉ hX.flow.unstableSet p := Set.disjoint_left.1 (Flow.disjoint_unstableSet hap) hza
    -- So `z ∈ W^s(q) - W^u(p)`, which is `q`, on no unstable manifold of index `1`.
    have hzq : z = q := by
      have hzs : z ∈ insert q O := hWs ▸ hzS.resolve_left hzu
      exact hzs.resolve_right fun h ↦ hzu (hWu ▸ mem_insert_of_mem _ h)
    subst hzq
    rw [← Flow.eq_of_mem_unstableSet (hX.flow_apply_of_mfderiv_eq_zero hq) hza, hqi] at ha1
    exact zero_ne_one ha1
  · obtain ⟨b, ⟨-, hb0, hbq⟩, hzb⟩ := mem_iUnion₂.1 hzT
    have hzs : z ∉ hX.flow.stableSet q := Set.disjoint_left.1 (Flow.disjoint_stableSet hbq) hzb
    -- So `z ∈ W^u(p) - W^s(q)`, which is `p`, on no stable manifold of index `0`.
    have hzp : z = p := by
      have hzu : z ∈ insert p O := hWu ▸ hzS.resolve_right hzs
      exact hzu.resolve_right fun h ↦ hzs (hWs ▸ mem_insert_of_mem _ h)
    subst hzp
    rw [← Flow.eq_of_mem_stableSet (hX.flow_apply_of_mfderiv_eq_zero hp) hzb, hpi] at hb0
    exact one_ne_zero hb0

/-- If a set `W` is a point `x` together with two orbits, and two points of `W` other than `x` lie
on different orbits, then `W` is `x` together with their orbits. -/
private theorem eq_insert_orbit_union_orbit {W : Set M} {x y₁ y₂ : M}
    (hW : ∃ u₁ u₂, W = insert x (hX.flow.orbit u₁ ∪ hX.flow.orbit u₂)) (hy₁ : y₁ ∈ W \ {x})
    (hy₂ : y₂ ∈ W \ {x}) (hne : y₂ ∉ hX.flow.orbit y₁) :
    W = insert x (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
  obtain ⟨u₁, u₂, rfl⟩ := hW
  rw [hX.flow.orbit_union_orbit_eq ((mem_insert_iff.1 hy₁.1).resolve_left hy₁.2)
    ((mem_insert_iff.1 hy₂.1).resolve_left hy₂.2) hne]

variable [ConnectedSpace M]

/-- **A pair of trajectories with common ends fills a connected one-dimensional manifold.** Let `p`
be a critical point of index `1` and `q` one of index `0` on a compact connected manifold of
dimension `1`. If two points `y₁` and `y₂` on different orbits both lie on trajectories from `p`
to `q`, then `p` and `q` are the only critical points of `f`. -/
theorem eq_or_eq_of_mem_unstableSet_inter_stableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hE : finrank ℝ E = 1) {p q y₁ y₂ : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hqi : manifoldMorseIndex 𝓘(ℝ, E) f q = 0)
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hne : y₂ ∉ hX.flow.orbit y₁)
    {c : M} (hc : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0) : c = p ∨ c = q := by
  have hpq : p ≠ q := fun h ↦ by rw [h, hqi] at hpi; exact zero_ne_one hpi
  -- The points of `W^u(p) ∩ W^s(q)` are neither `p` nor `q`.
  have hmem {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
      y ∈ hX.flow.unstableSet p \ {p} ∧ y ∈ hX.flow.stableSet q \ {q} :=
    ⟨⟨hy.1, fun he ↦ hpq (Flow.eq_of_mem_stableSet (hX.flow_apply_of_mfderiv_eq_zero hp)
        (by rw [← mem_singleton_iff.1 he]; exact hy.2))⟩,
      ⟨hy.2, fun he ↦ hpq (Flow.eq_of_mem_unstableSet (hX.flow_apply_of_mfderiv_eq_zero hq)
        (by rw [← mem_singleton_iff.1 he]; exact hy.1)).symm⟩⟩
  -- So `W^u(p)` and `W^s(q)` are `p` and `q` together with the orbits of `y₁` and `y₂`.
  have hWu : hX.flow.unstableSet p = insert p (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
    obtain ⟨u₁, u₂, -, -, -, hW⟩ := hX.exists_unstableSet_eq_insert_union_orbit hf hp hpi
    exact hX.eq_insert_orbit_union_orbit ⟨u₁, u₂, hW⟩ (hmem hy₁).1 (hmem hy₂).1 hne
  have hWs : hX.flow.stableSet q = insert q (hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) := by
    obtain ⟨u₁, u₂, -, -, -, hW⟩ := hX.exists_stableSet_eq_insert_union_orbit hq (by omega)
    exact hX.eq_insert_orbit_union_orbit ⟨u₁, u₂, hW⟩ (hmem hy₁).2 (hmem hy₂).2 hne
  -- So `S = W^u(p) ∪ W^s(q)` is open, and its complement is the open union of the other basins.
  set S := hX.flow.unstableSet p ∪ hX.flow.stableSet q
  have hST : Sᶜ = hX.otherBasins p q :=
    Set.Subset.antisymm (fun z hz ↦ (hX.mem_or_mem_otherBasins hf hE p q z).resolve_left hz)
      (hX.disjoint_otherBasins hp hpi hq hqi hWu hWs).subset_compl_left
  have hclopen : IsClopen S :=
    ⟨isOpen_compl_iff.1 (hST ▸ hX.isOpen_otherBasins hf hE p q),
      (hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf hp (hpi.trans hE.symm)).union
        (hX.isOpen_stableSet_of_manifoldMorseIndex_eq_zero hq hqi)⟩
  -- On a connected manifold the nonempty clopen set `S` is everything.
  have huniv : S = univ := (isClopen_iff.1 hclopen).resolve_left
    (Nonempty.ne_empty ⟨p, Or.inl (Flow.self_mem_unstableSet_iff.2
      (hX.flow_apply_of_mfderiv_eq_zero hp))⟩)
  rcases (huniv ▸ mem_univ c : c ∈ S) with hcS | hcS
  · exact Or.inl (Flow.eq_of_mem_unstableSet (hX.flow_apply_of_mfderiv_eq_zero hc) hcS)
  · exact Or.inr (Flow.eq_of_mem_stableSet (hX.flow_apply_of_mfderiv_eq_zero hc) hcS)

/-- **The two trajectories leaving a maximum end at two different minima.** Let `p` be a critical
point of index `1` on a compact connected manifold of dimension `1`, and suppose that `f` has a
critical point `c` other than `p` whose index is not `0`. Then there are two distinct critical
points `q₀` and `q₁` of index `0` such that there is exactly one trajectory from `p` to each of
them, and none from `p` to any other point but `p` itself. -/
theorem exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one (hf : IsMorse 𝓘(ℝ, E) f)
    (hE : finrank ℝ E = 1) {p c : criticalPoints 𝓘(ℝ, E) f}
    (hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) (hcp : c ≠ p)
    (hci : manifoldMorseIndex 𝓘(ℝ, E) f c ≠ 0) :
    ∃ q₀ q₁ : criticalPoints 𝓘(ℝ, E) f, q₀ ≠ q₁ ∧ manifoldMorseIndex 𝓘(ℝ, E) f q₀ = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q₁ = 0 ∧
      (∃ y₀, hX.morseTrajectorySlice p q₀ = {y₀}) ∧ (∃ y₁, hX.morseTrajectorySlice p q₁ = {y₁}) ∧
      ∀ q : M, q ≠ p → q ≠ q₀ → q ≠ q₁ → hX.morseTrajectorySlice p q = ∅ := by
  have hp := mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property
  have h := hX.isMorseSmale_of_finrank_eq_one hf hE
  obtain ⟨w, b, hb, hwmem, hw1, -, hslice⟩ :=
    h.exists_morseTrajectorySlice_eq_image_of_morseIndex_eq_one hf hp hpi
  -- The two ends differ: otherwise `p` and `b 0` would be the only critical points.
  have hb01 : b 0 ≠ b 1 := by
    intro he
    rcases hX.eq_or_eq_of_mem_unstableSet_inter_stableSet hf hE hp hpi (hb 0).1 (hb 0).2
      (hwmem 0) (he ▸ hwmem 1) hw1 (mem_criticalPoints_iff_mfderiv_eq_zero.1 c.property)
      with h' | h'
    · exact hcp (Subtype.ext h')
    · exact hci (h' ▸ (hb 0).2)
  have hbp (i : Fin 2) : (p : M) ≠ b i := fun he ↦ by
    have := (hb i).2
    rw [← he, hpi] at this
    exact one_ne_zero this
  have hslice_eq (i : Fin 2) : hX.morseTrajectorySlice p (b i) = {w i} := by
    rw [hslice _ (hbp i)]
    fin_cases i
    · simp [show {j : Fin 2 | b j = b 0} = {0} from
        Set.ext fun j ↦ by fin_cases j <;> simp [hb01.symm]]
    · simp [show {j : Fin 2 | b j = b 1} = {1} from
        Set.ext fun j ↦ by fin_cases j <;> simp [hb01]]
  refine ⟨⟨b 0, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hb 0).1⟩,
    ⟨b 1, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hb 1).1⟩,
    fun he ↦ hb01 (congrArg Subtype.val he), (hb 0).2, (hb 1).2, ⟨w 0, hslice_eq 0⟩,
    ⟨w 1, hslice_eq 1⟩, fun q hqp hq₀ hq₁ ↦ ?_⟩
  rw [hslice q hqp.symm]
  refine Set.image_eq_empty.2 (Set.eq_empty_of_forall_notMem fun j hj ↦ ?_)
  fin_cases j
  · exact hq₀ hj.symm
  · exact hq₁ hj.symm

namespace IsMorseSmale

variable {hX} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **The mod-two Morse boundary of a maximum on a one-dimensional manifold.** Let `p` be a
critical point of index `1` on a compact connected manifold of dimension `1`, and suppose that `f`
has a critical point `c` other than `p` whose index is not `0`. Then the mod-two Morse boundary of
`p` is the sum of two distinct critical points of index `0`. -/
theorem exists_ne_morseBoundary_single_of_finrank_eq_one (hE : finrank ℝ E = 1)
    {p c : criticalPoints 𝓘(ℝ, E) f} (hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) (hcp : c ≠ p)
    (hci : manifoldMorseIndex 𝓘(ℝ, E) f c ≠ 0) :
    ∃ q₀ q₁ : criticalPoints 𝓘(ℝ, E) f, q₀ ≠ q₁ ∧ manifoldMorseIndex 𝓘(ℝ, E) f q₀ = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q₁ = 0 ∧
      h.morseBoundary hf (Finsupp.single p 1) = Finsupp.single q₀ 1 + Finsupp.single q₁ 1 := by
  classical
  obtain ⟨q₀, q₁, hQ, hq₀, hq₁, ⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩, hempty⟩ :=
    hX.exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one hf hE hpi hcp hci
  have hind (q : criticalPoints 𝓘(ℝ, E) f) (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) :
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := by omega
  refine ⟨q₀, q₁, hQ, hq₀, hq₁, ?_⟩
  ext q
  rw [morseBoundary_single_apply, one_mul, Finsupp.add_apply]
  by_cases h₀ : q = q₀
  · rw [h₀, h.morseBoundaryCoeff_eq_ncard hf (hind _ hq₀), hy₀]
    simp [hQ]
  by_cases h₁ : q = q₁
  · rw [h₁, h.morseBoundaryCoeff_eq_ncard hf (hind _ hq₁), hy₁]
    simp [hQ.symm]
  rw [Finsupp.single_eq_of_ne h₀, Finsupp.single_eq_of_ne h₁, add_zero]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
  · have hqp : (q : M) ≠ p := fun he ↦ by rw [Subtype.ext he, hpi] at hq; exact one_ne_zero hq
    rw [h.morseBoundaryCoeff_eq_ncard hf (hind q hq),
      hempty q hqp (fun he ↦ h₀ (Subtype.ext he)) (fun he ↦ h₁ (Subtype.ext he)), ncard_empty,
      Nat.cast_zero]
  · exact h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf (by omega)

end IsMorseSmale

/-- **The integral Morse boundary of a maximum on a one-dimensional manifold.** Let `p` be a
critical point of index `1` on a compact connected manifold of dimension `1`, and suppose that `f`
has a critical point `c` other than `p` whose index is not `0`. For every choice of orientations,
the integral Morse boundary of `p` has coefficients `±1` at two distinct critical points `q₀` and
`q₁` of index `0` and `0` elsewhere, and the two coefficients cancel once weighted by the
augmentation signs: the two trajectories leave `p` in opposite directions. -/
theorem exists_ne_signedMorseBoundaryCoeff_of_finrank_eq_one (hf : IsMorse 𝓘(ℝ, E) f)
    (hE : finrank ℝ E = 1) (𝔬 : MorseOrientation f X) {p c : criticalPoints 𝓘(ℝ, E) f}
    (hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) (hcp : c ≠ p)
    (hci : manifoldMorseIndex 𝓘(ℝ, E) f c ≠ 0) :
    ∃ q₀ q₁ : criticalPoints 𝓘(ℝ, E) f, q₀ ≠ q₁ ∧ manifoldMorseIndex 𝓘(ℝ, E) f q₀ = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q₁ = 0 ∧
      (hX.signedMorseBoundaryCoeff 𝔬 p q₀ = 1 ∨ hX.signedMorseBoundaryCoeff 𝔬 p q₀ = -1) ∧
      𝔬.augmentationSign q₁ * hX.signedMorseBoundaryCoeff 𝔬 p q₁ =
        -(𝔬.augmentationSign q₀ * hX.signedMorseBoundaryCoeff 𝔬 p q₀) ∧
      ∀ q, q ≠ q₀ → q ≠ q₁ → hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  classical
  have h := hX.isMorseSmale_of_finrank_eq_one hf hE
  obtain ⟨q₀, q₁, hQ, hq₀, hq₁, ⟨y₀, hy₀⟩, -, hempty⟩ :=
    hX.exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one hf hE hpi hcp hci
  -- Away from `q₀` and `q₁` there is no trajectory, so the coefficient vanishes.
  have hzero (q : criticalPoints 𝓘(ℝ, E) f) (h₀ : q ≠ q₀) (h₁ : q ≠ q₁) :
      hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
    by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
    · have hqp : (q : M) ≠ p := fun he ↦ by rw [Subtype.ext he] at hpq; omega
      rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def,
        hempty q hqp (fun he ↦ h₀ (Subtype.ext he)) (fun he ↦ h₁ (Subtype.ext he)),
        finsum_mem_empty]
    · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq
  -- At `q₀` there is a single trajectory, of sign `±1`.
  have hpq₀ : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q₀ + 1 := by
    rw [hpi, hq₀]
  have hsign : hX.signedMorseBoundaryCoeff 𝔬 p q₀ = 1 ∨
      hX.signedMorseBoundaryCoeff 𝔬 p q₀ = -1 := by
    have hmem : y₀ ∈ hX.morseTrajectorySlice p q₀ := hy₀ ▸ mem_singleton y₀
    rw [hX.mem_morseTrajectorySlice] at hmem
    rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq₀, signedTrajectoryCount_def, hy₀,
      finsum_mem_singleton]
    exact trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q₀)
      h hf ⟨hmem.1, hmem.2.1⟩
  -- The weighted coefficients add up to zero.
  have hsum := h.finsum_augmentationSign_mul_signedMorseBoundaryCoeff hf 𝔬 p
  rw [finsum_eq_sum_of_support_subset (s := {q₀, q₁}) _ fun q hq ↦ by
      by_contra hmem
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
        not_or] at hmem
      exact hq (by simp [hzero q hmem.1 hmem.2]),
    Finset.sum_pair hQ] at hsum
  exact ⟨q₀, q₁, hQ, hq₀, hq₁, hsign, eq_neg_of_add_eq_zero_right hsum, hzero⟩

end IsAdaptedPseudoGradient

end TauCeti
