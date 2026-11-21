/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The augmentation and the fundamental cycle of the mod-two Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` an
adapted pseudo-gradient satisfying the Morse–Smale condition. This file computes the mod-two Morse
boundary `∂` in its lowest and highest degrees.

* **The augmentation.** The augmentation `ε` of the mod-two Morse chains adds up the coefficients
  of the critical points of index `0`. It vanishes on boundaries: `ε ∘ ∂ = 0`. Indeed, the unstable
  manifold of a critical point of index `1` consists of two trajectories, and under the Morse–Smale
  condition each of them ends at a critical point of index `0`; so the boundary of an index-one
  critical point has an even number of terms, counted with multiplicity.
* **The fundamental cycle.** The mod-two fundamental chain `[M]`, the sum of the critical points
  of index `n`, is a cycle: `∂ [M] = 0`. Dually, the stable manifold of a critical point of index
  `n - 1` consists of two trajectories, each starting at a critical point of index `n`.

The special case of a single critical point of index `0` or of index `n`, and the resulting
vanishing of the mod-two Morse boundary on a closed surface with one minimum and one maximum, is
in `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_eq_zero_of_finrank_eq_two`.

These identities do not use `∂ ∘ ∂ = 0`, which needs the gluing of index-two trajectories.

## Main declarations

* `TauCeti.morseAugmentation`: the augmentation of the mod-two Morse chains.
* `TauCeti.morseFundamentalChain`: the sum of the critical points of top index.
* In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`,
  `exists_morseTrajectorySlice_eq_image_of_morseIndex_eq_one`: the trajectories leaving a critical
  point of index `1` are the crossings of two orbits, and dually
  `exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank` for the trajectories reaching a
  critical point of index `n - 1`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseAugmentation_comp_morseBoundary`:
  `ε ∘ ∂ = 0`.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_morseFundamentalChain`:
  `∂ [M] = 0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, its homology in degree `0`, and its computation for the torus).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

variable (f) in
/-- The **augmentation** of the mod-two Morse chains of `f`: the sum of the coefficients of the
critical points of Morse index `0`. -/
noncomputable def morseAugmentation : (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) fun p ↦
    if manifoldMorseIndex 𝓘(ℝ, E) f p = 0 then 1 else 0

/-- The augmentation of a chain `c` is the sum of its coefficients at the critical points of
index `0`. -/
theorem morseAugmentation_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    morseAugmentation f c =
      c.sum fun p a ↦ if manifoldMorseIndex 𝓘(ℝ, E) f p = 0 then a else 0 := by
  simp [morseAugmentation, Finsupp.linearCombination_apply]

/-- The augmentation of `a • p` is `a` when `p` has index `0`, and `0` otherwise. -/
@[simp]
theorem morseAugmentation_single (p : criticalPoints 𝓘(ℝ, E) f) (a : ZMod 2) :
    morseAugmentation f (Finsupp.single p a) =
      if manifoldMorseIndex 𝓘(ℝ, E) f p = 0 then a else 0 := by
  simp [morseAugmentation]

/-- A point of `M` lies in the image of the finite set of critical points of index `k` exactly when
it is a critical point of index `k`. -/
private theorem mem_map_filter_manifoldMorseIndex_iff [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    {k : ℕ} {x : M} :
    x ∈ (Finset.univ.filter fun p : criticalPoints 𝓘(ℝ, E) f ↦
      manifoldMorseIndex 𝓘(ℝ, E) f p = k).map (Embedding.subtype _) ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f x = k := by
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Embedding.coe_subtype]
  refine ⟨?_, fun ⟨hx, hxk⟩ ↦ ⟨⟨x, mem_criticalPoints_iff_mfderiv_eq_zero.2 hx⟩, hxk, rfl⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property, hp⟩

/-- A sum of mod-two coefficients over a finite set `S` of critical points vanishes when each
coefficient counts a set `s p` and these counts add up to `2`. -/
private theorem sum_eq_zero_of_sum_ncard_eq_two {S : Finset (criticalPoints 𝓘(ℝ, E) f)}
    {c : criticalPoints 𝓘(ℝ, E) f → ZMod 2} {s : M → Set M}
    (hc : ∀ p ∈ S, c p = (s p).ncard)
    (hcount : ∑ x ∈ S.map (Embedding.subtype _), (s x).ncard = 2) :
    ∑ p ∈ S, c p = 0 := by
  rw [Finset.sum_map] at hcount
  simp only [Embedding.coe_subtype] at hcount
  rw [Finset.sum_congr rfl hc, ← Nat.cast_sum, hcount]
  exact ZMod.natCast_self 2

/-- If the sets `s x` for `x ∈ T` are the images under an injective `w : Fin 2 → β` of the
fibres of a labelling `a : Fin 2 → α` with values in `T`, their sizes add up to `2`. -/
private theorem sum_ncard_eq_two_of_eq_image {α β : Type*} {T : Finset α} {s : α → Set β}
    {w : Fin 2 → β} {a : Fin 2 → α}
    (hwinj : Injective w) (ha : ∀ i, a i ∈ T) (hs : ∀ x ∈ T, s x = w '' {i | a i = x}) :
    ∑ x ∈ T, (s x).ncard = 2 := by
  classical
  calc ∑ x ∈ T, (s x).ncard
      = ∑ x ∈ T, (Finset.univ.filter fun i ↦ a i = x).card :=
        Finset.sum_congr rfl fun x hx ↦ by
          rw [hs x hx, ncard_image_of_injective _ hwinj, ← ncard_coe_finset, Finset.coe_filter]
          simp
    _ = (Finset.univ : Finset (Fin 2)).card :=
        (Finset.card_eq_sum_card_fiberwise fun i _ ↦ ha i).symm
    _ = 2 := by simp

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- The **mod-two fundamental chain** of a Morse function on a compact manifold of dimension `n`:
the sum of its critical points of Morse index `n`. -/
noncomputable def morseFundamentalChain (hf : IsMorse 𝓘(ℝ, E) f) :
    criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2 :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.ofSupportFinite
    (fun p ↦ if manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E then 1 else 0) (toFinite _)

/-- The coefficient of a critical point in the fundamental chain is `1` when it has top index, and
`0` otherwise. -/
@[simp]
theorem morseFundamentalChain_apply (hf : IsMorse 𝓘(ℝ, E) f) (p : criticalPoints 𝓘(ℝ, E) f) :
    morseFundamentalChain hf p = if manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E then 1 else 0 := by
  rw [morseFundamentalChain, Finsupp.ofSupportFinite_coe]

variable [FiniteDimensional ℝ E] [T2Space M] {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **The trajectories reaching a critical point of index `n - 1`.** If `q` is a critical point of
index `n - 1`, there are two points `w 0` and `w 1` on different orbits, on trajectories to `q` from
critical points `a 0` and `a 1` of index `n`, such that for every point `p ≠ q` the trajectories
from `p` to `q` are the points `w i` with `a i = p`. -/
theorem exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank {q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E) :
    ∃ w a : Fin 2 → M,
      (∀ i, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (a i) = 0 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f (a i) = finrank ℝ E) ∧
      (∀ i, w i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q) ∧
      w 1 ∉ hX.flow.orbit (w 0) ∧ Injective w ∧
      ∀ p, p ≠ q → hX.morseTrajectorySlice p q = w '' {i | a i = p} := by
  obtain ⟨y₁, y₂, hy₁, hy₂, hdisj, hW⟩ := hX.exists_stableSet_eq_insert_union_orbit hq hind
  set y : Fin 2 → M := ![y₁, y₂] with hy
  have hW' : hX.flow.stableSet q = insert q (⋃ i, hX.flow.orbit (y i)) := by
    ext w
    simp [hW, hy, Fin.exists_fin_two]
  have hyq (i : Fin 2) : y i ≠ q := by fin_cases i <;> simp [hy, hy₁, hy₂]
  -- Each orbit starts at a critical point `a i`, which has index `n` by the Morse–Smale condition.
  choose a ha hlim using fun i ↦ hX.exists_tendsto_atBot hf (y i)
  have hmem (i : Fin 2) : y i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q :=
    ⟨Flow.mem_unstableSet.2 (hlim i),
      hW' ▸ mem_insert_of_mem _ (mem_iUnion.2 ⟨i, Flow.mem_orbit_self _ _⟩)⟩
  have haq (i : Fin 2) : a i ≠ q := fun he ↦
    hyq i (hX.eq_of_mem_unstableSet_inter_stableSet (he ▸ hmem i))
  have hind' (i : Fin 2) : manifoldMorseIndex 𝓘(ℝ, E) f (a i) = finrank ℝ E := by
    refine le_antisymm manifoldMorseIndex_le_finrank ?_
    have := hX.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet hf (haq i)
      (hmem i) (h.span_mtangentConeAt_sup_eq_top (hmem i))
    omega
  -- The `i`-th orbit crosses the middle level between `a i` and `q` at the time `τ i`.
  choose τ hτ using fun i ↦
    (hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet (haq i) (hmem i)).exists
  -- The crossings lie on the disjoint orbits of `y₁` and `y₂`.
  have hw1 : hX.flow (τ 1) (y 1) ∉ hX.flow.orbit (hX.flow (τ 0) (y 0)) := by
    rw [Flow.orbit_apply]
    exact fun hw ↦ hdisj.ne_of_mem hw (hX.flow.mem_orbit _ (τ 1)) rfl
  have hwinj : Injective fun i ↦ hX.flow (τ i) (y i) := by
    have hne := hdisj.ne_of_mem (hX.flow.mem_orbit _ (τ 0)) (hX.flow.mem_orbit _ (τ 1))
    intro i j hij
    fin_cases i <;> fin_cases j
    exacts [rfl, (hne hij).elim, (hne hij.symm).elim, rfl]
  refine ⟨_, a, fun i ↦ ⟨ha i, hind' i⟩,
    fun i ↦ ⟨(Flow.apply_mem_unstableSet_iff _ _).2 (hmem i).1,
      (Flow.apply_mem_stableSet_iff _ _).2 (hmem i).2⟩, hw1, hwinj, fun p hpq ↦ ?_⟩
  -- The trajectories from `p` to `q` are the crossings of the orbits starting at `p`.
  exact hX.morseTrajectorySlice_eq_image_of_stableSet_subset hpq hW'.subset hmem hτ

/-- **The trajectories leaving a critical point of index `1`.** If `p` is a critical point of index
`1`, there are two points `w 0` and `w 1` on different orbits, on trajectories from `p` to critical
points `b 0` and `b 1` of index `0`, such that for every point `q ≠ p` the trajectories from `p`
to `q` are the points `w i` with `b i = q`. -/
theorem exists_morseTrajectorySlice_eq_image_of_morseIndex_eq_one {p : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) :
    ∃ w b : Fin 2 → M,
      (∀ i, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (b i) = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f (b i) = 0) ∧
      (∀ i, w i ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet (b i)) ∧
      w 1 ∉ hX.flow.orbit (w 0) ∧ Injective w ∧
      ∀ q, p ≠ q → hX.morseTrajectorySlice p q = w '' {i | b i = q} := by
  -- Reversing the flow turns the trajectories leaving `p` into those of `-X` reaching `p`.
  have hsum (x : M) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :=
    (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
      ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  obtain ⟨w, b, hb, hmem, hw1, hwinj, hslice⟩ :=
    exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank (h.neg hf) hf.neg
      (mfderiv_neg_eq_zero_iff.2 hp) (by have := hsum p hp; omega)
  refine ⟨w, b, fun i ↦ ?_, fun i ↦ ?_, ?_, hwinj, fun q hpq ↦ ?_⟩
  · have hbi := mfderiv_neg_eq_zero_iff.1 (hb i).1
    have := hsum _ hbi
    exact ⟨hbi, by have := (hb i).2; omega⟩
  · simpa only [hX.neg_flow hf, Flow.unstableSet_reverse, Flow.stableSet_reverse,
      inter_comm] using hmem i
  · simpa only [hX.neg_flow hf, Flow.orbit_reverse] using hw1
  · rw [← hX.neg_morseTrajectorySlice hf, hslice q hpq.symm]

/-- **Two trajectories reach a critical point of index `n - 1`.** Summed over the critical points
`p` of index `n`, the numbers of trajectories from `p` to a critical point `q` of index `n - 1` add
up to `2`. Here `T` is the finite set of critical points of index `n`. -/
private theorem sum_ncard_morseTrajectorySlice_of_add_one_eq_finrank {q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E) {T : Finset M}
    (hT : ∀ p, p ∈ T ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    ∑ p ∈ T, (hX.morseTrajectorySlice p q).ncard = 2 := by
  obtain ⟨w, a, ha, -, -, hwinj, hslice⟩ :=
    exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank h hf hq hind
  refine sum_ncard_eq_two_of_eq_image hwinj (fun i ↦ (hT _).2 (ha i)) fun p hp ↦ hslice p ?_
  exact ne_of_apply_ne (manifoldMorseIndex 𝓘(ℝ, E) f) (by have := ((hT p).1 hp).2; omega)

/-- **Two trajectories leave a critical point of index `1`.** Summed over the critical points `q`
of index `0`, the numbers of trajectories from a critical point `p` of index `1` to `q` add up to
`2`. Here `T` is the finite set of critical points of index `0`. -/
private theorem sum_ncard_morseTrajectorySlice_of_eq_one {p : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    {T : Finset M}
    (hT : ∀ q, q ∈ T ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f q = 0) :
    ∑ q ∈ T, (hX.morseTrajectorySlice p q).ncard = 2 := by
  obtain ⟨w, b, hb, -, -, hwinj, hslice⟩ :=
    exists_morseTrajectorySlice_eq_image_of_morseIndex_eq_one h hf hp hind
  refine sum_ncard_eq_two_of_eq_image hwinj (fun i ↦ (hT _).2 (hb i)) fun q hq ↦ hslice q ?_
  exact ne_of_apply_ne (manifoldMorseIndex 𝓘(ℝ, E) f) (by rw [hind, ((hT q).1 hq).2]; omega)

/-- The coefficients of the boundary of the critical points of index `n` at a critical point `q`
add up to zero. -/
private theorem sum_morseBoundaryCoeff_of_eq_finrank [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (q : criticalPoints 𝓘(ℝ, E) f) :
    ∑ p ∈ Finset.univ.filter (fun p : criticalPoints 𝓘(ℝ, E) f ↦
      manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E), h.morseBoundaryCoeff hf p q = 0 := by
  classical
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E
  · exact sum_eq_zero_of_sum_ncard_eq_two (s := fun x ↦ hX.morseTrajectorySlice x q)
      (fun p hp ↦ h.morseBoundaryCoeff_eq_ncard hf ((Finset.mem_filter.1 hp).2.trans hq.symm))
      (sum_ncard_morseTrajectorySlice_of_add_one_eq_finrank h hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hq
        fun _ ↦ mem_map_filter_manifoldMorseIndex_iff)
  · exact Finset.sum_eq_zero fun p hp ↦ h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf
      (by rw [(Finset.mem_filter.1 hp).2]; omega)

/-- The coefficients of the boundary of a critical point `p` at the critical points of index `0`
add up to zero. -/
private theorem sum_morseBoundaryCoeff_of_eq_zero [Fintype (criticalPoints 𝓘(ℝ, E) f)]
    (p : criticalPoints 𝓘(ℝ, E) f) :
    ∑ q ∈ Finset.univ.filter (fun q : criticalPoints 𝓘(ℝ, E) f ↦
      manifoldMorseIndex 𝓘(ℝ, E) f q = 0), h.morseBoundaryCoeff hf p q = 0 := by
  classical
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1
  · exact sum_eq_zero_of_sum_ncard_eq_two (s := hX.morseTrajectorySlice p)
      (fun q hq ↦ h.morseBoundaryCoeff_eq_ncard hf (by rw [hp, (Finset.mem_filter.1 hq).2]))
      (sum_ncard_morseTrajectorySlice_of_eq_one h hf
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) hp
        fun _ ↦ mem_map_filter_manifoldMorseIndex_iff)
  · exact Finset.sum_eq_zero fun q hq ↦ h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf
      (by rw [(Finset.mem_filter.1 hq).2]; exact hp)

/-- **The augmentation vanishes on boundaries.** For a Morse–Smale pseudo-gradient, the
augmentation of the mod-two Morse boundary of every chain is zero: `ε ∘ ∂ = 0`. -/
theorem morseAugmentation_comp_morseBoundary :
    morseAugmentation f ∘ₗ h.morseBoundary hf = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  refine Finsupp.lhom_ext fun p a ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, morseAugmentation_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  simp only [morseBoundary_single_apply, ← Finset.sum_filter, ← Finset.mul_sum,
    sum_morseBoundaryCoeff_of_eq_zero h hf p, mul_zero]

/-- **The augmentation of a boundary is zero.** The applied form of `ε ∘ ∂ = 0`. -/
@[simp]
theorem morseAugmentation_morseBoundary (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    morseAugmentation f (h.morseBoundary hf c) = 0 := by
  rw [← LinearMap.comp_apply, h.morseAugmentation_comp_morseBoundary hf, LinearMap.zero_apply]

/-- **The fundamental chain is a cycle.** For a Morse–Smale pseudo-gradient, the mod-two Morse
boundary of the sum of the critical points of top index is zero: `∂ [M] = 0`. -/
@[simp]
theorem morseBoundary_morseFundamentalChain :
    h.morseBoundary hf (morseFundamentalChain hf) = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  ext q
  rw [morseBoundary_apply, Finsupp.zero_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [morseFundamentalChain_apply, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    sum_morseBoundaryCoeff_of_eq_finrank h hf q]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
