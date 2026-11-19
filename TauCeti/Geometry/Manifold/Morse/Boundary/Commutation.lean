/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation

/-!
# The continuation map commutes with the Morse boundaries exactly when broken continuation
trajectories come in pairs

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them, and let `V` be a vector field on `M × ℝ` along
which the mod-two continuation map `Φ = TauCeti.morseContinuationMap f₀ hf₁ V` counts the
trajectories from `(p, 0)` to `(q, 1)` between critical points of equal index. For `Φ` to induce
a map on Morse homology it must be a chain map, `∂₁ ∘ Φ = Φ ∘ ∂₀`. This file proves the algebraic
half of that statement and packages its consequence as a morphism of Morse chain complexes.

For a critical point `p` of `f₀` and a critical point `r` of `f₁` with `ind p = ind r + 1`, a
*broken continuation trajectory* from `p` to `r` breaks at one of the two ends of the slab:

* at the source (`TauCeti.morseSourceBrokenContinuationSet`): a trajectory of `X₀` from `p` to a
  critical point `p'` of `f₀` of index `ind r`, followed by a continuation trajectory from
  `(p', 0)` to `(r, 1)`;
* at the target (`TauCeti.morseTargetBrokenContinuationSet`): a continuation trajectory from
  `(p, 0)` to `(q', 1)` for a critical point `q'` of `f₁` of index `ind p`, followed by a
  trajectory of `X₁` from `q'` to `r`.

Each component is recorded by its point on its middle level, so the broken trajectories form sets
of triples `(p', z₁, z₂)` and `(q', z₁, z₂)`. When these sets are finite, the `r`-coefficient of
`Φ (∂₀ p)` is the number of broken trajectories at the source modulo two
(`TauCeti.morseContinuationMap_morseBoundary_single_apply`), and that of `∂₁ (Φ p)` is the number
at the target (`TauCeti.morseBoundary_morseContinuationMap_single_apply`). Both sets are finite
when the continuation slices between critical points of equal index are
(`TauCeti.finite_morseSourceBrokenContinuationSet`,
`TauCeti.finite_morseTargetBrokenContinuationSet`). So, under that finiteness, `Φ` commutes with
the Morse boundaries exactly when, between any two critical points, the broken continuation
trajectories at the two ends are evenly many in total
(`TauCeti.morseBoundary_comp_morseContinuationMap_eq_iff`). The geometric half, that the broken
continuation trajectories are the ends of the compact one-dimensional spaces of continuation
trajectories between critical points whose indices differ by one, needs the compactification and
gluing of those spaces in the slab, and is not proved here.

A continuation map commuting with the boundaries preserves the Morse index, so it restricts to the
graded chains (`TauCeti.morseContinuationMapAt`, `TauCeti.mapDomain_morseContinuationMapAt`) and
defines a morphism of mod-two Morse chain complexes (`TauCeti.morseContinuationHom`), hence a map
on mod-two Morse homology. For the constant path, the continuation map is the identity, so it
commutes with the boundary and its morphism is the identity of the Morse complex
(`TauCeti.morseContinuationHom_constantContinuationField`). Its continuation slices are finite, so
the criterion above shows that the broken continuation trajectories of a constant path come in
pairs (`TauCeti.even_ncard_morseSourceBrokenContinuationSet_add_ncard_constantContinuationField`).

## Main declarations

* `TauCeti.morseSourceBrokenContinuationSet`, `TauCeti.morseTargetBrokenContinuationSet`: the
  broken continuation trajectories at the source and at the target.
* `TauCeti.morseContinuationMap_morseBoundary_single_apply`,
  `TauCeti.morseBoundary_morseContinuationMap_single_apply`: the coefficients of `Φ ∘ ∂₀` and
  `∂₁ ∘ Φ` count broken continuation trajectories modulo two.
* `TauCeti.morseBoundary_comp_morseContinuationMap_eq_iff`: `∂₁ ∘ Φ = Φ ∘ ∂₀` exactly when the
  broken continuation trajectories between any two critical points are evenly many.
* `TauCeti.morseContinuationMapAt`: the continuation map between the chains of index `n`.
* `TauCeti.morseContinuationHom`: a continuation map commuting with the boundaries, as a morphism
  of mod-two Morse chain complexes.
* `TauCeti.morseContinuationHom_constantContinuationField`: the morphism of a constant path is the
  identity.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional continuation trajectory spaces).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-! ### Broken continuation trajectories -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

variable (f₁ V) in
/-- The continuation trajectories from `p` to `r` broken at the source: triples `(p', z₁, z₂)` of
a critical point `p'` of `f₀` whose Morse index lies one below that of `p` and equals that of `r`,
a point `z₁` on the middle-level slice of the trajectories of `X₀` from `p` to `p'`, and a point
`z₂` on the middle level `t = 1 / 2` of the trajectories of `V` from `(p', 0)` to `(r, 1)`. -/
def morseSourceBrokenContinuationSet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f₀ × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseContinuationSlice V x.1 r}

/-- Membership in the set of continuation trajectories broken at the source. -/
@[simp]
theorem mem_morseSourceBrokenContinuationSet {p r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M} :
    x ∈ morseSourceBrokenContinuationSet f₁ V hX₀ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ morseContinuationSlice V x.1 r :=
  Iff.rfl

variable (f₀ V) in
/-- The continuation trajectories from `p` to `r` broken at the target: triples `(q', z₁, z₂)` of
a critical point `q'` of `f₁` whose Morse index equals that of `p` and lies one above that of `r`,
a point `z₁` on the middle level `t = 1 / 2` of the trajectories of `V` from `(p, 0)` to
`(q', 1)`, and a point `z₂` on the middle-level slice of the trajectories of `X₁` from `q'` to
`r`. -/
def morseTargetBrokenContinuationSet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f₁ × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
    x.2.1 ∈ morseContinuationSlice V p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 r}

/-- Membership in the set of continuation trajectories broken at the target. -/
@[simp]
theorem mem_morseTargetBrokenContinuationSet {p r : M}
    {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M} :
    x ∈ morseTargetBrokenContinuationSet f₀ V hX₁ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
          x.2.1 ∈ morseContinuationSlice V p x.1 ∧ x.2.2 ∈ hX₁.morseTrajectorySlice x.1 r :=
  Iff.rfl

end BrokenSets

/-! ### Counting broken continuation trajectories -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include h₀ hf₀ in
/-- **Finitely many continuation trajectories broken at the source**, when the continuation slices
between critical points of equal index are finite. -/
theorem finite_morseSourceBrokenContinuationSet
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V p q).Finite)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    (morseSourceBrokenContinuationSet f₁ V hX₀ p r).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  -- Sort the broken trajectories by their intermediate critical point `p'`.
  refine ((toFinite {p' : criticalPoints 𝓘(ℝ, E) f₀ |
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p' = manifoldMorseIndex 𝓘(ℝ, E) f₁ r}).biUnion
    fun p' hp' ↦ ((h₀.finite_morseTrajectorySlice hf₀ hp'.1).prod
      (hV p' r hp'.2)).image (Prod.mk p')).subset
    fun x hx ↦ mem_biUnion ⟨hx.1, hx.2.1⟩ ⟨x.2, ⟨hx.2.2.1, hx.2.2.2⟩, rfl⟩

include h₁ hf₁ in
/-- **Finitely many continuation trajectories broken at the target**, when the continuation slices
between critical points of equal index are finite. -/
theorem finite_morseTargetBrokenContinuationSet
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V p q).Finite)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    (morseTargetBrokenContinuationSet f₀ V hX₁ p r).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  -- Sort the broken trajectories by their intermediate critical point `q'`.
  refine ((toFinite {q' : criticalPoints 𝓘(ℝ, E) f₁ |
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q' ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1}).biUnion
    fun q' hq' ↦ ((hV p q' hq'.1).prod
      (h₁.finite_morseTrajectorySlice hf₁ hq'.2)).image (Prod.mk q')).subset
    fun x hx ↦ mem_biUnion ⟨hx.1, hx.2.1⟩ ⟨x.2, ⟨hx.2.2.1, hx.2.2.2⟩, rfl⟩

include h₀ in
/-- **`Φ ∘ ∂₀` counts continuation trajectories broken at the source.** When they are finitely
many, the `r`-coefficient of the continuation of the Morse boundary of `p` is the number of
continuation trajectories from `p` to `r` broken at the source, modulo two. -/
theorem morseContinuationMap_morseBoundary_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁)
    (hfin : (morseSourceBrokenContinuationSet f₁ V hX₀ p r).Finite) :
    morseContinuationMap f₀ hf₁ V (h₀.morseBoundary hf₀ (Finsupp.single p 1)) r =
      ((morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard : ZMod 2) := by
  classical
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  -- Sort the broken trajectories by their intermediate critical point `p'`.
  rw [morseContinuationMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise fun x _ ↦ Finset.mem_univ x.1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p' _ ↦ ?_
  -- The fiber over `p'` is a copy of the pairs of trajectories through `p'`.
  rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_single_apply, one_mul,
    ← ncard_coe_finset, Finset.coe_filter,
    ← ncard_preimage_of_injective_subset_range (Prod.mk_right_injective p') ?_]
  swap
  · rintro ⟨_, z⟩ ⟨-, rfl⟩
    exact ⟨z, rfl⟩
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p' = manifoldMorseIndex 𝓘(ℝ, E) f₁ r
  · rw [h₀.morseBoundaryCoeff_eq_ncard hf₀ hind.1, morseContinuationCoeff_eq_ncard hind.2,
      ← Nat.cast_mul, ← ncard_prod]
    congr 2
    ext
    simp [hind]
  · rcases not_and_or.mp hind with hpp' | hp'r
    · simp [hpp']
    · simp [hp'r]

include h₁ in
/-- **`∂₁ ∘ Φ` counts continuation trajectories broken at the target.** When they are finitely
many, the `r`-coefficient of the Morse boundary of the continuation of `p` is the number of
continuation trajectories from `p` to `r` broken at the target, modulo two. -/
theorem morseBoundary_morseContinuationMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁)
    (hfin : (morseTargetBrokenContinuationSet f₀ V hX₁ p r).Finite) :
    h₁.morseBoundary hf₁ (morseContinuationMap f₀ hf₁ V (Finsupp.single p 1)) r =
      ((morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard : ZMod 2) := by
  classical
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  -- Sort the broken trajectories by their intermediate critical point `q'`.
  rw [IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise fun x _ ↦ Finset.mem_univ x.1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  -- The fiber over `q'` is a copy of the pairs of trajectories through `q'`.
  rw [morseContinuationMap_single_apply, one_mul, ← ncard_coe_finset, Finset.coe_filter,
    ← ncard_preimage_of_injective_subset_range (Prod.mk_right_injective q') ?_]
  swap
  · rintro ⟨_, z⟩ ⟨-, rfl⟩
    exact ⟨z, rfl⟩
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q' ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1
  · rw [morseContinuationCoeff_eq_ncard hind.1, h₁.morseBoundaryCoeff_eq_ncard hf₁ hind.2,
      ← Nat.cast_mul, ← ncard_prod]
    congr 2
    ext
    simp [hind]
  · rcases not_and_or.mp hind with hpq' | hq'r
    · simp [hpq']
    · simp [hq'r]

include h₀ hf₀ h₁ in
/-- **The continuation map is a chain map exactly when broken continuation trajectories come in
pairs.** When the continuation slices between critical points of equal index are finite, the
mod-two continuation map commutes with the Morse boundaries, `∂₁ ∘ Φ = Φ ∘ ∂₀`, exactly when,
between any critical point `p` of `f₀` and any critical point `r` of `f₁`, the continuation
trajectories broken at the source and at the target are evenly many in total. -/
theorem morseBoundary_comp_morseContinuationMap_eq_iff
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (morseContinuationSlice V p q).Finite) :
    h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
        morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁),
        Even ((morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard +
          (morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard) := by
  -- Over `ZMod 2`, two coefficients agree exactly when their sum vanishes.
  have hcoeff : ∀ p r, (h₁.morseBoundary hf₁ (morseContinuationMap f₀ hf₁ V
      (Finsupp.single p 1)) r = morseContinuationMap f₀ hf₁ V
        (h₀.morseBoundary hf₀ (Finsupp.single p 1)) r) ↔
      Even ((morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard +
        (morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard) := fun p r ↦ by
    rw [morseBoundary_morseContinuationMap_single_apply h₁ hf₁ p r
        (finite_morseTargetBrokenContinuationSet h₁ hf₁ hV p r),
      morseContinuationMap_morseBoundary_single_apply h₀ hf₀ hf₁ p r
        (finite_morseSourceBrokenContinuationSet h₀ hf₀ hV p r),
      ← ZMod.natCast_eq_zero_iff_even, Nat.cast_add, CharTwo.add_eq_zero]
    exact eq_comm
  simp_rw [← hcoeff]
  constructor
  · intro h0 p r
    exact DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- Over `ZMod 2`, both maps send `a • p` to `a` times their value at `p`.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul,
      map_smul, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, h0]

end Count

/-! ### The continuation morphism of Morse chain complexes -/

section Graded

variable (f₀) in
/-- **The graded mod-two continuation map.** The `ZMod 2`-linear map from the free module on the
critical points of `f₀` of index `n` to the free module on the critical points of `f₁` of index
`n` sending `p` to the sum of the critical points `q`, each weighted by the number of trajectories
of `V` from `(p, 0)` to `(q, 1)` modulo two. -/
noncomputable def morseContinuationMapAt (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (n : ℕ) :
    ({p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n} →₀ ZMod 2) →ₗ[ZMod 2]
      ({q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = n} →₀ ZMod 2) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ morseContinuationCoeff f₀ f₁ V p q) (toFinite _)

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded continuation of a chain `c` is the sum over the critical
points `p` of index `n` of `c p` times the continuation coefficient. -/
theorem morseContinuationMapAt_apply {n : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n} →₀ ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = n}) :
    morseContinuationMapAt f₀ hf₁ V n c q =
      c.sum fun p a ↦ a * morseContinuationCoeff f₀ f₁ V p q := by
  simp [morseContinuationMapAt, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `q` in the graded continuation of `a • p` is `a` times the continuation
coefficient. -/
@[simp]
theorem morseContinuationMapAt_single_apply {n : ℕ}
    (p : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n}) (a : ZMod 2)
    (q : {q : criticalPoints 𝓘(ℝ, E) f₁ // manifoldMorseIndex 𝓘(ℝ, E) f₁ q = n}) :
    morseContinuationMapAt f₀ hf₁ V n (Finsupp.single p a) q =
      a * morseContinuationCoeff f₀ f₁ V p q := by
  rw [morseContinuationMapAt_apply, Finsupp.sum_single_index (zero_mul _)]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **The graded and total continuation maps agree.** Including the chains of index `n` into all
Morse chains intertwines the graded continuation map with the total one `morseContinuationMap`:
the continuation of a chain of index `n` is a chain of index `n`. -/
@[simp]
theorem mapDomain_morseContinuationMapAt {n : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f₀ // manifoldMorseIndex 𝓘(ℝ, E) f₀ p = n} →₀ ZMod 2) :
    (morseContinuationMapAt f₀ hf₁ V n c).mapDomain Subtype.val =
      morseContinuationMap f₀ hf₁ V (c.mapDomain Subtype.val) := by
  ext r
  rw [morseContinuationMap_apply,
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul ..]
  by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f₁ r = n
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨r, hr⟩).trans
      (morseContinuationMapAt_apply hf₁ c ⟨r, hr⟩)
  · -- Outside index `n` both sides vanish: the left side by support, the right side because every
    -- continuation coefficient from index `n` to `r` is zero.
    rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hr (hq ▸ q.2), Finsupp.sum]
    refine (Finset.sum_eq_zero fun p _ ↦ ?_).symm
    rw [morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne (by grind), mul_zero]

end Graded

section Hom

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

/-- **The graded continuation map commutes with the graded Morse boundaries** when the total
continuation map commutes with the total Morse boundaries. -/
theorem morseBoundaryAt_comp_morseContinuationMapAt
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
      morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀) (n : ℕ) :
    h₁.morseBoundaryAt hf₁ n ∘ₗ morseContinuationMapAt f₀ hf₁ V (n + 1) =
      morseContinuationMapAt f₀ hf₁ V n ∘ₗ h₀.morseBoundaryAt hf₀ n := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  simpa using LinearMap.congr_fun hcomm (Finsupp.single p.1 1)

/-- **The continuation morphism.** A mod-two continuation map along `V` that commutes with the
Morse boundaries, `∂₁ ∘ Φ = Φ ∘ ∂₀`, as a morphism from the mod-two Morse chain complex of
`(f₀, X₀)` to that of `(f₁, X₁)`; in degree `n` it is the graded continuation map
`morseContinuationMapAt`. It induces the continuation map on mod-two Morse homology. -/
noncomputable def morseContinuationHom
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
      morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀) :
    h₀.morseComplex hf₀ ⟶ h₁.morseComplex hf₁ :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (morseContinuationMapAt f₀ hf₁ V n)) fun n ↦ by
    -- Unfolding the two complexes exposes their terms as the free modules on which the graded
    -- continuation maps act, and their differentials as the graded Morse boundaries.
    unfold IsAdaptedPseudoGradient.IsMorseSmale.morseComplex
    simp only [ChainComplex.of_d]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      morseBoundaryAt_comp_morseContinuationMapAt h₀ hf₀ h₁ hf₁ hcomm n]

/-- The component of the continuation morphism in degree `n` is the graded continuation map. -/
@[simp]
theorem morseContinuationHom_f
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
      morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀) (n : ℕ) :
    (morseContinuationHom h₀ hf₀ h₁ hf₁ hcomm).f n =
      ModuleCat.ofHom (morseContinuationMapAt f₀ hf₁ V n) :=
  (rfl)

end Hom

/-! ### The constant path -/

section Constant

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h in
/-- **The graded continuation map of a constant path is the identity**: under the Morse–Smale
condition, for `C > 0`, the graded continuation map along the constant continuation field
`(X x, C t (1 - t²))` is the identity of the chains of index `n`. -/
@[simp]
theorem morseContinuationMapAt_constantContinuationField (hC : 0 < C) (n : ℕ) :
    morseContinuationMapAt f hf (constantContinuationField X C) n = LinearMap.id := by
  ext p : 2
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  simp [h.morseContinuationMap_constantContinuationField hf hC]

include h in
/-- **The continuation map of a constant path commutes with the Morse boundary**, since it is the
identity. -/
theorem morseBoundary_comp_morseContinuationMap_constantContinuationField (hC : 0 < C) :
    h.morseBoundary hf ∘ₗ morseContinuationMap f hf (constantContinuationField X C) =
      morseContinuationMap f hf (constantContinuationField X C) ∘ₗ h.morseBoundary hf := by
  rw [h.morseContinuationMap_constantContinuationField hf hC, LinearMap.comp_id, LinearMap.id_comp]

/-- **The continuation morphism of a constant path is the identity** of the mod-two Morse chain
complex, so it induces the identity on mod-two Morse homology. -/
theorem morseContinuationHom_constantContinuationField (hC : 0 < C)
    (hcomm : h.morseBoundary hf ∘ₗ morseContinuationMap f hf (constantContinuationField X C) =
      morseContinuationMap f hf (constantContinuationField X C) ∘ₗ h.morseBoundary hf) :
    morseContinuationHom h hf h hf hcomm = 𝟙 (h.morseComplex hf) := by
  ext n : 1
  rw [morseContinuationHom_f, morseContinuationMapAt_constantContinuationField h hf hC,
    HomologicalComplex.id_f]
  -- The term of the Morse complex in degree `n` is the free module on which `LinearMap.id` acts
  -- (`IsAdaptedPseudoGradient.IsMorseSmale.morseComplex_X`).
  exact ModuleCat.ofHom_id

include h hf in
/-- **The broken continuation trajectories of a constant path come in pairs.** Under the
Morse–Smale condition, for `C > 0`, between any two critical points of `f` the trajectories of the
constant continuation field broken at the source and at the target are evenly many in total. -/
theorem even_ncard_morseSourceBrokenContinuationSet_add_ncard_constantContinuationField (hC : 0 < C)
    (p r : criticalPoints 𝓘(ℝ, E) f) :
    Even ((morseSourceBrokenContinuationSet f (constantContinuationField X C) hX p r).ncard +
      (morseTargetBrokenContinuationSet f (constantContinuationField X C) hX p r).ncard) := by
  -- The continuation slices of a constant path between critical points of equal index are a
  -- single point or empty.
  have hV : ∀ p q : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q →
        (morseContinuationSlice (constantContinuationField X C) p q).Finite := fun p q hpq ↦ by
    by_cases hqp : (q : M) = p
    · rw [hqp, h.morseContinuationSlice_constantContinuationField_self hf hC p.2]
      exact finite_singleton _
    · rw [h.morseContinuationSlice_constantContinuationField_eq_empty hf hC p.2 hpq.le hqp]
      exact finite_empty
  exact (morseBoundary_comp_morseContinuationMap_eq_iff h hf h hf hV).1
    (morseBoundary_comp_morseContinuationMap_constantContinuationField h hf hC) p r

end Constant

end TauCeti
