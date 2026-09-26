/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCoefficients

/-!
# Cohomological dimension tested on torsion coefficients

For a compact group `G` and a prime `p`, the vanishing predicate `CohomologicalDimensionLE p G n`
asks `Hⁱ(G, M)` to vanish for every `i > n` and every discrete `p`-primary torsion `G`-module `M`.
NSW (3.3.1) states the ordinary cohomological dimension through a second interface: the
`p`-primary component of `Hⁱ(G, M)` vanishes for every `i > n` and every discrete **torsion**
`G`-module `M`. This file proves that the two interfaces agree.

One direction is immediate: a `p`-primary module is torsion, and its cohomology is `p`-primary
torsion, so the vanishing of its `p`-primary component is the vanishing of the whole group. For the
other, a class of `Hⁱ(G, M)` with `M` torsion comes from a finite `G`-stable subgroup `N ≤ M`.
Writing the order of `N` as `pᵇ * c` with `c` prime to `p`, multiplication by `c` on `N` lands in a
`p`-primary torsion submodule, whose cohomology vanishes above `n`, so `c` kills `Hⁱ(G, N)`. A class
killed both by a power of `p` and by `c` is zero.

The second interface differs from the strict predicate `StrictCohomologicalDimensionLE p G n` only
by its torsion hypothesis on `M`, which is why the two are kept apart.

## Main results

* `TauCeti.cohomologicalDimensionLE_iff_torsion`: over a compact group and for prime `p`,
  `CohomologicalDimensionLE p G n` holds exactly when the `p`-primary component of `Hⁱ(G, M)`
  vanishes for every `i > n` and every discrete torsion `G`-module `M`.
* `TauCeti.cohomologicalDimensionAt_le_iff_torsion`: the same characterization of
  `cd_p G ≤ n`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Under `CohomologicalDimensionLE p G n`, a natural number `c` kills `Hⁱ(G, M)` for every
`i > n` as soon as `c • m` is `p`-primary torsion for every `m : M`: multiplication by `c` on `M`
factors through its range, a `p`-primary torsion module whose cohomology vanishes above `n`. -/
private theorem CohomologicalDimensionLE.nsmul_eq_zero {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p G n) {M : Type (max u v)} [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] {c : ℕ}
    (hc : ∀ m : M, ∃ k : ℕ, p ^ k • c • m = 0) {i : ℕ} (hi : n < i)
    (x : continuousCohomology i (ofDiscreteModule ℤ G M)) : c • x = 0 := by
  set K := (nsmulAddMonoidHom c : M →+ M).range
  have hK : ∀ g : G, ∀ m ∈ K, g • m ∈ K := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨g • m, smul_comm c g m⟩
  let := K.restrictDistribMulAction hK
  have : ContinuousSMul G K := K.restrictDistribMulAction_continuousSMul hK
  have hKp : IsPPrimaryTorsion p K := by
    rw [isPPrimaryTorsion_iff]
    rintro ⟨_, m, rfl⟩
    obtain ⟨k, hk⟩ := hc m
    exact ⟨k, Subtype.ext hk⟩
  have := cohomologicalDimensionLE_iff.1 h K hKp i hi
  -- multiplication by `c` on `M`, as the composite `M → K → M`
  have hfac : c • 𝟙 (ofDiscreteModule ℤ G M) =
      ofDiscreteModuleMap (nsmulAddMonoidHom c : M →+ M).rangeRestrict.toIntLinearMap
          (fun g m ↦ Subtype.ext (by simp [smul_comm c g m])) ≫
        ofDiscreteModuleMap K.subtype.toIntLinearMap (K.restrictDistribMulAction_coe_smul hK) := by
    -- Both sides send `m` to `c • m`. Mathlib's `TopRep` states no lemma for `(c • f).hom`: the
    -- `ℕ`-action on morphisms is transported from `ContIntertwiningMap`, so this holds by `rfl`.
    ext m
    rfl
  -- `Hⁱ(G, -)` is additive, so it sends `c • 𝟙` to `c • 𝟙`
  have hmap : ContinuousCohomology.coeffMap (c • 𝟙 (ofDiscreteModule ℤ G M)) i = c • 𝟙 _ :=
    (ContinuousCohomology.continuousCohomologyFunctor ℤ G i).map_nsmul.trans
      (congrArg (c • ·) ((ContinuousCohomology.continuousCohomologyFunctor ℤ G i).map_id _))
  rw [hfac, ContinuousCohomology.coeffMap_comp] at hmap
  have hx := congrArg (fun f ↦ (f : continuousCohomology i _ ⟶ _) x) hmap
  simp only [ConcreteCategory.comp_apply, Subsingleton.elim (ContinuousCohomology.coeffMap _ i x) 0,
    map_zero] at hx
  simpa using hx.symm

variable [CompactSpace G]

/-- **The torsion interface for the vanishing predicate of cohomological dimension**
(NSW (3.3.1)). For a compact group `G` and a prime `p`, `CohomologicalDimensionLE p G n` holds
exactly when the `p`-primary component of `Hⁱ(G, M)` vanishes for every `i > n` and every discrete
torsion `G`-module `M` with continuous action. -/
theorem cohomologicalDimensionLE_iff_torsion (hp : p.Prime) {n : ℕ} :
    CohomologicalDimensionLE.{v} p G n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsAddTorsion M → ∀ i : ℕ, n < i →
        AddCommGroup.primaryComponent (continuousCohomology i (ofDiscreteModule ℤ G M)) p = ⊥ := by
  refine ⟨fun h M _ _ _ _ _ hM i hi ↦ ?_, fun h ↦ ?_⟩
  · refine (AddSubgroup.eq_bot_iff_forall _).2 fun x ⟨k, hk⟩ ↦ ?_
    -- the class comes from a finite `G`-stable subgroup `N`
    obtain ⟨N, hN, hfin, y, rfl⟩ :=
      ContinuousCohomology.exists_finite_addSubgroup_coeffMap_eq hM i x
    let := N.restrictDistribMulAction hN
    have : ContinuousSMul G N := N.restrictDistribMulAction_continuousSMul hN
    -- the order of `N` is `p ^ b * c` with `c` prime to `p`, and `c • N` is `p`-primary
    obtain ⟨b, c, hc, hcard⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := N)).ne' p hp.ne_one
    have hcy : c • y = 0 := h.nsmul_eq_zero
      (fun m ↦ ⟨b, by rw [smul_smul, ← hcard, card_nsmul_eq_zero']⟩) hi y
    have hcx : c • ContinuousCohomology.coeffMap (ofDiscreteModuleMap N.subtype.toIntLinearMap
        (N.restrictDistribMulAction_coe_smul hN)) i y = 0 := by
      rw [← map_nsmul, hcy, map_zero]
    -- the class is killed by the coprime integers `p ^ k` and `c`
    exact (nsmul_eq_zero_iff_of_coprime ((hp.coprime_iff_not_dvd.2 hc).pow_left k)).1 ⟨hk, hcx⟩
  · -- a `p`-primary module is torsion, and its cohomology is `p`-primary
    refine cohomologicalDimensionLE_iff.2 fun M _ _ _ _ _ hM i hi ↦ ?_
    have hH := isPPrimaryTorsion_continuousCohomology (ofDiscreteModule ℤ G M) hM i
    exact subsingleton_of_forall_eq 0 fun x ↦
      AddSubgroup.mem_bot.1 (h M (hM.isAddTorsion hp.ne_zero) i hi ▸ hH.mem x)

/-- **The torsion interface for the `p`-cohomological dimension** (NSW (3.3.1)). For a compact
group `G` and a prime `p`, `cd_p G ≤ n` exactly when the `p`-primary component of `Hⁱ(G, M)`
vanishes for every `i > n` and every discrete torsion `G`-module `M` with continuous action. -/
theorem cohomologicalDimensionAt_le_iff_torsion (hp : p.Prime) (n : ℕ) :
    cohomologicalDimensionAt.{v} p G ≤ n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M], IsAddTorsion M → ∀ i : ℕ, n < i →
        AddCommGroup.primaryComponent (continuousCohomology i (ofDiscreteModule ℤ G M)) p = ⊥ := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_torsion hp]

end TauCeti
