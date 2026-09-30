/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The strict cohomological dimension exceeds the ordinary one by at most one

For a compact group `G` and a natural number `p`, the strict `p`-cohomological dimension is at
most one more than the ordinary one, `scd_p G ≤ cd_p G + 1` (NSW (3.3.3)). Together with
`TauCeti.cohomologicalDimensionAt_le_strictCohomologicalDimensionAt` this pins `scd_p G` to one
of the two values `cd_p G` and `cd_p G + 1`; both occur, `ℤ_p` having `cd_p = 1` and `scd_p = 2`.

The argument is Serre's. Suppose `Hⁱ(G, A) = 0` for every `i > n` and every discrete `p`-primary
torsion `G`-module `A`, and let `M` be an arbitrary discrete `G`-module. Multiplication by `p` on
`M` factors as `M ↠ pM ↪ M`, which gives two short exact sequences

```text
0 → M[p] → M → pM → 0,        0 → pM → M → M ⧸ pM → 0,
```

whose outer terms `M[p]` and `M ⧸ pM` are killed by `p`, hence `p`-primary torsion. For `i > n + 1`
the long exact sequences make `Hⁱ(G, M) → Hⁱ(G, pM)` injective, because `Hⁱ(G, M[p]) = 0`, and
`Hⁱ(G, pM) → Hⁱ(G, M)` injective, because `Hⁱ⁻¹(G, M ⧸ pM) = 0`. Their composite is multiplication
by `p` on `Hⁱ(G, M)`, which is therefore injective, so no nonzero class of `Hⁱ(G, M)` is killed by
a power of `p`: the `p`-primary component of `Hⁱ(G, M)` vanishes.

The long exact sequence of continuous cohomology is available for coefficients in the universe of
`G`, so the statements here fix the auxiliary universe parameter of the predicates of
`TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic` to that of
`G`, as in `TauCeti.cohomologicalDimensionLE_iff_forall_subsingleton_succ`.

## Main results

* `TauCeti.CohomologicalDimensionLE.nsmul_right_injective`: under `CohomologicalDimensionLE p G n`,
  multiplication by `p` is injective on `Hⁱ(G, M)` for every `i > n + 1` and every discrete `M`.
* `TauCeti.CohomologicalDimensionLE.strictCohomologicalDimensionLE_add_one`:
  `CohomologicalDimensionLE p G n` implies `StrictCohomologicalDimensionLE p G (n + 1)`.
* `TauCeti.strictCohomologicalDimensionAt_le_cohomologicalDimensionAt_add_one`:
  `scd_p G ≤ cd_p G + 1` in `ℕ∞`, including the case `cd_p G = ⊤`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.3).
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.2, Prop. 13.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- **Multiplication by `p` is injective above `cd_p + 1`.** For a compact group `G` with
`CohomologicalDimensionLE p G n`, multiplication by `p` is injective on `Hⁱ(G, M)` for every
`i > n + 1` and every discrete `G`-module `M` with continuous action, `p`-primary or not. -/
theorem CohomologicalDimensionLE.nsmul_right_injective {n : ℕ}
    (h : CohomologicalDimensionLE.{u} p G n) (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] {i : ℕ} (hi : n + 1 < i) :
    Function.Injective fun x : continuousCohomology i (ofDiscreteModule ℤ G M) ↦ p • x := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- the `p`-torsion `K = M[p]` and the image `I = pM` of multiplication by `p`
  set K := (nsmulAddMonoidHom p : M →+ M).ker
  set I := (nsmulAddMonoidHom p : M →+ M).range
  have hK : ∀ g : G, ∀ m ∈ K, g • m ∈ K := fun g m hm ↦ by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hm ⊢
    rw [smul_comm, hm, smul_zero]
  have hI : ∀ g : G, ∀ m ∈ I, g • m ∈ I := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨g • m, smul_comm p g m⟩
  let := K.restrictDistribMulAction hK
  let := I.restrictDistribMulAction hI
  let := I.quotientDistribMulAction hI
  have : ContinuousSMul G K := K.restrictDistribMulAction_continuousSMul hK
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul G (M ⧸ I) := I.quotientDistribMulAction_continuousSMul hI
  -- the short exact sequence `0 → M[p] → M → pM → 0`
  let S₁ : DiscreteShortExact G K M I :=
    { incl := K.subtype
      proj := (nsmulAddMonoidHom p : M →+ M).rangeRestrict
      incl_equivariant := K.restrictDistribMulAction_coe_smul hK
      proj_equivariant := fun g m ↦ Subtype.ext <| by
        rw [I.restrictDistribMulAction_coe_smul hI]
        exact smul_comm p g m
      incl_injective := K.subtype_injective
      proj_surjective := AddMonoidHom.rangeRestrict_surjective _
      exact := fun m ↦ by
        rw [← AddMonoidHom.mem_ker, AddMonoidHom.ker_rangeRestrict]
        exact ⟨fun hm ↦ ⟨⟨m, hm⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩ }
  -- the short exact sequence `0 → pM → M → M ⧸ pM → 0`
  let S₂ := DiscreteShortExact.ofAddSubgroup I hI
  -- `M[p]` and `M ⧸ pM` are killed by `p`, so their cohomology vanishes above `n`
  have hKp : IsPPrimaryTorsion p K :=
    isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, Subtype.ext (by simpa [K] using AddMonoidHom.mem_ker.1 m.2)⟩
  have hQp : IsPPrimaryTorsion p (M ⧸ I) := isPPrimaryTorsion_iff.2 fun q ↦ by
    induction q using QuotientAddGroup.induction_on with
    | H m => exact ⟨1, (QuotientAddGroup.eq_zero_iff _).2 (by simp [I])⟩
  have := cohomologicalDimensionLE_iff.1 h K hKp (j + 1) (by omega)
  have := cohomologicalDimensionLE_iff.1 h (M ⧸ I) hQp j (by omega)
  -- `Hʲ⁺¹(G, M) → Hʲ⁺¹(G, pM)` and `Hʲ⁺¹(G, pM) → Hʲ⁺¹(G, M)` are injective
  have hinj₁ := S₁.coeffMap_proj_injective (n := j + 1)
  have hinj₂ := S₂.coeffMap_incl_injective (n := j)
  -- multiplication by `p` on `M`, as the composite `M → pM → M`
  have hfac : p • 𝟙 (ofDiscreteModule ℤ G M) =
      ofDiscreteModuleMap S₁.proj.toIntLinearMap S₁.proj_equivariant ≫
        ofDiscreteModuleMap S₂.incl.toIntLinearMap S₂.incl_equivariant := by
    -- Both sides send `m` to `p • m`: the left-hand side by definition, since Mathlib's `TopRep`
    -- states no lemma for `(p • f).hom` (the `ℕ`-action on morphisms is transported from
    -- `ContIntertwiningMap`), and the right-hand side because `S₂.incl` is the inclusion of `pM`.
    ext m
    exact (congrArg (fun f : I →+ M ↦ f (S₁.proj m))
      (DiscreteShortExact.ofAddSubgroup_incl I hI)).symm
  -- `Hⁱ(G, -)` is additive, so it sends `p • 𝟙` to `p • 𝟙`
  have hmap : ContinuousCohomology.coeffMap (p • 𝟙 (ofDiscreteModule ℤ G M)) (j + 1) = p • 𝟙 _ :=
    (ContinuousCohomology.continuousCohomologyFunctor ℤ G (j + 1)).map_nsmul.trans
      (congrArg (p • ·) ((ContinuousCohomology.continuousCohomologyFunctor ℤ G (j + 1)).map_id _))
  rw [hfac, ContinuousCohomology.coeffMap_comp] at hmap
  have hcomp (x : continuousCohomology (j + 1) (ofDiscreteModule ℤ G M)) :
      p • x = ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap S₂.incl.toIntLinearMap S₂.incl_equivariant) (j + 1)
          (ContinuousCohomology.coeffMap
            (ofDiscreteModuleMap S₁.proj.toIntLinearMap S₁.proj_equivariant) (j + 1) x) := by
    simpa using (congrArg (fun f ↦ (f : continuousCohomology (j + 1) _ ⟶ _) x) hmap).symm
  refine fun x y hxy ↦ hinj₁ (hinj₂ ?_)
  rw [← hcomp, ← hcomp]
  exact hxy

/-- **`cd_p ≤ n` implies `scd_p ≤ n + 1`** (NSW (3.3.3)). For a compact group `G`, if `Hⁱ(G, A)`
vanishes for every `i > n` and every discrete `p`-primary torsion `G`-module `A`, then the
`p`-primary component of `Hⁱ(G, M)` vanishes for every `i > n + 1` and every discrete
`G`-module `M`. -/
theorem CohomologicalDimensionLE.strictCohomologicalDimensionLE_add_one {n : ℕ}
    (h : CohomologicalDimensionLE.{u} p G n) : StrictCohomologicalDimensionLE.{u} p G (n + 1) := by
  refine strictCohomologicalDimensionLE_iff.2 fun M _ _ _ _ _ i hi ↦ ?_
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun x ⟨k, hk⟩ ↦ ?_
  -- `p ^ k • x = 0`, and multiplication by `p` is injective, hence so is multiplication by `p ^ k`
  have hinj := (h.nsmul_right_injective M hi).iterate k
  rw [smul_iterate] at hinj
  exact hinj (hk.trans (smul_zero _).symm)

variable (p G)

/-- **`scd_p ≤ cd_p + 1`** (NSW (3.3.3)): over a compact group, the strict `p`-cohomological
dimension exceeds the `p`-cohomological dimension by at most one. The case `cd_p G = ⊤` is
included, the right-hand side then being `⊤ + 1 = ⊤`. -/
theorem strictCohomologicalDimensionAt_le_cohomologicalDimensionAt_add_one :
    strictCohomologicalDimensionAt.{u} p G ≤ cohomologicalDimensionAt.{u} p G + 1 := by
  induction hcd : cohomologicalDimensionAt.{u} p G using ENat.recTopCoe with
  | top => simp
  | coe n =>
    have h := (cohomologicalDimensionAt_le_iff p G n).1 hcd.le
    exact_mod_cast (strictCohomologicalDimensionAt_le_iff p G (n + 1)).2
      h.strictCohomologicalDimensionLE_add_one

end TauCeti
