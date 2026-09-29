/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.GolodShafarevich
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationCocycle
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationRank

/-!
# The Golod–Shafarevich inequality for finite `p`-groups

A nontrivial finite `p`-group `G` with generator rank `d(G)` and relation rank
`r(G) = dim_{𝔽_p} H²(G, 𝔽_p)` satisfies

```text
d(G)² < 4 r(G).
```

So a finite `p`-group needs many relations: more than a quarter of the square of the number of
generators.

The proof transfers a minimal presentation of `G` to the group algebra `A = 𝔽_p[G]` and applies
the Golod–Shafarevich inequality for finite-dimensional algebras
(`TauCeti.card_sq_lt_four_mul_card`). Let `π : F ↠ G` be a minimal presentation by the free
pro-`p` group `F` on `d = d(G)` generators `xᵢ`, and let `ρ₁, …, ρ_r` generate its relation
subgroup `R` as a closed normal subgroup, with `r = r(G)`. Write `gᵢ = π xᵢ`.

* The `gᵢ` generate `G`, so the elements `gᵢ - 1` generate the augmentation ideal `I` of `A` as a
  left ideal (`TauCeti.MonoidAlgebra.range_linearCombination_eq_ker_augmentation`).
* Let `D : F → A^d` be the continuous `1`-cocycle with `D xᵢ = eᵢ`, for the action of `F` on `A^d`
  by left multiplication through `π` (`TauCeti.freeProP.exists_mem_Z1_forall_apply_of_eq`). On `R`
  it is additive and conjugation-equivariant, so `D R` lies in the `A`-span `S` of the `D ρⱼ`.
  Modulo `S`, `D` therefore descends to a function `δ` on `G`, and extending `δ` linearly to `A`
  inverts the map `a ↦ ∑ aᵢ (gᵢ - 1)` modulo `S`. Hence the relation module of the `gᵢ`
  (`TauCeti.MonoidAlgebra.relationModule`) is spanned by the `r` vectors `D ρⱼ`.
* The relators lie in the Frattini subgroup of `F`, and composing `D` with the augmentation
  `A → 𝔽_p` gives a continuous homomorphism to an elementary abelian `p`-group, so the entries of
  every `D ρⱼ` lie in `I`.

## Main results

* `IsPGroup.sq_topologicalGeneratorRankNat_lt_four_mul_finrank_cohomFp_two`: **the
  Golod–Shafarevich inequality** `d(G)² < 4 r(G)` for a nontrivial finite `p`-group `G`.

## References

* E. S. Golod and I. R. Shafarevich, *On the class field tower*, Izv. Akad. Nauk SSSR Ser. Mat.
  28 (1964).
* P. Roquette, *On class field towers*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic
  Number Theory*, Chapter IX, §4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.7).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Theorem 7.8.5.
-/

public section

namespace TauCeti

open Subgroup ContCohomology Module _root_.MonoidAlgebra

universe u

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- cohomology API would not see a single additive structure on `ZMod p`. Preferring the ring path
-- locally keeps one.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Fintype X] {G : Type u} [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G]

omit [Fintype X] in
/-- The cocycle `D : F → 𝔽_p[G]^X` of a continuous homomorphism `π : F → G` from a free pro-`p`
group to a finite discrete group, for the action of `F` on `𝔽_p[G]^X` by left multiplication
through `π`: it is locally constant and sends the generators to the standard basis vectors. -/
private theorem exists_cocycle [Finite X] [DecidableEq X] (π : freeProP p X →ₜ* G) :
    ∃ D : freeProP p X → X → MonoidAlgebra (ZMod p) G, IsLocallyConstant D ∧
      (∀ g h, D (g * h) = single (π g) (1 : ZMod p) • D h + D g) ∧
      ∀ i, D (freeProP.of i) = Pi.single i 1 := by
  -- `F` acts on the discrete module `𝔽_p[G]` by left multiplication through `π`.
  let : TopologicalSpace (MonoidAlgebra (ZMod p) G) := ⊥
  have : DiscreteTopology (MonoidAlgebra (ZMod p) G) := ⟨rfl⟩
  let : DistribMulAction (freeProP p X) (MonoidAlgebra (ZMod p) G) :=
    DistribMulAction.compHom _ ((MonoidAlgebra.of (ZMod p) G).comp π.toMonoidHom)
  have : ContinuousSMul (freeProP p X) (MonoidAlgebra (ZMod p) G) :=
    ⟨(continuous_of_discreteTopology (f := fun y : G × MonoidAlgebra (ZMod p) G ↦
      single y.1 (1 : ZMod p) * y.2)).comp (π.continuous.prodMap continuous_id)⟩
  have : Finite (MonoidAlgebra (ZMod p) G) := Module.finite_of_finite (ZMod p)
  have hM : IsProP p (Multiplicative (X → MonoidAlgebra (ZMod p) G)) :=
    IsPGroup.isProP (ZModModule.isPGroup_multiplicative (n := p))
  obtain ⟨D, hD, hDof⟩ := freeProP.exists_mem_Z1_forall_apply_of_eq hM fun i ↦ Pi.single i 1
  obtain ⟨hDc, hDcoc⟩ := mem_Z1_iff.1 hD
  exact ⟨D, IsLocallyConstant.iff_continuous D |>.2 hDc, hDcoc, hDof⟩

/-- **The Golod–Shafarevich inequality.** A nontrivial finite `p`-group `G`, with the discrete
topology, satisfies `d(G)² < 4 r(G)`, where `d(G)` is its generator rank and
`r(G) = dim_{𝔽_p} H²(G, 𝔽_p)` is its relation rank. Finite generation follows from
`TauCeti.isTopologicallyFinitelyGenerated_of_fg`. -/
theorem _root_.IsPGroup.sq_topologicalGeneratorRankNat_lt_four_mul_finrank_cohomFp_two
    {G : Type u} [Group G] [Finite G] [Nontrivial G] [TopologicalSpace G] [DiscreteTopology G]
    (hG : IsPGroup p G) :
    topologicalGeneratorRankNat G isTopologicallyFinitelyGenerated_of_fg ^ 2 <
      4 * finrank (ZMod p) (cohomFp p G 2) := by
  classical
  let hfg : IsTopologicallyFinitelyGenerated G := isTopologicallyFinitelyGenerated_of_fg
  -- The relation rank is the dimension of the explicit `H²(G, 𝔽_p)`, which is finite.
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  rw [(cohomFpLinearEquivH2 p G fun _ _ ↦ rfl).finrank_eq]
  have hH2 : Finite (H2 G (ZMod p)) := inferInstance
  -- A minimal presentation `G ≅ ⟨X ∣ rels⟩` on `d(G)` generators, and at most `r(G)` elements `s`
  -- generating its relation subgroup as a closed normal subgroup.
  let X := ULift.{u} (Fin (topologicalGeneratorRankNat G hfg))
  obtain ⟨rels, hrels, ⟨e⟩⟩ :=
    hG.isProP.exists_subset_proPFrattini_continuousMulEquiv_presentedProP hfg X (by simp [X])
  obtain ⟨t, htcard, ht⟩ := (presentedProP.finrank_H2_le_iff rels hrels e (fun _ _ ↦ rfl)
    ((presentedProP.finite_H2_iff rels hrels e fun _ _ ↦ rfl).1 hH2) _).1 le_rfl
  let s : Finset (freeProP p X) := t.image Subtype.val
  let π : freeProP p X →ₜ* G := (e : presentedProP p X rels →ₜ* G).comp (presentedProP.mk p rels)
  have hπ : Function.Surjective π := e.surjective.comp (presentedProP.mk_surjective p rels)
  have hs (w : freeProP p X) :
      π w = 1 ↔ w ∈ (normalClosure (s : Set (freeProP p X))).topologicalClosure := by
    rw [Finset.coe_image, ht, ← presentedProP.mk_eq_one_iff]
    exact map_eq_one_iff e e.injective
  have hsΦ (ρ : s) : (ρ : freeProP p X) ∈ proPFrattini p (freeProP p X) := by
    obtain ⟨⟨ρ, hρR⟩, -, hρ⟩ := Finset.mem_image.1 ρ.2
    rw [← hρ]
    exact (topologicalClosure_normalClosure_le_iff isClosed_proPFrattini).2 hrels hρR
  obtain ⟨D, hD, hcoc, hDof⟩ := exists_cocycle π
  -- The `π xᵢ` generate `G`, so the `π xᵢ - 1` generate the augmentation ideal as a left ideal.
  have hgen : Subgroup.closure (Set.range fun i ↦ π (freeProP.of i)) = ⊤ := by
    have h := topologicalClosure_closure_image_eq_top
      (freeProP.topologicalClosure_closure_range_of_eq_top p X) (f := (π : freeProP p X →* G))
      π.continuous hπ.denseRange
    rw [← Set.range_comp, Function.comp_def] at h
    exact eq_top_iff.2 (h.ge.trans (topologicalClosure_minimal _ le_rfl (isClosed_discrete _)))
  have hspan := Fintype.range_linearCombination (MonoidAlgebra (ZMod p) G)
    (fun i ↦ single (π (freeProP.of i)) (1 : ZMod p) - 1) ▸
      MonoidAlgebra.range_linearCombination_eq_ker_augmentation hgen
  have hX : Nonempty X := by
    have hd : topologicalGeneratorRankNat G hfg ≠ 0 := fun h0 ↦
      not_subsingleton G <| topologicalGeneratorRank_eq_zero_iff.1 <| by
        rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank hfg, h0, Nat.cast_zero]
    exact ⟨⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩⟩
  have key := card_sq_lt_four_mul_card (ZMod p) _
    (RingHom.ker_ne_top (MonoidAlgebra.augmentation (ZMod p) G)) _ hspan
    (fun ρ : s ↦ D ρ)
    (fun ρ i ↦ RingHom.mem_ker.2
      (augmentation_apply_eq_zero_of_mem_proPFrattini hcoc hD (hsΦ ρ) i))
    fun a ha ↦ relationModule_le_span hcoc hπ hs hD hDof
      (MonoidAlgebra.mem_relationModule_iff.2 ha)
  have hcardX : Fintype.card X = topologicalGeneratorRankNat G hfg := by simp [X]
  have hcards : Fintype.card s ≤ finrank (ZMod p) (H2 G (ZMod p)) := by
    rw [Fintype.card_coe]
    exact Finset.card_image_le.trans htcard
  rw [hcardX] at key
  omega

end TauCeti
