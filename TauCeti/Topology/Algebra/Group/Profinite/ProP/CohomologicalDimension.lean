/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.RightExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.TrivialFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Devissage

/-!
# The cohomological dimension of a pro-`p` group is detected on `𝔽_p`

Let `G` be a compact pro-`p` group. Its `p`-cohomological dimension `cd_p G` asks for the vanishing
of `Hⁱ(G, M)` in every degree `i > n` and for every discrete `p`-primary torsion `G`-module `M`.
For a pro-`p` group the single module `𝔽_p` with trivial action suffices:

> `cd_p G ≤ n` if and only if `Hⁿ⁺¹(G, 𝔽_p) = 0`.

Two reductions compose. Cohomological dimension is detected in the single degree `n + 1` on the
finite discrete `p`-primary modules
(`TauCeti.cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ`, by dimension
shifting), and for a pro-`p` group the vanishing of a fixed degree on those modules is detected on
the trivial modules of order `p`
(`TauCeti.IsProP.forall_subsingleton_continuousCohomology_iff_forall_natCard_eq`, by dévissage
along the trivial filtration). A trivial discrete `G`-module of order `p` is `𝔽_p` up to a
`G`-equivariant isomorphism, so its cohomology is `cohomFp p G (n + 1)`
(`TauCeti.subsingleton_continuousCohomology_iff_subsingleton_cohomFp_of_natCard_eq`).

This is a reduction and not a definition: `cd_p G` is the standard invariant, and the equivalence
is the content of dévissage. The pro-`p` hypothesis is used. For the symmetric group `S₃` at
`p = 3`, `H¹(S₃, 𝔽₃) = Hom(S₃, 𝔽₃)` vanishes, while `cd_3 S₃` is not `0`: by Shapiro's lemma
`H¹(S₃, 𝔽₃[S₃/C₃]) = H¹(C₃, 𝔽₃) ≠ 0`, and `𝔽₃[S₃/C₃]` is a finite `3`-primary module.

The equivalence is restated for `<`, `=` and `= ⊤`: `n < cd_p G` exactly when `Hⁿ⁺¹(G, 𝔽_p) ≠ 0`,
`cd_p G = n` exactly when `Hⁿ⁺¹(G, 𝔽_p) = 0` and `Hⁿ(G, 𝔽_p) ≠ 0`, and `cd_p G = ⊤` exactly when
`Hⁿ(G, 𝔽_p) ≠ 0` for every `n`.

The file also records Tate's criterion for a profinite pro-`p` group: if `Hⁿ(G, -)` is right exact
on the finite discrete `G`-modules killed by `p`, then `cd_p G ≤ n`. The vanishing of `Hⁿ⁺¹` on
those modules is
`TauCeti.subsingleton_continuousCohomology_succ_of_forall_coeffMap_proj_surjective`, and
dévissage extends it to all finite `p`-primary modules. This is how the cohomological dimension of
a Demushkin group is bounded (Serre, *Structure de certains pro-`p`-groupes*, §9.1).

## Main results

* `TauCeti.IsProP.cohomologicalDimensionAt_le_iff_forall_smul_eq_self`,
  `TauCeti.IsProP.cohomologicalDimensionAt_le_iff_forall_natCard_eq_smul_eq_self`: the pro-`p`
  reduction of `cd_p G ≤ n` to the finite trivial modules killed by `p`, resp. of order `p`.
* `TauCeti.IsProP.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp`: **the pro-`p` reduction
  of `cd_p`**, `cd_p G ≤ n ↔ Hⁿ⁺¹(G, 𝔽_p) = 0`.
* `TauCeti.IsProP.lt_cohomologicalDimensionAt_iff_nontrivial_cohomFp`,
  `TauCeti.IsProP.cohomologicalDimensionAt_eq_iff`,
  `TauCeti.IsProP.cohomologicalDimensionAt_eq_top_iff`: the `<`, `=` and `= ⊤` forms.
* `TauCeti.IsProP.cohomologicalDimensionAt_le_of_forall_coeffMap_proj_surjective`: **Tate's
  criterion**: right exactness of `Hⁿ(G, -)` on the finite discrete `G`-modules killed by `p`
  gives `cd_p G ≤ n`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.1, Prop. 21.
* J.-P. Serre, *Structure de certains pro-`p`-groupes (d'après Demuškin)*, Séminaire Bourbaki,
  exp. 252 (1963), §9.1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2).
* H. Koch, *Galois Theory of `p`-Extensions*, Springer (2002), Definition 5.1.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction continuousSMul_trivialFp

variable [CompactSpace G] (hG : IsProP p G)
include hG

/-- **The pro-`p` reduction of `cd_p`, on the trivial modules of order `p`.** For a compact pro-`p`
group `G`, `cd_p G ≤ n` exactly when `Hⁿ⁺¹(G, A)` vanishes for every discrete `G`-module `A` of
order `p` with trivial action. -/
theorem IsProP.cohomologicalDimensionAt_le_iff_forall_natCard_eq_smul_eq_self (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
        [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
        (∀ (g : G) (a : A), g • a = a) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G A)) := by
  rw [cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ p G hp.out.ne_zero,
    hG.forall_subsingleton_continuousCohomology_iff_forall_natCard_eq]

/-- **The pro-`p` reduction of `cd_p`, on the finite trivial modules killed by `p`.** For a compact
pro-`p` group `G`, `cd_p G ≤ n` exactly when `Hⁿ⁺¹(G, A)` vanishes for every finite discrete
`G`-module `A` killed by `p` with trivial action, that is for every finite elementary abelian
`p`-group with trivial action. -/
theorem IsProP.cohomologicalDimensionAt_le_iff_forall_smul_eq_self (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
        [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, p • a = 0) →
        (∀ (g : G) (a : A), g • a = a) →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G A)) := by
  rw [cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ p G hp.out.ne_zero,
    hG.forall_subsingleton_continuousCohomology_iff]

/-- **The pro-`p` reduction of `cd_p` to the single module `𝔽_p`.** For a compact pro-`p` group
`G`, `cd_p G ≤ n` exactly when `Hⁿ⁺¹(G, 𝔽_p)` vanishes. -/
theorem IsProP.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔ Subsingleton (cohomFp p G (n + 1)) := by
  rw [hG.cohomologicalDimensionAt_le_iff_forall_natCard_eq_smul_eq_self]
  refine ⟨fun h ↦ (subsingleton_continuousCohomology_ofDiscreteModule_iff (trivialFp p G) _).1
    (h _ (natCard_trivialFp_V p G) (smul_trivialFp_V p G)), fun h A _ _ _ _ _ _ hA htriv ↦ ?_⟩
  exact (subsingleton_continuousCohomology_iff_subsingleton_cohomFp_of_natCard_eq A hA htriv _).2 h

/-- For a compact pro-`p` group `G`, `cd_p G ≤ n` exactly when `Hᵐ(G, 𝔽_p)` vanishes for every
`m > n`. -/
theorem IsProP.cohomologicalDimensionAt_le_iff_forall_subsingleton_cohomFp (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔ ∀ m, n < m → Subsingleton (cohomFp p G m) :=
  ⟨fun h _ hm ↦ subsingleton_cohomFp_of_cohomologicalDimensionAt_le h hm,
    fun h ↦ (hG.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp n).2 (h _ n.lt_succ_self)⟩

/-- For a compact pro-`p` group `G`, `n < cd_p G` exactly when `Hⁿ⁺¹(G, 𝔽_p)` is nontrivial. -/
theorem IsProP.lt_cohomologicalDimensionAt_iff_nontrivial_cohomFp (n : ℕ) :
    (n : ℕ∞) < cohomologicalDimensionAt.{u} p G ↔ Nontrivial (cohomFp p G (n + 1)) := by
  rw [← not_le, hG.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp,
    ← not_nontrivial_iff_subsingleton, not_not]

/-- For a compact pro-`p` group `G`, `n + 1 ≤ cd_p G` exactly when `Hⁿ⁺¹(G, 𝔽_p)` is
nontrivial. -/
theorem IsProP.le_cohomologicalDimensionAt_iff_nontrivial_cohomFp (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ cohomologicalDimensionAt.{u} p G ↔ Nontrivial (cohomFp p G (n + 1)) := by
  rw [Nat.cast_succ, ENat.add_one_le_iff (ENat.natCast_ne_top n),
    hG.lt_cohomologicalDimensionAt_iff_nontrivial_cohomFp]

/-- **`cd_p G = n` on `𝔽_p`.** For a compact pro-`p` group `G`, `cd_p G = n` exactly when
`Hⁿ⁺¹(G, 𝔽_p)` vanishes and `Hⁿ(G, 𝔽_p)` does not. -/
theorem IsProP.cohomologicalDimensionAt_eq_iff (n : ℕ) :
    cohomologicalDimensionAt.{u} p G = n ↔
      Subsingleton (cohomFp p G (n + 1)) ∧ Nontrivial (cohomFp p G n) := by
  rw [le_antisymm_iff, hG.cohomologicalDimensionAt_le_iff_subsingleton_cohomFp]
  cases n with
  | zero => simp [nontrivial_cohomFp_zero]
  | succ m => rw [hG.le_cohomologicalDimensionAt_iff_nontrivial_cohomFp]

/-- **Infinite `cd_p` on `𝔽_p`.** For a compact pro-`p` group `G`, `cd_p G = ⊤` exactly when
`Hⁿ(G, 𝔽_p)` is nontrivial in every degree. -/
theorem IsProP.cohomologicalDimensionAt_eq_top_iff :
    cohomologicalDimensionAt.{u} p G = ⊤ ↔ ∀ n, Nontrivial (cohomFp p G n) := by
  rw [ENat.eq_top_iff_forall_gt]
  refine ⟨fun h n ↦ ?_, fun h n ↦ (hG.lt_cohomologicalDimensionAt_iff_nontrivial_cohomFp n).2 (h _)⟩
  cases n with
  | zero => exact nontrivial_cohomFp_zero p G
  | succ m => exact (hG.lt_cohomologicalDimensionAt_iff_nontrivial_cohomFp m).1 (h m)

/-- **Tate's criterion for the cohomological dimension of a pro-`p` group.** Let `G` be a profinite
pro-`p` group. If for every short exact sequence `0 → A → B → C → 0` of finite discrete `G`-modules
killed by `p` the map `Hⁿ(G, B) → Hⁿ(G, C)` is surjective, then `cd_p G ≤ n`: right exactness
kills `Hⁿ⁺¹` on those modules, and dévissage extends the vanishing to every finite discrete
`p`-primary module. -/
theorem IsProP.cohomologicalDimensionAt_le_of_forall_coeffMap_proj_surjective
    [TotallyDisconnectedSpace G] (n : ℕ)
    (h : ∀ (A B C : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
      [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
      [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
      [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
      (S : DiscreteShortExact G A B C),
      (∀ a : A, p • a = 0) → (∀ b : B, p • b = 0) → (∀ c : C, p • c = 0) →
      Function.Surjective (ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) n)) :
    cohomologicalDimensionAt.{u} p G ≤ n := by
  rw [cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ p G hp.out.ne_zero n]
  intro M _ _ _ _ _ _ hM
  exact hG.subsingleton_continuousCohomology_of_forall_smul_eq_self
    (fun A _ _ _ _ _ _ hA _ ↦
      subsingleton_continuousCohomology_succ_of_forall_coeffMap_proj_surjective h A hA) M hM

end TauCeti
