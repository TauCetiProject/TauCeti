/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete
public import TauCeti.Topology.CompactOpen

/-!
# Continuous cohomology of a discrete representation of a compact group

Mathlib builds continuous cohomology as the homology of the homogeneous cochain complex, whose
terms are the invariants of the iterated coinduced representations `C(G, C(G, …, X.V))`. Over a
compact group `G` and for a representation whose underlying module is discrete, every one of those
function spaces is discrete in the compact-open topology, hence so is every term of the complex and
every subquotient of it. So `continuousCohomology n X` is a *discrete* topological module.

This matters because the topology is part of the statement. The low-degree explicit model presents
`H¹` and `H²` as quotients of subgroups of `G → M` and `G × G → M`; those carry the pointwise
topology, whose quotient is not discrete for an infinite profinite `G` (with trivial `ZMod 2`
coefficients on an infinite product of copies of `ZMod 2`, no finite set of evaluations isolates
the zero character). A comparison between the explicit model and the canonical one must therefore
say in which category it holds, and the results here are what make the canonical side of that
comparison a discrete object.

When the action on `X` is moreover continuous, so that `X` is smooth discrete
(`TauCeti.IsSmoothDiscrete`), every term of the resolution is smooth discrete as well
(`TauCeti.IsSmoothDiscrete.resolutionX`), since coinduction from the trivial subgroup preserves
smoothness over a compact group.

The predicate `TauCeti.ContinuousCohomology.ResolutionVanishesOn X T n F` records that a term
`F` of the resolution `C(G, C(G, …, X))` vanishes on all `n`-tuples of points of a subset `T ⊆ G`,
and `TauCeti.ContinuousCohomology.ResolutionVanishesOn.exists_isOpen` shows that vanishing on a
compact set already holds on an open neighbourhood of it. For an arbitrary compact set that is
all one gets; when the compact set is a closed subgroup of a profinite `G`, the neighbourhood
contains an open subgroup, so the vanishing holds on an open subgroup containing the closed one
(`TauCeti.ContinuousCohomology.exists_openSubgroup_le_resolutionMap_subgroupSubtype_eq_zero` in
`ClosedSubgroup.lean`). This is how cohomological statements about a closed subgroup descend to the
open subgroups containing it.

This implements the "category of the comparison" milestone of Layer 3 of the human-authored
roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`.
-/

public section

namespace TauCeti

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (X : TopRep k G) [DiscreteTopology X.V] (n : ℕ)

/-- Every term of the coinduced resolution of a discrete representation of a compact group is
discrete: it is an iterated space of continuous maps out of the compact group `G`. -/
instance discreteTopology_resolutionX : DiscreteTopology (TopRep.resolutionX X n).V := by
  induction n with
  | zero => exact ‹DiscreteTopology X.V›
  -- the successor step is `TopRep.coind₁`, whose underlying module is `C(G, -)` by definition
  | succ n ih => exact inferInstanceAs (DiscreteTopology C(G, (TopRep.resolutionX X n).V))

/-- Every term of the homogeneous cochain complex of a discrete representation of a compact group
is discrete. -/
instance discreteTopology_homogeneousCochains :
    DiscreteTopology ((TopRep.homogeneousCochains X).X n) :=
  -- degree `n` of the complex is the invariants of the shifted resolution, an additive subgroup
  -- of a discrete module; the equality holds by definition but is not a syntactic match
  inferInstanceAs (DiscreteTopology (TopRep.invariants (TopRep.resolutionX X (n + 1))))

/-- The continuous cocycles of a discrete representation of a compact group are discrete. -/
instance discreteTopology_cocycles : DiscreteTopology (ContinuousCohomology.cocycles X n) :=
  HomologicalComplex.discreteTopology_cycles _ n

section Smooth

variable {X}

attribute [local instance] TopRep.distribMulAction

omit [DiscreteTopology X.V] in
/-- **Coinduction from the trivial subgroup preserves smoothness** over a compact group: if `X` is
a smooth discrete representation of the compact group `G`, so is `X.coind₁ = C(G, X)`. -/
theorem IsSmoothDiscrete.coind₁ (hX : IsSmoothDiscrete k X) : IsSmoothDiscrete k X.coind₁ := by
  -- The stabilizer of `F : C(G, X)` under `(g • F) x = g • F (g⁻¹ * x)` contains an open
  -- neighbourhood of `1`, by the tube lemma applied to the locus where the two locally constant
  -- maps `(g, x) ↦ g • F (g⁻¹ * x)` and `(g, x) ↦ F x` agree.
  have := hX.discreteTopology
  have : ContinuousSMul G X.V := hX.continuousSMul
  refine ⟨inferInstance, fun F ↦ ?_⟩
  have hΦ : Continuous fun p : G × G ↦ X.ρ p.1 (F (p.1⁻¹ * p.2)) := by
    have : Continuous fun p : G × G ↦ p.1 • F (p.1⁻¹ * p.2) :=
      continuous_fst.smul (F.continuous.comp (continuous_fst.inv.mul continuous_snd))
    simpa only [TopRep.distribMulAction_smul] using this
  -- the locus where the twisted translate of `F` agrees with `F`
  have hA : IsOpen {p : G × G | X.ρ p.1 (F (p.1⁻¹ * p.2)) = F p.2} :=
    (hΦ.prodMk (F.continuous.comp continuous_snd)).isOpen_preimage
      {q : X.V × X.V | q.1 = q.2} (isOpen_discrete _)
  obtain ⟨u, v, hu, -, h1u, hv, huv⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (1 : G))) (isCompact_univ (X := G)) hA fun p hp ↦ by
      have hp1 : p.1 = 1 := hp.1
      simp only [Set.mem_ofPred_eq, hp1, inv_one, one_mul, map_one, one_apply_eq_self]
  -- the stabilizer of `F` is a subgroup containing the open neighbourhood `u` of `1`
  rw [← X.coind₁.coe_stabilizer F]
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hu.mem_nhds (h1u rfl))
    fun g hg ↦ ?_)
  rw [X.coind₁.coe_stabilizer F, Set.mem_ofPred_eq]
  ext x
  exact huv (Set.mk_mem_prod hg (hv (Set.mem_univ x)))

omit [DiscreteTopology X.V] in
/-- **The coinduced resolution of a smooth discrete representation of a compact group is smooth
discrete in every degree.** -/
theorem IsSmoothDiscrete.resolutionX (hX : IsSmoothDiscrete k X) :
    ∀ n : ℕ, IsSmoothDiscrete k (TopRep.resolutionX X n)
  | 0 => hX
  | n + 1 => (hX.resolutionX n).coind₁

end Smooth

section Vanishing

namespace ContinuousCohomology

/-! ### Vanishing on a subset

`ResolutionVanishesOn X T n F` says that the iterated map `F : C(G, C(G, …, X))` of degree `n`
vanishes on all `n`-tuples of points of `T`. For a subgroup `S` it is the vanishing of the
restriction of `F` to `S`. -/

omit [CompactSpace G] [DiscreteTopology X.V] in
/-- An element `F` of the `n`-th term `C(G, C(G, …, X))` of the coinduced resolution **vanishes on
`T`** when it is zero on every `n`-tuple of points of `T`. -/
def ResolutionVanishesOn (T : Set G) : (n : ℕ) → (TopRep.resolutionX X n).V → Prop
  | 0, v => v = 0
  | n + 1, F => ∀ g ∈ T, ResolutionVanishesOn T n ((F : C(G, (TopRep.resolutionX X n).V)) g)

omit [CompactSpace G] [DiscreteTopology X.V] in
@[simp]
theorem resolutionVanishesOn_zero (T : Set G) (v : (TopRep.resolutionX X 0).V) :
    ResolutionVanishesOn X T 0 v ↔ v = 0 :=
  Iff.rfl

omit [CompactSpace G] [DiscreteTopology X.V] in
@[simp]
theorem resolutionVanishesOn_succ (T : Set G) (n : ℕ) (F : (TopRep.resolutionX X (n + 1)).V) :
    ResolutionVanishesOn X T (n + 1) F ↔
      ∀ g ∈ T, ResolutionVanishesOn X T n ((F : C(G, (TopRep.resolutionX X n).V)) g) :=
  Iff.rfl

variable {X}

omit [CompactSpace G] [DiscreteTopology X.V] in
/-- Vanishing on a set implies vanishing on every subset. -/
theorem ResolutionVanishesOn.mono {T T' : Set G} (h : T' ⊆ T) :
    ∀ (n : ℕ) {F : (TopRep.resolutionX X n).V},
      ResolutionVanishesOn X T n F → ResolutionVanishesOn X T' n F
  | 0, _, hF => hF
  | n + 1, _, hF => fun g hg ↦ (hF g (h hg)).mono h n

/-- **Vanishing on a compact set spreads to an open neighbourhood.** An element of the coinduced
resolution of a discrete representation of a compact group that vanishes on a compact set `T`
vanishes on an open set containing `T`. -/
theorem ResolutionVanishesOn.exists_isOpen {T : Set G} (hT : IsCompact T) (n : ℕ) :
    ∀ {F : (TopRep.resolutionX X n).V}, ResolutionVanishesOn X T n F →
      ∃ W : Set G, IsOpen W ∧ T ⊆ W ∧ ResolutionVanishesOn X W n F := by
  -- On `T` the locally constant map `F` takes finitely many values, each of which vanishes on `T`
  -- in one degree less; induct on the degree.
  induction n with
  | zero => exact fun hF ↦ ⟨Set.univ, isOpen_univ, Set.subset_univ _, hF⟩
  | succ n ih =>
    intro F hF
    set F' : C(G, (TopRep.resolutionX X n).V) := F
    have : Finite (F' '' T) := ((hT.image F'.continuous).finite_of_discrete).to_subtype
    -- each of the finitely many values of `F'` on `T` vanishes on an open set containing `T`
    choose W hWopen hTW hW using fun v : F' '' T ↦
      ih (F := v) (by obtain ⟨g, hg, hgv⟩ := v.2; exact hgv ▸ hF g hg)
    refine ⟨F' ⁻¹' (F' '' T) ∩ ⋂ v, W v, ((isOpen_discrete _).preimage F'.continuous).inter
      (isOpen_iInter_of_finite fun v ↦ hWopen v),
      Set.subset_inter (Set.subset_preimage_image _ _) (Set.subset_iInter fun v ↦ hTW v),
      fun g hg ↦ ?_⟩
    exact (hW ⟨F' g, hg.1⟩).mono (Set.inter_subset_right.trans (Set.iInter_subset _ _)) n

end ContinuousCohomology

end Vanishing

/-- The continuous cohomology of a discrete representation of a compact group is discrete.

This is the statement that lets a comparison with an explicit low-degree model be phrased as an
isomorphism in `TopModuleCat k` between discrete objects rather than as an additive isomorphism
after forgetting the topology. -/
instance discreteTopology_continuousCohomology : DiscreteTopology (continuousCohomology n X) :=
  HomologicalComplex.discreteTopology_homology _ n

end TauCeti
