/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.FundamentalGroup.RelCWComplex
public import TauCeti.Geometry.Manifold.Morse.Exhaustion
public import TauCeti.Geometry.Manifold.Morse.RelCWComplex

/-!
# Critical points of index one and the fundamental group

Let `f` be a Morse function on a boundaryless manifold `M`, and write `M_b = {f ≤ b}`. Crossing a
critical level attaches to the lower sublevel one cell for each critical point of the level, of
dimension its Morse index (`TauCeti.IsMorse.exists_relCWComplex_sublevel_deformation`), and cells of
dimension other than one create no loops
(`TauCeti.subsingleton_fundamentalGroup_of_isEmpty_cell_one`). Across a compact band without
critical points the sublevels are homotopy equivalent (`TauCeti.exists_sublevelHomotopyEquiv`).
So critical points of index one are the only ones through which loops can appear:

* if `f⁻¹[a, b]` is a compact band between regular values containing no critical point of index
  one, and every loop in `M_a` is nullhomotopic, then so is every loop in `M_b`
  (`TauCeti.IsMorse.subsingleton_fundamentalGroup_sublevel_of_subsingleton`);
* if the regular sublevel `M_b` is compact and contains no critical point of index one, every loop
  in `M_b` is nullhomotopic
  (`TauCeti.IsMorse.subsingleton_fundamentalGroup_sublevel_of_manifoldMorseIndex_ne_one`);
* if `f` is proper and bounded below and has no critical point of index one, every loop in `M` is
  nullhomotopic (`TauCeti.IsMorse.subsingleton_fundamentalGroup_of_manifoldMorseIndex_ne_one`),
  since a loop has compact image, which lies in a regular sublevel. In particular a connected
  such `M` is simply connected
  (`TauCeti.IsMorse.simplyConnectedSpace_of_manifoldMorseIndex_ne_one`).

Conversely, a proper Morse function bounded below on a manifold with a nontrivial fundamental group
has a critical point of index one (`TauCeti.IsMorse.exists_manifoldMorseIndex_eq_one`), so its
count `c₁` of critical points of index one is nonzero (`TauCeti.IsMorse.criticalCount_one_ne_zero`).
This is an obstruction to perfection that homology does not see: on a compact manifold with a
nontrivial fundamental group whose first Betti number over a division ring `k` vanishes, such as
`ℝℙⁿ` for `n ≥ 2` over `ℚ`, the weak Morse inequality `b₁ ≤ c₁` is strict
(`TauCeti.IsMorse.finrank_singularHomology_one_lt_toNat_criticalCount`). Hence no Morse function
on such a manifold has exactly `bⱼ` critical points of index `j` in every degree `j`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1, 3.2 and 3.5.
* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. (N.S.) 7 (1982),
  331–358, §1.
-/

public section

noncomputable section

open Set Topology
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b : ℝ}

/-- **Crossing a band without critical points of index one creates no loops.** Let `f` be a Morse
function and `a ≤ b` regular values of `f` with compact band `f⁻¹[a, b]`, and suppose no critical
point in the band has Morse index one. If every loop in the sublevel `{f ≤ a}` is nullhomotopic,
then so is every loop in the sublevel `{f ≤ b}`. -/
theorem IsMorse.subsingleton_fundamentalGroup_sublevel_of_subsingleton (hf : IsMorse I f)
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hd : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, manifoldMorseIndex I f p ≠ 1)
    (hsub : ∀ x : {x | f x ≤ a}, Subsingleton (FundamentalGroup ({x | f x ≤ a} : Set M) x))
    (x : {x | f x ≤ b}) : Subsingleton (FundamentalGroup ({x | f x ≤ b} : Set M) x) := by
  refine hf.band_induction (P := fun s t _ ↦
      (∀ x : {x | f x ≤ s}, Subsingleton (FundamentalGroup ({x | f x ≤ s} : Set M) x)) →
        ∀ x : {x | f x ≤ t}, Subsingleton (FundamentalGroup ({x | f x ≤ t} : Set M) x))
    hab hcompact ha hb
    (fun s t hst hcompact hcrit hs y ↦ ?_) (fun p hp hap hpb δ hδ hcompact ↦ ?_)
    (fun _ _ _ _ _ _ h₁ h₂ hs ↦ h₂ (h₁ hs)) hsub x
  · -- Across a band without critical points the sublevels are homotopy equivalent.
    obtain ⟨e, -⟩ := exists_sublevelHomotopyEquiv hf.contMDiff hst hcompact
      fun z hz₁ hz₂ hz ↦ hcrit z (mem_criticalPoints_iff_mfderiv_eq_zero.2 hz) ⟨hz₁, hz₂⟩
    have := hs (e.symm.toFun y)
    exact (e.symm.fundamentalGroupMulEquiv y).injective.subsingleton
  · -- Across the level `f p`, the upper sublevel deformation retracts onto the lower sublevel
    -- with cells attached along it, one for each critical point of the level, of dimension its
    -- index. None of them has dimension one.
    obtain ⟨ε, hε, hεδ, C, _, -, hC, hcells, hfr, r, hr, ⟨G⟩⟩ :=
      hf.exists_relCWComplex_sublevel_deformation hδ hcompact
    refine ⟨ε, hε, hεδ, fun hs y ↦ ?_⟩
    have : IsEmpty (RelCWComplex.cell C 1) := (hcells 1).some.isEmpty_congr.2
      ⟨fun q ↦ hd q.1 ⟨q.1.2.1, by
        have : f q.1 = f p := q.1.2.2
        constructor <;> linarith⟩ q.2⟩
    have hCsub := subsingleton_fundamentalGroup_of_isEmpty_cell_one this hfr hs
    -- The complex is a strong deformation retract of the upper sublevel.
    let e : ContinuousMap.HomotopyEquiv C {x | f x ≤ f p + ε} :=
      { toFun := ContinuousMap.inclusion hC
        invFun := r
        left_inv := by
          rw [show r.comp (ContinuousMap.inclusion hC) = ContinuousMap.id C from
            ContinuousMap.ext hr]
        right_inv := ⟨G.toHomotopy⟩ }
    have := hCsub (e.symm.toFun y)
    exact (e.symm.fundamentalGroupMulEquiv y).injective.subsingleton

/-- **A compact regular sublevel without critical points of index one has no loops.** Let `f` be a
Morse function and `b` a regular value of `f` with compact sublevel `{f ≤ b}`, and suppose no
critical point in this sublevel has Morse index one. Then every loop in `{f ≤ b}` is
nullhomotopic. -/
theorem IsMorse.subsingleton_fundamentalGroup_sublevel_of_manifoldMorseIndex_ne_one
    (hf : IsMorse I f) (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hd : ∀ p ∈ criticalPoints I f, f p ≤ b → manifoldMorseIndex I f p ≠ 1)
    (x : {x | f x ≤ b}) : Subsingleton (FundamentalGroup ({x | f x ≤ b} : Set M) x) := by
  -- Start from a value `a` below every value of `f`, where the sublevel is empty.
  have hfc : Continuous f := hf.contMDiff.continuous
  obtain ⟨a, hab, ha⟩ := exists_le_forall_lt_of_isCompact_sublevel hcompact hfc.continuousOn
  refine hf.subsingleton_fundamentalGroup_sublevel_of_subsingleton hab
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc) fun y hy ↦ hy.2)
    (isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ (ha p).ne' hp) hb
    (fun p hp ↦ hd p hp.1 hp.2.2) (fun y ↦ ((ha y).not_ge y.2).elim) x

/-- **A proper Morse function without critical points of index one leaves no loops.** Let `f` be a
proper Morse function, bounded below, with no critical point of Morse index one. Then every loop
in `M` is nullhomotopic. -/
theorem IsMorse.subsingleton_fundamentalGroup_of_manifoldMorseIndex_ne_one (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hd : ∀ p ∈ criticalPoints I f, manifoldMorseIndex I f p ≠ 1) (x : M) :
    Subsingleton (FundamentalGroup M x) := by
  obtain ⟨c, K, -, -, hreg, hK, -, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  refine subsingleton_fundamentalGroup_iff.2 fun γ ↦ ?_
  -- The loop has compact image, which lies in a regular sublevel `K j = {f ≤ c j}`.
  obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact (isCompact_range γ.continuous)
  have hKj : (K j : Set M) = {x | f x ≤ c j} := hK j
  have hmem (t : unitInterval) : γ t ∈ {x | f x ≤ c j} := hKj ▸ hj (mem_range_self t)
  have hx : x ∈ {x | f x ≤ c j} := γ.source ▸ hmem 0
  have := hf.subsingleton_fundamentalGroup_sublevel_of_manifoldMorseIndex_ne_one
    (hKj ▸ K.isCompact j) (hreg j) (fun p hp _ ↦ hd p hp) ⟨x, hx⟩
  exact Path.Homotopic.refl_of_forall_mem_of_subsingleton (x := ⟨x, hx⟩) γ hmem

/-- **A proper Morse function without critical points of index one forces simple connectivity.**
A connected manifold carrying a proper Morse function, bounded below, with no critical point of
Morse index one is simply connected. -/
theorem IsMorse.simplyConnectedSpace_of_manifoldMorseIndex_ne_one [ConnectedSpace M]
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hd : ∀ p ∈ criticalPoints I f, manifoldMorseIndex I f p ≠ 1) : SimplyConnectedSpace M := by
  -- A connected manifold with a boundaryless model is path connected.
  have : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have := hf.subsingleton_fundamentalGroup_of_manifoldMorseIndex_ne_one hp hbdd hd
    (Classical.arbitrary M)
  exact simplyConnectedSpace_of_subsingleton_fundamentalGroup (Classical.arbitrary M)

/-- **A nontrivial fundamental group forces a critical point of index one.** A proper Morse
function, bounded below, on a manifold whose fundamental group is nontrivial at some basepoint has
a critical point of Morse index one. -/
theorem IsMorse.exists_manifoldMorseIndex_eq_one (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (x : M) [Nontrivial (FundamentalGroup M x)] :
    ∃ p ∈ criticalPoints I f, manifoldMorseIndex I f p = 1 := by
  by_contra! h
  have := hf.subsingleton_fundamentalGroup_of_manifoldMorseIndex_ne_one hp hbdd h x
  exact false_of_nontrivial_of_subsingleton (FundamentalGroup M x)

/-- **A nontrivial fundamental group forces critical points of index one.** A proper Morse
function, bounded below, on a manifold whose fundamental group is nontrivial at some basepoint has
a nonzero number of critical points of Morse index one. -/
theorem IsMorse.criticalCount_one_ne_zero (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (x : M) [Nontrivial (FundamentalGroup M x)] :
    criticalCount I f 1 ≠ 0 := by
  obtain ⟨p, hp, hp₁⟩ := hf.exists_manifoldMorseIndex_eq_one hp hbdd x
  rw [criticalCount_def, Ne, encard_eq_zero]
  exact nonempty_iff_ne_empty.1 ⟨p, hp, hp₁⟩

/-- **The fundamental group obstructs perfection.** Let `f` be a Morse function on a compact
manifold whose fundamental group is nontrivial at some basepoint, and let `k` be a division ring
over which the first Betti number `b₁ = dim_k H₁(M; k)` vanishes. Then the weak Morse inequality
`b₁ ≤ c₁` is strict: `f` has more critical points of index one than `b₁`, so it does not have
exactly `bⱼ` critical points of index `j` in every degree. This is the compact case of
`TauCeti.IsMorse.criticalCount_one_ne_zero`, read against the vanishing first Betti number. -/
theorem IsMorse.finrank_singularHomology_one_lt_toNat_criticalCount [CompactSpace M]
    (hf : IsMorse I f) (x : M) [Nontrivial (FundamentalGroup M x)] (k : Type u) [DivisionRing k]
    (hb : Module.finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) = 0) :
    Module.finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) < (criticalCount I f 1).toNat := by
  have hc := hf.criticalCount_one_ne_zero hf.contMDiff.continuous.isProperMap
    (isCompact_range hf.contMDiff.continuous).bddBelow x
  have hfin : criticalCount I f 1 ≠ ⊤ := by
    rw [criticalCount_def, Ne, encard_eq_top_iff, not_infinite]
    exact hf.finite_criticalPoints.subset fun q hq ↦ hq.1
  rw [hb]
  exact Nat.pos_of_ne_zero fun h ↦ (ENat.toNat_eq_zero.1 h).elim hc hfin

end TauCeti
