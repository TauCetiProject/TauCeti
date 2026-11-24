/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ExponentP
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import Mathlib.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
import TauCeti.LinearAlgebra.Exact

/-!
# Testing cohomological dimension on finite simple modules

For a prime `p` and a compact group `G`, the bound `cd_p G ≤ n` can be tested in the single
degree `n + 1` on the finite discrete `G`-modules that are simple `𝔽_p`-representations of `G`:
nonzero `ZMod p`-modules on which `G` acts with no `G`-stable additive subgroups other than `0` and
the whole module. This is the last reduction in the dévissage of Neukirch–Schmidt–Wingberg (3.3.2),
following the reduction to finite modules killed by `p`
(`TauCeti.cohomologicalDimensionLE_iff_forall_finite_nsmul_eq_zero`).

A nonzero finite module `M` killed by `p` is a `ZMod p`-representation of `G`, and its lattice of
subrepresentations is finite, so it has an atom `P`: a minimal nonzero `G`-stable subgroup, which
carries an irreducible representation. The quotient `M ⧸ P` is again killed by `p` and is smaller,
and exactness of `Hⁿ(G, P) → Hⁿ(G, M) → Hⁿ(G, M ⧸ P)` gives the induction. No compactness is
needed for this fixed-degree step.

Simplicity is stated as irreducibility of `Representation.ofDistribMulAction (ZMod p) G M`. A
finite discrete `G`-module `M` is acted on trivially by an open normal subgroup `U`, for instance
`TauCeti.openActionKernel G M`, and then `M` is also an object of `Rep (ZMod p) (G ⧸ U)`; that
object is simple exactly when the representation of `G` is irreducible, whichever such `U` is
chosen (`Representation.isIrreducible_ofQuotient_iff`, `Rep.simple_ofQuotient_iff`).

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_forall_isIrreducible`: the
  fixed-degree reduction from finite discrete modules killed by `p` to finite simple ones.
* `TauCeti.cohomologicalDimensionLE_iff_forall_isIrreducible` and
  `TauCeti.cohomologicalDimensionAt_le_iff_forall_isIrreducible`: `cd_p G ≤ n` is tested in degree
  `n + 1` on finite discrete simple `𝔽_p`-representations of `G`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Proposition (3.3.2).
* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.1, Prop. 11.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G]

namespace ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Vanishing of `Hⁿ(G, -)` on the finite discrete simple `𝔽_p`-representations of `G` implies
vanishing of `Hⁿ(G, M)` for every finite discrete `G`-module `M` killed by `p`. -/
theorem subsingleton_continuousCohomology_of_forall_isIrreducible [Fact p.Prime] (n : ℕ)
    (h : ∀ (A : Type u) [AddCommGroup A] [Module (ZMod p) A] [TopologicalSpace A]
      [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
      (Representation.ofDistribMulAction (ZMod p) G A).IsIrreducible →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  -- strong induction on the order of the coefficient module
  suffices H : ∀ (k : ℕ) (A : Type u) [AddCommGroup A] [TopologicalSpace A]
      [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
      (∀ a : A, p • a = 0) → Nat.card A = k →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)) from H _ M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A _ _ _ _ _ _ hA hk
  rcases subsingleton_or_nontrivial A with _ | _
  · exact subsingleton_continuousCohomology_ofDiscreteModule_of_subsingleton A n
  -- split off a simple subrepresentation `P`
  have := AddCommGroup.zmodModule hA
  obtain ⟨W, hW, hWirr⟩ := Representation.exists_isIrreducible_subrepresentation
    (Representation.ofDistribMulAction (ZMod p) G A)
  let P : AddSubgroup A := W.toSubmodule.toAddSubgroup
  have hP : ∀ g : G, ∀ x ∈ P, g • x ∈ P := fun g _ hx ↦ W.apply_mem_toSubmodule g hx
  let := P.restrictDistribMulAction hP
  have hPcard : 1 < Nat.card P := by
    have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 fun h ↦
      hW (Subrepresentation.toSubmodule_injective h)
    exact Finite.one_lt_card_iff_nontrivial.2 this
  -- `W.toSubmodule` and `P` have the same elements, and the identity between them is additive,
  -- hence `ZMod p`-linear; it is equivariant since `g` acts on both as `g • ·` on `A`
  have hPirr : (Representation.ofDistribMulAction (ZMod p) G P).IsIrreducible := by
    let e : W.toSubmodule ≃+ P := AddEquiv.refl _
    exact Representation.isIrreducible_of_linearEquiv
      { e with map_smul' := ZMod.map_smul e } (fun _ _ ↦ rfl) hWirr
  let := P.quotientDistribMulAction hP
  have : ContinuousSMul G P := P.restrictDistribMulAction_continuousSMul hP
  have : ContinuousSMul G (A ⧸ P) := P.quotientDistribMulAction_continuousSMul hP
  let E := DiscreteShortExact.ofAddSubgroup P hP
  have := h P hPirr
  -- the quotient is killed by `p` and smaller, so the induction hypothesis applies to it
  have : Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G (A ⧸ P))) := by
    refine ih _ ?_ (A ⧸ P) (E.nsmul_eq_zero_right hA) rfl
    rw [← hk, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup P]
    exact lt_mul_of_one_lt_right Nat.card_pos hPcard
  exact subsingleton_of_exact (E.longExact_exact₂ n)

end ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- For a prime `p` and a compact group `G`, `CohomologicalDimensionLE p G n` can be tested in
degree `n + 1` on the finite discrete `G`-modules that are simple `𝔽_p`-representations of `G`. -/
theorem cohomologicalDimensionLE_iff_forall_isIrreducible [Fact p.Prime] (n : ℕ) :
    CohomologicalDimensionLE.{u} p G n ↔
      ∀ (M : Type u) [AddCommGroup M] [Module (ZMod p) M] [TopologicalSpace M]
        [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M],
        (Representation.ofDistribMulAction (ZMod p) G M).IsIrreducible →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionLE_iff_forall_finite_nsmul_eq_zero (Fact.out : p.Prime).ne_zero]
  refine ⟨fun h M _ _ _ _ _ _ _ _ ↦ h M fun m ↦ ?_, fun h M _ _ _ _ _ _ hM ↦
    ContinuousCohomology.subsingleton_continuousCohomology_of_forall_isIrreducible (n + 1) h M hM⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

/-- For a prime `p` and a compact group `G`, the bound `cd_p G ≤ n` is equivalent to the vanishing
of `Hⁿ⁺¹(G, M)` for every finite discrete `G`-module `M` that is a simple `𝔽_p`-representation of
`G`. -/
theorem cohomologicalDimensionAt_le_iff_forall_isIrreducible (p : ℕ) [Fact p.Prime] (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (n : ℕ) :
    cohomologicalDimensionAt.{u} p G ≤ n ↔
      ∀ (M : Type u) [AddCommGroup M] [Module (ZMod p) M] [TopologicalSpace M]
        [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M],
        (Representation.ofDistribMulAction (ZMod p) G M).IsIrreducible →
        Subsingleton (continuousCohomology (n + 1) (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_forall_isIrreducible]

end TauCeti
