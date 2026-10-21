/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
-- A complex `E` is finite-dimensional over `ℝ`, so the instances below apply to complex tori.
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Complex tori

Let `L : Submodule ℤ E` be a discrete subgroup of a finite-dimensional complex normed space `E`.
The translation action of `L` on `E` is free and properly discontinuous
(`Submodule.properlyDiscontinuousVAdd_of_discreteTopology`) and acts by biholomorphisms
(`SetLike.contMDiffConstVAdd`), so its standard orbit space `AddAction.orbitRel.Quotient L E` is a
complex manifold (`TauCeti.instIsManifoldAddQuotient`) and the orbit projection
`E → AddAction.orbitRel.Quotient L E` is a local biholomorphism
(`TauCeti.isLocalDiffeomorph_addQuotientMk`). This file proves that the quotient, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is a complex Lie
group, and that it is compact when `L` is a full lattice, `IsZLattice ℝ L`: it is then the complex
torus `E / L`. The quotient is also Hausdorff (`t2Space_of_properlyDiscontinuousVAdd_of_t2Space`)
and connected (`Quotient.instConnectedSpace`) by Mathlib's instances, and second countable by an
instance below.

The Lie group statement holds over any nontrivially normed field `𝕜`, for a discrete submodule of
a locally compact normed space and at every regularity `n`. Addition and negation are smooth
because near each point of the quotient they are read through smooth local sections of the orbit
projection, namely its local inverses.

## Main results

* `Submodule.instLieAddGroupOrbitRelQuotient`: the quotient of a locally compact normed space by a
  discrete submodule is a `C^n` additive Lie group; for `𝕜 = ℂ` and `n = ω` it is a complex Lie
  group.
* `Submodule.instCompactSpaceOrbitRelQuotient`: the quotient by a full lattice is compact.
* `Submodule.instSecondCountableTopologyOrbitRelQuotient`: the quotient of a second countable
  space by translations is second countable.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

section LieGroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [LocallyCompactSpace E] {R : Type*} [Ring R] [Module R E] (L : Submodule R E)
  [DiscreteTopology L] {n : ℕ∞ω}

/-- Every point of the quotient of `E` by a discrete submodule has a local section of the orbit
projection that is `C^n` at the point. -/
private theorem exists_contMDiffAt_section (a : AddAction.orbitRel.Quotient L E) :
    ∃ σ : AddAction.orbitRel.Quotient L E → E, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n σ a ∧
      ∀ᶠ b in 𝓝 a, Quotient.mk (AddAction.orbitRel L E) (σ b) = b := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
  have hx := TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n) (G := L) (M := E) x
  exact ⟨hx.localInverse, hx.contMDiffAt_localInverse, hx.localInverse_eventuallyEq_right⟩

/-- The quotient of a locally compact normed space `E` over `𝕜` by a discrete submodule `L` is a
`C^n` additive Lie group, for its quotient manifold structure and the additive group structure of
`E ⧸ L`. For a discrete subgroup `L : Submodule ℤ E` of a finite-dimensional complex vector space
`E` and `n = ω` it is a complex Lie group. -/
instance Submodule.instLieAddGroupOrbitRelQuotient :
    LieAddGroup 𝓘(𝕜, E) n (AddAction.orbitRel.Quotient L E) where
  contMDiff_add := by
    rintro ⟨a, b⟩
    obtain ⟨σ, hσ, hσa⟩ := exists_contMDiffAt_section (𝕜 := 𝕜) L (n := n) a
    obtain ⟨τ, hτ, hτb⟩ := exists_contMDiffAt_section (𝕜 := 𝕜) L (n := n) b
    have hq := (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n) (G := L)
      (M := E)).contMDiff
    refine (hq.contMDiffAt.comp (a, b) ((hσ.comp (a, b) contMDiffAt_fst).add
      (hτ.comp (a, b) contMDiffAt_snd))).congr_of_eventuallyEq ?_
    filter_upwards [hσa.prodMk_nhds hτb] with p hp
    simp [hp.1, hp.2]
  contMDiff_neg a := by
    obtain ⟨σ, hσ, hσa⟩ := exists_contMDiffAt_section (𝕜 := 𝕜) L (n := n) a
    have hq := (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n) (G := L)
      (M := E)).contMDiff
    refine (hq.contMDiffAt.comp a hσ.neg).congr_of_eventuallyEq ?_
    filter_upwards [hσa] with b hb
    simp [hb]

end LieGroup

/-- The quotient of a finite-dimensional real normed space by a full lattice is compact: it is the
image of a compact fundamental parallelepiped of the lattice. -/
instance Submodule.instCompactSpaceOrbitRelQuotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : CompactSpace (AddAction.orbitRel.Quotient L E) := by
  refine isCompact_univ_iff.1 ?_
  rw [← Set.range_eq_univ.2 _root_.Quotient.mk_surjective]
  refine IsZLattice.isCompact_range_of_periodic L _ continuous_quotient_mk' fun z w hw ↦ ?_
  rw [Submodule.orbitRelQuotient_mk_add, (L.orbitRelQuotient_mk_eq_zero_iff).2 hw, add_zero]

/-- The quotient of a second countable topological module by translations by a submodule is
second countable. -/
instance Submodule.instSecondCountableTopologyOrbitRelQuotient {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [SecondCountableTopology M] (p : Submodule R M) :
    SecondCountableTopology (AddAction.orbitRel.Quotient p M) :=
  ContinuousConstVAdd.secondCountableTopology
