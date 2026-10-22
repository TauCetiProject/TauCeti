/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Quotients of normed spaces by discrete submodules are Lie groups

Let `L` be a discrete submodule of a locally compact normed space `E` over a nontrivially normed
field `𝕜`. The translation action of `L` on `E` is free and properly discontinuous
(`Submodule.properlyDiscontinuousVAdd_of_discreteTopology`) and acts by `C^n` maps
(`SetLike.contMDiffConstVAdd`), so its standard orbit space `AddAction.orbitRel.Quotient L E` is a
`C^n` manifold (`TauCeti.instIsManifoldAddQuotient`) and the orbit projection
`E → AddAction.orbitRel.Quotient L E` is a `C^n` local diffeomorphism
(`TauCeti.isLocalDiffeomorph_addQuotientMk`). This file proves that the quotient, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is a `C^n` additive
Lie group. Addition and negation are smooth because near each point of the quotient they are read
through smooth local sections of the orbit projection, namely its local inverses.

For a discrete subgroup `L : Submodule ℤ E` of a finite-dimensional complex vector space `E` and
`n = ω`, this makes `E / L` a complex Lie group. When `L` is moreover a full lattice,
`IsZLattice ℝ L`, the quotient is the complex torus `E / L`; it is compact
(`Submodule.instCompactSpaceOrbitRelQuotient`), Hausdorff
(`t2Space_of_properlyDiscontinuousVAdd_of_t2Space`), connected (`Quotient.instConnectedSpace`)
and second countable (`Submodule.instSecondCountableTopologyOrbitRelQuotient`).

## Main results

* `Submodule.instLieAddGroupOrbitRelQuotient`: the quotient of a locally compact normed space by a
  discrete submodule is a `C^n` additive Lie group; for `𝕜 = ℂ` and `n = ω` it is a complex Lie
  group.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

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
  contMDiff_neg := by
    have hq := TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(𝕜, E)) (n := n) (G := L) (M := E)
    refine (hq.contMDiff_comp_iff _root_.Quotient.mk_surjective le_rfl).1 ?_
    simpa [Function.comp_def] using hq.contMDiff.comp contDiff_neg.contMDiff
