/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# Finite quotients of tori

Let `L` be a full lattice in a finite-dimensional real normed space `E`, so that `E ⧸ L` is a
compact torus, and let `F` be a finite subgroup of `E ⧸ L`. Its preimage
`L' = F.comap (QuotientAddGroup.mk' L)` in `E` contains `L` with `L' / L ≅ F`. It is again a full
lattice: it is discrete because `L` and `F` are, and it spans `E` because `L` does. The third
isomorphism theorem (`AddSubgroup.quotientComapMk'ContinuousAddEquiv`) identifies `(E ⧸ L) ⧸ F`
with `E ⧸ L'` as topological groups. So a finite quotient of a torus is a torus of the same
dimension; in circle coordinates for a basis of `L'` it is a product of `dim E` additive circles.

This is the statement used for compact connected Lie groups with trivial semisimple part: such a
group is the quotient of a torus `ℝʳ / Λ` by the finite group `Γ / Λ`, and is therefore itself a
torus.

## Main results

* `AddSubgroup.instIsZLatticeComapMk'`: the preimage `L'` in `E` of a finite subgroup of `E ⧸ L`
  is a full lattice. It is discrete by `AddSubgroup.instDiscreteTopologyComapMk'`.
* `AddSubgroup.nonempty_quotient_continuousAddEquiv_unitAddTorus`: `(E ⧸ L) ⧸ F` is a product
  of additive circles, indexed by any finite type of cardinality `dim E`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3, and Chapter V, Theorem (8.1).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.31.
-/

public section

noncomputable section

open Module QuotientAddGroup

namespace AddSubgroup

/-- The preimage in `E` of a finite subgroup of the torus `E ⧸ L` is a full lattice. -/
instance instIsZLatticeComapMk' {K : Type*} [NormedField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace K E] (L : AddSubgroup E) [DiscreteTopology L] [IsZLattice K L.toIntSubmodule]
    (F : AddSubgroup (E ⧸ L)) [Finite F] : IsZLattice K (F.comap (mk' L)).toIntSubmodule :=
  IsZLattice.of_le (L₁ := L.toIntSubmodule) (toIntSubmodule.monotone (le_comap_mk' L F))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : AddSubgroup E) [DiscreteTopology L] [IsZLattice ℝ L.toIntSubmodule]
  (F : AddSubgroup (E ⧸ L)) [Finite F]

/-- **A finite quotient of a torus is a product of circles.** For a finite subgroup `F` of the
torus `E ⧸ L`, the quotient `(E ⧸ L) ⧸ F` is isomorphic as a topological group to the product of
`dim E` additive circles, indexed by any finite type `ι` of that cardinality. -/
theorem nonempty_quotient_continuousAddEquiv_unitAddTorus {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank ℝ E) :
    Nonempty ((E ⧸ L) ⧸ F ≃ₜ+ UnitAddTorus ι) := by
  -- Circle coordinates in a `ℤ`-basis of the full lattice `L' = F.comap (mk' L)`, reindexed by `ι`.
  set L' := (F.comap (mk' L)).toIntSubmodule
  have := ZLattice.module_free ℝ L'
  have := ZLattice.module_finite ℝ L'
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L') = Fintype.card ι := by
    rw [hι, ← ZLattice.rank ℝ L', finrank_eq_card_chooseBasisIndex]
  let b := (Free.chooseBasis ℤ L').reindex (Fintype.equivOfCardEq hcard)
  exact ⟨(quotientComapMk'ContinuousAddEquiv L F).trans b.quotientLatticeEquiv⟩

end AddSubgroup
