/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Divisor
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.FreeLocus
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic

/-!
# The Riemann–Hurwitz formula for finite-index maps of Fuchsian quotients

Let `Γ ≤ PSL(2, ℝ)` be discrete. Deleting the elliptic orbits and the adjoined cusps from the
compactified quotient `X(Γ)` leaves exactly the orbit space of the free locus of `Γ`, the
points of `ℍ` with trivial stabilizer
(`Subgroup.CompactifiedQuotient.freeLocusQuotientHomeomorph`, in
`TauCeti.Analysis.Complex.Fuchsian.Compactification.FreeLocus`). When `X(Γ)` is compact, only
finitely many points are deleted.

For a discrete `Δ ≤ Γ` of finite index, the map `X(Δ) → X(Γ)` is ramified only over elliptic
orbits and cusps of `Γ`. Applying the topological branched-cover formula
`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`
with that finite set of punctures, the degree being the index `[Γ : Δ]`, gives the
Riemann–Hurwitz formula for Fuchsian groups in Euler-characteristic form,

`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - ∑_{interior} (e - 1) - ∑_{cusps} (e - 1)`,

where `e` is the index of the elliptic stabilizer of `Δ` in that of `Γ` at an interior orbit and
the index of the boundary stabilizers at a cusp. Euler characteristics are the finite-CW Euler
characteristics `TauCeti.eulerChar`. The finite-CW-type hypotheses are on the two compactified
quotients and on the free-locus quotient of `Γ`, an object attached to `Γ` alone.

## Main results

* `TauCeti.Fuchsian.branchValues_subset_ellipticOrbits_union_cusps`: a finite-index map of
  compactified quotients branches only over elliptic orbits and cusps.
* `TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree`: the
  Riemann–Hurwitz formula `χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`, with `R` the ramification degree.
* `TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_interior_sub_cusps`: the
  same, with `R` split into elliptic stabilizer indices and cusp stabilizer indices.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §3.1 (the genus of `X(Γ)` from Riemann–Hurwitz).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §17 (the topological Riemann–Hurwitz formula).
-/

public noncomputable section

open Function MulAction Set Topology UpperHalfPlane
open Subgroup Subgroup.CompactifiedQuotient TauCeti TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

/-- **A finite-index map of compactified Fuchsian quotients branches only over elliptic orbits
and cusps.** Over an orbit of points with trivial stabilizer in `Γ`, every elliptic stabilizer
index is one. -/
theorem branchValues_subset_ellipticOrbits_union_cusps :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    (compactifiedQuotientFiniteHolomorphicMap h).branchValues ⊆
      ofQuotient '' Γ.ellipticOrbits ∪ range ofCusp := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  intro y hy
  obtain ⟨x, rfl, hx⟩ := (FiniteHolomorphicMap.mem_branchValues_iff _ y).mp hy
  rw [coe_compactifiedQuotientFiniteHolomorphicMap] at hx ⊢
  cases x with
  | ofCusp C => exact Or.inr ⟨cuspOrbitMap h C, (compactifiedQuotientMap_ofCusp h C).symm⟩
  | ofQuotient q =>
    induction q using Quotient.inductionOn with
    | h z =>
      rw [localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex] at hx
      refine Or.inl ⟨Quotient.mk (orbitRel Γ ℍ) z, ?_, ?_⟩
      swap
      · rw [compactifiedQuotientMap_ofQuotient]
        rfl
      rw [quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
      intro hz
      rw [ellipticRamificationIndex_eq_one_of_stabilizer_eq_bot h z hz] at hx
      exact lt_irrefl 1 hx

variable [hcompact : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  CompactSpace Δ.CompactifiedQuotient]
variable [hcw : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  FiniteCWType Δ.CompactifiedQuotient]
variable [FiniteCWType Γ.CompactifiedQuotient] [FiniteCWType (orbitRel.Quotient Γ (freeLocus Γ ℍ))]

/-- **The Riemann–Hurwitz formula for Fuchsian groups.** Let `Δ ≤ Γ` be discrete subgroups of
`PSL(2, ℝ)` of finite index, with `X(Δ)` compact. If the compactified quotients and the
free-locus quotient of `Γ` have finite CW type, then
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`, where `R` is the ramification degree of `X(Δ) → X(Γ)`. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let f := compactifiedQuotientFiniteHolomorphicMap h
  have : CompactSpace Γ.CompactifiedQuotient :=
    ⟨f.surjective.range_eq ▸ isCompact_range f.holomorphic.continuous⟩
  have := (freeLocusQuotientHomeomorph Γ).symm.finiteCWType
  have hR := f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset
    finite_ellipticOrbits_union_cusps (branchValues_subset_ellipticOrbits_union_cusps h)
  rwa [coe_compactifiedQuotientFiniteHolomorphicMap, degree_compactifiedQuotientMap] at hR

/-- **The Riemann–Hurwitz formula for Fuchsian groups, with explicit ramification.** Under the
hypotheses of
`TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree`,
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - ∑_q (e_q - 1) - ∑_C (e_C - 1)`. Here `q` runs over the orbits of
`Δ` on `ℍ`, with `e_q` the index of the stabilizer in `Δ` of a representative in its stabilizer
in `Γ`, and `C` runs over the cusp orbits of `Δ`, with `e_C` the index of the boundary
stabilizers at a representative cusp. Both sums have finite support, and the formula holds for
any choice of representatives. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_interior_sub_cusps
    (z : orbitRel.Quotient Δ ℍ → ℍ) (hz : ∀ q, Quotient.mk'' (z q) = q)
    (c : Δ.CuspOrbit → Δ.cuspPoints) (hc : ∀ C, Δ.cuspOrbitMk (c C) = C) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        (∑ᶠ q : orbitRel.Quotient Δ ℍ, (ellipticRamificationIndex h (z q) - 1) : ℕ) -
        (∑ᶠ C : Δ.CuspOrbit,
          ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1) : ℕ) := by
  rw [eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree h,
    ramificationDegree_eq_interior_add_cusps h z hz c hc]
  push_cast
  ring

end TauCeti.Fuchsian

end
