/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.LowDimTopology.Heegaard.Admissibility
public import TauCeti.LowDimTopology.Heegaard.Nice
public import TauCeti.LowDimTopology.Heegaard.RelativeGrading

/-!
# The combinatorial hat differential of a Heegaard diagram

The hat chain group `\widehat{CF}` of a pointed Heegaard diagram is the `𝔽₂`-vector space on its
generators. Its differential sends a generator `x` to the sum over generators `y` of the number,
modulo two, of holomorphic disks from `x` to `y` of Maslov index one avoiding the basepoints. The
domain of such a disk is a nonnegative domain from `x` to `y` with multiplicity zero at every
basepoint and Maslov index one. Sarkar and Wang show that in a genuine nice Heegaard diagram,
one on a surface in which every region containing no basepoint is an embedded disk with two or
four corners, every such domain is an empty embedded bigon or an empty embedded rectangle, and
each of those is the domain of exactly one holomorphic disk modulo translation. So in a genuine
nice diagram the differential counts these domains themselves, which is the combinatorial chain
complex of Sarkar–Wang and Ozsváth–Stipsicz–Szabó.

This file defines that count for the abstract region incidence data
`TauCeti.HeegaardRegionSystem` with region Euler characteristics `χ`. The counted domains from
`x` to `y` form the set `H.hatDomains χ x y`. It is finite when the diagram is weakly admissible,
and the matrix coefficient `H.hatCoefficient χ x y` is its cardinality modulo two. The linear
map `H.hatDifferential χ` on `H.Generator →₀ ZMod 2` has these coefficients. The abstract
condition `TauCeti.HeegaardRegionSystem.IsNice` only records that every region containing no
basepoint has Euler characteristic one and two or four corners; it does not say that `H` and `χ`
come from regions of an actual surface. The agreement of this count with the holomorphic
differential therefore applies only to incidence data realized by a genuine nice Heegaard
diagram with these region Euler characteristics, and neither that realization nor the agreement
is formalized here. Otherwise the count of domains need not be the count of holomorphic disks.
In a diagram that is not weakly admissible the set can be infinite, in which case the
coefficient is `0` by the convention of `Set.ncard`; the results below carry the combinatorial
hypotheses under which the count is finite and has the properties listed next. That the
differential squares to zero on nice diagrams is not proved here.

The basic properties of the count are the following. In a weakly admissible diagram nothing is
counted from a generator to itself, since a nonnegative periodic domain vanishes. Without nonzero
periodic domains at most one domain is counted between two generators, so each coefficient is `1`
exactly when a counted domain exists. In a nice weakly admissible diagram a counted domain
changes the points of `x` on exactly one or two `α`-curves, as a bigon or a rectangle does. In a
singly pointed diagram with a well-defined relative grading, the differential lowers it by one.

## Main definitions

* `TauCeti.HeegaardRegionSystem.hatDomains`: the nonnegative domains of Maslov index one from `x`
  to `y` avoiding the basepoints.
* `TauCeti.HeegaardRegionSystem.hatCoefficient`: their number modulo two.
* `TauCeti.HeegaardRegionSystem.hatDifferential`: the `ZMod 2`-linear map on the free module on
  generators with these matrix coefficients.

## Main results

* `TauCeti.HeegaardRegionSystem.WeaklyAdmissible.finite_hatDomains`: in a weakly admissible
  diagram only finitely many domains are counted.
* `TauCeti.HeegaardRegionSystem.WeaklyAdmissible.hatCoefficient_self`: in a weakly admissible
  diagram the differential has no diagonal terms.
* `TauCeti.HeegaardRegionSystem.hatCoefficient_eq_one_iff_of_periodicDomains_eq_bot`: without
  nonzero periodic domains, a coefficient is `1` exactly when some domain is counted.
* `TauCeti.HeegaardRegionSystem.hatDifferential_single_apply`: the matrix coefficients of the
  differential.
* `TauCeti.HeegaardRegionSystem.hatDifferential_eq_zero_iff`: the differential vanishes exactly
  when all of its coefficients do.
* `TauCeti.HeegaardRegionSystem.IsNice.hammingDist_eq_one_or_eq_two_of_hatCoefficient_ne_zero`:
  in a nice weakly admissible diagram the differential only joins generators differing on one
  or two `α`-curves.
* `TauCeti.HeegaardRegionSystem.relativeGrading_eq_one_of_hatCoefficient_ne_zero`: the
  differential lowers the relative Maslov grading by one.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.1 (the hat chain complex).
* S. Sarkar and J. Wang, *An algorithm for computing some Heegaard Floer homologies*, Ann. of
  Math. **171** (2010), [arXiv:math/0607777](https://arxiv.org/abs/math/0607777), §3 (in a genuine
  nice diagram the differential counts the positive index-one domains avoiding the basepoints,
  each of which is an empty embedded bigon or rectangle).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830)
  (the combinatorial chain complex of a nice diagram with several basepoints).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

section Domains

variable (H) in
/-- The domains counted by the hat differential from the generator `x` to the generator `y`:
the nonnegative domains from `x` to `y` with multiplicity zero at every basepoint and Maslov
index one, for the region Euler characteristics `χ`. -/
def hatDomains (χ : Region → ℤ) (x y : H.Generator) : Set (Region → ℤ) :=
  {D | H.IsDomainBetween x y D ∧ (∀ z, D (H.basepoint z) = 0) ∧ 0 ≤ D ∧
    H.maslovIndex χ x y D = 1}

variable {χ : Region → ℤ} {x y : H.Generator} {D : Region → ℤ}

@[simp]
theorem mem_hatDomains_iff : D ∈ H.hatDomains χ x y ↔
    H.IsDomainBetween x y D ∧ (∀ z, D (H.basepoint z) = 0) ∧ 0 ≤ D ∧
      H.maslovIndex χ x y D = 1 :=
  Iff.rfl

/-- In a weakly admissible diagram only finitely many domains are counted by the hat
differential between two generators. -/
theorem WeaklyAdmissible.finite_hatDomains (hW : H.WeaklyAdmissible) (χ : Region → ℤ)
    (x y : H.Generator) : (H.hatDomains χ x y).Finite :=
  (hW.finite_setOf_isDomainBetween_basepoint_eq_nonneg x y 0).subset fun _ hD =>
    ⟨hD.1, hD.2.1, hD.2.2.1⟩

/-- In a weakly admissible diagram no domain is counted by the hat differential from a generator
to itself: such a domain is a nonnegative periodic domain, hence zero, and the zero domain has
Maslov index zero. -/
@[simp]
theorem WeaklyAdmissible.hatDomains_self (hW : H.WeaklyAdmissible) (χ : Region → ℤ)
    (x : H.Generator) : H.hatDomains χ x x = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun D ⟨hD, hz, hD0, hμ⟩ => ?_
  obtain rfl := weaklyAdmissible_iff.mp hW D (isDomainBetween_self_iff.mp ⟨hD, hz⟩) hD0
  simp at hμ

/-- In a diagram without nonzero periodic domains at most one domain is counted by the hat
differential between two generators: two of them differ by a periodic domain. -/
theorem subsingleton_hatDomains_of_periodicDomains_eq_bot (hP : H.periodicDomains = ⊥)
    (χ : Region → ℤ) (x y : H.Generator) : (H.hatDomains χ x y).Subsingleton := by
  rintro D ⟨hD, hz, -⟩ D' ⟨hD', hz', -⟩
  have h := hD.sub_mem_periodicDomains_iff.mpr ⟨hD', fun z => by rw [hz z, hz' z]⟩
  rw [hP, AddSubgroup.mem_bot, sub_eq_zero] at h
  exact h.symm

end Domains

section Coefficient

variable (H) in
/-- The coefficient of the generator `y` in the hat differential of the generator `x`: the
number, modulo two, of nonnegative domains of Maslov index one from `x` to `y` avoiding the
basepoints. This is meaningful when the set `H.hatDomains χ x y` of these domains is finite, for
instance in a weakly admissible diagram (`WeaklyAdmissible.finite_hatDomains`); for an infinite
set the coefficient is `0`. -/
noncomputable def hatCoefficient (χ : Region → ℤ) (x y : H.Generator) : ZMod 2 :=
  (H.hatDomains χ x y).ncard

variable {χ : Region → ℤ} {x y : H.Generator} {D : Region → ℤ}

theorem hatCoefficient_def : H.hatCoefficient χ x y = (H.hatDomains χ x y).ncard :=
  (rfl)

/-- The hat differential has coefficient zero from `x` to `y` when no domain from `x` to `y` is
counted. -/
theorem hatCoefficient_eq_zero_of_hatDomains_eq_empty (h : H.hatDomains χ x y = ∅) :
    H.hatCoefficient χ x y = 0 := by
  simp [hatCoefficient_def, h]

/-- A nonzero coefficient of the hat differential from `x` to `y` comes from a counted domain
from `x` to `y`. -/
theorem nonempty_hatDomains_of_hatCoefficient_ne_zero (h : H.hatCoefficient χ x y ≠ 0) :
    (H.hatDomains χ x y).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun he => h (hatCoefficient_eq_zero_of_hatDomains_eq_empty he)

/-- In a weakly admissible diagram the hat differential has no diagonal terms. -/
@[simp]
theorem WeaklyAdmissible.hatCoefficient_self (hW : H.WeaklyAdmissible) (χ : Region → ℤ)
    (x : H.Generator) : H.hatCoefficient χ x x = 0 :=
  hatCoefficient_eq_zero_of_hatDomains_eq_empty (hW.hatDomains_self χ x)

/-- In a diagram without nonzero periodic domains, the hat differential has coefficient one from
`x` to `y` exactly when some domain from `x` to `y` is counted. -/
theorem hatCoefficient_eq_one_iff_of_periodicDomains_eq_bot (hP : H.periodicDomains = ⊥) :
    H.hatCoefficient χ x y = 1 ↔ (H.hatDomains χ x y).Nonempty := by
  refine ⟨fun h => nonempty_hatDomains_of_hatCoefficient_ne_zero (h ▸ one_ne_zero),
    fun ⟨D, hD⟩ => ?_⟩
  rw [hatCoefficient_def,
    (subsingleton_hatDomains_of_periodicDomains_eq_bot hP χ x y).eq_singleton_of_mem hD,
    Set.ncard_singleton, Nat.cast_one]

/-- In a nice weakly admissible diagram, the hat differential only joins generators whose points
differ on exactly one `α`-curve, as across a bigon, or on exactly two, as across a rectangle. -/
theorem IsNice.hammingDist_eq_one_or_eq_two_of_hatCoefficient_ne_zero [DecidableEq Point]
    (h : H.IsNice χ) (hW : H.WeaklyAdmissible) (hc : H.hatCoefficient χ x y ≠ 0) :
    hammingDist (H.point x) (H.point y) = 1 ∨ hammingDist (H.point x) (H.point y) = 2 := by
  obtain ⟨D, hD, hz, hD0, hμ⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  exact h.hammingDist_eq_one_or_eq_two_of_maslovIndex_eq_one hW hD hD0 hz hμ

/-- In a singly pointed diagram of a closed surface of genus `n` whose periodic domains have
Maslov index zero at `x`, the hat differential lowers the relative Maslov grading by one: a
nonzero coefficient from `x` to `y` forces `gr(x, y) = 1`. -/
theorem relativeGrading_eq_one_of_hatCoefficient_ne_zero [Subsingleton Basepoint]
    (z : Basepoint) (hχ : ∑ r, χ r - Fintype.card Point = 2 - 2 * (n : ℤ))
    (hP : ∀ P ∈ H.periodicDomains, H.maslovIndex χ x x P = 0)
    (hc : H.hatCoefficient χ x y ≠ 0) : H.relativeGrading χ z x y = 1 := by
  obtain ⟨D, hD, hz, -, hμ⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  rw [hD.relativeGrading_eq z hχ hP, hμ, hz z]
  simp

end Coefficient

section Differential

variable (H) in
/-- The hat differential of a Heegaard diagram with region Euler characteristics `χ`: the
`ZMod 2`-linear endomorphism of the free module on generators whose coefficient from `x` to `y`
is the number, modulo two, of nonnegative domains of Maslov index one from `x` to `y` avoiding
the basepoints (`TauCeti.HeegaardRegionSystem.hatCoefficient`). -/
noncomputable def hatDifferential (χ : Region → ℤ) :
    (H.Generator →₀ ZMod 2) →ₗ[ZMod 2] H.Generator →₀ ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) fun x =>
    Finsupp.equivFunOnFinite.symm (H.hatCoefficient χ x)

variable {χ : Region → ℤ}

/-- The matrix coefficients of the hat differential are the counts
`TauCeti.HeegaardRegionSystem.hatCoefficient`. -/
@[simp]
theorem hatDifferential_single_apply (x y : H.Generator) (a : ZMod 2) :
    H.hatDifferential χ (Finsupp.single x a) y = a * H.hatCoefficient χ x y := by
  simp [hatDifferential]

/-- The coefficient of `y` in the hat differential of a chain `c`. -/
theorem hatDifferential_apply (c : H.Generator →₀ ZMod 2) (y : H.Generator) :
    H.hatDifferential χ c y = c.sum fun x a => a * H.hatCoefficient χ x y := by
  simp [hatDifferential, Finsupp.linearCombination_apply, Finsupp.sum_apply]

/-- The hat differential vanishes exactly when all of its coefficients vanish. -/
theorem hatDifferential_eq_zero_iff :
    H.hatDifferential χ = 0 ↔ ∀ x y, H.hatCoefficient χ x y = 0 := by
  refine ⟨fun h x y => ?_, fun h => ?_⟩
  · simpa using DFunLike.congr_fun (LinearMap.congr_fun h (Finsupp.single x 1)) y
  · ext x y
    simp [h]

end Differential

end HeegaardRegionSystem

end TauCeti
