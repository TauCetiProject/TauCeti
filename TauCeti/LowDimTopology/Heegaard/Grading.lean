/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Finsupp
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.LowDimTopology.Heegaard.FlavorExactSequence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Polynomial.Laurent.Coeff
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Maslov gradings of the generators and of the flavor complexes

The relative Maslov grading of a Heegaard diagram
(`TauCeti.LowDimTopology.Heegaard.RelativeGrading`) assigns to generators `x`, `y` joined by a
domain `D` the number `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)`. This file lifts it to a grading of the generators
and of the chain groups of all the flavors, and shows that the differentials have degree `-1` and
that `U` has degree `-2`.

A **Maslov grading** (`TauCeti.HeegaardRegionSystem.IsMaslovGrading`) is a function
`gr : Generator → ℚ` with `gr(x) - gr(y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for every domain `D` from `x` to
`y`. It computes the relative grading (`IsMaslovGrading.relativeGrading_eq`), and two Maslov
gradings differ by a constant on each class of generators joined by domains
(`IsMaslovGrading.sub_eq_sub`, `IsMaslovGrading.exists_eq_add`). One
exists exactly when every domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`
(`TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`); when the domains from a generator to
itself are normalized as in a singly pointed diagram of a closed surface, this says that every
periodic domain has Maslov index zero
(`exists_isMaslovGrading_iff_forall_periodicMaslovIndices_eq_bot`). On a geometric diagram the
Maslov index of a periodic domain is the evaluation of `c₁` of the spin^c structure of the
generator (not formalized here), so this is the case of torsion spin^c structures, the case in
which Ozsváth and Szabó grade the generators by integers. The grading is
`ℚ`-valued here because the combinatorial Maslov index is a rational number; the Maslov component
of a knot grading is an integer-valued example
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.isMaslovGrading`). When a periodic domain has nonzero
Maslov index there is no Maslov grading, as for the genus-one diagram of `S¹ × S²` with its
basepoint in a bigon, where two domains from one generator to the other give `μ(D) - 2 n_z(D)`
the values `-1` and `1`
(`TauCeti.HeegaardRegionSystem.maslovIndex_sub_two_mul_circleTimesSphere_one`).

Without a Maslov grading the generators still carry a **Maslov grading modulo** a subgroup `Λ`
of `ℚ` (`TauCeti.HeegaardRegionSystem.IsMaslovGradingMod`): a function `gr : Generator → ℚ` with
`gr(x) - gr(y) ≡ μ(D) - 2 ∑ᵢ n_{zᵢ}(D) (mod Λ)` for every domain `D` from `x` to `y`. One exists
exactly when every domain `E` from a generator to itself has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E) ∈ Λ`
(`TauCeti.HeegaardRegionSystem.exists_isMaslovGradingMod_iff`), and with the normalization of a
singly pointed diagram exactly when `Λ` contains the periodic Maslov indices of all generators
(`exists_isMaslovGradingMod_iff_forall_periodicMaslovIndices_le`). On the generators joined by
domains to a generator `x₀` it exists modulo the periodic Maslov indices at `x₀` when every domain
from `x₀` to itself satisfies the normalization of the relative grading, as in a singly pointed
diagram (`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton`)
(`TauCeti.HeegaardRegionSystem.exists_coe_sub_eq_of_maslovIndex_sub_two_mul_sum_mem` with
`Λ` these indices), the multiples of some `d ≥ 0`: this is the relative `ℤ / d(s)` grading of
Ozsváth and Szabó for a non-torsion spin^c structure `s` (the identification of `d` with the
divisibility of `c₁(s)` is not formalized here). Modulo `Λ = ⊥` it is a Maslov grading
(`isMaslovGradingMod_bot_iff`).

A grading `gr` of the generators grades the chain groups over `𝔽₂ = ZMod 2`:

* `CF̂`, by `gr` (`TauCeti.HeegaardRegionSystem.hatGrading`);
* `CF⁻` and `CF^∞`, in which `U ^ k x` has degree `gr(x) - 2 k`
  (`TauCeti.HeegaardRegionSystem.minusGrading`, `TauCeti.HeegaardRegionSystem.infinityGrading`).
  Each is the grading of the `𝔽₂`-basis of the chains `U ^ k x` by these degrees;
* `CF⁺ = CF^∞ / CF⁻`, by the images of the pieces of `CF^∞`
  (`TauCeti.HeegaardRegionSystem.plusGrading`). This is a grading because `CF⁻` is a homogeneous
  submodule of `CF^∞`.

In the notation `[x, i] = U ^ (-i) x` of Ozsváth and Szabó this is their grading
`gr([x, i]) = gr(x) + 2 i`, and `U` lowers it by two (`X_smul_mem_minusGradedPiece`,
`X_smul_mem_infinityGradedPiece`, `X_smul_mem_plusGrading_piece`). For a Maslov grading, the hat,
minus, infinity and plus differentials have degree `-1`
(`IsMaslovGrading.isHomogeneous_hatDifferential`, `IsMaslovGrading.isHomogeneous_minusDifferential`,
`IsMaslovGrading.isHomogeneous_infinityDifferential`,
`IsMaslovGrading.isHomogeneous_plusDifferential`): a counted domain from `x` to `y` with
`n_z(D) = k` has Maslov index one, so it joins `U ^ j x`, of degree `gr(x) - 2 j`, to
`U ^ (j + k) y`, of degree `gr(y) - 2 (j + k) = gr(x) - 2 j - 1`.

The maps of the short exact sequences relating the flavors
(`TauCeti.LowDimTopology.Heegaard.FlavorExactSequence`) are homogeneous: the inclusion of `CF⁻`
into `CF^∞` (`isHomogeneous_mapRange_toLaurent`), the quotient map onto `CF⁺`
(`TauCeti.InternalGrading.isHomogeneous_mkQ`) and setting `U = 0`
(`isHomogeneous_mapRange_constantCoeff`) have degree `0`, and the inclusion of `CF̂` into
`CF⁺` has degree `2` (`isHomogeneous_hatToPlus`), since it sends `x` to the class of `U⁻¹ x`. Our
`CF⁻` is spanned by the `U ^ k x` with `k ≥ 0` rather than `k > 0`, which is why this map, of degree
`0` in the conventions of Ozsváth and Szabó, has degree `2` here.

For a Maslov grading modulo `Λ`, coarsening these gradings along `ℚ → ℚ ⧸ Λ`
(`TauCeti.InternalGrading.coarsen`) grades the chain groups by `ℚ ⧸ Λ`. In these gradings the four
differentials have degree `-1` (`IsMaslovGradingMod.isHomogeneous_hatDifferential` and its three
companions) and `U` has degree `-2` (`X_smul_mem_coarsenGrading_minusGradedPiece`,
`X_smul_mem_coarsenGrading_infinityGradedPiece`, `X_smul_mem_coarsenGrading_plusGrading_piece`,
and `T_smul_mem_coarsenGrading_infinityGradedPiece` for every power of `U` on `CF^∞`). The
inclusion of `CF⁻` into `CF^∞` and the quotient map onto `CF⁺` keep the coarsened degree
(`mapRange_toLaurent_mem_coarsenGrading_infinityGradedPiece`,
`mk_mem_coarsenGrading_plusGrading_piece`), and the coarsened pieces of `CF⁺` are the images of
those of `CF^∞` (`mem_coarsenGrading_plusGrading_piece_iff`). The
statements for Maslov gradings are the case `Λ = ⊥`, in which coarsening merges no degrees
(`LinearMap.IsHomogeneous.of_coarsenGrading`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsMaslovGrading`: a rational grading of the generators lifting the
  relative Maslov grading.
* `TauCeti.HeegaardRegionSystem.IsMaslovGradingMod`: a rational grading of the generators lifting
  the relative Maslov grading modulo a subgroup of `ℚ`.
* `TauCeti.HeegaardRegionSystem.minusGradedPiece`,
  `TauCeti.HeegaardRegionSystem.infinityGradedPiece`: the homogeneous pieces of `CF⁻` and `CF^∞`.
* `TauCeti.HeegaardRegionSystem.hatGrading`, `TauCeti.HeegaardRegionSystem.minusGrading`,
  `TauCeti.HeegaardRegionSystem.infinityGrading`, `TauCeti.HeegaardRegionSystem.plusGrading`: the
  internal gradings of `CF̂`, `CF⁻`, `CF^∞` and `CF⁺`.

## Main results

* `TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`: existence of Maslov gradings.
* `TauCeti.HeegaardRegionSystem.IsMaslovGrading.exists_eq_add`: their uniqueness up to a shift.
* `TauCeti.HeegaardRegionSystem.exists_isMaslovGradingMod_iff` and
  `TauCeti.HeegaardRegionSystem.exists_coe_sub_eq_of_maslovIndex_sub_two_mul_sum_mem`:
  existence of Maslov gradings modulo a subgroup, on all generators and on one class of
  generators; the latter gives the relative `ℤ / d` grading.
* `TauCeti.HeegaardRegionSystem.IsMaslovGradingMod.isHomogeneous_hatDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGradingMod.isHomogeneous_minusDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGradingMod.isHomogeneous_infinityDifferential` and
  `TauCeti.HeegaardRegionSystem.IsMaslovGradingMod.isHomogeneous_plusDifferential`: the
  differentials have degree `-1` modulo the subgroup.
* `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_hatDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_minusDifferential`,
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_infinityDifferential` and
  `TauCeti.HeegaardRegionSystem.IsMaslovGrading.isHomogeneous_plusDifferential`: the differentials
  have degree `-1`.
* `TauCeti.HeegaardRegionSystem.X_smul_mem_minusGradedPiece`,
  `TauCeti.HeegaardRegionSystem.X_smul_mem_infinityGradedPiece` and
  `TauCeti.HeegaardRegionSystem.X_smul_mem_plusGrading_piece`: `U` has degree `-2`, and
  `TauCeti.HeegaardRegionSystem.X_smul_mem_coarsenGrading_minusGradedPiece` and its two companions
  after coarsening.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.1 (the complexes `CF^∞`, `CF⁻`,
  `CF⁺`, and the grading `gr([x, i]) = gr(x) + 2 i` for torsion spin^c structures), and the relative
  `ℤ / d(s)` grading for non-torsion spin^c structures.
-/

public section

open Polynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section MaslovGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]

variable (H) in
/-- A **Maslov grading** of the generators: a rational grading `gr` whose differences are given by
every domain, `gr(x) - gr(y) = μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for each domain `D` from `x` to `y`, where
`μ` is the combinatorial Maslov index with region Euler characteristics `χ`. With a single
basepoint `z` this is `gr(x) - gr(y) = μ(D) - 2 n_z(D)`. Such a grading exists exactly when every
domain from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`
(`TauCeti.HeegaardRegionSystem.exists_isMaslovGrading_iff`), and it is then unique up to a
constant on each class of generators joined by domains. -/
structure IsMaslovGrading (χ : Region → ℤ) (gr : H.Generator → ℚ) : Prop where
  /-- The grading drops by `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` along every domain `D`. -/
  sub_eq {x y : H.Generator} {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    gr x - gr y = H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ)

variable {χ : Region → ℤ} {gr gr' : H.Generator → ℚ} {x y : H.Generator} {D E : Region → ℤ}

/-- If every domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`, the normalization
of the relative grading holds. -/
private theorem maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_forall
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ))
    (x : H.Generator) (E : Region → ℤ) (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x := by
  rw [hself x E hE, sub_self]
  exact zero_mem _

/-- If every domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`, every periodic
domain has Maslov index zero at every generator. -/
private theorem maslovIndex_eq_zero_of_mem_periodicDomains_of_forall
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ))
    {P : Region → ℤ} (hP : P ∈ H.periodicDomains) (x : H.Generator) :
    H.maslovIndex χ x x P = 0 := by
  obtain ⟨hxx, hz⟩ := (isDomainBetween_self_iff (x := x)).mpr hP
  simp [hself x P hxx, hz]

namespace IsMaslovGrading

/-- Shifting a Maslov grading by a constant gives a Maslov grading. -/
theorem add_const (h : H.IsMaslovGrading χ gr) (c : ℚ) :
    H.IsMaslovGrading χ fun x => gr x + c where
  sub_eq hD := by
    rw [← h.sub_eq hD]
    ring

end IsMaslovGrading

/-! ### Maslov gradings modulo a subgroup -/

variable (H) in
/-- A **Maslov grading modulo** a subgroup `Λ` of `ℚ`: a rational grading `gr` of the generators
whose differences are given by every domain modulo `Λ`,
`gr(x) - gr(y) ≡ μ(D) - 2 ∑ᵢ n_{zᵢ}(D) (mod Λ)` for each domain `D` from `x` to `y`. Only the
classes of the values `gr(x)` in `ℚ ⧸ Λ` matter (`IsMaslovGradingMod.of_coe_eq`). For `Λ = ⊥` this
is a Maslov grading (`TauCeti.HeegaardRegionSystem.isMaslovGradingMod_bot_iff`). For `Λ` the
periodic Maslov indices, the multiples of the combinatorial divisibility `d`
(`exists_nonneg_periodicMaslovIndices_eq_zmultiples`), it is the relative `ℤ / d` grading of
Ozsváth and Szabó in a non-torsion spin^c sector, which exists on a class of generators joined by
domains when every domain from a generator of the class to itself satisfies the normalization of
the relative grading, as in a singly pointed diagram
(`TauCeti.HeegaardRegionSystem.exists_coe_sub_eq_of_maslovIndex_sub_two_mul_sum_mem`). -/
structure IsMaslovGradingMod (Λ : AddSubgroup ℚ) (χ : Region → ℤ) (gr : H.Generator → ℚ) :
    Prop where
  /-- Modulo `Λ`, the grading drops by `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` along every domain `D`. -/
  coe_sub_eq {x y : H.Generator} {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    ((gr x - gr y : ℚ) : ℚ ⧸ Λ) =
      ((H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) : ℚ) : ℚ ⧸ Λ)

variable {Λ Λ' : AddSubgroup ℚ}

/-- A Maslov grading is a Maslov grading modulo every subgroup. -/
theorem IsMaslovGrading.isMaslovGradingMod (h : H.IsMaslovGrading χ gr) (Λ : AddSubgroup ℚ) :
    H.IsMaslovGradingMod Λ χ gr where
  coe_sub_eq hD := by rw [h.sub_eq hD]

namespace IsMaslovGradingMod

/-- Modulo `Λ`, the grading drops by `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` along every domain `D`, in the form
of a membership in `Λ`. -/
theorem sub_sub_mem (h : H.IsMaslovGradingMod Λ χ gr) (hD : H.IsDomainBetween x y D) :
    gr x - gr y - (H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ)) ∈ Λ :=
  QuotientAddGroup.eq_iff_sub_mem.mp (h.coe_sub_eq hD)

/-- A Maslov grading modulo `Λ` is a Maslov grading modulo every larger subgroup. -/
theorem mono (h : H.IsMaslovGradingMod Λ χ gr) (hΛ : Λ ≤ Λ') : H.IsMaslovGradingMod Λ' χ gr where
  coe_sub_eq hD := QuotientAddGroup.eq_iff_sub_mem.mpr (hΛ (h.sub_sub_mem hD))

/-- A Maslov grading modulo `Λ` only depends on the classes of its values modulo `Λ`. -/
theorem of_coe_eq (h : H.IsMaslovGradingMod Λ χ gr)
    (hgr : ∀ x, (gr' x : ℚ ⧸ Λ) = gr x) : H.IsMaslovGradingMod Λ χ gr' where
  coe_sub_eq hD := by rw [QuotientAddGroup.mk_sub, hgr, hgr, ← QuotientAddGroup.mk_sub,
    h.coe_sub_eq hD]

/-- Shifting a Maslov grading modulo `Λ` by a constant gives a Maslov grading modulo `Λ`. -/
theorem add_const (h : H.IsMaslovGradingMod Λ χ gr) (c : ℚ) :
    H.IsMaslovGradingMod Λ χ fun x => gr x + c where
  coe_sub_eq hD := by rw [← h.coe_sub_eq hD, add_sub_add_right_eq_sub]

/-- Two Maslov gradings modulo `Λ` differ by the same amount modulo `Λ` at generators joined by a
domain. -/
theorem coe_sub_eq_coe_sub (h : H.IsMaslovGradingMod Λ χ gr) (h' : H.IsMaslovGradingMod Λ χ gr')
    (hD : H.IsDomainBetween x y D) :
    ((gr' x - gr x : ℚ) : ℚ ⧸ Λ) = ((gr' y - gr y : ℚ) : ℚ ⧸ Λ) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  convert sub_mem (h'.sub_sub_mem hD) (h.sub_sub_mem hD) using 1
  ring

/-- **Maslov gradings modulo `Λ` are unique up to an overall shift modulo `Λ`.** When every two
generators are joined by a domain, two Maslov gradings modulo `Λ` differ by a constant modulo
`Λ`. -/
theorem exists_coe_eq_add (h : H.IsMaslovGradingMod Λ χ gr) (h' : H.IsMaslovGradingMod Λ χ gr')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D) :
    ∃ c : ℚ, ∀ x, (gr' x : ℚ ⧸ Λ) = ((gr x + c : ℚ) : ℚ ⧸ Λ) := by
  rcases isEmpty_or_nonempty H.Generator with hH | ⟨⟨x₀⟩⟩
  · exact ⟨0, isEmptyElim⟩
  refine ⟨gr' x₀ - gr x₀, fun x => ?_⟩
  obtain ⟨D, hD⟩ := hconn x x₀
  rw [QuotientAddGroup.eq_iff_sub_mem]
  convert QuotientAddGroup.eq_iff_sub_mem.mp (h.coe_sub_eq_coe_sub h' hD) using 1
  ring

/-- In the presence of a Maslov grading modulo `Λ`, a domain `E` from a generator to itself has
`μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` in `Λ`. -/
theorem maslovIndex_sub_two_mul_sum_mem (h : H.IsMaslovGradingMod Λ χ gr)
    (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ Λ := by
  simpa using neg_mem (h.sub_sub_mem hE)

/-- In the presence of a Maslov grading modulo `Λ`, the periodic Maslov indices at every
generator lie in `Λ`. -/
theorem periodicMaslovIndices_le (h : H.IsMaslovGradingMod Λ χ gr) (x : H.Generator) :
    H.periodicMaslovIndices χ x ≤ Λ := fun q hq => by
  obtain ⟨P, hP, rfl⟩ := mem_periodicMaslovIndices_iff.mp hq
  obtain ⟨hxx, hz⟩ := (isDomainBetween_self_iff (x := x)).mpr hP
  simpa [hz] using h.maslovIndex_sub_two_mul_sum_mem hxx

/-- Modulo `Λ`, a Maslov grading modulo `Λ` computes the relative grading of generators joined by
a domain: `gr(x, y) ≡ gr(x) - gr(y)`. -/
theorem coe_relativeGrading_eq (h : H.IsMaslovGradingMod Λ χ gr)
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x)
    (hD : H.IsDomainBetween x y D) :
    (H.relativeGrading χ x y : ℚ ⧸ Λ) = ((gr x - gr y : ℚ) : ℚ ⧸ Λ) := by
  have hrel := h.periodicMaslovIndices_le x
    (QuotientAddGroup.eq_iff_sub_mem.mp (hD.coe_relativeGrading_eq hself))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  convert sub_mem hrel (h.sub_sub_mem hD) using 1
  ring

/-- **The hat differential lowers a Maslov grading modulo `Λ` by one.** A nonzero coefficient of
the hat differential from `x` to `y` forces `gr(x) - gr(y) ≡ 1 (mod Λ)`. -/
theorem coe_sub_eq_one_of_hatCoefficient_ne_zero (h : H.IsMaslovGradingMod Λ χ gr)
    (hc : H.hatCoefficient χ x y ≠ 0) : ((gr x - gr y : ℚ) : ℚ ⧸ Λ) = ((1 : ℚ) : ℚ ⧸ Λ) := by
  obtain ⟨D, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  obtain ⟨hD, hz, -, hμ⟩ := mem_hatDomains_iff.mp hD
  simp [h.coe_sub_eq hD, hμ, hz]

/-- **The minus differential lowers a Maslov grading modulo `Λ` by one.** A term `U ^ k y` of the
minus differential of `x` has `gr(x) - gr(y) ≡ 1 - 2 k (mod Λ)`. -/
theorem coe_sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero
    (h : H.IsMaslovGradingMod Λ χ gr) {k : ℕ} (hc : (H.minusCoefficient χ x y).coeff k ≠ 0) :
    ((gr x - gr y : ℚ) : ℚ ⧸ Λ) = ((1 - 2 * k : ℚ) : ℚ ⧸ Λ) := by
  obtain ⟨D, hD, hk⟩ := exists_mem_minusDomains_of_coeff_minusCoefficient_ne_zero hc
  obtain ⟨hD, -, hμ⟩ := mem_minusDomains_iff.mp hD
  rw [h.coe_sub_eq hD, hμ, ← Int.cast_sum, hk, Int.cast_natCast]

end IsMaslovGradingMod

/-- **Maslov gradings modulo the trivial subgroup are Maslov gradings.** -/
@[simp]
theorem isMaslovGradingMod_bot_iff : H.IsMaslovGradingMod ⊥ χ gr ↔ H.IsMaslovGrading χ gr := by
  refine ⟨fun h => ⟨fun hD => ?_⟩, fun h => h.isMaslovGradingMod ⊥⟩
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp (h.sub_sub_mem hD))

namespace IsMaslovGrading

/-! The following statements about Maslov gradings are the case `Λ = ⊥` of those about Maslov
gradings modulo `Λ`. -/

/-- Two Maslov gradings differ by the same amount at generators joined by a domain. -/
theorem sub_eq_sub (h : H.IsMaslovGrading χ gr) (h' : H.IsMaslovGrading χ gr')
    (hD : H.IsDomainBetween x y D) : gr' x - gr x = gr' y - gr y :=
  QuotientAddGroup.mk'_bot_injective
    ((h.isMaslovGradingMod ⊥).coe_sub_eq_coe_sub (h'.isMaslovGradingMod ⊥) hD)

/-- **Maslov gradings are unique up to an overall shift.** When every two generators are joined
by a domain, two Maslov gradings differ by a constant. -/
theorem exists_eq_add (h : H.IsMaslovGrading χ gr) (h' : H.IsMaslovGrading χ gr')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D) :
    ∃ c : ℚ, gr' = fun x => gr x + c := by
  obtain ⟨c, hc⟩ := (h.isMaslovGradingMod ⊥).exists_coe_eq_add (h'.isMaslovGradingMod ⊥) hconn
  exact ⟨c, funext fun x => QuotientAddGroup.mk'_bot_injective (hc x)⟩

/-- In the presence of a Maslov grading, a domain `E` from a generator to itself has Maslov index
`2 ∑ᵢ n_{zᵢ}(E)`. -/
theorem maslovIndex_self_eq_two_mul_sum (h : H.IsMaslovGrading χ gr)
    (hE : H.IsDomainBetween x x E) :
    H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ) :=
  sub_eq_zero.mp
    (AddSubgroup.mem_bot.mp ((h.isMaslovGradingMod ⊥).maslovIndex_sub_two_mul_sum_mem hE))

/-- In the presence of a Maslov grading, every periodic domain has Maslov index zero at every
generator. -/
theorem maslovIndex_eq_zero_of_mem_periodicDomains (h : H.IsMaslovGrading χ gr)
    {P : Region → ℤ} (hP : P ∈ H.periodicDomains) (x : H.Generator) :
    H.maslovIndex χ x x P = 0 :=
  maslovIndex_eq_zero_of_mem_periodicDomains_of_forall
    (fun _ _ => h.maslovIndex_self_eq_two_mul_sum) hP x

/-- In the presence of a Maslov grading, the periodic Maslov indices vanish at every generator, so
the relative grading is well defined in `ℚ` rather than only modulo them. -/
theorem periodicMaslovIndices_eq_bot (h : H.IsMaslovGrading χ gr) (x : H.Generator) :
    H.periodicMaslovIndices χ x = ⊥ :=
  le_bot_iff.mp ((h.isMaslovGradingMod ⊥).periodicMaslovIndices_le x)

/-- A Maslov grading computes the relative grading of generators joined by a domain:
`gr(x, y) = gr(x) - gr(y)`. -/
theorem relativeGrading_eq (h : H.IsMaslovGrading χ gr) (hD : H.IsDomainBetween x y D) :
    H.relativeGrading χ x y = gr x - gr y :=
  QuotientAddGroup.mk'_bot_injective
    ((h.isMaslovGradingMod ⊥).coe_relativeGrading_eq
      (maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_forall
        fun _ _ => h.maslovIndex_self_eq_two_mul_sum) hD)

/-- **The minus differential lowers a Maslov grading by one.** A term `U ^ k y` of the minus
differential of `x` has `gr(x) - gr(y) = 1 - 2 k`. -/
theorem sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero (h : H.IsMaslovGrading χ gr)
    {k : ℕ} (hc : (H.minusCoefficient χ x y).coeff k ≠ 0) : gr x - gr y = 1 - 2 * k :=
  QuotientAddGroup.mk'_bot_injective
    ((h.isMaslovGradingMod ⊥).coe_sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero hc)

/-- **The hat differential lowers a Maslov grading by one.** A nonzero coefficient of the hat
differential from `x` to `y` forces `gr(x) - gr(y) = 1`. -/
theorem sub_eq_one_of_hatCoefficient_ne_zero (h : H.IsMaslovGrading χ gr)
    (hc : H.hatCoefficient χ x y ≠ 0) : gr x - gr y = 1 :=
  QuotientAddGroup.mk'_bot_injective
    ((h.isMaslovGradingMod ⊥).coe_sub_eq_one_of_hatCoefficient_ne_zero hc)

end IsMaslovGrading

/-- For domains `D` from `r` to `x`, `E` from `x` to `y` and `F` from `r` to `y`, the domain
`D + E - F` from `r` to itself has `μ - 2 ∑ᵢ n_{zᵢ}` equal to the alternating sum of the values
of `D`, `E` and `F`. -/
private theorem maslovIndex_sub_two_mul_sum_add_add_neg {r : H.Generator} {F : Region → ℤ}
    (hD : H.IsDomainBetween r x D) (hE : H.IsDomainBetween x y E)
    (hF : H.IsDomainBetween r y F) :
    H.maslovIndex χ r r (D + (E + -F)) - 2 * ∑ z, ((D + (E + -F)) (H.basepoint z) : ℚ) =
      H.maslovIndex χ r x D - 2 * ∑ z, (D (H.basepoint z) : ℚ) +
        (H.maslovIndex χ x y E - 2 * ∑ z, (E (H.basepoint z) : ℚ)) -
        (H.maslovIndex χ r y F - 2 * ∑ z, (F (H.basepoint z) : ℚ)) := by
  rw [hD.maslovIndex_add χ (hE.add hF.neg), hE.maslovIndex_add χ hF.neg, maslovIndex_neg]
  simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

/-- **Existence of Maslov gradings modulo `Λ`.** The generators carry a Maslov grading modulo
`Λ` exactly when every domain `E` from a generator to itself has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` in `Λ`.
Such a grading is obtained by choosing a generator in each class of generators joined by domains
and grading the class by `μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` for a chosen domain `D` from it. -/
theorem exists_isMaslovGradingMod_iff :
    (∃ gr, H.IsMaslovGradingMod Λ χ gr) ↔ ∀ (x : H.Generator) (E : Region → ℤ),
      H.IsDomainBetween x x E → H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ Λ := by
  refine ⟨fun ⟨_, h⟩ _ _ hE => h.maslovIndex_sub_two_mul_sum_mem hE, fun hself => ?_⟩
  -- Being joined by a domain is an equivalence relation on generators.
  let s : Setoid H.Generator :=
    { r := fun x y => ∃ D, H.IsDomainBetween x y D
      iseqv := ⟨fun x => ⟨0, isDomainBetween_zero x⟩, fun ⟨D, hD⟩ => ⟨-D, hD.neg⟩,
        fun ⟨D, hD⟩ ⟨E, hE⟩ => ⟨D + E, hD.add hE⟩⟩ }
  -- A chosen domain from the representative of the class of each generator to the generator.
  choose D hD using fun y : H.Generator => Quotient.mk_out (s := s) y
  refine ⟨fun y => -(H.maslovIndex χ (Quotient.mk s y).out y (D y) -
      2 * ∑ z, (D y (H.basepoint z) : ℚ)),
    ⟨fun {x y E} hE => QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩⟩
  -- `D x + E - D y` runs from the common representative to itself.
  have hxy : (Quotient.mk s x).out = (Quotient.mk s y).out :=
    congrArg Quotient.out (Quotient.sound ⟨E, hE⟩)
  have hDx := hD x
  rw [hxy] at hDx
  have h := neg_mem (hself _ _ (hDx.add (hE.add (hD y).neg)))
  rw [maslovIndex_sub_two_mul_sum_add_add_neg hDx hE (hD y)] at h
  convert h using 1
  simp only [hxy]
  ring

/-- When every domain from a generator to itself satisfies the normalization of the relative
grading, as in a singly pointed diagram of a closed surface of genus `n`
(`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton`), the generators carry
a Maslov grading modulo `Λ` exactly when the periodic Maslov indices at every generator lie in
`Λ`. On a geometric diagram this asks `Λ` to contain the values of `c₁` of the spin^c structures
of the generators on `H₂(Y; ℤ)`. -/
theorem exists_isMaslovGradingMod_iff_forall_periodicMaslovIndices_le
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    (∃ gr, H.IsMaslovGradingMod Λ χ gr) ↔ ∀ x : H.Generator, H.periodicMaslovIndices χ x ≤ Λ :=
  ⟨fun ⟨_, h⟩ x => h.periodicMaslovIndices_le x,
    fun h => exists_isMaslovGradingMod_iff.mpr fun x E hE => h x (hself x E hE)⟩

/-- **Maslov gradings modulo `Λ` on one class of generators, and the relative `ℤ / d` grading.**
When every domain `E` from `x₀` to itself has `μ(E) - 2 ∑ᵢ n_{zᵢ}(E)` in `Λ`, the generators
joined by domains to `x₀` carry a grading `gr` with `gr(x) - gr(y) ≡ μ(D) - 2 ∑ᵢ n_{zᵢ}(D)` modulo
`Λ` for every domain `D` from `x` to `y`. When every generator is joined to `x₀`, `gr` is a Maslov
grading modulo `Λ`.

For `Λ` the periodic Maslov indices at `x₀`, the multiples of some `d ≥ 0`
(`exists_nonneg_periodicMaslovIndices_eq_zmultiples`), the hypothesis is the normalization of the
relative grading at `x₀`, and `gr` is the relative `ℤ / d` grading. On a geometric diagram the
generators joined to `x₀` are those of one spin^c structure `s` and `d = d(s)` is the
divisibility of `c₁(s)` (not formalized here). -/
theorem exists_coe_sub_eq_of_maslovIndex_sub_two_mul_sum_mem {x₀ : H.Generator}
    (hself : ∀ E : Region → ℤ, H.IsDomainBetween x₀ x₀ E →
      H.maslovIndex χ x₀ x₀ E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ Λ) :
    ∃ gr : H.Generator → ℚ, ∀ {x y : H.Generator} {D E : Region → ℤ},
      H.IsDomainBetween x₀ x E → H.IsDomainBetween x y D →
      ((gr x - gr y : ℚ) : ℚ ⧸ Λ) =
        ((H.maslovIndex χ x y D - 2 * ∑ z, (D (H.basepoint z) : ℚ) : ℚ) : ℚ ⧸ Λ) := by
  classical
  -- Grade each generator joined to `x₀` by the value of a chosen domain from `x₀` to it.
  refine ⟨fun y => if hy : ∃ F, H.IsDomainBetween x₀ y F then
      -(H.maslovIndex χ x₀ y hy.choose - 2 * ∑ z, (hy.choose (H.basepoint z) : ℚ)) else 0,
    fun {x y D E} hE hD => QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
  have hx : ∃ F, H.IsDomainBetween x₀ x F := ⟨E, hE⟩
  have hy : ∃ F, H.IsDomainBetween x₀ y F := ⟨E + D, hE.add hD⟩
  -- The chosen domain to `x`, then `D`, then back along the chosen domain to `y`, is periodic.
  have h := neg_mem (hself _ (hx.choose_spec.add (hD.add hy.choose_spec.neg)))
  rw [maslovIndex_sub_two_mul_sum_add_add_neg hx.choose_spec hD hy.choose_spec] at h
  convert h using 1
  simp only [dite_eq_left hx, dite_eq_left hy]
  ring

/-- **Existence of Maslov gradings.** The generators carry a Maslov grading exactly when every
domain `E` from a generator to itself has `μ(E) = 2 ∑ᵢ n_{zᵢ}(E)`: this is the case `Λ = ⊥` of
`TauCeti.HeegaardRegionSystem.exists_isMaslovGradingMod_iff`. -/
theorem exists_isMaslovGrading_iff :
    (∃ gr, H.IsMaslovGrading χ gr) ↔ ∀ (x : H.Generator) (E : Region → ℤ),
      H.IsDomainBetween x x E → H.maslovIndex χ x x E = 2 * ∑ z, (E (H.basepoint z) : ℚ) := by
  simp only [← isMaslovGradingMod_bot_iff, exists_isMaslovGradingMod_iff, AddSubgroup.mem_bot,
    sub_eq_zero]

/-- When every domain from a generator to itself satisfies the normalization of the relative
grading, as in a singly pointed diagram of a closed surface of genus `n`
(`maslovIndex_sub_two_mul_sum_mem_periodicMaslovIndices_of_subsingleton`), the generators carry
a Maslov grading exactly when the periodic Maslov indices vanish at every generator. On a
geometric diagram this is the condition that `c₁` of the spin^c structures of the generators is
torsion. -/
theorem exists_isMaslovGrading_iff_forall_periodicMaslovIndices_eq_bot
    (hself : ∀ (x : H.Generator) (E : Region → ℤ), H.IsDomainBetween x x E →
      H.maslovIndex χ x x E - 2 * ∑ z, (E (H.basepoint z) : ℚ) ∈ H.periodicMaslovIndices χ x) :
    (∃ gr, H.IsMaslovGrading χ gr) ↔ ∀ x : H.Generator, H.periodicMaslovIndices χ x = ⊥ := by
  simpa only [← isMaslovGradingMod_bot_iff, le_bot_iff] using
    exists_isMaslovGradingMod_iff_forall_periodicMaslovIndices_le (Λ := ⊥) hself

end MaslovGrading

section ChainGrading

variable (H) (gr : H.Generator → ℚ)

/-- The grading of `CF̂` by a grading `gr` of the generators: the free grading
`TauCeti.InternalGrading.finsupp` placing each generator `x` in degree `gr(x)`, whose degree-`q`
piece consists of the chains supported on the generators of degree `q`. -/
noncomputable abbrev hatGrading : InternalGrading (ZMod 2) (H.Generator →₀ ZMod 2) ℚ :=
  InternalGrading.finsupp (ZMod 2) gr

/-- The degree-`q` piece of `CF⁻` for a grading `gr` of the generators: the span of the chains
`U ^ k x` with `gr(x) - 2 k = q`. -/
noncomputable def minusGradedPiece (q : ℚ) : Submodule (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) :=
  Submodule.span (ZMod 2)
    (Finsupp.basis (fun _ : H.Generator => basisMonomials (ZMod 2)) ''
      {i | gr i.1 - 2 * i.2 = q})

/-- The degree-`q` piece of `CF^∞` for a grading `gr` of the generators: the span of the chains
`U ^ k x`, `k ∈ ℤ`, with `gr(x) - 2 k = q`. -/
noncomputable def infinityGradedPiece (q : ℚ) :
    Submodule (ZMod 2) (H.Generator →₀ (ZMod 2)[T;T⁻¹]) :=
  Submodule.span (ZMod 2)
    (Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ''
      {i | gr i.1 - 2 * i.2 = q})

variable {H gr}

/-- A chain of `CF⁻` lies in the piece of degree `k` of the grading coarsened along `f : ℚ → κ`
exactly when each of its terms `U ^ j x` has `f (gr(x) - 2 j) = k`. -/
@[simp]
theorem mem_coarsenGrading_minusGradedPiece_iff {κ : Type*} {f : ℚ → κ} {k : κ}
    {c : H.Generator →₀ (ZMod 2)[X]} :
    c ∈ coarsenGrading (H.minusGradedPiece gr) f k ↔
      ∀ x (j : ℕ), (c x).coeff j ≠ 0 → f (gr x - 2 * j) = k := by
  have h := coarsenGrading_span_image_fiber (R := ZMod 2) f
    (Finsupp.basis fun _ : H.Generator => basisMonomials (ZMod 2))
    fun i : (Σ _ : H.Generator, ℕ) => gr i.1 - 2 * i.2
  unfold minusGradedPiece
  simp only [h, Module.Basis.mem_span_image]
  simp [Set.subset_def, basisMonomials, Sigma.forall]

/-- A chain of `CF^∞` lies in the piece of degree `k` of the grading coarsened along
`f : ℚ → κ` exactly when each of its terms `U ^ j x` has `f (gr(x) - 2 j) = k`. -/
@[simp]
theorem mem_coarsenGrading_infinityGradedPiece_iff {κ : Type*} {f : ℚ → κ} {k : κ}
    {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ coarsenGrading (H.infinityGradedPiece gr) f k ↔
      ∀ x (j : ℤ), (c x).coeff j ≠ 0 → f (gr x - 2 * j) = k := by
  have h := coarsenGrading_span_image_fiber (R := ZMod 2) f
    (Finsupp.basis fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2))
    fun i : (Σ _ : H.Generator, ℤ) => gr i.1 - 2 * i.2
  unfold infinityGradedPiece
  simp only [h, Module.Basis.mem_span_image]
  simp [Set.subset_def, AddMonoidAlgebra.basis, Sigma.forall]

/-- A chain of `CF⁻` has degree `q` exactly when each of its terms `U ^ k x` has
`gr(x) - 2 k = q`. -/
@[simp]
theorem mem_minusGradedPiece_iff {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]} :
    c ∈ H.minusGradedPiece gr q ↔ ∀ x (k : ℕ), (c x).coeff k ≠ 0 → gr x - 2 * k = q := by
  simpa using mem_coarsenGrading_minusGradedPiece_iff (f := id) (k := q) (c := c)

/-- A chain of `CF^∞` has degree `q` exactly when each of its terms `U ^ k x` has
`gr(x) - 2 k = q`. -/
@[simp]
theorem mem_infinityGradedPiece_iff {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.infinityGradedPiece gr q ↔ ∀ x (k : ℤ), (c x).coeff k ≠ 0 → gr x - 2 * k = q := by
  simpa using mem_coarsenGrading_infinityGradedPiece_iff (f := id) (k := q) (c := c)

variable (H gr) in
/-- The grading of `CF⁻` by a grading `gr` of the generators, in which `U ^ k x` has degree
`gr(x) - 2 k`. -/
noncomputable def minusGrading : InternalGrading (ZMod 2) (H.Generator →₀ (ZMod 2)[X]) ℚ where
  piece := H.minusGradedPiece gr
  isInternal := (Finsupp.basis fun _ : H.Generator => basisMonomials (ZMod 2))
    |>.isInternal_span_image_fiber fun i => gr i.1 - 2 * i.2

variable (H gr) in
/-- The grading of `CF^∞` by a grading `gr` of the generators, in which `U ^ k x` has degree
`gr(x) - 2 k` for every integer `k`. -/
noncomputable def infinityGrading :
    InternalGrading (ZMod 2) (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ℚ where
  piece := H.infinityGradedPiece gr
  isInternal := (Finsupp.basis fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2))
    |>.isInternal_span_image_fiber fun i => gr i.1 - 2 * i.2

@[simp]
theorem minusGrading_piece : (H.minusGrading gr).piece = H.minusGradedPiece gr :=
  (rfl)

@[simp]
theorem infinityGrading_piece : (H.infinityGrading gr).piece = H.infinityGradedPiece gr :=
  (rfl)

/-- The chain `U ^ k x` of `CF⁻` has degree `gr(x) - 2 k`. -/
theorem single_X_pow_mem_minusGradedPiece (x : H.Generator) (k : ℕ) :
    Finsupp.single x (X ^ k : (ZMod 2)[X]) ∈ H.minusGradedPiece gr (gr x - 2 * k) := by
  rw [mem_minusGradedPiece_iff]
  intro y j hj
  by_cases hy : y = x
  · subst hy
    simp only [Finsupp.single_eq_same, coeff_X_pow, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hj
    rw [hj.1]
  · simp [Finsupp.single_eq_of_ne hy] at hj

/-- The chain `U ^ k x` of `CF^∞`, for an integer `k`, has degree `gr(x) - 2 k`. -/
theorem single_T_mem_infinityGradedPiece (x : H.Generator) (k : ℤ) :
    Finsupp.single x (T k : (ZMod 2)[T;T⁻¹]) ∈ H.infinityGradedPiece gr (gr x - 2 * k) := by
  rw [mem_infinityGradedPiece_iff]
  intro y j hj
  by_cases hy : y = x
  · subst hy
    simp only [Finsupp.single_eq_same, T_apply, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hj
    rw [hj.1]
  · simp [Finsupp.single_eq_of_ne hy] at hj

/-- **`U` lowers the degree of `CF⁻` by two.** -/
theorem X_smul_mem_minusGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) : (X : (ZMod 2)[X]) • c ∈ H.minusGradedPiece gr (q - 2) := by
  rw [mem_minusGradedPiece_iff] at hc ⊢
  intro x k hk
  rw [Finsupp.smul_apply, smul_eq_mul, ← pow_one X, coeff_X_pow_mul'] at hk
  split_ifs at hk with h1
  · have := hc x (k - 1) hk
    push_cast [h1] at this
    linarith
  · exact absurd rfl hk

/-- **Multiplication by `U ^ m` shifts the degree of `CF^∞` by `-2 m`**, for every integer `m`. -/
theorem T_smul_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) (m : ℤ) :
    (T m : (ZMod 2)[T;T⁻¹]) • c ∈ H.infinityGradedPiece gr (q - 2 * m) := by
  rw [mem_infinityGradedPiece_iff] at hc ⊢
  intro x k hk
  rw [Finsupp.smul_apply, smul_eq_mul, T_mul, coeff_mul_T] at hk
  have := hc x (k - m) hk
  push_cast at this
  linarith

/-- **`U` lowers the degree of `CF^∞` by two.** -/
theorem X_smul_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) :
    (X : (ZMod 2)[X]) • c ∈ H.infinityGradedPiece gr (q - 2) := by
  have hX : (X : (ZMod 2)[X]) • c = (T 1 : (ZMod 2)[T;T⁻¹]) • c := by
    ext x
    simp only [Finsupp.smul_apply, X_smul_eq_T_one_mul, smul_eq_mul]
  simpa [hX] using T_smul_mem_infinityGradedPiece hc 1

/-- **The inclusion of `CF⁻` into `CF^∞` has degree `0`.** -/
theorem isHomogeneous_mapRange_toLaurent :
    LinearMap.IsHomogeneous
      (Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹]))
      (H.minusGradedPiece gr) (H.infinityGradedPiece gr) 0 := by
  -- Check the degree on the basis `U ^ k x` of `CF⁻`, which spans its pieces.
  refine LinearMap.isHomogeneous_span_iff.2 ?_
  rintro p _ ⟨⟨x, k⟩, hi, rfl⟩
  have hb : Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹])
      (Finsupp.basis (fun _ : H.Generator => basisMonomials (ZMod 2)) ⟨x, k⟩) =
      Finsupp.single x (T k) := by
    simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C_mul_T]
  rw [hb, add_zero, ← hi]
  exact single_T_mem_infinityGradedPiece x k

/-- **The inclusion of `CF⁻` into `CF^∞` preserves the degree after coarsening** along any map
`f : ℚ → κ`, for instance modulo a subgroup of `ℚ`. -/
theorem mapRange_toLaurent_mem_coarsenGrading_infinityGradedPiece {κ : Type*} [AddMonoid κ]
    {f : ℚ → κ} {k : κ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ coarsenGrading (H.minusGradedPiece gr) f k) :
    Finsupp.mapRange toLaurent (map_zero _) c ∈ coarsenGrading (H.infinityGradedPiece gr) f k := by
  have heq : Finsupp.mapRange toLaurent (map_zero _) c =
      Finsupp.mapRange.linearMap (Algebra.linearMap (ZMod 2)[X] (ZMod 2)[T;T⁻¹]) c := by
    ext x
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  simpa [heq] using (isHomogeneous_mapRange_toLaurent.coarsenGrading_zero f).map_mem hc

/-- **The inclusion of `CF⁻` into `CF^∞` preserves the degree.** -/
theorem mapRange_toLaurent_mem_infinityGradedPiece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) :
    Finsupp.mapRange toLaurent (map_zero _) c ∈ H.infinityGradedPiece gr q := by
  simpa using mapRange_toLaurent_mem_coarsenGrading_infinityGradedPiece (f := id) (k := q)
    (by simpa using hc)

/-- **Setting `U = 0` has degree `0`**: taking constant coefficients maps the degree-`q` piece of
`CF⁻` to the degree-`q` piece of `CF̂`. -/
theorem isHomogeneous_mapRange_constantCoeff :
    LinearMap.IsHomogeneous (Finsupp.mapRange.linearMap (lcoeff (ZMod 2) 0))
      (H.minusGradedPiece gr) (H.hatGrading gr).piece 0 := by
  refine LinearMap.isHomogeneous_def.2 fun q c hc => ?_
  rw [mem_minusGradedPiece_iff] at hc
  rw [add_zero, InternalGrading.mem_finsupp_piece_iff]
  intro x hx
  rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, lcoeff_apply] at hx
  simpa using hc x 0 hx

/-- **Setting `U = 0` preserves the degree**: it maps the degree-`q` piece of `CF⁻` to the
degree-`q` piece of `CF̂`. -/
theorem mapRange_constantCoeff_mem_hatGrading_piece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ H.minusGradedPiece gr q) :
    Finsupp.mapRange constantCoeff (map_zero _) c ∈ (H.hatGrading gr).piece q := by
  have heq : Finsupp.mapRange constantCoeff (map_zero _) c =
      Finsupp.mapRange.linearMap (lcoeff (ZMod 2) 0) c := by
    ext x
    simp [coeff_zero_eq_eval_zero, constantCoeff_apply]
  simpa [heq] using isHomogeneous_mapRange_constantCoeff.map_mem hc

/-- The chains of `CF^∞` with polynomial coefficients are spanned by the chains `U ^ k x` with
`k ≥ 0`. -/
private theorem mem_minusLattice_iff_mem_span {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]} :
    c ∈ H.minusLattice ↔ c ∈ Submodule.span (ZMod 2)
      (Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ''
        {i | 0 ≤ i.2}) := by
  rw [mem_minusLattice_iff, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.basis_repr,
    Set.mem_ofPred_eq]
  refine ⟨fun h i hi => ?_, fun h x => ?_⟩
  · by_contra hneg
    exact hi (exists_toLaurent_eq_iff.mp (h i.1) i.2 (not_le.mp hneg))
  · rw [Set.mem_range, exists_toLaurent_eq_iff]
    intro k hk
    by_contra hne
    exact absurd (h ⟨x, k⟩ hne) (not_le.mpr hk)

variable (H gr) in
/-- `CF⁻` is a homogeneous submodule of `CF^∞`: it contains the homogeneous components of each of
its chains. -/
theorem isHomogeneous_minusLattice :
    DirectSum.SetLike.IsHomogeneous (H.infinityGrading gr).piece H.minusLattice := by
  intro q c hc
  rw [mem_minusLattice_iff_mem_span] at hc ⊢
  refine InternalGrading.isHomogeneous_span (H.infinityGrading gr) _ ?_ q hc
  rintro _ ⟨i, -, rfl⟩
  exact ⟨gr i.1 - 2 * i.2, Submodule.subset_span ⟨i, rfl, rfl⟩⟩

variable (H gr) in
/-- The grading of `CF⁺ = CF^∞ / CF⁻` by a grading `gr` of the generators: its degree-`q` piece is
the image of that of `CF^∞`, and the class of `U ^ k x`, `k < 0`, has degree `gr(x) - 2 k`. -/
noncomputable def plusGrading :
    InternalGrading (ZMod 2) ((H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) ℚ :=
  (H.infinityGrading gr).quotient H.minusLattice (isHomogeneous_minusLattice H gr)

/-- The degree-`q` piece of `CF⁺` is the image of the degree-`q` piece of `CF^∞`. -/
@[simp]
theorem plusGrading_piece (q : ℚ) :
    (H.plusGrading gr).piece q =
      (H.infinityGradedPiece gr q).map (H.minusLattice.mkQ.restrictScalars (ZMod 2)) :=
  InternalGrading.quotient_piece _ _ _ q

/-- A class of `CF⁺` has degree `q` exactly when it is the class of a chain of `CF^∞` of
degree `q`. -/
theorem mem_plusGrading_piece_iff {q : ℚ}
    {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice} :
    y ∈ (H.plusGrading gr).piece q ↔
      ∃ c ∈ H.infinityGradedPiece gr q, Submodule.Quotient.mk c = y :=
  InternalGrading.mem_quotient_piece_iff _ _ _

/-- The class of a chain of `CF^∞` of degree `q` has degree `q` in `CF⁺`. -/
theorem mk_mem_plusGrading_piece {q : ℚ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ H.infinityGradedPiece gr q) :
    (Submodule.Quotient.mk c : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) ∈
      (H.plusGrading gr).piece q :=
  InternalGrading.mk_mem_quotient_piece _ _ _ hc

/-- **`U` lowers the degree of `CF⁺` by two.** -/
theorem X_smul_mem_plusGrading_piece {q : ℚ}
    {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice} (hy : y ∈ (H.plusGrading gr).piece q) :
    (X : (ZMod 2)[X]) • y ∈ (H.plusGrading gr).piece (q - 2) := by
  obtain ⟨c, hc, rfl⟩ := mem_plusGrading_piece_iff.mp hy
  rw [← Submodule.Quotient.mk_smul]
  exact mk_mem_plusGrading_piece (X_smul_mem_infinityGradedPiece hc)

/-- **The inclusion of `CF̂` into `CF⁺` raises the degree by two.** It sends a generator `x` to the
class of `U⁻¹ x`, of degree `gr(x) + 2`. -/
theorem isHomogeneous_hatToPlus :
    LinearMap.IsHomogeneous H.hatToPlus (H.hatGrading gr).piece (H.plusGrading gr).piece 2 := by
  have hspan : (H.hatGrading gr).piece = fun q => Submodule.span (ZMod 2)
      ((fun x => Finsupp.single x (1 : ZMod 2)) '' {x | gr x = q}) :=
    funext fun q =>
      (InternalGrading.finsupp_piece _ _ q).trans (Finsupp.supported_eq_span_single _ _)
  rw [hspan]
  refine LinearMap.isHomogeneous_span_iff.2 ?_
  rintro p _ ⟨x, hx, rfl⟩
  rw [hatToPlus_single, map_one, one_mul]
  refine mk_mem_plusGrading_piece ?_
  convert single_T_mem_infinityGradedPiece (gr := gr) x (-1) using 2
  simp only [Set.mem_ofPred_eq] at hx
  rw [← hx]
  push_cast
  ring

/-! ### Gradings of the chain groups modulo a subgroup

For a Maslov grading `gr` modulo a subgroup `Λ` of `ℚ` the chain groups are graded by `ℚ ⧸ Λ`:
coarsening the gradings by `gr` above along `QuotientAddGroup.mk' Λ`
(`TauCeti.InternalGrading.coarsen`) gives the internal gradings `(H.hatGrading gr).coarsen _`,
`(H.minusGrading gr).coarsen _`, `(H.infinityGrading gr).coarsen _` and
`(H.plusGrading gr).coarsen _`, whose pieces are the `coarsenGrading` families below. The maps
of the flavor exact sequences keep their degrees after coarsening
(`LinearMap.IsHomogeneous.coarsenGrading`). -/

/-- **`U` lowers the degree of `CF⁻` by two after coarsening** along an additive map `f`, for
instance modulo a subgroup of `ℚ`. -/
theorem X_smul_mem_coarsenGrading_minusGradedPiece {κ : Type*} [AddMonoid κ] (f : ℚ →+ κ)
    {k : κ} {c : H.Generator →₀ (ZMod 2)[X]}
    (hc : c ∈ coarsenGrading (H.minusGradedPiece gr) f k) :
    (X : (ZMod 2)[X]) • c ∈ coarsenGrading (H.minusGradedPiece gr) f (k + f (-2)) :=
  smul_mem_coarsenGrading (fun _ _ hc => by
    rw [← sub_eq_add_neg]
    exact X_smul_mem_minusGradedPiece hc) f hc

/-- **Multiplication by `U ^ m` shifts the degree of `CF^∞` by `-2 m` after coarsening** along an
additive map `f`, for every integer `m`. -/
theorem T_smul_mem_coarsenGrading_infinityGradedPiece {κ : Type*} [AddMonoid κ]
    (f : ℚ →+ κ) {k : κ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ coarsenGrading (H.infinityGradedPiece gr) f k) (m : ℤ) :
    (T m : (ZMod 2)[T;T⁻¹]) • c ∈ coarsenGrading (H.infinityGradedPiece gr) f (k + f (-2 * m)) :=
  smul_mem_coarsenGrading (fun _ _ hc => by
    rw [neg_mul, ← sub_eq_add_neg]
    exact T_smul_mem_infinityGradedPiece hc m) f hc

/-- **`U` lowers the degree of `CF^∞` by two after coarsening** along an additive map `f`. -/
theorem X_smul_mem_coarsenGrading_infinityGradedPiece {κ : Type*} [AddMonoid κ] (f : ℚ →+ κ)
    {k : κ} {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ coarsenGrading (H.infinityGradedPiece gr) f k) :
    (X : (ZMod 2)[X]) • c ∈ coarsenGrading (H.infinityGradedPiece gr) f (k + f (-2)) :=
  smul_mem_coarsenGrading (fun _ _ hc => by
    rw [← sub_eq_add_neg]
    exact X_smul_mem_infinityGradedPiece hc) f hc

/-- The class in `CF⁺` of a chain of `CF^∞` of coarsened degree `k` has coarsened degree `k`: the
quotient map has degree `0` (`TauCeti.InternalGrading.isHomogeneous_mkQ`) also after coarsening. -/
theorem mk_mem_coarsenGrading_plusGrading_piece {κ : Type*} [AddMonoid κ] {f : ℚ → κ} {k : κ}
    {c : H.Generator →₀ (ZMod 2)[T;T⁻¹]}
    (hc : c ∈ coarsenGrading (H.infinityGradedPiece gr) f k) :
    (Submodule.Quotient.mk c : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice) ∈
      coarsenGrading (H.plusGrading gr).piece f k := by
  simpa only [add_zero, Submodule.mkQ_apply, plusGrading] using
    (((H.infinityGrading gr).isHomogeneous_mkQ H.minusLattice
      (isHomogeneous_minusLattice H gr)).coarsenGrading_zero f).map_mem hc

/-- A class of `CF⁺` has coarsened degree `k` exactly when it is the class of a chain of `CF^∞` of
coarsened degree `k`. -/
theorem mem_coarsenGrading_plusGrading_piece_iff {κ : Type*} [AddMonoid κ] {f : ℚ → κ} {k : κ}
    {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice} :
    y ∈ coarsenGrading (H.plusGrading gr).piece f k ↔
      ∃ c ∈ coarsenGrading (H.infinityGradedPiece gr) f k, Submodule.Quotient.mk c = y := by
  refine ⟨fun hy => ?_, fun ⟨c, hc, hcy⟩ => hcy ▸ mk_mem_coarsenGrading_plusGrading_piece hc⟩
  refine coarsenGrading_induction hy (fun q hq y hy => ?_) ⟨0, zero_mem _, rfl⟩ ?_
  · obtain ⟨c, hc, rfl⟩ := mem_plusGrading_piece_iff.mp hy
    exact ⟨c, hq ▸ mem_coarsenGrading_of_mem f hc, rfl⟩
  · rintro - - ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, add_mem hc hd, rfl⟩

/-- **`U` lowers the degree of `CF⁺` by two after coarsening** along an additive map `f`. -/
theorem X_smul_mem_coarsenGrading_plusGrading_piece {κ : Type*} [AddMonoid κ] (f : ℚ →+ κ)
    {k : κ} {y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice}
    (hy : y ∈ coarsenGrading (H.plusGrading gr).piece f k) :
    (X : (ZMod 2)[X]) • y ∈ coarsenGrading (H.plusGrading gr).piece f (k + f (-2)) :=
  smul_mem_coarsenGrading (fun _ _ hy => by
    rw [← sub_eq_add_neg]
    exact X_smul_mem_plusGrading_piece hy) f hy

section Differential

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]
  {χ : Region → ℤ} {Λ : AddSubgroup ℚ}

/-- The degree count shared by the hat and minus differentials: when `p - q ≡ c (mod Λ)`, a degree
`b` with `a - b - 1 = p - q - c` lies one below the degree `a` modulo `Λ`. -/
private theorem mk'_eq_mk'_add_neg_one_of_coe_sub_eq {p q c a b : ℚ}
    (h : ((p - q : ℚ) : ℚ ⧸ Λ) = (c : ℚ)) (hab : a - b - 1 = p - q - c) :
    QuotientAddGroup.mk' Λ b = QuotientAddGroup.mk' Λ a + QuotientAddGroup.mk' Λ (-1) := by
  rw [← map_add, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  convert neg_mem (QuotientAddGroup.eq_iff_sub_mem.mp h) using 1
  linarith

namespace IsMaslovGradingMod

/-- **The hat differential has degree `-1` modulo `Λ`** for a Maslov grading modulo `Λ`. -/
theorem isHomogeneous_hatDifferential (h : H.IsMaslovGradingMod Λ χ gr) :
    LinearMap.IsHomogeneous (H.hatDifferential χ)
      (coarsenGrading (H.hatGrading gr).piece (QuotientAddGroup.mk' Λ))
      (coarsenGrading (H.hatGrading gr).piece (QuotientAddGroup.mk' Λ))
      (QuotientAddGroup.mk' Λ (-1)) := by
  refine LinearMap.isHomogeneous_def.2 fun p c hc => ?_
  rw [InternalGrading.mem_coarsenGrading_finsupp_piece_iff] at hc ⊢
  intro y hy
  rw [hatDifferential_apply, Finsupp.sum] at hy
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  rw [← hc x (left_ne_zero_of_mul hx)]
  exact mk'_eq_mk'_add_neg_one_of_coe_sub_eq
    (h.coe_sub_eq_one_of_hatCoefficient_ne_zero (right_ne_zero_of_mul hx)) (by ring)

/-- **The minus differential has degree `-1` modulo `Λ`** for a Maslov grading modulo `Λ`. -/
theorem isHomogeneous_minusDifferential (h : H.IsMaslovGradingMod Λ χ gr) :
    LinearMap.IsHomogeneous (H.minusDifferential χ)
      (coarsenGrading (H.minusGradedPiece gr) (QuotientAddGroup.mk' Λ))
      (coarsenGrading (H.minusGradedPiece gr) (QuotientAddGroup.mk' Λ))
      (QuotientAddGroup.mk' Λ (-1)) := by
  -- Check the degree on the basis `U ^ k x` of `CF⁻`, which spans its pieces.
  refine LinearMap.isHomogeneous_coarsenGrading_span_iff.2 ?_
  rintro ⟨x, k⟩
  rw [mem_coarsenGrading_minusGradedPiece_iff]
  intro y j hj
  simp only [Finsupp.coe_basis, coe_basisMonomials, ← X_pow_eq_monomial,
    minusDifferential_single_apply, coeff_X_pow_mul'] at hj
  split_ifs at hj with hkj
  · exact mk'_eq_mk'_add_neg_one_of_coe_sub_eq
      (h.coe_sub_eq_one_sub_two_mul_of_coeff_minusCoefficient_ne_zero hj)
      (by push_cast [hkj]; ring)
  · exact absurd rfl hj

/-- **The infinity differential has degree `-1` modulo `Λ`** for a Maslov grading modulo `Λ`. -/
theorem isHomogeneous_infinityDifferential (h : H.IsMaslovGradingMod Λ χ gr) :
    LinearMap.IsHomogeneous (H.infinityDifferential χ)
      (coarsenGrading (H.infinityGradedPiece gr) (QuotientAddGroup.mk' Λ))
      (coarsenGrading (H.infinityGradedPiece gr) (QuotientAddGroup.mk' Λ))
      (QuotientAddGroup.mk' Λ (-1)) := by
  -- On the basis, `U ^ k x = U ^ k • x` and the infinity differential of `x` is the minus
  -- differential of `x`.
  refine LinearMap.isHomogeneous_coarsenGrading_span_iff.2 ?_
  rintro ⟨x, k⟩
  have hb : Finsupp.basis (fun _ : H.Generator => AddMonoidAlgebra.basis ℤ (ZMod 2)) ⟨x, k⟩ =
      (T k : (ZMod 2)[T;T⁻¹]) •
        Finsupp.mapRange toLaurent (map_zero _) (Finsupp.single x (1 : (ZMod 2)[X])) := by
    rw [Finsupp.mapRange_single, map_one, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [Finsupp.coe_basis, AddMonoidAlgebra.basis_apply, single_eq_C_mul_T, map_one,
      one_mul]
  rw [hb, map_smul, infinityDifferential_mapRange_toLaurent]
  have hx := h.isHomogeneous_minusDifferential.map_mem
    (mem_coarsenGrading_of_mem (QuotientAddGroup.mk' Λ) (single_X_pow_mem_minusGradedPiece x 0))
  rw [pow_zero] at hx
  -- The inclusion of `CF⁻` into `CF^∞` keeps the coarsened degree.
  have hx' := mapRange_toLaurent_mem_coarsenGrading_infinityGradedPiece hx
  convert T_smul_mem_coarsenGrading_infinityGradedPiece (QuotientAddGroup.mk' Λ) hx' k using 2
  simp only [← map_add]
  congr 1
  push_cast
  ring

/-- **The plus differential has degree `-1` modulo `Λ`** for a Maslov grading modulo `Λ`. -/
theorem isHomogeneous_plusDifferential (h : H.IsMaslovGradingMod Λ χ gr) :
    LinearMap.IsHomogeneous (H.plusDifferential χ)
      (coarsenGrading (H.plusGrading gr).piece (QuotientAddGroup.mk' Λ))
      (coarsenGrading (H.plusGrading gr).piece (QuotientAddGroup.mk' Λ))
      (QuotientAddGroup.mk' Λ (-1)) := by
  refine LinearMap.isHomogeneous_def.2 fun p y hy => ?_
  obtain ⟨c, hc, rfl⟩ := mem_coarsenGrading_plusGrading_piece_iff.mp hy
  rw [plusDifferential_mk]
  exact mk_mem_coarsenGrading_plusGrading_piece (h.isHomogeneous_infinityDifferential.map_mem hc)

end IsMaslovGradingMod

namespace IsMaslovGrading

/-! Coarsening along the quotient map of `ℚ` by `⊥`, which is injective
(`QuotientAddGroup.mk'_bot_injective`), merges no degrees, so these are the case `Λ = ⊥` of the
statements modulo `Λ`. -/

/-- **The hat differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_hatDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.hatDifferential χ) (H.hatGrading gr).piece (H.hatGrading gr).piece
      (-1) :=
  (h.isMaslovGradingMod ⊥).isHomogeneous_hatDifferential.of_coarsenGrading
    (f := QuotientAddGroup.mk' ⊥) QuotientAddGroup.mk'_bot_injective

/-- **The minus differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_minusDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.minusDifferential χ) (H.minusGradedPiece gr)
      (H.minusGradedPiece gr) (-1) :=
  (h.isMaslovGradingMod ⊥).isHomogeneous_minusDifferential.of_coarsenGrading
    (f := QuotientAddGroup.mk' ⊥) QuotientAddGroup.mk'_bot_injective

/-- **The infinity differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_infinityDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.infinityDifferential χ) (H.infinityGradedPiece gr)
      (H.infinityGradedPiece gr) (-1) :=
  (h.isMaslovGradingMod ⊥).isHomogeneous_infinityDifferential.of_coarsenGrading
    (f := QuotientAddGroup.mk' ⊥) QuotientAddGroup.mk'_bot_injective

/-- **The plus differential has degree `-1`** for a Maslov grading. -/
theorem isHomogeneous_plusDifferential (h : H.IsMaslovGrading χ gr) :
    LinearMap.IsHomogeneous (H.plusDifferential χ) (H.plusGrading gr).piece
      (H.plusGrading gr).piece (-1) :=
  (h.isMaslovGradingMod ⊥).isHomogeneous_plusDifferential.of_coarsenGrading
    (f := QuotientAddGroup.mk' ⊥) QuotientAddGroup.mk'_bot_injective

end IsMaslovGrading

end Differential

end ChainGrading

end HeegaardRegionSystem

end TauCeti
