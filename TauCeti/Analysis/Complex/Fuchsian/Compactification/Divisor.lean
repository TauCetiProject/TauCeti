/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Ramification
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap

/-!
# Divisors of finite-index maps of Fuchsian quotients

A finite-index inclusion of discrete projective subgroups induces a finite holomorphic map of
compactified quotients. This file applies the generic divisor pullback and
ramification-divisor constructions to that bundled map. Pullback weights at interior points are the
indices of elliptic stabilizers; at cusps they are the indices of boundary stabilizers, or,
equivalently, the ratios of widths in compatible normalized cusp data.

When the source compactification is compact, the ramification divisor has coefficient `e - 1`
at each point. Its total degree splits into the interior and cusp contributions. Compactness is
an explicit hypothesis here: neither finite index nor the construction of the compactified
carrier alone supplies it.

The constructions use `TauCeti.RiemannSurface.divisorPullback` and
`TauCeti.RiemannSurface.ramificationDivisor`, without introducing separate Fuchsian divisors.
The ramification count follows Diamond and Shurman, *A First Course in Modular Forms*, §3.1.
-/

public noncomputable section

open Filter Function MulAction Set Topology UpperHalfPlane
open Subgroup Subgroup.CompactifiedQuotient TauCeti.AlgebraicGeometry TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

-- The representative coefficient formulas are rewrite lemmas: the generic coefficient simp lemmas
-- already simplify their left-hand sides, so marking these specializations @[simp] fails simpNF.

/-- Pullback at an interior orbit multiplies the coefficient by the relative index of the
elliptic stabilizers. -/
theorem coeff_divisorPullback_ofQuotient (D : WeilDivisor Γ.CompactifiedQuotient) (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (divisorPullback (compactifiedQuotientFiniteHolomorphicMap h) D)
        (ofQuotient (Quotient.mk'' z)) =
      (ellipticRamificationIndex h z : ℤ) *
        WeilDivisor.coeff D (ofQuotient (Quotient.mk'' z)) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_divisorPullback, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]
  simp

/-- Pullback at a cusp multiplies the coefficient by the relative index of its boundary
stabilizers. This formula requires no choice of scaling or generator. -/
theorem coeff_divisorPullback_ofCusp (D : WeilDivisor Γ.CompactifiedQuotient)
    (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (divisorPullback (compactifiedQuotientFiniteHolomorphicMap h) D)
        (ofCusp (Δ.cuspOrbitMk c)) =
      ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) : ℤ) *
        WeilDivisor.coeff D (ofCusp (cuspOrbitMap h (Δ.cuspOrbitMk c))) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_divisorPullback, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]
  simp

/-- With compatible normalized cusp data, pullback multiplies the coefficient by the positive
cusp-width index. -/
theorem coeff_divisorPullback_ofCusp_eq_widthIndex (A : WeilDivisor Γ.CompactifiedQuotient)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum) (hσ : D.scaling = E.scaling) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (divisorPullback (compactifiedQuotientFiniteHolomorphicMap h) A)
        (ofCusp D.cuspOrbit) =
      (Subgroup.CuspDatum.widthIndex h D E (D.cusp_eq_of_scaling_eq E hσ) hσ : ℤ) *
        WeilDivisor.coeff A (ofCusp E.cuspOrbit) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_divisorPullback, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex h D E hσ]
  simp [cuspOrbitMap_cuspOrbit_eq_of_cusp_eq h (D.cusp_eq_of_scaling_eq E hσ).symm]

section Compact

variable [hcompact : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  CompactSpace Δ.CompactifiedQuotient]

/-- The ramification coefficient at an interior orbit is the elliptic stabilizer index minus one.
In particular it vanishes at an unramified interior orbit. -/
theorem coeff_ramificationDivisor_ofQuotient (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (compactifiedQuotientFiniteHolomorphicMap h))
        (ofQuotient (Quotient.mk'' z)) = (ellipticRamificationIndex h z : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]

/-- The ramification coefficient at a cusp is its boundary stabilizer index minus one. -/
theorem coeff_ramificationDivisor_ofCusp (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (compactifiedQuotientFiniteHolomorphicMap h))
        (ofCusp (Δ.cuspOrbitMk c)) =
      ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]

/-- With compatible normalized cusp data, the ramification coefficient is the positive
cusp-width index minus one. -/
theorem coeff_ramificationDivisor_ofCusp_eq_widthIndex_sub_one (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : D.scaling = E.scaling) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (compactifiedQuotientFiniteHolomorphicMap h))
        (ofCusp D.cuspOrbit) =
      (Subgroup.CuspDatum.widthIndex h D E (D.cusp_eq_of_scaling_eq E hσ) hσ : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex h D E hσ]

/-- The ramification coefficient at an interior point is nonzero exactly when the elliptic
stabilizer index is greater than one. -/
@[simp]
theorem ramificationDivisor_apply_ofQuotient_ne_zero_iff (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    (ramificationDivisor (compactifiedQuotientFiniteHolomorphicMap h))
        (ofQuotient (Quotient.mk'' z)) ≠ 0 ↔
      1 < ellipticRamificationIndex h z := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [← Finsupp.mem_support_iff, ← Finset.mem_coe, support_ramificationDivisor]
  simp only [mem_ofPred_eq, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]

/-- The ramification coefficient at a cusp is nonzero exactly when its boundary stabilizer index is
greater than one. -/
@[simp]
theorem ramificationDivisor_apply_ofCusp_ne_zero_iff (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    (ramificationDivisor (compactifiedQuotientFiniteHolomorphicMap h))
        (ofCusp (Δ.cuspOrbitMk c)) ≠ 0 ↔
      1 < (Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [← Finsupp.mem_support_iff, ← Finset.mem_coe, support_ramificationDivisor]
  simp only [mem_ofPred_eq, coe_compactifiedQuotientFiniteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]

/-- Total ramification splits into the interior contribution and the contribution from adjoined
cusps, with weights equal to stabilizer indices minus one. The formula holds for any choice
of interior and cusp representatives, and both sums have finite support. -/
theorem ramificationDegree_eq_interior_add_cusps
    (z : orbitRel.Quotient Δ ℍ → ℍ) (hz : ∀ q, Quotient.mk'' (z q) = q)
    (c : Δ.CuspOrbit → Δ.cuspPoints) (hc : ∀ C, Δ.cuspOrbitMk (c C) = C) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ramificationDegree (compactifiedQuotientMap h) =
      (∑ᶠ q : orbitRel.Quotient Δ ℍ,
        (ellipticRamificationIndex h (z q) - 1)) +
      ∑ᶠ C : Δ.CuspOrbit,
        ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let w : Δ.CompactifiedQuotient → ℕ := fun x ↦ localMultiplicity (compactifiedQuotientMap h) x - 1
  have hw : (support w).Finite := by
    refine
      ((compactifiedQuotientFiniteHolomorphicMap h).finite_setOf_one_lt_localMultiplicity).subset ?_
    intro x hx
    simpa only [mem_ofPred_eq, coe_compactifiedQuotientFiniteHolomorphicMap, mem_support, w,
      Nat.sub_ne_zero_iff_lt] using hx
  have hdisj : Disjoint (range (ofQuotient (Γ := Δ))) (range (ofCusp (Γ := Δ))) := by
    rw [← compl_range_ofQuotient]
    exact disjoint_compl_right
  have hcover : range (ofQuotient (Γ := Δ)) ∪ range (ofCusp (Γ := Δ)) = univ := by
    rw [← compl_range_ofQuotient, union_compl_self]
  have hsum := finsum_mem_union' (f := w) hdisj
    (hw.inter_of_right _) (hw.inter_of_right _)
  have hinj : Injective (ofCusp (Γ := Δ)) := fun _ _ hC ↦ by cases hC; rfl
  rw [hcover, finsum_mem_univ, finsum_mem_range ofQuotient_injective,
    finsum_mem_range hinj] at hsum
  have hinterior (q : orbitRel.Quotient Δ ℍ) :
      w (ofQuotient q) = ellipticRamificationIndex h (z q) - 1 := by
    conv_lhs => rw [← hz q]
    exact congrArg (fun n : ℕ ↦ n - 1)
      (localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex h (z q))
  have hcusps (C : Δ.CuspOrbit) :
      w (ofCusp C) = (Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1 := by
    conv_lhs => rw [← hc C]
    exact congrArg (fun n : ℕ ↦ n - 1)
      (localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk h (c C))
  simp_rw [hinterior, hcusps] at hsum
  simpa only [ramificationDegree_def, w] using hsum

end Compact

end TauCeti.Fuchsian
