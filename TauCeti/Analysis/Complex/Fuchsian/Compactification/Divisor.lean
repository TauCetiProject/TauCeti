/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Ramification
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Divisors of finite-index maps of Fuchsian quotients

A finite-index inclusion of discrete projective subgroups induces a finite holomorphic map of
compactified quotients. This file bundles that map so that the generic divisor pullback and
ramification-divisor constructions apply to it. Pullback weights at interior points are the
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

/-- The finite holomorphic map of compactified quotients induced by a finite-index inclusion.
Its forward function is the ordinary map on interior orbits and cusp orbits. No compactness
hypothesis is needed to construct it. -/
def finiteHolomorphicMap (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    FiniteHolomorphicMap Δ.CompactifiedQuotient Γ.CompactifiedQuotient := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  refine
    { toFun := compactifiedQuotientMap h
      holomorphic := mdifferentiable_compactifiedQuotientMap h
      finite_fiber := fun y ↦ by
        have hs : {x | compactifiedQuotientMap h x = y}.Finite :=
          Set.finite_coe_iff.mp (finite_fiber_compactifiedQuotientMap h y)
        simpa only [preimage, mem_singleton_iff] using hs
      nonconstant := ?_ }
  classical
  have : Nonempty Γ.CompactifiedQuotient := ⟨ofQuotient (Quotient.mk'' UpperHalfPlane.I)⟩
  let x : Δ.CompactifiedQuotient := ofQuotient (Quotient.mk'' UpperHalfPlane.I)
  have hpos : 0 < localMultiplicity (compactifiedQuotientMap h) x := by
    rw [localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]
    exact ellipticRamificationIndex_pos h _
  have hne := (localMultiplicity_pos_iff
    (.of_forall (mdifferentiable_compactifiedQuotientMap h))).mp hpos
  by_contra hn
  push Not at hn
  exact hne (eventuallyConst_iff_exists_eventuallyEq.mpr
    ⟨compactifiedQuotientMap h x, .of_forall fun y ↦ hn y x⟩)

/-- The bundled map has exactly the canonical compactified quotient map as its forward function. -/
@[simp]
theorem coe_finiteHolomorphicMap (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ⇑(finiteHolomorphicMap h) = compactifiedQuotientMap h :=
  (rfl)

variable (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ]

/-- Pullback at an interior orbit multiplies the coefficient by the relative index of the
elliptic stabilizers. -/
theorem coeff_divisorPullback_ofQuotient (D : WeilDivisor Γ.CompactifiedQuotient) (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (divisorPullback (finiteHolomorphicMap h) D)
        (ofQuotient (Quotient.mk'' z)) =
      (ellipticRamificationIndex h z : ℤ) *
        WeilDivisor.coeff D (ofQuotient (Quotient.mk'' z)) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_divisorPullback, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]
  simp

/-- Pullback at a cusp multiplies the coefficient by the relative index of its boundary
stabilizers. This formula requires no choice of scaling or generator. -/
theorem coeff_divisorPullback_ofCusp (D : WeilDivisor Γ.CompactifiedQuotient)
    (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (divisorPullback (finiteHolomorphicMap h) D)
        (ofCusp (Δ.cuspOrbitMk c)) =
      ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) : ℤ) *
        WeilDivisor.coeff D (ofCusp (cuspOrbitMap h (Δ.cuspOrbitMk c))) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_divisorPullback, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]
  simp

section Compact

variable [hcompact : letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  CompactSpace Δ.CompactifiedQuotient]

/-- Bundled finite holomorphic maps compose along subgroup towers, so generic divisor
functoriality and ramification chain rules apply to the canonical quotient maps. -/
@[simp]
theorem finiteHolomorphicMap_comp {Θ : Subgroup PSL(2, ℝ)} [DiscreteTopology Θ]
    (k : Γ ≤ Θ) [Γ.IsFiniteRelIndex Θ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    letI : Δ.IsFiniteRelIndex Θ := (inferInstance : Δ.IsFiniteRelIndex Γ).trans inferInstance
    (finiteHolomorphicMap k).comp (finiteHolomorphicMap h) = finiteHolomorphicMap (h.trans k) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let : Δ.IsFiniteRelIndex Θ := (inferInstance : Δ.IsFiniteRelIndex Γ).trans inferInstance
  apply FiniteHolomorphicMap.ext
  intro x
  simp

/-- The ramification coefficient at an interior orbit is the elliptic stabilizer index minus one.
In particular it vanishes at an unramified interior orbit. -/
theorem coeff_ramificationDivisor_ofQuotient (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (finiteHolomorphicMap h))
        (ofQuotient (Quotient.mk'' z)) = (ellipticRamificationIndex h z : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]

/-- The ramification coefficient at a cusp is its boundary stabilizer index minus one. -/
theorem coeff_ramificationDivisor_ofCusp (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (finiteHolomorphicMap h))
        (ofCusp (Δ.cuspOrbitMk c)) =
      ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]

/-- With compatible normalized cusp data, the ramification coefficient is the positive
cusp-width index minus one. -/
theorem coeff_ramificationDivisor_ofCusp_eq_widthIndex (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hσ : D.scaling = E.scaling) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    WeilDivisor.coeff (ramificationDivisor (finiteHolomorphicMap h)) (ofCusp D.cuspOrbit) =
      (Subgroup.CuspDatum.widthIndex h D E (D.cusp_eq_of_scaling_eq E hσ) hσ : ℤ) - 1 := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [coeff_ramificationDivisor, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex h D E hσ]

/-- An interior point is in the ramification support exactly when the elliptic stabilizer
index is greater than one. -/
@[simp]
theorem ofQuotient_mem_support_ramificationDivisor_iff (z : ℍ) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ofQuotient (Quotient.mk'' z) ∈ (ramificationDivisor (finiteHolomorphicMap h)).support ↔
      1 < ellipticRamificationIndex h z := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [← Finset.mem_coe, support_ramificationDivisor]
  simp only [mem_ofPred_eq, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofQuotient_eq_ellipticRamificationIndex]

/-- A cusp is in the ramification support exactly when its boundary stabilizer index is
greater than one. -/
@[simp]
theorem ofCusp_mem_support_ramificationDivisor_iff (c : Δ.cuspPoints) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ofCusp (Δ.cuspOrbitMk c) ∈ (ramificationDivisor (finiteHolomorphicMap h)).support ↔
      1 < (Δ.subgroupOf Γ).relIndex (stabilizer Γ (c : OnePoint ℝ)) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  rw [← Finset.mem_coe, support_ramificationDivisor]
  simp only [mem_ofPred_eq, coe_finiteHolomorphicMap,
    localMultiplicity_compactifiedQuotientMap_ofCusp_cuspOrbitMk]

/-- Total ramification splits into the interior contribution and the contribution from adjoined
cusps. Both sums have finite support; the pointwise weights are the stabilizer indices minus one. -/
theorem ramificationDegree_eq_interior_add_cusps :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    ramificationDegree (compactifiedQuotientMap h) =
      (∑ᶠ q : orbitRel.Quotient Δ ℍ,
        (localMultiplicity (compactifiedQuotientMap h) (ofQuotient q) - 1)) +
      ∑ᶠ C : Δ.CuspOrbit,
        (localMultiplicity (compactifiedQuotientMap h) (ofCusp C) - 1) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  let w : Δ.CompactifiedQuotient → ℕ := fun x ↦ localMultiplicity (compactifiedQuotientMap h) x - 1
  have hw : (support w).Finite := by
    refine ((finiteHolomorphicMap h).finite_setOf_one_lt_localMultiplicity).subset ?_
    intro x hx
    simpa only [mem_ofPred_eq, coe_finiteHolomorphicMap, mem_support, w,
      Nat.sub_ne_zero_iff_lt] using hx
  have hdisj : Disjoint (range (ofQuotient (Γ := Δ))) (range (ofCusp (Γ := Δ))) := by
    simp only [disjoint_left, mem_range]
    rintro x ⟨q, rfl⟩ ⟨C, heq⟩
    cases heq
  have hcover : range (ofQuotient (Γ := Δ)) ∪ range (ofCusp (Γ := Δ)) = univ := by
    ext x
    cases x <;> simp
  have hsum := finsum_mem_union' (f := w) hdisj
    (hw.inter_of_right _) (hw.inter_of_right _)
  have hinj : Injective (ofCusp (Γ := Δ)) := fun _ _ hC ↦ by cases hC; rfl
  rw [hcover, finsum_mem_univ, finsum_mem_range ofQuotient_injective,
    finsum_mem_range hinj] at hsum
  simpa only [ramificationDegree_def, w] using hsum

end Compact

end TauCeti.Fuchsian
