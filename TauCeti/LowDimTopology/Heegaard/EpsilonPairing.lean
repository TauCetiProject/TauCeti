/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.CurveHomology
public import TauCeti.LowDimTopology.Heegaard.RelativeGrading

/-!
# Pairing `ε(x, y)` with periodic domains

Let `(Σ, α, β, z)` be a pointed Heegaard diagram of a closed `3`-manifold `Y`. Ozsváth and Szabó
show that the spin^c structures of two generators differ by the Poincaré dual of their class
`ε(x, y) ∈ H₁(Y; ℤ)`, `s_z(y) - s_z(x) = PD(ε(x, y))`, and that the first Chern class of `s_z(x)`
evaluates on the class `H(P) ∈ H₂(Y; ℤ)` of a periodic domain `P` as
`⟨c₁(s_z(x)), H(P)⟩ = e(P) + 2 n_x(P)`, the combinatorial Maslov index of `P` at `x`. Since
`c₁(s + a) = c₁(s) + 2a`, the two facts together predict the *change-of-generator law*

`μ_y(P) - μ_x(P) = 2 (n_y(P) - n_x(P)) = 2 ⟨ε(x, y), H(P)⟩`.

This file proves the combinatorial form of this law for the incidence data
`TauCeti.HeegaardRegionSystem`, with `ε(x, y)` its class in
`TauCeti.HeegaardRegionSystem.CurveHomology`.

The pairing of a `1`-chain `c` on `α ∪ β` with a domain `P` is `∑_q ∂(c ∩ α)(q) n_q(P)`: the
boundary of the `α`-part of `c`, a `0`-chain on the intersection points, paired with the point
measures of `P` (`TauCeti.HeegaardRegionSystem.arcPairing`). For a chain connecting `x` to `y`
the boundary of the `α`-part is `y - x`, so the pairing is `n_y(P) - n_x(P)` with no hypothesis on
`P`. The content is that this pairing descends to `CurveHomology` when the `β`-part of the
boundary of `P` is a sum of whole `β`-curves, as it is for a periodic domain: it vanishes on whole
curves because their `α`-part has no boundary, and on the boundary of a domain `D` by the
reciprocity of point measures
(`sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_zero`),
which turns it into the pairing of `∂(∂P ∩ β) = 0` with the point measures of `D`. On a geometric
diagram the two theorems recalled above identify the pairing of `ε(x, y)` with a periodic domain
`P` with `⟨PD(ε(x, y)), H(P)⟩`; that identification is not formalized here.

So the periodic Maslov indices at `y` are those at `x` shifted by `2 ⟨ε(x, y), P⟩`. In particular
they agree when `ε(x, y)` pairs to zero with every periodic domain, for instance when it has finite
order: generators whose spin^c structures differ by a torsion class have the same divisibility of
the first Chern class. This extends
`TauCeti.HeegaardRegionSystem.IsDomainBetween.periodicMaslovIndices_eq`, the case `ε(x, y) = 0`.

## Main definitions

* `TauCeti.HeegaardRegionSystem.arcPairing`: the pairing `∑_q ∂(c ∩ α)(q) n_q(P)` of a `1`-chain
  `c` on `α ∪ β` with a domain `P`.
* `TauCeti.HeegaardRegionSystem.CurveHomology.pairing`: the induced pairing on `CurveHomology`,
  additive in a domain whose `β`-boundary is a sum of whole `β`-curves.

## Main results

* `TauCeti.HeegaardRegionSystem.arcPairing_domainBoundary`: pairing the boundary of a domain `D`
  with `P` is minus pairing `∂(∂P ∩ β)` with the point measures of `D`.
* `TauCeti.HeegaardRegionSystem.arcPairing_eq_neg_sum_betaArcBoundary_mul_pointMeasure`: on a
  cycle the pairing can also be read along `β`.
* `TauCeti.HeegaardRegionSystem.IsConnectingChain.arcPairing_eq`: a chain connecting `x` to `y`
  pairs with `P` to `n_y(P) - n_x(P)`.
* `TauCeti.HeegaardRegionSystem.CurveHomology.pairing_epsilon`: `⟨ε(x, y), P⟩ = n_y(P) - n_x(P)`.
* `TauCeti.HeegaardRegionSystem.maslovIndex_self_eq_add_two_mul_pairing_epsilon`: the
  change-of-generator law `μ_y(P) = μ_x(P) + 2 ⟨ε(x, y), P⟩`.
* `mem_periodicMaslovIndices_iff_exists_add_two_mul_pairing_epsilon`:
  the periodic Maslov indices at `y` are those at `x` shifted by `2 ⟨ε(x, y), P⟩`.
* `TauCeti.HeegaardRegionSystem.periodicMaslovIndices_eq_of_isOfFinAddOrder_epsilon`: generators
  whose class `ε(x, y)` has finite order have the same periodic Maslov indices.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Definition 2.11 and Lemma 2.19
  (`s_z(y) - s_z(x) = PD(ε(x, y))`).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), Proposition 7.5
  (`⟨c₁(s_z(x)), H(P)⟩ = e(P) + 2 n_x(P)`).
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), Lemma 4.11 (the same formula
  in the cylindrical setting).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint) [Fintype Point]

open Finset

section ArcPairing

/-- The pairing `∑_q ∂(c ∩ α)(q) n_q(P)` of a domain `P` with a `1`-chain `c` on `α ∪ β`: the
boundary of the `α`-part of `c` paired with the point measures of `P`. It is additive in both
arguments. -/
def arcPairing : (Region → ℤ) →+ (Point → ℤ) × (Point → ℤ) →+ ℚ where
  toFun P :=
    { toFun c := ∑ q, (H.alphaArcBoundary c.1 q : ℚ) * H.pointMeasure P q
      map_zero' := by
        simp only [Prod.fst_zero, map_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
          sum_const_zero]
      map_add' c d := by
        simp only [Prod.fst_add, map_add, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib] }
  map_zero' := AddMonoidHom.ext fun c => by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero, Pi.zero_apply, mul_zero,
      sum_const_zero, AddMonoidHom.zero_apply]
  map_add' P Q := AddMonoidHom.ext fun c => by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, Pi.add_apply, mul_add,
      sum_add_distrib, AddMonoidHom.add_apply]

@[simp]
theorem arcPairing_apply (P : Region → ℤ) (c : (Point → ℤ) × (Point → ℤ)) :
    H.arcPairing P c = ∑ q, (H.alphaArcBoundary c.1 q : ℚ) * H.pointMeasure P q :=
  (rfl)

/-- On a cycle, the pairing can also be read along `β`: it is minus the boundary of the `β`-part
paired with the point measures. -/
theorem arcPairing_eq_neg_sum_betaArcBoundary_mul_pointMeasure {c : (Point → ℤ) × (Point → ℤ)}
    (hc : c ∈ H.arcCycles) (P : Region → ℤ) :
    H.arcPairing P c = -∑ q, (H.betaArcBoundary c.2 q : ℚ) * H.pointMeasure P q := by
  rw [mem_arcCycles_iff, add_eq_zero_iff_eq_neg] at hc
  rw [arcPairing_apply, hc]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib]

/-- A combination of whole curves pairs to zero with every domain, since its `α`-part has no
boundary. -/
theorem arcPairing_eq_zero_of_mem_curveCycles {c : (Point → ℤ) × (Point → ℤ)}
    (hc : c ∈ H.curveCycles) (P : Region → ℤ) : H.arcPairing P c = 0 := by
  rw [arcPairing_apply, (mem_curveCycles_iff.mp hc).1]
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, sum_const_zero]

/-- Pairing the boundary of a domain `D` with `P` is minus pairing `∂(∂P ∩ β)` with the point
measures of `D`. -/
theorem arcPairing_domainBoundary (P D : Region → ℤ) :
    H.arcPairing P (H.domainBoundary D) =
      -∑ q, (H.betaArcBoundary (H.betaBoundary P) q : ℚ) * H.pointMeasure D q := by
  rw [arcPairing_apply, domainBoundary_apply, eq_neg_iff_add_eq_zero]
  exact H.sum_alphaArcBoundary_mul_pointMeasure_add_sum_betaArcBoundary_mul_pointMeasure_eq_zero D P

/-- If the `β`-part of the boundary of `P` is a sum of whole `β`-curves, then the boundary of every
domain pairs to zero with `P`. -/
theorem arcPairing_domainBoundary_eq_zero {P : Region → ℤ}
    (hP : H.betaArcBoundary (H.betaBoundary P) = 0) (D : Region → ℤ) :
    H.arcPairing P (H.domainBoundary D) = 0 := by
  rw [arcPairing_domainBoundary, hP]
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, sum_const_zero, neg_zero]

/-- If the `β`-part of the boundary of `P` is a sum of whole `β`-curves, then every relation of
`CurveHomology` pairs to zero with `P`. -/
theorem arcPairing_eq_zero_of_mem_arcRelations {P : Region → ℤ}
    (hP : H.betaArcBoundary (H.betaBoundary P) = 0) {c : (Point → ℤ) × (Point → ℤ)}
    (hc : c ∈ H.arcRelations) : H.arcPairing P c = 0 := by
  obtain ⟨D, hD⟩ := mem_arcRelations_iff.mp hc
  rw [← sub_add_cancel c (H.domainBoundary D), map_add,
    H.arcPairing_eq_zero_of_mem_curveCycles hD, H.arcPairing_domainBoundary_eq_zero hP, add_zero]

variable {H} in
/-- A chain connecting `x` to `y` pairs with every domain `P` to `n_y(P) - n_x(P)`. -/
theorem IsConnectingChain.arcPairing_eq {x y : H.Generator} {c : (Point → ℤ) × (Point → ℤ)}
    (hc : H.IsConnectingChain x y c) (P : Region → ℤ) :
    H.arcPairing P c = H.generatorPointMeasure y P - H.generatorPointMeasure x P := by
  rw [arcPairing_apply, (isConnectingChain_iff.mp hc).1]
  simp only [Pi.sub_apply, Int.cast_sub, sub_mul, sum_sub_distrib,
    ← generatorPointMeasure_eq_sum_generatorChain]

end ArcPairing

section CurveHomology

/-- The pairing of `CurveHomology` with the domains `P` whose `β`-boundary is a sum of whole
`β`-curves, such as the periodic domains, bundled as an additive map in `P`: the class of a cycle
`c` pairs to `∑_q ∂(c ∩ α)(q) n_q(P)`. The class `ε(x, y)` pairs to `n_y(P) - n_x(P)`
(`TauCeti.HeegaardRegionSystem.CurveHomology.pairing_epsilon`). -/
def CurveHomology.pairing :
    (H.betaArcBoundary.comp H.betaBoundary).ker →+ H.CurveHomology →+ ℚ where
  toFun P := CurveHomology.lift H ((H.arcPairing P).comp H.arcCycles.subtype) fun _ hc =>
    H.arcPairing_eq_zero_of_mem_arcRelations P.property hc
  map_zero' := by
    ext c
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, CurveHomology.lift_mk,
      AddSubgroup.coe_zero, map_zero, AddMonoidHom.zero_apply]
  map_add' P Q := by
    ext c
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, CurveHomology.lift_mk,
      AddSubgroup.coe_add, map_add, AddMonoidHom.add_apply]

@[simp]
theorem CurveHomology.pairing_mk (P : (H.betaArcBoundary.comp H.betaBoundary).ker)
    (c : H.arcCycles) :
    CurveHomology.pairing H P (CurveHomology.mk H c) = H.arcPairing P c :=
  CurveHomology.lift_mk H _ _ c

variable {H}

/-- The class `ε(x, y)` pairs with a domain `P` to `n_y(P) - n_x(P)`. -/
@[simp]
theorem CurveHomology.pairing_epsilon (P : (H.betaArcBoundary.comp H.betaBoundary).ker)
    (x y : H.Generator) :
    CurveHomology.pairing H P (H.epsilon x y) =
      H.generatorPointMeasure y P - H.generatorPointMeasure x P := by
  obtain ⟨c, hc⟩ := H.exists_isConnectingChain x y
  rw [hc.epsilon_eq, pairing_mk, hc.arcPairing_eq]

end CurveHomology

section MaslovIndex

variable {H} [DecidableEq Region] [Fintype Region]

/-- The change-of-generator law for the Maslov index of a domain `P` whose `β`-boundary is a sum
of whole `β`-curves: `μ_y(P) = μ_x(P) + 2 ⟨ε(x, y), P⟩`. For a periodic domain on a geometric
diagram this is the evaluation on `H(P)` of `c₁(s_z(y)) = c₁(s_z(x)) + 2 PD(ε(x, y))`. -/
theorem maslovIndex_self_eq_add_two_mul_pairing_epsilon (χ : Region → ℤ)
    (P : (H.betaArcBoundary.comp H.betaBoundary).ker) (x y : H.Generator) :
    H.maslovIndex χ y y P =
      H.maslovIndex χ x x P + 2 * CurveHomology.pairing H P (H.epsilon x y) := by
  rw [CurveHomology.pairing_epsilon, maslovIndex_apply, maslovIndex_apply]
  ring

/-- The periodic Maslov indices at `y` are those at `x` shifted by `2 ⟨ε(x, y), P⟩`: a rational
number is a periodic Maslov index at `y` exactly when it is `μ_x(P) + 2 ⟨ε(x, y), P⟩` for a
periodic domain `P`. -/
theorem mem_periodicMaslovIndices_iff_exists_add_two_mul_pairing_epsilon (χ : Region → ℤ)
    (x y : H.Generator) {q : ℚ} :
    q ∈ H.periodicMaslovIndices χ y ↔ ∃ P : (H.betaArcBoundary.comp H.betaBoundary).ker,
      (P : Region → ℤ) ∈ H.periodicDomains ∧
        H.maslovIndex χ x x P + 2 * CurveHomology.pairing H P (H.epsilon x y) = q := by
  simp only [mem_periodicMaslovIndices_iff, ← maslovIndex_self_eq_add_two_mul_pairing_epsilon]
  exact ⟨fun ⟨P, hP, h⟩ => ⟨⟨P, (mem_periodicDomains_iff.mp hP).2.2⟩, hP, h⟩,
    fun ⟨P, hP, h⟩ => ⟨P, hP, h⟩⟩

/-- Generators `x`, `y` whose class `ε(x, y)` pairs to zero with every periodic domain have the
same periodic Maslov indices. -/
theorem periodicMaslovIndices_eq_of_forall_pairing_epsilon_eq_zero {χ : Region → ℤ}
    {x y : H.Generator}
    (h : ∀ P : (H.betaArcBoundary.comp H.betaBoundary).ker, (P : Region → ℤ) ∈ H.periodicDomains →
      CurveHomology.pairing H P (H.epsilon x y) = 0) :
    H.periodicMaslovIndices χ x = H.periodicMaslovIndices χ y := by
  ext q
  rw [mem_periodicMaslovIndices_iff_exists_add_two_mul_pairing_epsilon χ x y,
    mem_periodicMaslovIndices_iff]
  refine ⟨fun ⟨P, hP, hq⟩ => ⟨⟨P, (mem_periodicDomains_iff.mp hP).2.2⟩, hP, ?_⟩,
    fun ⟨P, hP, hq⟩ => ⟨P, hP, ?_⟩⟩
  · rwa [h _ hP, mul_zero, add_zero]
  · rwa [h P hP, mul_zero, add_zero] at hq

/-- Generators whose class `ε(x, y)` has finite order have the same periodic Maslov indices. On a
geometric diagram this is the case of generators whose spin^c structures differ by a torsion
class. -/
theorem periodicMaslovIndices_eq_of_isOfFinAddOrder_epsilon {χ : Region → ℤ} {x y : H.Generator}
    (h : IsOfFinAddOrder (H.epsilon x y)) :
    H.periodicMaslovIndices χ x = H.periodicMaslovIndices χ y :=
  periodicMaslovIndices_eq_of_forall_pairing_epsilon_eq_zero fun P _ =>
    ((CurveHomology.pairing H P).isOfFinAddOrder h).eq_zero'

end MaslovIndex

end HeegaardRegionSystem

end TauCeti
