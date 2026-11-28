/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
public import TauCeti.LowDimTopology.Heegaard.AlphaComponent
public import TauCeti.LowDimTopology.Heegaard.Knot.Full

/-!
# Integrality and differentials of the Alexander multigrading of a link diagram

A link `L = L₁ ∪ ⋯ ∪ L_ℓ` in a closed three-manifold is presented by a multi-pointed Heegaard
diagram `(Σ, α, β, w, z)`, in which every basepoint is a `w` or a `z` of one of the components
`L_q`. The generators of the link Floer complex carry one Alexander grading for each component.
For generators `x`, `y` joined by a Whitney disk `φ`, the `q`-th grading changes by the
multiplicities of `φ` at the basepoints of `L_q`:

`A_q(x) - A_q(y) = ∑_{z ∈ zs q} n_z(φ) - ∑_{w ∈ ws q} n_w(φ)`.

The relative multigrading `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading ws zs`,
its periodic values `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues ws zs` and
its additivity, antisymmetry and filtration properties, and the Alexander function for the `w`'s
given by the total grading `∑_q A_q`
(`TauCeti.HeegaardRegionSystem.isAlexanderFunction_sum_relativeComponentAlexanderGrading`), are in
`TauCeti.LowDimTopology.Heegaard.AlexanderGrading`, where the relative Alexander grading of a knot
is its case of a single component with one `w` and one `z`. This file proves the results that use
the components of `Σ - α` and the full multi-pointed differential.

In a link diagram in the sense of Ozsváth and Szabó, each component of `Σ - α` contains exactly
one `w` and one `z`, both on the same component of the link, so the domain of that component of
`Σ - α` has vanishing multiplicity vector. Every domain from a generator to itself is a combination
of these components plus a domain with multiplicity zero at the `w`'s, so the periodic values
vanish, and the multigrading is a vector of integers, as soon as the multiplicity vector vanishes
on the latter domains
(`TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero`). With
two or more `w`'s these need not be zero: if `A` and `B` are the components of `Σ - α` and of
`Σ - β` through the same `w`, then `A - B` is one of them. For a link in `S³` they are combinations
of components of `Σ - α` and of `Σ - β`, each with vanishing multiplicity vector, but the
components of `Σ - β` are not formalized here, so the results below that need the periodic values
to vanish take this as a hypothesis.

* A term `∏_b X_b ^ m b · y` of the full multi-pointed differential of `x`
  (`TauCeti.LowDimTopology.Heegaard.Knot.Full`) has
  `A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`
  (`relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero`), so grading the
  variable `X_z` of a `z` on `L_q` by `+1` in the `q`-th grading and that of a `w` on `L_q` by
  `-1`, the full differential preserves every Alexander grading.

As for the knot grading, the comparison of domains with Whitney disks and of the multigrading with
relative spin^c structures is geometric and is not formalized here.

## Main results

* `TauCeti.HeegaardRegionSystem.periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero`:
  the periodic values vanish for a link diagram when the multiplicity vector vanishes on the
  domains with multiplicity zero at the `w`'s whose boundary is a combination of whole curves.
* In the namespace `TauCeti.HeegaardRegionSystem`,
  `relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero` and its version modulo
  the periodic values: the gradings of the terms of the full differential.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3: multi-pointed diagrams of links
  and the Alexander multigrading.
* C. Manolescu, P. Ozsváth, Z. Szabó and D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. **11** (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), §2: the
  multigrading computed from several basepoints on each component.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint} {K : Type*} {ws zs : K → Finset Basepoint}
  {x y : H.Generator}

/-- **A criterion for an integral Alexander multigrading.** Let `ι` pick out the `w`'s of a link
diagram, lying in distinct components of `Σ - α`, and suppose that the domain of each of these
components has vanishing Alexander multiplicity vector, as when it contains exactly one `w` and
one `z`, both on the same component of the link. If every domain with multiplicity zero at the
`w`'s whose boundary is a combination of whole curves has vanishing Alexander multiplicity vector,
then the periodic values vanish: a domain whose boundary is a combination of whole curves is such
a domain plus a combination of these components of `Σ - α`. With two or more `w`'s, the domains
with multiplicity zero at the `w`'s include the differences `A - B` of the components of `Σ - α`
and `Σ - β` through the same `w`, so `hP` does not ask them to be zero. -/
theorem periodicComponentAlexanderValues_eq_bot_of_forall_eq_zero {W : Type*} [Finite W]
    {ι : W → Basepoint}
    (hι : ∀ i j, H.SameAlphaComponent (H.basepoint (ι i)) (H.basepoint (ι j)) → i = j)
    (hP : ∀ P : Region → ℤ, H.alphaArcBoundary (H.alphaBoundary P) = 0 →
      H.betaArcBoundary (H.betaBoundary P) = 0 → (∀ i, P (H.basepoint (ι i)) = 0) →
        H.componentAlexanderMultiplicity ws zs P = 0)
    (hA : ∀ i, H.componentAlexanderMultiplicity ws zs
      (H.alphaComponentDomain (H.basepoint (ι i))) = 0) :
    H.periodicComponentAlexanderValues ws zs = ⊥ := by
  have := Fintype.ofFinite W
  refine periodicComponentAlexanderValues_eq_bot_iff.mpr fun E hα hβ => ?_
  -- `E` minus its components of `Σ - α` through the `w`'s vanishes at the `w`'s
  have hE : H.componentAlexanderMultiplicity ws zs E = H.componentAlexanderMultiplicity ws zs
      (∑ i, E (H.basepoint (ι i)) • H.alphaComponentDomain (H.basepoint (ι i))) := by
    rw [← sub_eq_zero, ← map_sub]
    refine hP _ (by simp only [map_sub, map_sum, map_zsmul, hα, smul_zero, Finset.sum_const_zero,
        alphaArcBoundary_alphaBoundary_alphaComponentDomain, sub_zero])
      (by simp only [map_sub, map_sum, map_zsmul, hβ, betaBoundary_alphaComponentDomain,
        smul_zero, Finset.sum_const_zero, sub_zero]) fun j => ?_
    rw [Pi.sub_apply, sum_smul_alphaComponentDomain_basepoint_apply_basepoint hι, sub_self]
  rw [hE, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_zsmul, hA i, smul_zero]

section Differentials

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]
  {χ : Region → ℤ}

/-- **The full differential preserves the Alexander multigrading**, modulo the periodic values. A
term `∏_b X_b ^ m b` of the full coefficient from `x` to `y` has relative Alexander multigrading
`A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`. -/
theorem coe_relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
    {m : Basepoint →₀ ℕ} (h : (H.fullCoefficient χ x y).coeff m ≠ 0) :
    (H.relativeComponentAlexanderGrading ws zs x y :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) =
      ((fun q => ∑ b ∈ zs q, (m b : ℤ) - ∑ b ∈ ws q, (m b : ℤ) : K → ℤ) :
        (K → ℤ) ⧸ H.periodicComponentAlexanderValues ws zs) := by
  obtain ⟨D, hD, hm⟩ := exists_mem_minusDomains_of_coeff_fullCoefficient_ne_zero h
  rw [(mem_minusDomains_iff.mp hD).1.coe_relativeComponentAlexanderGrading_eq]
  congr 1
  ext q
  simp [hm]

/-- **The full differential preserves the Alexander multigrading.** When the periodic values
vanish, a term `∏_b X_b ^ m b` of the full coefficient from `x` to `y` has
relative Alexander multigrading `A_q(x, y) = ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w`. Grading
`∏_b X_b ^ m b · y` by `A_q(y) + ∑_{z ∈ zs q} m z - ∑_{w ∈ ws q} m w` in the `q`-th grading, the
full differential preserves every Alexander grading. -/
theorem relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
    (hA : H.periodicComponentAlexanderValues ws zs = ⊥) {m : Basepoint →₀ ℕ}
    (h : (H.fullCoefficient χ x y).coeff m ≠ 0) (q : K) :
    H.relativeComponentAlexanderGrading ws zs x y q =
      ∑ b ∈ zs q, (m b : ℤ) - ∑ b ∈ ws q, (m b : ℤ) := by
  obtain ⟨D, hD, hm⟩ := exists_mem_minusDomains_of_coeff_fullCoefficient_ne_zero h
  simp [(mem_minusDomains_iff.mp hD).1.relativeComponentAlexanderGrading_eq hA, hm]

end Differentials

end HeegaardRegionSystem

end TauCeti
