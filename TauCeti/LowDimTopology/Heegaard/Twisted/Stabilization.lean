/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Stabilization
public import TauCeti.LowDimTopology.Heegaard.Twisted.Basic

/-!
# The twisted hat complex is unchanged by stabilization

Stabilizing a Heegaard diagram in a region `R₀` (`TauCeti.HeegaardRegionSystem.stabilize`), the
connected sum with a torus carrying a new `α`-curve and a new `β`-curve meeting in one point `x₀`,
does not change the domains, their Maslov indices, the periodic domains or the domains counted by
the hat differential (`TauCeti.HeegaardRegionSystem.isDomainBetween_stabilize_iff`,
`TauCeti.HeegaardRegionSystem.periodicDomains_stabilize`,
`TauCeti.HeegaardRegionSystem.hatDomains_stabilize`). This file shows that the same holds with
twisted coefficients (`TauCeti.HeegaardRegionSystem.twistedHatDifferential`): stabilization is an
isomorphism of twisted hat complexes, and so of twisted homologies.

**Coefficients.** The periodic domains of the stabilized diagram are those of the original diagram
as subgroups of the functions on the common set of regions, so the two group rings are identified
by the ring isomorphism `TauCeti.HeegaardRegionSystem.stabilizeTwistedRingEquiv`, sending each
monomial `t^P` to itself. The twisted complexes are compared along it, by semilinear maps.

**Reference domains.** Reference domains `D_x` of the original diagram induce reference domains of
the stabilized one (`TauCeti.HeegaardRegionSystem.ReferenceDomains.stabilize`): the reference
generator of `x ∪ {x₀}` is `x₀' ∪ {x₀}` for the reference generator `x₀'` of `x`, with the same
reference domain `D_x`. A counted domain from `x ∪ {x₀}` to `y ∪ {x₀}` is a counted domain from `x`
to `y`, with the same label (`TauCeti.HeegaardRegionSystem.ReferenceDomains.label_stabilize`), so
the twisted coefficients correspond under the ring isomorphism
(`TauCeti.HeegaardRegionSystem.twistedHatCoefficient_stabilize`), and the identification of chains
`x ↦ x ∪ {x₀}` with coefficients carried by the ring isomorphism
(`TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv`) intertwines the twisted hat
differentials
(`TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv_comp_twistedHatDifferential`).
Any other reference data of the stabilized diagram gives an isomorphic twisted homology by
`TauCeti.HeegaardRegionSystem.twistedHatHomologyEquiv`.

Together with `TauCeti.HeegaardRegionSystem.addBasepointTwistedHomologyEquiv` for an added
basepoint, this is the invariance of the twisted homology under the two kinds of stabilization
among the nice moves. As there, the vanishing of the square of the twisted differential is a
hypothesis wherever homology is formed; here it holds for the stabilized diagram exactly when it
holds for the original one
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_stabilize_comp_self_eq_zero_iff`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.stabilizeTwistedRingEquiv`: the identification of the group rings
  of periodic domains.
* `TauCeti.HeegaardRegionSystem.ReferenceDomains.stabilize`: the induced reference domains of the
  stabilized diagram.
* `TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv`: the semilinear identification of the
  twisted chain modules.
* `TauCeti.HeegaardRegionSystem.stabilizeTwistedHomologyEquiv`: the induced identification of
  twisted homologies.

## Main results

* `TauCeti.HeegaardRegionSystem.twistedHatCoefficient_stabilize`: the twisted coefficients of the
  stabilized diagram are those of the original diagram.
* `TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv_comp_twistedHatDifferential`: the
  identification of chains intertwines the twisted hat differentials.
* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_stabilize_comp_self_eq_zero_iff`: one
  twisted differential squares to zero exactly when the other does.

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830),
  §§7 and 9 (invariance under nice stabilizations, and the twisted complex in Theorem 9.4).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §10 (stabilization invariance).
-/

public section

open MonoidAlgebra Function

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint) (r₀ : Region)

section Ring

/-- The identification of the group ring of the periodic domains of a diagram with that of its
stabilization in the region `r₀`, induced by the equality of the periodic domains
(`TauCeti.HeegaardRegionSystem.periodicDomains_stabilize`): it sends each monomial `t^P` to
itself. -/
noncomputable def stabilizeTwistedRingEquiv :
    MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) ≃+*
      MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains) :=
  mapDomainRingEquiv (ZMod 2)
    (AddEquiv.toMultiplicative (AddEquiv.addSubgroupCongr (H.periodicDomains_stabilize r₀).symm))

/-- The identification sends the monomial `t^P` to the monomial of the same periodic domain. -/
@[simp]
theorem stabilizeTwistedRingEquiv_single (P : H.periodicDomains) (a : ZMod 2) :
    H.stabilizeTwistedRingEquiv r₀ (single (Multiplicative.ofAdd P) a) =
      single (Multiplicative.ofAdd ⟨P, (H.periodicDomains_stabilize r₀).ge P.property⟩) a := by
  simp only [stabilizeTwistedRingEquiv, mapDomainRingEquiv_single,
    AddEquiv.toMultiplicative_apply_apply, toAdd_ofAdd]
  refine congr(single (Multiplicative.ofAdd $(Subtype.ext ?_)) a)
  exact AddEquiv.addSubgroupCongr_apply _ P

/-- The inverse identification sends the monomial `t^P` to the monomial of the same periodic
domain. -/
@[simp]
theorem stabilizeTwistedRingEquiv_symm_single (P : (H.stabilize r₀).periodicDomains)
    (a : ZMod 2) :
    (H.stabilizeTwistedRingEquiv r₀).symm (single (Multiplicative.ofAdd P) a) =
      single (Multiplicative.ofAdd ⟨P, (H.periodicDomains_stabilize r₀).le P.property⟩) a := by
  rw [RingEquiv.symm_apply_eq, stabilizeTwistedRingEquiv_single]

/-- The identification of group rings and its inverse form a pair of inverse ring maps, so that
the twisted chain modules can be compared by semilinear equivalences along it. -/
instance : RingHomInvPair
    (H.stabilizeTwistedRingEquiv r₀ :
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains))
    ((H.stabilizeTwistedRingEquiv r₀).symm :
      MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :=
  .of_ringEquiv _

/-- The inverse of the identification of group rings and the identification form a pair of
inverse ring maps. -/
instance : RingHomInvPair
    ((H.stabilizeTwistedRingEquiv r₀).symm :
      MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))
    (H.stabilizeTwistedRingEquiv r₀ :
      MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains)) :=
  .of_ringEquiv_symm _

end Ring

namespace ReferenceDomains

variable {H}

/-- The reference domains of the stabilization in `r₀` induced by reference domains `D_x` of the
original diagram: the reference generator of `x ∪ {x₀}` is `x₀' ∪ {x₀}` for the reference generator
`x₀'` of `x`, and its reference domain is `D_x`. -/
noncomputable def stabilize (r : H.ReferenceDomains) (r₀ : Region) :
    (H.stabilize r₀).ReferenceDomains where
  base g := H.stabilizeGenerator r₀ (r.base ((H.stabilizeGeneratorEquiv r₀).symm g))
  domain g := r.domain ((H.stabilizeGeneratorEquiv r₀).symm g)
  isDomainBetween_domain g := by
    obtain ⟨x, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
    simpa using H.isDomainBetween_stabilize_iff.mpr (r.isDomainBetween_domain x)
  domain_basepoint g z := by
    simpa using r.domain_basepoint _ z
  base_eq_base {g g' D} hD hz := by
    obtain ⟨x, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
    obtain ⟨y, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g'
    simp only [stabilizeGeneratorEquiv_apply, stabilizeGeneratorEquiv_symm_apply] at hD ⊢
    rw [r.base_eq_base (H.isDomainBetween_stabilize_iff.mp hD) (by simpa using hz)]

variable (r : H.ReferenceDomains)

/-- The reference generator of `x ∪ {x₀}` is `x₀' ∪ {x₀}`, for the reference generator `x₀'` of
`x`. -/
@[simp]
theorem stabilize_base (x : H.Generator) :
    (r.stabilize r₀).base (H.stabilizeGenerator r₀ x) = H.stabilizeGenerator r₀ (r.base x) := by
  simp [stabilize]

/-- The reference domain of `x ∪ {x₀}` is that of `x`. -/
@[simp]
theorem stabilize_domain (x : H.Generator) :
    (r.stabilize r₀).domain (H.stabilizeGenerator r₀ x) = r.domain x := by
  simp [stabilize]

/-- The label of a domain from `x ∪ {x₀}` to `y ∪ {x₀}` in the stabilized diagram is its label
from `x` to `y` in the original diagram. -/
@[simp]
theorem label_stabilize (x y : H.Generator) (D : Region → ℤ) :
    (r.stabilize r₀).label (H.stabilizeGenerator r₀ x) (H.stabilizeGenerator r₀ y) D =
      r.label x y D := by
  simp [label_def]

end ReferenceDomains

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}
  {r : H.ReferenceDomains}

/-- **The twisted coefficients of the stabilized diagram.** The twisted coefficient of the
stabilization in `r₀` from `x ∪ {x₀}` to `y ∪ {x₀}`, for the induced reference domains, is the
twisted coefficient of the original diagram from `x` to `y`, under the identification of the group
rings. -/
theorem twistedHatCoefficient_stabilize (x y : H.Generator) :
    (H.stabilize r₀).twistedHatCoefficient (r.stabilize r₀) (stabilizeEuler χ r₀)
        (H.stabilizeGenerator r₀ x) (H.stabilizeGenerator r₀ y) =
      H.stabilizeTwistedRingEquiv r₀ (H.twistedHatCoefficient r χ x y) := by
  rw [twistedHatCoefficient_def, twistedHatCoefficient_def, AddEquivClass.map_finsum,
    ← finsum_comp_equiv (Set.equivOfEq (H.hatDomains_stabilize r₀ x y).symm)]
  refine finsum_congr fun D => ?_
  rw [stabilizeTwistedRingEquiv_single]
  congr 2
  exact Subtype.ext (by simp)

end Hat

section Differential

/-- The identification of the twisted chain module of a diagram with that of its stabilization in
`r₀`: the generator `x` goes to `x ∪ {x₀}`, and the coefficients are carried along the
identification of the group rings `TauCeti.HeegaardRegionSystem.stabilizeTwistedRingEquiv`. It is
semilinear along that identification. -/
noncomputable def stabilizeTwistedChainEquiv :
    (H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) ≃ₛₗ[
      (H.stabilizeTwistedRingEquiv r₀ :
        MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains))]
      (H.stabilize r₀).Generator →₀
        MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains) :=
  (Finsupp.mapRange.linearEquiv (H.stabilizeTwistedRingEquiv r₀).toSemilinearEquiv).trans
    (Finsupp.domLCongr (H.stabilizeGeneratorEquiv r₀))

/-- The identification sends `a x` to `σ(a) (x ∪ {x₀})`. -/
@[simp]
theorem stabilizeTwistedChainEquiv_single (x : H.Generator)
    (a : MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains)) :
    H.stabilizeTwistedChainEquiv r₀ (Finsupp.single x a) =
      Finsupp.single (H.stabilizeGenerator r₀ x) (H.stabilizeTwistedRingEquiv r₀ a) := by
  simp [stabilizeTwistedChainEquiv, Finsupp.domLCongr_apply]

/-- The coefficient of `x ∪ {x₀}` in the image of a chain is the image of the coefficient of
`x`. -/
@[simp]
theorem stabilizeTwistedChainEquiv_apply
    (c : H.Generator →₀ MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains))
    (x : H.Generator) :
    H.stabilizeTwistedChainEquiv r₀ c (H.stabilizeGenerator r₀ x) =
      H.stabilizeTwistedRingEquiv r₀ (c x) := by
  simp [stabilizeTwistedChainEquiv, Finsupp.domLCongr_apply, ← stabilizeGeneratorEquiv_apply]

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}
  {r : H.ReferenceDomains}

/-- **Stabilization does not change the twisted hat complex.** Under the identification of chains
`TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv`, the twisted hat differential of the
stabilized diagram, for the induced reference domains, is that of the original diagram. -/
theorem stabilizeTwistedChainEquiv_comp_twistedHatDifferential :
    (H.stabilizeTwistedChainEquiv r₀).toLinearMap ∘ₛₗ H.twistedHatDifferential r χ =
      (H.stabilize r₀).twistedHatDifferential (r.stabilize r₀) (stabilizeEuler χ r₀) ∘ₛₗ
        (H.stabilizeTwistedChainEquiv r₀).toLinearMap := by
  refine Finsupp.lhom_ext fun x a => Finsupp.ext fun g => ?_
  obtain ⟨y, rfl⟩ := (H.stabilizeGeneratorEquiv r₀).surjective g
  simp [twistedHatCoefficient_stabilize]

/-- The twisted hat differential of the stabilized diagram, for the induced reference domains,
squares to zero exactly when that of the original diagram does. -/
theorem twistedHatDifferential_stabilize_comp_self_eq_zero_iff :
    (H.stabilize r₀).twistedHatDifferential (r.stabilize r₀) (stabilizeEuler χ r₀) ∘ₗ
        (H.stabilize r₀).twistedHatDifferential (r.stabilize r₀) (stabilizeEuler χ r₀) = 0 ↔
      H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0 :=
  (H.stabilizeTwistedChainEquiv r₀).comp_self_eq_zero_iff_of_comp_eq
    (H.stabilizeTwistedChainEquiv_comp_twistedHatDifferential r₀)

end Differential

section Homology

variable [Fintype Point] [DecidableEq Region] [Fintype Region] {χ : Region → ℤ}
  {r : H.ReferenceDomains}

/-- **Stabilization does not change the twisted homology.** When the twisted hat differential of a
diagram squares to zero, the identification of chains
`TauCeti.HeegaardRegionSystem.stabilizeTwistedChainEquiv` induces an isomorphism from its twisted
homology onto that of the stabilization in `r₀`, for the induced reference domains, semilinear
along the identification of the group rings. -/
noncomputable def stabilizeTwistedHomologyEquiv
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0) :
    (H.twistedHatDifferential r χ).homology hd ≃ₛₗ[
      (H.stabilizeTwistedRingEquiv r₀ :
        MonoidAlgebra (ZMod 2) (Multiplicative H.periodicDomains) →+*
        MonoidAlgebra (ZMod 2) (Multiplicative (H.stabilize r₀).periodicDomains))]
      ((H.stabilize r₀).twistedHatDifferential (r.stabilize r₀) (stabilizeEuler χ r₀)).homology
        ((H.twistedHatDifferential_stabilize_comp_self_eq_zero_iff r₀).mpr hd) :=
  (H.stabilizeTwistedChainEquiv r₀).homologyEquiv hd _
    (H.stabilizeTwistedChainEquiv_comp_twistedHatDifferential r₀)

/-- The isomorphism of twisted homologies sends the class of a cycle `z` to the class of its image
under the identification of chains. -/
@[simp]
theorem stabilizeTwistedHomologyEquiv_mk
    (hd : H.twistedHatDifferential r χ ∘ₗ H.twistedHatDifferential r χ = 0)
    (z : LinearMap.ker (H.twistedHatDifferential r χ)) :
    H.stabilizeTwistedHomologyEquiv r₀ hd (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨H.stabilizeTwistedChainEquiv r₀ z,
        LinearMap.map_mem_ker_of_comp_eq (H.stabilizeTwistedChainEquiv r₀).toLinearMap
          (H.stabilizeTwistedChainEquiv_comp_twistedHatDifferential r₀) z.property⟩ :=
  LinearEquiv.homologyEquiv_mk _ hd _ _ z

end Homology

end HeegaardRegionSystem

end TauCeti
