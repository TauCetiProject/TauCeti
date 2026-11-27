/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.LensSpace.Diagram
public import TauCeti.LowDimTopology.Heegaard.Twisted.AddBasepoint
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# The twisted hat complex of a lens space with an added basepoint

The genus-one diagram of a lens space `L(p, q)` (`TauCeti.HeegaardRegionSystem.lensSpace`) has no
nonzero domain from a generator to itself avoiding the basepoint, and no domain between distinct
generators, so the Koszul comparison of
`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_apply` applies. Its twisted hat
differential vanishes, and after adding a basepoint in the basepoint region the twisted hat
differential sends the generator `(x, 0)` to `(1 + t) (x, 1)` and `(x, 1)` to `0`
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_apply`). Its cycles are
the chains vanishing on the generators `(x, 0)`, since `1 + t` is not a zero divisor
(`TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff`).

For `L(1, 1) = S³` this is the twice-pointed diagram of `S³`: the raw complex has two generators and
zero differential, while the twisted one is the injective multiplication by `1 + t` on the group
ring `𝔽₂[t, t⁻¹]` of the single new periodic domain. Its cokernel `𝔽₂[t, t⁻¹] ⧸ (1 + t)` is `𝔽₂`,
as for `S¹ × S²` in `TauCeti.HeegaardRegionSystem.circleTimesSphereQuotientEquiv`; that quotient is
not computed again here.

## Main results

* `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_apply` and
  `TauCeti.HeegaardRegionSystem.twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff`: the
  twisted hat complex of the diagram of a lens space with an added basepoint.

## References

* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830), §10
  (twisted coefficients for diagrams with several basepoints).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202), §8 (Floer homology with twisted
  coefficients).
-/

public section

open MonoidAlgebra

namespace TauCeti

namespace HeegaardRegionSystem

variable {p : ℕ} [NeZero p] {q : (ZMod p)ˣ} {s : ZMod p}
  (r : (lensSpace p q s).ReferenceDomains)

/-- **The twisted hat complex of a lens space with an added basepoint.** After adding a basepoint to
the genus-one diagram of `L(p, q)` in its basepoint region, the twisted hat differential sends a
chain `c` to the chain whose coefficient at `(y, 1)` is `(1 + t) c(y, 0)` and whose coefficient at
`(y, 0)` is zero: the direct sum over the generators of the Koszul complex of `1 + t`. For `p = 1`
this is the twice-pointed diagram of `S³`. -/
theorem twistedHatDifferential_addBasepoint_lensSpace_apply
    (c : ((lensSpace p q s).addBasepoint s).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative ((lensSpace p q s).addBasepoint s).periodicDomains))
    (y : (lensSpace p q s).Generator) (k : Fin 2) :
    ((lensSpace p q s).addBasepoint s).twistedHatDifferential
        (r.addBasepoint (Set.mem_range.mpr ⟨(), lensSpace_basepoint ()⟩))
        (addBasepointEuler 1 s) c ((lensSpace p q s).addBasepointGenerator s y k) =
      if k = 1 then c ((lensSpace p q s).addBasepointGenerator s y 0) *
        (1 + single (Multiplicative.ofAdd
          ((lensSpace p q s).addBasepointPeriodicDomainsEquiv s (0, 1))) 1)
      else 0 := by
  rw [twistedHatDifferential_addBasepoint_apply _ _ _
    (fun _ _ hE hz _ _ => eq_zero_of_isDomainBetween_lensSpace hE hz)]
  simp [twistedHatCoefficient_eq_zero_of_hatDomains_eq_empty (hatDomains_lensSpace _ _)]

/-- **The cycles of the twisted hat complex of a lens space with an added basepoint** are the
chains vanishing on the generators `(x, 0)`: the coefficient `1 + t` is not a zero divisor. -/
theorem twistedHatDifferential_addBasepoint_lensSpace_eq_zero_iff
    (c : ((lensSpace p q s).addBasepoint s).Generator →₀
      MonoidAlgebra (ZMod 2) (Multiplicative ((lensSpace p q s).addBasepoint s).periodicDomains)) :
    ((lensSpace p q s).addBasepoint s).twistedHatDifferential
        (r.addBasepoint (Set.mem_range.mpr ⟨(), lensSpace_basepoint ()⟩))
        (addBasepointEuler 1 s) c = 0 ↔
      ∀ x, c ((lensSpace p q s).addBasepointGenerator s x 0) = 0 := by
  constructor
  · intro h x
    have := twistedHatDifferential_addBasepoint_lensSpace_apply r c x 1
    simp only [h, Finsupp.zero_apply, ite_true] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (one_add_single_ne_zero (by simp) _)
  · intro h
    ext g
    obtain ⟨⟨y, k⟩, rfl⟩ := ((lensSpace p q s).addBasepointGeneratorEquiv s).surjective g
    rw [addBasepointGeneratorEquiv_apply, twistedHatDifferential_addBasepoint_lensSpace_apply,
      h, zero_mul, ite_self, Finsupp.zero_apply]

end HeegaardRegionSystem

end TauCeti
