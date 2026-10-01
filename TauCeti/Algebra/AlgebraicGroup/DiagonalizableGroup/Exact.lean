/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel
import TauCeti.Algebra.MonoidAlgebra.Exactness
import TauCeti.Algebra.MonoidAlgebra.FaithfullyFlat
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Exactness of the diagonalizable-group functor

A short exact sequence `1 → L → M → N → 1` of commutative groups induces, contravariantly, a
short exact sequence of diagonalizable groups

```text
1 → D(N) → D(M) → D(L) → 1,
```

whose coordinate maps are the group-algebra maps `R[L] → R[M] → R[N]`. Over a nonzero
commutative base ring the converse holds as well, so `D` reflects exactness
(`TauCeti.DiagonalizableGroup.isShortExact_mapDomainBialgHom_iff`). Neither group needs to be
finitely generated, and there is no hypothesis on the characteristic: for instance, for `n ≥ 1`
the sequence `1 → μₙ → 𝔾ₘ → 𝔾ₘ → 1` given by the `n`-th power map is the image of
`0 → ℤ → ℤ → ℤ/n → 0`, so it is short exact also when `n` is divisible by the characteristic.

The inputs are the faithful flatness of `R[L] → R[M]` for injective `L → M`
(`TauCeti.MonoidAlgebra.faithfullyFlat_mapDomainRingHom_iff`) and the ideal-theoretic exactness of
group algebras (`TauCeti.MonoidAlgebra.map_ker_augmentation_eq_ker_mapDomainRingHom`).

## Main declarations

* `TauCeti.DiagonalizableGroup.isShortExact_mapDomainBialgHom`: exact character sequences give
  short exact sequences of diagonalizable groups.
* `TauCeti.DiagonalizableGroup.isShortExact_mapDomainBialgHom_iff`: the converse over a nonzero
  base ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.
-/

public section

namespace TauCeti.DiagonalizableGroup

universe u v

variable (R : Type u) [CommRing R]
variable {L M N : Type v} [CommGroup L] [CommGroup M] [CommGroup N] (p : L →* M) (q : M →* N)

/-- A short exact sequence `1 → L → M → N → 1` of commutative groups induces a short exact
sequence `1 → D(N) → D(M) → D(L) → 1` of diagonalizable groups over every commutative ring. -/
theorem isShortExact_mapDomainBialgHom (hp : Function.Injective p)
    (hq : Function.Surjective q) (hpq : p.range = q.ker) :
    CommHopfAlgCat.IsShortExact (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p))
      (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R q)) where
  faithfullyFlat := MonoidAlgebra.faithfullyFlat_mapDomainRingHom_of_injective R p hp
  surjective := MonoidAlgebra.mapDomain_surjective hq
  ker_eq := by
    rw [kernelHopfIdeal_mapDomainBialgHom_toIdeal]
    exact (MonoidAlgebra.map_ker_augmentation_eq_ker_mapDomainRingHom R p q
      (congrArg Subgroup.toSubmonoid hpq)).symm.trans
        (MonoidAlgebra.map_ker_augmentation_eq_ker_mapDomainRingHom R p _
          (congrArg Subgroup.toSubmonoid (QuotientGroup.ker_mk' p.range).symm))

/-- Over a nonzero commutative ring, the diagonalizable groups `D(N) → D(M) → D(L)` form a short
exact sequence exactly when `1 → L → M → N → 1` is a short exact sequence of commutative
groups. -/
theorem isShortExact_mapDomainBialgHom_iff [Nontrivial R] :
    CommHopfAlgCat.IsShortExact (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p))
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R q)) ↔
      Function.Injective p ∧ Function.Surjective q ∧ p.range = q.ker := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun ⟨hp, hq, hpq⟩ ↦ isShortExact_mapDomainBialgHom R p q hp hq hpq⟩
  · exact (MonoidAlgebra.faithfullyFlat_mapDomainRingHom_iff R p).mp h.faithfullyFlat
  · intro n
    obtain ⟨x, hx⟩ := h.surjective (MonoidAlgebra.single n 1)
    refine Finsupp.mem_range_of_mapDomain_ne_zero (x := x.coeff) (b := n) ?_
    have hc := congrArg (fun y : MonoidAlgebra R N ↦ y.coeff n) hx
    simp only [CategoryTheory.ConcreteCategory.hom_ofHom,
      MonoidAlgebra.coeff_mapDomainBialgHom_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at hc
    exact hc ▸ one_ne_zero
  · have hker : RingHom.ker (MonoidAlgebra.mapDomainRingHom R q) =
        RingHom.ker (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' p.range)) :=
      h.ker_eq.trans (kernelHopfIdeal_mapDomainBialgHom_toIdeal R p)
    ext m
    rw [MonoidHom.mem_ker, ← MonoidAlgebra.single_sub_one_mem_ker_mapDomainRingHom_iff R, hker,
      MonoidAlgebra.single_sub_one_mem_ker_mapDomainRingHom_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]

end TauCeti.DiagonalizableGroup
