/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Augmentation

/-!
# Kernels of homomorphisms of diagonalizable groups

For a homomorphism `p : M →* N` of commutative groups, the kernel of
`D(N) → D(M)` has coordinate Hopf algebra `R[N / range p]`. The comparison respects
the quotient coordinate maps, so it identifies the kernel as a closed subgroup, rather
than merely identifying its abstract coordinate algebra.

The construction works over any commutative ring and does not require finite generation
of either character group. Over a nonzero base the kernel is finite exactly when the
character cokernel is finite. This gives the kernel calculation for isogenies of
diagonalizable groups, including inseparable isogenies.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b).

The ideal calculation uses `TauCeti.MonoidAlgebra.map_ker_augmentation_eq_ker_mapDomainRingHom`.
-/

public section

open CategoryTheory

namespace TauCeti.DiagonalizableGroup

universe u v

variable (R : Type u) [CommRing R]
variable {M N : Type v} [CommGroup M] [CommGroup N] (p : M →* N)

/-- The ideal defining the kernel of `D(N) → D(M)` is the kernel of the coordinate
map from `R[N]` to the group algebra of the character cokernel. -/
theorem kernelHopfIdeal_mapDomainBialgHom_toIdeal :
    (CommHopfAlgCat.kernelHopfIdeal
      (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p))).toIdeal =
        RingHom.ker (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' p.range)) := by
  rw [CommHopfAlgCat.kernelHopfIdeal_toIdeal, HopfIdeal.augmentation_toIdeal]
  -- The categorical carrier and the coercion of `counitAlgHom` hide the underlying ring maps.
  change Ideal.map (MonoidAlgebra.mapDomainRingHom R p)
    (RingHom.ker (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom) = _
  simp only [AlgHom.toRingHom_eq_coe, MonoidAlgebra.counitAlgHom_toRingHom]
  apply MonoidAlgebra.map_ker_augmentation_eq_ker_mapDomainRingHom
  exact congrArg Subgroup.toSubmonoid (QuotientGroup.ker_mk' p.range).symm

/-- The Hopf ideal defining a diagonalizable-group kernel agrees with the Hopf kernel
of the surjective map onto the character-cokernel group algebra. -/
private theorem kernelHopfIdeal_mapDomainBialgHom :
    CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)) =
      HopfIdeal.kerOfSurjective
        (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' p.range))
        (by exact MonoidAlgebra.mapDomain_surjective (QuotientGroup.mk'_surjective p.range)) := by
  ext x
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal,
    kernelHopfIdeal_mapDomainBialgHom_toIdeal]
  exact (HopfIdeal.mem_kerOfSurjective
    (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' p.range))
    (by exact MonoidAlgebra.mapDomain_surjective (QuotientGroup.mk'_surjective p.range))).symm

/-- The coordinate Hopf algebra of the kernel of `D(N) → D(M)` is the group algebra
of the cokernel of `M → N`. -/
noncomputable def kernelCoordinateIso :
    CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p))) ≅
      CommHopfAlgCat.of R (MonoidAlgebra R (N ⧸ p.range)) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient _) (kernelHopfIdeal_mapDomainBialgHom R p)) ≪≫
    CommHopfAlgCat.quotientKerOfSurjectiveIso
      (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' p.range)))
      (by exact MonoidAlgebra.mapDomain_surjective (QuotientGroup.mk'_surjective p.range))

/-- The kernel identification commutes with the maps from the ambient coordinate algebra. -/
@[simp]
theorem mkQuotient_comp_kernelCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of R (MonoidAlgebra R N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p))) ≫
        (kernelCoordinateIso R p).hom =
      CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' p.range)) := by
  rw [kernelCoordinateIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_eqToHom (kernelHopfIdeal_mapDomainBialgHom R p).symm]
  exact CommHopfAlgCat.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- Over a nonzero base, the kernel of a diagonalizable-group morphism is finite if and
only if the cokernel of its character homomorphism is finite. -/
theorem moduleFinite_kernelCoordinate_iff [Nontrivial R] :
    Module.Finite R
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)))) ↔
      Finite (N ⧸ p.range) := by
  let e := (CommHopfAlgCat.ofIso (kernelCoordinateIso R p)).toAlgEquiv.toLinearEquiv
  rw [e.toLinearMap.finite_iff_of_bijective e.bijective]
  let c := MonoidAlgebra.coeffLinearEquiv R (S := R) (M := N ⧸ p.range)
  rw [c.toLinearMap.finite_iff_of_bijective c.bijective]
  simp [Module.finite_finsupp_self_iff, not_subsingleton R]

/-- The finrank of the kernel coordinate algebra equals the natural cardinality of the
character cokernel. In particular, this computes the rank of every finite kernel even when
its order is divisible by the characteristic. -/
theorem finrank_kernelCoordinate [Nontrivial R] :
    Module.finrank R
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)))) =
      Nat.card (N ⧸ p.range) := by
  let e := (CommHopfAlgCat.ofIso (kernelCoordinateIso R p)).toAlgEquiv.toLinearEquiv
  rw [e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis (N ⧸ p.range) R)

end TauCeti.DiagonalizableGroup
