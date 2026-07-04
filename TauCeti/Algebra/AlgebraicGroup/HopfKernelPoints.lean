/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdealPoints
public import TauCeti.Algebra.HopfAlgebra.Kernel

/-!
# Points of kernel quotients

For a surjective morphism of commutative Hopf algebras `f : H →ₐc[R] K`, the quotient by
the Hopf-ideal kernel is bialgebra-equivalent to `K`. This file transports that first
isomorphism theorem to functors of points: for every commutative `R`-algebra `A`, the
convolution group of `A`-points of `H ⧸ ker f` is multiplicatively equivalent to the
convolution group of `A`-points of `K`.

The characteristic compatibility says that including an `A`-point of `H ⧸ ker f` back into
the ambient `H`-points is the same as first identifying it with a `K`-point and then
pre-composing along `f`. This is the point-level kernel case of the closed-subgroup
dictionary.

## Main declarations

* `TauCeti.HopfIdeal.kerQuotientPointsMulEquiv`: the equivalence between points of the
  kernel quotient and points of the codomain.
* `TauCeti.HopfIdeal.quotientPointsHom_kerQuotientPointsMulEquiv_symm`: compatibility of
  the inverse equivalence with the quotient-points inclusion.
* `TauCeti.HopfIdeal.quotientPointsHom_ker_eq_mapDomain`: the corresponding compatibility
  for an arbitrary point of the kernel quotient.

## References

This is a Layer 3 prerequisite for `TauCetiRoadmap/ReductiveGroups/README.md`, "Hopf ideals
↔ closed subgroup schemes", specifically the kernels part of the Hopf-ideal dictionary. It
uses the first isomorphism theorem `TauCeti.HopfIdeal.kerLiftBialgEquiv` and the
contravariant points functoriality `TauCeti.AlgHom.mapDomainMulEquiv`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w x

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : Type v} {K : Type w}

section RingSource

variable [Ring H] [Ring K] [HopfAlgebra R H] [HopfAlgebra R K]

/-- The points of the quotient by the Hopf-ideal kernel of a surjective Hopf algebra
morphism are the points of its codomain.

Contravariantly, this is induced by the bialgebra equivalence
`H ⧸ ker f ≃ₐc[R] K` from the Hopf-algebra first isomorphism theorem. -/
noncomputable def kerQuotientPointsMulEquiv (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R) :
    HopfAlgebra.points (R := R) (H := H ⧸ (ker f hf).toIdeal) A ≃*
      HopfAlgebra.points (R := R) (H := K) A :=
  (AlgHom.mapDomainMulEquiv (A := A) (kerLiftBialgEquiv f hf)).symm

end RingSource

section CommSource

variable [CommRing H] [Ring K] [HopfAlgebra R H] [HopfAlgebra R K]

/-- Including the quotient point attached to a `K`-point back into ambient `H`-points is
pre-composition along the original surjective Hopf algebra morphism. -/
@[simp]
theorem quotientPointsHom_kerQuotientPointsMulEquiv_symm (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    (@ConcreteCategory.hom GrpCat GrpCat.instCategory (fun X Y => X →* Y) GrpCat.carrier
        (fun _ _ => MonoidHom.instFunLike) GrpCat.instConcreteCategoryMonoidHomCarrier
        (@HopfAlgebra.points R _ (H ⧸ RingHom.ker (f : H →ₐ[R] K))
          (Ideal.Quotient.semiring (ker f hf).toIdeal)
          (HopfAlgebra.Quotient.instQuotientIdeal (ker f hf).toIdeal) A)
        (HopfAlgebra.points (R := R) (H := H) A)
        (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A)
      )
        ((@MulEquiv.symm
          (@HopfAlgebra.points R _ (H ⧸ RingHom.ker (f : H →ₐ[R] K))
            (Ideal.Quotient.semiring (ker f hf).toIdeal)
            (HopfAlgebra.Quotient.instQuotientIdeal (ker f hf).toIdeal) A)
          (HopfAlgebra.points (R := R) (H := K) A) _ _
          (kerQuotientPointsMulEquiv f hf A)) g) =
      AlgHom.mapDomain f g := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  change ((CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A
        ((kerQuotientPointsMulEquiv f hf A).symm g)).ofConv) h =
    ((AlgHom.mapDomain f) g).ofConv h
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply]
  rw [kerQuotientPointsMulEquiv, MulEquiv.symm_symm, AlgHom.mapDomainMulEquiv_apply,
    AlgHom.mapDomain_apply_apply, BialgEquiv.coe_toBialgHom,
    kerLiftBialgEquiv_apply, kerLiftBialgHom_mk, AlgHom.mapDomain_apply_apply]

/-- For an arbitrary point of `H ⧸ ker f`, the quotient-points inclusion agrees with first
identifying it as a `K`-point and then pre-composing along `f`. -/
@[simp]
theorem quotientPointsHom_ker_eq_mapDomain (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := H ⧸ (ker f hf).toIdeal) A) :
    (@ConcreteCategory.hom GrpCat GrpCat.instCategory (fun X Y => X →* Y) GrpCat.carrier
        (fun _ _ => MonoidHom.instFunLike) GrpCat.instConcreteCategoryMonoidHomCarrier
        (@HopfAlgebra.points R _ (H ⧸ RingHom.ker (f : H →ₐ[R] K))
          (Ideal.Quotient.semiring (ker f hf).toIdeal)
          (HopfAlgebra.Quotient.instQuotientIdeal (ker f hf).toIdeal) A)
        (HopfAlgebra.points (R := R) (H := H) A)
        (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H) (ker f hf) A)) g =
      AlgHom.mapDomain f (kerQuotientPointsMulEquiv f hf A g) := by
  convert quotientPointsHom_kerQuotientPointsMulEquiv_symm f hf A
    (kerQuotientPointsMulEquiv f hf A g)
  exact (MulEquiv.symm_apply_apply (kerQuotientPointsMulEquiv f hf A) g).symm

/-- The image of a codomain point under the kernel-quotient inclusion belongs to the
subgroup of ambient points cut out by the kernel Hopf ideal. -/
theorem mapDomain_mem_quotientPointsSubgroup_ker (f : H →ₐc[R] K)
    (hf : Function.Surjective f) (A : CommAlgCat.{x} R)
    (g : HopfAlgebra.points (R := R) (H := K) A) :
    AlgHom.mapDomain f g ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) (ker f hf) A := by
  rw [← quotientPointsHom_kerQuotientPointsMulEquiv_symm f hf A g]
  exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
    (_root_.CommHopfAlgCat.of R H) (ker f hf) A
    ((kerQuotientPointsMulEquiv f hf A).symm g)

end CommSource

end HopfIdeal

end TauCeti
