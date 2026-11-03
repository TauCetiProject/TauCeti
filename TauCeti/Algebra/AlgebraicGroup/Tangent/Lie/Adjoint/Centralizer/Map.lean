/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Maps between centralizers of Lie algebra elements

A homomorphism of affine groups carries the centralizer of `x` into the centralizer of its
image under the differential. If the differential is injective, the source centralizer is
exactly the scheme-theoretic inverse image of the target centralizer. Over a field,
injectivity survives tensoring with every coefficient algebra, including nonreduced ones.
Thus this is an equality of defining Hopf ideals, not only an equality on rational points.

The coordinate arrow `φ : H →ₐc[k] K` represents `Spec K → Spec H`. The induced map on
centralizer coordinate rings has the same contravariant direction. Its computation rule
records compatibility with the ambient group homomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3.

The construction uses the differential equivariance
`BialgHom.lTensor_dualCotangentMap_adjointAction`.
-/

public section

open TauCeti Derivation
open scoped TensorProduct

universe u

namespace BialgHom

variable {k H K : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing K] [HopfAlgebra k K]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [Module.Finite k (Bialgebra.CotangentSpace k K)]

/-- A group homomorphism carries the centralizer of `x` into the centralizer of `dφ(x)`.
In coordinate rings, the target centralizer ideal pulls back into the source ideal. -/
theorem map_centralizerHopfIdeal_le (φ : H →ₐc[k] K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal H (dualCotangentMap φ x)).map φ ≤ centralizerHopfIdeal K x := by
  apply (HopfIdeal.le_iff_forall_quotientPointsSubgroup_le
    (H := _root_.CommHopfAlgCat.of k K) _ _).mpr
  intro A g hg
  apply (CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff
    (_root_.CommHopfAlgCat.ofHom φ) _ A g).mpr
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply,
    _root_.CommHopfAlgCat.hom_ofHom]
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
  have hfix := (centralizerHopfIdeal_le_ker_iff_adjointAction x A g).mp hg
  apply (centralizerHopfIdeal_le_ker_iff_adjointAction _ A _).mpr
  rw [← LinearMap.lTensor_tmul, ← lTensor_dualCotangentMap_adjointAction, hfix]

/-- If the differential is injective, centralizing `dφ(x)` is equivalent to centralizing `x`
for every coefficient algebra. No smoothness or characteristic hypothesis is needed. -/
theorem centralizerHopfIdeal_le_ker_mapDomain_iff (φ : H →ₐc[k] K)
    (hφ : Function.Injective (dualCotangentMap φ))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (A : CommAlgCat.{u} k) (g : WithConv (K →ₐ[k] A)) :
    (centralizerHopfIdeal H (dualCotangentMap φ x)).toIdeal ≤
        RingHom.ker (mapDomain φ g).ofConv ↔
      (centralizerHopfIdeal K x).toIdeal ≤ RingHom.ker g.ofConv := by
  rw [centralizerHopfIdeal_le_ker_iff_adjointAction,
    centralizerHopfIdeal_le_ker_iff_adjointAction]
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ hφ
  rw [← hinj.eq_iff, lTensor_dualCotangentMap_adjointAction, LinearMap.lTensor_tmul]

/-- For an injective differential, the source centralizer is the scheme-theoretic inverse
image of the target centralizer. The equality includes the full defining ideals. -/
theorem map_centralizerHopfIdeal_eq_of_injective (φ : H →ₐc[k] K)
    (hφ : Function.Injective (dualCotangentMap φ))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal H (dualCotangentMap φ x)).map φ = centralizerHopfIdeal K x := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of k K)
  intro A
  ext g
  refine (CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff
    (_root_.CommHopfAlgCat.ofHom φ) _ A g).trans ?_
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply,
    _root_.CommHopfAlgCat.hom_ofHom, CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact φ.centralizerHopfIdeal_le_ker_mapDomain_iff hφ x A g

/-- The coordinate-ring map of the homomorphism `C_Spec K(x) → C_Spec H(dφ(x))`.
It exists even when the differential is not injective. -/
noncomputable def centralizerMap (φ : H →ₐc[k] K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (H ⧸ (centralizerHopfIdeal H (dualCotangentMap φ x)).toIdeal) →ₐc[k]
      (K ⧸ (centralizerHopfIdeal K x).toIdeal) :=
  Bialgebra.Quotient.liftBialgHom
    (centralizerHopfIdeal H (dualCotangentMap φ x)).toIdeal
    ((Bialgebra.Quotient.mkBialgHom (centralizerHopfIdeal K x).toIdeal).comp φ)
    (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((HopfIdeal.map_le_iff.mp (φ.map_centralizerHopfIdeal_le x)) ha))

/-- The centralizer coordinate map is induced by the ambient coordinate map. -/
@[simp]
theorem centralizerMap_mk (φ : H →ₐc[k] K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) (a : H) :
    φ.centralizerMap x (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (centralizerHopfIdeal K x).toIdeal (φ a) := by
  exact Bialgebra.Quotient.liftBialgHom_mk _ _ _ a

/-- The centralizer coordinate map commutes with the ambient quotient maps. -/
@[simp]
theorem centralizerMap_comp_mkBialgHom (φ : H →ₐc[k] K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (φ.centralizerMap x).comp
        (Bialgebra.Quotient.mkBialgHom (centralizerHopfIdeal H (dualCotangentMap φ x)).toIdeal) =
      (Bialgebra.Quotient.mkBialgHom (centralizerHopfIdeal K x).toIdeal).comp φ :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom _ _ _

end BialgHom
