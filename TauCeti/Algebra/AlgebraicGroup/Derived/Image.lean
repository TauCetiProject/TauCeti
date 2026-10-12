/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality
import TauCeti.Algebra.AlgebraicGroup.Derived.Smooth
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# Derived subgroups under dominant homomorphisms

A schematically dominant homomorphism of affine group schemes over a field restricts to a
schematically dominant homomorphism of their derived subgroups. In coordinates, an injective
Hopf algebra morphism `f : H ⟶ K` induces an injective morphism `derivedMap f` between the
quotient coordinate algebras. Equivalently, the inverse image of the derived defining ideal
of `K` is the derived defining ideal of `H`.

The ideal equality uses the universal property of the derived subgroup and injectivity of the
tensor square of `f`. It requires neither finite type nor smoothness, and preserves the full
scheme structure. For finite-type groups over any field, the induced morphism is surjective
on points valued in any algebraically closed extension field. Over an algebraically closed
base field, it is also faithfully flat when the target group is reduced. These results let
derived-subgroup constructions pass through quotient homomorphisms.

The construction uses the existing restriction map in
`TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality` and the smoothness theorem in
`TauCeti.Algebra.AlgebraicGroup.Derived.Smooth`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

open CategoryTheory TauCeti TauCeti.CommHopfAlgCat
open scoped TensorProduct

namespace BialgHom

universe u v w

section Field

variable {k : Type u} [Field k]
variable {H K : Type*} [CommRing H] [CommRing K] [HopfAlgebra k H] [HopfAlgebra k K]

/-- A schematically dominant homomorphism carries its source derived subgroup densely onto
its target derived subgroup. In coordinates, the inverse image of the derived defining
ideal along an injective Hopf algebra morphism is the derived defining ideal. -/
@[simp]
theorem comap_derivedDefiningIdeal_of_injective (f : H →ₐc[k] K)
    (hf : Function.Injective f) :
    (derivedDefiningIdeal (R := k) K).comap f = derivedDefiningIdeal (R := k) H := by
  apply le_antisymm
  · rw [le_derivedDefiningIdeal_iff, HopfIdeal.comap_toIdeal]
    intro x hx
    have hzero : HopfAlgebra.commutatorAlgHom (R := k) (H := K) (f x) = 0 :=
      RingHom.mem_ker.mp (derivedDefiningIdeal_toIdeal_le_ker (R := k) K hx)
    have hnatural := DFunLike.congr_fun (HopfAlgebra.map_comp_commutatorAlgHom f) x
    have hinj := Algebra.TensorProduct.map_injective_of_flat_flat
      f.toAlgHom f.toAlgHom hf hf
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    apply hinj
    simpa only [Bialgebra.TensorProduct.map_toAlgHom, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom, map_zero] using hnatural.trans hzero
  · intro x hx
    exact HopfIdeal.mem_comap.mpr
      (derivedDefiningIdeal_map_le f (HopfIdeal.mem_map_of_mem f hx))

end Field

end BialgHom

namespace TauCeti.CommHopfAlgCat

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}

/-- An injective coordinate morphism induces an injective morphism of derived coordinate
algebras. Thus a schematically dominant group homomorphism remains schematically dominant
on derived subgroups. -/
theorem derivedMap_injective (f : H ⟶ K) (hf : Function.Injective f.hom) :
    Function.Injective (derivedMap f).hom := by
  have hcomap := congrArg HopfIdeal.toIdeal
    (f.hom.comap_derivedDefiningIdeal_of_injective hf)
  rw [HopfIdeal.comap_toIdeal] at hcomap
  convert Ideal.quotientMap_injective'
    (f := (f.hom : H →+* K)) (H := hcomap.ge) hcomap.le using 1
  ext x
  obtain ⟨a, rfl⟩ := mkQuotient_surjective H (derivedDefiningIdeal H) x
  rw [mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk, derivedMap_mk,
    Ideal.quotientMap_mk]
  simp only [Ideal.Quotient.mkₐ_eq_mk, RingHom.coe_coe]

/-- A schematically dominant homomorphism between finite-type affine groups over a field is
surjective on the points of their derived subgroups valued in any algebraically closed
extension field. -/
theorem mapPointsFunctor_derivedMap_app_surjective
    [Algebra.FiniteType k H] [Algebra.FiniteType k K] (f : H ⟶ K)
    (hf : Function.Injective f.hom)
    (L : Type w) [Field L] [Algebra k L] [IsAlgClosed L] :
    Function.Surjective ((mapPointsFunctor (derivedMap f)).app (CommAlgCat.of k L)) :=
  mapPointsFunctor_app_surjective_of_injective L (derivedMap f) (derivedMap_injective f hf)

section AlgClosed

variable {H K : _root_.CommHopfAlgCat.{u} k}
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.FiniteType k K] [IsReduced H]

/-- Over an algebraically closed field, a schematically dominant homomorphism between
finite-type affine groups with reduced target restricts to a faithfully flat homomorphism
of derived subgroups. The source group need not be reduced. -/
theorem faithfullyFlat_derivedMap (f : H ⟶ K) (hf : Function.Injective f.hom) :
    (derivedMap f).hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let _ := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_quotient_derivedDefiningIdeal H)
  let _ : Algebra.IsGeometricallyReduced k (quotient H (derivedDefiningIdeal H)) :=
    isGeometricallyReduced_of_smooth k _
  exact (faithfullyFlat_iff_injective_of_isGeometricallyReduced (derivedMap f)).mpr
    (derivedMap_injective f hf)

end AlgClosed

end TauCeti.CommHopfAlgCat
