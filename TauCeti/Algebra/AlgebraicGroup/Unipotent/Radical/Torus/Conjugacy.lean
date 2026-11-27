/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ComplementConjugacy
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Center
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Diagonalizable
import TauCeti.Algebra.Coalgebra.Comodule.Yoneda
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType

/-!
# Diagonalizable subgroups modulo the centre of the unipotent radical

Let `G` be a finite-type affine group over an algebraically closed field `k` of characteristic
zero, with unipotent radical `U = R_u(G)`, and let `N = Z(U)°_red` be the reduced connected centre
of `U`. Then `N` is a vector group on which `G` acts linearly by conjugation
(`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCenterConjLinearAut`). This file proves the
vector-group step of the conjugacy of maximal tori in a connected solvable group (Milne, the
proof of Theorem 16.33(d)): two diagonalizable closed subgroups `T` and `T'` of `G` with the same
image modulo `N`, in the sense that `N(A) ⊔ T(A) = N(A) ⊔ T'(A)` for every commutative
`k`-algebra `A`, are conjugate by a rational point of `N`
(`TauCeti.FiniteTypeCommHopfAlgCat.exists_eq_conjugate_of_reducedConnectedCenter_sup_eq`).

The statement is the general conjugacy theorem
`TauCeti.HopfIdeal.exists_eq_conjugate_kerOfSurjective_of_vectorGroup` for the vector group `N`.
Its hypotheses are supplied as follows.

* The diagonalizable subgroup `T` is the diagonalizable group `D(X)` of the group `X` of
  group-like elements of its coordinate algebra
  (`TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.exists_kerOfSurjective_eq`).
* The space `P` of primitive elements of the coordinate algebra of `N` is finite-dimensional,
  since `N` is the vector group of `P` and of finite type
  (`TauCeti.SymmetricAlgebra.module_finite_of_finiteType`). The points `N(A)`, the linear maps
  `P →ₗ[k] A`, are then the scalar extensions `A ⊗[k] P*` of the dual space `P*`
  (`TauCeti.Module.Dual.baseChangeLinearMapEquiv`).
* Conjugation by `T` acts on these points by `A`-linear automorphisms, naturally in `A`; by the
  Yoneda lemma (`TauCeti.Comodule.ofNaturality`) this is the action of a comodule structure on
  `P*` over the coordinate algebra `k[X]` of `T`, so `T` acts on `N` through a representation.
* The diagonalizable subgroup `T'` meets the smooth unipotent subgroup `N` trivially
  (`TauCeti.FiniteTypeCommHopfAlgCat.sup_eq_augmentation_of_groupLikeSpanned_of_smoothUnipotent`).

Coordinate rings reverse arrows: the subgroups `N`, `T` and `T'` are cut out by Hopf ideals of
the coordinate algebra of `G`, and the conjugate of `T` by a rational point `y` is cut out by
`TauCeti.HopfIdeal.conjugate`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.exists_eq_conjugate_of_reducedConnectedCenter_sup_eq`: two
  diagonalizable subgroups with the same image modulo the reduced connected centre of the
  unipotent radical are conjugate by a rational point of that centre.

## References

* J. S. Milne, *Algebraic Groups* (2017), the proof of Theorem 16.33(d), p. 336.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The Hopf ideal of the reduced connected centre of the unipotent radical. -/
private abbrev centerIdeal : HopfIdeal k G :=
  (unipotentRadicalDefiningIdeal G).reducedConnectedCenter

/-- The primitive elements of the coordinate algebra of the reduced connected centre of the
unipotent radical, the additive characters of this vector group. -/
private abbrev centerPrimitive : Submodule k (G ⧸ (centerIdeal G).toIdeal) :=
  Coalgebra.skewPrimitive k (1 : G ⧸ (centerIdeal G).toIdeal) 1

/-- The space of primitive elements of the centre is finite-dimensional. -/
private instance : Module.Finite k (centerPrimitive G) := by
  have : Algebra.FiniteType k (SymmetricAlgebra k (centerPrimitive G)) :=
    Algebra.FiniteType.equiv inferInstance
      (unipotentRadicalCenterVectorGroupEquiv G).toAlgEquiv.symm
  exact SymmetricAlgebra.module_finite_of_finiteType k _

/-- A point of the centre, read as the linear map on the primitive elements that it induces. -/
private def restrictEquiv (A : Type u) [CommRing A] [Algebra k A] :
    WithConv (G ⧸ (centerIdeal G).toIdeal →ₐ[k] A) ≃*
      Multiplicative (centerPrimitive G →ₗ[k] A) :=
  ((unipotentRadicalCenterVectorGroupEquiv G).mapDomainMulEquiv (A := A)).trans
    AdditiveGroup.pointsMulEquiv

private theorem toAdd_restrictEquiv (A : Type u) [CommRing A] [Algebra k A]
    (n : WithConv (G ⧸ (centerIdeal G).toIdeal →ₐ[k] A)) :
    Multiplicative.toAdd (restrictEquiv G A n) =
      n.ofConv.toLinearMap ∘ₗ (centerPrimitive G).subtype := by
  ext p
  simp only [restrictEquiv, MulEquiv.trans_apply, AdditiveGroup.toAdd_pointsMulEquiv_apply,
    BialgEquiv.mapDomainMulEquiv_apply, BialgHom.mapDomain_apply_apply, LinearMap.coe_comp,
    Function.comp_apply, AlgHom.toLinearMap_apply, Submodule.coe_subtype]
  exact congrArg n.ofConv (unipotentRadicalCenterVectorGroupEquiv_ι G p)

/-- The point of the centre whose linear map on the primitive elements is `e_A x`. -/
private def centerPoint (A : Type u) [CommRing A] [Algebra k A]
    (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    WithConv (G ⧸ (centerIdeal G).toIdeal →ₐ[k] A) :=
  (restrictEquiv G A).symm (.ofAdd (Module.Dual.baseChangeLinearMapEquiv x))

private theorem restrictEquiv_centerPoint (A : Type u) [CommRing A] [Algebra k A]
    (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    (centerPoint G A x).ofConv.toLinearMap ∘ₗ (centerPrimitive G).subtype =
      Module.Dual.baseChangeLinearMapEquiv x := by
  rw [← toAdd_restrictEquiv, centerPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- A point of the centre is determined by its linear map on the primitive elements. -/
private theorem eq_centerPoint_iff (A : Type u) [CommRing A] [Algebra k A]
    (x : A ⊗[k] Module.Dual k (centerPrimitive G))
    (n : WithConv (G ⧸ (centerIdeal G).toIdeal →ₐ[k] A)) :
    n = centerPoint G A x ↔
      n.ofConv.toLinearMap ∘ₗ (centerPrimitive G).subtype =
        Module.Dual.baseChangeLinearMapEquiv x := by
  rw [centerPoint, MulEquiv.eq_symm_apply, ← toAdd_restrictEquiv,
    ← Multiplicative.toAdd.apply_eq_iff_eq, toAdd_ofAdd]

/-- The identification of the scalar extensions of the dual of the primitive elements with the
points of the centre inside the points of `G`. -/
private def centerPointsEquiv (A : Type u) [CommRing A] [Algebra k A] :
    Multiplicative (A ⊗[k] Module.Dual k (centerPrimitive G)) ≃*
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G) (centerIdeal G)
        (CommAlgCat.of k A) :=
  ((Module.Dual.baseChangeLinearMapEquiv).toAddEquiv.toMultiplicative.trans
      (restrictEquiv G A).symm).trans
    (MonoidHom.ofInjective (CommHopfAlgCat.quotientPointsHom_injective
      (_root_.CommHopfAlgCat.of k G) (centerIdeal G) (CommAlgCat.of k A)))

private theorem coe_centerPointsEquiv (A : Type u) [CommRing A] [Algebra k A]
    (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    (centerPointsEquiv G A (.ofAdd x) : WithConv (G →ₐ[k] A)) =
      BialgHom.mapDomain (Bialgebra.Quotient.mkBialgHom (centerIdeal G).toIdeal)
        (centerPoint G A x) :=
  WithConv.ofConv_injective (AlgHom.ext fun h ↦ by
    -- By definition, the ambient point is the image of the quotient point `centerPoint G A x`.
    have hx : (centerPointsEquiv G A (.ofAdd x) : WithConv (G →ₐ[k] A)) =
        CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of k G) (centerIdeal G)
          (CommAlgCat.of k A) (centerPoint G A x) := rfl
    rw [hx, CommHopfAlgCat.quotientPointsHom_apply_apply, BialgHom.mapDomain_apply_apply,
      Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk])

/-- The points of the centre are natural in the value algebra. -/
private theorem mapValue_centerPointsEquiv (A B : Type u) [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    AlgHom.mapValue φ (centerPointsEquiv G A (.ofAdd x) : WithConv (G →ₐ[k] A)) =
      centerPointsEquiv G B (.ofAdd (LinearMap.rTensor _ φ.toLinearMap x)) := by
  rw [coe_centerPointsEquiv, coe_centerPointsEquiv, ← BialgHom.mapDomain_mapValue_apply]
  congr 1
  rw [eq_centerPoint_iff, AlgHom.baseChangeLinearMapEquiv_rTensor, ← restrictEquiv_centerPoint,
    AlgHom.mapValue_apply,
    ofConv_toConv, AlgHom.comp_toLinearMap, LinearMap.comp_assoc]

section Action

variable {X : Type u} [CommGroup X] (π : G →ₐc[k] MonoidAlgebra k X)

/-- The action of the points of the diagonalizable group `D(X)`, through `π`, on the scalar
extensions of the dual of the primitive elements of the centre, by conjugation. -/
private def centerAction (A : Type u) [CommRing A] [Algebra k A] :
    WithConv (MonoidAlgebra k X →ₐ[k] A) →*
      Module.End A (A ⊗[k] Module.Dual k (centerPrimitive G)) where
  toFun t := (Module.Dual.baseChangeLinearMapEquiv).symm.toLinearMap ∘ₗ
    (unipotentRadicalCenterConjLinearAut G A (BialgHom.mapDomain π t)).toLinearMap ∘ₗ
      (Module.Dual.baseChangeLinearMapEquiv).toLinearMap
  map_one' := LinearMap.ext fun x ↦ by
    simp only [map_one, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      one_apply_eq_self, LinearEquiv.symm_apply_apply]
  map_mul' s t := LinearMap.ext fun x ↦ by
    simp only [map_mul, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      mul_apply_eq_comp, LinearEquiv.apply_symm_apply]

private theorem baseChangeLinearMapEquiv_centerAction (A : Type u) [CommRing A] [Algebra k A]
    (t : WithConv (MonoidAlgebra k X →ₐ[k] A)) (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    Module.Dual.baseChangeLinearMapEquiv (centerAction G π A t x) =
      unipotentRadicalCenterConjLinearAut G A (BialgHom.mapDomain π t)
        (Module.Dual.baseChangeLinearMapEquiv x) := by
  simp only [centerAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The conjugation action on the centre is natural in the value algebra. -/
private theorem rTensor_centerAction (A B : Type u) [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (φ : A →ₐ[k] B) (t : WithConv (MonoidAlgebra k X →ₐ[k] A))
    (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    LinearMap.rTensor _ φ.toLinearMap (centerAction G π A t x) =
      centerAction G π B (AlgHom.mapValue φ t) (LinearMap.rTensor _ φ.toLinearMap x) := by
  refine (Module.Dual.baseChangeLinearMapEquiv).injective ?_
  rw [baseChangeLinearMapEquiv_centerAction, AlgHom.baseChangeLinearMapEquiv_rTensor,
    AlgHom.baseChangeLinearMapEquiv_rTensor, baseChangeLinearMapEquiv_centerAction,
    unipotentRadicalCenterConjLinearAut_mapValue, BialgHom.mapDomain_mapValue_apply]

/-- Conjugation by the points of `D(X)` acts on the points of the centre through the comodule
structure defined by the conjugation action. -/
private theorem centerPointsEquiv_endOfPoint (A : Type u) [CommRing A] [Algebra k A]
    (t : WithConv (MonoidAlgebra k X →ₐ[k] A)) (x : A ⊗[k] Module.Dual k (centerPrimitive G)) :
    letI := Comodule.ofNaturality (rTensor_centerAction G π)
    (centerPointsEquiv G A (.ofAdd (Comodule.endOfPoint _ t.ofConv x)) : WithConv (G →ₐ[k] A)) =
      BialgHom.mapDomain π t * centerPointsEquiv G A (.ofAdd x) *
        (BialgHom.mapDomain π t)⁻¹ := by
  have := HopfAlgebra.isReduced_of_charZero k G
  have hN := isNormal_reducedConnectedCenter_unipotentRadicalDefiningIdeal G
  rw [Comodule.endOfPoint_ofNaturality, coe_centerPointsEquiv, coe_centerPointsEquiv,
    ← hN.mapDomain_conjPoints]
  congr 1
  symm
  rw [eq_centerPoint_iff, baseChangeLinearMapEquiv_centerAction, ← restrictEquiv_centerPoint,
    unipotentRadicalCenterConjLinearAut_apply G hN]

end Action

/-- **Diagonalizable subgroups with the same image modulo the centre of the unipotent radical
are conjugate by a rational point of the centre.** Let `G` be a finite-type affine group over an
algebraically closed field of characteristic zero, and let `N` be the reduced connected centre of
its unipotent radical, a vector group on which `G` acts linearly by conjugation. If the Hopf
ideals `J` and `J'` cut out diagonalizable closed subgroups `T` and `T'` with the same image
modulo `N`, that is `N(A) ⊔ T(A) = N(A) ⊔ T'(A)` for every commutative `k`-algebra `A`
(`himage`), then `T'` is the conjugate of `T` by a rational point `y` of `N`.

This is the vector-group step in the conjugacy of maximal tori of a connected solvable group
(Milne, the proof of Theorem 16.33(d)). -/
theorem exists_eq_conjugate_of_reducedConnectedCenter_sup_eq {J J' : HopfIdeal k G}
    (hJ : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G J))
    (hJ' : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G J'))
    (himage : ∀ (A : Type u) [CommRing A] [Algebra k A],
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G)
          (unipotentRadicalDefiningIdeal G).reducedConnectedCenter (CommAlgCat.of k A) ⊔
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G) J
          (CommAlgCat.of k A) =
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G)
          (unipotentRadicalDefiningIdeal G).reducedConnectedCenter (CommAlgCat.of k A) ⊔
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G) J'
          (CommAlgCat.of k A)) :
    ∃ y ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k G)
        (unipotentRadicalDefiningIdeal G).reducedConnectedCenter (CommAlgCat.of k k),
      J' = J.conjugate y := by
  obtain ⟨X, _, π, hπ, rfl⟩ := hJ.exists_kerOfSurjective_eq
  let _ := Comodule.ofNaturality (rTensor_centerAction G π)
  have hN : smoothUnipotentCommHopfAlgProperty k (quotient G (centerIdeal G)) :=
    HopfIdeal.smoothUnipotent_reducedConnectedCenter (geometricallyUnipotent_unipotentRadical G)
  exact HopfIdeal.exists_eq_conjugate_kerOfSurjective_of_vectorGroup (centerIdeal G) J' π hπ
    (centerPointsEquiv G) (fun A B _ _ _ _ φ x ↦ mapValue_centerPointsEquiv G A B φ x)
    (fun A _ _ t x ↦ centerPointsEquiv_endOfPoint G π A t x)
    ((sup_comm _ _).trans (sup_eq_augmentation_of_groupLikeSpanned_of_smoothUnipotent G hJ' hN))
    himage

end

end TauCeti.FiniteTypeCommHopfAlgCat
