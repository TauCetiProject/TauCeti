/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.RingTheory.Smooth.Retract

/-!
# The coordinate algebra of the dynamic Levi decomposition

Multiplication identifies the underlying affine scheme of a dynamic parabolic with the
product of its dynamic unipotent subgroup and its Levi subgroup. Contravariantly this gives
an algebra equivalence `O(P) ≃ O(U) ⊗ O(Z)`. It holds over any commutative base ring,
without smoothness, finite type or reductivity hypotheses, and includes nonreduced groups.

This is an equivalence of algebras: the direct-product Hopf structure on the tensor product
does not in general give the parabolic group law. On points the forward coordinate map
induces multiplication in the order unipotent, then Levi. The characteristic formula below
specifies that map without unfolding its construction.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory WithConv TauCeti TauCeti.Cocharacter
open scoped TensorProduct

namespace BialgHom

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The coordinate Hopf algebra of the represented dynamic parabolic. -/
private noncomputable abbrev P (l : H →ₐc[R] LaurentPolynomial R) :=
  CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (parabolicDefiningHopfIdeal l)

/-- The coordinate Hopf algebra of the represented dynamic unipotent subgroup. -/
private noncomputable abbrev U (l : H →ₐc[R] LaurentPolynomial R) :=
  CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (l.unipotentDefiningHopfIdeal)

/-- The coordinate Hopf algebra of the represented dynamic Levi subgroup. -/
private noncomputable abbrev Z (l : H →ₐc[R] LaurentPolynomial R) :=
  CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l)

/-- The represented point bijection induced by the dynamic Levi factorization. -/
private noncomputable def decompositionPointsEquiv (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{v} R) :
    WithConv (((U l) ⊗[R] (Z l)) →ₐ[R] A) ≃ WithConv ((P l) →ₐ[R] A) :=
  (AffineGroup.Product.pointsMulEquiv (R := R) (H₁ := U l) (H₂ := Z l)).toEquiv |>.trans
    (((l.unipotentPointsIso.app A).groupIsoToMulEquiv.toEquiv.prodCongr
      ((leviPointsIso l).app A).groupIsoToMulEquiv.toEquiv).trans
      (SemidirectProduct.equivProd.symm.trans
        ((leviDecompositionMulEquiv A l).toEquiv.trans
          ((parabolicPointsIso l).app A).groupIsoToMulEquiv.symm.toEquiv)))

private theorem decompositionPointsEquiv_ambient (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{v} R) (f : WithConv (((U l) ⊗[R] (Z l)) →ₐ[R] A)) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) A (decompositionPointsEquiv l A f) =
      CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
          l.unipotentDefiningHopfIdeal A
          (AffineGroup.Product.pointsMulEquiv f).1 *
        CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l) A
          (AffineGroup.Product.pointsMulEquiv f).2 := by
  -- Expand the composite equivalence to expose the represented subgroup points; the
  -- representing isomorphisms themselves remain opaque.
  change CommHopfAlgCat.quotientPointsHom _ _ A
    ((parabolicPointsIso l).inv.app A
      (leviDecompositionMulEquiv A l
        ⟨l.unipotentPointsIso.hom.app A (AffineGroup.Product.pointsMulEquiv f).1,
          (leviPointsIso l).hom.app A (AffineGroup.Product.pointsMulEquiv f).2⟩)) = _
  rw [quotientPointsHom_parabolicPointsIso_inv_app_apply]
  simp only [leviDecompositionMulEquiv_apply, Subgroup.coe_mul]
  exact congrArg₂ (· * ·)
    ((coe_unipotentToParabolic_apply A l _).trans
      (l.coe_unipotentPointsIso_hom_app_apply A _))
    ((coe_leviToParabolic_apply A l _).trans
      (coe_leviPointsIso_hom_app_apply l A _))

private theorem decompositionPointsEquiv_mapValue (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (f : WithConv (((U l) ⊗[R] (Z l)) →ₐ[R] A)) :
    decompositionPointsEquiv l B (AlgHom.mapValue φ.hom f) =
      AlgHom.mapValue φ.hom (decompositionPointsEquiv l A f) := by
  have hU : l.unipotentPointsIso.hom.app B
      (AlgHom.mapValue φ.hom (AffineGroup.Product.pointsMulEquiv f).1) =
      mapUnipotent l φ
        (l.unipotentPointsIso.hom.app A (AffineGroup.Product.pointsMulEquiv f).1) := by
    have hn := l.unipotentPointsIso.hom.naturality φ
    rw [unipotentFunctor_map, HopfAlgebra.pointsFunctor_map] at hn
    exact congrArg (fun k ↦ k.hom (AffineGroup.Product.pointsMulEquiv f).1) hn
  have hZ : (leviPointsIso l).hom.app B
      (AlgHom.mapValue φ.hom (AffineGroup.Product.pointsMulEquiv f).2) =
      mapLevi l φ ((leviPointsIso l).hom.app A (AffineGroup.Product.pointsMulEquiv f).2) := by
    have hn := (leviPointsIso l).hom.naturality φ
    rw [leviFunctor_map, HopfAlgebra.pointsFunctor_map] at hn
    exact congrArg (fun k ↦ k.hom (AffineGroup.Product.pointsMulEquiv f).2) hn
  have hP (g : parabolic A l) : (parabolicPointsIso l).inv.app B (mapParabolic l φ g) =
      AlgHom.mapValue φ.hom ((parabolicPointsIso l).inv.app A g) := by
    have hn := (parabolicPointsIso l).inv.naturality φ
    rw [parabolicFunctor_map, HopfAlgebra.pointsFunctor_map] at hn
    exact congrArg (fun k ↦ k.hom g) hn
  -- Expand only the composite equivalence to apply naturality of its three representing
  -- isomorphisms and the existing dynamic Levi decomposition.
  change (parabolicPointsIso l).inv.app B
    (leviDecompositionMulEquiv B l
      ⟨l.unipotentPointsIso.hom.app B
          (AffineGroup.Product.pointsMulEquiv (AlgHom.mapValue φ.hom f)).1,
        (leviPointsIso l).hom.app B
          (AffineGroup.Product.pointsMulEquiv (AlgHom.mapValue φ.hom f)).2⟩) =
    AlgHom.mapValue φ.hom ((parabolicPointsIso l).inv.app A
      (leviDecompositionMulEquiv A l
        ⟨l.unipotentPointsIso.hom.app A (AffineGroup.Product.pointsMulEquiv f).1,
          (leviPointsIso l).hom.app A (AffineGroup.Product.pointsMulEquiv f).2⟩))
  rw [AffineGroup.Product.pointsMulEquiv_mapValue, hU, hZ, ← hP,
    mapParabolic_leviDecompositionMulEquiv_apply, leviSemidirectMap_apply]

/-- The Levi factorization as a bijection between algebra-category hom sets. -/
private noncomputable def decompositionHomEquiv (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{v} R) :
    (CommAlgCat.of R ((U l) ⊗[R] (Z l)) ⟶ A) ≃ (CommAlgCat.of R (P l) ⟶ A) :=
  (HopfAlgebra.pointsHomEquiv _ A).trans
    ((decompositionPointsEquiv l A).trans (HopfAlgebra.pointsHomEquiv _ A).symm)

private theorem decompositionHomEquiv_apply (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{v} R) (f : CommAlgCat.of R ((U l) ⊗[R] (Z l)) ⟶ A) :
    decompositionHomEquiv l A f =
      CommAlgCat.ofHom (decompositionPointsEquiv l A (toConv f.hom)).ofConv := by
  rw [decompositionHomEquiv, Equiv.trans_apply, Equiv.trans_apply,
    HopfAlgebra.pointsHomEquiv_symm_apply, HopfAlgebra.pointsHomEquiv_apply]

private theorem decompositionHomEquiv_naturality (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{v} R} (f : CommAlgCat.of R ((U l) ⊗[R] (Z l)) ⟶ A)
    (φ : A ⟶ B) :
    decompositionHomEquiv l B (f ≫ φ) = decompositionHomEquiv l A f ≫ φ := by
  apply (HopfAlgebra.pointsHomEquiv (P l) B).injective
  simp only [decompositionHomEquiv, Equiv.trans_apply,
    HopfAlgebra.pointsHomEquiv_apply, HopfAlgebra.pointsHomEquiv_symm_apply,
    CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  simpa only [AlgHom.mapValue_apply, toConv_ofConv] using
    decompositionPointsEquiv_mapValue l φ (toConv f.hom)

/-- The algebra-category isomorphism corepresenting the Levi point bijection. -/
private noncomputable def decompositionCoordinateIso (l : H →ₐc[R] LaurentPolynomial R) :
    CommAlgCat.of R (P l) ≅ CommAlgCat.of R ((U l) ⊗[R] (Z l)) :=
  Coyoneda.ext _ _ (fun f ↦ (decompositionHomEquiv l _).symm f)
    (fun f ↦ decompositionHomEquiv l _ f)
    (fun f ↦ Equiv.apply_symm_apply _ f) (fun f ↦ Equiv.symm_apply_apply _ f)
    (decompositionHomEquiv_naturality l)

/-- The coordinate morphism is the point bijection evaluated at the identity. -/
private theorem decompositionCoordinateIso_hom (l : H →ₐc[R] LaurentPolynomial R) :
    (decompositionCoordinateIso l).hom =
      decompositionHomEquiv l (CommAlgCat.of R ((U l) ⊗[R] (Z l))) (𝟙 _) := by
  -- Coyoneda corepresents the natural point bijection by its value at the identity.
  rfl

/-- Multiplication `U(l) × Z(l) → P(l)` is an isomorphism of underlying affine schemes,
expressed contravariantly as an equivalence of coordinate algebras. The tensor product is
not equipped with the semidirect-product Hopf structure here. -/
noncomputable def parabolicCoordinateAlgEquiv (l : H →ₐc[R] LaurentPolynomial R) :
    (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) ≃ₐ[R]
      (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) ⊗[R]
        (H ⧸ (leviDefiningHopfIdeal l).toIdeal) :=
  CommAlgCat.algEquivOfIso (decompositionCoordinateIso l)

private theorem parabolicCoordinateAlgEquiv_toAlgHom (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicCoordinateAlgEquiv l).toAlgHom =
      (decompositionHomEquiv l (CommAlgCat.of R ((U l) ⊗[R] (Z l))) (𝟙 _)).hom := by
  ext h
  exact (CommAlgCat.algEquivOfIso_apply (decompositionCoordinateIso l) h).trans
    (congrArg (fun f ↦ f h) (decompositionCoordinateIso_hom l))

private theorem quotientPointsHom_comp_parabolicCoordinateAlgEquiv
    (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{v} R)
    (f : (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        l.unipotentDefiningHopfIdeal) →ₐ[R] A)
    (g : (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H)
        (leviDefiningHopfIdeal l)) →ₐ[R] A) :
    CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) A
        (toConv ((Algebra.TensorProduct.productMap f g).comp
          (parabolicCoordinateAlgEquiv l).toAlgHom)) =
      CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
          l.unipotentDefiningHopfIdeal A (toConv f) *
        CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
          (leviDefiningHopfIdeal l) A (toConv g) := by
  rcases A with ⟨A⟩
  have hn := decompositionHomEquiv_naturality l
    (𝟙 (CommAlgCat.of R ((U l) ⊗[R] (Z l))))
    (CommAlgCat.ofHom (Algebra.TensorProduct.productMap f g))
  rw [Category.id_comp] at hn
  have heq : decompositionPointsEquiv l (CommAlgCat.of R A)
      (toConv (Algebra.TensorProduct.productMap f g)) =
      toConv ((Algebra.TensorProduct.productMap f g).comp
        (parabolicCoordinateAlgEquiv l).toAlgHom) := by
    rw [parabolicCoordinateAlgEquiv_toAlgHom]
    simpa only [decompositionHomEquiv_apply l _ (CommAlgCat.ofHom _), CommAlgCat.hom_ofHom,
      toConv_ofConv, CommAlgCat.hom_comp] using
      congrArg (fun h ↦ toConv (CommAlgCat.Hom.hom h)) hn
  rw [← heq, decompositionPointsEquiv_ambient]
  congr 1 <;> simp

/-- On an ambient coordinate function, the dynamic Levi coordinate equivalence is
comultiplication followed by the unipotent and Levi quotient maps. This characterizes it
on the generators of the parabolic quotient. -/
@[simp]
theorem parabolicCoordinateAlgEquiv_mk
    (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    l.parabolicCoordinateAlgEquiv
        (Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal h) =
      Algebra.TensorProduct.map
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
            l.unipotentDefiningHopfIdeal).hom.toAlgHom
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
            (leviDefiningHopfIdeal l)).hom.toAlgHom
        (Coalgebra.comul (R := R) h) := by
  let qU := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
    l.unipotentDefiningHopfIdeal).hom.toAlgHom
  let qZ := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
    (leviDefiningHopfIdeal l)).hom.toAlgHom
  let A := CommAlgCat.of R ((U l) ⊗[R] (Z l))
  have hid : Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft : (U l) →ₐ[R] A)
      (Algebra.TensorProduct.includeRight : (Z l) →ₐ[R] A) = AlgHom.id R A :=
    Algebra.TensorProduct.lift_includeLeft_includeRight
  have hp := quotientPointsHom_comp_parabolicCoordinateAlgEquiv l A
    Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
  rw [hid, AlgHom.id_comp] at hp
  have hv := congrArg (fun p : WithConv (H →ₐ[R] A) ↦ p.ofConv h) hp
  rw [AlgHom.convMul_apply] at hv
  -- The quotient point maps have sealed categorical carriers; specialize their public
  -- formulas before rewriting inside the tensor-product lift.
  have hqU : (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
      l.unipotentDefiningHopfIdeal A (toConv Algebra.TensorProduct.includeLeft)).ofConv =
      Algebra.TensorProduct.includeLeft.comp qU :=
    congrArg ofConv (CommHopfAlgCat.quotientPointsHom_apply _ _ A _)
  have hqZ : (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
      (leviDefiningHopfIdeal l) A (toConv Algebra.TensorProduct.includeRight)).ofConv =
      Algebra.TensorProduct.includeRight.comp qZ :=
    congrArg ofConv (CommHopfAlgCat.quotientPointsHom_apply _ _ A _)
  rw [hqU, hqZ] at hv
  have ht : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp qU)
      (Algebra.TensorProduct.includeRight.comp qZ) (fun _ _ ↦ .all ..) =
      Algebra.TensorProduct.map qU qZ := by
    ext <;> simp
  rw [ht] at hv
  have hqP : (CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l) A (toConv l.parabolicCoordinateAlgEquiv.toAlgHom)).ofConv h =
      l.parabolicCoordinateAlgEquiv
        ((CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
          (parabolicDefiningHopfIdeal l)).hom h) :=
    congrArg (fun p : WithConv (H →ₐ[R] A) ↦ p.ofConv h)
      (CommHopfAlgCat.quotientPointsHom_apply (_root_.CommHopfAlgCat.of R H)
        (parabolicDefiningHopfIdeal l) A (toConv l.parabolicCoordinateAlgEquiv.toAlgHom))
  have hm : (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l)).hom h =
      Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal h := by
    rw [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact (congrArg l.parabolicCoordinateAlgEquiv hm).symm.trans (hqP.symm.trans hv)

/-- The dynamic unipotent subgroup is an algebra retract of the dynamic parabolic, so it is
formally smooth whenever the dynamic parabolic is. -/
instance formallySmooth_quotient_unipotentDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    [Algebra.FormallySmooth R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)] :
    Algebra.FormallySmooth R (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) := by
  let ε : (H ⧸ (leviDefiningHopfIdeal l).toIdeal) →ₐ[R] R :=
    Bialgebra.counitAlgHom R (H ⧸ (leviDefiningHopfIdeal l).toIdeal)
  refine Algebra.FormallySmooth.of_retract
    ((l.parabolicCoordinateAlgEquiv.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft)
    (((Algebra.TensorProduct.rid R R _).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R _) ε)).comp
        l.parabolicCoordinateAlgEquiv.toAlgHom) ?_
  ext x
  simp

/-- The dynamic Levi subgroup is an algebra retract of the dynamic parabolic, so it is formally
smooth whenever the dynamic parabolic is. -/
instance formallySmooth_quotient_leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    [Algebra.FormallySmooth R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)] :
    Algebra.FormallySmooth R (H ⧸ (leviDefiningHopfIdeal l).toIdeal) := by
  let ε : (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) →ₐ[R] R :=
    Bialgebra.counitAlgHom R (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)
  refine Algebra.FormallySmooth.of_retract
    ((l.parabolicCoordinateAlgEquiv.symm.toAlgHom).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.lid R _).toAlgHom.comp
      (Algebra.TensorProduct.map ε (AlgHom.id R _))).comp
        l.parabolicCoordinateAlgEquiv.toAlgHom) ?_
  ext x
  simp

end BialgHom
