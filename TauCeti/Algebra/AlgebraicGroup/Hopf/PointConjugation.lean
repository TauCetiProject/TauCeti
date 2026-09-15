/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Conjugation by a rational point

A rational point `g` of an affine group scheme acts on the group by the inner automorphism
`x ↦ g * x * g⁻¹`. Contravariantly, this file constructs the corresponding automorphism of
the coordinate Hopf algebra. Its characteristic lemma describes precomposition on points, and
the bialgebra structure records that inner automorphisms are group homomorphisms.

This is the coordinate-algebra operation needed to formulate conjugacy of closed subgroup
schemes, in particular conjugacy of Borel subgroups and maximal tori.

## Main declarations

* `TauCeti.HopfAlgebra.pointConjugationBialgEquiv`: the coordinate Hopf-algebra automorphism
  induced by conjugation by a rational point.
* `TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv`: its action on arbitrary
  algebra-valued points is group-theoretic conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 3.5 and 10.20.
* T. A. Springer, *Linear Algebraic Groups*, Section 6.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v w

variable {R : Type u} [CommSemiring R]
variable {H : Type v} [CommSemiring H] [_root_.HopfAlgebra R H]

private theorem mapValue_algebraOfId {A : Type w} [CommSemiring A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue (H := H) x.ofConv
        (AlgHom.mapValue (H := H) (Algebra.ofId R H) g) =
      AlgHom.mapValue (H := H) (Algebra.ofId R A) g := by
  apply WithConv.ofConv_injective
  ext h
  exact x.ofConv.commutes (g.ofConv h)

/-- Pullback on the coordinate algebra by conjugation by an `R`-valued point. -/
noncomputable def pointConjugationAlgHom (g : WithConv (H →ₐ[R] R)) : H →ₐ[R] H :=
  (Algebra.TensorProduct.productMap
      (AlgHom.mapValue (H := H) (Algebra.ofId R H) g).ofConv
      (AlgHom.id R H)).comp
    (conjugationAlgHom (R := R) (H := H))

/-- Point conjugation is the specialization of the universal conjugation morphism at the
conjugating rational point. -/
theorem toConv_pointConjugationAlgHom (g : WithConv (H →ₐ[R] R)) :
    WithConv.toConv (pointConjugationAlgHom g) =
      AlgHom.mapValue (H := H) (Algebra.ofId R H) g *
        WithConv.toConv (AlgHom.id R H) *
        (AlgHom.mapValue (H := H) (Algebra.ofId R H) g)⁻¹ := by
  rw [pointConjugationAlgHom, productMap_comp_conjugationAlgHom]

/-- Precomposition by point conjugation is group-theoretic conjugation by the corresponding
constant point. -/
theorem comp_pointConjugationAlgHom {A : Type w} [CommSemiring A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    WithConv.toConv (x.ofConv.comp (pointConjugationAlgHom g)) =
      AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
        (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ := by
  change AlgHom.mapValue x.ofConv
      (WithConv.toConv (pointConjugationAlgHom g)) = _
  rw [toConv_pointConjugationAlgHom, map_mul, map_mul, map_inv]
  rw [mapValue_algebraOfId]
  simp [AlgHom.mapValue_apply]

/-- Conjugation by the identity point is the identity coordinate map. -/
@[simp]
theorem pointConjugationAlgHom_one :
    pointConjugationAlgHom (1 : WithConv (H →ₐ[R] R)) = AlgHom.id R H := by
  apply WithConv.toConv_injective
  rw [toConv_pointConjugationAlgHom,
    map_one (AlgHom.mapValue (H := H) (Algebra.ofId R H))]
  simp

/-- Coordinate maps for point conjugation compose in the order forced by contravariance. -/
theorem pointConjugationAlgHom_mul (g h : WithConv (H →ₐ[R] R)) :
    pointConjugationAlgHom (g * h) =
      (pointConjugationAlgHom h).comp (pointConjugationAlgHom g) := by
  apply WithConv.toConv_injective
  rw [comp_pointConjugationAlgHom]
  rw [toConv_pointConjugationAlgHom (g * h), toConv_pointConjugationAlgHom h]
  rw [map_mul (AlgHom.mapValue (H := H) (Algebra.ofId R H))]
  simp only [mul_inv_rev, mul_assoc]

private theorem pointConjugationAlgHom_bijective (g : WithConv (H →ₐ[R] R)) :
    Function.Bijective (pointConjugationAlgHom g) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨pointConjugationAlgHom g⁻¹, ?_, ?_⟩
  · intro x
    have h := AlgHom.congr_fun (pointConjugationAlgHom_mul g g⁻¹) x
    simpa using h.symm
  · intro x
    have h := AlgHom.congr_fun (pointConjugationAlgHom_mul g⁻¹ g) x
    simpa using h.symm

private theorem counit_comp_pointConjugationAlgHom (g : WithConv (H →ₐ[R] R)) :
    (Bialgebra.counitAlgHom R H).comp (pointConjugationAlgHom g) =
      Bialgebra.counitAlgHom R H := by
  apply WithConv.toConv_injective
  rw [comp_pointConjugationAlgHom]
  change AlgHom.mapValue (H := H) (Algebra.ofId R R) g *
      (1 : WithConv (H →ₐ[R] R)) *
      (AlgHom.mapValue (H := H) (Algebra.ofId R R) g)⁻¹ = 1
  simp

private theorem map_comp_comul_pointConjugationAlgHom
    (g : WithConv (H →ₐ[R] R)) :
    (Algebra.TensorProduct.map (pointConjugationAlgHom g)
        (pointConjugationAlgHom g)).comp (Bialgebra.comulAlgHom R H) =
      (Bialgebra.comulAlgHom R H).comp (pointConjugationAlgHom g) := by
  apply WithConv.toConv_injective
  rw [Bialgebra.toConv_comp_comulAlgHom, comp_pointConjugationAlgHom]
  let g' : WithConv (H →ₐ[R] H ⊗[R] H) :=
    AlgHom.mapValue (H := H) (Algebra.ofId R (H ⊗[R] H)) g
  let x : WithConv (H →ₐ[R] H ⊗[R] H) :=
    WithConv.toConv (Algebra.TensorProduct.includeLeft.comp (pointConjugationAlgHom g))
  let y : WithConv (H →ₐ[R] H ⊗[R] H) :=
    WithConv.toConv (Algebra.TensorProduct.includeRight.comp (pointConjugationAlgHom g))
  have hx : x = g' * WithConv.toConv Algebra.TensorProduct.includeLeft * g'⁻¹ := by
    exact comp_pointConjugationAlgHom g
      (WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H))
  have hy : y = g' * WithConv.toConv Algebra.TensorProduct.includeRight * g'⁻¹ := by
    exact comp_pointConjugationAlgHom g
      (WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H))
  simp only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom]
  rw [Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight]
  change x * y = g' * WithConv.toConv (Bialgebra.comulAlgHom R H) * g'⁻¹
  rw [hx, hy, Bialgebra.comulPoint_eq_include_mul]
  simp only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom]
  let a := WithConv.toConv
    (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
  let b := WithConv.toConv
    (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
  change g' * a * g'⁻¹ * (g' * b * g'⁻¹) = g' * (a * b) * g'⁻¹
  calc
    g' * a * g'⁻¹ * (g' * b * g'⁻¹) =
        (g' * a * g'⁻¹ * g') * b * g'⁻¹ := by simp only [mul_assoc]
    _ = (g' * a) * b * g'⁻¹ := by
      rw [show g' * a * g'⁻¹ * g' = g' * a by simp]
    _ = g' * (a * b) * g'⁻¹ := by rw [mul_assoc g' a b]

/-- Conjugation by a rational point as a bialgebra automorphism of the coordinate Hopf algebra. -/
noncomputable def pointConjugationBialgEquiv (g : WithConv (H →ₐ[R] R)) :
    H ≃ₐc[R] H :=
  BialgEquiv.ofBijective
    (BialgHom.ofAlgHom (pointConjugationAlgHom g)
      (counit_comp_pointConjugationAlgHom g)
      (map_comp_comul_pointConjugationAlgHom g))
    (pointConjugationAlgHom_bijective g)

/-- The bialgebra equivalence underlying point conjugation has the expected algebra map. -/
@[simp]
theorem pointConjugationBialgEquiv_toAlgHom (g : WithConv (H →ₐ[R] R)) :
    (pointConjugationBialgEquiv g).toBialgHom.toAlgHom = pointConjugationAlgHom g := by
  rfl

/-- Pulling back an algebra-valued point by the bialgebra automorphism of point conjugation
conjugates it by the corresponding constant point. -/
theorem mapDomain_pointConjugationBialgEquiv {A : Type w} [CommSemiring A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    AlgHom.mapDomain (A := A) (pointConjugationBialgEquiv g).toBialgHom x =
      AlgHom.mapValue (H := H) (Algebra.ofId R A) g * x *
        (AlgHom.mapValue (H := H) (Algebra.ofId R A) g)⁻¹ := by
  rw [AlgHom.mapDomain_apply]
  exact comp_pointConjugationAlgHom g x

end TauCeti.HopfAlgebra
