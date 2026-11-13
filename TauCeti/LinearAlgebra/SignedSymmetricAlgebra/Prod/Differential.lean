/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Prod.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.TensorProduct

/-!
# Differentials on the signed symmetric algebra of a product

For differential graded signed symmetric algebras `A(V)` and `A(W)`, the algebra
`A(V × W)` has the differential determined on generators by the sum of the two
factor differentials. The equivalence `SignedSym.prodEquiv` identifies it with
the Koszul tensor differential on `A(V) ᵍ⊗ A(W)`. In particular the factor
inclusions are DG algebra maps, and the differential on a product of their
images carries the sign of the degree of the left factor.

The construction transports the existing tensor differential, then identifies
it with the unique odd extension of the generator assignment. It retains
constant terms in either factor differential. This supplies the algebraic comparison
used for orbit algebras of disjoint unions.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, (1.22), pp. 8–9.
-/

public section

open scoped TensorProduct

namespace TauCeti.SignedSym

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
variable (G : InternalGrading R V ℤ) (H : InternalGrading R W ℤ)
variable (dV : SignedSym G →ₗ[R] SignedSym G) (dW : SignedSym H →ₗ[R] SignedSym H)

/-- The differential on `A(V × W)`, transported from the Koszul tensor differential.
For DG factor differentials, `prodDifferential_generator` gives its generator values. -/
noncomputable def prodDifferential : SignedSym (G.prod H) →ₗ[R] SignedSym (G.prod H) :=
  (toProd G H).toAlgHom.toLinearMap ∘ₗ
    dgTensorDifferential (signedSymPiece G) (signedSymPiece H) dV dW ∘ₗ
      (ofProd G H).toAlgHom.toLinearMap

/-- Evaluation of the transported differential. -/
theorem prodDifferential_apply (a : SignedSym (G.prod H)) :
    prodDifferential G H dV dW a =
      toProd G H (dgTensorDifferential (signedSymPiece G) (signedSymPiece H) dV dW
        (ofProd G H a)) := (rfl)

/-- The product comparison intertwines the product and tensor differentials. -/
@[simp]
theorem ofProd_prodDifferential (a : SignedSym (G.prod H)) :
    ofProd G H (prodDifferential G H dV dW a) =
      dgTensorDifferential (signedSymPiece G) (signedSymPiece H) dV dW (ofProd G H a) := by
  rw [prodDifferential_apply, ofProd_toProd]

/-- The inverse product comparison also intertwines the differentials. -/
@[simp]
theorem prodDifferential_toProd (a : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    prodDifferential G H dV dW (toProd G H a) =
      toProd G H (dgTensorDifferential (signedSymPiece G) (signedSymPiece H) dV dW a) := by
  rw [prodDifferential_apply, ofProd_toProd]

variable {G H dV dW}

/-- DG factor differentials give a DG differential on the signed symmetric algebra of the
product of the generator modules. -/
theorem isDGAlgebra_prodDifferential (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    IsDGAlgebra (signedSymPiece (G.prod H)) (prodDifferential G H dV dW) where
  map_mem hx := (toProd G H).map_mem
    ((isDGAlgebra_gradedTensorGrading hV hW).map_mem ((ofProd G H).map_mem hx))
  sq_zero a := by
    simp only [prodDifferential_apply, ofProd_toProd,
      (isDGAlgebra_gradedTensorGrading hV hW).sq_zero, map_zero]
  leibniz hx b := by
    apply (prodEquiv G H).injective
    simp only [prodEquiv_apply, ofProd_prodDifferential, map_mul, map_add, map_zsmul_unit]
    exact (isDGAlgebra_gradedTensorGrading hV hW).leibniz ((ofProd G H).map_mem hx) _

/-- The left inclusion commutes with the differential when the right factor kills the unit. -/
@[simp]
theorem prodDifferential_inl (hW : dW 1 = 0) (a : SignedSym G) :
    prodDifferential G H dV dW (inl G H a) = inl G H (dV a) := by
  apply (prodEquiv G H).injective
  simp [dgTensorDifferential_tmul, hW]

/-- The right inclusion commutes with the differential when the left factor kills the unit. -/
@[simp]
theorem prodDifferential_inr (hV : dV 1 = 0) (b : SignedSym H) :
    prodDifferential G H dV dW (inr G H b) = inr G H (dW b) := by
  apply (prodEquiv G H).injective
  simp only [prodEquiv_apply, ofProd_prodDifferential, ofProd_inr]
  rw [dgTensorDifferential_tmul_of_mem (SetLike.one_mem_graded (signedSymPiece G)), hV]
  simp

/-- On a generator pair the differential is the sum of the included factor values.
No restriction on the word lengths of these values is imposed. -/
@[simp]
theorem prodDifferential_generator (hV : dV 1 = 0) (hW : dW 1 = 0) (z : V × W) :
    prodDifferential G H dV dW (generator (G.prod H) z) =
      inl G H (dV (generator G z.1)) + inr G H (dW (generator H z.2)) := by
  have hz : generator (G.prod H) z =
      inl G H (generator G z.1) + inr G H (generator H z.2) := by
    simp only [inl_generator, inr_generator, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add, Prod.mk.eta]
  rw [hz, map_add, prodDifferential_inl hW, prodDifferential_inr hV]

/-- The product differential obeys the signed tensor rule on products of included elements. -/
theorem prodDifferential_inl_mul_inr {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (b : SignedSym H) :
    prodDifferential G H dV dW (inl G H a * inr G H b) =
      inl G H (dV a) * inr G H b +
        p.negOnePow • (inl G H a * inr G H (dW b)) := by
  apply (prodEquiv G H).injective
  simp only [prodEquiv_apply, ofProd_prodDifferential, map_mul, map_add, map_zsmul_unit,
    ofProd_inl, ofProd_inr, GradedTensorProduct.tmul_one_mul_one_tmul]
  exact dgTensorDifferential_tmul_of_mem ha b

-- A graded map intertwines signed Leibniz maps if it does so on generators.
-- This handles both factor inclusions without any degree-shift or square-zero assumption.
private theorem map_leibniz_of_generator {U : Type*} [AddCommGroup U] [Module R U]
    {K : InternalGrading R U ℤ} {dU : SignedSym K →ₗ[R] SignedSym K}
    (hU : ∀ {p : ℤ} {a : SignedSym K}, a ∈ signedSymPiece K p →
      ∀ b, dU (a * b) = dU a * b + p.negOnePow • (a * dU b))
    {d : SignedSym (G.prod H) →ₗ[R] SignedSym (G.prod H)}
    (hd : ∀ {p : ℤ} {a : SignedSym (G.prod H)}, a ∈ signedSymPiece (G.prod H) p →
      ∀ b, d (a * b) = d a * b + p.negOnePow • (a * d b))
    (f : signedSymPiece K →ₐᵍ[R] signedSymPiece (G.prod H))
    (hgen : ∀ x, d (f (generator K x)) = f (dU (generator K x)))
    {p : ℤ} {a : SignedSym K} (ha : a ∈ signedSymPiece K p) :
    d (f a) = f (dU a) := by
  have hUone := map_one_eq_zero_of_leibniz hU
  have hdone := map_one_eq_zero_of_leibniz hd
  exact (homogeneous_induction K
    (P := fun p a => a ∈ signedSymPiece K p ∧ d (f a) = f (dU a))
    ⟨SetLike.one_mem_graded _, by simp [hUone, hdone]⟩
    (fun p x hx => ⟨generator_mem_signedSymPiece K hx, hgen x⟩)
    (fun p q a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
      rw [map_mul, hd (Graded.map_mem f ha.1), hU ha.1, ha.2, hb.2]
      simp only [map_add, map_zsmul_unit, map_mul]⟩)
    (fun p => ⟨zero_mem _, by simp⟩)
    (fun p a b ha hb => ⟨add_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩)
    (fun p r a ha => ⟨Submodule.smul_mem _ r ha.1, by simp [ha.2]⟩) ha).2

/-- A signed Leibniz map with the prescribed factor values on generators is the product
differential. Only the signed Leibniz laws on the factors are needed, not degree-one
homogeneity or square-zero laws. -/
theorem eq_prodDifferential
    (hV : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p →
      ∀ b, dV (a * b) = dV a * b + p.negOnePow • (a * dV b))
    (hW : ∀ {p : ℤ} {a : SignedSym H}, a ∈ signedSymPiece H p →
      ∀ b, dW (a * b) = dW a * b + p.negOnePow • (a * dW b))
    {d : SignedSym (G.prod H) →ₗ[R] SignedSym (G.prod H)}
    (hleibniz : ∀ {p : ℤ} {a : SignedSym (G.prod H)}, a ∈ signedSymPiece (G.prod H) p →
      ∀ b, d (a * b) = d a * b + p.negOnePow • (a * d b))
    (hgen : ∀ z : V × W, d (generator (G.prod H) z) =
      inl G H (dV (generator G z.1)) + inr G H (dW (generator H z.2))) :
    d = prodDifferential G H dV dW := by
  have hinl {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) :=
    map_leibniz_of_generator hV hleibniz (inl G H)
      (fun x => by simpa using hgen (x, 0)) ha
  have hinr {q : ℤ} {b : SignedSym H} (hb : b ∈ signedSymPiece H q) :=
    map_leibniz_of_generator hW hleibniz (inr G H)
      (fun y => by simpa using hgen (0, y)) hb
  have hcomp : d ∘ₗ (toProd G H).toAlgHom.toLinearMap =
      prodDifferential G H dV dW ∘ₗ (toProd G H).toAlgHom.toLinearMap := by
    refine gradedTensor_linearMap_ext (signedSymPiece G) (signedSymPiece H)
      fun p q a ha b hb => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
      toProd_tmul, prodDifferential_inl_mul_inr ha,
      hleibniz (Graded.map_mem (inl G H) ha), hinl ha, hinr hb]
  ext a
  simpa using LinearMap.congr_fun hcomp (ofProd G H a)

/-- The DG algebra map `A(V) → A(V × W)` induced by the first factor inclusion. -/
noncomputable def dgInl (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    DGAlgHom hV (isDGAlgebra_prodDifferential hV hW) where
  toGradedAlgHom := inl G H
  map_d' a := prodDifferential_inl hW.map_one_eq_zero a

/-- The DG algebra map `A(W) → A(V × W)` induced by the second factor inclusion. -/
noncomputable def dgInr (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    DGAlgHom hW (isDGAlgebra_prodDifferential hV hW) where
  toGradedAlgHom := inr G H
  map_d' b := prodDifferential_inr hV.map_one_eq_zero b

/-- The DG algebra map `A(V × W) → A(V) ᵍ⊗ A(W)` lifting `ofProd`. -/
noncomputable def dgOfProd (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    DGAlgHom (isDGAlgebra_prodDifferential hV hW) (isDGAlgebra_gradedTensorGrading hV hW) where
  toGradedAlgHom := ofProd G H
  map_d' a := (ofProd_prodDifferential G H dV dW a).symm

/-- The inverse DG algebra map `A(V) ᵍ⊗ A(W) → A(V × W)` lifting `toProd`. -/
noncomputable def dgToProd (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    DGAlgHom (isDGAlgebra_gradedTensorGrading hV hW) (isDGAlgebra_prodDifferential hV hW) where
  toGradedAlgHom := toProd G H
  map_d' := prodDifferential_toProd G H dV dW

/-- The DG left inclusion has the same values as the graded algebra inclusion. -/
@[simp]
theorem dgInl_apply (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) (a : SignedSym G) :
    dgInl hV hW a = inl G H a := (rfl)

/-- The DG right inclusion has the same values as the graded algebra inclusion. -/
@[simp]
theorem dgInr_apply (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) (b : SignedSym H) :
    dgInr hV hW b = inr G H b := (rfl)

/-- The forward DG comparison has the same values as the graded algebra comparison. -/
@[simp]
theorem dgOfProd_apply (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) (a : SignedSym (G.prod H)) :
    dgOfProd hV hW a = ofProd G H a := (rfl)

/-- The inverse DG comparison has the same values as the graded algebra comparison. -/
@[simp]
theorem dgToProd_apply (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW)
    (a : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    dgToProd hV hW a = toProd G H a := (rfl)

/-- The DG product comparisons compose to the identity on `A(V × W)`. -/
@[simp]
theorem dgToProd_comp_dgOfProd (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    (dgToProd hV hW).comp (dgOfProd hV hW) =
      DGAlgHom.id (isDGAlgebra_prodDifferential hV hW) := by
  apply DGAlgHom.ext
  intro a
  simp

/-- The DG product comparisons compose to the identity on the graded tensor product. -/
@[simp]
theorem dgOfProd_comp_dgToProd (hV : IsDGAlgebra (signedSymPiece G) dV)
    (hW : IsDGAlgebra (signedSymPiece H) dW) :
    (dgOfProd hV hW).comp (dgToProd hV hW) =
      DGAlgHom.id (isDGAlgebra_gradedTensorGrading hV hW) := by
  apply DGAlgHom.ext
  intro a
  simp

end TauCeti.SignedSym
