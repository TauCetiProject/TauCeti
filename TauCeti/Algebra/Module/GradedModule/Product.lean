/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Module.GradedModule.GradedObject
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Degreewise products of internally graded modules

The product of graded modules consists of families with a common finite set of possible degrees.
Its degree-`p` piece is the product of the degree-`p` pieces of the factors. The total module is
the range of the canonical map from the direct sum of these degreewise products to the product
of the total modules. An arbitrary family of inhomogeneous elements need not belong to it.

The internal grading is transported from `InternalGrading.ofGradedObject`. Homogeneous maps of
one common degree lift componentwise into this product. This includes degree-one differentials
and degree-minus-one homotopies, as well as degree-zero graded morphisms.

The construction supplies the graded product needed by the small products of curved DG right
modules in `StablePeriodicCurved`, Layer 6, opening paragraph, within intention 811.

## References

* Mathlib's direct-sum decomposition and module APIs.
* The Tau Ceti contributors, `TauCeti.Algebra.Module.GradedModule.GradedObject`: the internal
  grading of a total graded object is reused here.
-/

public section

open scoped DirectSum

namespace TauCeti.InternalGrading

universe u v w z

variable {R : Type u} [CommRing R] {J : Type v} {M : J → Type w}
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
  (G : ∀ j, InternalGrading R (M j))

/-- Families all of whose components have degree `p`. -/
def productPiece (p : ℤ) : Submodule R (∀ j, M j) :=
  Submodule.pi Set.univ fun j ↦ (G j).piece p

/-- Homogeneity of a family is checked componentwise. -/
@[simp]
theorem mem_productPiece_iff (p : ℤ) (x : ∀ j, M j) :
    x ∈ productPiece G p ↔ ∀ j, x j ∈ (G j).piece p := by
  simp [productPiece]

/-- The families that are finite sums of homogeneous families. -/
def productCarrier : Submodule R (∀ j, M j) :=
  LinearMap.range (DirectSum.coeLinearMap (productPiece G))

/-- Every homogeneous family belongs to the graded product. -/
theorem productPiece_le_productCarrier (p : ℤ) : productPiece G p ≤ productCarrier G := by
  intro x hx
  exact ⟨DirectSum.lof R ℤ (fun q ↦ productPiece G q) p ⟨x, hx⟩,
    DirectSum.coeLinearMap_lof (productPiece G) p ⟨x, hx⟩⟩

private def productCoordinate (j : J) (p : ℤ) :
    productPiece G p →ₗ[R] (G j).piece p where
  toFun x := ⟨x.1 j, (mem_productPiece_iff G p x.1).mp x.2 j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def productComponent (j : J) :
    (⨁ p, productPiece G p) →ₗ[R] ⨁ p, (G j).piece p :=
  DirectSum.lmap (productCoordinate G j)

private theorem productComponent_total (j : J) :
    (DirectSum.coeLinearMap (G j).piece).comp (productComponent G j) =
      (LinearMap.proj j).comp (DirectSum.coeLinearMap (productPiece G)) := by
  apply DirectSum.linearMap_ext R
  intro p
  ext x
  simp [productComponent, productCoordinate]

private theorem product_recompose_injective :
    Function.Injective (DirectSum.coeLinearMap (productPiece G)) := by
  intro x y hxy
  apply DirectSum.ext
  intro p
  apply Subtype.ext
  funext j
  have hj : productComponent G j x = productComponent G j y := by
    apply (DirectSum.decomposeLinearEquiv (G j).piece).symm.injective
    change DirectSum.coeLinearMap (G j).piece (productComponent G j x) =
      DirectSum.coeLinearMap (G j).piece (productComponent G j y)
    calc
      _ = DirectSum.coeLinearMap (productPiece G) x j :=
        LinearMap.congr_fun (productComponent_total G j) x
      _ = DirectSum.coeLinearMap (productPiece G) y j := congrFun hxy j
      _ = _ := (LinearMap.congr_fun (productComponent_total G j) y).symm
  have hp := congrArg (fun t ↦ (t p).1) hj
  change (x p).1 j = (y p).1 j at hp
  exact hp

/-- The sum of the degreewise products is the total graded product. -/
noncomputable def productEquiv :
    (⨁ p, productPiece G p) ≃ₗ[R] productCarrier G :=
  LinearEquiv.ofInjective (DirectSum.coeLinearMap (productPiece G))
    (product_recompose_injective G)

/-- The comparison sums the finitely many homogeneous families. -/
@[simp]
theorem productEquiv_apply (x : ⨁ p, productPiece G p) :
    ((productEquiv G x : productCarrier G) : ∀ j, M j) =
      DirectSum.coeLinearMap (productPiece G) x := by
  rw [productEquiv]
  exact LinearEquiv.ofInjective_apply _ _

/-- The internal grading on the product, obtained from its degreewise product presentation. -/
noncomputable def product : InternalGrading R (productCarrier G) :=
  (ofGradedObject R fun p ↦ ModuleCat.of R (productPiece G p)).map (productEquiv G)

/-- An element of the graded product has degree `p` exactly when each component does. -/
theorem mem_product_piece_iff (p : ℤ) (x : productCarrier G) :
    x ∈ (product G).piece p ↔ ∀ j, x.1 j ∈ (G j).piece p := by
  rw [product, map_piece, ofGradedObject_piece]
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    simpa only [LinearEquiv.coe_coe, productEquiv_apply, DirectSum.coeLinearMap_lof] using
      (mem_productPiece_iff G p t.1).mp t.2
  · intro hx
    let t : productPiece G p := ⟨x.1, (mem_productPiece_iff G p x.1).mpr hx⟩
    refine ⟨DirectSum.lof R ℤ (fun q ↦ productPiece G q) p t, ⟨t, rfl⟩, ?_⟩
    apply Subtype.ext
    simp only [LinearEquiv.coe_coe, productEquiv_apply, DirectSum.coeLinearMap_lof, t]

/-- Evaluation at one factor, as a linear map on the graded product. -/
def productEval (j : J) : productCarrier G →ₗ[R] M j :=
  (LinearMap.proj j).comp (productCarrier G).subtype

/-- Evaluation is the corresponding coordinate of the underlying family. -/
@[simp]
theorem productEval_apply (j : J) (x : productCarrier G) : productEval G j x = x.1 j :=
  by simp only [productEval, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply]

section Lift

variable {N : Type z} [AddCommGroup N] [Module R N] (H : InternalGrading R N)
  (r : ℤ) (f : ∀ j, N →ₗ[R] M j)
  (hf : ∀ j, LinearMap.IsHomogeneous (f j) H.piece (G j).piece r)

include H r hf in
/-- A family of maps of one common degree has values in the total graded product: the finite
degree support of the source element controls every component at once. -/
theorem productLift_mem (x : N) : (fun j ↦ f j x) ∈ productCarrier G := by
  classical
  change (LinearMap.pi f) x ∈ productCarrier G
  rw [← DirectSum.sum_support_decompose H.piece x, map_sum]
  apply (productCarrier G).sum_mem
  intro p hp
  apply productPiece_le_productCarrier G (p + r)
  exact (mem_productPiece_iff G (p + r) _).mpr fun j ↦
    (hf j).map_mem (DirectSum.decompose H.piece x p).2

/-- The componentwise lift of homogeneous maps into the graded product. -/
noncomputable def productLiftLinear : N →ₗ[R] productCarrier G :=
  (LinearMap.pi f).codRestrict (productCarrier G) (productLift_mem G H r f hf)

/-- The homogeneous lift has the prescribed components. -/
@[simp]
theorem productLiftLinear_apply (x : N) (j : J) :
    (productLiftLinear G H r f hf x).1 j = f j x := by
  change (LinearMap.pi f) x j = f j x
  exact LinearMap.pi_apply f x j

/-- The lift has the same common degree as its components. -/
theorem productLiftLinear_isHomogeneous :
    LinearMap.IsHomogeneous (productLiftLinear G H r f hf) H.piece (product G).piece r := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  exact (mem_product_piece_iff G (p + r) _).mpr fun j ↦ (hf j).map_mem hx

end Lift

section Scalars

variable {S : Type*} [Ring S] [Algebra R S]
  [∀ j, Module S (M j)] [∀ j, IsScalarTower R S (M j)]
  (𝒜 : ℤ → Submodule R S) [GradedAlgebra 𝒜]
  [∀ j, SetLike.GradedSMul 𝒜 (G j).piece]

include 𝒜 in
omit [∀ j, IsScalarTower R S (M j)] in
/-- The graded product is stable under the graded scalar action. A scalar also has finite
homogeneous support, so multiplication preserves a common finite degree support. -/
theorem productCarrier_smul_mem (a : S) {x : ∀ j, M j} (hx : x ∈ productCarrier G) :
    a • x ∈ productCarrier G := by
  classical
  obtain ⟨y, rfl⟩ := hx
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, Submodule.zero_mem]
  | add y z hy hz => simpa only [map_add, smul_add] using
      (productCarrier G).add_mem hy hz
  | of p y =>
    rw [DirectSum.coeLinearMap_of]
    rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul]
    apply (productCarrier G).sum_mem
    intro q hq
    apply productPiece_le_productCarrier G (q + p)
    exact (mem_productPiece_iff G (q + p) _).mpr fun j ↦
      SetLike.GradedSMul.smul_mem (B := (G j).piece)
        (DirectSum.decompose 𝒜 a q).2 ((mem_productPiece_iff G p y.1).mp y.2 j)

/-- The same graded product as a submodule for the acting graded algebra. -/
@[expose, implicit_reducible]
def productScalarSubmodule : Submodule S (∀ j, M j) where
  carrier := productCarrier G
  zero_mem' := (productCarrier G).zero_mem
  add_mem' := fun hx hy ↦ (productCarrier G).add_mem hx hy
  smul_mem' := fun a _ hx ↦ productCarrier_smul_mem G 𝒜 a hx

/-- Restricting scalars recovers the base-linear graded-product submodule. -/
@[simp]
theorem productScalarSubmodule_restrictScalars :
    (productScalarSubmodule G 𝒜).restrictScalars R = productCarrier G :=
  rfl

variable {N : Type z} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (H : InternalGrading R N) (r : ℤ) (f : ∀ j, N →ₗ[S] M j)
  (hf : ∀ j, LinearMap.IsHomogeneous ((f j).restrictScalars R) H.piece (G j).piece r)

/-- The componentwise lift is linear over the acting algebra as well as the base ring. -/
noncomputable def productLift : N →ₗ[S] productScalarSubmodule G 𝒜 :=
  (LinearMap.pi f).codRestrict (productScalarSubmodule G 𝒜)
    (productLift_mem G H r (fun j ↦ (f j).restrictScalars R) hf)

/-- The algebra-linear product lift is computed componentwise. -/
@[simp]
theorem productLift_apply (x : N) (j : J) :
    (productLift G 𝒜 H r f hf x).1 j = f j x := by
  change (LinearMap.pi f) x j = f j x
  exact LinearMap.pi_apply f x j

/-- The algebra-linear lift retains the common homogeneous degree. -/
theorem productLift_isHomogeneous :
    LinearMap.IsHomogeneous ((productLift G 𝒜 H r f hf).restrictScalars R)
      H.piece (product G).piece r := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  exact (mem_product_piece_iff G (p + r) _).mpr fun j ↦ (hf j).map_mem hx

end Scalars

end TauCeti.InternalGrading
