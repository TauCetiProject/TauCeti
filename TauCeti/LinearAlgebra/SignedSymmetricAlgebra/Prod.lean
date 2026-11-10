/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Prod
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# The signed symmetric algebra of a product

For internally graded modules `V` and `W`, give `V × W` the componentwise grading. Its signed
symmetric algebra is the Koszul-signed graded tensor product of the signed symmetric algebras of
`V` and `W`:

`A(V × W) ≃ A(V) ᵍ⊗ A(W)`, `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`.

Both directions are graded algebra maps for the input-degree gradings, so the equivalence
preserves degree. The multiplication on the right is Mathlib's `GradedTensorProduct`, so for odd
`x` and `y` the product `(1 ᵍ⊗ₜ y) * (x ᵍ⊗ₜ 1)` is `-(x ᵍ⊗ₜ y)`.

This is the disjoint-orbit comparison of orbit algebras with the super tensor product in
J. Pardon, *Contact homology and virtual fundamental cycles*, §1 (equation (1.22) and pp. 8–9).
The construction mirrors Mathlib's `CliffordAlgebra.prodEquiv`, here upgraded to graded algebra
maps.

## Main definitions

* `TauCeti.SignedSym.inl` and `TauCeti.SignedSym.inr`: the graded algebra maps `A(V) → A(V × W)`
  and `A(W) → A(V × W)` induced by the two inclusions.
* `TauCeti.SignedSym.ofProd`: the graded algebra map `A(V × W) → A(V) ᵍ⊗ A(W)`.
* `TauCeti.SignedSym.toProd`: the graded algebra map `A(V) ᵍ⊗ A(W) → A(V × W)`.
* `TauCeti.SignedSym.prodEquiv`: the resulting algebra equivalence.

## Main results

* `TauCeti.SignedSym.inl_mul_inr`: homogeneous images of the two factors supercommute in
  `A(V × W)`.
* `TauCeti.SignedSym.toProd_comp_ofProd` and `TauCeti.SignedSym.ofProd_comp_toProd`: the two
  graded algebra maps are mutually inverse.
* `TauCeti.SignedSym.prodEquiv_mem_iff`: the equivalence identifies the degree-`p` pieces.
-/

public section

open scoped TensorProduct

namespace TauCeti.SignedSym

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable (G : InternalGrading R V) (H : InternalGrading R W)

/-! ### The two inclusions -/

/-- The graded algebra map `A(V) → A(V × W)` induced by the first inclusion. -/
noncomputable def inl : signedSymPiece G →ₐᵍ[R] signedSymPiece (G.prod H) :=
  gradedMap G (G.prod H) (LinearMap.inl R V W) (G.isHomogeneous_inl H)

/-- The graded algebra map `A(W) → A(V × W)` induced by the second inclusion. -/
noncomputable def inr : signedSymPiece H →ₐᵍ[R] signedSymPiece (G.prod H) :=
  gradedMap H (G.prod H) (LinearMap.inr R V W) (G.isHomogeneous_inr H)

/-- The first inclusion sends the generator of `x` to the generator of `(x, 0)`. -/
@[simp]
theorem inl_generator (x : V) : inl G H (generator G x) = generator (G.prod H) (x, 0) := by
  simp [inl]

/-- The second inclusion sends the generator of `y` to the generator of `(0, y)`. -/
@[simp]
theorem inr_generator (y : W) : inr G H (generator H y) = generator (G.prod H) (0, y) := by
  simp [inr]

variable {G H} in
/-- Homogeneous images of the two factors supercommute in `A(V × W)`, with the Koszul sign of
their degrees. -/
theorem inl_mul_inr {p q : ℤ} {a : SignedSym G} {b : SignedSym H}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece H q) :
    inl G H a * inr G H b = ((p * q).negOnePow : ℤ) • (inr G H b * inl G H a) :=
  mul_eq_negOnePow_smul_mul (G.prod H) ((inl G H).map_mem ha) ((inr G H).map_mem hb)

/-! ### The graded tensor product of the factors -/

/-- The graded algebra map `A(V) ᵍ⊗ A(W) → A(V × W)`, `a ᵍ⊗ₜ b ↦ inl a * inr b`. -/
noncomputable def toProd :
    gradedTensorGrading (signedSymPiece G) (signedSymPiece H) →ₐᵍ[R]
      signedSymPiece (G.prod H) :=
  gradedTensorLift _ _ _ (inl G H) (inr G H) fun i j a b ↦ by
    rw [inl_mul_inr a.2 b.2, Units.smul_def, mul_comm j i, Int.negOnePow_def]

/-- `toProd` sends a pure tensor `a ᵍ⊗ₜ b` to `inl a * inr b`. -/
@[simp]
theorem toProd_tmul (a : SignedSym G) (b : SignedSym H) :
    toProd G H (a ᵍ⊗ₜ[R] b) = inl G H a * inr G H b :=
  gradedTensorLift_tmul _ _ _ _ _ _ a b

/-- The generator assignment `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y` defining `ofProd`. -/
private noncomputable def ofProdGenerator :
    V × W →ₗ[R] signedSymPiece G ᵍ⊗[R] signedSymPiece H :=
  LinearMap.coprod
    ((GradedTensorProduct.includeLeft (signedSymPiece G) (signedSymPiece H)).toLinearMap ∘ₗ
      generator G)
    ((GradedTensorProduct.includeRight (signedSymPiece G) (signedSymPiece H)).toLinearMap ∘ₗ
      generator H)

/-- The generator assignment of `ofProd` on a pair. -/
private theorem ofProdGenerator_apply (z : V × W) :
    ofProdGenerator G H z = generator G z.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] generator H z.2 :=
  (rfl)

/-- The generator assignment of `ofProd` preserves degree. -/
private theorem isHomogeneous_ofProdGenerator :
    LinearMap.IsHomogeneous (ofProdGenerator G H) (G.prod H).piece
      (gradedTensorGrading (signedSymPiece G) (signedSymPiece H)) 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_
  rw [InternalGrading.prod_piece, Submodule.mem_prod] at hz
  rw [ofProdGenerator_apply, add_zero]
  refine add_mem ?_ ?_
  · simpa using tmul_mem_gradedTensorGrading _ _ (generator_mem_signedSymPiece G hz.1)
      (SetLike.one_mem_graded (signedSymPiece H))
  · simpa using tmul_mem_gradedTensorGrading _ _ (SetLike.one_mem_graded (signedSymPiece G))
      (generator_mem_signedSymPiece H hz.2)

/-- The values of the generator assignment of `ofProd` satisfy the Koszul relation. -/
private theorem ofProdGenerator_mul_comm (p q : ℤ) (z z' : V × W)
    (hz : z ∈ (G.prod H).piece p) (hz' : z' ∈ (G.prod H).piece q) :
    ofProdGenerator G H z * ofProdGenerator G H z' =
      ((p * q).negOnePow : ℤ) • (ofProdGenerator G H z' * ofProdGenerator G H z) := by
  rw [InternalGrading.prod_piece, Submodule.mem_prod] at hz hz'
  simp only [ofProdGenerator_apply, ← Units.smul_def]
  have h₁₁ : generator G z.1 ᵍ⊗ₜ[R] (1 : SignedSym H) * generator G z'.1 ᵍ⊗ₜ[R] 1 =
      (p * q).negOnePow • (generator G z'.1 ᵍ⊗ₜ[R] (1 : SignedSym H) *
        generator G z.1 ᵍ⊗ₜ[R] 1 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    simp only [← GradedTensorProduct.includeLeft_apply, ← map_mul,
      generator_mul_generator G hz.1 hz'.1, Units.smul_def, map_zsmul]
  have h₂₂ : (1 : SignedSym G) ᵍ⊗ₜ[R] generator H z.2 * 1 ᵍ⊗ₜ[R] generator H z'.2 =
      (p * q).negOnePow • ((1 : SignedSym G) ᵍ⊗ₜ[R] generator H z'.2 *
        1 ᵍ⊗ₜ[R] generator H z.2 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    simp only [← GradedTensorProduct.includeRight_apply, ← map_mul,
      generator_mul_generator H hz.2 hz'.2, Units.smul_def, map_zsmul]
  have h₁₂ : generator G z.1 ᵍ⊗ₜ[R] (1 : SignedSym H) * 1 ᵍ⊗ₜ[R] generator H z'.2 =
      (p * q).negOnePow • ((1 : SignedSym G) ᵍ⊗ₜ[R] generator H z'.2 *
        generator G z.1 ᵍ⊗ₜ[R] 1 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    rw [Units.smul_def]
    exact gradedTensor_tmul_one_mul_one_tmul_comm (generator_mem_signedSymPiece G hz.1)
      (generator_mem_signedSymPiece H hz'.2)
  have h₂₁ : (1 : SignedSym G) ᵍ⊗ₜ[R] generator H z.2 * generator G z'.1 ᵍ⊗ₜ[R] 1 =
      (p * q).negOnePow • (generator G z'.1 ᵍ⊗ₜ[R] (1 : SignedSym H) *
        1 ᵍ⊗ₜ[R] generator H z.2 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    rw [gradedTensor_tmul_one_mul_one_tmul_comm (generator_mem_signedSymPiece G hz'.1)
      (generator_mem_signedSymPiece H hz.2), mul_comm q p, ← Units.smul_def, smul_smul,
      Int.units_mul_self, one_smul]
  rw [add_mul, mul_add, mul_add, h₁₁, h₁₂, h₂₁, h₂₂]
  simp only [add_mul, mul_add, smul_add]

/-- The graded algebra map `A(V × W) → A(V) ᵍ⊗ A(W)`, `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
noncomputable def ofProd :
    signedSymPiece (G.prod H) →ₐᵍ[R]
      gradedTensorGrading (signedSymPiece G) (signedSymPiece H) :=
  gradedLift (G.prod H) _ (ofProdGenerator G H) (ofProdGenerator_mul_comm G H)
    (isHomogeneous_ofProdGenerator G H)

/-- `ofProd` sends the generator of `(x, y)` to `x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
@[simp]
theorem ofProd_generator (z : V × W) :
    ofProd G H (generator (G.prod H) z) =
      generator G z.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] generator H z.2 :=
  gradedLift_generator _ _ _ _ _ z

/-- `ofProd` restricts to the left factor inclusion `a ↦ a ᵍ⊗ₜ 1` on `A(V)`. -/
@[simp]
theorem ofProd_inl (a : SignedSym G) : ofProd G H (inl G H a) = a ᵍ⊗ₜ[R] 1 := by
  have h : (ofProd G H).comp (inl G H) = gradedTensorIncludeLeft _ _ := by
    ext x
    simp
  simpa using GradedAlgHom.congr_fun h a

/-- `ofProd` restricts to the right factor inclusion `b ↦ 1 ᵍ⊗ₜ b` on `A(W)`. -/
@[simp]
theorem ofProd_inr (b : SignedSym H) : ofProd G H (inr G H b) = 1 ᵍ⊗ₜ[R] b := by
  have h : (ofProd G H).comp (inr G H) = gradedTensorIncludeRight _ _ := by
    ext y
    simp
  simpa using GradedAlgHom.congr_fun h b

/-- `toProd` is a left inverse of `ofProd`. -/
theorem toProd_comp_ofProd :
    (toProd G H).comp (ofProd G H) = GradedAlgHom.id R (signedSymPiece (G.prod H)) := by
  ext z
  simp [← map_add (generator (G.prod H))]

/-- `ofProd` is a left inverse of `toProd`. -/
theorem ofProd_comp_toProd :
    (ofProd G H).comp (toProd G H) =
      GradedAlgHom.id R (gradedTensorGrading (signedSymPiece G) (signedSymPiece H)) := by
  ext <;> simp

/-- Pointwise form of `toProd_comp_ofProd`. -/
@[simp]
theorem toProd_ofProd (a : SignedSym (G.prod H)) : toProd G H (ofProd G H a) = a :=
  GradedAlgHom.congr_fun (toProd_comp_ofProd G H) a

/-- Pointwise form of `ofProd_comp_toProd`. -/
@[simp]
theorem ofProd_toProd (x : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    ofProd G H (toProd G H x) = x :=
  GradedAlgHom.congr_fun (ofProd_comp_toProd G H) x

/-- The signed symmetric algebra of a product is the Koszul-signed graded tensor product of the
signed symmetric algebras of the factors. `prodEquiv_mem_iff` records that it preserves
degree. -/
noncomputable def prodEquiv :
    SignedSym (G.prod H) ≃ₐ[R] signedSymPiece G ᵍ⊗[R] signedSymPiece H :=
  AlgEquiv.ofAlgHom (ofProd G H).toAlgHom (toProd G H).toAlgHom
    (congrArg GradedAlgHom.toAlgHom (ofProd_comp_toProd G H))
    (congrArg GradedAlgHom.toAlgHom (toProd_comp_ofProd G H))

/-- The forward map of `prodEquiv` is `ofProd`. -/
@[simp]
theorem prodEquiv_apply (a : SignedSym (G.prod H)) : prodEquiv G H a = ofProd G H a := (rfl)

/-- The inverse map of `prodEquiv` is `toProd`. -/
@[simp]
theorem prodEquiv_symm_apply (x : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    (prodEquiv G H).symm x = toProd G H x := (rfl)

/-- The equivalence identifies the degree-`p` piece of `A(V × W)` with the total-degree-`p` piece
of `A(V) ᵍ⊗ A(W)`. -/
theorem prodEquiv_mem_iff {p : ℤ} {a : SignedSym (G.prod H)} :
    prodEquiv G H a ∈ gradedTensorGrading (signedSymPiece G) (signedSymPiece H) p ↔
      a ∈ signedSymPiece (G.prod H) p := by
  refine ⟨fun h ↦ ?_, fun h ↦ (ofProd G H).map_mem h⟩
  simpa using (toProd G H).map_mem h

end TauCeti.SignedSym
