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

For internally graded modules `V` and `W` over any Koszul-signed degree semiring `ι` (such as `ℤ`
or `ZMod 2`), give `V × W` the componentwise grading. Its signed symmetric algebra is Mathlib's
Koszul-signed graded tensor product of the signed symmetric algebras of `V` and `W`:

`A(V × W) ≃ A(V) ᵍ⊗ A(W)`, `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`.

For integer gradings, both directions upgrade to `GradedAlgHom`s for the total-degree grading
`TauCeti.gradedTensorGrading`, so the equivalence identifies homogeneous pieces degree by degree.
The multiplication on the right is Mathlib's `GradedTensorProduct`, so for odd `x` and `y` the
product `(1 ᵍ⊗ₜ y) * (x ᵍ⊗ₜ 1)` is `-(x ᵍ⊗ₜ y)`.

This is the disjoint-orbit comparison of orbit algebras with the super tensor product in
J. Pardon, *Contact homology and virtual fundamental cycles*, §1 (equation (1.22) and pp. 8–9).
The construction mirrors Mathlib's `CliffordAlgebra.prodEquiv`, upgraded to graded algebra maps in
integer degree.

## Main definitions

* `TauCeti.SignedSym.inl` and `TauCeti.SignedSym.inr`: the graded algebra maps `A(V) → A(V × W)`
  and `A(W) → A(V × W)` induced by the two inclusions.
* `TauCeti.SignedSym.prodEquiv`: the algebra equivalence `A(V × W) ≃ₐ[R] A(V) ᵍ⊗ A(W)` over any
  Koszul-signed grading index semiring `ι`.
* `TauCeti.SignedSym.ofProd` and `TauCeti.SignedSym.toProd`: the mutually inverse `ℤ`-graded
  algebra maps upgrading `prodEquiv` and its inverse.

## Main results

* `TauCeti.SignedSym.inl_mul_inr`: homogeneous images of the two factors supercommute in
  `A(V × W)`.
* `TauCeti.SignedSym.toProd_comp_ofProd` and `TauCeti.SignedSym.ofProd_comp_toProd`: the two
  `ℤ`-graded algebra maps are mutually inverse.
* `TauCeti.SignedSym.prodEquiv_mem_iff`: for integer gradings, the equivalence identifies the
  degree-`p` pieces.
-/

public section

open scoped TensorProduct

namespace TauCeti.SignedSym

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

section General

variable {ι : Type*} [DecidableEq ι] [CommSemiring ι] [Module ι (Additive ℤˣ)]
variable (G : InternalGrading R V ι) (H : InternalGrading R W ι)

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
theorem inl_mul_inr {p q : ι} {a : SignedSym G} {b : SignedSym H}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece H q) :
    inl G H a * inr G H b = ((-1 : ℤˣ) ^ (p * q)) • (inr G H b * inl G H a) :=
  mul_eq_uzpow_smul_mul (G.prod H) ((inl G H).map_mem ha) ((inr G H).map_mem hb)

/-! ### The graded tensor product equivalence -/

private theorem inl_mul_inr_coe ⦃i j : ι⦄ (a : signedSymPiece G i) (b : signedSymPiece H j) :
    (inl G H).toAlgHom a * (inr G H).toAlgHom b =
      ((-1 : ℤˣ) ^ (j * i)) • ((inr G H).toAlgHom b * (inl G H).toAlgHom a) := by
  simpa only [GradedAlgHom.coe_toAlgHom, mul_comm j i] using inl_mul_inr a.2 b.2

/-- The algebra map `A(V) ᵍ⊗ A(W) → A(V × W)`, `a ᵍ⊗ₜ b ↦ inl a * inr b`. -/
private noncomputable def toProdAlgHom :
    (signedSymPiece G ᵍ⊗[R] signedSymPiece H) →ₐ[R] SignedSym (G.prod H) :=
  GradedTensorProduct.lift (signedSymPiece G) (signedSymPiece H)
    (inl G H).toAlgHom (inr G H).toAlgHom (inl_mul_inr_coe G H)

/-- The generator assignment `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y` defining `prodEquiv`. -/
private noncomputable def ofProdGenerator :
    V × W →ₗ[R] signedSymPiece G ᵍ⊗[R] signedSymPiece H :=
  LinearMap.coprod
    ((GradedTensorProduct.includeLeft (signedSymPiece G) (signedSymPiece H)).toLinearMap ∘ₗ
      generator G)
    ((GradedTensorProduct.includeRight (signedSymPiece G) (signedSymPiece H)).toLinearMap ∘ₗ
      generator H)

/-- The generator assignment on a pair. -/
private theorem ofProdGenerator_apply (z : V × W) :
    ofProdGenerator G H z = generator G z.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] generator H z.2 :=
  (rfl)

/-- The values of `ofProdGenerator` satisfy the Koszul relation. -/
private theorem ofProdGenerator_mul_comm (p q : ι) (z z' : V × W)
    (hz : z ∈ (G.prod H).piece p) (hz' : z' ∈ (G.prod H).piece q) :
    ofProdGenerator G H z * ofProdGenerator G H z' =
      ((-1 : ℤˣ) ^ (p * q)) • (ofProdGenerator G H z' * ofProdGenerator G H z) := by
  rw [InternalGrading.prod_piece, Submodule.mem_prod] at hz hz'
  simp only [ofProdGenerator_apply]
  have h₁₁ : generator G z.1 ᵍ⊗ₜ[R] (1 : SignedSym H) * generator G z'.1 ᵍ⊗ₜ[R] 1 =
      ((-1 : ℤˣ) ^ (p * q)) • (generator G z'.1 ᵍ⊗ₜ[R] (1 : SignedSym H) *
        generator G z.1 ᵍ⊗ₜ[R] 1 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    simp only [← GradedTensorProduct.includeLeft_apply, ← map_mul,
      generator_mul_generator G hz.1 hz'.1, map_zsmul_unit]
  have h₂₂ : (1 : SignedSym G) ᵍ⊗ₜ[R] generator H z.2 * 1 ᵍ⊗ₜ[R] generator H z'.2 =
      ((-1 : ℤˣ) ^ (p * q)) • ((1 : SignedSym G) ᵍ⊗ₜ[R] generator H z'.2 *
        1 ᵍ⊗ₜ[R] generator H z.2 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    simp only [← GradedTensorProduct.includeRight_apply, ← map_mul,
      generator_mul_generator H hz.2 hz'.2, map_zsmul_unit]
  have h₁₂ : generator G z.1 ᵍ⊗ₜ[R] (1 : SignedSym H) * 1 ᵍ⊗ₜ[R] generator H z'.2 =
      ((-1 : ℤˣ) ^ (p * q)) • ((1 : SignedSym G) ᵍ⊗ₜ[R] generator H z'.2 *
        generator G z.1 ᵍ⊗ₜ[R] 1 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :=
    gradedTensor_tmul_one_mul_one_tmul_comm (generator_mem_signedSymPiece G hz.1)
      (generator_mem_signedSymPiece H hz'.2)
  have h₂₁ : (1 : SignedSym G) ᵍ⊗ₜ[R] generator H z.2 * generator G z'.1 ᵍ⊗ₜ[R] 1 =
      ((-1 : ℤˣ) ^ (p * q)) • (generator G z'.1 ᵍ⊗ₜ[R] (1 : SignedSym H) *
        1 ᵍ⊗ₜ[R] generator H z.2 : signedSymPiece G ᵍ⊗[R] signedSymPiece H) := by
    rw [gradedTensor_tmul_one_mul_one_tmul_comm (generator_mem_signedSymPiece G hz'.1)
      (generator_mem_signedSymPiece H hz.2), mul_comm q p, smul_smul, Int.units_mul_self, one_smul]
  rw [add_mul, mul_add, mul_add, h₁₁, h₁₂, h₂₁, h₂₂]
  simp only [add_mul, mul_add, Units.smul_def, zsmul_add]

/-- The algebra map `A(V × W) → A(V) ᵍ⊗ A(W)`, `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
private noncomputable def ofProdAlgHom :
    SignedSym (G.prod H) →ₐ[R] signedSymPiece G ᵍ⊗[R] signedSymPiece H :=
  lift (G.prod H) (ofProdGenerator G H) (ofProdGenerator_mul_comm G H)

private theorem ofProdAlgHom_comp_inl :
    (ofProdAlgHom G H).comp (inl G H).toAlgHom =
      GradedTensorProduct.includeLeft (signedSymPiece G) (signedSymPiece H) := by
  ext x
  simp [ofProdAlgHom, ofProdGenerator]

private theorem ofProdAlgHom_comp_inr :
    (ofProdAlgHom G H).comp (inr G H).toAlgHom =
      GradedTensorProduct.includeRight (signedSymPiece G) (signedSymPiece H) := by
  ext y
  simp [ofProdAlgHom, ofProdGenerator]

/-- The signed symmetric algebra of a product is the Koszul-signed graded tensor product of the
signed symmetric algebras of the factors. For integer gradings, `prodEquiv_mem_iff` records that it
identifies the total-degree pieces. -/
noncomputable def prodEquiv :
    SignedSym (G.prod H) ≃ₐ[R] signedSymPiece G ᵍ⊗[R] signedSymPiece H :=
  AlgEquiv.ofAlgHom (ofProdAlgHom G H) (toProdAlgHom G H)
    (GradedTensorProduct.algHom_ext _ _
      (by ext x; simp [toProdAlgHom, ofProdAlgHom, ofProdGenerator])
      (by ext y; simp [toProdAlgHom, ofProdAlgHom, ofProdGenerator]))
    (hom_ext (G.prod H) fun z ↦ by
      simp [toProdAlgHom, ofProdAlgHom, ofProdGenerator_apply, ← map_add (generator (G.prod H))])

/-- `prodEquiv` sends the generator of `(x, y)` to `x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
@[simp]
theorem prodEquiv_generator (z : V × W) :
    prodEquiv G H (generator (G.prod H) z) =
      generator G z.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] generator H z.2 :=
  lift_generator (G.prod H) (ofProdGenerator G H) (ofProdGenerator_mul_comm G H) z

/-- `prodEquiv` restricts to the left factor inclusion `a ↦ a ᵍ⊗ₜ 1` on `A(V)`. -/
@[simp]
theorem prodEquiv_inl (a : SignedSym G) : prodEquiv G H (inl G H a) = a ᵍ⊗ₜ[R] 1 :=
  AlgHom.congr_fun (ofProdAlgHom_comp_inl G H) a

/-- `prodEquiv` restricts to the right factor inclusion `b ↦ 1 ᵍ⊗ₜ b` on `A(W)`. -/
@[simp]
theorem prodEquiv_inr (b : SignedSym H) : prodEquiv G H (inr G H b) = 1 ᵍ⊗ₜ[R] b :=
  AlgHom.congr_fun (ofProdAlgHom_comp_inr G H) b

/-- The inverse of `prodEquiv` sends a pure tensor `a ᵍ⊗ₜ b` to `inl a * inr b`. -/
@[simp]
theorem prodEquiv_symm_tmul (a : SignedSym G) (b : SignedSym H) :
    (prodEquiv G H).symm (a ᵍ⊗ₜ[R] b) = inl G H a * inr G H b :=
  GradedTensorProduct.lift_tmul (signedSymPiece G) (signedSymPiece H)
    (inl G H).toAlgHom (inr G H).toAlgHom (inl_mul_inr_coe G H) a b

end General

/-! ### Graded algebra maps for integer gradings -/

section Int

variable (G : InternalGrading R V ℤ) (H : InternalGrading R W ℤ)

/-- The generator assignment of `ofProd` preserves integer degree. -/
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

/-- The graded algebra map `A(V) ᵍ⊗ A(W) → A(V × W)`, `a ᵍ⊗ₜ b ↦ inl a * inr b`. -/
noncomputable def toProd :
    gradedTensorGrading (signedSymPiece G) (signedSymPiece H) →ₐᵍ[R]
      signedSymPiece (G.prod H) :=
  gradedTensorLift _ _ _ (inl G H) (inr G H) fun i j a b ↦ by
    simpa only [mul_comm j i] using inl_mul_inr a.2 b.2

/-- The graded algebra map `A(V × W) → A(V) ᵍ⊗ A(W)`, `(x, y) ↦ x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
noncomputable def ofProd :
    signedSymPiece (G.prod H) →ₐᵍ[R]
      gradedTensorGrading (signedSymPiece G) (signedSymPiece H) :=
  gradedLift (G.prod H) _ (ofProdGenerator G H) (ofProdGenerator_mul_comm G H)
    (isHomogeneous_ofProdGenerator G H)

/-- The underlying algebra map of `ofProd` is `prodEquiv`. -/
@[simp]
theorem ofProd_toAlgHom : (ofProd G H).toAlgHom = (prodEquiv G H).toAlgHom := by
  ext z
  simp [ofProd, ofProdGenerator_apply]

/-- `ofProd` agrees pointwise with `prodEquiv`. -/
@[simp]
theorem ofProd_apply (a : SignedSym (G.prod H)) : ofProd G H a = prodEquiv G H a :=
  AlgHom.congr_fun (ofProd_toAlgHom G H) a

/-- `toProd` sends a pure tensor `a ᵍ⊗ₜ b` to `inl a * inr b`. -/
theorem toProd_tmul (a : SignedSym G) (b : SignedSym H) :
    toProd G H (a ᵍ⊗ₜ[R] b) = inl G H a * inr G H b :=
  gradedTensorLift_tmul _ _ _ _ _ _ a b

/-- The underlying algebra map of `toProd` is `(prodEquiv G H).symm`. -/
@[simp]
theorem toProd_toAlgHom : (toProd G H).toAlgHom = (prodEquiv G H).symm.toAlgHom := by
  apply GradedTensorProduct.algHom_ext _ _ <;> ext x <;> simp [toProd_tmul]

/-- `toProd` agrees pointwise with `(prodEquiv G H).symm`. -/
@[simp]
theorem toProd_apply (x : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    toProd G H x = (prodEquiv G H).symm x :=
  AlgHom.congr_fun (toProd_toAlgHom G H) x

/-- `ofProd` sends the generator of `(x, y)` to `x ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ y`. -/
theorem ofProd_generator (z : V × W) :
    ofProd G H (generator (G.prod H) z) =
      generator G z.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] generator H z.2 := by
  rw [ofProd_apply, prodEquiv_generator]

/-- `ofProd` restricts to the left factor inclusion `a ↦ a ᵍ⊗ₜ 1` on `A(V)`. -/
theorem ofProd_inl (a : SignedSym G) : ofProd G H (inl G H a) = a ᵍ⊗ₜ[R] 1 := by
  rw [ofProd_apply, prodEquiv_inl]

/-- `ofProd` restricts to the right factor inclusion `b ↦ 1 ᵍ⊗ₜ b` on `A(W)`. -/
theorem ofProd_inr (b : SignedSym H) : ofProd G H (inr G H b) = 1 ᵍ⊗ₜ[R] b := by
  rw [ofProd_apply, prodEquiv_inr]

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
theorem toProd_ofProd (a : SignedSym (G.prod H)) : toProd G H (ofProd G H a) = a :=
  GradedAlgHom.congr_fun (toProd_comp_ofProd G H) a

/-- Pointwise form of `ofProd_comp_toProd`. -/
theorem ofProd_toProd (x : signedSymPiece G ᵍ⊗[R] signedSymPiece H) :
    ofProd G H (toProd G H x) = x :=
  GradedAlgHom.congr_fun (ofProd_comp_toProd G H) x

/-- The equivalence identifies the degree-`p` piece of `A(V × W)` with the total-degree-`p` piece
of `A(V) ᵍ⊗ A(W)`. -/
theorem prodEquiv_mem_iff {p : ℤ} {a : SignedSym (G.prod H)} :
    prodEquiv G H a ∈ gradedTensorGrading (signedSymPiece G) (signedSymPiece H) p ↔
      a ∈ signedSymPiece (G.prod H) p := by
  rw [← ofProd_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ (ofProd G H).map_mem h⟩
  simpa using (toProd G H).map_mem h

end Int

end TauCeti.SignedSym
