/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct
public import TauCeti.RingTheory.AdicCompletion.CofinalLimit
public import TauCeti.RingTheory.TensorProduct.Quotient

/-!
# The completed tensor product as a limit of simultaneous thickenings

For ideals of definition `I_B` and `I_C`, the completed tensor product is the inverse limit of
`(B / I_B ^ (n + 1)) ⊗[A] (C / I_C ^ (n + 1))`. The transition maps are the tensor products
of the quotient maps. The cone constructed here has apex the existing completed tensor
product, and its projections send a represented tensor to the tensor of its residue classes.
This describes the coordinate rings of simultaneous infinitesimal fibre products.

The proof compares the powers of `J = I_B ⊗ 1 + 1 ⊗ I_C` with the sums of the separately
extended powers, and then uses the cofinal quotient limit of an adic completion.

Reference: Grothendieck–Dieudonné, EGA I, Ch. 0, 7.7.1, and Ch. I, 10.7.
-/

public section

open CategoryTheory Limits Opposite TensorProduct

namespace TauCeti.AdicRing.CompletedTensorProduct

universe u

variable (A : Type*) (B C : Type u) [CommRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [Algebra A B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [Algebra A C]

/-- The sum of the extensions of the `(n + 1)`-st powers of the factor ideals of definition. -/
noncomputable abbrev truncationIdeal (n : ℕ) : Ideal (B ⊗[A] C) :=
  (IsAdicRing.ideal B ^ (n + 1)).map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) ⊔
    (IsAdicRing.ideal C ^ (n + 1)).map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C)

/-- The separate-power ideals decrease with the level. -/
theorem truncationIdeal_antitone : Antitone (truncationIdeal A B C) := by
  intro m n h
  exact sup_le_sup (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
    (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- Separate powers are contained in the corresponding power of the tensor ideal. -/
theorem truncationIdeal_le_pow (n : ℕ) :
    truncationIdeal A B C n ≤ tensorIdeal A B C ^ (n + 1) := by
  simp only [truncationIdeal, Ideal.map_pow, tensorIdeal_def]
  exact sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

/-- A sufficiently deep power of the tensor ideal lies in the separate-power ideal. -/
theorem pow_le_truncationIdeal (n : ℕ) :
    tensorIdeal A B C ^ ((n + 1) + (n + 1)) ≤ truncationIdeal A B C n := by
  simpa only [truncationIdeal, tensorIdeal_def, Ideal.map_pow] using
    (Ideal.sup_pow_add_le_pow_sup_pow (I := (IsAdicRing.ideal B).map
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C))
      (J := (IsAdicRing.ideal C).map
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C)) (n := n + 1) (m := n + 1))

/-- The inverse system of tensor products of the two infinitesimal reductions. -/
noncomputable abbrev thickeningDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of
    ((B ⧸ IsAdicRing.ideal B ^ (n.unop + 1)) ⊗[A]
      (C ⧸ IsAdicRing.ideal C ^ (n.unop + 1)))
  map f := CommRingCat.ofHom (Algebra.TensorProduct.map
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))))
    (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))))).toRingHom
  map_id _ := by ext b <;> rfl
  map_comp _ _ := by ext b <;> rfl

/-- Levelwise, the tensor products of reductions are quotients by the separate-power ideals. -/
noncomputable def thickeningDiagramIso : thickeningDiagram A B C ≅
    Ideal.quotientDiagram (truncationIdeal A B C) (truncationIdeal_antitone A B C) :=
  NatIso.ofComponents
    (fun n ↦ (Algebra.TensorProduct.quotientTensorQuotientEquiv (A := A)
      (IsAdicRing.ideal B ^ (n.unop + 1))
      (IsAdicRing.ideal C ^ (n.unop + 1))).toRingEquiv.toCommRingCatIso)
    (by
      intro n m f
      apply CommRingCat.hom_ext
      dsimp only [thickeningDiagram, Ideal.quotientDiagram,
        RingEquiv.toCommRingCatIso, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
      ext b <;> simp)

/-- The cone from the completed tensor product to the simultaneous thickenings.
Its apex is exposed so that the limit API accepts the completed tensor product directly. -/
@[expose] noncomputable def thickeningCone : Cone (thickeningDiagram A B C) :=
  (Cone.postcompose (thickeningDiagramIso A B C).inv).obj
    ((AdicCompletion.quotientCone (tensorIdeal A B C) (truncationIdeal A B C)
      (truncationIdeal_antitone A B C) (fun n ↦ ⟨_, pow_le_truncationIdeal A B C n⟩)).extend
        (adicCompletionEquiv A B C).toRingEquiv.toCommRingCatIso.hom)

/-- The completed tensor product is the limit of the tensor products of the simultaneous
infinitesimal reductions, with their actual quotient transition maps. -/
noncomputable def isLimitThickeningCone : IsLimit (thickeningCone A B C) :=
  (IsLimit.postcomposeInvEquiv (thickeningDiagramIso A B C) _).symm
    (IsLimit.extendIso _ (AdicCompletion.isLimitQuotientCone (tensorIdeal A B C)
      (truncationIdeal A B C) (truncationIdeal_antitone A B C)
      (fun n ↦ ⟨_, pow_le_truncationIdeal A B C n⟩)
      (fun n ↦ (truncationIdeal_le_pow A B C n).trans
        (Ideal.pow_le_pow_right (Nat.le_succ n)))))

/-- The projection to the tensor product of the two `(n + 1)`-st reductions. -/
noncomputable def thickeningProjection (n : ℕ) : CompletedTensorProduct A B C →+*
    (B ⧸ IsAdicRing.ideal B ^ (n + 1)) ⊗[A] (C ⧸ IsAdicRing.ideal C ^ (n + 1)) :=
  ((thickeningCone A B C).π.app (op n)).hom

/-- The cone components are the named projections to simultaneous thickenings. -/
theorem thickeningCone_π (n : ℕ) :
    (thickeningCone A B C).π.app (op n) = CommRingCat.ofHom (thickeningProjection A B C n) :=
  (rfl)

/-- Projection is reduction to the separate-power quotient followed by the tensor comparison. -/
theorem thickeningProjection_eq (n : ℕ) :
    thickeningProjection A B C n =
      (Algebra.TensorProduct.quotientTensorQuotientEquiv (A := A)
        (IsAdicRing.ideal B ^ (n + 1)) (IsAdicRing.ideal C ^ (n + 1))).symm.toRingHom.comp
          ((AdicCompletion.toQuotient (tensorIdeal A B C)
            ⟨_, pow_le_truncationIdeal A B C n⟩).comp (adicCompletionEquiv A B C).toRingHom) := by
  simp [thickeningProjection, thickeningCone, thickeningDiagramIso, NatIso.ofComponents,
    RingEquiv.toCommRingCatIso, AdicCompletion.quotientCone, RingHom.comp_assoc]

/-- Reduction from a deeper simultaneous thickening commutes with projection. -/
@[simp]
theorem thickeningProjection_comp_map {m n : ℕ} (h : m ≤ n) :
    (Algebra.TensorProduct.map
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (I := IsAdicRing.ideal B) (Nat.succ_le_succ h)))
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (I := IsAdicRing.ideal C) (Nat.succ_le_succ h))) : _ →+* _).comp
        (thickeningProjection A B C n) = thickeningProjection A B C m := by
  have hw := (thickeningCone A B C).w (homOfLE h).op
  rw [thickeningCone_π, thickeningCone_π] at hw
  exact congrArg CommRingCat.Hom.hom hw

/-- Maps into the completed tensor product are determined by their thickening projections. -/
theorem thickeningProjection_ext {D : Type*} [NonAssocSemiring D]
    {f g : D →+* CompletedTensorProduct A B C}
    (h : ∀ n, (thickeningProjection A B C n).comp f =
      (thickeningProjection A B C n).comp g) : f = g := by
  ext x
  apply Concrete.isLimit_ext _ (isLimitThickeningCone A B C)
  intro n
  exact RingHom.congr_fun (h n.unop) x

/-- A represented ordinary tensor projects to the tensor of its two residue classes. -/
@[simp]
theorem thickeningProjection_algebraMap_tmul (n : ℕ) (b : B) (c : C) :
    thickeningProjection A B C n
      (algebraMap (B ⊗[A] C) (CompletedTensorProduct A B C) (b ⊗ₜ[A] c)) =
        Ideal.Quotient.mk _ b ⊗ₜ[A] Ideal.Quotient.mk _ c := by
  simp [thickeningProjection_eq, AdicCompletion.algebraMap_apply]

end TauCeti.AdicRing.CompletedTensorProduct
