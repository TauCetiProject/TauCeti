/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple

/-!
# The class of a graded quiver vertex simple

The first-arrow resolution of a vertex simple gives its class in the graded Grothendieck group
as the class of the vertex projective minus the class of the direct sum of shifted projectives
indexed by outgoing arrows. This is the resolution identity behind the graded Cartan inverse
and the q-Euler form for a path algebra. The path-length shift is retained in the kernel term.

In `K₀^gr(proj kQ)`, `TauCeti.PathAlgebra.laurentK0_gradedArrowSum_eq_sum` expresses the arrow
kernel class `[⨁_{a : j ⟶ i} (kQ eᵢ){1}]` explicitly as `∑ i, |j ⟶ i| q [kQ eᵢ]`.

The resolution is the graded form of the projective resolution in Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter III, Section 2.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe u v w

variable (k : Type w) (Q : Type u) [Quiver.{v} Q]

section ArrowSumClass

variable [CommRing k] [Fintype Q]

/-- The class of the arrow kernel `⨁_{a : j ⟶ i} (kQ eᵢ){1}` in `K₀^gr(proj kQ)` is
`∑ i, |j ⟶ i| q [kQ eᵢ]`. -/
theorem laurentK0_gradedArrowSum_eq_sum (j : Q) [Finite ((i : Q) × (j ⟶ i))] :
    LaurentK0.of.{max u v w}
        (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
        ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ =
      ∑ i : Q, ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) •
        gradedVertexProjectiveClass k Q i := by
  classical
  let _ (i : Q) : Finite (j ⟶ i) :=
    Finite.of_injective (fun f : j ⟶ i => (⟨i, f⟩ : (i : Q) × (j ⟶ i)))
      fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  let _ (i : Q) : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  let e : Fin (Fintype.card ((i : Q) × (j ⟶ i))) ≃ ((i : Q) × (j ⟶ i)) :=
    (Fintype.equivFin _).symm
  let P := gradedFiniteProjectiveModules (integerGrade k Q)
  let G : ((i : Q) × (j ⟶ i)) → GradedModuleCat.{max u v w} (integerGrade k Q) :=
    fun a => (gradedVertexProjective k Q a.1).shiftObj 1
  let F : Fin (Fintype.card ((i : Q) × (j ⟶ i))) → P.FullSubcategory := fun m =>
    ⟨G (e m), gradedFiniteProjectiveModules_shiftObj
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q (e m).1) 1⟩
  have _ : HasFiniteBiproducts P.FullSubcategory := hasFiniteBiproducts_of_hasBinaryBiproducts
  have _ : HasBiproduct (fun m => G (e m)) := HasBiproduct.of_hasCoproduct _
  have _ : HasBiproduct G := HasBiproduct.of_hasCoproduct _
  let e₁ : P.ι.obj (⨁ F) ≅ ⨁ (fun m => G (e m)) := P.ι.mapBiproduct F
  let e₂ : ⨁ (fun m => G (e m)) ≅ ⨁ G := biproduct.whiskerEquiv e (fun _ => Iso.refl _)
  let e₃ : ⨁ G ≅ GradedModuleCat.directSumObj G :=
    (biproduct.isColimit G).coconePointUniqueUpToIso (GradedModuleCat.coproductCofanIsColimit G)
  let iso : (⨁ F) ≅
      (⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ :
        P.FullSubcategory) :=
    ObjectProperty.isoMk P (e₁ ≪≫ e₂ ≪≫ e₃)
  rw [← LaurentK0.of_congr.{max u v w} _ iso,
    ← LaurentK0.ofExactK0_exactK0_of.{max u v w},
    ← ExactK0.fromSplit_of.{max u v w},
    SplitK0.of_biproduct, map_sum, map_sum]
  have hterm : ∀ m,
      LaurentK0.ofExactK0.{max u v w}
          (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
          (ExactK0.fromSplit.{max u v w} _ (SplitK0.of.{max u v w} (F m))) =
        (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClass k Q (e m).1 := fun m => by
    rw [ExactK0.fromSplit_of.{max u v w}, LaurentK0.ofExactK0_exactK0_of.{max u v w},
      gradedVertexProjectiveClass_eq]
    exact laurentK0_projective_of_shiftObj
      ⟨gradedVertexProjective k Q (e m).1,
        gradedFiniteProjectiveModules_gradedVertexProjective k Q (e m).1⟩ 1
  simp_rw [hterm]
  rw [e.sum_comp fun a : (i : Q) × (j ⟶ i) =>
    (T 1 : LaurentPolynomial ℤ) • gradedVertexProjectiveClass k Q a.1,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul
    (LaurentPolynomial ℤ), smul_smul]

end ArrowSumClass

section SimpleClass

variable [Field k] [Finite Q]

/-- The first-arrow resolution expresses a graded vertex simple in `G₀^gr(mod kQ)` as its
projective cover minus the shifted direct sum of vertex projectives at the heads of its outgoing
arrows. -/
theorem laurentK0_gradedVertexSimple_eq_projective_sub_arrowSum (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    LaurentK0.of.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
        ⟨gradedVertexSimple k Q i, gradedFiniteModules_gradedVertexSimple k Q i⟩ =
      gradedCartanMap (integerGrade k Q) (gradedVertexProjectiveClass k Q i) -
        LaurentK0.of.{max u v w} (gradedFiniteModulesExactStructure (integerGrade k Q))
          ⟨gradedArrowSum k Q i, gradedFiniteModules_gradedArrowSum k Q i⟩ := by
  let _ := integerGradedAlgebra k Q
  let S := gradedVertexSimpleResolution k Q i
  have hS : (GradedExactStructure.abelian _
      (GradedModuleCat.shift (integerGrade k Q))).toExactStructure.Conflation S := by
    rw [GradedExactStructure.abelian_toExactStructure, ExactStructure.abelian_conflation]
    exact shortExact_gradedVertexSimpleResolution k Q i
  have h₁ : gradedFiniteModules (integerGrade k Q) S.X₁ := by
    simpa only [S, gradedVertexSimpleResolution_def] using
      gradedFiniteModules_gradedArrowSum k Q i
  have h₃ : gradedFiniteModules (integerGrade k Q) S.X₃ :=
    by simpa only [S, gradedVertexSimpleResolution_def] using
      gradedFiniteModules_gradedVertexSimple k Q i
  have h := ExactK0.of_conflation_fullSubcategory.{max u v w}
    (isExtensionClosed_gradedFiniteModules_gradedAbelian (𝒜 := integerGrade k Q)) hS h₁ h₃
  rw [← GradedExactStructure.fullSubcategory_toExactStructure
    (E := GradedExactStructure.abelian _ (GradedModuleCat.shift (integerGrade k Q)))
    (P := gradedFiniteModules (integerGrade k Q))
    isExtensionClosed_gradedFiniteModules_gradedAbelian
    gradedFiniteModules_gradedAbelian_shift] at h
  apply_fun LaurentK0.ofExactK0.{max u v w}
      ((GradedExactStructure.abelian _ (GradedModuleCat.shift (integerGrade k Q))).fullSubcategory
        _ isExtensionClosed_gradedFiniteModules_gradedAbelian
          gradedFiniteModules_gradedAbelian_shift) at h
  simp only [map_add, LaurentK0.ofExactK0_exactK0_of] at h
  rw [gradedVertexProjectiveClass_eq, gradedCartanMap_of]
  rw [eq_sub_iff_add_eq]
  simp only [S, gradedVertexSimpleResolution_def] at h
  exact (add_comm _ _).trans h.symm

end SimpleClass

end TauCeti.PathAlgebra
