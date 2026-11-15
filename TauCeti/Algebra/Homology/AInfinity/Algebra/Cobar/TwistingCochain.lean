/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain

/-!
# Twisting cochains and the bar--cobar adjunction for `A∞` algebras

For a nonunital differential graded algebra `(B, d_B)`, all `A∞` operations in arity at least three
vanish, so evaluating `B.taylor` on `coalgHom R f` reduces to `d_B ∘ f` plus binary multiplication
along reduced deconcatenation twisted by `σ_B = (InternalGrading.ofDecomposition ℬ).koszulTwist 1`.
Postcomposing suspended Taylor maps with `σ_B` gives `AInfinityAlgebra.barTwistingCochainEquiv`
identifying `A∞` morphisms `A ⟶ B` with degree-one twisting cochains `Tᶜ(sA) →ₗ[R] B`.

When `B` is unital, combining this with `cobarTwistingCochainEquiv` yields the **bar--cobar
adjunction** `AInfinityAlgebra.cobarDGAlgHomEquiv : DGAlgHom (Ω Tᶜ(sA)) B ≃ AInfinityHom A B`, the
universal morphism `AInfinityAlgebra.toCobar : A ⟶ Ω Tᶜ(sA)`, and functoriality
`AInfinityHom.cobarMap`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

namespace TauCeti

open TensorProduct TensorAlgebra ReducedTensorWords

universe uR uA uA' uA'' uB uC

section Common

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A'']

section TwistingCochain

variable [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  {ℬ : ℤ → Submodule R B} [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ] {dB : B →ₗ[R] B}
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  {𝒞 : ℤ → Submodule R C} [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞] {dC : C →ₗ[R] C}

private theorem isHomogeneous_suspended_iff {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B} :
    LinearMap.IsHomogeneous f (gradedPiece (𝒜.grading.shift 1))
        (hB.toAInfinityAlgebra.grading.shift 1).piece 0 ↔
      LinearMap.IsHomogeneous f (grading (𝒜.grading.shift 1)).piece ℬ 1 := by
  simp only [LinearMap.isHomogeneous_def, grading_piece, add_zero, hB.toAInfinityAlgebra_grading,
    InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece]

private theorem twistingEquation_eq_neg_koszulTwist (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f (grading (𝒜.grading.shift 1)).piece ℬ 1)
    (w : ReducedTensorWords R A) :
    let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
    dB ((σB ∘ₗ f) w) + (σB ∘ₗ f) (𝒜.barDifferential w) +
        LinearMap.mul' R B (TensorProduct.map
          ((σB ∘ₗ f) ∘ₗ (grading (𝒜.grading.shift 1)).koszulTwist 1) (σB ∘ₗ f)
          (deconcatenation R A w)) =
      -σB (hB.toAInfinityAlgebra.taylor (coalgHom R f w) - f (𝒜.barDifferential w)) := by
  intro σB; have hf' : LinearMap.IsHomogeneous f (grading (𝒜.grading.shift 1)).piece
      (InternalGrading.ofDecomposition ℬ).piece 1 := by rwa [InternalGrading.ofDecomposition_piece]
  have hτtwist : (σB ∘ₗ f) ∘ₗ (grading (𝒜.grading.shift 1)).koszulTwist 1 = -f :=
    LinearMap.ext fun u ↦ by
      simpa [σB, InternalGrading.koszulTwist_koszulTwist] using
        (congrArg (fun y ↦ -σB y) (hf'.koszulTwist_apply 1 u)).symm
  have hquad : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
      σB (LinearMap.mul' R B (TensorProduct.map (σB ∘ₗ f) f z)) =
        -LinearMap.mul' R B (TensorProduct.map
          ((σB ∘ₗ f) ∘ₗ (grading (𝒜.grading.shift 1)).koszulTwist 1) (σB ∘ₗ f) z) := by
    rw [hτtwist]; intro z; induction z using TensorProduct.inductionOn with
    | tmul u v => simp [σB, InternalGrading.koszulTwist_ofDecomposition_mul,
        InternalGrading.koszulTwist_koszulTwist]
    | add _ _ hx hy => simp only [map_add, neg_add, hx, hy]
  rw [hB.toAInfinityAlgebra_taylor_coalgHom, map_sub, map_add, hB.koszulTwist_map (f w), hquad]
  dsimp only [σB, LinearMap.comp_apply]; abel

/-- Composing the Taylor map of an `A∞` morphism into a nonunital DG algebra with the degree-one
Koszul twist gives a twisting cochain on the reduced bar coalgebra. -/
theorem AInfinityHom.isTwistingCochain_koszulTwist_comp_taylor {𝒜 : AInfinityAlgebra R A}
    {hB : IsNonUnitalDGAlgebra ℬ dB} (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    IsTwistingCochain (grading (𝒜.grading.shift 1)) (deconcatenation R A) 𝒜.barDifferential ℬ dB
      ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor) where
  isHomogeneous := by
    simpa using (InternalGrading.isHomogeneous_koszulTwist_ofDecomposition ℬ 1).comp
      ((isHomogeneous_suspended_iff hB).1 g.isHomogeneous_taylor)
  equation w := by
    rw [twistingEquation_eq_neg_koszulTwist 𝒜 hB
      ((isHomogeneous_suspended_iff hB).1 g.isHomogeneous_taylor) w]
    have hcomp := LinearMap.congr_fun g.taylor_comp_barMap w
    rw [g.barMap_eq_coalgHom] at hcomp; simp only [LinearMap.comp_apply] at hcomp
    rw [hcomp, sub_self, map_zero, neg_zero]

/-- A twisting cochain from the reduced bar coalgebra of `𝒜` to a nonunital DG algebra `(B, d_B)`
induces an `A∞` morphism `𝒜 ⟶ B` whose Taylor map is
`(InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ`. -/
noncomputable def IsTwistingCochain.toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (grading (𝒜.grading.shift 1)) (deconcatenation R A)
      𝒜.barDifferential ℬ dB τ) : AInfinityHom 𝒜 hB.toAInfinityAlgebra :=
  have hστ : LinearMap.IsHomogeneous ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ)
      (grading (𝒜.grading.shift 1)).piece ℬ 1 := by
    simpa using (InternalGrading.isHomogeneous_koszulTwist_ofDecomposition ℬ 1).comp
      hτ.isHomogeneous
  AInfinityHom.ofTaylor ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ)
    ((isHomogeneous_suspended_iff hB).2 hστ)
    (LinearMap.ext fun w ↦ by
      have hσf : (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ
          ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ) = τ := by
        rw [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]
      have heq := twistingEquation_eq_neg_koszulTwist 𝒜 hB hστ w
      dsimp only at heq; rw [hσf, hτ.equation w] at heq
      simpa only [map_neg, map_zero, InternalGrading.koszulTwist_koszulTwist, neg_eq_zero,
        sub_eq_zero, LinearMap.comp_apply] using
        congrArg ((InternalGrading.ofDecomposition ℬ).koszulTwist 1) heq.symm)

/-- The Taylor map of `IsTwistingCochain.toAInfinityHom` is the Koszul-twisted cochain. -/
@[simp] theorem IsTwistingCochain.taylor_toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (grading (𝒜.grading.shift 1)) (deconcatenation R A)
      𝒜.barDifferential ℬ dB τ) :
    (hτ.toAInfinityHom hB).taylor = (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- `IsTwistingCochain.toAInfinityHom` has linear part restricting the twisted cochain to `A`. -/
@[simp] theorem IsTwistingCochain.linearPart_toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (grading (𝒜.grading.shift 1)) (deconcatenation R A)
      𝒜.barDifferential ℬ dB τ) :
    (hτ.toAInfinityHom hB).linearPart =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ ∘ₗ ofLetter R A :=
  LinearMap.ext fun _ ↦ by simp

namespace AInfinityAlgebra

/-- **`A∞` morphisms into a nonunital DG algebra correspond bijectively to twisting cochains** on
the reduced bar coalgebra, via postcomposition of Taylor maps with the degree-one Koszul twist
`(InternalGrading.ofDecomposition ℬ).koszulTwist 1`. -/
noncomputable def barTwistingCochainEquiv (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) :
    AInfinityHom 𝒜 hB.toAInfinityAlgebra ≃
      {τ : ReducedTensorWords R A →ₗ[R] B //
        IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1)) (deconcatenation R A)
          𝒜.barDifferential ℬ dB τ} where
  toFun g := ⟨(InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor,
    g.isTwistingCochain_koszulTwist_comp_taylor⟩
  invFun τ := τ.property.toAInfinityHom hB
  left_inv g := AInfinityHom.ext <| by
    simp [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self]
  right_inv τ := Subtype.ext <| by
    simp [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self]

@[simp] theorem barTwistingCochainEquiv_apply (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    (𝒜.barTwistingCochainEquiv hB g).val =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor := (rfl)

@[simp] theorem taylor_barTwistingCochainEquiv_symm (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (τ) :
    ((𝒜.barTwistingCochainEquiv hB).symm τ).taylor =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ.val :=
  τ.property.taylor_toAInfinityHom hB

/-- The linear part of `(barTwistingCochainEquiv).symm` restricts the twisted cochain to `A`. -/
@[simp] theorem linearPart_barTwistingCochainEquiv_symm (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (τ) :
    ((𝒜.barTwistingCochainEquiv hB).symm τ).linearPart =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ.val ∘ₗ ofLetter R A :=
  τ.property.linearPart_toAInfinityHom hB

/-- Precomposing an `A∞` morphism with `k : A' ⟶ A` pulls back its bar twisting cochain along
`k.barMap`. -/
theorem barTwistingCochainEquiv_comp_right {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (hB : IsNonUnitalDGAlgebra ℬ dB) (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra)
    (k : AInfinityHom 𝒜' 𝒜) :
    (𝒜'.barTwistingCochainEquiv hB (g.comp k)).val =
      (𝒜.barTwistingCochainEquiv hB g).val ∘ₗ k.barMap := by
  rw [barTwistingCochainEquiv_apply, barTwistingCochainEquiv_apply, AInfinityHom.taylor_comp,
    LinearMap.comp_assoc]

/-- Postcomposing an `A∞` morphism with a nonunital DG algebra morphism `ψ : B ⟶ C` pushes forward
its bar twisting cochain by `ψ`. -/
theorem barTwistingCochainEquiv_comp_left (𝒜 : AInfinityAlgebra R A)
    {hB : IsNonUnitalDGAlgebra ℬ dB} {hC : IsNonUnitalDGAlgebra 𝒞 dC}
    (ψ : NonUnitalDGAlgHom hB hC) (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    (𝒜.barTwistingCochainEquiv hC (ψ.toAInfinityStrictHom.toAInfinityHom.comp g)).val =
      ψ.toAInfinityStrictHom.toLinearMap ∘ₗ (𝒜.barTwistingCochainEquiv hB g).val := by
  have hhom : LinearMap.IsHomogeneous ψ.toAInfinityStrictHom.toLinearMap
      (InternalGrading.ofDecomposition ℬ).piece (InternalGrading.ofDecomposition 𝒞).piece 0 := by
    simpa only [hB.toAInfinityAlgebra_grading, hC.toAInfinityAlgebra_grading] using
      ψ.toAInfinityStrictHom.isHomogeneous
  refine LinearMap.ext fun w ↦ ?_
  have htw := hhom.koszulTwist_apply 1 (g.taylor w)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at htw
  simp only [barTwistingCochainEquiv_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    LinearMap.comp_apply, htw]

end AInfinityAlgebra
end TwistingCochain

section CobarAdjunction

variable [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra

/-- The **bar--cobar adjunction** between `A∞` algebras and unital differential graded algebras:
DG algebra morphisms `Ω Tᶜ(sA) ⟶ B` correspond bijectively to `A∞` morphisms `A ⟶ B`. -/
noncomputable def cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ≃
      AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hB).trans
    (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm

@[simp] theorem taylor_cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB φ).taylor w =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (φ (ι R w)) := by
  simp [cobarDGAlgHomEquiv]

/-- The linear part of `cobarDGAlgHomEquiv` negates the Koszul-twisted action on letters. -/
@[simp] theorem linearPart_cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (𝒜.cobarDGAlgHomEquiv hB φ).linearPart =
      -((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ
        (φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] B) ∘ₗ ι R ∘ₗ ofLetter R A) :=
  LinearMap.ext fun _ ↦ by simp

@[simp] theorem cobarDGAlgHomEquiv_symm_apply_ι (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB).symm g (ι R w) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (g.taylor w) := by
  simp [cobarDGAlgHomEquiv]

/-- The bar--cobar adjunction is natural in its target DG algebra. -/
@[simp] theorem cobarDGAlgHomEquiv_comp (𝒜 : AInfinityAlgebra R A) {hB : IsDGAlgebra ℬ dB}
    {hC : IsDGAlgebra 𝒞 dC} (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarDGAlgHomEquiv hC (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (𝒜.cobarDGAlgHomEquiv hB φ) := by
  refine (𝒜.barTwistingCochainEquiv hC.toIsNonUnitalDGAlgebra).injective (Subtype.ext ?_)
  rw [barTwistingCochainEquiv_comp_left]
  simp only [cobarDGAlgHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp]
  exact LinearMap.ext fun _ ↦ by simp

/-- The **universal `A∞` morphism** `A ⟶ Ω Tᶜ(sA)` corresponding under the bar--cobar adjunction
to the identity DG algebra morphism of `Ω Tᶜ(sA)`. -/
noncomputable def toCobar (𝒜 : AInfinityAlgebra R A) :
    AInfinityHom 𝒜 (IsDGAlgebra.toIsNonUnitalDGAlgebra
      𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential).toAInfinityAlgebra :=
  𝒜.cobarDGAlgHomEquiv _ (DGAlgHom.id _)

@[simp] theorem cobarDGAlgHomEquiv_id (𝒜 : AInfinityAlgebra R A) :
    𝒜.cobarDGAlgHomEquiv _ (DGAlgHom.id _) = 𝒜.toCobar := (rfl)

@[simp] theorem cobarDGAlgHomEquiv_symm_toCobar (𝒜 : AInfinityAlgebra R A) :
    (𝒜.cobarDGAlgHomEquiv _).symm 𝒜.toCobar = DGAlgHom.id _ :=
  (𝒜.cobarDGAlgHomEquiv _).symm_apply_apply _

/-- The Taylor map of `𝒜.toCobar` sends a bar word to the generator of its Koszul-twisted word. -/
@[simp] theorem taylor_toCobar (𝒜 : AInfinityAlgebra R A) (w : ReducedTensorWords R A) :
    𝒜.toCobar.taylor w =
      ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 w) := by
  rw [toCobar, taylor_cobarDGAlgHomEquiv, DGAlgHom.id_apply, koszulTwist_tensorAlgebraPiece_ι,
    InternalGrading.koszulTwist_shift]; simp

/-- The linear part of `𝒜.toCobar` sends `a : A` to `-ι (ofLetter (koszulTwist 1 a))`. -/
@[simp] theorem linearPart_toCobar (𝒜 : AInfinityAlgebra R A) :
    𝒜.toCobar.linearPart = -(ι R ∘ₗ ofLetter R A ∘ₗ 𝒜.grading.koszulTwist 1) :=
  LinearMap.ext fun _ ↦ by simp [koszulTwist_grading, InternalGrading.koszulTwist_one_shift_one]

/-- Every `A∞` morphism corresponding to `φ : Ω Tᶜ(sA) ⟶ B` factors as `φ` after `𝒜.toCobar`. -/
theorem cobarDGAlgHomEquiv_eq_comp_toCobar (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarDGAlgHomEquiv hB φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobar := by
  simpa only [DGAlgHom.comp_id, cobarDGAlgHomEquiv_id] using
    𝒜.cobarDGAlgHomEquiv_comp φ (DGAlgHom.id _)

/-- Universal factorization characterization: `φ : Ω Tᶜ(sA) ⟶ B` is the DG algebra lift of
`g : A ⟶ B` if and only if `φ ∘ 𝒜.toCobar = g`. -/
theorem eq_cobarDGAlgHomEquiv_symm_iff (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = (𝒜.cobarDGAlgHomEquiv hB).symm g ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobar = g := by
  rw [Equiv.eq_symm_apply, cobarDGAlgHomEquiv_eq_comp_toCobar]

end AInfinityAlgebra

namespace AInfinityHom

private theorem isHomogeneous_barMap_grading {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') :
    LinearMap.IsHomogeneous k.barMap (grading (𝒜.grading.shift 1)).piece
      (grading (𝒜'.grading.shift 1)).piece 0 := by
  simpa only [grading_piece] using k.isHomogeneous_barMap

/-- An `A∞` morphism `k : A ⟶ A'` induces a DG algebra morphism `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` on cobar
constructions, sending `ι w` to `ι (k.barMap w)`. -/
noncomputable def cobarMap {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar k.barMap
    k.isHomogeneous_barMap_grading (isCoalgHom_iff.1 k.isCoalgHom_barMap)
    k.barDifferential_comp_barMap

@[simp] theorem cobarMap_ι {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') (w : ReducedTensorWords R A) :
    k.cobarMap (ι R w) = ι R (k.barMap w) :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap_ι _ _ _ _ _ w

@[simp] theorem cobarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

@[simp] theorem cobarMap_comp {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    {𝒜'' : AInfinityAlgebra R A''} (k₂ : AInfinityHom 𝒜' 𝒜'') (k₁ : AInfinityHom 𝒜 𝒜') :
    (k₂.comp k₁).cobarMap = k₂.cobarMap.comp k₁.cobarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

/-- The bar--cobar adjunction is natural in its source `A∞` algebra along `cobarMap`. -/
theorem cobarDGAlgHomEquiv_comp_cobarMap {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (hB : IsDGAlgebra ℬ dB) (k : AInfinityHom 𝒜' 𝒜)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜'.cobarDGAlgHomEquiv hB (φ.comp k.cobarMap) = (𝒜.cobarDGAlgHomEquiv hB φ).comp k := by
  refine (𝒜'.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).injective (Subtype.ext ?_)
  rw [AInfinityAlgebra.barTwistingCochainEquiv_comp_right]
  simp only [AInfinityAlgebra.cobarDGAlgHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    cobarMap, IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp_cobarMap]

/-- The universal `A∞` morphism `toCobar` is natural with respect to `AInfinityHom.cobarMap`. -/
theorem cobarMap_comp_toCobar {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜' 𝒜) :
    k.cobarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜'.toCobar =
      𝒜.toCobar.comp k := by
  rw [← AInfinityAlgebra.cobarDGAlgHomEquiv_eq_comp_toCobar
      (hB := 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential),
    ← DGAlgHom.id_comp k.cobarMap, cobarDGAlgHomEquiv_comp_cobarMap,
    AInfinityAlgebra.cobarDGAlgHomEquiv_id]

end AInfinityHom
end CobarAdjunction
end Common
end TauCeti
