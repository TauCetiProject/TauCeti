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

For a differential graded algebra `(B, d_B)`, all `A∞` operations in arity at least three vanish,
so evaluating `B.taylor` on `coalgHom R f` reduces to `d_B ∘ f` plus binary multiplication along
reduced deconcatenation twisted by `σ_B = (InternalGrading.ofDecomposition ℬ).koszulTwist 1`.
Postcomposing suspended Taylor maps with `σ_B` gives `AInfinityAlgebra.barTwistingCochainEquiv`
identifying `A∞` morphisms `A ⟶ B` with degree-one twisting cochains `Tᶜ(sA) →ₗ[R] B`.

Combining this with `cobarTwistingCochainEquiv` yields the **bar--cobar adjunction**
`AInfinityAlgebra.cobarDGAlgHomEquiv : DGAlgHom (Ω Tᶜ(sA)) B ≃ AInfinityHom A B`, the universal
morphism `AInfinityAlgebra.toCobar : A ⟶ Ω Tᶜ(sA)`, and functoriality `AInfinityHom.cobarMap`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uA uA' uA'' uB uC

section NonUnital

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A]
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  {ℬ : ℤ → Submodule R B} [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ] {dB : B →ₗ[R] B}

namespace IsNonUnitalDGAlgebra

theorem toAInfinityAlgebra_taylor_ofLetter (hB : IsNonUnitalDGAlgebra ℬ dB) (x : B) :
    hB.toAInfinityAlgebra.taylor (ReducedTensorWords.ofLetter R B x) = dB x := by
  rw [AInfinityAlgebra.taylor_ofLetter, hB.toAInfinityAlgebra_m_one_apply, Matrix.cons_val_zero]

theorem toAInfinityAlgebra_taylor_of_two (hB : IsNonUnitalDGAlgebra ℬ dB) (x y : B) :
    hB.toAInfinityAlgebra.taylor
        (ReducedTensorWords.of R B (2 : ℕ+) (PiTensorProduct.tprod R ![x, y])) =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 x * y := by
  rw [AInfinityAlgebra.taylor_of_two, hB.toAInfinityAlgebra_grading,
    hB.toAInfinityAlgebra_m_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero]

theorem toAInfinityAlgebra_taylor_prepend_prepend (hB : IsNonUnitalDGAlgebra ℬ dB)
    (x y : B) (w : ReducedTensorWords R B) :
    hB.toAInfinityAlgebra.taylor
      (ReducedTensorWords.prepend R B x (ReducedTensorWords.prepend R B y w)) = 0 := by
  refine LinearMap.congr_fun (f := hB.toAInfinityAlgebra.taylor ∘ₗ
    ReducedTensorWords.prepend R B x ∘ₗ ReducedTensorWords.prepend R B y) (g := 0) ?_ w
  refine ReducedTensorWords.linearMap_ext R B fun k _ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [ReducedTensorWords.prepend_of_tprod, ReducedTensorWords.prepend_of_tprod,
    AInfinityAlgebra.taylor_of_tprod,
    hB.toAInfinityAlgebra_m_of_three_le (by have := k.2; dsimp only; omega)]
  rfl

/-- Evaluating the Taylor map of a nonunital DG algebra on `coalgHom R f` keeps only the one-block
differential term and the two-block deconcatenation product. -/
theorem toAInfinityAlgebra_taylor_coalgHom (hB : IsNonUnitalDGAlgebra ℬ dB)
    (f : ReducedTensorWords R A →ₗ[R] B) (w : ReducedTensorWords R A) :
    hB.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R f w) =
      dB (f w) + TensorProduct.lift (LinearMap.mul R B)
        (TensorProduct.map ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f) f
          (ReducedTensorWords.deconcatenation R A w)) := by
  let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
  refine LinearMap.congr_fun (f := hB.toAInfinityAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R f)
    (g := dB ∘ₗ f + TensorProduct.lift (LinearMap.mul R B) ∘ₗ
      TensorProduct.map (σB ∘ₗ f) f ∘ₗ ReducedTensorWords.deconcatenation R A) ?_ w
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply,
    ReducedTensorWords.of_tprod_eq_subword R n.2]
  rw [ReducedTensorWords.coalgHom_subword, map_add, hB.toAInfinityAlgebra_taylor_ofLetter,
    map_sum, ReducedTensorWords.map_deconcatenation_subword, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [ReducedTensorWords.coalgHom_subword, map_add, map_add, map_sum, map_sum,
    Finset.sum_eq_zero fun _ _ ↦ hB.toAInfinityAlgebra_taylor_prepend_prepend _ _ _,
    add_zero, ReducedTensorWords.prepend_ofLetter, hB.toAInfinityAlgebra_taylor_of_two,
    TensorProduct.lift.tmul, LinearMap.mul_apply', LinearMap.comp_apply]

end IsNonUnitalDGAlgebra

end NonUnital

section Common

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A'] [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B] [Ring C] [Algebra R C]

section TwistingCochain

variable {ℬ : ℤ → Submodule R B} [DirectSum.Decomposition ℬ] {dB : B →ₗ[R] B}

private theorem lift_mul_eq_mul' :
    TensorProduct.lift (LinearMap.mul R B) = LinearMap.mul' R B :=
  TensorProduct.ext' fun _ _ ↦ rfl

private theorem isHomogeneous_koszulTwist_of_one {G : InternalGrading R (ReducedTensorWords R A) ℤ}
    {f : ReducedTensorWords R A →ₗ[R] B} (hf : LinearMap.IsHomogeneous f G.piece ℬ 1) :
    LinearMap.IsHomogeneous ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f)
      G.piece ℬ 1 :=
  LinearMap.isHomogeneous_def.mpr fun p w hw ↦ by
    simpa only [LinearMap.comp_apply, InternalGrading.ofDecomposition_piece] using
      (InternalGrading.ofDecomposition ℬ).koszulTwist_mem_piece (e := p + 1)
        (by simpa only [InternalGrading.ofDecomposition_piece] using hf.map_mem hw) 1

variable [SetLike.GradedMul ℬ]
  {𝒞 : ℤ → Submodule R C} [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞] {dC : C →ₗ[R] C}

private theorem isHomogeneous_suspended_iff {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B} :
    LinearMap.IsHomogeneous f (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
        (hB.toAInfinityAlgebra.grading.shift 1).piece 0 ↔
      LinearMap.IsHomogeneous f
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1 := by
  simp only [LinearMap.isHomogeneous_def, ReducedTensorWords.grading_piece, add_zero,
    hB.toAInfinityAlgebra_grading, InternalGrading.shift_piece,
    InternalGrading.ofDecomposition_piece]

private theorem twistingEquation_eq_neg_koszulTwist (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1)
    (w : ReducedTensorWords R A) :
    let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
    dB ((σB ∘ₗ f) w) + (σB ∘ₗ f) (𝒜.barDifferential w) +
        LinearMap.mul' R B (TensorProduct.map
          ((σB ∘ₗ f) ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)
          (σB ∘ₗ f) (ReducedTensorWords.deconcatenation R A w)) =
      -σB (hB.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R f w) -
        f (𝒜.barDifferential w)) := by
  intro σB
  have hf' : LinearMap.IsHomogeneous f (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece
      (InternalGrading.ofDecomposition ℬ).piece 1 := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hτtwist : (σB ∘ₗ f) ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 =
      -f := LinearMap.ext fun u ↦ by
    have hu := congrArg (fun y ↦ -σB y) (hf'.koszulTwist_apply 1 u)
    simpa [σB, InternalGrading.koszulTwist_koszulTwist] using hu.symm
  have hquad : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
      σB (LinearMap.mul' R B (TensorProduct.map (σB ∘ₗ f) f z)) =
        -LinearMap.mul' R B (TensorProduct.map
          ((σB ∘ₗ f) ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)
          (σB ∘ₗ f) z) := by
    rw [hτtwist]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp [σB, InternalGrading.koszulTwist_ofDecomposition_mul,
        InternalGrading.koszulTwist_koszulTwist]
    | add _ _ hx hy => simp only [map_add, neg_add, hx, hy]
  rw [hB.toAInfinityAlgebra_taylor_coalgHom, lift_mul_eq_mul', map_sub, map_add,
    hB.koszulTwist_map (f w), hquad]
  dsimp only [σB, LinearMap.comp_apply]
  abel

/-- Composing the Taylor map of an `A∞` morphism into a DG algebra with the Koszul twist gives a
twisting cochain on the reduced bar coalgebra. -/
theorem AInfinityHom.isTwistingCochain {𝒜 : AInfinityAlgebra R A}
    {hB : IsNonUnitalDGAlgebra ℬ dB} (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB
      ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor) where
  isHomogeneous := isHomogeneous_koszulTwist_of_one
    ((isHomogeneous_suspended_iff hB).1 g.isHomogeneous_taylor)
  equation w := by
    rw [twistingEquation_eq_neg_koszulTwist 𝒜 hB
      ((isHomogeneous_suspended_iff hB).1 g.isHomogeneous_taylor) w]
    have hcomp := LinearMap.congr_fun g.taylor_comp_barMap w
    rw [g.barMap_eq_coalgHom] at hcomp
    simp only [LinearMap.comp_apply] at hcomp
    rw [hcomp, sub_self, map_zero, neg_zero]

/-- A twisting cochain from the reduced bar coalgebra of `𝒜` to `(B, d_B)` induces an `A∞`
morphism `𝒜 ⟶ B` whose Taylor map is `σ_B ∘ₗ τ`. -/
noncomputable def IsTwistingCochain.toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ) :
    AInfinityHom 𝒜 hB.toAInfinityAlgebra :=
  AInfinityHom.ofTaylor ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ)
    ((isHomogeneous_suspended_iff hB).2 (isHomogeneous_koszulTwist_of_one hτ.isHomogeneous))
    (LinearMap.ext fun w ↦ by
      have hσf : (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ
          ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ) = τ := by
        rw [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]
      have heq := twistingEquation_eq_neg_koszulTwist 𝒜 hB
        (isHomogeneous_koszulTwist_of_one hτ.isHomogeneous) w
      dsimp only at heq
      rw [hσf, hτ.equation w] at heq
      have h0 := congrArg ((InternalGrading.ofDecomposition ℬ).koszulTwist 1) heq.symm
      simpa only [map_neg, map_zero, InternalGrading.koszulTwist_koszulTwist, neg_eq_zero,
        sub_eq_zero, LinearMap.comp_apply] using h0)

@[simp]
theorem IsTwistingCochain.taylor_toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ) :
    (hτ.toAInfinityHom hB).taylor = (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ :=
  AInfinityHom.taylor_ofTaylor _ _ _

namespace AInfinityAlgebra

/-- **`A∞` morphisms into a DG algebra correspond bijectively to twisting cochains** on the
reduced bar coalgebra, via postcomposition of Taylor maps with the Koszul twist `σ_B`. -/
noncomputable def barTwistingCochainEquiv (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) :
    AInfinityHom 𝒜 hB.toAInfinityAlgebra ≃
      {τ : ReducedTensorWords R A →ₗ[R] B //
        IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
          (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ} where
  toFun g := ⟨(InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor, g.isTwistingCochain⟩
  invFun τ := τ.property.toAInfinityHom hB
  left_inv g := AInfinityHom.ext <| by
    simp [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self]
  right_inv τ := Subtype.ext <| by
    simp [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self]

@[simp]
theorem barTwistingCochainEquiv_apply (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    (𝒜.barTwistingCochainEquiv hB g).val =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor := (rfl)

@[simp]
theorem taylor_barTwistingCochainEquiv_symm (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB)
    (τ : {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ}) :
    ((𝒜.barTwistingCochainEquiv hB).symm τ).taylor =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ.val :=
  τ.property.taylor_toAInfinityHom hB

theorem barTwistingCochainEquiv_comp_right {𝒜 : AInfinityAlgebra R A}
    {𝒜' : AInfinityAlgebra R A'} (hB : IsNonUnitalDGAlgebra ℬ dB)
    (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) (k : AInfinityHom 𝒜' 𝒜) :
    (𝒜'.barTwistingCochainEquiv hB (g.comp k)).val =
      (𝒜.barTwistingCochainEquiv hB g).val ∘ₗ k.barMap := by
  rw [barTwistingCochainEquiv_apply, barTwistingCochainEquiv_apply, AInfinityHom.taylor_comp,
    LinearMap.comp_assoc]

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

variable {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra

/-- The **bar--cobar adjunction** between `A∞` algebras and unital differential graded algebras:
DG algebra morphisms `Ω Tᶜ(sA) ⟶ B` correspond bijectively to `A∞` morphisms `A ⟶ B`. -/
noncomputable def cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ≃
      AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hB).trans
    (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm

@[simp]
theorem taylor_cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB φ).taylor w =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (φ (ι R w)) := by
  simp [cobarDGAlgHomEquiv]

@[simp]
theorem cobarDGAlgHomEquiv_symm_apply_ι (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB).symm g (ι R w) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (g.taylor w) := by
  simp [cobarDGAlgHomEquiv]

@[simp]
theorem cobarDGAlgHomEquiv_comp (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC} (ψ : DGAlgHom hB hC)
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
    AInfinityHom 𝒜
      (IsDGAlgebra.toIsNonUnitalDGAlgebra
        𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential).toAInfinityAlgebra :=
  𝒜.cobarDGAlgHomEquiv _ (DGAlgHom.id _)

@[simp]
theorem cobarDGAlgHomEquiv_id (𝒜 : AInfinityAlgebra R A) :
    𝒜.cobarDGAlgHomEquiv _ (DGAlgHom.id _) = 𝒜.toCobar := (rfl)

@[simp]
theorem cobarDGAlgHomEquiv_symm_toCobar (𝒜 : AInfinityAlgebra R A) :
    (𝒜.cobarDGAlgHomEquiv _).symm 𝒜.toCobar = DGAlgHom.id _ :=
  (𝒜.cobarDGAlgHomEquiv _).symm_apply_apply _

theorem taylor_toCobar (𝒜 : AInfinityAlgebra R A) (w : ReducedTensorWords R A) :
    𝒜.toCobar.taylor w =
      ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 w) := by
  rw [toCobar, taylor_cobarDGAlgHomEquiv, DGAlgHom.id_apply, koszulTwist_tensorAlgebraPiece_ι,
    InternalGrading.koszulTwist_shift]
  simp

theorem cobarDGAlgHomEquiv_eq_comp_toCobar (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarDGAlgHomEquiv hB φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobar := by
  simpa only [DGAlgHom.comp_id, cobarDGAlgHomEquiv_id] using
    𝒜.cobarDGAlgHomEquiv_comp φ (DGAlgHom.id _)

theorem eq_cobarDGAlgHomEquiv_symm_iff (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = (𝒜.cobarDGAlgHomEquiv hB).symm g ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobar = g := by
  rw [Equiv.eq_symm_apply, cobarDGAlgHomEquiv_eq_comp_toCobar]

end AInfinityAlgebra

namespace AInfinityHom

private theorem isHomogeneous_barMap_grading {𝒜 : AInfinityAlgebra R A}
    {𝒜' : AInfinityAlgebra R A'} (k : AInfinityHom 𝒜 𝒜') :
    LinearMap.IsHomogeneous k.barMap
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece
      (ReducedTensorWords.grading (𝒜'.grading.shift 1)).piece 0 := by
  simpa only [ReducedTensorWords.grading_piece] using k.isHomogeneous_barMap

/-- An `A∞` morphism `k : A ⟶ A'` induces a DG algebra morphism `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` on cobar
constructions, sending `ι w` to `ι (k.barMap w)`. -/
noncomputable def cobarMap {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar k.barMap
    k.isHomogeneous_barMap_grading (ReducedTensorWords.isCoalgHom_iff.1 k.isCoalgHom_barMap)
    k.barDifferential_comp_barMap

@[simp]
theorem cobarMap_ι {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') (w : ReducedTensorWords R A) :
    k.cobarMap (ι R w) = ι R (k.barMap w) :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap_ι _ _ _ _ _ w

@[simp]
theorem cobarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

@[simp]
theorem cobarMap_comp {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    {𝒜'' : AInfinityAlgebra R A''} (k₂ : AInfinityHom 𝒜' 𝒜'') (k₁ : AInfinityHom 𝒜 𝒜') :
    (k₂.comp k₁).cobarMap = k₂.cobarMap.comp k₁.cobarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

theorem cobarDGAlgHomEquiv_comp_cobarMap {𝒜 : AInfinityAlgebra R A}
    {𝒜' : AInfinityAlgebra R A'} (hB : IsDGAlgebra ℬ dB) (k : AInfinityHom 𝒜' 𝒜)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜'.cobarDGAlgHomEquiv hB (φ.comp k.cobarMap) = (𝒜.cobarDGAlgHomEquiv hB φ).comp k := by
  refine (𝒜'.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).injective (Subtype.ext ?_)
  rw [AInfinityAlgebra.barTwistingCochainEquiv_comp_right]
  simp only [AInfinityAlgebra.cobarDGAlgHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    cobarMap, IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp_cobarMap]

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
