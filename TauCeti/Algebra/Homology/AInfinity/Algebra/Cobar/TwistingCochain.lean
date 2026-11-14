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

When the target of an `A∞` morphism `A ⟶ B` is the `A∞` algebra of a differential graded algebra
`(B, d_B)`, all operations of `B` in arity at least three vanish.  Evaluating `B.taylor` on the
Taylor coalgebra map `coalgHom R f` of a suspended linear map `f : Tᶜ(sA) →ₗ[R] B` therefore
reduces to the unary differential `d_B ∘ f` and the binary product along reduced deconcatenation,
with the suspension sign of `taylor_of_two` carried by the Koszul involution
`σ_B = (InternalGrading.ofDecomposition ℬ).koszulTwist 1`.

Composing `f` with `σ_B` (`τ = σ_B ∘ₗ f`, equivalently `f = σ_B ∘ₗ τ`) translates:

* degree `0` for suspended maps `Tᶜ(sA) → sB` into degree `1` for maps `Tᶜ(sA) → B`, and
* the `A∞` component equation `d_B(f w) + μ((σ_B ∘ f) ⊗ f)(Δ w) = f(b_A w)` into the
  cohomological twisting-cochain equation
  `d_B(τ w) + τ(b_A w) + μ((τ ∘ σ_{Tᶜ(sA)}) ⊗ τ)(Δ w) = 0` (`TauCeti.IsTwistingCochain`),

because `σ_B` is an algebra involution anticommuting with `d_B` and `(τ ∘ σ_{Tᶜ(sA)}) u = -f u`.

Combining this bijection (`TauCeti.AInfinityAlgebra.barTwistingCochainEquiv`) with the cobar
universal property `TauCeti.IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv` for unital DG
algebras yields the **bar--cobar adjunction** `TauCeti.AInfinityAlgebra.cobarDGAlgHomEquiv`
identifying DG algebra morphisms `Ω Tᶜ(sA) ⟶ B` with `A∞` morphisms `A ⟶ B`.  Applying the
adjunction to the identity of `Ω Tᶜ(sA)` constructs the universal `A∞` morphism
`TauCeti.AInfinityAlgebra.toCobar : A ⟶ Ω Tᶜ(sA)`, through which every `A∞` morphism from `A` into
a unital DG algebra factors via a unique DG algebra morphism.

## Main definitions

* `TauCeti.AInfinityAlgebra.barTwistingCochainEquiv`: `A∞` morphisms `A ⟶ B` into a differential
  graded algebra correspond bijectively to degree-one twisting cochains `Tᶜ(sA) → B`.
* `TauCeti.AInfinityAlgebra.cobarDGAlgHomEquiv`: the bar--cobar adjunction
  `DGAlgHom (Ω Tᶜ(sA)) B ≃ AInfinityHom A B`.
* `TauCeti.AInfinityAlgebra.toCobar`: the universal `A∞` morphism `A ⟶ Ω Tᶜ(sA)`.
* `TauCeti.AInfinityHom.cobarMap`: functoriality of `Ω Tᶜ(s-)` on `A∞` morphisms.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra_taylor_coalgHom`: evaluation of the Taylor map
  of a nonunital DG algebra on `coalgHom R f`.
* `TauCeti.AInfinityAlgebra.cobarDGAlgHomEquiv_eq_comp_toCobar` and
  `TauCeti.AInfinityAlgebra.eq_cobarDGAlgHomEquiv_symm_iff`: every `A∞` morphism `A ⟶ B` into a
  unital DG algebra factors uniquely through `toCobar` via a DG algebra morphism `Ω Tᶜ(sA) ⟶ B`.
* `TauCeti.AInfinityHom.cobarMap_comp_toCobar`: `toCobar` is natural with respect to `A∞`
  morphisms.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
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
  {ℬ : ℤ → Submodule R B} [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  {dB : B →ₗ[R] B}

namespace IsNonUnitalDGAlgebra

/-- On a single letter, the Taylor map of a nonunital DG algebra applies its differential. -/
theorem toAInfinityAlgebra_taylor_ofLetter (hB : IsNonUnitalDGAlgebra ℬ dB) (x : B) :
    hB.toAInfinityAlgebra.taylor (ReducedTensorWords.ofLetter R B x) = dB x := by
  rw [AInfinityAlgebra.taylor_ofLetter, hB.toAInfinityAlgebra_m_one_apply, Matrix.cons_val_zero]

/-- On a two-letter word, the Taylor map of a nonunital DG algebra multiplies the Koszul-twisted
first letter by the second. -/
theorem toAInfinityAlgebra_taylor_of_two (hB : IsNonUnitalDGAlgebra ℬ dB) (x y : B) :
    hB.toAInfinityAlgebra.taylor
        (ReducedTensorWords.of R B (2 : ℕ+) (PiTensorProduct.tprod R ![x, y])) =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 x * y := by
  rw [AInfinityAlgebra.taylor_of_two, hB.toAInfinityAlgebra_grading,
    hB.toAInfinityAlgebra_m_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero]

/-- On any word of length at least three obtained by prepending twice, the Taylor map of a
nonunital DG algebra vanishes because `m n = 0` for `n ≥ 3`. -/
theorem toAInfinityAlgebra_taylor_prepend_prepend (hB : IsNonUnitalDGAlgebra ℬ dB)
    (x y : B) (w : ReducedTensorWords R B) :
    hB.toAInfinityAlgebra.taylor
      (ReducedTensorWords.prepend R B x (ReducedTensorWords.prepend R B y w)) = 0 := by
  have h : (hB.toAInfinityAlgebra.taylor ∘ₗ ReducedTensorWords.prepend R B x ∘ₗ
      ReducedTensorWords.prepend R B y) = 0 := by
    refine ReducedTensorWords.linearMap_ext R B fun k z ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [ReducedTensorWords.prepend_of_tprod, ReducedTensorWords.prepend_of_tprod,
      AInfinityAlgebra.taylor_of_tprod,
      hB.toAInfinityAlgebra_m_of_three_le (by have := k.2; dsimp only; omega)]
    rfl
  exact LinearMap.congr_fun h w

/-- Evaluating the Taylor map of a nonunital DG algebra on the coalgebra extension `coalgHom R f`
keeps only the one-block differential term and the two-block deconcatenation product. -/
theorem toAInfinityAlgebra_taylor_coalgHom (hB : IsNonUnitalDGAlgebra ℬ dB)
    (f : ReducedTensorWords R A →ₗ[R] B) (w : ReducedTensorWords R A) :
    hB.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R f w) =
      dB (f w) + TensorProduct.lift (LinearMap.mul R B)
        (TensorProduct.map ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f) f
          (ReducedTensorWords.deconcatenation R A w)) := by
  let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
  have h : hB.toAInfinityAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R f =
      dB ∘ₗ f + TensorProduct.lift (LinearMap.mul R B) ∘ₗ
        TensorProduct.map (σB ∘ₗ f) f ∘ₗ ReducedTensorWords.deconcatenation R A := by
    refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply,
      ReducedTensorWords.of_tprod_eq_subword R n.2]
    rw [ReducedTensorWords.coalgHom_subword, map_add, hB.toAInfinityAlgebra_taylor_ofLetter,
      map_sum, ReducedTensorWords.map_deconcatenation_subword, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [ReducedTensorWords.coalgHom_subword, map_add, map_add, map_sum, map_sum]
    have htriple : ∑ c ∈ Finset.range (n.1 - d), hB.toAInfinityAlgebra.taylor
        (ReducedTensorWords.prepend R B (f (ReducedTensorWords.subword R x 0 d))
          (ReducedTensorWords.prepend R B (f (ReducedTensorWords.subword R x (0 + d) c))
            (ReducedTensorWords.coalgHom R f
              (ReducedTensorWords.subword R x (0 + d + c) (n.1 - d - c))))) = 0 :=
      Finset.sum_eq_zero fun _ _ ↦ hB.toAInfinityAlgebra_taylor_prepend_prepend _ _ _
    rw [htriple, add_zero, ReducedTensorWords.prepend_ofLetter,
      hB.toAInfinityAlgebra_taylor_of_two, TensorProduct.lift.tmul, LinearMap.mul_apply',
      LinearMap.comp_apply]
  exact LinearMap.congr_fun h w

end IsNonUnitalDGAlgebra

end NonUnital

section TwistingCochain

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B]
  [Ring C] [Algebra R C]
  {ℬ : ℤ → Submodule R B} [DirectSum.Decomposition ℬ] {dB : B →ₗ[R] B}
  {𝒞 : ℤ → Submodule R C} [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞] {dC : C →ₗ[R] C}

private theorem lift_mul_eq_mul' :
    TensorProduct.lift (LinearMap.mul R B) = LinearMap.mul' R B :=
  TensorProduct.ext' fun _ _ ↦ rfl

private theorem isHomogeneous_koszulTwist_of_one {G : InternalGrading R (ReducedTensorWords R A) ℤ}
    {f : ReducedTensorWords R A →ₗ[R] B} (hf : LinearMap.IsHomogeneous f G.piece ℬ 1) :
    LinearMap.IsHomogeneous ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f)
      G.piece ℬ 1 := by
  refine LinearMap.isHomogeneous_def.mpr fun p w hw ↦ ?_
  have hfw : f w ∈ (InternalGrading.ofDecomposition ℬ).piece (p + 1) := by
    rw [InternalGrading.ofDecomposition_piece]
    exact hf.map_mem hw
  simpa only [LinearMap.comp_apply, InternalGrading.ofDecomposition_piece] using
    (InternalGrading.ofDecomposition ℬ).koszulTwist_mem_piece hfw 1

variable [SetLike.GradedMul ℬ]

private theorem isHomogeneous_one_of_suspended {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (hB.toAInfinityAlgebra.grading.shift 1).piece 0) :
    LinearMap.IsHomogeneous f (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1 := by
  refine LinearMap.isHomogeneous_def.mpr fun p w hw ↦ ?_
  rw [ReducedTensorWords.grading_piece] at hw
  have hfw := hf.map_mem hw
  rwa [add_zero, hB.toAInfinityAlgebra_grading, InternalGrading.shift_piece,
    InternalGrading.ofDecomposition_piece] at hfw

private theorem isHomogeneous_suspended_of_one {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1) :
    LinearMap.IsHomogeneous f (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (hB.toAInfinityAlgebra.grading.shift 1).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun p w hw ↦ ?_
  rw [← ReducedTensorWords.grading_piece] at hw
  rw [add_zero, hB.toAInfinityAlgebra_grading, InternalGrading.shift_piece,
    InternalGrading.ofDecomposition_piece]
  exact hf.map_mem hw

/-- Key Koszul-sign identity relating the twisting-cochain left-hand side for
`τ = σ_B ∘ₗ f` to `-σ_B` applied to the `A∞` Taylor component defect of `f`. -/
private theorem twistingEquation_eq_neg_koszulTwist (𝒜 : AInfinityAlgebra R A)
    (hB : IsNonUnitalDGAlgebra ℬ dB) {f : ReducedTensorWords R A →ₗ[R] B}
    (hf : LinearMap.IsHomogeneous f
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1)
    (w : ReducedTensorWords R A) :
    let GA := ReducedTensorWords.grading (𝒜.grading.shift 1)
    let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
    let τ := σB ∘ₗ f
    dB (τ w) + τ (𝒜.barDifferential w) +
        LinearMap.mul' R B (TensorProduct.map (τ ∘ₗ GA.koszulTwist 1) τ
          (ReducedTensorWords.deconcatenation R A w)) =
      -σB (hB.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R f w) -
        f (𝒜.barDifferential w)) := by
  intro GA σB τ
  have hf' : LinearMap.IsHomogeneous f GA.piece
      (InternalGrading.ofDecomposition ℬ).piece 1 := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hτtwist : τ ∘ₗ GA.koszulTwist 1 = -f := by
    refine LinearMap.ext fun u ↦ ?_
    have hu := hf'.koszulTwist_apply 1 u
    simp only [mul_one, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one, neg_one_smul] at hu
    have hu' := congrArg (fun y ↦ -σB y) hu
    dsimp only [σB] at hu'
    simpa only [τ, σB, LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg,
      InternalGrading.koszulTwist_koszulTwist] using hu'.symm
  have hquad : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
      σB (LinearMap.mul' R B (TensorProduct.map τ f z)) =
        -LinearMap.mul' R B (TensorProduct.map (τ ∘ₗ GA.koszulTwist 1) τ z) := by
    rw [hτtwist]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.neg_apply,
        σB, τ, LinearMap.comp_apply, InternalGrading.koszulTwist_ofDecomposition_mul,
        InternalGrading.koszulTwist_koszulTwist, neg_mul, neg_neg]
    | add x y hx hy => simp only [map_add, neg_add, hx, hy]
  rw [hB.toAInfinityAlgebra_taylor_coalgHom, lift_mul_eq_mul', map_sub, map_add,
    hB.koszulTwist_map (f w), hquad]
  dsimp only [τ, σB, LinearMap.comp_apply]
  abel

/-- Composing the Taylor map of an `A∞` morphism into a DG algebra with the Koszul twist gives a
twisting cochain on the reduced bar coalgebra. -/
theorem AInfinityHom.isTwistingCochain {𝒜 : AInfinityAlgebra R A}
    {hB : IsNonUnitalDGAlgebra ℬ dB} (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB
      ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.taylor) where
  isHomogeneous := isHomogeneous_koszulTwist_of_one
    (isHomogeneous_one_of_suspended hB g.isHomogeneous_taylor)
  equation w := by
    rw [twistingEquation_eq_neg_koszulTwist 𝒜 hB
      (isHomogeneous_one_of_suspended hB g.isHomogeneous_taylor) w]
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
    (isHomogeneous_suspended_of_one hB (isHomogeneous_koszulTwist_of_one hτ.isHomogeneous))
    (LinearMap.ext fun w ↦ by
      let σB := (InternalGrading.ofDecomposition ℬ).koszulTwist 1
      let f := σB ∘ₗ τ
      have hf : LinearMap.IsHomogeneous f
          (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1 :=
        isHomogeneous_koszulTwist_of_one hτ.isHomogeneous
      have hσf : σB ∘ₗ f = τ := by
        dsimp only [f, σB]
        rw [← LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]
      have heq := twistingEquation_eq_neg_koszulTwist 𝒜 hB hf w
      dsimp only [σB] at heq
      rw [hσf, hτ.equation w] at heq
      have hzero := congrArg σB heq.symm
      rw [map_neg, InternalGrading.koszulTwist_koszulTwist, map_zero, neg_eq_zero,
        sub_eq_zero] at hzero
      exact hzero)

@[simp]
theorem IsTwistingCochain.taylor_toAInfinityHom {𝒜 : AInfinityAlgebra R A}
    (hB : IsNonUnitalDGAlgebra ℬ dB) {τ : ReducedTensorWords R A →ₗ[R] B}
    (hτ : IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ) :
    (hτ.toAInfinityHom hB).taylor = (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ τ := by
  rw [IsTwistingCochain.toAInfinityHom, AInfinityHom.taylor_ofTaylor]

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
    dsimp only
    rw [IsTwistingCochain.taylor_toAInfinityHom, ← LinearMap.comp_assoc,
      InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]
  right_inv τ := Subtype.ext <| by
    dsimp only
    rw [IsTwistingCochain.taylor_toAInfinityHom, ← LinearMap.comp_assoc,
      InternalGrading.koszulTwist_comp_self, LinearMap.id_comp]

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

/-- Naturality of `barTwistingCochainEquiv` in the source `A∞` algebra. -/
theorem barTwistingCochainEquiv_comp_right {𝒜 : AInfinityAlgebra R A}
    {𝒜' : AInfinityAlgebra R A'} (hB : IsNonUnitalDGAlgebra ℬ dB)
    (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) (k : AInfinityHom 𝒜' 𝒜) :
    (𝒜'.barTwistingCochainEquiv hB (g.comp k)).val =
      (𝒜.barTwistingCochainEquiv hB g).val ∘ₗ k.barMap := by
  rw [barTwistingCochainEquiv_apply, barTwistingCochainEquiv_apply, AInfinityHom.taylor_comp,
    LinearMap.comp_assoc]

/-- Naturality of `barTwistingCochainEquiv` in the target DG algebra. -/
theorem barTwistingCochainEquiv_comp_left (𝒜 : AInfinityAlgebra R A)
    {hB : IsNonUnitalDGAlgebra ℬ dB} {hC : IsNonUnitalDGAlgebra 𝒞 dC}
    (ψ : NonUnitalDGAlgHom hB hC) (g : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    (𝒜.barTwistingCochainEquiv hC (ψ.toAInfinityStrictHom.toAInfinityHom.comp g)).val =
      ψ.toAInfinityStrictHom.toLinearMap ∘ₗ (𝒜.barTwistingCochainEquiv hB g).val := by
  have hhom : LinearMap.IsHomogeneous ψ.toAInfinityStrictHom.toLinearMap
      (InternalGrading.ofDecomposition ℬ).piece
      (InternalGrading.ofDecomposition 𝒞).piece 0 := by
    have h := ψ.toAInfinityStrictHom.isHomogeneous
    rwa [hB.toAInfinityAlgebra_grading, hC.toAInfinityAlgebra_grading] at h
  refine LinearMap.ext fun w ↦ ?_
  have htw := hhom.koszulTwist_apply 1 (g.taylor w)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at htw
  simp only [barTwistingCochainEquiv_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    LinearMap.comp_apply, htw]

end AInfinityAlgebra

end TwistingCochain

section CobarAdjunction

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B]
  [Ring C] [Algebra R C]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra

/-- The **bar--cobar adjunction** between `A∞` algebras and unital differential graded algebras:
DG algebra morphisms `Ω Tᶜ(sA) ⟶ B` correspond bijectively to `A∞` morphisms `A ⟶ B`. -/
noncomputable def cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ≃
      AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hB).trans
    (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm

/-- The Taylor map of the `A∞` morphism associated to `φ : Ω Tᶜ(sA) ⟶ B` sends a bar word `w` to
`-σ_B (φ (ι w))`. -/
@[simp]
theorem taylor_cobarDGAlgHomEquiv (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB φ).taylor w =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (φ (ι R w)) := by
  simp [cobarDGAlgHomEquiv]

/-- The inverse of the bar--cobar adjunction sends a desuspended generator `ι w` to
`-σ_B (g.taylor w)`. -/
@[simp]
theorem cobarDGAlgHomEquiv_symm_apply_ι (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (w : ReducedTensorWords R A) :
    (𝒜.cobarDGAlgHomEquiv hB).symm g (ι R w) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (g.taylor w) := by
  simp [cobarDGAlgHomEquiv]

/-- Naturality of the bar--cobar adjunction in the target DG algebra. -/
@[simp]
theorem cobarDGAlgHomEquiv_comp (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
    (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarDGAlgHomEquiv hC (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (𝒜.cobarDGAlgHomEquiv hB φ) := by
  apply (𝒜.barTwistingCochainEquiv hC.toIsNonUnitalDGAlgebra).injective
  apply Subtype.ext
  rw [barTwistingCochainEquiv_comp_left]
  simp only [cobarDGAlgHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp]
  refine LinearMap.ext fun w ↦ ?_
  simp

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

/-- The Taylor map of `toCobar` sends each bar word `w` to the desuspended cobar generator of its
Koszul-twisted word `σ_{Tᶜ(sA)} w`. -/
theorem taylor_toCobar (𝒜 : AInfinityAlgebra R A) (w : ReducedTensorWords R A) :
    𝒜.toCobar.taylor w =
      ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 w) := by
  rw [toCobar, taylor_cobarDGAlgHomEquiv, DGAlgHom.id_apply, koszulTwist_tensorAlgebraPiece_ι,
    InternalGrading.koszulTwist_shift]
  simp

/-- **Universal property of `toCobar`**: the `A∞` morphism corresponding to a DG algebra morphism
`φ : Ω Tᶜ(sA) ⟶ B` is obtained by postcomposing `𝒜.toCobar` with `φ`. -/
theorem cobarDGAlgHomEquiv_eq_comp_toCobar (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarDGAlgHomEquiv hB φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobar := by
  have h := 𝒜.cobarDGAlgHomEquiv_comp φ (DGAlgHom.id _)
  rwa [DGAlgHom.comp_id, cobarDGAlgHomEquiv_id] at h

/-- **Universal factorization through `toCobar`**: a DG algebra morphism `φ : Ω Tᶜ(sA) ⟶ B` is the
bar--cobar transpose of `g : A ⟶ B` if and only if postcomposing `𝒜.toCobar` with `φ` recovers
`g`. -/
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
  rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
  exact k.isHomogeneous_barMap

/-- An `A∞` morphism `k : A ⟶ A'` induces a DG algebra morphism `Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA')` on cobar
constructions, sending each desuspended generator `ι w` to `ι (k.barMap w)`. -/
noncomputable def cobarMap {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar k.barMap
    k.isHomogeneous_barMap_grading
    (ReducedTensorWords.isCoalgHom_iff.1 k.isCoalgHom_barMap)
    k.barDifferential_comp_barMap

/-- On desuspended generators, `k.cobarMap` applies the bar coalgebra morphism `k.barMap`. -/
@[simp]
theorem cobarMap_ι {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜 𝒜') (w : ReducedTensorWords R A) :
    k.cobarMap (ι R w) = ι R (k.barMap w) :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap_ι _ _ _ _ _ w

/-- The identity `A∞` morphism induces the identity DG algebra morphism on `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun w ↦ by simp

/-- The cobar functor `Ω Tᶜ(s-)` preserves composition of `A∞` morphisms. -/
@[simp]
theorem cobarMap_comp {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    {𝒜'' : AInfinityAlgebra R A''} (k₂ : AInfinityHom 𝒜' 𝒜'') (k₁ : AInfinityHom 𝒜 𝒜') :
    (k₂.comp k₁).cobarMap = k₂.cobarMap.comp k₁.cobarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun w ↦ by simp

/-- Naturality of the bar--cobar adjunction in the source `A∞` algebra. -/
theorem cobarDGAlgHomEquiv_comp_cobarMap {𝒜 : AInfinityAlgebra R A}
    {𝒜' : AInfinityAlgebra R A'} (hB : IsDGAlgebra ℬ dB) (k : AInfinityHom 𝒜' 𝒜)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜'.cobarDGAlgHomEquiv hB (φ.comp k.cobarMap) =
      (𝒜.cobarDGAlgHomEquiv hB φ).comp k := by
  apply (𝒜'.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).injective
  apply Subtype.ext
  rw [AInfinityAlgebra.barTwistingCochainEquiv_comp_right]
  simp only [AInfinityAlgebra.cobarDGAlgHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    cobarMap, IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv_comp_cobarMap]

/-- Naturality of the universal `A∞` morphism `toCobar` with respect to `A∞` morphisms. -/
theorem cobarMap_comp_toCobar {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    (k : AInfinityHom 𝒜' 𝒜) :
    k.cobarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜'.toCobar =
      𝒜.toCobar.comp k := by
  rw [← AInfinityAlgebra.cobarDGAlgHomEquiv_eq_comp_toCobar
      (hB := 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential),
    ← DGAlgHom.id_comp k.cobarMap,
    cobarDGAlgHomEquiv_comp_cobarMap, AInfinityAlgebra.cobarDGAlgHomEquiv_id]

end AInfinityHom

end CobarAdjunction

end TauCeti
