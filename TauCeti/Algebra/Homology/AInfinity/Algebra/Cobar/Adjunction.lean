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
# Twisting cochains and the bar–cobar adjunction for `A∞` algebras

For an uncurved nonunital `A∞` algebra `A` and a nonunital differential graded algebra `B`, an
`A∞` morphism `f : A ⟶ B` is determined by its suspended Taylor map `f.taylor : Tᶜ(sA) → B`.
Because the higher operations of `B` vanish above arity two, the `A∞` morphism equation
`taylor_B ∘ coalgHom f = f ∘ b_A` collapses to a quadratic Maurer–Cartan equation on `Tᶜ(sA)`.
Precomposing with the total-degree Koszul involution `σ` of `Tᶜ(sA)` and negating identifies `A∞`
morphisms `A ⟶ B` bijectively with cohomological degree-one twisting cochains `Tᶜ(sA) → B`
(`TauCeti.AInfinityAlgebra.twistingCochainEquiv`).

When `B` is a unital differential graded algebra, combining `twistingCochainEquiv` with the cobar
universal property `IsNonCounitalDGCoalgebra.cobarTwistingCochainEquiv` yields the **bar–cobar
adjunction** (`TauCeti.AInfinityAlgebra.cobarHomEquiv`): DG algebra morphisms `Ω Tᶜ(sA) → B`
correspond bijectively to `A∞` morphisms `A ⟶ B`. The two minus signs in the twisting-cochain
correspondences cancel, so the universal `A∞` unit `cobarUnit : A ⟶ Ω Tᶜ(sA)` has suspended Taylor
map `ι ∘ σ`, and `cobarHomEquiv` acts simply by postcomposing `cobarUnit` with a DG algebra
morphism viewed as a strict `A∞` morphism.

Functoriality of the bar and cobar constructions upgrades `Ω Tᶜ(s-)` to a functor `cobarMap` from
`A∞` algebras (with all `A∞` morphisms) to DG algebras, and for a DG algebra `B` the counit
`IsDGAlgebra.cobarCounit : Ω Tᶜ(sB) → B` satisfies both triangle identities of the adjunction.

## Main definitions

* `TauCeti.AInfinityAlgebra.twistingCochainEquiv`: bijection between `A∞` morphisms `A ⟶ B` into a
  nonunital DG algebra and twisting cochains `Tᶜ(sA) → B`.
* `TauCeti.AInfinityAlgebra.cobarHomEquiv`: the bar–cobar adjunction `DGAlgHom (Ω Tᶜ(sA)) B ≃
  AInfinityHom A B`.
* `TauCeti.AInfinityAlgebra.cobarUnit`: the universal `A∞` morphism `A ⟶ Ω Tᶜ(sA)`.
* `TauCeti.AInfinityHom.cobarMap`: functoriality of `Ω Tᶜ(s-)` along arbitrary `A∞` morphisms.
* `TauCeti.IsDGAlgebra.cobarCounit`: the counit DG algebra morphism `Ω Tᶜ(sB) → B`.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra_taylor_apply`: explicit formula for the Taylor
  map of a nonunital DG algebra on any reduced tensor word.
* `TauCeti.AInfinityAlgebra.cobarHomEquiv_eq_comp_cobarUnit`: the adjunction bijection is
  postcomposition with `cobarUnit`.
* `TauCeti.IsDGAlgebra.toAInfinityHom_cobarCounit_comp_cobarUnit` and
  `TauCeti.AInfinityAlgebra.cobarCounit_comp_cobarMap_cobarUnit`: the two triangle identities of
  the bar–cobar adjunction.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 2.
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

/-- The suspended Taylor map of a nonunital DG algebra on any reduced tensor word picks out the
differential of its length-one part plus the signed product of the length-two cuts. -/
theorem IsNonUnitalDGAlgebra.toAInfinityAlgebra_taylor_apply
    (hB : IsNonUnitalDGAlgebra ℬ dB) (w : ReducedTensorWords R B) :
    hB.toAInfinityAlgebra.taylor w =
      dB (ReducedTensorWords.letter R B w) +
        LinearMap.mul' R B (TensorProduct.map
          ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ ReducedTensorWords.letter R B)
          (ReducedTensorWords.letter R B)
          (ReducedTensorWords.deconcatenation R B w)) := by
  let rhs : ReducedTensorWords R B →ₗ[R] B :=
    dB ∘ₗ ReducedTensorWords.letter R B +
      LinearMap.mul' R B ∘ₗ TensorProduct.map
        ((InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ ReducedTensorWords.letter R B)
        (ReducedTensorWords.letter R B) ∘ₗ ReducedTensorWords.deconcatenation R B
  suffices h : hB.toAInfinityAlgebra.taylor = rhs from LinearMap.congr_fun h w
  refine ReducedTensorWords.linearMap_ext R B fun n x ↦ ?_
  rcases n with ⟨_ | _ | _ | k, hk⟩
  · omega
  · rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.subword_one R B x Nat.one_pos]
    simp [rhs]
  · rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.subword_two_eq R x le_rfl]
    simp [rhs, AInfinityAlgebra.taylor_of_two, ReducedTensorWords.deconcatenation_of_two]
  · have hn3 : 3 ≤ k + 3 := by omega
    have hne1 : (⟨k + 3, hk⟩ : {n : ℕ // 0 < n}) ≠ 1 := by
      intro h
      have hval : k + 3 = 1 := by simpa using congrArg Subtype.val h
      omega
    have hlhs := LinearMap.congr_fun
      (hB.toAInfinityAlgebra.taylor_comp_of_eq_zero_of_m_eq_zero ⟨k + 3, hk⟩
        (hB.toAInfinityAlgebra_m_of_three_le hn3))
      (PiTensorProduct.tprod R x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hlhs
    rw [hlhs]
    symm
    simp only [rhs, LinearMap.add_apply, LinearMap.comp_apply,
      ReducedTensorWords.letter_of_of_ne_one R B hne1, map_zero, zero_add]
    rw [ReducedTensorWords.of_tprod_eq_subword R hk x,
      ReducedTensorWords.deconcatenation_subword, map_sum, map_sum]
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Finset.mem_Ioo] at hc
    rcases eq_or_ne c 1 with rfl | hc1
    · rw [TensorProduct.map_tmul,
        ReducedTensorWords.letter_subword_of_ne_one R B x (0 + 1) (by omega),
        TensorProduct.tmul_zero, map_zero]
    · rw [TensorProduct.map_tmul, LinearMap.comp_apply,
        ReducedTensorWords.letter_subword_of_ne_one R B x 0 hc1, map_zero,
        TensorProduct.zero_tmul, map_zero]

namespace AInfinityAlgebra

private theorem tensorProduct_map_neg_left {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f : M₁ →ₗ[R] N₁) (g : M₂ →ₗ[R] N₂) (z : M₁ ⊗[R] M₂) :
    TensorProduct.map (-f) g z = -TensorProduct.map f g z := by
  induction z using TensorProduct.inductionOn with
  | tmul u v => simp [TensorProduct.neg_tmul]
  | add u v hu hv => simp only [map_add, hu, hv, neg_add_rev]; abel

private theorem tensorProduct_map_neg_neg {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f : M₁ →ₗ[R] N₁) (g : M₂ →ₗ[R] N₂) (z : M₁ ⊗[R] M₂) :
    TensorProduct.map (-f) (-g) z = TensorProduct.map f g z := by
  induction z using TensorProduct.inductionOn with
  | tmul u v => simp [TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  | add u v hu hv => simp only [map_add, hu, hv]

variable (𝒜 : AInfinityAlgebra R A) (hB : IsNonUnitalDGAlgebra ℬ dB)

include hB in
/-- A linear map out of `Tᶜ(sA)` has degree zero into the shifted grading of `B` if and only if it
has degree one into `ℬ`. -/
theorem isHomogeneous_taylor_toAInfinityAlgebra_iff (f : ReducedTensorWords R A →ₗ[R] B) :
    LinearMap.IsHomogeneous f (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
        (hB.toAInfinityAlgebra.grading.shift 1).piece 0 ↔
      LinearMap.IsHomogeneous f (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1 := by
  simp only [LinearMap.isHomogeneous_def, hB.toAInfinityAlgebra_grading,
    InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece, add_zero,
    ReducedTensorWords.grading_piece]

private theorem taylor_coalgHom_eq (f : ReducedTensorWords R A →ₗ[R] B)
    (hf : LinearMap.IsHomogeneous f (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1)
    (z : ReducedTensorWords R A) :
    hB.toAInfinityAlgebra.taylor (ReducedTensorWords.coalgHom R f z) =
      dB (f z) - LinearMap.mul' R B (TensorProduct.map
        (f ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) f
        (ReducedTensorWords.deconcatenation R A z)) := by
  have hf' : LinearMap.IsHomogeneous f
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece
      (InternalGrading.ofDecomposition ℬ).piece 1 := by
    rwa [InternalGrading.ofDecomposition_piece]
  have htwist : (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ f =
      -(f ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) := by
    simpa using hf'.koszulTwist_comp_eq_smul 1
  rw [hB.toAInfinityAlgebra_taylor_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) (ReducedTensorWords.coalgHom R f),
    ReducedTensorWords.letter_comp_coalgHom,
    (ReducedTensorWords.isCoalgHom_coalgHom f).deconcatenation_apply,
    ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
    ← TensorProduct.map_comp, LinearMap.comp_assoc, ReducedTensorWords.letter_comp_coalgHom,
    htwist, tensorProduct_map_neg_left, map_neg, sub_eq_add_neg]

/-- Negating the Koszul-twisted Taylor map of an `A∞` morphism into a nonunital DG algebra gives a
twisting cochain on the reduced bar coalgebra. -/
theorem isTwistingCochain_of_aInfinityHom (f : AInfinityHom 𝒜 hB.toAInfinityAlgebra) :
    IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB
      (-(f.taylor ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)) where
  isHomogeneous := by
    have hf := (𝒜.isHomogeneous_taylor_toAInfinityAlgebra_iff hB f.taylor).mp f.isHomogeneous_taylor
    refine (LinearMap.isHomogeneous_def.mpr fun p c hc ↦ ?_).neg
    exact hf.map_mem (InternalGrading.koszulTwist_mem_piece _ hc 1)
  equation c := by
    let G := ReducedTensorWords.grading (𝒜.grading.shift 1)
    have hf := (𝒜.isHomogeneous_taylor_toAInfinityAlgebra_iff hB f.taylor).mp f.isHomogeneous_taylor
    have hcomp := LinearMap.congr_fun f.taylor_comp_barMap (G.koszulTwist 1 c)
    rw [f.barMap_eq_coalgHom, LinearMap.comp_apply, LinearMap.comp_apply,
      𝒜.taylor_coalgHom_eq hB f.taylor hf] at hcomp
    have hd : f.taylor (G.koszulTwist 1 (𝒜.barDifferential c)) =
        -f.taylor (𝒜.barDifferential (G.koszulTwist 1 c)) := by
      rw [𝒜.isNonCounitalDGCoalgebra_bar.koszulTwist_differential, map_neg]
    have hΔ : TensorProduct.map
        ((-(f.taylor ∘ₗ G.koszulTwist 1)) ∘ₗ G.koszulTwist 1)
        (-(f.taylor ∘ₗ G.koszulTwist 1))
        (ReducedTensorWords.deconcatenation R A c) =
        TensorProduct.map (f.taylor ∘ₗ G.koszulTwist 1) f.taylor
          (ReducedTensorWords.deconcatenation R A (G.koszulTwist 1 c)) := by
      rw [𝒜.isNonCounitalDGCoalgebra_bar.comul_koszulTwist,
        ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
        ← TensorProduct.map_comp]
      simp only [G, LinearMap.neg_comp, LinearMap.comp_assoc, InternalGrading.koszulTwist_comp_self,
        LinearMap.comp_id]
      exact tensorProduct_map_neg_neg _ _ _
    rw [hΔ]
    simp only [G, LinearMap.neg_apply, LinearMap.comp_apply, map_neg] at hd ⊢
    rw [hd, neg_neg]
    grind

/-- Building an `A∞` morphism `A ⟶ B` into a nonunital DG algebra from a twisting cochain
`τ : Tᶜ(sA) → B`. -/
noncomputable def aInfinityHomOfTwistingCochain (τ : ReducedTensorWords R A →ₗ[R] B)
    (hτ : IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ) :
    AInfinityHom 𝒜 hB.toAInfinityAlgebra :=
  have hf : LinearMap.IsHomogeneous
      (-(τ ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1))
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece ℬ 1 :=
    (LinearMap.isHomogeneous_def
      (f := τ ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1)).mpr
      (fun _ _ hc ↦ hτ.isHomogeneous.map_mem
        ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist_mem_piece hc 1)) |>.neg
  AInfinityHom.ofTaylor
    (-(τ ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1))
    ((𝒜.isHomogeneous_taylor_toAInfinityAlgebra_iff hB _).mpr hf) <|
    LinearMap.ext fun z ↦ by
      let G := ReducedTensorWords.grading (𝒜.grading.shift 1)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, 𝒜.taylor_coalgHom_eq hB _ hf z]
      have heq := hτ.equation (G.koszulTwist 1 z)
      have hd : τ (𝒜.barDifferential (G.koszulTwist 1 z)) =
          -τ (G.koszulTwist 1 (𝒜.barDifferential z)) := by
        rw [𝒜.isNonCounitalDGCoalgebra_bar.koszulTwist_differential, map_neg, neg_neg]
      have hΔ : TensorProduct.map
          ((-(τ ∘ₗ G.koszulTwist 1)) ∘ₗ G.koszulTwist 1)
          (-(τ ∘ₗ G.koszulTwist 1))
          (ReducedTensorWords.deconcatenation R A z) =
          TensorProduct.map (τ ∘ₗ G.koszulTwist 1) τ
            (ReducedTensorWords.deconcatenation R A (G.koszulTwist 1 z)) := by
        rw [𝒜.isNonCounitalDGCoalgebra_bar.comul_koszulTwist,
          ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
          ← TensorProduct.map_comp]
        simp only [G, LinearMap.neg_comp, LinearMap.comp_assoc,
          InternalGrading.koszulTwist_comp_self, LinearMap.comp_id]
        exact tensorProduct_map_neg_neg _ _ _
      rw [hΔ]
      rw [hd] at heq
      simp only [G, LinearMap.neg_apply, LinearMap.comp_apply, map_neg] at heq ⊢
      grind

/-- The **twisting-cochain representation of `A∞` morphisms** into a nonunital DG algebra: `A∞`
morphisms `A ⟶ B` correspond bijectively to degree-one twisting cochains `Tᶜ(sA) → B`. -/
noncomputable def twistingCochainEquiv :
    AInfinityHom 𝒜 hB.toAInfinityAlgebra ≃
      {τ : ReducedTensorWords R A →ₗ[R] B //
        IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
          (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ} where
  toFun f := ⟨-(f.taylor ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1),
    𝒜.isTwistingCochain_of_aInfinityHom hB f⟩
  invFun τ := 𝒜.aInfinityHomOfTwistingCochain hB τ.val τ.property
  left_inv f := AInfinityHom.ext <| LinearMap.ext fun z ↦ by
    simp [aInfinityHomOfTwistingCochain]
  right_inv τ := Subtype.ext <| LinearMap.ext fun z ↦ by
    simp [aInfinityHomOfTwistingCochain]

/-- Under `twistingCochainEquiv`, an `A∞` morphism `f : A ⟶ B` maps to `-f.taylor ∘ σ`. -/
@[simp]
theorem twistingCochainEquiv_apply (f : AInfinityHom 𝒜 hB.toAInfinityAlgebra)
    (z : ReducedTensorWords R A) :
    (𝒜.twistingCochainEquiv hB f).val z =
      -f.taylor ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) := (rfl)

/-- The Taylor map of `(twistingCochainEquiv hB).symm τ` is `-τ ∘ σ`. -/
@[simp]
theorem taylor_twistingCochainEquiv_symm_apply
    (τ : {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ}) :
    ((𝒜.twistingCochainEquiv hB).symm τ).taylor =
      -(τ.val ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) := by
  simp [twistingCochainEquiv, aInfinityHomOfTwistingCochain]

end AInfinityAlgebra

end NonUnital

section Unital

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A'] [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra

variable (𝒜 : AInfinityAlgebra R A) (hB : IsDGAlgebra ℬ dB)

/-- The **bar–cobar adjunction** between `A∞` algebras and differential graded algebras: DG algebra
morphisms `Ω Tᶜ(sA) → B` correspond bijectively to `A∞` morphisms `A ⟶ B`. -/
noncomputable def cobarHomEquiv :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ≃
      AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  (𝒜.isNonCounitalDGCoalgebra_bar.cobarTwistingCochainEquiv hB).trans
    (𝒜.twistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm

/-- The Taylor map of `cobarHomEquiv φ` restricts `φ` to desuspended generators after the
total-degree Koszul involution `σ` of `Tᶜ(sA)`. -/
@[simp]
theorem taylor_cobarHomEquiv
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (𝒜.cobarHomEquiv hB φ).taylor =
      (φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] B) ∘ₗ ι R ∘ₗ
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 :=
  LinearMap.ext fun z ↦ by simp [cobarHomEquiv]

/-- The DG algebra lift `(cobarHomEquiv).symm f : Ω Tᶜ(sA) → B` evaluates on a desuspended
generator `s⁻¹ z` to `f.taylor (σ z)`. -/
@[simp]
theorem cobarHomEquiv_symm_apply_ι
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (z : ReducedTensorWords R A) :
    (𝒜.cobarHomEquiv hB).symm f (ι R z) =
      f.taylor ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) := by
  simp [cobarHomEquiv]

/-- The **adjunction unit** `A ⟶ Ω Tᶜ(sA)`: the universal `A∞` morphism from `A` into the cobar
construction of its reduced bar coalgebra. -/
noncomputable def cobarUnit :
    AInfinityHom 𝒜
      (𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential.toIsNonUnitalDGAlgebra
        ).toAInfinityAlgebra :=
  𝒜.cobarHomEquiv 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
    (DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential)

/-- The suspended Taylor map of `cobarUnit` embeds words as desuspended generators after the
total-degree Koszul twist `σ`. -/
@[simp]
theorem taylor_cobarUnit :
    𝒜.cobarUnit.taylor =
      ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 :=
  LinearMap.ext fun z ↦ by simp [cobarUnit]

/-- On a single letter `a`, the linear part of `cobarUnit` is the generator `s⁻¹ [s a]` twisted by
the shifted Koszul sign `(-1)^(|a| - 1)`. -/
theorem linearPart_cobarUnit_apply (a : A) :
    𝒜.cobarUnit.linearPart a =
      ι R (ReducedTensorWords.ofLetter R A ((𝒜.grading.shift 1).koszulTwist 1 a)) := by
  rw [AInfinityHom.linearPart_apply, taylor_cobarUnit, LinearMap.comp_apply,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

/-- Under `cobarHomEquiv`, a DG algebra morphism `φ : Ω Tᶜ(sA) → B` corresponds to postcomposing
the universal `A∞` morphism `cobarUnit` with `φ` viewed as a strict `A∞` morphism. -/
theorem cobarHomEquiv_eq_comp_cobarUnit
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarHomEquiv hB φ =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.cobarUnit := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  exact LinearMap.ext fun z ↦ by simp

/-- Every `A∞` morphism `f : A ⟶ B` into a DG algebra factors through `cobarUnit` via its unique
DG algebra extension `(cobarHomEquiv).symm f`. -/
@[simp]
theorem toAInfinityHom_cobarHomEquiv_symm_comp_cobarUnit
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    ((𝒜.cobarHomEquiv hB).symm f).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        𝒜.cobarUnit = f := by
  rw [← 𝒜.cobarHomEquiv_eq_comp_cobarUnit hB, Equiv.apply_symm_apply]

/-- **Universal property of `Ω Tᶜ(sA)`**: a DG algebra morphism `φ : Ω Tᶜ(sA) → B` is the cobar
extension of `f : A ⟶ B` if and only if postcomposing `cobarUnit` with `φ` recovers `f`. -/
theorem eq_cobarHomEquiv_symm_iff
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = (𝒜.cobarHomEquiv hB).symm f ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.cobarUnit = f := by
  rw [← 𝒜.cobarHomEquiv_eq_comp_cobarUnit hB, Equiv.eq_symm_apply]

/-- Target naturality of `cobarHomEquiv`: postcomposing a DG algebra morphism out of `Ω Tᶜ(sA)`
with `ψ : B → C` postcomposes the corresponding `A∞` morphism with `ψ`. -/
@[simp]
theorem cobarHomEquiv_comp {hC : IsDGAlgebra 𝒞 dC} (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    𝒜.cobarHomEquiv hC (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp (𝒜.cobarHomEquiv hB φ) := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  exact LinearMap.ext fun z ↦ by simp

end AInfinityAlgebra

namespace AInfinityHom

variable {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} {𝒜'' : AInfinityAlgebra R A''}

/-- Functoriality of `Ω Tᶜ(s-)`: any `A∞` morphism `g : A ⟶ A'` induces a strict DG algebra
morphism `Ω Tᶜ(sA) → Ω Tᶜ(sA')` via its bar coalgebra morphism `g.barMap`. -/
noncomputable def cobarMap (g : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar g.barMap
    (by
      rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
      exact g.isHomogeneous_barMap)
    (ReducedTensorWords.isCoalgHom_iff.mp g.isCoalgHom_barMap)
    g.barDifferential_comp_barMap

/-- On a desuspended generator `s⁻¹ z`, `g.cobarMap` applies `g.barMap`. -/
@[simp]
theorem cobarMap_ι (g : AInfinityHom 𝒜 𝒜') (z : ReducedTensorWords R A) :
    g.cobarMap (ι R z) = ι R (g.barMap z) := by
  simp [cobarMap]

/-- The identity `A∞` morphism induces the identity DG algebra morphism on `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  apply 𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext
    𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
  intro z
  simp

/-- Passing to cobar DG algebras preserves composition of `A∞` morphisms. -/
@[simp]
theorem cobarMap_comp (g' : AInfinityHom 𝒜' 𝒜'') (g : AInfinityHom 𝒜 𝒜') :
    (g'.comp g).cobarMap = g'.cobarMap.comp g.cobarMap := by
  apply 𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext
    𝒜''.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
  intro z
  simp

/-- Naturality of the adjunction unit `cobarUnit` with respect to arbitrary `A∞` morphisms. -/
@[simp]
theorem toAInfinityHom_cobarMap_comp_cobarUnit (g : AInfinityHom 𝒜 𝒜') :
    g.cobarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.cobarUnit =
      𝒜'.cobarUnit.comp g := by
  have hg : LinearMap.IsHomogeneous g.barMap
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece
      (ReducedTensorWords.grading (𝒜'.grading.shift 1)).piece 0 := by
    rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
    exact g.isHomogeneous_barMap
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  refine LinearMap.ext fun z ↦ ?_
  have htwist := hg.koszulTwist_apply 1 z
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at htwist
  simp [htwist]

/-- Source naturality of `cobarHomEquiv`: precomposing `φ : Ω Tᶜ(sA') → B` with `g.cobarMap`
precomposes the corresponding `A∞` morphism with `g`. -/
theorem cobarHomEquiv_comp_cobarMap (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (g : AInfinityHom 𝒜 𝒜') :
    𝒜.cobarHomEquiv hB (φ.comp g.cobarMap) = (𝒜'.cobarHomEquiv hB φ).comp g := by
  rw [𝒜.cobarHomEquiv_comp _ φ g.cobarMap, 𝒜.cobarHomEquiv_eq_comp_cobarUnit _ g.cobarMap,
    toAInfinityHom_cobarMap_comp_cobarUnit, ← AInfinityHom.comp_assoc,
    ← 𝒜'.cobarHomEquiv_eq_comp_cobarUnit hB φ]

end AInfinityHom

namespace IsDGAlgebra

/-- The **adjunction counit** `Ω Tᶜ(sB) → B` for a differential graded algebra `B`: the unique DG
algebra morphism corresponding under `cobarHomEquiv` to the identity `A∞` morphism of `B`. -/
noncomputable def cobarCounit (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom
      (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.isNonCounitalDGCoalgebra_bar
        ).isDGAlgebra_cobarDifferential
      hB :=
  (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarHomEquiv hB).symm
    (AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)

/-- On a desuspended generator `s⁻¹ z`, `cobarCounit` projects onto the single-letter component
after the Koszul involution, vanishing on all words of length at least two. -/
@[simp]
theorem cobarCounit_ι (hB : IsDGAlgebra ℬ dB) (z : ReducedTensorWords R B) :
    hB.cobarCounit (ι R z) =
      ReducedTensorWords.letter R B
        ((ReducedTensorWords.grading
          (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.shift 1)).koszulTwist 1 z) := by
  simp [cobarCounit]

/-- First triangle identity of the bar–cobar adjunction: for a DG algebra `B`, `cobarCounit`
followed by `cobarUnit` is the identity `A∞` morphism of `B`. -/
@[simp]
theorem toAInfinityHom_cobarCounit_comp_cobarUnit (hB : IsDGAlgebra ℬ dB) :
    hB.cobarCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarUnit =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toAInfinityHom_cobarHomEquiv_symm_comp_cobarUnit hB
    (AInfinityHom.id _)

end IsDGAlgebra

namespace AInfinityAlgebra

/-- Second triangle identity of the bar–cobar adjunction: for an `A∞` algebra `A`, applying
`cobarMap` to `cobarUnit` and composing with the counit of `Ω Tᶜ(sA)` gives the identity DG algebra
morphism of `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarCounit_comp_cobarMap_cobarUnit (𝒜 : AInfinityAlgebra R A) :
    𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential.cobarCounit.comp
        𝒜.cobarUnit.cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  let hΩ := 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
  apply (𝒜.cobarHomEquiv hΩ).injective
  rw [AInfinityHom.cobarHomEquiv_comp_cobarMap, IsDGAlgebra.cobarCounit, Equiv.apply_symm_apply,
    AInfinityHom.id_comp, cobarUnit]

end AInfinityAlgebra

end Unital

end TauCeti
