/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.Adjunction
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.Augmentation

/-!
# The universal enveloping differential graded algebra of an augmented `A∞` algebra

For an augmented uncurved `A∞` algebra `(A, ε_A)`, the reduced bar construction of its reduced
augmentation ideal `Ī = ker ε_A` is the reduced bar coalgebra `B∞ A = Tᶜ(sĪ)`. Applying the cobar
construction produces the **universal enveloping differential graded algebra**

`U(A) = Ω B∞ A = T(s⁻¹ Tᶜ(s(ker ε_A)))`,

equipped with its canonical cobar augmentation `envelopingAugmentation : U(A) → R` annihilating all
desuspended generators (`TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`).

Combining three equivalences —
1. the augmented cobar universal property (`IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff`
   together with `AInfinityAlgebra.cobarHomEquiv`),
2. factorization of `A∞` morphisms valued in `ker e_B` through the reduced augmentation ideal, and
3. the splitting equivalence `AInfinityAlgebra.Augmentation.augmentedHomEquiv` between strictly
   unital augmented `A∞` morphisms and reduced `A∞` morphisms —
yields the **augmented bar–cobar adjunction**
(`TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv`): augmented DG algebra morphisms
`(U(A), ε_{U(A)}) → (B, e_B)` correspond bijectively to strictly unital augmented `A∞` morphisms
`(A, ε_A) ⟶ (B, e_B)`.

Functoriality along augmented `A∞` morphisms (`TauCeti.AInfinityHom.IsAugmented.envelopingMap`), the
universal augmented `A∞` unit `envelopingUnit : A ⟶ U(A)`, the augmented DG counit
`envelopingCounit : U(B) → B`, and both triangle identities of the adjunction follow directly from
this factorization.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`: the DG algebra structure on
  `U(A) = Ω B∞ A`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: the canonical augmentation
  `U(A) → R`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv`: the augmented bar–cobar adjunction
  between augmented DG algebra morphisms `(U(A), ε_{U(A)}) → (B, e_B)` and strictly unital
  augmented `A∞` morphisms `(A, ε_A) ⟶ (B, e_B)`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingUnit`: the universal augmented `A∞` morphism
  `A ⟶ U(A)`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap`: functoriality of `U(-)` along strictly unital
  augmented `A∞` morphisms.
* `TauCeti.DGAlgAugmentation.envelopingCounit`: the counit augmented DG algebra morphism
  `U(B) → B`.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv_eq_comp_envelopingUnit`: the augmented
  adjunction bijection acts by postcomposing `envelopingUnit` with an augmented DG algebra morphism.
* `TauCeti.DGAlgAugmentation.toAInfinityHom_envelopingCounit_comp_envelopingUnit` and
  `TauCeti.AInfinityAlgebra.Augmentation.envelopingCounit_comp_envelopingMap_envelopingUnit`: the
  two triangle identities of the augmented bar–cobar adjunction.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 2.
-/

public section

open scoped DirectSum TensorProduct
open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uA uA' uA'' uB uC

section Helpers

variable {R : Type uR} {M : Type uA} {N : Type uA'} {B : Type uB} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup B] [Module R B]

private noncomputable def toReducedHom (II : AInfinityAlgebra R M) {BB : AInfinityAlgebra R B}
    (εB : BB.Augmentation) (f : AInfinityHom II BB)
    (hf : ∀ z, f.taylor z ∈ εB.augmentationIdeal) :
    AInfinityHom II εB.reducedAlgebra :=
  let t := εB.reducedPart ∘ₗ f.taylor
  have hπ : LinearMap.IsHomogeneous εB.reducedPart
      (BB.grading.shift 1).piece (εB.reducedAlgebra.grading.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.mpr εB.isHomogeneous_reducedPart
  have ht_hom : LinearMap.IsHomogeneous t
      (ReducedTensorWords.gradedPiece (II.grading.shift 1))
      (εB.reducedAlgebra.grading.shift 1).piece 0 := by
    simpa only [add_zero] using hπ.comp f.isHomogeneous_taylor
  AInfinityHom.ofTaylor t ht_hom <| by
    have hsub : εB.augmentationIdeal.subtype ∘ₗ t = f.taylor :=
      LinearMap.ext fun z ↦ by
        simp [t, εB.coe_reducedPart, (εB.mem_augmentationIdeal).mp (hf z)]
    have hcoalg :
        ReducedTensorWords.map (R := R) εB.augmentationIdeal.subtype ∘ₗ
          ReducedTensorWords.coalgHom R t = f.barMap := by
      rw [ReducedTensorWords.map_comp_coalgHom, hsub, ← f.barMap_eq_coalgHom]
    have hinc := εB.inclusionStrictHom.taylor_comp_barMap
    rw [AInfinityStrictHom.barMap_def,
      AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap] at hinc
    refine LinearMap.ext fun z ↦ Subtype.ext ?_
    have h1 := LinearMap.congr_fun (congrArg (· ∘ₗ ReducedTensorWords.coalgHom R t) hinc.symm) z
    have h2 := LinearMap.congr_fun (congrArg (· ∘ₗ II.barDifferential) hsub) z
    simp only [t, LinearMap.comp_apply, Submodule.subtype_apply] at h1 h2 ⊢
    rw [h1, ← LinearMap.comp_apply (ReducedTensorWords.map _ _), hcoalg,
      ← LinearMap.comp_apply BB.taylor, f.taylor_comp_barMap, LinearMap.comp_apply]
    exact h2.symm

private theorem taylor_toReducedHom (II : AInfinityAlgebra R M) {BB : AInfinityAlgebra R B}
    (εB : BB.Augmentation) (f : AInfinityHom II BB)
    (hf : ∀ z, f.taylor z ∈ εB.augmentationIdeal) :
    (toReducedHom II εB f hf).taylor = εB.reducedPart ∘ₗ f.taylor := by
  simp [toReducedHom]

private noncomputable def homToReducedEquiv (II : AInfinityAlgebra R M) {BB : AInfinityAlgebra R B}
    (εB : BB.Augmentation) :
    {f : AInfinityHom II BB // ∀ z, f.taylor z ∈ εB.augmentationIdeal} ≃
      AInfinityHom II εB.reducedAlgebra where
  toFun f := toReducedHom II εB f.1 f.2
  invFun g :=
    ⟨εB.inclusionStrictHom.toAInfinityHom.comp g, fun z ↦ by
      rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, LinearMap.comp_apply,
        AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap]
      exact (g.taylor z).2⟩
  left_inv f := Subtype.ext <| AInfinityHom.ext <| by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_toReducedHom]
    refine LinearMap.ext fun z ↦ ?_
    simp [εB.coe_reducedPart, (εB.mem_augmentationIdeal).mp (f.2 z)]
  right_inv g := AInfinityHom.ext <| by
    rw [taylor_toReducedHom, AInfinityStrictHom.taylor_toAInfinityHom_comp]
    refine LinearMap.ext fun z ↦ ?_
    simp

private theorem homToReducedEquiv_comp (II : AInfinityAlgebra R M) (JJ : AInfinityAlgebra R N)
    {BB : AInfinityAlgebra R B} (εB : BB.Augmentation)
    (f : {f : AInfinityHom JJ BB // ∀ z, f.taylor z ∈ εB.augmentationIdeal})
    (h : AInfinityHom II JJ) :
    homToReducedEquiv II εB ⟨f.1.comp h, fun z ↦ by rw [AInfinityHom.taylor_comp]; exact f.2 _⟩ =
      (homToReducedEquiv JJ εB f).comp h := by
  apply AInfinityHom.ext
  simp only [homToReducedEquiv, Equiv.coe_fn_mk]
  rw [taylor_toReducedHom, AInfinityHom.taylor_comp, AInfinityHom.taylor_comp,
    taylor_toReducedHom, LinearMap.comp_assoc]

private theorem koszulTwist_barMap {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {AA : AInfinityAlgebra R M₁} {BB : AInfinityAlgebra R M₂}
    (f : AInfinityHom AA BB) (z : ReducedTensorWords R M₁) :
    (ReducedTensorWords.grading (BB.grading.shift 1)).koszulTwist 1 (f.barMap z) =
      f.barMap ((ReducedTensorWords.grading (AA.grading.shift 1)).koszulTwist 1 z) := by
  have hf : LinearMap.IsHomogeneous f.barMap
      (ReducedTensorWords.grading (AA.grading.shift 1)).piece
      (ReducedTensorWords.grading (BB.grading.shift 1)).piece 0 := by
    rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
    exact f.isHomogeneous_barMap
  simpa using hf.koszulTwist_apply 1 z

private theorem letter_barMap {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {AA : AInfinityAlgebra R M₁} {BB : AInfinityAlgebra R M₂}
    (f : AInfinityHom AA BB) (z : ReducedTensorWords R M₁) :
    ReducedTensorWords.letter R M₂ (f.barMap z) = f.taylor z := by
  rw [f.taylor_def, LinearMap.comp_apply]

end Helpers

section Enveloping

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
  {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A'] [AddCommGroup A''] [Module R A'']
  [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} (ε : 𝒜.Augmentation)

/-- **The universal enveloping differential graded algebra** `U(A) = Ω B∞ A` of an augmented `A∞`
algebra `(A, ε)`: the cobar construction of the reduced bar coalgebra `B∞ A = Tᶜ(s(ker ε))` on the
reduced augmentation ideal. -/
theorem isDGAlgebra_enveloping :
    IsDGAlgebra
      (tensorAlgebraPiece
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1)))
      (cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
        (ReducedTensorWords.deconcatenation R ε.augmentationIdeal)
        ε.reducedAlgebra.barDifferential) :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- The canonical DG algebra augmentation `U(A) → R` of the universal enveloping DG algebra,
annihilating all desuspended generators. -/
noncomputable def envelopingAugmentation : DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- The canonical augmentation of `U(A)` kills every desuspended generator. -/
@[simp]
theorem envelopingAugmentation_ι (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (ι R z) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι z

private noncomputable def cobarAugmentedToHomEquiv {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom ε.reducedAlgebra hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        ∀ z, f.taylor z ∈ eB.toAInfinityAugmentation.augmentationIdeal} where
  toFun φ :=
    ⟨ε.reducedAlgebra.cobarHomEquiv hB φ.1, fun z ↦ by
      have hφ := (ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff
        eB φ.1).mp φ.2
      rw [eB.toAInfinityAugmentation.mem_augmentationIdeal, taylor_cobarHomEquiv]
      simpa using (eB.mem_augmentationIdeal).mp (hφ _)⟩
  invFun f :=
    ⟨(ε.reducedAlgebra.cobarHomEquiv hB).symm f.1, by
      rw [envelopingAugmentation,
        ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eB]
      intro z
      rw [eB.mem_augmentationIdeal, cobarHomEquiv_symm_apply_ι]
      simpa using (eB.toAInfinityAugmentation.mem_augmentationIdeal).mp (f.2 _)⟩
  left_inv φ := Subtype.ext ((ε.reducedAlgebra.cobarHomEquiv hB).symm_apply_apply φ.1)
  right_inv f := Subtype.ext ((ε.reducedAlgebra.cobarHomEquiv hB).apply_symm_apply f.1)

/-- **The augmented bar–cobar adjunction**: augmented DG algebra morphisms
`(U(A), ε_{U(A)}) → (B, e_B)` correspond bijectively to strictly unital augmented `A∞` morphisms
`(A, ε_A) ⟶ (B, e_B)`. -/
noncomputable def envelopingHomEquiv {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsAugmented ε eB.toAInfinityAugmentation} :=
  (ε.cobarAugmentedToHomEquiv eB).trans <|
    (homToReducedEquiv ε.reducedAlgebra eB.toAInfinityAugmentation).trans
      (ε.augmentedHomEquiv eB.toAInfinityAugmentation).symm

/-- The Taylor map of `envelopingHomEquiv eB φ` sends single-letter scalars via `algebraMap R B`
and reduced words via `φ ∘ ι ∘ σ` on the reduced-part projection. -/
@[simp]
theorem taylor_envelopingHomEquiv {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation})
    (w : ReducedTensorWords R A) :
    ((ε.envelopingHomEquiv eB φ).1).taylor w =
      algebraMap R B (ε (ReducedTensorWords.letter R A w)) +
        φ.1 (ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (ReducedTensorWords.map (R := R) ε.reducedPart w))) := by
  have hφ := (ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff
    eB φ.1).mp φ.2
  have h0 : eB (φ.1 (ι R ((ReducedTensorWords.grading
      (ε.reducedGrading.shift 1)).koszulTwist 1
        (ReducedTensorWords.map (R := R) ε.reducedPart w)))) = 0 :=
    (eB.mem_augmentationIdeal).mp (hφ _)
  simp [envelopingHomEquiv, cobarAugmentedToHomEquiv, homToReducedEquiv, taylor_toReducedHom,
    Algebra.algebraMap_eq_smul_one, h0]

/-- The augmented DG algebra lift `(envelopingHomEquiv eB).symm f` evaluates on a desuspended
generator `s⁻¹ z` to `f.taylor` applied to the included and Koszul-twisted reduced word `σ z`. -/
@[simp]
theorem envelopingHomEquiv_symm_apply_ι {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation})
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ((ε.envelopingHomEquiv eB).symm f).1 (ι R z) =
      f.1.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 z)) := by
  let u := (ReducedTensorWords.grading (ε.reducedGrading.shift 1)).koszulTwist 1 z
  have hlet := LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map ε.augmentationIdeal.subtype) u
  have hz := LinearMap.congr_fun f.2.comp_taylor
    (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u)
  simp only [LinearMap.comp_apply, DGAlgAugmentation.toAInfinityAugmentation_apply] at hlet hz
  rw [hlet] at hz
  have h0 : ε (ReducedTensorWords.letter R ε.augmentationIdeal u : A) = 0 :=
    (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R ε.augmentationIdeal u).2
  have heB : eB (f.1.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u)) = 0 :=
    hz.trans h0
  dsimp only [u] at heB
  rw [envelopingHomEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  simp only [cobarAugmentedToHomEquiv, homToReducedEquiv, Equiv.coe_fn_symm_mk]
  rw [cobarHomEquiv_symm_apply_ι, AInfinityStrictHom.taylor_toAInfinityHom_comp]
  simp [heB]

/-- The **augmented adjunction unit** `A ⟶ U(A)`: the universal strictly unital augmented `A∞`
morphism from `(A, ε)` into its enveloping DG algebra `(U(A), ε_{U(A)})`. -/
noncomputable def envelopingUnit :
    AInfinityHom 𝒜 (ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra).toAInfinityAlgebra :=
  (ε.envelopingHomEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩).1

/-- The universal `A∞` morphism `envelopingUnit : A ⟶ U(A)` is strictly unital and augmented. -/
theorem isAugmented_envelopingUnit :
    ε.envelopingUnit.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.envelopingHomEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩).2

/-- Explicit formula for the Taylor map of `envelopingUnit`. -/
@[simp]
theorem taylor_envelopingUnit (w : ReducedTensorWords R A) :
    ε.envelopingUnit.taylor w =
      algebraMap R (TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal))
        (ε (ReducedTensorWords.letter R A w)) +
        ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (ReducedTensorWords.map (R := R) ε.reducedPart w)) := by
  simp [envelopingUnit]

/-- On a word of elements in `ker ε`, `envelopingUnit.taylor` embeds it as a desuspended generator
after the Koszul involution `σ`. -/
theorem taylor_envelopingUnit_map_subtype (u : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingUnit.taylor
        (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u) =
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 u) := by
  have hlet := LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map ε.augmentationIdeal.subtype) u
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hlet
  have h0 : ε (ReducedTensorWords.letter R ε.augmentationIdeal u : A) = 0 :=
    (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R ε.augmentationIdeal u).2
  have hret : ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u) = u := by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      show ε.reducedPart ∘ₗ ε.augmentationIdeal.subtype = LinearMap.id from
        LinearMap.ext ε.reducedPart_coe,
      ReducedTensorWords.map_id, LinearMap.id_apply]
  rw [ε.taylor_envelopingUnit, hlet, h0, map_zero, zero_add, hret]

/-- Under `envelopingHomEquiv`, an augmented DG algebra morphism `φ : U(A) → B` corresponds to
postcomposing `envelopingUnit` with `φ` viewed as a strict `A∞` morphism. -/
theorem envelopingHomEquiv_eq_comp_envelopingUnit {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingHomEquiv eB φ).1 =
      φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  refine LinearMap.ext fun w ↦ ?_
  simp [AlgHomClass.commutes]

/-- Every strictly unital augmented `A∞` morphism `f : (A, ε) ⟶ (B, e_B)` into an augmented DG
algebra factors through `envelopingUnit` via `(envelopingHomEquiv e_B).symm f`. -/
@[simp]
theorem toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    (((ε.envelopingHomEquiv eB).symm
      f).1).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit =
      f.1 := by
  rw [← ε.envelopingHomEquiv_eq_comp_envelopingUnit eB, Equiv.apply_symm_apply]

/-- **Universal property of `U(A)`**: an augmented DG algebra morphism `φ : U(A) → B` equals
`(envelopingHomEquiv e_B).symm f` if and only if postcomposing `envelopingUnit` with `φ` recovers
`f`. -/
theorem eq_envelopingHomEquiv_symm_iff {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation})
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    φ = (ε.envelopingHomEquiv eB).symm f ↔
      φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit = f.1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (ε.envelopingHomEquiv eB).eq_symm_apply.mpr (Subtype.ext ?_)⟩
  · rw [h, ε.toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit]
  · rwa [ε.envelopingHomEquiv_eq_comp_envelopingUnit]

/-- Target naturality of `envelopingHomEquiv`: postcomposing an augmented DG algebra morphism out
of `U(A)` with an augmented DG algebra morphism `ψ : (B, e_B) → (C, e_C)` postcomposes the
corresponding augmented `A∞` morphism with `ψ`. -/
@[simp]
theorem envelopingHomEquiv_comp {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
    (eB : DGAlgAugmentation hB) (eC : DGAlgAugmentation hC)
    (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingHomEquiv eC
      ⟨ψ.comp φ.1, by rw [← DGAlgHom.comp_assoc, hψ, φ.2]⟩).1 =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (ε.envelopingHomEquiv eB φ).1 := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  refine LinearMap.ext fun w ↦ ?_
  simp [AlgHomClass.commutes]

end AInfinityAlgebra.Augmentation

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} {𝒜'' : AInfinityAlgebra R A''}
  {εA : 𝒜.Augmentation} {εA' : 𝒜'.Augmentation} {εA'' : 𝒜''.Augmentation}

private theorem reducedHom_eq_augmentedHomEquiv {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') :
    hg.reducedHom = εA.augmentedHomEquiv εA' ⟨g, hg⟩ :=
  AInfinityHom.ext <| hg.taylor_reducedHom.trans
    (εA.taylor_augmentedHomEquiv_apply εA' ⟨g, hg⟩).symm

/-- Functoriality of `U(-)`: any strictly unital augmented `A∞` morphism
`g : (A, ε_A) ⟶ (A', ε_{A'})` induces a strict DG algebra morphism `U(A) → U(A')` via the cobar
map of its reduced morphism `g.reducedHom`. -/
noncomputable def envelopingMap {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA') :
    DGAlgHom εA.isDGAlgebra_enveloping εA'.isDGAlgebra_enveloping :=
  hg.reducedHom.cobarMap

/-- On a desuspended generator `s⁻¹ z`, `hg.envelopingMap` applies `hg.reducedHom.barMap`. -/
@[simp]
theorem envelopingMap_ι {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA')
    (z : ReducedTensorWords R εA.augmentationIdeal) :
    hg.envelopingMap (ι R z) = ι R (hg.reducedHom.barMap z) :=
  hg.reducedHom.cobarMap_ι z

/-- Every induced morphism `envelopingMap` preserves the canonical cobar augmentation. -/
@[simp]
theorem envelopingAugmentation_comp_envelopingMap {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') :
    εA'.envelopingAugmentation.comp hg.envelopingMap = εA.envelopingAugmentation := by
  apply εA.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext (isDGAlgebra_trivialGrading R)
  intro z
  simp [AInfinityAlgebra.Augmentation.envelopingAugmentation, envelopingMap]

/-- The identity augmented `A∞` morphism induces the identity DG algebra morphism on `U(A)`. -/
@[simp]
theorem envelopingMap_id (εA : 𝒜.Augmentation) :
    (AInfinityHom.isAugmented_id εA).envelopingMap = DGAlgHom.id εA.isDGAlgebra_enveloping := by
  rw [envelopingMap, (AInfinityHom.isAugmented_id εA).reducedHom_eq_augmentedHomEquiv,
    εA.augmentedHomEquiv_id, AInfinityHom.cobarMap_id]

/-- Passing to universal enveloping DG algebras preserves composition of augmented `A∞`
morphisms. -/
theorem envelopingMap_comp {g' : AInfinityHom 𝒜' 𝒜''} {g : AInfinityHom 𝒜 𝒜'}
    (hg' : g'.IsAugmented εA' εA'') (hg : g.IsAugmented εA εA') :
    (hg'.comp hg).envelopingMap = hg'.envelopingMap.comp hg.envelopingMap := by
  rw [envelopingMap, envelopingMap, envelopingMap,
    (hg'.comp hg).reducedHom_eq_augmentedHomEquiv,
    εA.augmentedHomEquiv_comp εA' ⟨g', hg'⟩ ⟨g, hg⟩,
    ← hg'.reducedHom_eq_augmentedHomEquiv, ← hg.reducedHom_eq_augmentedHomEquiv,
    AInfinityHom.cobarMap_comp]

/-- Source naturality of `envelopingHomEquiv`: precomposing an augmented DG algebra morphism
`φ : U(A') → B` with `hg.envelopingMap` precomposes the corresponding augmented `A∞` morphism with
`g`. -/
@[simp]
theorem envelopingHomEquiv_comp_envelopingMap {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom εA'.isDGAlgebra_enveloping hB //
      eB.comp φ = εA'.envelopingAugmentation})
    {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA') :
    (εA.envelopingHomEquiv eB
      ⟨φ.1.comp hg.envelopingMap, by
        rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩).1 =
      (εA'.envelopingHomEquiv eB φ).1.comp g := by
  let f' := εA'.envelopingHomEquiv eB φ
  let f := εA.envelopingHomEquiv eB
    ⟨φ.1.comp hg.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩
  suffices h : f = ⟨f'.1.comp g, f'.2.comp hg⟩ from congrArg Subtype.val h
  apply (εA.augmentedHomEquiv eB.toAInfinityAugmentation).injective
  rw [εA.augmentedHomEquiv_comp εA' f' ⟨g, hg⟩, ← hg.reducedHom_eq_augmentedHomEquiv]
  have hf : εA.augmentedHomEquiv eB.toAInfinityAugmentation f =
      homToReducedEquiv εA.reducedAlgebra eB.toAInfinityAugmentation
        (εA.cobarAugmentedToHomEquiv eB
          ⟨φ.1.comp hg.envelopingMap, by
            rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩) :=
    (εA.augmentedHomEquiv eB.toAInfinityAugmentation).apply_symm_apply _
  have hf' : εA'.augmentedHomEquiv eB.toAInfinityAugmentation f' =
      homToReducedEquiv εA'.reducedAlgebra eB.toAInfinityAugmentation
        (εA'.cobarAugmentedToHomEquiv eB φ) :=
    (εA'.augmentedHomEquiv eB.toAInfinityAugmentation).apply_symm_apply _
  rw [hf, hf']
  have hcob : εA.cobarAugmentedToHomEquiv eB
      ⟨φ.1.comp hg.envelopingMap, by
        rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩ =
      ⟨(εA'.cobarAugmentedToHomEquiv eB φ).1.comp hg.reducedHom, fun z ↦ by
        rw [AInfinityHom.taylor_comp]
        exact (εA'.cobarAugmentedToHomEquiv eB φ).2 _⟩ :=
    Subtype.ext (AInfinityHom.cobarHomEquiv_comp_cobarMap hB φ.1 hg.reducedHom)
  rw [hcob, homToReducedEquiv_comp εA.reducedAlgebra εA'.reducedAlgebra]

/-- Naturality of the augmented adjunction unit `envelopingUnit` with respect to strictly unital
augmented `A∞` morphisms. -/
@[simp]
theorem toAInfinityHom_envelopingMap_comp_envelopingUnit {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') :
    hg.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        εA.envelopingUnit =
      εA'.envelopingUnit.comp g := by
  have h1 := εA.envelopingHomEquiv_eq_comp_envelopingUnit εA'.envelopingAugmentation
    ⟨hg.envelopingMap, hg.envelopingAugmentation_comp_envelopingMap⟩
  have h2 := hg.envelopingHomEquiv_comp_envelopingMap εA'.envelopingAugmentation
    ⟨DGAlgHom.id εA'.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩
  simp only [DGAlgHom.id_comp] at h2
  exact h1.symm.trans h2

end AInfinityHom.IsAugmented

namespace DGAlgAugmentation

/-- The **augmented adjunction counit** `U(B) → B` for an augmented differential graded algebra
`(B, e_B)`: the unique augmented DG algebra morphism corresponding under `envelopingHomEquiv` to
the identity augmented `A∞` morphism of `(B, e_B)`. -/
noncomputable def envelopingCounit {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    DGAlgHom eB.toAInfinityAugmentation.isDGAlgebra_enveloping hB :=
  ((eB.toAInfinityAugmentation.envelopingHomEquiv eB).symm
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩).1

/-- The counit `envelopingCounit : U(B) → B` commutes with the augmentations. -/
@[simp]
theorem comp_envelopingCounit {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    eB.comp eB.envelopingCounit = eB.toAInfinityAugmentation.envelopingAugmentation :=
  ((eB.toAInfinityAugmentation.envelopingHomEquiv eB).symm
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩).2

/-- On a desuspended generator `s⁻¹ z`, `envelopingCounit` projects onto the single-letter
component in `ker e_B` after the Koszul involution, vanishing on words of length at least two. -/
@[simp]
theorem envelopingCounit_ι {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (z : ReducedTensorWords R eB.toAInfinityAugmentation.augmentationIdeal) :
    eB.envelopingCounit (ι R z) =
      (ReducedTensorWords.letter R eB.toAInfinityAugmentation.augmentationIdeal
        ((ReducedTensorWords.grading
          (eB.toAInfinityAugmentation.reducedAlgebra.grading.shift 1)).koszulTwist 1 z) : B) := by
  rw [envelopingCounit, AInfinityAlgebra.Augmentation.envelopingHomEquiv_symm_apply_ι,
    AInfinityHom.taylor_id]
  exact LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map eB.toAInfinityAugmentation.augmentationIdeal.subtype) _

/-- First triangle identity of the augmented bar–cobar adjunction: for an augmented DG algebra
`(B, e_B)`, `envelopingCounit` followed by `envelopingUnit` is the identity `A∞` morphism of
`B`. -/
@[simp]
theorem toAInfinityHom_envelopingCounit_comp_envelopingUnit {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) :
    eB.envelopingCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        eB.toAInfinityAugmentation.envelopingUnit =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  eB.toAInfinityAugmentation.toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit eB _

end DGAlgAugmentation

namespace AInfinityAlgebra.Augmentation

private theorem envelopingCounit_comp_envelopingMap_ι {𝒜 : AInfinityAlgebra R A}
    (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    {u : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra}
    (hu : u.IsAugmented ε eB.toAInfinityAugmentation)
    (gen : ReducedTensorWords R ε.augmentationIdeal → B)
    (hgen_aug : ∀ z, eB (gen z) = 0)
    (hgen_taylor : ∀ w,
      u.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype w) =
        gen ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 w))
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    (eB.envelopingCounit.comp hu.envelopingMap) (ι R z) = gen z := by
  let hbar := hu.reducedHom
  let σ := (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
  have h1 : (eB.envelopingCounit.comp hu.envelopingMap) (ι R z) =
      eB.envelopingCounit (ι R (hbar.barMap z)) := by
    rw [DGAlgHom.comp_apply, hu.envelopingMap_ι]
  have h2 := eB.envelopingCounit_ι (hbar.barMap z)
  have h3 : ReducedTensorWords.letter R eB.toAInfinityAugmentation.augmentationIdeal
      ((ReducedTensorWords.grading
        (eB.toAInfinityAugmentation.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (hbar.barMap z)) =
      hbar.taylor (σ z) :=
    (congrArg _ (koszulTwist_barMap hbar z)).trans (letter_barMap hbar (σ z))
  have h4 : (hbar.taylor (σ z) : B) =
      (eB.toAInfinityAugmentation.reducedPart
        (u.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype (σ z))) : B) := by
    simpa only [LinearMap.comp_apply] using
      congrArg Subtype.val (LinearMap.congr_fun hu.taylor_reducedHom (σ z))
  have h5 : (eB.toAInfinityAugmentation.reducedPart
      (u.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype (σ z))) : B) =
      gen z := by
    have huz : u.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype (σ z)) =
        gen z :=
      (hgen_taylor (σ z)).trans
        (congrArg gen (InternalGrading.koszulTwist_koszulTwist _ 1 z))
    rw [huz, eB.toAInfinityAugmentation.coe_reducedPart,
      DGAlgAugmentation.toAInfinityAugmentation_apply, hgen_aug z, zero_smul, sub_zero]
  exact h1.trans <| h2.trans <| (congrArg Subtype.val h3).trans <| h4.trans h5

/-- Second triangle identity of the augmented bar–cobar adjunction: for an augmented `A∞` algebra
`(A, ε)`, applying `envelopingMap` to `envelopingUnit` and composing with `envelopingCounit` gives
the identity DG algebra morphism of `U(A)`. -/
@[simp]
theorem envelopingCounit_comp_envelopingMap_envelopingUnit {𝒜 : AInfinityAlgebra R A}
    (ε : 𝒜.Augmentation) :
    ε.envelopingAugmentation.envelopingCounit.comp
        ε.isAugmented_envelopingUnit.envelopingMap =
      DGAlgHom.id ε.isDGAlgebra_enveloping := by
  apply ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext ε.isDGAlgebra_enveloping
  intro z
  exact (ε.envelopingCounit_comp_envelopingMap_ι ε.envelopingAugmentation
    ε.isAugmented_envelopingUnit (ι R) ε.envelopingAugmentation_ι
    ε.taylor_envelopingUnit_map_subtype z).trans (DGAlgHom.id_apply _ _).symm

end AInfinityAlgebra.Augmentation

end Enveloping

end TauCeti
