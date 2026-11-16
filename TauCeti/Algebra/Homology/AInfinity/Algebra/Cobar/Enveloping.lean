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

For an augmented uncurved `A∞` algebra `(A, ε_A)`, the cobar construction of the reduced bar
coalgebra `B∞ A = Tᶜ(s(ker ε_A))` is the **universal enveloping differential graded algebra**
`U(A) = Ω B∞ A = T(s⁻¹ Tᶜ(s(ker ε_A)))`, equipped with its canonical cobar augmentation
`envelopingAugmentation : U(A) → R` annihilating all desuspended generators.

Combining the augmented cobar universal property, factorization through the reduced augmentation
ideal (`AInfinityAlgebra.Augmentation.homToReducedEquiv`), and the splitting equivalence
`AInfinityAlgebra.Augmentation.augmentedHomEquiv` yields the **augmented bar–cobar adjunction**
(`TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv`) between augmented DG algebra morphisms
`(U(A), ε_{U(A)}) → (B, e_B)` and strictly unital augmented `A∞` morphisms `(A, ε_A) ⟶ (B, e_B)`,
together with functoriality (`envelopingMap`), the unit `envelopingUnit : A ⟶ U(A)`, the counit
`envelopingCounit : U(B) → B`, and both triangle identities.

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

section Enveloping

variable {R : Type uR} [CommRing R]

namespace AInfinityAlgebra.Augmentation

section Source

variable {A : Type uA} [AddCommGroup A] [Module R A] {𝒜 : AInfinityAlgebra R A}
  (ε : 𝒜.Augmentation)

/-- **The universal enveloping differential graded algebra** `U(A) = Ω B∞ A` of an augmented `A∞`
algebra `(A, ε)`: the cobar construction of `B∞ A = Tᶜ(s(ker ε))`. -/
theorem isDGAlgebra_enveloping :
    IsDGAlgebra
      (tensorAlgebraPiece
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1)))
      (cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
        (ReducedTensorWords.deconcatenation R ε.augmentationIdeal)
        ε.reducedAlgebra.barDifferential) :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- The canonical DG algebra augmentation `U(A) → R` annihilating all desuspended generators. -/
noncomputable def envelopingAugmentation : DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- The canonical augmentation of `U(A)` kills every desuspended generator. -/
@[simp]
theorem envelopingAugmentation_ι (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (ι R z) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι z

section Target

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)

private noncomputable def cobarAugmentedToHomEquiv :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom ε.reducedAlgebra hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        ∀ z, f.taylor z ∈ eB.toAInfinityAugmentation.augmentationIdeal} :=
  (ε.reducedAlgebra.cobarBarHomEquiv hB).symm.subtypeEquiv fun φ ↦ by
    rw [envelopingAugmentation,
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eB]
    simp only [DGAlgAugmentation.mem_augmentationIdeal,
      AInfinityAlgebra.Augmentation.mem_augmentationIdeal,
      DGAlgAugmentation.toAInfinityAugmentation_apply,
      AInfinityAlgebra.taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist,
      LinearMap.comp_apply, LinearMap.coe_ofClass]
    refine ⟨fun h z ↦ h _, fun h z ↦ ?_⟩
    simpa [InternalGrading.koszulTwist_koszulTwist] using
      h ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 z)

/-- **The augmented bar–cobar adjunction**: augmented DG algebra morphisms
`(U(A), ε_{U(A)}) → (B, e_B)` correspond bijectively to strictly unital augmented `A∞` morphisms
`(A, ε_A) ⟶ (B, e_B)`. -/
noncomputable def envelopingHomEquiv :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsAugmented ε eB.toAInfinityAugmentation} :=
  (ε.cobarAugmentedToHomEquiv eB).trans <|
    (eB.toAInfinityAugmentation.homToReducedEquiv ε.reducedAlgebra).trans
      (ε.augmentedHomEquiv eB.toAInfinityAugmentation).symm

/-- Explicit Taylor map of `envelopingHomEquiv eB φ`. -/
@[simp]
theorem taylor_envelopingHomEquiv_apply
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation})
    (w : ReducedTensorWords R A) :
    ((ε.envelopingHomEquiv eB φ).1).taylor w =
      algebraMap R B (ε (ReducedTensorWords.letter R A w)) +
        φ.1 (ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (ReducedTensorWords.map (R := R) ε.reducedPart w))) := by
  have hφ := (ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff
    eB φ.1).mp φ.2
  have h0 (u) : eB (φ.1 (ι R u)) = 0 := (eB.mem_augmentationIdeal).mp (hφ u)
  simp [envelopingHomEquiv, cobarAugmentedToHomEquiv, Augmentation.coe_reducedPart,
    -AInfinityAlgebra.taylor_cobarBarHomEquiv_symm,
    AInfinityAlgebra.taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist,
    Algebra.algebraMap_eq_smul_one, h0]

/-- The augmented DG algebra lift `(envelopingHomEquiv eB).symm f` evaluates on `s⁻¹ z` to
`f.taylor` on the included and Koszul-twisted reduced word `σ z`. -/
@[simp]
theorem envelopingHomEquiv_symm_apply_ι
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation})
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ((ε.envelopingHomEquiv eB).symm f).1 (ι R z) =
      f.1.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 z)) := by
  simp only [envelopingHomEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    ε.augmentedHomEquiv_apply, cobarAugmentedToHomEquiv, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply]
  rw [AInfinityAlgebra.cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist,
    AInfinityAlgebra.Augmentation.homToReducedEquiv_symm_apply,
    f.2.inclusionStrictHom_comp_reducedHom, AInfinityHom.taylor_comp,
    AInfinityStrictHom.barMap_toAInfinityHom, AInfinityStrictHom.barMap_def,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap, LinearMap.comp_apply]

end Target

/-- The **augmented adjunction unit** `A ⟶ U(A)`: the universal strictly unital augmented `A∞`
morphism from `(A, ε)` into `(U(A), ε_{U(A)})`. -/
noncomputable def envelopingUnit :
    AInfinityHom 𝒜 (ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra).toAInfinityAlgebra :=
  (ε.envelopingHomEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩).1

/-- The universal `A∞` morphism `envelopingUnit : A ⟶ U(A)` is strictly unital and augmented. -/
@[simp]
theorem isAugmented_envelopingUnit :
    ε.envelopingUnit.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.envelopingHomEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩).2

/-- Under `envelopingHomEquiv`, the identity of `U(A)` corresponds to `envelopingUnit`. -/
theorem envelopingHomEquiv_id :
    ε.envelopingHomEquiv ε.envelopingAugmentation
        ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩ =
      ⟨ε.envelopingUnit, ε.isAugmented_envelopingUnit⟩ :=
  (rfl)

/-- Under `(envelopingHomEquiv).symm`, `envelopingUnit` corresponds to the identity of `U(A)`. -/
@[simp]
theorem envelopingHomEquiv_symm_envelopingUnit :
    (ε.envelopingHomEquiv ε.envelopingAugmentation).symm
        ⟨ε.envelopingUnit, ε.isAugmented_envelopingUnit⟩ =
      ⟨DGAlgHom.id ε.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩ :=
  Equiv.symm_apply_apply _ _

/-- Explicit formula for the Taylor map of `envelopingUnit`. -/
@[simp]
theorem taylor_envelopingUnit_apply (w : ReducedTensorWords R A) :
    ε.envelopingUnit.taylor w =
      algebraMap R (TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal))
        (ε (ReducedTensorWords.letter R A w)) +
        ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (ReducedTensorWords.map (R := R) ε.reducedPart w)) := by
  simp [envelopingUnit]

/-- On words in `ker ε`, `envelopingUnit.taylor` embeds as a desuspended generator after `σ`. -/
theorem taylor_envelopingUnit_map_subtype (u : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingUnit.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u) =
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 u) := by
  simp [ε.taylor_envelopingUnit_apply,
    (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ u).2]

section UniversalProperty

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)

/-- Under `envelopingHomEquiv`, an augmented DG algebra morphism `φ : U(A) → B` acts by
postcomposing `envelopingUnit` with `φ`. -/
theorem envelopingHomEquiv_eq_comp_envelopingUnit
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingHomEquiv eB φ).1 =
      φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  exact LinearMap.ext fun _ ↦ by simp [AlgHomClass.commutes]

/-- Every strictly unital augmented `A∞` morphism `f : (A, ε) ⟶ (B, e_B)` factors through
`envelopingUnit` via `(envelopingHomEquiv e_B).symm f`. -/
@[simp]
theorem toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    (((ε.envelopingHomEquiv eB).symm
      f).1).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit =
      f.1 := by
  rw [← ε.envelopingHomEquiv_eq_comp_envelopingUnit eB, Equiv.apply_symm_apply]

/-- **Universal property of `U(A)`**: `φ = (envelopingHomEquiv e_B).symm f` iff
`φ ∘ envelopingUnit = f`. -/
theorem eq_envelopingHomEquiv_symm_iff
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation})
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    φ = (ε.envelopingHomEquiv eB).symm f ↔
      φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.envelopingUnit = f.1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (ε.envelopingHomEquiv eB).eq_symm_apply.mpr (Subtype.ext ?_)⟩
  · rw [h, ε.toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit]
  · rwa [ε.envelopingHomEquiv_eq_comp_envelopingUnit]

/-- Target naturality of `envelopingHomEquiv` along `ψ : (B, e_B) → (C, e_C)`. -/
@[simp]
theorem envelopingHomEquiv_comp {C : Type uC} [Ring C] [Algebra R C]
    {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}
    (eC : DGAlgAugmentation hC) (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingHomEquiv eC ⟨ψ.comp φ.1, by rw [← DGAlgHom.comp_assoc, hψ, φ.2]⟩).1 =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (ε.envelopingHomEquiv eB φ).1 := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  exact LinearMap.ext fun _ ↦ by simp [AlgHomClass.commutes]

/-- Target naturality of `(envelopingHomEquiv).symm` along `ψ : (B, e_B) → (C, e_C)`. -/
@[simp]
theorem envelopingHomEquiv_symm_toAInfinityHom_comp {C : Type uC} [Ring C] [Algebra R C]
    {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}
    (eC : DGAlgAugmentation hC) (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    ((ε.envelopingHomEquiv eC).symm
        ⟨ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f.1,
          ((ψ.isAugmented_toAInfinityHom_iff eB eC).mpr hψ).comp f.2⟩).1 =
      ψ.comp ((ε.envelopingHomEquiv eB).symm f).1 := by
  let φ := (ε.envelopingHomEquiv eB).symm f
  suffices h : (ε.envelopingHomEquiv eC).symm
      ⟨ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f.1,
        ((ψ.isAugmented_toAInfinityHom_iff eB eC).mpr hψ).comp f.2⟩ =
      ⟨ψ.comp φ.1, by rw [← DGAlgHom.comp_assoc, hψ, φ.2]⟩ from congrArg Subtype.val h
  refine ((ε.envelopingHomEquiv eC).symm_apply_eq).mpr (Subtype.ext ?_)
  rw [ε.envelopingHomEquiv_comp eB eC ψ hψ φ]
  exact congrArg _ (congrArg Subtype.val ((ε.envelopingHomEquiv eB).apply_symm_apply f)).symm

end UniversalProperty

end Source

end AInfinityAlgebra.Augmentation

namespace AInfinityHom.IsAugmented

section Functoriality

variable {A : Type uA} [AddCommGroup A] [Module R A] {𝒜 : AInfinityAlgebra R A}

section Hom

variable {A' : Type uA'} [AddCommGroup A'] [Module R A'] {𝒜' : AInfinityAlgebra R A'}
  {εA : 𝒜.Augmentation} {εA' : 𝒜'.Augmentation}

/-- Functoriality of `U(-)`: any strictly unital augmented `A∞` morphism induces a DG algebra
morphism `U(A) → U(A')` via `hg.reducedHom.cobarBarMap`. -/
noncomputable def envelopingMap {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA') :
    DGAlgHom εA.isDGAlgebra_enveloping εA'.isDGAlgebra_enveloping :=
  hg.reducedHom.cobarBarMap

/-- On a desuspended generator `s⁻¹ z`, `hg.envelopingMap` applies `hg.reducedHom.barMap`. -/
@[simp]
theorem envelopingMap_ι {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA')
    (z : ReducedTensorWords R εA.augmentationIdeal) :
    hg.envelopingMap (ι R z) = ι R (hg.reducedHom.barMap z) :=
  hg.reducedHom.cobarBarMap_ι z

/-- Every induced morphism `envelopingMap` preserves the canonical cobar augmentation. -/
@[simp]
theorem envelopingAugmentation_comp_envelopingMap {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') :
    εA'.envelopingAugmentation.comp hg.envelopingMap = εA.envelopingAugmentation :=
  εA.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext (isDGAlgebra_trivialGrading R)
    fun _ ↦ by simp [AInfinityAlgebra.Augmentation.envelopingAugmentation, envelopingMap]

/-- Passing to enveloping DG algebras preserves composition of augmented `A∞` morphisms. -/
theorem envelopingMap_comp {A'' : Type uA''} [AddCommGroup A''] [Module R A'']
    {𝒜'' : AInfinityAlgebra R A''} {εA'' : 𝒜''.Augmentation}
    {g' : AInfinityHom 𝒜' 𝒜''} {g : AInfinityHom 𝒜 𝒜'}
    (hg' : g'.IsAugmented εA' εA'') (hg : g.IsAugmented εA εA') :
    (hg'.comp hg).envelopingMap = hg'.envelopingMap.comp hg.envelopingMap := by
  rw [envelopingMap, envelopingMap, envelopingMap, hg'.reducedHom_comp hg,
    AInfinityHom.cobarBarMap_comp]

/-- Source naturality of `envelopingHomEquiv` under precomposition with `hg.envelopingMap`. -/
@[simp]
theorem envelopingHomEquiv_comp_envelopingMap {B : Type uB} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom εA'.isDGAlgebra_enveloping hB // eB.comp φ = εA'.envelopingAugmentation})
    {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA') :
    (εA.envelopingHomEquiv eB ⟨φ.1.comp hg.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩).1 =
      (εA'.envelopingHomEquiv eB φ).1.comp g := by
  let ψ : {ψ : DGAlgHom εA.isDGAlgebra_enveloping hB // eB.comp ψ = εA.envelopingAugmentation} :=
    ⟨φ.1.comp hg.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, φ.2, hg.envelopingAugmentation_comp_envelopingMap]⟩
  let f' := εA'.envelopingHomEquiv eB φ
  suffices h : εA.envelopingHomEquiv eB ψ = ⟨f'.1.comp g, f'.2.comp hg⟩ from congrArg Subtype.val h
  apply (εA.augmentedHomEquiv eB.toAInfinityAugmentation).injective
  rw [εA.augmentedHomEquiv_comp εA' f' ⟨g, hg⟩, εA.augmentedHomEquiv_apply εA' ⟨g, hg⟩]
  dsimp only [AInfinityAlgebra.Augmentation.envelopingHomEquiv, Equiv.trans_apply, f']
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    ← eB.toAInfinityAugmentation.homToReducedEquiv_comp εA.reducedAlgebra εA'.reducedAlgebra]
  refine congrArg _ (Subtype.ext ?_)
  dsimp only [AInfinityAlgebra.Augmentation.cobarAugmentedToHomEquiv, Equiv.subtypeEquiv_apply,
    ψ, envelopingMap]
  exact εA.reducedAlgebra.cobarBarHomEquiv_symm_comp_cobarBarMap hB φ.1 hg.reducedHom

/-- Naturality of `envelopingUnit` with respect to strictly unital augmented `A∞` morphisms. -/
@[simp]
theorem toAInfinityHom_envelopingMap_comp_envelopingUnit {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') :
    hg.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        εA.envelopingUnit = εA'.envelopingUnit.comp g := by
  have h1 := εA.envelopingHomEquiv_eq_comp_envelopingUnit εA'.envelopingAugmentation
    ⟨hg.envelopingMap, hg.envelopingAugmentation_comp_envelopingMap⟩
  have h2 := hg.envelopingHomEquiv_comp_envelopingMap εA'.envelopingAugmentation
    ⟨DGAlgHom.id εA'.isDGAlgebra_enveloping, DGAlgHom.comp_id _⟩
  simp only [DGAlgHom.id_comp] at h2
  exact h1.symm.trans h2

end Hom

/-- The identity augmented `A∞` morphism induces the identity DG algebra morphism on `U(A)`. -/
@[simp]
theorem envelopingMap_id (εA : 𝒜.Augmentation) :
    (AInfinityHom.isAugmented_id εA).envelopingMap = DGAlgHom.id εA.isDGAlgebra_enveloping := by
  rw [envelopingMap, AInfinityHom.IsAugmented.reducedHom_id, AInfinityHom.cobarBarMap_id]

end Functoriality

end AInfinityHom.IsAugmented

namespace AInfinityAlgebra.Augmentation

/-- Source naturality of `(envelopingHomEquiv).symm` under precomposition with an augmented `A∞`
morphism `g : (A, ε_A) ⟶ (A', ε_{A'})`. -/
@[simp]
theorem envelopingHomEquiv_symm_comp {A : Type uA} {A' : Type uA'} {B : Type uB}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}
    [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
    {hB : IsDGAlgebra ℬ dB} (εA : 𝒜.Augmentation) {εA' : 𝒜'.Augmentation}
    (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜' hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented εA' eB.toAInfinityAugmentation})
    {g : AInfinityHom 𝒜 𝒜'} (hg : g.IsAugmented εA εA') :
    ((εA.envelopingHomEquiv eB).symm ⟨f.1.comp g, f.2.comp hg⟩).1 =
      ((εA'.envelopingHomEquiv eB).symm f).1.comp hg.envelopingMap := by
  let φ' := (εA'.envelopingHomEquiv eB).symm f
  suffices h : (εA.envelopingHomEquiv eB).symm ⟨f.1.comp g, f.2.comp hg⟩ =
      ⟨φ'.1.comp hg.envelopingMap, by
        rw [← DGAlgHom.comp_assoc, φ'.2, hg.envelopingAugmentation_comp_envelopingMap]⟩ from
    congrArg Subtype.val h
  refine ((εA.envelopingHomEquiv eB).symm_apply_eq).mpr (Subtype.ext ?_)
  rw [hg.envelopingHomEquiv_comp_envelopingMap eB φ']
  exact congrArg (fun x : AInfinityHom 𝒜' _ ↦ x.comp g)
    (congrArg Subtype.val ((εA'.envelopingHomEquiv eB).apply_symm_apply f)).symm

end AInfinityAlgebra.Augmentation

namespace DGAlgAugmentation

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)

/-- The **augmented adjunction counit** `U(B) → B` for an augmented DG algebra `(B, e_B)`,
corresponding under `envelopingHomEquiv` to `AInfinityHom.id`. -/
noncomputable def envelopingCounit :
    DGAlgHom eB.toAInfinityAugmentation.isDGAlgebra_enveloping hB :=
  ((eB.toAInfinityAugmentation.envelopingHomEquiv eB).symm
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩).1

/-- The counit `envelopingCounit : U(B) → B` commutes with the augmentations. -/
@[simp]
theorem comp_envelopingCounit :
    eB.comp eB.envelopingCounit = eB.toAInfinityAugmentation.envelopingAugmentation :=
  ((eB.toAInfinityAugmentation.envelopingHomEquiv eB).symm
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩).2

/-- Under `(envelopingHomEquiv).symm`, the identity `A∞` morphism of `B` corresponds to
`envelopingCounit`. -/
theorem envelopingHomEquiv_symm_id :
    (eB.toAInfinityAugmentation.envelopingHomEquiv eB).symm
        ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩ =
      ⟨eB.envelopingCounit, eB.comp_envelopingCounit⟩ :=
  (rfl)

/-- Under `envelopingHomEquiv`, `envelopingCounit` corresponds to the identity `A∞` morphism
of `B`. -/
@[simp]
theorem envelopingHomEquiv_envelopingCounit :
    eB.toAInfinityAugmentation.envelopingHomEquiv eB
        ⟨eB.envelopingCounit, eB.comp_envelopingCounit⟩ =
      ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩ :=
  Equiv.apply_symm_apply _ _

/-- On `s⁻¹ z`, `envelopingCounit` projects onto single letters in `ker e_B` and applies the
negated Koszul involution. -/
@[simp]
theorem envelopingCounit_ι
    (z : ReducedTensorWords R eB.toAInfinityAugmentation.augmentationIdeal) :
    eB.envelopingCounit (ι R z) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1
        (ReducedTensorWords.letter R eB.toAInfinityAugmentation.augmentationIdeal z : B) := by
  have htwist := eB.toAInfinityAugmentation.inclusionStrictHom.isHomogeneous.koszulTwist_apply 1
    (ReducedTensorWords.letter R eB.toAInfinityAugmentation.augmentationIdeal z)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap, Submodule.subtype_apply,
    IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading] at htwist
  rw [envelopingCounit, AInfinityAlgebra.Augmentation.envelopingHomEquiv_symm_apply_ι,
    AInfinityHom.taylor_id, ReducedTensorWords.letter_map,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.letter_map,
    InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, Submodule.subtype_apply,
    Submodule.coe_neg, ← htwist]

/-- First triangle identity of the augmented bar–cobar adjunction for `(B, e_B)`. -/
@[simp]
theorem toAInfinityHom_envelopingCounit_comp_envelopingUnit :
    eB.envelopingCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        eB.toAInfinityAugmentation.envelopingUnit =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  eB.toAInfinityAugmentation.toAInfinityHom_envelopingHomEquiv_symm_comp_envelopingUnit eB _

/-- Factoring `(envelopingHomEquiv eB).symm` through `envelopingMap` and `envelopingCounit`. -/
theorem envelopingCounit_comp_envelopingMap {A : Type uA} [AddCommGroup A] [Module R A]
    {𝒜 : AInfinityAlgebra R A} {ε : 𝒜.Augmentation}
    {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra}
    (hf : f.IsAugmented ε eB.toAInfinityAugmentation) :
    eB.envelopingCounit.comp hf.envelopingMap =
      ((ε.envelopingHomEquiv eB).symm ⟨f, hf⟩).1 := by
  have h := ε.envelopingHomEquiv_symm_comp eB
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eB.toAInfinityAugmentation⟩ hf
  simpa only [AInfinityHom.id_comp, eB.envelopingHomEquiv_symm_id] using h.symm

/-- Naturality of `envelopingCounit` along an augmented DG algebra morphism
`ψ : (A, e_A) → (B, e_B)`. -/
@[simp]
theorem envelopingCounit_comp_envelopingMap_toAInfinityHom {A : Type uA} [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}
    (eA : DGAlgAugmentation hA) (ψ : DGAlgHom hA hB) (hψ : eB.comp ψ = eA) :
    eB.envelopingCounit.comp
        ((ψ.isAugmented_toAInfinityHom_iff eA eB).mpr hψ).envelopingMap =
      ψ.comp eA.envelopingCounit := by
  rw [eB.envelopingCounit_comp_envelopingMap]
  have h := eA.toAInfinityAugmentation.envelopingHomEquiv_symm_toAInfinityHom_comp eA eB ψ hψ
    ⟨AInfinityHom.id _, AInfinityHom.isAugmented_id eA.toAInfinityAugmentation⟩
  simpa only [AInfinityHom.comp_id, eA.envelopingHomEquiv_symm_id] using h

end DGAlgAugmentation

namespace AInfinityAlgebra.Augmentation

/-- Second triangle identity of the augmented bar–cobar adjunction for `(A, ε)`. -/
@[simp]
theorem envelopingCounit_comp_envelopingMap_envelopingUnit {A : Type uA}
    [AddCommGroup A] [Module R A] {𝒜 : AInfinityAlgebra R A} (ε : 𝒜.Augmentation) :
    ε.envelopingAugmentation.envelopingCounit.comp ε.isAugmented_envelopingUnit.envelopingMap =
      DGAlgHom.id ε.isDGAlgebra_enveloping :=
  (ε.envelopingAugmentation.envelopingCounit_comp_envelopingMap
    ε.isAugmented_envelopingUnit).trans <|
    congrArg Subtype.val ((ε.envelopingHomEquiv ε.envelopingAugmentation).symm_apply_apply
      ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩)

end AInfinityAlgebra.Augmentation

end Enveloping

end TauCeti
