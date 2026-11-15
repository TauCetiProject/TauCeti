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
        ∀ z, f.taylor z ∈ eB.toAInfinityAugmentation.augmentationIdeal} where
  toFun φ := ⟨(ε.reducedAlgebra.cobarBarHomEquiv hB).symm φ.1, fun z ↦ by
    have hφ := (ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff
      eB φ.1).mp φ.2
    rw [eB.toAInfinityAugmentation.mem_augmentationIdeal,
      AInfinityAlgebra.taylor_cobarBarHomEquiv_symm_eq]
    simpa using (eB.mem_augmentationIdeal).mp (hφ _)⟩
  invFun f := ⟨ε.reducedAlgebra.cobarBarHomEquiv hB f.1, by
    rw [envelopingAugmentation,
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eB]
    intro z
    rw [eB.mem_augmentationIdeal, AInfinityAlgebra.cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist]
    simpa using (eB.toAInfinityAugmentation.mem_augmentationIdeal).mp (f.2 _)⟩
  left_inv φ := Subtype.ext ((ε.reducedAlgebra.cobarBarHomEquiv hB).apply_symm_apply φ.1)
  right_inv f := Subtype.ext ((ε.reducedAlgebra.cobarBarHomEquiv hB).symm_apply_apply f.1)

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
theorem taylor_envelopingHomEquiv
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
    AInfinityAlgebra.taylor_cobarBarHomEquiv_symm_eq, Algebra.algebraMap_eq_smul_one, h0]

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
  have heB (u : ReducedTensorWords R ε.augmentationIdeal) :
      eB (f.1.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u)) = 0 := by
    have h1 := LinearMap.congr_fun f.2.comp_taylor
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u)
    have h2 := LinearMap.congr_fun
      (ReducedTensorWords.letter_comp_map ε.augmentationIdeal.subtype) u
    simp only [LinearMap.comp_apply, DGAlgAugmentation.toAInfinityAugmentation_apply] at h1 h2
    exact h1.trans (h2 ▸ (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ u).2)
  rw [envelopingHomEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  simp only [cobarAugmentedToHomEquiv, Equiv.coe_fn_symm_mk]
  rw [AInfinityAlgebra.cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist,
    AInfinityAlgebra.Augmentation.homToReducedEquiv_symm_apply,
    AInfinityStrictHom.taylor_toAInfinityHom_comp]
  simp [Augmentation.coe_reducedPart, heB]

end Target

/-- The **augmented adjunction unit** `A ⟶ U(A)`: the universal strictly unital augmented `A∞`
morphism from `(A, ε)` into `(U(A), ε_{U(A)})`. -/
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

/-- On words in `ker ε`, `envelopingUnit.taylor` embeds as a desuspended generator after `σ`. -/
theorem taylor_envelopingUnit_map_subtype (u : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingUnit.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u) =
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 u) := by
  have hlet := LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map ε.augmentationIdeal.subtype) u
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hlet
  have hret : ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype u) = u := by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      show ε.reducedPart ∘ₗ ε.augmentationIdeal.subtype = LinearMap.id from
        LinearMap.ext ε.reducedPart_coe, ReducedTensorWords.map_id, LinearMap.id_apply]
  rw [ε.taylor_envelopingUnit, hlet,
    (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R _ u).2, map_zero, zero_add, hret]

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

end UniversalProperty

end Source

end AInfinityAlgebra.Augmentation

namespace AInfinityHom.IsAugmented

section Functoriality

variable {A : Type uA} [AddCommGroup A] [Module R A] {𝒜 : AInfinityAlgebra R A}

section Hom

variable {A' : Type uA'} [AddCommGroup A'] [Module R A'] {𝒜' : AInfinityAlgebra R A'}
  {εA : 𝒜.Augmentation} {εA' : 𝒜'.Augmentation}

private theorem reducedHom_eq_augmentedHomEquiv {g : AInfinityHom 𝒜 𝒜'}
    (hg : g.IsAugmented εA εA') : hg.reducedHom = εA.augmentedHomEquiv εA' ⟨g, hg⟩ :=
  AInfinityHom.ext <|
    hg.taylor_reducedHom.trans (εA.taylor_augmentedHomEquiv_apply εA' ⟨g, hg⟩).symm

/-- Functoriality of `U(-)`: any strictly unital augmented `A∞` morphism induces a DG algebra
morphism `U(A) → U(A')` via `hg.reducedHom.cobarMap`. -/
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
    εA'.envelopingAugmentation.comp hg.envelopingMap = εA.envelopingAugmentation :=
  εA.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext (isDGAlgebra_trivialGrading R)
    fun _ ↦ by simp [AInfinityAlgebra.Augmentation.envelopingAugmentation, envelopingMap]

/-- Passing to enveloping DG algebras preserves composition of augmented `A∞` morphisms. -/
theorem envelopingMap_comp {A'' : Type uA''} [AddCommGroup A''] [Module R A'']
    {𝒜'' : AInfinityAlgebra R A''} {εA'' : 𝒜''.Augmentation}
    {g' : AInfinityHom 𝒜' 𝒜''} {g : AInfinityHom 𝒜 𝒜'}
    (hg' : g'.IsAugmented εA' εA'') (hg : g.IsAugmented εA εA') :
    (hg'.comp hg).envelopingMap = hg'.envelopingMap.comp hg.envelopingMap := by
  rw [envelopingMap, envelopingMap, envelopingMap, (hg'.comp hg).reducedHom_eq_augmentedHomEquiv,
    εA.augmentedHomEquiv_comp εA' ⟨g', hg'⟩ ⟨g, hg⟩, ← hg'.reducedHom_eq_augmentedHomEquiv,
    ← hg.reducedHom_eq_augmentedHomEquiv, AInfinityHom.cobarMap_comp]

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
  rw [εA.augmentedHomEquiv_comp εA' f' ⟨g, hg⟩, ← hg.reducedHom_eq_augmentedHomEquiv]
  dsimp only [AInfinityAlgebra.Augmentation.envelopingHomEquiv, Equiv.trans_apply, f']
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    ← eB.toAInfinityAugmentation.homToReducedEquiv_comp εA.reducedAlgebra εA'.reducedAlgebra]
  exact congrArg _ (Subtype.ext
    (AInfinityHom.cobarBarHomEquiv_symm_comp_cobarMap hB φ.1 hg.reducedHom))

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
  rw [envelopingMap, (AInfinityHom.isAugmented_id εA).reducedHom_eq_augmentedHomEquiv,
    εA.augmentedHomEquiv_id, AInfinityHom.cobarMap_id]

end Functoriality

end AInfinityHom.IsAugmented

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

/-- On `s⁻¹ z`, `envelopingCounit` projects onto single letters in `ker e_B` after `σ`. -/
@[simp]
theorem envelopingCounit_ι
    (z : ReducedTensorWords R eB.toAInfinityAugmentation.augmentationIdeal) :
    eB.envelopingCounit (ι R z) =
      (ReducedTensorWords.letter R eB.toAInfinityAugmentation.augmentationIdeal
        ((ReducedTensorWords.grading
          (eB.toAInfinityAugmentation.reducedAlgebra.grading.shift 1)).koszulTwist 1 z) : B) := by
  rw [envelopingCounit, AInfinityAlgebra.Augmentation.envelopingHomEquiv_symm_apply_ι,
    AInfinityHom.taylor_id]
  exact LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map eB.toAInfinityAugmentation.augmentationIdeal.subtype) _

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
  let ψ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} :=
    ⟨eB.envelopingCounit.comp hf.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, eB.comp_envelopingCounit,
        hf.envelopingAugmentation_comp_envelopingMap]⟩
  suffices h : ψ = (ε.envelopingHomEquiv eB).symm ⟨f, hf⟩ from congrArg Subtype.val h
  refine (ε.envelopingHomEquiv eB).eq_symm_apply.mpr (Subtype.ext ?_)
  have h1 := hf.envelopingHomEquiv_comp_envelopingMap eB
    ⟨eB.envelopingCounit, eB.comp_envelopingCounit⟩
  have hc : (eB.toAInfinityAugmentation.envelopingHomEquiv eB
      ⟨eB.envelopingCounit, eB.comp_envelopingCounit⟩).1 = AInfinityHom.id _ :=
    congrArg Subtype.val ((eB.toAInfinityAugmentation.envelopingHomEquiv eB).apply_symm_apply _)
  simpa only [hc, AInfinityHom.id_comp] using h1

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
