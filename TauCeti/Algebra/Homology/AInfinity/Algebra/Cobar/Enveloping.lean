/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented.Lift
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.Augmentation

/-!
# The enveloping differential graded algebra of an augmented `A∞` algebra

Given an augmented `A∞` algebra `(A, ε)` over a commutative ring `R`, its reduced augmentation
ideal `ker ε` carries a nonunital `A∞` algebra structure `ε.reducedAlgebra`, so its reduced bar
construction `B∞ A = Tᶜ(s ker ε)` is a noncounital DG coalgebra. Applying the cobar construction
produces the **enveloping differential graded algebra** `U(A, ε) = Ω B∞ A = Ω Tᶜ(s ker ε)`
(`TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`), equipped with the canonical cobar
augmentation `ε.envelopingAugmentation : U(A, ε) → R`.

Combining `TauCeti.AInfinityAlgebra.cobarBarHomEquiv`, the canonical cobar augmentation, the kernel
universal property of `ker e_B ↪ B`, and the splitting equivalence between `A∞` morphisms
`ker ε ⟶ ker e_B` and strictly unital augmented `A∞` morphisms `A ⟶ B` yields the **enveloping
adjunction** (`TauCeti.AInfinityAlgebra.Augmentation.envelopingAdjunctionEquiv`) and universal
strictly unital augmented morphism `ε.universalEnvelopingHom : A ⟶ U(A, ε)`.

## Main definitions

* `TauCeti.AInfinityAlgebra.augmentedCobarAdjunctionEquiv`: bijection between
  augmentation-preserving DG algebra maps `Ω Tᶜ(sA) → B` and `A∞` morphisms `A ⟶ ker e_B`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: canonical augmentation of
  `U(A, ε) = Ω Tᶜ(s ker ε)`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAdjunctionEquiv`,
  `universalEnvelopingHom`, and `envelopingLift`: the enveloping adjunction, universal morphism
  `A ⟶ U(A, ε)`, and universal DG algebra lift `U(A, ε) → B`.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`: `U(A, ε)` is a DG algebra.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom`
  and `eq_envelopingLift_iff`: universal factorization through `universalEnvelopingHom`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6; *A-infinity algebras,
  modules and functor categories*, Contemp. Math. 406 (2006), Section 4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 9.2.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uA uB uC

section AugmentedCobar

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A]
  [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}

namespace AInfinityAlgebra

private theorem taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist (𝒜 : AInfinityAlgebra R A)
    (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    ((𝒜.cobarBarHomEquiv hB).symm φ).taylor =
      ((φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] B) ∘ₗ ι R) ∘ₗ
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 := by
  rw [𝒜.cobarBarHomEquiv_symm_apply hB φ, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    𝒜.taylor_toCobarBar]
  ext z
  simp

private theorem linearPart_cobarBarHomEquiv_symm (𝒜 : AInfinityAlgebra R A)
    (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) (a : A) :
    ((𝒜.cobarBarHomEquiv hB).symm φ).linearPart a =
      -φ (ι R (ReducedTensorWords.ofLetter R A (𝒜.grading.koszulTwist 1 a))) := by
  rw [AInfinityHom.linearPart_apply, taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist 𝒜 hB φ,
    LinearMap.comp_apply, ReducedTensorWords.koszulTwist_grading,
    ReducedTensorWords.map_ofLetter, InternalGrading.koszulTwist_one_shift_one,
    LinearMap.neg_apply, map_neg, LinearMap.comp_apply, map_neg, map_neg]
  rfl

private theorem cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist (𝒜 : AInfinityAlgebra R A)
    (hB : IsDGAlgebra ℬ dB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (z : ReducedTensorWords R A) :
    𝒜.cobarBarHomEquiv hB f (ι R z) =
      f.taylor ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) := by
  have hg := f.isHomogeneous_taylor
  rw [← ReducedTensorWords.grading_piece] at hg
  have h := hg.koszulTwist_apply 1 z
  rw [InternalGrading.koszulTwist_one_shift_one,
    IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading] at h
  simpa [𝒜.cobarBarHomEquiv_apply_ι hB f z] using h

/-- Under `cobarBarHomEquiv.symm`, a DG algebra morphism `φ : Ω Tᶜ(sA) → B` commutes with the
augmentations if and only if the suspended Taylor map of `(cobarBarHomEquiv hB).symm φ` takes
values in `ker e_B`. -/
theorem comp_eq_cobarAugmentation_iff_taylor_mem (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    eB.comp φ = 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation ↔
      ∀ z, ((𝒜.cobarBarHomEquiv hB).symm φ).taylor z ∈
        eB.toAInfinityAugmentation.augmentationIdeal := by
  rw [𝒜.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eB]
  set κ := (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1
  constructor
  · intro hφ z
    rw [eB.mem_toAInfinityAugmentation_augmentationIdeal,
      taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist 𝒜 hB φ]
    exact hφ (κ z)
  · intro ht z
    have hz := ht (κ z)
    rw [eB.mem_toAInfinityAugmentation_augmentationIdeal,
      taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist 𝒜 hB φ,
      LinearMap.comp_apply, LinearMap.comp_apply, InternalGrading.koszulTwist_koszulTwist] at hz
    exact hz

/-- **Augmented bar--cobar adjunction for nonunital `A∞` sources**: augmentation-preserving DG
algebra morphisms `(Ω Tᶜ(sA), ε_Ω) → (B, e_B)` correspond bijectively to `A∞` morphisms
`A ⟶ ker e_B`. -/
noncomputable def augmentedCobarAdjunctionEquiv (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation} ≃
      AInfinityHom 𝒜 eB.toAInfinityAugmentation.reducedAlgebra :=
  { toFun := fun φ ↦
      eB.toAInfinityAugmentation.liftToReduced ((𝒜.cobarBarHomEquiv hB).symm φ.val)
        ((𝒜.comp_eq_cobarAugmentation_iff_taylor_mem eB φ.val).1 φ.property)
    invFun := fun g ↦
      ⟨𝒜.cobarBarHomEquiv hB (eB.toAInfinityAugmentation.idealValuedHomEquiv 𝒜 g).val,
        (𝒜.comp_eq_cobarAugmentation_iff_taylor_mem eB _).2 (by
          rw [Equiv.symm_apply_apply]
          exact (eB.toAInfinityAugmentation.idealValuedHomEquiv 𝒜 g).property)⟩
    left_inv := fun φ ↦ Subtype.ext <| by
      simp only [AInfinityAlgebra.Augmentation.idealValuedHomEquiv_apply,
        AInfinityAlgebra.Augmentation.inclusionStrictHom_comp_liftToReduced,
        Equiv.apply_symm_apply]
    right_inv := fun g ↦ by
      simp only [Equiv.symm_apply_apply, AInfinityAlgebra.Augmentation.idealValuedHomEquiv_apply,
        AInfinityAlgebra.Augmentation.liftToReduced_inclusionStrictHom_comp] }

/-- Composing the Taylor map of `augmentedCobarAdjunctionEquiv φ` with the inclusion
`ker e_B ↪ B` gives `(φ ∘ ι) ∘ κ`. -/
@[simp]
theorem subtype_comp_taylor_augmentedCobarAdjunctionEquiv (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation}) :
    eB.toAInfinityAugmentation.augmentationIdeal.subtype ∘ₗ
        (𝒜.augmentedCobarAdjunctionEquiv eB φ).taylor =
      ((φ.val : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] B) ∘ₗ ι R) ∘ₗ
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 := by
  rw [augmentedCobarAdjunctionEquiv, Equiv.coe_fn_mk]
  have hinc := eB.toAInfinityAugmentation.inclusionStrictHom_comp_liftToReduced
    ((𝒜.cobarBarHomEquiv hB).symm φ.val)
    ((𝒜.comp_eq_cobarAugmentation_iff_taylor_mem eB φ.val).1 φ.property)
  have ht := congrArg AInfinityHom.taylor hinc
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap] at ht
  exact ht.trans (taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist 𝒜 hB φ.val)

/-- In `B`, the linear part of `augmentedCobarAdjunctionEquiv φ` evaluates `φ` on minus the
Koszul-twisted single-letter generator. -/
theorem coe_linearPart_augmentedCobarAdjunctionEquiv (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation}) (a : A) :
    ((𝒜.augmentedCobarAdjunctionEquiv eB φ).linearPart a : B) =
      -φ.val (ι R (ReducedTensorWords.ofLetter R A (𝒜.grading.koszulTwist 1 a))) := by
  have ht := LinearMap.congr_fun
    (𝒜.subtype_comp_taylor_augmentedCobarAdjunctionEquiv eB φ)
    (ReducedTensorWords.ofLetter R A a)
  rw [← taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist 𝒜 hB φ.val, LinearMap.comp_apply,
    Submodule.subtype_apply, ← AInfinityHom.linearPart_apply, ← AInfinityHom.linearPart_apply,
    linearPart_cobarBarHomEquiv_symm 𝒜 hB φ.val a] at ht
  exact ht

/-- Under `augmentedCobarAdjunctionEquiv.symm`, the induced DG algebra morphism acts on each
desuspended bar word by the Koszul-twisted Taylor map of `g`. -/
@[simp]
theorem augmentedCobarAdjunctionEquiv_symm_apply_ι (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (g : AInfinityHom 𝒜 eB.toAInfinityAugmentation.reducedAlgebra)
    (z : ReducedTensorWords R A) :
    ((𝒜.augmentedCobarAdjunctionEquiv eB).symm g).val (ι R z) =
      (g.taylor ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) : B) := by
  rw [augmentedCobarAdjunctionEquiv, Equiv.coe_fn_symm_mk,
    cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist 𝒜 hB,
    AInfinityAlgebra.Augmentation.idealValuedHomEquiv_apply,
    AInfinityStrictHom.taylor_toAInfinityHom_comp,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
    LinearMap.comp_apply, Submodule.subtype_apply]

end AInfinityAlgebra

end AugmentedCobar

section Enveloping

variable {R : Type uR} {A : Type uA}
  [CommRing R] [AddCommGroup A] [Module R A] {𝒜 : AInfinityAlgebra R A}

namespace AInfinityAlgebra.Augmentation

/-- **The enveloping differential graded algebra** `U(A, ε) = Ω Tᶜ(s ker ε)` of an augmented
`A∞` algebra `(A, ε)`, obtained by applying the cobar construction to the reduced bar DG
coalgebra of `ε.reducedAlgebra`. -/
theorem isDGAlgebra_enveloping (ε : 𝒜.Augmentation) :
    IsDGAlgebra
      (tensorAlgebraPiece
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1)))
      (cobarDifferential
        (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
        (ReducedTensorWords.deconcatenation R ε.augmentationIdeal)
        ε.reducedAlgebra.barDifferential) :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- The canonical DG algebra augmentation `U(A, ε) → R` of the enveloping DG algebra, sending
every desuspended reduced bar word to zero. -/
noncomputable def envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- Unfolding characterization of `envelopingAugmentation` as the cobar augmentation of the
reduced bar coalgebra. -/
theorem envelopingAugmentation_eq (ε : 𝒜.Augmentation) :
    ε.envelopingAugmentation =
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation := (rfl)

/-- The canonical augmentation of `U(A, ε)` annihilates every desuspended bar word. -/
@[simp]
theorem envelopingAugmentation_ι (ε : 𝒜.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (ι R w) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι w

/-- Every desuspended bar word lies in the augmentation ideal of `U(A, ε)`. -/
theorem ι_mem_envelopingAugmentationIdeal (ε : 𝒜.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ι R w ∈ ε.envelopingAugmentation.augmentationIdeal :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.ι_mem_cobarAugmentationIdeal w

section Target

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B}

/-- **The enveloping DG algebra adjunction**: for an augmented `A∞` algebra `(A, ε)` and an
augmented DG algebra `(B, e_B)`, augmentation-preserving DG algebra morphisms `U(A, ε) → B`
correspond bijectively to strictly unital augmented `A∞` morphisms `A ⟶ B`. -/
noncomputable def envelopingAdjunctionEquiv (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one ∧
          f.IsAugmented ε eB.toAInfinityAugmentation} :=
  ((ε.reducedAlgebra.augmentedCobarAdjunctionEquiv eB).trans
    (ε.strictlyUnitalAugmentedHomEquiv eB.toAInfinityAugmentation).symm).trans
    (Equiv.subtypeEquivRight fun f ↦
      and_congr_left' (eB.isStrictlyUnital_toAInfinityAugmentation_iff f))

/-- In the underlying `A∞` morphism type, `envelopingAdjunctionEquiv` lifts the reduced morphism
`augmentedCobarAdjunctionEquiv` along the augmentation splitting. -/
theorem envelopingAdjunctionEquiv_apply_val (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv eB φ).val =
      ε.liftHom eB.toAInfinityAugmentation
        (ε.reducedAlgebra.augmentedCobarAdjunctionEquiv eB
          ⟨φ.val, φ.property.trans ε.envelopingAugmentation_eq⟩) := by
  cases φ with | mk φ hφ =>
  unfold envelopingAdjunctionEquiv envelopingAugmentation at *
  simp

/-- In the underlying DG algebra morphism type, `envelopingAdjunctionEquiv.symm` applies
`augmentedCobarAdjunctionEquiv.symm` to the reduced restriction of `f`. -/
theorem envelopingAdjunctionEquiv_symm_apply_val (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one ∧
        f.IsAugmented ε eB.toAInfinityAugmentation}) :
    ((ε.envelopingAdjunctionEquiv eB).symm f).val =
      ((ε.reducedAlgebra.augmentedCobarAdjunctionEquiv eB).symm f.property.2.reducedHom).val := by
  cases f with | mk f hf =>
  unfold envelopingAdjunctionEquiv envelopingAugmentation at *
  simp

/-- The suspended Taylor map of `envelopingAdjunctionEquiv e_B φ` adds the scalar augmentation part
on one-letter words to the Koszul-twisted action of `φ ∘ ι` on the reduced projection of bar
words. -/
@[simp]
theorem taylor_envelopingAdjunctionEquiv (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv eB φ).val.taylor =
      Algebra.linearMap R B ∘ₗ ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A +
        (((φ.val : TensorAlgebra R
              (ReducedTensorWords R ε.augmentationIdeal) →ₗ[R] B) ∘ₗ ι R) ∘ₗ
            (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1) ∘ₗ
          ReducedTensorWords.map (R := R) ε.reducedPart := by
  rw [ε.envelopingAdjunctionEquiv_apply_val, taylor_liftHom,
    DGAlgAugmentation.toAInfinityAugmentation_unitHom]
  congr 1
  rw [← LinearMap.comp_assoc,
    ε.reducedAlgebra.subtype_comp_taylor_augmentedCobarAdjunctionEquiv]

/-- The linear part of `envelopingAdjunctionEquiv e_B φ` maps the strict unit of `A` to `1`. -/
theorem linearPart_envelopingAdjunctionEquiv_unit (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv eB φ).val.linearPart ε.unit = 1 :=
  (ε.envelopingAdjunctionEquiv eB φ).property.1.map_unit

/-- On `ker ε`, the linear part of `envelopingAdjunctionEquiv e_B φ` evaluates `φ` on minus the
Koszul-twisted single-letter generator. -/
theorem linearPart_envelopingAdjunctionEquiv_coe (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation})
    (x : ε.augmentationIdeal) :
    (ε.envelopingAdjunctionEquiv eB φ).val.linearPart (x : A) =
      -φ.val (ι R (ReducedTensorWords.ofLetter R ε.augmentationIdeal
        (ε.reducedAlgebra.grading.koszulTwist 1 x))) := by
  rw [ε.envelopingAdjunctionEquiv_apply_val, ε.linearPart_liftHom_coe,
    ε.reducedAlgebra.coe_linearPart_augmentedCobarAdjunctionEquiv]

/-- Under `envelopingAdjunctionEquiv.symm`, the induced DG algebra morphism acts on each
desuspended reduced bar word by the Koszul-twisted Taylor map of `f`. -/
@[simp]
theorem envelopingAdjunctionEquiv_symm_apply_ι (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one ∧
        f.IsAugmented ε eB.toAInfinityAugmentation})
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ((ε.envelopingAdjunctionEquiv eB).symm f).val (ι R w) =
      f.val.taylor
        (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
          ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 w)) := by
  rw [ε.envelopingAdjunctionEquiv_symm_apply_val,
    ε.reducedAlgebra.augmentedCobarAdjunctionEquiv_symm_apply_ι,
    AInfinityHom.IsAugmented.taylor_reducedHom, LinearMap.comp_apply]
  exact congrArg Subtype.val
    (eB.toAInfinityAugmentation.reducedPart_coe ⟨_, f.property.2.taylor_map_subtype_mem _⟩)

end Target

/-- **The universal strictly unital augmented `A∞` morphism** `A ⟶ U(A, ε)` into the enveloping
DG algebra, corresponding to the identity DG algebra morphism of `U(A, ε)`. -/
noncomputable def universalEnvelopingHom (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜
      (IsDGAlgebra.toIsNonUnitalDGAlgebra ε.isDGAlgebra_enveloping).toAInfinityAlgebra :=
  (ε.envelopingAdjunctionEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).val

/-- The universal morphism `universalEnvelopingHom` is strictly unital. -/
theorem isStrictlyUnital_universalEnvelopingHom (ε : 𝒜.Augmentation) :
    ε.universalEnvelopingHom.IsStrictlyUnital
      ε.isStrictUnit ε.isDGAlgebra_enveloping.strictUnit_one :=
  (ε.envelopingAdjunctionEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).property.1

/-- The universal morphism `universalEnvelopingHom` commutes with the augmentations. -/
theorem isAugmented_universalEnvelopingHom (ε : 𝒜.Augmentation) :
    ε.universalEnvelopingHom.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.envelopingAdjunctionEquiv ε.envelopingAugmentation
    ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).property.2

/-- The suspended Taylor map of `universalEnvelopingHom` sends a bar word to its scalar
augmentation on single letters plus the Koszul-twisted cobar generator of its reduced
projection. -/
@[simp]
theorem taylor_universalEnvelopingHom (ε : 𝒜.Augmentation) :
    ε.universalEnvelopingHom.taylor =
      Algebra.linearMap R (TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal)) ∘ₗ
          ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A +
        (ι R ∘ₗ
            (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1) ∘ₗ
          ReducedTensorWords.map (R := R) ε.reducedPart := by
  refine LinearMap.ext fun z ↦ ?_
  simp [universalEnvelopingHom]

/-- `universalEnvelopingHom` sends the strict unit of `A` to `1`. -/
theorem linearPart_universalEnvelopingHom_unit (ε : 𝒜.Augmentation) :
    ε.universalEnvelopingHom.linearPart ε.unit = 1 :=
  ε.isStrictlyUnital_universalEnvelopingHom.map_unit

/-- On `ker ε`, the linear part of `universalEnvelopingHom` sends `x` to minus the generator of
the Koszul-twisted single letter `[σ x]`. -/
theorem linearPart_universalEnvelopingHom_coe (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.universalEnvelopingHom.linearPart (x : A) =
      -ι R (ReducedTensorWords.ofLetter R ε.augmentationIdeal
        (ε.reducedAlgebra.grading.koszulTwist 1 x)) := by
  simpa [universalEnvelopingHom] using
    ε.linearPart_envelopingAdjunctionEquiv_coe ε.envelopingAugmentation
      ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩ x

section Factorization

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B}

/-- **Universal factorization for the enveloping DG algebra**: every `envelopingAdjunctionEquiv`
image is obtained by postcomposing `universalEnvelopingHom` with the augmentation-preserving DG
algebra morphism regarded as a strict `A∞` morphism. -/
theorem envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv eB φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.universalEnvelopingHom := by
  apply AInfinityHom.ext
  rw [ε.taylor_envelopingAdjunctionEquiv, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    ε.taylor_universalEnvelopingHom]
  refine LinearMap.ext fun z ↦ ?_
  simp [AlgHomClass.commutes]

/-- Naturality of `envelopingAdjunctionEquiv` in the target augmented DG algebra. -/
theorem envelopingAdjunctionEquiv_comp {C : Type uC} [Ring C] [Algebra R C]
    {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}
    (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
    (eB : DGAlgAugmentation hB) (eC : DGAlgAugmentation hC)
    (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv eC
        ⟨ψ.comp φ.val, by rw [← DGAlgHom.comp_assoc, hψ, φ.property]⟩).val =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (ε.envelopingAdjunctionEquiv eB φ).val := by
  rw [ε.envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom,
    ε.envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc]

/-- Lift a strictly unital augmented `A∞` morphism `f : A ⟶ B` into an augmented DG algebra to
an augmentation-preserving DG algebra morphism `U(A, ε) → B`. -/
noncomputable def envelopingLift (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (hf_unit : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hf_aug : f.IsAugmented ε eB.toAInfinityAugmentation) :
    DGAlgHom ε.isDGAlgebra_enveloping hB :=
  ((ε.envelopingAdjunctionEquiv eB).symm ⟨f, hf_unit, hf_aug⟩).val

/-- `envelopingLift` commutes with the DG algebra augmentations. -/
@[simp]
theorem comp_envelopingLift (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (hf_unit : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hf_aug : f.IsAugmented ε eB.toAInfinityAugmentation) :
    eB.comp (ε.envelopingLift eB f hf_unit hf_aug) = ε.envelopingAugmentation :=
  ((ε.envelopingAdjunctionEquiv eB).symm ⟨f, hf_unit, hf_aug⟩).property

/-- On each desuspended reduced bar word, `envelopingLift` evaluates the Koszul-twisted Taylor map
of `f`. -/
@[simp]
theorem envelopingLift_ι (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (hf_unit : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hf_aug : f.IsAugmented ε eB.toAInfinityAugmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingLift eB f hf_unit hf_aug (ι R w) =
      f.taylor
        (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
          ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 w)) :=
  ε.envelopingAdjunctionEquiv_symm_apply_ι eB ⟨f, hf_unit, hf_aug⟩ w

/-- Restricting `envelopingLift` along `universalEnvelopingHom` recovers `f`. -/
@[simp]
theorem envelopingLift_comp_universalEnvelopingHom (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (hf_unit : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hf_aug : f.IsAugmented ε eB.toAInfinityAugmentation) :
    (ε.envelopingLift eB f hf_unit
        hf_aug).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.universalEnvelopingHom = f := by
  have h := ε.envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom eB
    ((ε.envelopingAdjunctionEquiv eB).symm ⟨f, hf_unit, hf_aug⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- **Universal property of the enveloping DG algebra**: an augmentation-preserving DG algebra
morphism `φ : U(A, ε) → B` restricts along `universalEnvelopingHom` to `f` if and only if
`φ = envelopingLift e_B f`. -/
theorem eq_envelopingLift_iff (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB} (hφ : eB.comp φ = ε.envelopingAugmentation)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (hf_unit : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hf_aug : f.IsAugmented ε eB.toAInfinityAugmentation) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.universalEnvelopingHom = f ↔
      φ = ε.envelopingLift eB f hf_unit hf_aug := by
  rw [← ε.envelopingAdjunctionEquiv_eq_comp_universalEnvelopingHom eB ⟨φ, hφ⟩]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hsub : ε.envelopingAdjunctionEquiv eB ⟨φ, hφ⟩ = ⟨f, hf_unit, hf_aug⟩ :=
      Subtype.ext h
    exact congrArg Subtype.val (((ε.envelopingAdjunctionEquiv eB).eq_symm_apply).2 hsub)
  · subst h
    exact congrArg Subtype.val
      ((ε.envelopingAdjunctionEquiv eB).apply_symm_apply ⟨f, hf_unit, hf_aug⟩)

end Factorization

end AInfinityAlgebra.Augmentation

end Enveloping

end TauCeti
