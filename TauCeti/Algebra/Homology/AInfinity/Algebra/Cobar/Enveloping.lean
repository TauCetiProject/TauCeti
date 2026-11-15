/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented

/-!
# The enveloping differential graded algebra of an augmented `A∞` algebra

Given an augmented `A∞` algebra `(A, ε)`, its reduced bar construction `B_∞ A = Tᶜ(s ker ε)` is a
noncounital differential graded coalgebra (`TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_bar`),
and its cobar construction

  `U(A) := Ω B_∞ A = T(s⁻¹ Tᶜ(s ker ε))`

is an augmented differential graded algebra
(`TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`,
`TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`).

Extending the reduced universal `A∞` morphism `ker ε ⟶ Ω Tᶜ(s ker ε)` along the splitting
`A ≃ R · 1_A ⊕ ker ε` produces a canonical strictly unital augmented `A∞` morphism
`toEnveloping : A ⟶ U(A)` (`TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`).  Combining the
unreduced bar--cobar adjunction (`TauCeti.AInfinityAlgebra.cobarAdjunctionEquiv`) on `ker ε` with
the reduced-ideal equivalence (`TauCeti.AInfinityAlgebra.Augmentation.homEquivReduced`) yields its
universal property (`TauCeti.AInfinityAlgebra.Augmentation.envelopingAdjunctionEquiv`): precomposing
with `toEnveloping` identifies morphisms of augmented DG algebras `U(A) ⟶ B` bijectively with
strictly unital augmented `A∞` morphisms `A ⟶ B`.

In particular, when `(A, ε_A)` is already an augmented differential graded algebra, applying this
universal property to the identity `A∞` morphism of `A` produces the canonical strict augmented DG
algebra counit `counitEnveloping : U(A) ⟶ A` (`TauCeti.DGAlgAugmentation.counitEnveloping`), which
retracts `toEnveloping : A ⟶ U(A)` in the category of `A∞` algebras.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping` and
  `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: the enveloping augmented DG
  algebra `U(A) = Ω B_∞ A` of an augmented `A∞` algebra `(A, ε)`.
* `TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`: the universal strictly unital augmented
  `A∞` morphism `A ⟶ U(A)`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingLift`: the DG algebra morphism `U(A) ⟶ B`
  induced by an `A∞` morphism `A ⟶ B`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAdjunctionEquiv`: the bijection between morphisms
  of augmented DG algebras `U(A) ⟶ B` and strictly unital augmented `A∞` morphisms `A ⟶ B`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap`: functoriality of `U(A)` along augmented `A∞`
  morphisms, commuting with `toEnveloping` when the morphism is strictly unital.
* `TauCeti.DGAlgAugmentation.counitEnveloping`: the canonical augmented DG algebra counit
  `U(A) ⟶ A` of an augmented DG algebra, satisfying `counitEnveloping ∘ toEnveloping = id_A`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Sections 2.2 and 9.2.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC

/-! ### Strict-unit helpers -/

namespace AInfinityHom.IsStrictlyUnital

/-- Since strict units of an `A∞` algebra are unique, `IsStrictlyUnital` is independent of the
chosen strict-unit witnesses. -/
theorem congr {R : Type uR} {A : Type uA} {C : Type uC}
    [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    {AA : AInfinityAlgebra R A} {CC : AInfinityAlgebra R C} {f : AInfinityHom AA CC}
    {eA eA' : A} {eC eC' : C}
    {hA : AA.StrictUnit eA} {hA' : AA.StrictUnit eA'}
    {hC : CC.StrictUnit eC} {hC' : CC.StrictUnit eC'}
    (hf : f.IsStrictlyUnital hA hC) : f.IsStrictlyUnital hA' hC' := by
  obtain rfl := hA.eq hA'
  obtain rfl := hC.eq hC'
  exact hf

end AInfinityHom.IsStrictlyUnital

namespace DGAlgHom

/-- A morphism of differential graded algebras is strictly unital as an `A∞` morphism. -/
@[simp]
theorem isStrictlyUnital_toAInfinityHom {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
    {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
    {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} (φ : DGAlgHom hA hB) :
    φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsStrictlyUnital
      hA.strictUnit_one hB.strictUnit_one := by
  rw [← φ.toAInfinityStrictHom_toAInfinityStrictUnitalHom]
  exact φ.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom

end DGAlgHom

/-! ### The enveloping DG algebra and universal `A∞` morphism -/

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [Ring B] [Algebra R B]
  {AA : AInfinityAlgebra R A}

/-- **The enveloping differential graded algebra `U(A) = Ω B_∞ A`** of an augmented `A∞` algebra
`(A, ε)`, defined as the cobar DG algebra of its reduced augmentation ideal `ker ε`. -/
theorem isDGAlgebra_enveloping (ε : AA.Augmentation) :
    IsDGAlgebra
      (tensorAlgebraPiece
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1)))
      (cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
        (deconcatenation R ε.augmentationIdeal) ε.reducedAlgebra.barDifferential) :=
  ε.reducedAlgebra.isDGAlgebra_cobar

/-- The canonical augmentation of the enveloping DG algebra `U(A) = Ω B_∞ A`, sending every
desuspended reduced bar word to zero. -/
noncomputable def envelopingAugmentation (ε : AA.Augmentation) :
    DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

@[simp]
theorem envelopingAugmentation_ι (ε : AA.Augmentation)
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (TensorAlgebra.ι R z) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι z

/-- Every Taylor value of `ε.reducedAlgebra.toCobar` lies in the augmentation ideal of `U(A)`. -/
theorem toCobar_taylor_mem_envelopingAugmentation (ε : AA.Augmentation)
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.reducedAlgebra.toCobar.taylor z ∈
      ε.envelopingAugmentation.toAInfinityAugmentation.augmentationIdeal := by
  rw [ε.envelopingAugmentation.toAInfinityAugmentation.mem_augmentationIdeal]
  simp

/-- The reduced universal `A∞` morphism `ker ε ⟶ ker ε_{U(A)}` obtained by corestricting
`ε.reducedAlgebra.toCobar` to the augmentation ideal of `U(A)`. -/
noncomputable def reducedToEnveloping (ε : AA.Augmentation) :
    AInfinityHom ε.reducedAlgebra
      ε.envelopingAugmentation.toAInfinityAugmentation.reducedAlgebra :=
  ε.reducedAlgebra.toCobar.codRestrictReduced
    ε.envelopingAugmentation.toAInfinityAugmentation
    ε.toCobar_taylor_mem_envelopingAugmentation

@[simp]
theorem subtype_comp_taylor_reducedToEnveloping (ε : AA.Augmentation) :
    ε.envelopingAugmentation.toAInfinityAugmentation.augmentationIdeal.subtype ∘ₗ
        ε.reducedToEnveloping.taylor =
      ε.reducedAlgebra.toCobar.taylor := by
  have h := congrArg AInfinityHom.taylor
    (AInfinityHom.reducedInclusion_comp_codRestrictReduced ε.reducedAlgebra.toCobar
      ε.envelopingAugmentation.toAInfinityAugmentation
      ε.toCobar_taylor_mem_envelopingAugmentation)
  rwa [AInfinityStrictHom.taylor_toAInfinityHom_comp, toLinearMap_reducedInclusion] at h

/-- **The universal strictly unital augmented `A∞` morphism `A ⟶ U(A) = Ω B_∞ A`** from an
augmented `A∞` algebra to its enveloping differential graded algebra. -/
noncomputable def toEnveloping (ε : AA.Augmentation) :
    AInfinityHom AA ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  ε.extendHom ε.envelopingAugmentation.toAInfinityAugmentation ε.reducedToEnveloping

/-- The universal `A∞` morphism `toEnveloping` is strictly unital. -/
theorem isStrictlyUnital_toEnveloping (ε : AA.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit ε.isDGAlgebra_enveloping.strictUnit_one := by
  rw [toEnveloping]
  exact (ε.isStrictlyUnital_extendHom _ _).congr

/-- The universal `A∞` morphism `toEnveloping` commutes with the augmentations. -/
theorem isAugmented_toEnveloping (ε : AA.Augmentation) :
    ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation := by
  rw [toEnveloping]
  exact ε.isAugmented_extendHom _ _

@[simp]
theorem restrictReduced_toEnveloping (ε : AA.Augmentation) :
    ε.isAugmented_toEnveloping.restrictReduced = ε.reducedToEnveloping := by
  refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
  simp [toEnveloping]

/-- Restricting `toEnveloping` to the reduced augmentation ideal `ker ε` recovers the unreduced
universal cobar morphism `ε.reducedAlgebra.toCobar`. -/
@[simp]
theorem toEnveloping_comp_reducedInclusion (ε : AA.Augmentation) :
    ε.toEnveloping.comp ε.reducedInclusion.toAInfinityHom = ε.reducedAlgebra.toCobar := by
  rw [toEnveloping, extendHom_comp_reducedInclusion, reducedToEnveloping,
    AInfinityHom.reducedInclusion_comp_codRestrictReduced]

@[simp]
theorem taylor_toEnveloping (ε : AA.Augmentation) :
    ε.toEnveloping.taylor =
      ε.envelopingAugmentation.toAInfinityAugmentation.unitHom ∘ₗ
          ε.toLinearMap ∘ₗ letter R A +
        TensorAlgebra.ι R ∘ₗ
          (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 ∘ₗ
            ReducedTensorWords.map (R := R) ε.reducedPart := by
  refine LinearMap.ext fun z ↦ ?_
  have h := LinearMap.congr_fun ε.subtype_comp_taylor_reducedToEnveloping
    (ReducedTensorWords.map (R := R) ε.reducedPart z)
  rw [LinearMap.comp_apply, AInfinityAlgebra.taylor_toCobar, LinearMap.comp_apply] at h
  rw [toEnveloping, taylor_extendHom]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h]

/-- On single elements, `toEnveloping` sends `a ∈ A` to `ε(a) · 1 - ι(ofLetter(σ(reducedPart a)))`.
-/
theorem linearPart_toEnveloping_apply (ε : AA.Augmentation) (a : A) :
    ε.toEnveloping.linearPart a =
      ε a • (1 : TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal)) -
        TensorAlgebra.ι R (ofLetter R ε.augmentationIdeal
          (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a))) := by
  have h := LinearMap.congr_fun ε.subtype_comp_taylor_reducedToEnveloping
    (ofLetter R ε.augmentationIdeal (ε.reducedPart a))
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    ← AInfinityHom.linearPart_apply, AInfinityAlgebra.linearPart_toCobar_apply] at h
  rw [toEnveloping, linearPart_extendHom_apply, DGAlgAugmentation.toAInfinityAugmentation_unit,
    h, sub_eq_add_neg]

@[simp]
theorem linearPart_toEnveloping (ε : AA.Augmentation) :
    ε.toEnveloping.linearPart =
      ε.envelopingAugmentation.toAInfinityAugmentation.unitHom ∘ₗ ε.toLinearMap -
        TensorAlgebra.ι R ∘ₗ ofLetter R ε.augmentationIdeal ∘ₗ
          ε.reducedAlgebra.grading.koszulTwist 1 ∘ₗ ε.reducedPart := by
  ext a
  rw [linearPart_toEnveloping_apply]
  simp

/-! ### Universal property of the enveloping DG algebra -/

/-- Lift an `A∞` morphism `f : A ⟶ B` into a unital differential graded algebra to a morphism of
differential graded algebras `U(A) ⟶ B` by applying the cobar adjunction on `ker ε`. -/
noncomputable def envelopingLift (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    DGAlgHom ε.isDGAlgebra_enveloping hB :=
  (ε.reducedAlgebra.cobarAdjunctionEquiv hB).symm (f.comp ε.reducedInclusion.toAInfinityHom)

@[simp]
theorem envelopingLift_ι (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingLift hB f (TensorAlgebra.ι R z) =
      (f.comp ε.reducedInclusion.toAInfinityHom).taylor
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 z) :=
  ε.reducedAlgebra.cobarAdjunctionEquiv_symm_apply_ι hB _ z

/-- When `f : (A, ε) ⟶ (B, εB)` is an augmented `A∞` morphism, its DG algebra lift `U(A) ⟶ B`
commutes with the augmentations. -/
theorem comp_envelopingLift_eq (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB)
    {f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra}
    (hf : f.IsAugmented ε εB.toAInfinityAugmentation) :
    εB.comp (ε.envelopingLift hB f) = ε.envelopingAugmentation := by
  refine ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun z ↦ ?_
  rw [DGAlgHom.comp_apply, envelopingLift_ι, envelopingAugmentation_ι]
  simpa using (εB.toAInfinityAugmentation.mem_augmentationIdeal).mp
    (hf.taylor_comp_reducedInclusion_mem _)

/-- Every DG algebra morphism `φ : U(A) ⟶ B` is recovered by lifting `φ ∘ toEnveloping`. -/
@[simp]
theorem envelopingLift_comp_eq_self (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (φ : DGAlgHom ε.isDGAlgebra_enveloping hB) :
    ε.envelopingLift hB
        (φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping) = φ := by
  symm
  rw [envelopingLift, ε.reducedAlgebra.eq_cobarAdjunctionEquiv_symm_iff,
    AInfinityHom.comp_assoc, ε.toEnveloping_comp_reducedInclusion]

/-- Every strictly unital augmented `A∞` morphism `f : A ⟶ B` into an augmented DG algebra factors
through `toEnveloping` via `envelopingLift`. -/
theorem envelopingLift_comp_toEnveloping (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB)
    {f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra}
    (hfu : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hfa : f.IsAugmented ε εB.toAInfinityAugmentation) :
    (ε.envelopingLift hB f).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.toEnveloping = f := by
  set φ := ε.envelopingLift hB f with hφ
  have hφu := φ.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping
  have hφa := ((DGAlgHom.isAugmented_toAInfinityHom_iff φ).mpr
    (ε.comp_envelopingLift_eq εB hfa)).comp ε.isAugmented_toEnveloping
  have hinc :
      (φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping).comp
          ε.reducedInclusion.toAInfinityHom =
        f.comp ε.reducedInclusion.toAInfinityHom := by
    rw [AInfinityHom.comp_assoc, ε.toEnveloping_comp_reducedInclusion,
      ← ε.reducedAlgebra.cobarAdjunctionEquiv_apply hB φ, hφ, envelopingLift,
      Equiv.apply_symm_apply]
  have hres : hφa.restrictReduced = hfa.restrictReduced := by
    refine AInfinityHom.ext <| LinearMap.ext fun z ↦ ?_
    have hz := congrArg
      (fun k ↦ εB.toAInfinityAugmentation.reducedPart (k.taylor z)) hinc
    simpa only [AInfinityHom.IsAugmented.taylor_restrictReduced, AInfinityHom.taylor_comp,
      AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedInclusion,
      LinearMap.comp_apply] using hz
  rw [← ε.extendHom_restrictReduced εB.toAInfinityAugmentation hφu.congr hφa,
    hres, ε.extendHom_restrictReduced εB.toAInfinityAugmentation hfu.congr hfa]

/-- **Universal property of the enveloping DG algebra `U(A) = Ω B_∞ A`**: precomposing with
`toEnveloping : A ⟶ U(A)` identifies morphisms of augmented differential graded algebras `U(A) ⟶ B`
bijectively with strictly unital augmented `A∞` morphisms `A ⟶ B`. -/
noncomputable def envelopingAdjunctionEquiv (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // εB.comp φ = ε.envelopingAugmentation} ≃
      {f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one ∧
          f.IsAugmented ε εB.toAInfinityAugmentation} where
  toFun φ :=
    ⟨φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
      φ.val.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping,
      ((DGAlgHom.isAugmented_toAInfinityHom_iff φ.val).mpr φ.property).comp
        ε.isAugmented_toEnveloping⟩
  invFun f := ⟨ε.envelopingLift hB f.val, ε.comp_envelopingLift_eq εB f.property.2⟩
  left_inv φ := Subtype.ext (ε.envelopingLift_comp_eq_self φ.val)
  right_inv f := Subtype.ext (ε.envelopingLift_comp_toEnveloping εB f.property.1 f.property.2)

@[simp]
theorem envelopingAdjunctionEquiv_apply (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hB // εB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingAdjunctionEquiv εB φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := (rfl)

@[simp]
theorem envelopingAdjunctionEquiv_symm_apply (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one ∧
        f.IsAugmented ε εB.toAInfinityAugmentation}) :
    ((ε.envelopingAdjunctionEquiv εB).symm f).val = ε.envelopingLift hB f.val := (rfl)

/-- Uniqueness in the universal property: a DG algebra morphism `φ : U(A) ⟶ B` equals
`envelopingLift hB f` precisely when `φ ∘ toEnveloping = f` (for strictly unital augmented `f`). -/
theorem eq_envelopingLift_iff (ε : AA.Augmentation)
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} {hB : IsDGAlgebra ℬ dB}
    (εB : DGAlgAugmentation hB) (φ : DGAlgHom ε.isDGAlgebra_enveloping hB)
    {f : AInfinityHom AA hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra}
    (hfu : f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one)
    (hfa : f.IsAugmented ε εB.toAInfinityAugmentation) :
    φ = ε.envelopingLift hB f ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping = f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · subst h
    exact ε.envelopingLift_comp_toEnveloping εB hfu hfa
  · rw [← h, ε.envelopingLift_comp_eq_self]

end AInfinityAlgebra.Augmentation

/-! ### Functoriality of the enveloping DG algebra -/

namespace AInfinityHom.IsAugmented

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- Functoriality of the enveloping DG algebra `U(A) = Ω B_∞ A` along an augmented `A∞` morphism
`f : (A, ε) ⟶ (B, ε')`. -/
noncomputable def envelopingMap {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    DGAlgHom ε.isDGAlgebra_enveloping ε'.isDGAlgebra_enveloping :=
  hf.restrictReduced.cobarMap

@[simp]
theorem envelopingMap_ι {f : AInfinityHom AA BB} {ε : AA.Augmentation} {ε' : BB.Augmentation}
    (hf : f.IsAugmented ε ε') (z : ReducedTensorWords R ε.augmentationIdeal) :
    hf.envelopingMap (TensorAlgebra.ι R z) = TensorAlgebra.ι R (hf.restrictReduced.barMap z) :=
  hf.restrictReduced.cobarMap_ι z

/-- The induced morphism `envelopingMap` commutes with the canonical cobar augmentations. -/
@[simp]
theorem envelopingAugmentation_comp_envelopingMap {f : AInfinityHom AA BB}
    {ε : AA.Augmentation} {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    ε'.envelopingAugmentation.comp hf.envelopingMap = ε.envelopingAugmentation :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun z ↦ by simp

@[simp]
theorem envelopingMap_id (ε : AA.Augmentation) :
    (AInfinityHom.isAugmented_id ε).envelopingMap = DGAlgHom.id ε.isDGAlgebra_enveloping := by
  simp [envelopingMap]

theorem envelopingMap_comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    {ε : AA.Augmentation} {ε' : BB.Augmentation} {ε'' : CC.Augmentation}
    (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).envelopingMap = hg.envelopingMap.comp hf.envelopingMap := by
  rw [envelopingMap, envelopingMap, envelopingMap, restrictReduced_comp hg hf,
    AInfinityHom.cobarMap_comp]

/-- `hf.envelopingMap` is the enveloping lift of `ε'.toEnveloping ∘ f`. -/
theorem envelopingMap_eq_envelopingLift {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε') :
    hf.envelopingMap =
      ε.envelopingLift ε'.isDGAlgebra_enveloping (ε'.toEnveloping.comp f) := by
  rw [AInfinityAlgebra.Augmentation.envelopingLift,
    ε.reducedAlgebra.eq_cobarAdjunctionEquiv_symm_iff, envelopingMap,
    hf.restrictReduced.cobarMap_comp_toCobar, AInfinityHom.comp_assoc,
    ← hf.reducedInclusion_comp_restrictReduced, ← AInfinityHom.comp_assoc,
    ε'.toEnveloping_comp_reducedInclusion]

/-- Naturality of the universal `A∞` morphism `toEnveloping` along strictly unital augmented `A∞`
morphisms: `U(f) ∘ toEnveloping_A = toEnveloping_B ∘ f`. -/
@[simp]
theorem envelopingMap_comp_toEnveloping {f : AInfinityHom AA BB} {ε : AA.Augmentation}
    {ε' : BB.Augmentation} (hf : f.IsAugmented ε ε')
    (hfu : f.IsStrictlyUnital ε.isStrictUnit ε'.isStrictUnit) :
    hf.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.toEnveloping =
      ε'.toEnveloping.comp f := by
  rw [hf.envelopingMap_eq_envelopingLift]
  exact ε.envelopingLift_comp_toEnveloping ε'.envelopingAugmentation
    (ε'.isStrictlyUnital_toEnveloping.comp hfu) (ε'.isAugmented_toEnveloping.comp hf)

end AInfinityHom.IsAugmented

/-! ### The canonical counit `U(A) ⟶ A` of an augmented DG algebra -/

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}

/-- **The canonical augmented DG algebra counit `U(A) = Ω B_∞ A ⟶ A`** of an augmented differential
graded algebra `(A, ε_A)`, corresponding to the identity `A∞` morphism of `A` under the universal
property of the enveloping DG algebra. -/
noncomputable def counitEnveloping (εA : DGAlgAugmentation hA) :
    DGAlgHom εA.toAInfinityAugmentation.isDGAlgebra_enveloping hA :=
  εA.toAInfinityAugmentation.envelopingLift hA
    (AInfinityHom.id hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)

/-- The counit `counitEnveloping : U(A) ⟶ A` preserves the augmentations. -/
@[simp]
theorem comp_counitEnveloping (εA : DGAlgAugmentation hA) :
    εA.comp εA.counitEnveloping = εA.toAInfinityAugmentation.envelopingAugmentation :=
  εA.toAInfinityAugmentation.comp_envelopingLift_eq εA
    (AInfinityHom.isAugmented_id εA.toAInfinityAugmentation)

/-- Composing the strict DG algebra counit `U(A) ⟶ A` with the universal `A∞` morphism `A ⟶ U(A)`
recovers the identity `A∞` morphism of `A`. -/
@[simp]
theorem counitEnveloping_comp_toEnveloping (εA : DGAlgAugmentation hA) :
    εA.counitEnveloping.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        εA.toAInfinityAugmentation.toEnveloping =
      AInfinityHom.id hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  εA.toAInfinityAugmentation.envelopingLift_comp_toEnveloping εA
    (AInfinityHom.isStrictlyUnital_id hA.strictUnit_one).congr
    (AInfinityHom.isAugmented_id εA.toAInfinityAugmentation)

/-- On desuspended reduced bar words, `counitEnveloping` projects onto single letters (with the
desuspension Koszul twist) and vanishes on words of length at least two. -/
@[simp]
theorem counitEnveloping_ι (εA : DGAlgAugmentation hA)
    (z : ReducedTensorWords R εA.toAInfinityAugmentation.augmentationIdeal) :
    εA.counitEnveloping (TensorAlgebra.ι R z) =
      (letter R εA.toAInfinityAugmentation.augmentationIdeal
        ((ReducedTensorWords.grading
          (εA.toAInfinityAugmentation.reducedAlgebra.grading.shift 1)).koszulTwist 1 z) : A) := by
  simp [counitEnveloping]

end DGAlgAugmentation

end TauCeti
