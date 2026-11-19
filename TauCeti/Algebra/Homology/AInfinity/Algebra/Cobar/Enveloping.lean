/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.Augmentation

/-!
# The enveloping differential graded algebra of an augmented `A∞` algebra

For an augmented `A∞` algebra `(A, ε)`, whereas the unreduced cobar construction `Ω Tᶜ(sA)`
classifies nonunital `A∞` morphisms out of `A`, forming the cobar construction
`U(A, ε) = Ω B_∞ A = T(s⁻¹ Tᶜ(s(ker ε)))` on the reduced bar coalgebra of `ker ε` eliminates
unit-containing bar words and carries the canonical augmentation
`ε.envelopingAugmentation : U(A, ε) ⟶ R`.

Together with the universal strictly unital `A∞` morphism `ε.toEnveloping : A ⟶ U(A, ε)`,
`U(A, ε)` represents strictly unital `A∞` morphisms `(A, ε) ⟶ B` into any unital DG algebra `B`
(`AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv`, `bijective_comp_toEnveloping`).
Restricting to augmentation-preserving morphisms yields `augmentedEnvelopingDGAlgHomEquiv` and
`bijective_augmented_comp_toEnveloping`.  Applying `cobarBarMap` to the induced morphism on reduced
augmentation ideals makes `U(A, ε)` functorial (`AInfinityHom.IsAugmented.envelopingMap`).

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: the canonical augmentation
  `U(A, ε) ⟶ R`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv`: the universal-property bijection
  between DG algebra maps `U(A, ε) ⟶ B` and strictly unital `A∞` morphisms `(A, ε) ⟶ B`.
* `TauCeti.AInfinityAlgebra.Augmentation.augmentedEnvelopingDGAlgHomEquiv`: the augmented
  universal-property bijection between augmented DG algebra maps `U(A, ε) ⟶ B` and strictly unital
  augmented `A∞` morphisms `(A, ε) ⟶ (B, ε_B)`.
* `TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`: the canonical strictly unital augmented
  `A∞` morphism `A ⟶ U(A, ε)`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap`: functoriality `U(A, ε) ⟶ U(A', ε')` along
  augmented `A∞` morphisms.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.taylor_toEnveloping`: Taylor formula for `ε.toEnveloping`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping` and
  `TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping`: **the universal property of
  `U(A, ε)`** among strictly unital `A∞` morphisms into unital DG algebras.
* `TauCeti.AInfinityAlgebra.Augmentation.augmentedEnvelopingDGAlgHomEquiv_eq_comp_toEnveloping`
  and `TauCeti.AInfinityAlgebra.Augmentation.bijective_augmented_comp_toEnveloping`: the augmented
  universal property of `(U(A, ε), ε.envelopingAugmentation)`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap_comp_toEnveloping`: naturality of `toEnveloping`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

namespace TauCeti

open TensorAlgebra ReducedTensorWords

universe uR uA uA' uA'' uB uC

variable {R : Type uR} {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {B : Type uB} {C : Type uC}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup A''] [Module R A''] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C}

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A}

/-! ### The canonical augmentation of `U(A, ε)` -/

/-- The canonical DG algebra augmentation `U(A, ε) = Ω Tᶜ(s(ker ε)) ⟶ R` of the enveloping DG
algebra of an augmented `A∞` algebra. -/
noncomputable abbrev envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-! ### Universal property of `U(A, ε)` for strictly unital `A∞` morphisms -/

/-- **Universal property of the enveloping DG algebra `U(A, ε) = Ω B_∞ A`**: DG algebra morphisms
`U(A, ε) ⟶ B` into any unital DG algebra `B` correspond bijectively to strictly unital `A∞`
morphisms `(A, ε) ⟶ B`. -/
noncomputable def envelopingDGAlgHomEquiv (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ≃
      {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one} :=
  (ε.reducedAlgebra.cobarBarHomEquiv hB).symm.trans
    (ε.strictlyUnitalHomEquiv hB.strictUnit_one).symm

/-- Restricting `ε.envelopingDGAlgHomEquiv hB φ` to `ker ε` gives the nonunital bar--cobar morphism
(`cobarBarHomEquiv`) of `φ` on `ker ε`. -/
@[simp] theorem envelopingDGAlgHomEquiv_comp_inclusion (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (ε.envelopingDGAlgHomEquiv hB φ).val.comp ε.inclusion.toAInfinityHom =
      (ε.reducedAlgebra.cobarBarHomEquiv hB).symm φ := by simp [envelopingDGAlgHomEquiv]

/-- The DG algebra morphism `(ε.envelopingDGAlgHomEquiv hB).symm f` is the nonunital cobar lift
(`cobarBarHomEquiv`) of `f` restricted to `ker ε`. -/
@[simp] theorem envelopingDGAlgHomEquiv_symm_apply (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one}) :
    (ε.envelopingDGAlgHomEquiv hB).symm f =
      ε.reducedAlgebra.cobarBarHomEquiv hB (f.val.comp ε.inclusion.toAInfinityHom) := by
  simp [envelopingDGAlgHomEquiv]

/-- The **universal strictly unital augmented `A∞` morphism** `A ⟶ U(A, ε)` into the enveloping
differential graded algebra `U(A, ε) = Ω Tᶜ(s(ker ε))`. -/
noncomputable def toEnveloping (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜 (IsNonUnitalDGAlgebra.toAInfinityAlgebra (IsDGAlgebra.toIsNonUnitalDGAlgebra
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential)) :=
  (ε.envelopingDGAlgHomEquiv _ (DGAlgHom.id _)).val

/-- The universal morphism `ε.toEnveloping : A ⟶ U(A, ε)` is strictly unital. -/
@[simp] theorem isStrictlyUnital_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit (IsDGAlgebra.strictUnit_one
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential) :=
  (ε.envelopingDGAlgHomEquiv _ (DGAlgHom.id _)).property

/-- Under `envelopingDGAlgHomEquiv`, the identity morphism of `U(A, ε)` maps to `ε.toEnveloping`. -/
@[simp] theorem envelopingDGAlgHomEquiv_id (ε : 𝒜.Augmentation) :
    ε.envelopingDGAlgHomEquiv _ (DGAlgHom.id _) =
      ⟨ε.toEnveloping, ε.isStrictlyUnital_toEnveloping⟩ := (rfl)

/-- Restricting `ε.toEnveloping` to `ker ε` recovers `ε.reducedAlgebra.toCobarBar`. -/
@[simp] theorem toEnveloping_comp_inclusion (ε : 𝒜.Augmentation) :
    ε.toEnveloping.comp ε.inclusion.toAInfinityHom = ε.reducedAlgebra.toCobarBar := by
  rw [toEnveloping, envelopingDGAlgHomEquiv_comp_inclusion, cobarBarHomEquiv_symm_id]

/-- On any bar word, `ε.toEnveloping.taylor` splits into the scalar augmentation of its single
letter plus the Koszul-twisted generator on its reduced bar word. -/
@[simp] theorem taylor_toEnveloping (ε : 𝒜.Augmentation) (z : ReducedTensorWords R A) :
    ε.toEnveloping.taylor z = algebraMap R _ (ε (letter R A z)) +
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
        (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
  have hcomp := congrArg (fun f ↦ f.taylor (ReducedTensorWords.map (R := R) ε.reducedPart z))
    ε.toEnveloping_comp_inclusion
  simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    LinearMap.comp_apply, taylor_toCobarBar] at hcomp
  rw [ε.isStrictlyUnital_toEnveloping.taylor_apply z, hcomp, ← Algebra.algebraMap_eq_smul_one]

/-- The linear part of `ε.toEnveloping` subtracts the Koszul-twisted single-letter generator of
`ε.reducedPart` from the scalar augmentation. -/
@[simp] theorem linearPart_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.linearPart = Algebra.linearMap R _ ∘ₗ ε.toLinearMap -
      ι R ∘ₗ ofLetter R _ ∘ₗ ε.reducedAlgebra.grading.koszulTwist 1 ∘ₗ ε.reducedPart :=
  LinearMap.ext fun _ ↦ by
    simp [koszulTwist_grading, InternalGrading.koszulTwist_one_shift_one, sub_eq_add_neg]

/-- Every strictly unital `A∞` morphism corresponding to `φ : U(A, ε) ⟶ B` factors as `φ` after
the universal morphism `ε.toEnveloping`. -/
theorem envelopingDGAlgHomEquiv_eq_comp_toEnveloping (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (ε.envelopingDGAlgHomEquiv hB φ).val =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  refine (ε.envelopingDGAlgHomEquiv hB φ).property.ext_comp_inclusion
    (AInfinityHom.IsStrictlyUnital.comp
      (by simpa using φ.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom)
      ε.isStrictlyUnital_toEnveloping) ?_
  rw [envelopingDGAlgHomEquiv_comp_inclusion, AInfinityHom.comp_assoc, toEnveloping_comp_inclusion,
    cobarBarHomEquiv_symm_apply]

/-- Universal factorization characterization of `U(A, ε)`: a DG algebra morphism
`φ : U(A, ε) ⟶ B` is the lift of a strictly unital `A∞` morphism `f : A ⟶ B` if and only if
`φ ∘ ε.toEnveloping = f`. -/
theorem eq_envelopingDGAlgHomEquiv_symm_iff (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one}) :
    φ = (ε.envelopingDGAlgHomEquiv hB).symm f ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping = f.val := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, envelopingDGAlgHomEquiv_eq_comp_toEnveloping]

/-- **Universal property of `U(A, ε)`**: every strictly unital `A∞` morphism from `(A, ε)` to a
unital DG algebra `B` factors through `ε.toEnveloping` by a unique DG algebra morphism
`U(A, ε) ⟶ B`. -/
theorem bijective_comp_toEnveloping (ε : 𝒜.Augmentation) (hB : IsDGAlgebra ℬ dB) :
    Function.Bijective fun φ :
        DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB ↦
      (⟨φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        AInfinityHom.IsStrictlyUnital.comp
          (by simpa using φ.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom)
          ε.isStrictlyUnital_toEnveloping⟩ :
        {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one}) := by
  convert (ε.envelopingDGAlgHomEquiv hB).bijective using 1
  exact funext fun φ ↦ Subtype.ext (ε.envelopingDGAlgHomEquiv_eq_comp_toEnveloping hB φ).symm

/-- `envelopingDGAlgHomEquiv` is natural with respect to DG algebra morphisms in the target. -/
@[simp] theorem envelopingDGAlgHomEquiv_comp_left (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    {hC : IsDGAlgebra 𝒞 dC} (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (ε.envelopingDGAlgHomEquiv hC (ψ.comp φ)).val =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (ε.envelopingDGAlgHomEquiv hB φ).val := by
  rw [envelopingDGAlgHomEquiv_eq_comp_toEnveloping, envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc]

/-- The inverse enveloping-algebra correspondence is natural with respect to DG algebra morphisms
in the target. -/
theorem envelopingDGAlgHomEquiv_symm_comp (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    {hC : IsDGAlgebra 𝒞 dC} (ψ : DGAlgHom hB hC)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hB.strictUnit_one}) :
    (ε.envelopingDGAlgHomEquiv hC).symm
        ⟨ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f.val,
          AInfinityHom.IsStrictlyUnital.comp
            (by simpa using ψ.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom)
            f.property⟩ =
      ψ.comp ((ε.envelopingDGAlgHomEquiv hB).symm f) := by simp

/-! ### Specialization to augmented DG algebras -/

/-- A DG algebra morphism `φ : U(A, ε) ⟶ B` preserves augmentations if and only if its
corresponding strictly unital `A∞` morphism `(A, ε) ⟶ B` is augmented. -/
theorem comp_eq_envelopingAugmentation_iff (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB)
    (φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    eB.comp φ = ε.envelopingAugmentation ↔
      (ε.envelopingDGAlgHomEquiv hB φ).val.IsAugmented ε eB.toAInfinityAugmentation := by
  have hsu : (ε.envelopingDGAlgHomEquiv hB φ).val.IsStrictlyUnital ε.isStrictUnit
      eB.toAInfinityAugmentation.isStrictUnit := by simpa using (ε.envelopingDGAlgHomEquiv hB φ).2
  rw [hsu.isAugmented_iff_taylor_comp_inclusion_mem, envelopingDGAlgHomEquiv_comp_inclusion]
  refine ⟨fun h w ↦ ?_, fun h ↦
    ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun w ↦ by simpa using h w⟩
  have heB : eB (φ (ι R w)) = 0 := by simpa using congrArg (· (ι R w)) h
  simp [heB]

/-- **Augmented universal property of `U(A, ε) = Ω B_∞ A`**: augmentation-preserving DG algebra
morphisms `U(A, ε) ⟶ B` correspond bijectively to strictly unital augmented `A∞` morphisms
`(A, ε) ⟶ (B, ε_B)`. -/
noncomputable def augmentedEnvelopingDGAlgHomEquiv (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = ε.envelopingAugmentation} ≃
    {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation} :=
  ((ε.envelopingDGAlgHomEquiv hB).subtypeEquiv (ε.comp_eq_envelopingAugmentation_iff eB)).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      (Equiv.subtypeEquivRight fun _ ↦
        ⟨fun h ↦ h.2, fun h ↦ ⟨by simpa using h.isStrictlyUnital, h⟩⟩))

/-- The underlying `A∞` morphism of `ε.augmentedEnvelopingDGAlgHomEquiv eB φ` agrees with the
unaugmented correspondence `ε.envelopingDGAlgHomEquiv hB φ.val`. -/
@[simp] theorem augmentedEnvelopingDGAlgHomEquiv_apply_val (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (φ) :
    (ε.augmentedEnvelopingDGAlgHomEquiv eB φ).val = (ε.envelopingDGAlgHomEquiv hB φ.val).val :=
  (rfl)

/-- The underlying DG algebra morphism of `(ε.augmentedEnvelopingDGAlgHomEquiv eB).symm f` is the
nonunital cobar lift (`cobarBarHomEquiv`) of `f` restricted to `ker ε`. -/
@[simp] theorem augmentedEnvelopingDGAlgHomEquiv_symm_apply_val (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (f) :
    ((ε.augmentedEnvelopingDGAlgHomEquiv eB).symm f).val =
      ε.reducedAlgebra.cobarBarHomEquiv hB (f.val.comp ε.inclusion.toAInfinityHom) := by
  simp [augmentedEnvelopingDGAlgHomEquiv]

/-- The universal morphism `ε.toEnveloping : A ⟶ U(A, ε)` is augmented. -/
@[simp] theorem isAugmented_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.comp_eq_envelopingAugmentation_iff ε.envelopingAugmentation (DGAlgHom.id _)).1
    (DGAlgHom.comp_id _)

/-- Every augmented `A∞` morphism corresponding to `φ : U(A, ε) ⟶ B` factors as `φ` after the
universal morphism `ε.toEnveloping`. -/
theorem augmentedEnvelopingDGAlgHomEquiv_eq_comp_toEnveloping (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (φ) :
    (ε.augmentedEnvelopingDGAlgHomEquiv eB φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping :=
  ε.envelopingDGAlgHomEquiv_eq_comp_toEnveloping hB φ.val

/-- Augmented universal factorization characterization of `U(A, ε)`: an augmentation-preserving DG
algebra morphism `φ : U(A, ε) ⟶ B` is the lift of `f : A ⟶ B` if and only if
`φ ∘ ε.toEnveloping = f`. -/
theorem eq_augmentedEnvelopingDGAlgHomEquiv_symm_iff (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (φ) (f) :
    φ = (ε.augmentedEnvelopingDGAlgHomEquiv eB).symm f ↔
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
        f.val := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, augmentedEnvelopingDGAlgHomEquiv_eq_comp_toEnveloping]

/-- **Augmented universal property of `U(A, ε)`**: every strictly unital augmented `A∞` morphism
from `(A, ε)` to an augmented DG algebra `(B, ε_B)` factors through `ε.toEnveloping` by a unique
augmentation-preserving DG algebra morphism `U(A, ε) ⟶ B`. -/
theorem bijective_augmented_comp_toEnveloping (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) :
    Function.Bijective fun φ :
        {φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
          hB // eB.comp φ = ε.envelopingAugmentation} ↦
      (⟨φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        ((DGAlgHom.isAugmented_toAInfinityHom_iff φ.val _ eB).2 φ.property).comp
          ε.isAugmented_toEnveloping⟩ :
        {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsAugmented ε eB.toAInfinityAugmentation}) := by
  convert (ε.augmentedEnvelopingDGAlgHomEquiv eB).bijective using 1
  exact funext fun φ ↦ Subtype.ext
    (ε.augmentedEnvelopingDGAlgHomEquiv_eq_comp_toEnveloping eB φ).symm

end AInfinityAlgebra.Augmentation

/-! ### Functoriality and source naturality -/

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} {𝒜'' : AInfinityAlgebra R A''}
  {ε : 𝒜.Augmentation} {ε' : 𝒜'.Augmentation} {ε'' : 𝒜''.Augmentation}
  {f : AInfinityHom 𝒜 𝒜'} {g : AInfinityHom 𝒜' 𝒜''}

/-- A strictly unital augmented `A∞` morphism `f : (A, ε) ⟶ (A', ε')` induces an
augmentation-preserving DG algebra morphism `U(A, ε) ⟶ U(A', ε')` on enveloping DG algebras. -/
noncomputable abbrev envelopingMap (hf : f.IsAugmented ε ε') :
    DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      ε'.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  hf.reducedHom.cobarBarMap

/-- The induced enveloping DG algebra morphism intertwines canonical augmentations. -/
@[simp] theorem envelopingAugmentation_comp_envelopingMap (hf : f.IsAugmented ε ε') :
    ε'.envelopingAugmentation.comp hf.envelopingMap = ε.envelopingAugmentation :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

/-- `envelopingMap` preserves composition of augmented `A∞` morphisms. -/
theorem envelopingMap_comp (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).envelopingMap = hg.envelopingMap.comp hf.envelopingMap := by
  rw [envelopingMap, hg.reducedHom_comp hf, AInfinityHom.cobarBarMap_comp]

/-- The universal morphism `toEnveloping` is natural with respect to `envelopingMap`. -/
theorem envelopingMap_comp_toEnveloping (hf : f.IsAugmented ε ε') :
    hf.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
      ε'.toEnveloping.comp f := by
  refine ext_comp_inclusion (((DGAlgHom.isAugmented_toAInfinityHom_iff hf.envelopingMap _ _).2
    hf.envelopingAugmentation_comp_envelopingMap).comp ε.isAugmented_toEnveloping)
    (ε'.isAugmented_toEnveloping.comp hf) ?_
  rw [AInfinityHom.comp_assoc, ε.toEnveloping_comp_inclusion,
    AInfinityHom.cobarBarMap_comp_toCobarBar, AInfinityHom.comp_assoc,
    ← hf.inclusion_comp_reducedHom, ← AInfinityHom.comp_assoc, ε'.toEnveloping_comp_inclusion]

end AInfinityHom.IsAugmented

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}

/-- `envelopingDGAlgHomEquiv` is natural in its source augmented `A∞` algebra along
`envelopingMap`. -/
theorem envelopingDGAlgHomEquiv_comp_envelopingMap (ε : 𝒜.Augmentation)
    {ε' : 𝒜'.Augmentation} {f : AInfinityHom 𝒜 𝒜'} (hf : f.IsAugmented ε ε')
    (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom ε'.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      hB) :
    (ε.envelopingDGAlgHomEquiv hB (φ.comp hf.envelopingMap)).val =
      (ε'.envelopingDGAlgHomEquiv hB φ).val.comp f := by
  rw [envelopingDGAlgHomEquiv_eq_comp_toEnveloping, envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc,
    hf.envelopingMap_comp_toEnveloping, ← AInfinityHom.comp_assoc]

/-- The inverse enveloping-algebra correspondence is natural in its source augmented `A∞` algebra
along `envelopingMap`. -/
theorem envelopingDGAlgHomEquiv_symm_comp_right (ε : 𝒜.Augmentation)
    {ε' : 𝒜'.Augmentation} {f : AInfinityHom 𝒜 𝒜'} (hf : f.IsAugmented ε ε')
    (hB : IsDGAlgebra ℬ dB)
    (g : {g : AInfinityHom 𝒜' hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      g.IsStrictlyUnital ε'.isStrictUnit hB.strictUnit_one}) :
    (ε.envelopingDGAlgHomEquiv hB).symm ⟨g.val.comp f, g.property.comp hf.isStrictlyUnital⟩ =
      ((ε'.envelopingDGAlgHomEquiv hB).symm g).comp hf.envelopingMap := by
  rw [envelopingDGAlgHomEquiv_symm_apply, envelopingDGAlgHomEquiv_symm_apply,
    AInfinityHom.comp_assoc, ← hf.inclusion_comp_reducedHom, ← AInfinityHom.comp_assoc,
    cobarBarHomEquiv_comp_right]

/-- `augmentedEnvelopingDGAlgHomEquiv` is natural in its source augmented `A∞` algebra along
`envelopingMap`. -/
theorem augmentedEnvelopingDGAlgHomEquiv_comp_envelopingMap (ε : 𝒜.Augmentation)
    {ε' : 𝒜'.Augmentation} {f : AInfinityHom 𝒜 𝒜'} (hf : f.IsAugmented ε ε')
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (φ) :
    (ε.augmentedEnvelopingDGAlgHomEquiv eB ⟨φ.val.comp hf.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, φ.property, hf.envelopingAugmentation_comp_envelopingMap]⟩).val =
      (ε'.augmentedEnvelopingDGAlgHomEquiv eB φ).val.comp f :=
  ε.envelopingDGAlgHomEquiv_comp_envelopingMap hf hB φ.val

/-- The inverse augmented enveloping-algebra correspondence is natural in its source augmented
`A∞` algebra along `envelopingMap`. -/
theorem augmentedEnvelopingDGAlgHomEquiv_symm_comp_right (ε : 𝒜.Augmentation)
    {ε' : 𝒜'.Augmentation} {f : AInfinityHom 𝒜 𝒜'} (hf : f.IsAugmented ε ε')
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (g : {g : AInfinityHom 𝒜' hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      g.IsAugmented ε' eB.toAInfinityAugmentation}) :
    ((ε.augmentedEnvelopingDGAlgHomEquiv eB).symm ⟨g.val.comp f, g.property.comp hf⟩).val =
      ((ε'.augmentedEnvelopingDGAlgHomEquiv eB).symm g).val.comp hf.envelopingMap :=
  ε.envelopingDGAlgHomEquiv_symm_comp_right hf hB
    ⟨g.val, by simpa using g.property.isStrictlyUnital⟩

end AInfinityAlgebra.Augmentation
end TauCeti
