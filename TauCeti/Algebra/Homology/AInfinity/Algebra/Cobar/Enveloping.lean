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

Together with the universal strictly unital augmented `A∞` morphism `ε.toEnveloping : A ⟶ U(A, ε)`,
`(U(A, ε), ε.envelopingAugmentation)` represents strictly unital augmented `A∞` morphisms `(A, ε) ⟶
(B, ε_B)` into augmented DG algebras (`AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv`).
Applying the cobar functor to the induced morphism on reduced bar coalgebras makes `U(A, ε)`
functorial in augmented `A∞` morphisms (`AInfinityHom.IsAugmented.envelopingMap`).

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

namespace AInfinityAlgebra

/-- `A∞` morphisms `A ⟶ B` into an augmented DG algebra `(B, ε_B)` whose Taylor map lands in
`ker ε_B` correspond bijectively to bar twisting cochains `Tᶜ(sA) →ₗ[R] B` landing in `ker ε_B`. -/
noncomputable def augmentedBarTwistingCochainEquiv (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      ∀ w, g.taylor w ∈ eB.toAInfinityAugmentation.augmentationIdeal} ≃
    {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1)) (deconcatenation R A)
        𝒜.barDifferential ℬ dB τ ∧ ∀ w, τ w ∈ eB.augmentationIdeal} where
  toFun g := ⟨_, (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra g.val).property,
    fun w ↦ by simpa [barTwistingCochainEquiv_apply] using g.property w⟩
  invFun τ := ⟨(𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm ⟨τ.val, τ.property.1⟩,
    fun w ↦ by simpa using τ.property.2 w⟩
  left_inv g := Subtype.ext ((𝒜.barTwistingCochainEquiv _).symm_apply_apply g.val)
  right_inv _ := Subtype.ext (by simp)

@[simp] theorem augmentedBarTwistingCochainEquiv_apply_val (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (g : {g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      ∀ w, g.taylor w ∈ eB.toAInfinityAugmentation.augmentationIdeal}) :
    (𝒜.augmentedBarTwistingCochainEquiv eB g).val =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.val.taylor :=
  𝒜.barTwistingCochainEquiv_apply hB.toIsNonUnitalDGAlgebra g.val

@[simp] theorem augmentedBarTwistingCochainEquiv_symm_apply_val (𝒜 : AInfinityAlgebra R A)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (τ : {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1)) (deconcatenation R A)
        𝒜.barDifferential ℬ dB τ ∧ ∀ w, τ w ∈ eB.augmentationIdeal}) :
    ((𝒜.augmentedBarTwistingCochainEquiv eB).symm τ).val =
      (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm ⟨τ.val, τ.property.1⟩ := (rfl)

namespace Augmentation

variable {𝒜 : AInfinityAlgebra R A}

/-- The canonical DG algebra augmentation `U(A, ε) = Ω Tᶜ(s(ker ε)) ⟶ R` of the enveloping DG
algebra of an augmented `A∞` algebra. -/
noncomputable def envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- `envelopingAugmentation` is `cobarAugmentation` on the reduced bar coalgebra of `ker ε`. -/
theorem envelopingAugmentation_def (ε : 𝒜.Augmentation) :
    ε.envelopingAugmentation = ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation :=
  (rfl)

/-- The canonical augmentation of `U(A, ε)` annihilates every desuspended reduced bar generator. -/
@[simp] theorem envelopingAugmentation_ι (ε : 𝒜.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) : ε.envelopingAugmentation (ι R w) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι w

/-- **Universal property of the enveloping DG algebra `U(A, ε) = Ω B_∞ A`**: augmentation-preserving
DG algebra morphisms `U(A, ε) ⟶ B` correspond bijectively to strictly unital augmented `A∞`
morphisms `(A, ε) ⟶ (B, ε_B)`. -/
noncomputable def envelopingDGAlgHomEquiv (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = ε.envelopingAugmentation} ≃
    {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation} :=
  ((Equiv.subtypeEquivRight fun _ ↦ by rw [envelopingAugmentation_def]).trans
    ((ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.augmentedCobarTwistingCochainEquiv eB).trans
      (ε.reducedAlgebra.augmentedBarTwistingCochainEquiv eB).symm)).trans
    ((liftReducedHomEquiv ε.reducedAlgebra eB.toAInfinityAugmentation).symm.trans
      (ε.augmentedHomEquiv eB.toAInfinityAugmentation).symm)

@[simp] theorem envelopingDGAlgHomEquiv_comp_inclusion (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) (φ) :
    (ε.envelopingDGAlgHomEquiv eB φ).val.comp ε.inclusion.toAInfinityHom =
      ε.reducedAlgebra.cobarDGAlgHomEquiv hB φ.val := by
  simp only [envelopingDGAlgHomEquiv, Equiv.trans_apply, augmentedHomEquiv_symm_apply_val,
    extendReducedHom_comp_inclusion]
  rw [← liftReducedHomEquiv_apply_val, Equiv.apply_symm_apply,
    augmentedBarTwistingCochainEquiv_symm_apply_val]
  exact AInfinityHom.ext (LinearMap.ext fun _ ↦ by simp)

/-- The underlying DG algebra morphism of `(ε.envelopingDGAlgHomEquiv eB).symm f` is the unreduced
cobar lift of `f` restricted to `ker ε`. -/
@[simp] theorem envelopingDGAlgHomEquiv_symm_apply_val (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) (f) :
    ((ε.envelopingDGAlgHomEquiv eB).symm f).val =
      (ε.reducedAlgebra.cobarDGAlgHomEquiv hB).symm (f.val.comp ε.inclusion.toAInfinityHom) :=
  (Equiv.eq_symm_apply _).2 <| by
    rw [← envelopingDGAlgHomEquiv_comp_inclusion, Equiv.apply_symm_apply]

/-- Evaluating `(ε.envelopingDGAlgHomEquiv eB).symm f` on a generator `ι w` negates the
Koszul-twisted Taylor map of `f` on `w`. -/
theorem envelopingDGAlgHomEquiv_symm_apply_ι (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) (f) (w : ReducedTensorWords R ε.augmentationIdeal) :
    ((ε.envelopingDGAlgHomEquiv eB).symm f).val (ι R w) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1
        (f.val.taylor (ε.inclusion.barMap w)) := by
  simp [AInfinityHom.taylor_comp]

/-- The **universal strictly unital augmented `A∞` morphism** `A ⟶ U(A, ε)` into the enveloping
differential graded algebra `U(A, ε) = Ω Tᶜ(s(ker ε))`. -/
noncomputable def toEnveloping (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜 (IsNonUnitalDGAlgebra.toAInfinityAlgebra (IsDGAlgebra.toIsNonUnitalDGAlgebra
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential)) :=
  (ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).val

/-- The universal morphism `ε.toEnveloping : A ⟶ U(A, ε)` is augmented. -/
@[simp] theorem isAugmented_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).property

/-- Under `envelopingDGAlgHomEquiv`, the identity morphism of `U(A, ε)` maps to `ε.toEnveloping`. -/
@[simp] theorem envelopingDGAlgHomEquiv_id (ε : 𝒜.Augmentation)
    (h : ε.envelopingAugmentation.comp (DGAlgHom.id _) = ε.envelopingAugmentation :=
      DGAlgHom.comp_id _) :
    ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation ⟨DGAlgHom.id _, h⟩ =
      ⟨ε.toEnveloping, ε.isAugmented_toEnveloping⟩ := (rfl)

/-- Applying `(ε.envelopingDGAlgHomEquiv _).symm` to `ε.toEnveloping` recovers `DGAlgHom.id`. -/
@[simp] theorem envelopingDGAlgHomEquiv_symm_toEnveloping (ε : 𝒜.Augmentation)
    (hf : ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
      ε.isAugmented_toEnveloping) :
    (ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation).symm ⟨ε.toEnveloping, hf⟩ =
      ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩ :=
  (ε.envelopingDGAlgHomEquiv _).symm_apply_apply _

/-- The universal morphism `ε.toEnveloping : A ⟶ U(A, ε)` is strictly unital. -/
@[simp] theorem isStrictlyUnital_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit (IsDGAlgebra.strictUnit_one
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential) := by
  simpa using ε.isAugmented_toEnveloping.isStrictlyUnital

/-- The linear part of `ε.toEnveloping` sends the strict unit of `A` to `1`. -/
theorem linearPart_toEnveloping_unit (ε : 𝒜.Augmentation) : ε.toEnveloping.linearPart ε.unit = 1 :=
  ε.isStrictlyUnital_toEnveloping.map_unit

@[simp] theorem toEnveloping_comp_inclusion (ε : 𝒜.Augmentation) :
    ε.toEnveloping.comp ε.inclusion.toAInfinityHom = ε.reducedAlgebra.toCobar := by
  rw [toEnveloping, envelopingDGAlgHomEquiv_comp_inclusion, cobarDGAlgHomEquiv_id]

/-- On any bar word, `ε.toEnveloping.taylor` splits into the scalar augmentation of its single
letter plus the Koszul-twisted generator on its reduced bar word. -/
@[simp] theorem taylor_toEnveloping (ε : 𝒜.Augmentation) (z : ReducedTensorWords R A) :
    ε.toEnveloping.taylor z = algebraMap R _ (ε (letter R A z)) +
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
        (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
  have hcomp := congrArg (fun f ↦ f.taylor (ReducedTensorWords.map (R := R) ε.reducedPart z))
    ε.toEnveloping_comp_inclusion
  simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    LinearMap.comp_apply, taylor_toCobar] at hcomp
  rw [ε.isAugmented_toEnveloping.taylor_apply z, hcomp,
    DGAlgAugmentation.toAInfinityAugmentation_unit, ← Algebra.algebraMap_eq_smul_one]

/-- The linear part of `ε.toEnveloping` subtracts the Koszul-twisted single-letter generator of
`ε.reducedPart` from the scalar augmentation. -/
@[simp] theorem linearPart_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.linearPart = Algebra.linearMap R _ ∘ₗ ε.toLinearMap -
      ι R ∘ₗ ofLetter R _ ∘ₗ ε.reducedAlgebra.grading.koszulTwist 1 ∘ₗ ε.reducedPart :=
  LinearMap.ext fun _ ↦ by
    simp [koszulTwist_grading, InternalGrading.koszulTwist_one_shift_one, sub_eq_add_neg]

/-- Every augmented `A∞` morphism corresponding to `φ : U(A, ε) ⟶ B` factors as `φ` after the
universal morphism `ε.toEnveloping`. -/
theorem envelopingDGAlgHomEquiv_eq_comp_toEnveloping (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) (φ) :
    (ε.envelopingDGAlgHomEquiv eB φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  refine AInfinityHom.IsAugmented.ext_comp_inclusion (ε.envelopingDGAlgHomEquiv eB φ).property
    (((DGAlgHom.isAugmented_toAInfinityHom_iff φ.val _ eB).2 φ.property).comp
      ε.isAugmented_toEnveloping) ?_
  rw [envelopingDGAlgHomEquiv_comp_inclusion, AInfinityHom.comp_assoc, toEnveloping_comp_inclusion,
    cobarDGAlgHomEquiv_eq_comp_toCobar]

/-- Universal factorization characterization of `U(A, ε)`: an augmentation-preserving DG algebra
morphism `φ : U(A, ε) ⟶ B` is the lift of `f : A ⟶ B` if and only if `φ ∘ ε.toEnveloping = f`. -/
theorem eq_envelopingDGAlgHomEquiv_symm_iff (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    (eB : DGAlgAugmentation hB) (φ) (f) :
    φ = (ε.envelopingDGAlgHomEquiv eB).symm f ↔
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
        f.val := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, envelopingDGAlgHomEquiv_eq_comp_toEnveloping]

/-- `envelopingDGAlgHomEquiv` is natural with respect to augmentation-preserving DG algebra
morphisms in the target. -/
@[simp] theorem envelopingDGAlgHomEquiv_comp_left (ε : 𝒜.Augmentation) {hB : IsDGAlgebra ℬ dB}
    {hC : IsDGAlgebra 𝒞 dC} (eB : DGAlgAugmentation hB) (eC : DGAlgAugmentation hC)
    (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB) (φ) :
    (ε.envelopingDGAlgHomEquiv eC
      ⟨ψ.comp φ.val, by rw [← DGAlgHom.comp_assoc, hψ, φ.property]⟩).val =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        (ε.envelopingDGAlgHomEquiv eB φ).val := by
  rw [envelopingDGAlgHomEquiv_eq_comp_toEnveloping, envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc]

end Augmentation
end AInfinityAlgebra

namespace AInfinityHom.IsAugmented

variable {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'} {𝒜'' : AInfinityAlgebra R A''}
  {ε : 𝒜.Augmentation} {ε' : 𝒜'.Augmentation} {ε'' : 𝒜''.Augmentation}
  {f : AInfinityHom 𝒜 𝒜'} {g : AInfinityHom 𝒜' 𝒜''}

/-- A strictly unital augmented `A∞` morphism `f : (A, ε) ⟶ (A', ε')` induces an
augmentation-preserving DG algebra morphism `U(A, ε) ⟶ U(A', ε')` on enveloping DG algebras. -/
noncomputable def envelopingMap (hf : f.IsAugmented ε ε') :
    DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      ε'.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  hf.reducedHom.cobarMap

@[simp] theorem envelopingMap_ι (hf : f.IsAugmented ε ε')
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    hf.envelopingMap (ι R w) = ι R (hf.reducedHom.barMap w) :=
  hf.reducedHom.cobarMap_ι w

/-- The induced enveloping DG algebra morphism intertwines canonical augmentations. -/
@[simp] theorem envelopingAugmentation_comp_envelopingMap (hf : f.IsAugmented ε ε') :
    ε'.envelopingAugmentation.comp hf.envelopingMap = ε.envelopingAugmentation :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

@[simp] theorem envelopingMap_id (ε : 𝒜.Augmentation) :
    (AInfinityHom.isAugmented_id ε).envelopingMap =
      DGAlgHom.id ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  rw [envelopingMap, reducedHom_id, AInfinityHom.cobarMap_id]

/-- `envelopingMap` preserves composition of augmented `A∞` morphisms. -/
theorem envelopingMap_comp (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).envelopingMap = hg.envelopingMap.comp hf.envelopingMap := by
  simp only [envelopingMap, hg.reducedHom_comp hf, AInfinityHom.cobarMap_comp]

/-- The universal morphism `toEnveloping` is natural with respect to `envelopingMap`. -/
theorem envelopingMap_comp_toEnveloping (hf : f.IsAugmented ε ε') :
    hf.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
      ε'.toEnveloping.comp f := by
  refine ext_comp_inclusion (((DGAlgHom.isAugmented_toAInfinityHom_iff hf.envelopingMap _ _).2
    hf.envelopingAugmentation_comp_envelopingMap).comp ε.isAugmented_toEnveloping)
    (ε'.isAugmented_toEnveloping.comp hf) ?_
  rw [AInfinityHom.comp_assoc, ε.toEnveloping_comp_inclusion, envelopingMap,
    AInfinityHom.cobarMap_comp_toCobar, AInfinityHom.comp_assoc, ← hf.inclusion_comp_reducedHom,
    ← AInfinityHom.comp_assoc, ε'.toEnveloping_comp_inclusion]

/-- `envelopingDGAlgHomEquiv` is natural in its source augmented `A∞` algebra along
`envelopingMap`. -/
@[simp] theorem envelopingDGAlgHomEquiv_comp_envelopingMap (hf : f.IsAugmented ε ε')
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) (φ) :
    (ε.envelopingDGAlgHomEquiv eB ⟨φ.val.comp hf.envelopingMap, by
      rw [← DGAlgHom.comp_assoc, φ.property, hf.envelopingAugmentation_comp_envelopingMap]⟩).val =
      (ε'.envelopingDGAlgHomEquiv eB φ).val.comp f := by
  rw [AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc,
    hf.envelopingMap_comp_toEnveloping, ← AInfinityHom.comp_assoc]

end AInfinityHom.IsAugmented
end TauCeti
