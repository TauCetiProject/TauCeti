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

For an augmented `A∞` algebra `(A, ε)` over `R`, the reduced bar construction of its augmentation
ideal `B_∞ A = Tᶜ(s(ker ε))` is a noncounital differential graded coalgebra
(`ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar`), and its cobar construction
`U(A, ε) = Ω B_∞ A = T(s⁻¹ Tᶜ(s(ker ε)))` is a unital differential graded algebra equipped with
the canonical cobar augmentation `ε.envelopingAugmentation : U(A, ε) ⟶ R` annihilating every
desuspended bar word.

Combining four equivalences —

1. the augmented cobar universal property (`augmentedCobarTwistingCochainEquiv`), identifying
   augmentation-preserving DG algebra morphisms `U(A, ε) ⟶ B` into an augmented DG algebra
   `(B, ε_B)` with twisting cochains `Tᶜ(s(ker ε)) →ₗ[R] B` landing in `ker ε_B`;
2. the bar twisting-cochain bijection (`augmentedBarTwistingCochainEquiv`), identifying such
   twisting cochains with `A∞` morphisms `ker ε ⟶ B` whose Taylor map takes values in `ker ε_B`
   (since `ε_B` is invariant under the Koszul twist `σ_B`);
3. the universal property of the target augmentation ideal (`liftReducedHomEquiv`), lifting those
   morphisms uniquely to `A∞` morphisms `ker ε ⟶ ker ε_B`;
4. the reduction equivalence for augmented `A∞` morphisms (`augmentedHomEquiv`), identifying
   nonunital `A∞` morphisms `ker ε ⟶ ker ε_B` with strictly unital augmented `A∞` morphisms
   `(A, ε) ⟶ (B, ε_B)` —

yields the **universal property of the enveloping DG algebra**
(`AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv`):

`{φ : U(A, ε) ⟶_{DGA} B // ε_B ∘ φ = ε_{U(A, ε)}} ≃ {f : A ⟶_{A∞} B // f.IsAugmented ε ε_B}`.

Evaluating at the identity morphism of `U(A, ε)` produces the **universal strictly unital augmented
`A∞` morphism** `ε.toEnveloping : A ⟶ U(A, ε)` (`isAugmented_toEnveloping`,
`isStrictlyUnital_toEnveloping`), whose Taylor map sends any bar word `z` over `A` to
`ε(z₁) • 1 + ι(σ(π(z)))` (`taylor_toEnveloping`), where `π(z)` applies `ε.reducedPart` letterwise.
Every strictly unital augmented `A∞` morphism `(A, ε) ⟶ (B, ε_B)` into an augmented DG algebra
factors uniquely as `φ ∘ ε.toEnveloping` for a single augmentation-preserving DG algebra morphism
`φ : U(A, ε) ⟶ B` (`envelopingDGAlgHomEquiv_eq_comp_toEnveloping`,
`eq_envelopingDGAlgHomEquiv_symm_iff`), and `U(-)` is functorial on strictly unital augmented `A∞`
morphisms (`AInfinityHom.IsAugmented.envelopingMap`).

## Main definitions

* `TauCeti.AInfinityAlgebra.augmentedBarTwistingCochainEquiv`: equivalence between `A∞` morphisms
  `D ⟶ B` landing in `ker ε_B` and bar twisting cochains `Tᶜ(sD) →ₗ[R] B` landing in `ker ε_B`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: the canonical DG algebra
  augmentation `U(A, ε) ⟶ R`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv`: the universal bijection between
  augmentation-preserving DG algebra morphisms `U(A, ε) ⟶ B` and strictly unital augmented `A∞`
  morphisms `A ⟶ B`.
* `TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`: the canonical strictly unital augmented `A∞`
  morphism `A ⟶ U(A, ε)`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap`: the induced augmentation-preserving DG algebra
  morphism `U(A, ε) ⟶ U(A', ε')` of a strictly unital augmented `A∞` morphism `f : A ⟶ A'`.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.isAugmented_toEnveloping` and
  `isStrictlyUnital_toEnveloping`: `ε.toEnveloping` is strictly unital and augmented.
* `TauCeti.AInfinityAlgebra.Augmentation.taylor_toEnveloping`: explicit Taylor formula for
  `ε.toEnveloping` on arbitrary bar words of `A`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping` and
  `eq_envelopingDGAlgHomEquiv_symm_iff`: every strictly unital augmented `A∞` morphism from `A` to
  an augmented DG algebra factors uniquely through `ε.toEnveloping`.
* `TauCeti.AInfinityHom.IsAugmented.envelopingMap_id`, `envelopingMap_comp`, and
  `envelopingMap_comp_toEnveloping`: functoriality of `U(A, ε)` and naturality of `toEnveloping`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

namespace TauCeti

open TensorAlgebra ReducedTensorWords

universe uR uA uA' uA'' uB uC

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

/-- For an `A∞` algebra `D` and an augmented DG algebra `(B, ε_B)`, `A∞` morphisms `D ⟶ B` whose
Taylor map lands in `ker ε_B` correspond bijectively to bar twisting cochains `Tᶜ(sD) →ₗ[R] B`
landing in `ker ε_B`. -/
noncomputable def augmentedBarTwistingCochainEquiv
    (𝒜 : AInfinityAlgebra R A) {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      ∀ w, g.taylor w ∈ eB.toAInfinityAugmentation.augmentationIdeal} ≃
    {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ ∧
      ∀ w, τ w ∈ eB.augmentationIdeal} where
  toFun g := ⟨(𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra g.val).val,
    (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra g.val).property,
    fun w ↦ by simpa [barTwistingCochainEquiv_apply] using g.property w⟩
  invFun τ := ⟨(𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm ⟨τ.val, τ.property.1⟩,
    fun w ↦ by simpa using τ.property.2 w⟩
  left_inv g := by
    apply Subtype.ext
    dsimp only
    exact (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm_apply_apply g.val
  right_inv τ := by
    apply Subtype.ext
    dsimp only
    exact congrArg Subtype.val
      ((𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).apply_symm_apply ⟨τ.val, τ.property.1⟩)

@[simp]
theorem augmentedBarTwistingCochainEquiv_apply_val
    (𝒜 : AInfinityAlgebra R A) {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (g : {g : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      ∀ w, g.taylor w ∈ eB.toAInfinityAugmentation.augmentationIdeal}) :
    (𝒜.augmentedBarTwistingCochainEquiv eB g).val =
      (InternalGrading.ofDecomposition ℬ).koszulTwist 1 ∘ₗ g.val.taylor :=
  𝒜.barTwistingCochainEquiv_apply hB.toIsNonUnitalDGAlgebra g.val

@[simp]
theorem augmentedBarTwistingCochainEquiv_symm_apply_val
    (𝒜 : AInfinityAlgebra R A) {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (τ : {τ : ReducedTensorWords R A →ₗ[R] B //
      IsTwistingCochain (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential ℬ dB τ ∧
      ∀ w, τ w ∈ eB.augmentationIdeal}) :
    ((𝒜.augmentedBarTwistingCochainEquiv eB).symm τ).val =
      (𝒜.barTwistingCochainEquiv hB.toIsNonUnitalDGAlgebra).symm ⟨τ.val, τ.property.1⟩ := (rfl)

namespace Augmentation

variable {𝒜 : AInfinityAlgebra R A}

/-- The canonical DG algebra augmentation `U(A, ε) = Ω Tᶜ(s(ker ε)) ⟶ R` of the enveloping DG
algebra of an augmented `A∞` algebra, annihilating every desuspended bar generator. -/
noncomputable abbrev envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- The canonical augmentation of `U(A, ε)` vanishes on every desuspended bar word. -/
theorem envelopingAugmentation_ι (ε : 𝒜.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (ι R w) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι w

/-- **Universal property of the enveloping DG algebra `U(A, ε) = Ω B_∞ A`**: augmentation-preserving
DG algebra morphisms `U(A, ε) ⟶ B` into an augmented DG algebra `(B, ε_B)` correspond bijectively
to strictly unital augmented `A∞` morphisms `(A, ε) ⟶ (B, ε_B)`. -/
noncomputable def envelopingDGAlgHomEquiv (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB) :
    {φ : DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
      eB.comp φ = ε.envelopingAugmentation} ≃
    {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation} :=
  ((ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.augmentedCobarTwistingCochainEquiv eB).trans
    (ε.reducedAlgebra.augmentedBarTwistingCochainEquiv eB).symm).trans
    ((liftReducedHomEquiv ε.reducedAlgebra eB.toAInfinityAugmentation).symm.trans
      (ε.augmentedHomEquiv eB.toAInfinityAugmentation).symm)

/-- Restricting the augmented `A∞` morphism associated to `φ : U(A, ε) ⟶ B` to the augmentation
ideal `ker ε` recovers the bar--cobar transpose of `φ` on `ker ε`. -/
@[simp]
theorem envelopingDGAlgHomEquiv_comp_inclusion (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ :
      DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
        eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingDGAlgHomEquiv eB φ).val.comp ε.inclusion.toAInfinityHom =
      ε.reducedAlgebra.cobarDGAlgHomEquiv hB φ.val := by
  simp only [envelopingDGAlgHomEquiv, Equiv.trans_apply, augmentedHomEquiv_symm_apply_val,
    extendReducedHom_comp_inclusion]
  rw [← liftReducedHomEquiv_apply_val, Equiv.apply_symm_apply,
    augmentedBarTwistingCochainEquiv_symm_apply_val]
  apply AInfinityHom.ext
  refine LinearMap.ext fun w ↦ ?_
  simp

/-- On desuspended bar words `ι w`, the inverse of `envelopingDGAlgHomEquiv` evaluates `-σ_B` on
the Taylor value of `f` at the included word `ε.inclusion.barMap w`. -/
@[simp]
theorem envelopingDGAlgHomEquiv_symm_apply_ι (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation})
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ((ε.envelopingDGAlgHomEquiv eB).symm f).val (ι R w) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1
        (f.val.taylor (ε.inclusion.barMap w)) := by
  have h : ε.reducedAlgebra.cobarDGAlgHomEquiv hB ((ε.envelopingDGAlgHomEquiv eB).symm f).val =
      f.val.comp ε.inclusion.toAInfinityHom := by
    rw [← envelopingDGAlgHomEquiv_comp_inclusion, Equiv.apply_symm_apply]
  have hsymm : ((ε.envelopingDGAlgHomEquiv eB).symm f).val =
      (ε.reducedAlgebra.cobarDGAlgHomEquiv hB).symm (f.val.comp ε.inclusion.toAInfinityHom) :=
    (Equiv.eq_symm_apply _).2 h
  rw [hsymm, cobarDGAlgHomEquiv_symm_apply_ι, AInfinityHom.taylor_comp,
    AInfinityStrictHom.barMap_toAInfinityHom, LinearMap.comp_apply]

/-- The **universal strictly unital augmented `A∞` morphism** `A ⟶ U(A, ε)` from an augmented `A∞`
algebra into its enveloping differential graded algebra `U(A, ε) = Ω Tᶜ(s(ker ε))`. -/
noncomputable def toEnveloping (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜
      (IsNonUnitalDGAlgebra.toAInfinityAlgebra
        (IsDGAlgebra.toIsNonUnitalDGAlgebra
          ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential)) :=
  (ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).val

/-- The canonical morphism `ε.toEnveloping : A ⟶ U(A, ε)` is strictly unital and augmented. -/
theorem isAugmented_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation :=
  (ε.envelopingDGAlgHomEquiv ε.envelopingAugmentation ⟨DGAlgHom.id _, DGAlgHom.comp_id _⟩).property

/-- The canonical morphism `ε.toEnveloping : A ⟶ U(A, ε)` is strictly unital. -/
theorem isStrictlyUnital_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit
      (IsDGAlgebra.strictUnit_one
        ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential) := by
  simpa using ε.isAugmented_toEnveloping.isStrictlyUnital

theorem toEnveloping_linearPart_unit (ε : 𝒜.Augmentation) :
    ε.toEnveloping.linearPart ε.unit = 1 :=
  ε.isStrictlyUnital_toEnveloping.map_unit

/-- Restricting `ε.toEnveloping` to the augmentation ideal `ker ε` recovers the universal nonunital
bar--cobar morphism `ε.reducedAlgebra.toCobar`. -/
@[simp]
theorem toEnveloping_comp_inclusion (ε : 𝒜.Augmentation) :
    ε.toEnveloping.comp ε.inclusion.toAInfinityHom = ε.reducedAlgebra.toCobar := by
  rw [toEnveloping, envelopingDGAlgHomEquiv_comp_inclusion, cobarDGAlgHomEquiv_id]

/-- Explicit Taylor formula for `ε.toEnveloping`: on any bar word `z` of `A`, the scalar part comes
from `ε` on the length-one component of `z` while the reduced part is the desuspended cobar
generator of the Koszul-twisted reduced word `σ(π(z))`. -/
theorem taylor_toEnveloping (ε : 𝒜.Augmentation) (z : ReducedTensorWords R A) :
    ε.toEnveloping.taylor z =
      algebraMap R _ (ε (letter R A z)) +
        ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
          (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
  let P : A →ₗ[R] A := ε.inclusion.toLinearMap ∘ₗ ε.reducedPart
  have hP : ∀ a, ∃ c : R, a - P a = c • ε.unit := fun a ↦ ⟨ε a, by simp [P, coe_reducedPart]⟩
  let w := z - ReducedTensorWords.map (R := R) P z
  have hw : w ∈ degenerateWords R A ε.unit := sub_map_mem_degenerateWords P hP z
  have hlw : letter R A w = ε (letter R A z) • ε.unit := by
    have hlp := LinearMap.congr_fun (letter_comp_map (R := R) P) z
    simp only [LinearMap.comp_apply] at hlp
    rw [map_sub, hlp]
    simp only [P, LinearMap.comp_apply, inclusion_toLinearMap, Submodule.subtype_apply,
      coe_reducedPart, sub_sub_cancel]
  have htw : ε.toEnveloping.taylor w = algebraMap R _ (ε (letter R A z)) := by
    rw [ε.isStrictlyUnital_toEnveloping.taylor_eq_linearPart_letter hw, hlw, map_smul,
      toEnveloping_linearPart_unit, Algebra.algebraMap_eq_smul_one]
  have hred : ε.toEnveloping.taylor (ReducedTensorWords.map (R := R) P z) =
      ι R ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
        (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
    have hmap : ReducedTensorWords.map (R := R) P z =
        ε.inclusion.barMap (ReducedTensorWords.map (R := R) ε.reducedPart z) := by
      dsimp only [P]
      rw [AInfinityStrictHom.barMap_def, ReducedTensorWords.map_comp, LinearMap.comp_apply]
    have hcomp := congrArg (fun f ↦ f.taylor (ReducedTensorWords.map (R := R) ε.reducedPart z))
      ε.toEnveloping_comp_inclusion
    simp only [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
      LinearMap.comp_apply, taylor_toCobar] at hcomp
    rwa [hmap]
  have hz : z = w + ReducedTensorWords.map (R := R) P z := (sub_add_cancel z _).symm
  conv_lhs => rw [hz]
  rw [map_add, htw, hred]

/-- **Universal property of `toEnveloping`**: the strictly unital augmented `A∞` morphism
corresponding to an augmentation-preserving DG algebra morphism `φ : U(A, ε) ⟶ B` is obtained by
postcomposing `ε.toEnveloping` with `φ`. -/
theorem envelopingDGAlgHomEquiv_eq_comp_toEnveloping (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ :
      DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
        eB.comp φ = ε.envelopingAugmentation}) :
    (ε.envelopingDGAlgHomEquiv eB φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  have hφ : φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
      ε.envelopingAugmentation.toAInfinityAugmentation eB.toAInfinityAugmentation :=
    (DGAlgHom.isAugmented_toAInfinityHom_iff φ.val ε.envelopingAugmentation eB).2 φ.property
  refine AInfinityHom.IsAugmented.ext_comp_inclusion (ε.envelopingDGAlgHomEquiv eB φ).property
    (hφ.comp ε.isAugmented_toEnveloping) ?_
  rw [envelopingDGAlgHomEquiv_comp_inclusion, AInfinityHom.comp_assoc, toEnveloping_comp_inclusion,
    cobarDGAlgHomEquiv_eq_comp_toCobar]

/-- **Universal factorization through `toEnveloping`**: an augmentation-preserving DG algebra
morphism `φ : U(A, ε) ⟶ B` is the transpose of a strictly unital augmented `A∞` morphism
`f : A ⟶ B` if and only if postcomposing `ε.toEnveloping` with `φ` recovers `f`. -/
theorem eq_envelopingDGAlgHomEquiv_symm_iff (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ :
      DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
        eB.comp φ = ε.envelopingAugmentation})
    (f : {f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsAugmented ε eB.toAInfinityAugmentation}) :
    φ = (ε.envelopingDGAlgHomEquiv eB).symm f ↔
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
        f.val := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, envelopingDGAlgHomEquiv_eq_comp_toEnveloping]

/-- Naturality of `envelopingDGAlgHomEquiv` in the target augmented DG algebra. -/
@[simp]
theorem envelopingDGAlgHomEquiv_comp_left (ε : 𝒜.Augmentation)
    {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
    (eB : DGAlgAugmentation hB) (eC : DGAlgAugmentation hC)
    (ψ : DGAlgHom hB hC) (hψ : eC.comp ψ = eB)
    (φ : {φ :
      DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
        eB.comp φ = ε.envelopingAugmentation}) :
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
augmentation-preserving DG algebra morphism `U(A, ε) ⟶ U(A', ε')` on enveloping DG algebras via
its reduced `A∞` morphism `ker ε ⟶ ker ε'`. -/
noncomputable def envelopingMap (hf : f.IsAugmented ε ε') :
    DGAlgHom ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      ε'.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  hf.reducedHom.cobarMap

/-- On desuspended bar words, `hf.envelopingMap` applies the reduced bar coalgebra map. -/
@[simp]
theorem envelopingMap_ι (hf : f.IsAugmented ε ε')
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    hf.envelopingMap (ι R w) = ι R (hf.reducedHom.barMap w) :=
  hf.reducedHom.cobarMap_ι w

/-- The induced enveloping DG algebra map preserves canonical cobar augmentations. -/
@[simp]
theorem envelopingAugmentation_comp_envelopingMap (hf : f.IsAugmented ε ε') :
    ε'.envelopingAugmentation.comp hf.envelopingMap = ε.envelopingAugmentation :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun w ↦ by simp

/-- The identity augmented `A∞` morphism induces the identity DG algebra morphism on `U(A, ε)`. -/
@[simp]
theorem envelopingMap_id (ε : 𝒜.Augmentation) :
    (AInfinityHom.isAugmented_id ε).envelopingMap =
      DGAlgHom.id ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  rw [envelopingMap, reducedHom_id, AInfinityHom.cobarMap_id]

/-- The enveloping DG algebra construction preserves composition of strictly unital augmented `A∞`
morphisms. -/
theorem envelopingMap_comp (hg : g.IsAugmented ε' ε'') (hf : f.IsAugmented ε ε') :
    (hg.comp hf).envelopingMap = hg.envelopingMap.comp hf.envelopingMap := by
  rw [envelopingMap, hg.reducedHom_comp hf, AInfinityHom.cobarMap_comp]
  rfl

/-- Naturality of the universal morphism `toEnveloping` with respect to strictly unital augmented
`A∞` morphisms. -/
theorem envelopingMap_comp_toEnveloping (hf : f.IsAugmented ε ε') :
    hf.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping =
      ε'.toEnveloping.comp f := by
  have henv : hf.envelopingMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
      ε.envelopingAugmentation.toAInfinityAugmentation
      ε'.envelopingAugmentation.toAInfinityAugmentation :=
    (DGAlgHom.isAugmented_toAInfinityHom_iff hf.envelopingMap
      ε.envelopingAugmentation ε'.envelopingAugmentation).2
      hf.envelopingAugmentation_comp_envelopingMap
  refine ext_comp_inclusion (henv.comp ε.isAugmented_toEnveloping)
    (ε'.isAugmented_toEnveloping.comp hf) ?_
  rw [AInfinityHom.comp_assoc, ε.toEnveloping_comp_inclusion, envelopingMap,
    AInfinityHom.cobarMap_comp_toCobar, AInfinityHom.comp_assoc, ← hf.inclusion_comp_reducedHom,
    ← AInfinityHom.comp_assoc, ε'.toEnveloping_comp_inclusion]

/-- Naturality of `envelopingDGAlgHomEquiv` in the source augmented `A∞` algebra. -/
@[simp]
theorem envelopingDGAlgHomEquiv_comp_envelopingMap (hf : f.IsAugmented ε ε')
    {hB : IsDGAlgebra ℬ dB} (eB : DGAlgAugmentation hB)
    (φ : {φ :
      DGAlgHom ε'.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB //
        eB.comp φ = ε'.envelopingAugmentation}) :
    (ε.envelopingDGAlgHomEquiv eB
      ⟨φ.val.comp hf.envelopingMap, by
        rw [← DGAlgHom.comp_assoc, φ.property,
          hf.envelopingAugmentation_comp_envelopingMap]⟩).val =
      (ε'.envelopingDGAlgHomEquiv eB φ).val.comp f := by
  rw [AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    AInfinityAlgebra.Augmentation.envelopingDGAlgHomEquiv_eq_comp_toEnveloping,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc,
    hf.envelopingMap_comp_toEnveloping, ← AInfinityHom.comp_assoc]

end AInfinityHom.IsAugmented

end TauCeti
