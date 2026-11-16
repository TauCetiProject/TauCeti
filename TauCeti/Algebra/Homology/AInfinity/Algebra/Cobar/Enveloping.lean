/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation.UnitalHom
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.Contraction
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG.Cohomology

/-!
# The enveloping differential graded algebra of an augmented `A∞` algebra

Let `(A, ε)` be an augmented `A∞` algebra over a commutative ring `R`, with reduced augmentation
ideal `A⁺ = ker ε` (`TauCeti.AInfinityAlgebra.Augmentation.reducedAlgebra`).  Its **enveloping
differential graded algebra** is the cobar construction of the reduced bar construction,

`U(A) = Ω Tᶜ(sA⁺)`,

equipped with the cobar grading, cobar differential, and canonical augmentation `U(A) ⟶ R`
(`TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`,
`TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`).

Combining the bijection between strictly unital `A∞` morphisms out of `A` and nonunital `A∞`
morphisms out of `A⁺` (`TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`) with the
universal property of the cobar construction (`TauCeti.AInfinityAlgebra.cobarBarHomEquiv`) yields:

* a bijection `TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv` between strictly unital
  `A∞` morphisms `A ⟶ D` into any DG algebra `D` and DG algebra morphisms `U(A) ⟶ D`;
* the canonical strictly unital, augmentation-preserving `A∞` morphism
  `η : A ⟶ U(A)` (`TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`), through which every
  strictly unital `A∞` morphism `A ⟶ D` factors uniquely by a DG algebra morphism
  (`TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping`), and every strictly unital
  augmented `A∞` morphism into an augmented DG algebra factors uniquely by an augmented DG algebra
  morphism (`TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping_augmented`);
* functoriality of `U(-)` on strictly unital `A∞` morphisms
  (`TauCeti.AInfinityAlgebra.Augmentation.envelopingMap`), naturality of `η`, and preservation and
  reflection of quasi-isomorphisms
  (`TauCeti.AInfinityAlgebra.Augmentation.bijective_cohomologyMap_envelopingMap_iff`).

Extending the explicit homogeneous special contraction of `Ω⁺ Tᶜ(sA⁺)` onto `(A⁺, m₁)`
(`TauCeti.AInfinityAlgebra.cobarAugmentationIdealContraction`) by the identity on the scalar unit
summand `R` yields a homogeneous special contraction `U(A) ≃ A`
(`TauCeti.AInfinityAlgebra.Augmentation.envelopingContraction`) whose inclusion is the linear part
of `η : A ⟶ U(A)`.  Consequently `η : A ⟶ U(A)` is an `A∞` quasi-isomorphism over an arbitrary
commutative ring (`TauCeti.AInfinityAlgebra.Augmentation.isQuasiIso_toEnveloping`), with no
field or flatness hypothesis.

When `(A, e)` is an augmented DG algebra viewed as an augmented `A∞` algebra, the universal
property applied to the identity morphism yields the bar--cobar counit
`U(A) ⟶ A` (`TauCeti.DGAlgAugmentation.fromEnveloping`), an augmented DG algebra morphism left
inverse to `η : A ⟶ U(A)`.  Comparing DG cohomology maps with `A∞` quasi-isomorphisms
(`TauCeti.DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso`) shows that this counit is a DG
algebra quasi-isomorphism (`TauCeti.DGAlgAugmentation.bijective_cohomologyMap_fromEnveloping`).

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.Enveloping`, `envelopingGrading`,
  `envelopingDifferential`, `envelopingAugmentation`: the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`
  and its canonical augmentation.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv` and `envelopingAugmentedHomEquiv`:
  the universal bijections between strictly unital (and augmented) `A∞` morphisms `A ⟶ D` and
  (augmented) DG algebra morphisms `U(A) ⟶ D`.
* `TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`: the canonical strictly unital augmented
  `A∞` morphism `A ⟶ U(A)`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingMap`: functorial action of `U(-)` on strictly
  unital `A∞` morphisms.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingContraction`: the explicit homogeneous special
  contraction of `U(A)` onto `(A, m₁)`.
* `TauCeti.DGAlgAugmentation.fromEnveloping`: the canonical bar--cobar counit `U(A) ⟶ A` of an
  augmented DG algebra.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.isDGAlgebra_enveloping`: `U(A)` is a DG algebra.
* `TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping` and
  `TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping_augmented`: **the universal
  property of `U(A)`** among strictly unital and augmented `A∞` morphisms into DG algebras.
* `TauCeti.AInfinityAlgebra.Augmentation.isQuasiIso_toEnveloping`: **the canonical `A∞` morphism
  `A ⟶ U(A)` is a quasi-isomorphism** over any commutative ring.
* `TauCeti.AInfinityAlgebra.Augmentation.bijective_cohomologyMap_envelopingMap_iff`: `U(f)` is a
  DG quasi-isomorphism if and only if `f` is an `A∞` quasi-isomorphism.
* `TauCeti.DGAlgAugmentation.bijective_cohomologyMap_fromEnveloping`: **the bar--cobar counit
  `U(A) ⟶ A` of an augmented DG algebra is a DG algebra quasi-isomorphism.**

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the enveloping DG algebra `Ω B∞ A`, its universal property, and the
  canonical `A∞` quasi-isomorphism `A ⟶ Ω B∞ A`.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2 and Chapter 11, for the bar--cobar resolution and its
  contracting homotopy.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC uD

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-! ### The enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)` -/

/-- The underlying algebra carrier of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)` of an augmented
`A∞` algebra `(A, ε)`. -/
abbrev Enveloping (ε : 𝒜.Augmentation) :=
  TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal)

/-- The internal `ℤ`-grading of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`. -/
noncomputable abbrev envelopingGrading (ε : 𝒜.Augmentation) :
    ℤ → Submodule R ε.Enveloping :=
  tensorAlgebraPiece
    ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1))

/-- The differential of the enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)`. -/
noncomputable abbrev envelopingDifferential (ε : 𝒜.Augmentation) :
    Module.End R ε.Enveloping :=
  cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
    (ReducedTensorWords.deconcatenation R ε.augmentationIdeal)
    ε.reducedAlgebra.barDifferential

/-- The enveloping DG algebra `U(A) = Ω Tᶜ(sA⁺)` is a differential graded algebra. -/
theorem isDGAlgebra_enveloping (ε : 𝒜.Augmentation) :
    IsDGAlgebra ε.envelopingGrading ε.envelopingDifferential :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- The canonical augmentation `U(A) ⟶ R` of the enveloping DG algebra, sending every generator of
`Ω Tᶜ(sA⁺)` to zero. -/
noncomputable abbrev envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- The canonical augmentation of `U(A)` kills every generator `s⁻¹ z`. -/
theorem envelopingAugmentation_ι (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (TensorAlgebra.ι R z) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι z

private theorem cobarBarHomEquiv_symm_id (ε : 𝒜.Augmentation) :
    (ε.reducedAlgebra.cobarBarHomEquiv ε.isDGAlgebra_enveloping).symm (DGAlgHom.id _) =
      ε.reducedAlgebra.toCobarBar :=
  ((ε.reducedAlgebra.cobarBarHomEquiv _).symm_apply_eq).2
    ε.reducedAlgebra.cobarBarHomEquiv_toCobarBar.symm

/-! ### The universal property of `U(A)` -/

section UniversalProperty

variable [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}

/-- **Strictly unital `A∞` morphisms `A ⟶ D` into a DG algebra are the DG algebra morphisms
`U(A) ⟶ D`.**  This composes restriction to the augmentation ideal (`strictlyUnitalHomEquiv`) with
the bar--cobar equivalence (`cobarBarHomEquiv`). -/
noncomputable def envelopingHomEquiv (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one} ≃
      DGAlgHom ε.isDGAlgebra_enveloping hD :=
  (ε.strictlyUnitalHomEquiv hD.strictUnit_one).trans (ε.reducedAlgebra.cobarBarHomEquiv hD)

/-- The DG algebra morphism `U(A) ⟶ D` corresponding to a strictly unital `A∞` morphism `f : A ⟶ D`
sends a generator `s⁻¹ z` to `-σ ((f ∘ incl)(z))`. -/
@[simp]
theorem envelopingHomEquiv_apply_ι (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD)
    (f : {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one})
    (z : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingHomEquiv hD f (TensorAlgebra.ι R z) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1
        ((f.1.comp ε.reducedInclusion.toAInfinityHom).taylor z) := by
  simp [envelopingHomEquiv]

/-- The canonical strictly unital `A∞` morphism `η : A ⟶ U(A)`, corresponding to the identity of
`U(A)` under `envelopingHomEquiv`. -/
noncomputable def toEnveloping (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜 ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  ((ε.envelopingHomEquiv ε.isDGAlgebra_enveloping).symm (DGAlgHom.id _)).1

/-- The canonical morphism `A ⟶ U(A)` is strictly unital. -/
theorem isStrictlyUnital_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit ε.isDGAlgebra_enveloping.strictUnit_one :=
  ((ε.envelopingHomEquiv ε.isDGAlgebra_enveloping).symm (DGAlgHom.id _)).2

/-- The canonical morphism `A ⟶ U(A)` corresponds to the identity DG algebra morphism of `U(A)`. -/
@[simp]
theorem envelopingHomEquiv_toEnveloping (ε : 𝒜.Augmentation) :
    ε.envelopingHomEquiv ε.isDGAlgebra_enveloping
        ⟨ε.toEnveloping, ε.isStrictlyUnital_toEnveloping⟩ =
      DGAlgHom.id _ :=
  Equiv.apply_symm_apply _ _

/-- Restricting the canonical morphism `A ⟶ U(A)` to the augmentation ideal recovers the nonunital
canonical morphism `A⁺ ⟶ Ω Tᶜ(sA⁺)`. -/
@[simp]
theorem toEnveloping_comp_reducedInclusion (ε : 𝒜.Augmentation) :
    ε.toEnveloping.comp ε.reducedInclusion.toAInfinityHom = ε.reducedAlgebra.toCobarBar := by
  have h := Equiv.apply_symm_apply
    (ε.strictlyUnitalHomEquiv ε.isDGAlgebra_enveloping.strictUnit_one) ε.reducedAlgebra.toCobarBar
  rw [← ε.cobarBarHomEquiv_symm_id] at h
  simpa only [strictlyUnitalHomEquiv_apply, toEnveloping, envelopingHomEquiv,
    Equiv.symm_trans_apply, ε.cobarBarHomEquiv_symm_id] using h

/-- The Taylor map of the canonical morphism `A ⟶ U(A)`. -/
@[simp]
theorem taylor_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.taylor =
      TensorAlgebra.ι R ∘ₗ
        (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1 ∘ₗ
        ReducedTensorWords.map (R := R) ε.reducedPart +
      LinearMap.toSpanSingleton R ε.Enveloping 1 ∘ₗ ε.toLinearMap ∘ₗ
        ReducedTensorWords.letter R A := by
  rw [toEnveloping, envelopingHomEquiv, Equiv.symm_trans_apply, ε.cobarBarHomEquiv_symm_id,
    taylor_strictlyUnitalHomEquiv_symm, AInfinityAlgebra.taylor_toCobarBar, LinearMap.comp_assoc]

/-- On the augmentation ideal, the linear part of `A ⟶ U(A)` agrees with the linear part of
`A⁺ ⟶ Ω Tᶜ(sA⁺)`. -/
theorem linearPart_toEnveloping_coe (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.toEnveloping.linearPart x = ε.reducedAlgebra.toCobarBar.linearPart x := by
  rw [toEnveloping, envelopingHomEquiv, Equiv.symm_trans_apply, ε.cobarBarHomEquiv_symm_id,
    linearPart_strictlyUnitalHomEquiv_symm_coe]

/-- The linear part of `A ⟶ U(A)` carries the strict unit of `A` to `1 : U(A)`. -/
theorem linearPart_toEnveloping_unit (ε : 𝒜.Augmentation) :
    ε.toEnveloping.linearPart ε.unit = 1 :=
  ε.isStrictlyUnital_toEnveloping.map_unit

/-- Explicit decomposition of the linear part of `A ⟶ U(A)` into its scalar and reduced parts. -/
theorem linearPart_toEnveloping_apply (ε : 𝒜.Augmentation) (a : A) :
    ε.toEnveloping.linearPart a =
      algebraMap R ε.Enveloping (ε a) +
        ε.reducedAlgebra.toCobarBar.linearPart (ε.reducedPart a) := by
  have ha : a = ε a • ε.unit + (ε.reducedPart a : A) := by
    rw [ε.coe_reducedPart]
    abel
  conv_lhs => rw [ha]
  rw [map_add, map_smul, ε.linearPart_toEnveloping_unit, ε.linearPart_toEnveloping_coe,
    Algebra.algebraMap_eq_smul_one]

/-- The canonical morphism `A ⟶ U(A)` commutes with the augmentations. -/
@[simp]
theorem envelopingAugmentation_comp_toEnveloping (ε : 𝒜.Augmentation) :
    ε.envelopingAugmentation.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ε.toEnveloping =
      ε.toAInfinityStrictHom.toAInfinityHom := by
  have hsu : ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit
      ε.envelopingAugmentation.toAInfinityAugmentation.isStrictUnit :=
    AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2 ε.isStrictlyUnital_toEnveloping
  rw [← DGAlgAugmentation.toAInfinityAugmentation_toAInfinityStrictHom,
    ε.comp_toAInfinityStrictHom_eq_iff ε.envelopingAugmentation.toAInfinityAugmentation
      ⟨ε.toEnveloping, hsu⟩]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, strictlyUnitalHomEquiv_apply,
    toEnveloping_comp_reducedInclusion, AInfinityAlgebra.taylor_toCobarBar,
    DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
    GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom, envelopingAugmentation_ι]

/-- The strictly unital `A∞` morphism corresponding to a DG algebra morphism `φ : U(A) ⟶ D` is `φ`
composed with the canonical morphism `A ⟶ U(A)`. -/
theorem envelopingHomEquiv_symm_apply (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD)
    (φ : DGAlgHom ε.isDGAlgebra_enveloping hD) :
    ((ε.envelopingHomEquiv hD).symm φ).1 =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  rw [envelopingHomEquiv, Equiv.symm_trans_apply, AInfinityAlgebra.cobarBarHomEquiv_symm_apply,
    ← DGAlgHom.toAInfinityStrictHom_toAInfinityStrictUnitalHom,
    ε.strictlyUnitalHomEquiv_symm_comp_strict ε.isDGAlgebra_enveloping.strictUnit_one
      hD.strictUnit_one φ.toAInfinityStrictUnitalHom,
    toEnveloping, envelopingHomEquiv, Equiv.symm_trans_apply, ε.cobarBarHomEquiv_symm_id]

/-- **The universal property of `U(A)` among strictly unital `A∞` morphisms.**  Every strictly
unital `A∞` morphism from `A` to a DG algebra `D` factors uniquely through `A ⟶ U(A)` by a DG
algebra morphism `U(A) ⟶ D`. -/
theorem bijective_comp_toEnveloping (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD) :
    Function.Bijective fun φ : DGAlgHom ε.isDGAlgebra_enveloping hD ↦
      (⟨φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        φ.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping⟩ :
        {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one}) := by
  convert (ε.envelopingHomEquiv hD).symm.bijective using 1
  funext φ
  exact Subtype.ext (ε.envelopingHomEquiv_symm_apply hD φ).symm

/-- A DG algebra augmentation is invariant under the degree-one Koszul twist because it vanishes
in every nonzero degree and the twist is the identity in degree zero. -/
private theorem apply_koszulTwist_of_dgAlgAugmentation {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD) (x : D) :
    eD ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 x) = eD x := by
  let f : D →ₗ[R] R := eD.toGradedAlgHom.toAlgHom.toLinearMap ∘ₗ
    (InternalGrading.ofDecomposition 𝒟).koszulTwist 1
  let g : D →ₗ[R] R := eD.toGradedAlgHom.toAlgHom.toLinearMap
  suffices h : f = g from LinearMap.congr_fun h x
  refine (InternalGrading.ofDecomposition 𝒟).linearMap_ext fun p y hy ↦ ?_
  simp only [f, g, LinearMap.comp_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
    DGAlgHom.coe_toGradedAlgHom]
  rw [(InternalGrading.ofDecomposition 𝒟).koszulTwist_apply_of_mem hy 1, map_smul, smul_eq_mul]
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · have h0 : eD y = 0 := by
      simpa only [DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
        GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom] using
        eD.toAInfinityAugmentation.map_of_mem_ne_zero p y (by simpa using hy) hp
    rw [h0, mul_zero]

/-- The DG algebra morphism `U(A) ⟶ D` corresponding to a strictly unital `A∞` morphism `f : A ⟶ D`
preserves augmentations if and only if `f` does. -/
theorem comp_envelopingHomEquiv_eq_iff (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD)
    (f : {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one}) :
    eD.comp (ε.envelopingHomEquiv hD f) = ε.envelopingAugmentation ↔
      eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f.1 =
        ε.toAInfinityStrictHom.toAInfinityHom := by
  have hsu : f.1.IsStrictlyUnital ε.isStrictUnit eD.toAInfinityAugmentation.isStrictUnit :=
    AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2 f.2
  rw [ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eD,
    ← DGAlgAugmentation.toAInfinityAugmentation_toAInfinityStrictHom,
    ε.comp_toAInfinityStrictHom_eq_iff eD.toAInfinityAugmentation ⟨f.1, hsu⟩]
  simp only [envelopingHomEquiv_apply_ι, map_neg, neg_eq_zero,
    apply_koszulTwist_of_dgAlgAugmentation, LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.zero_apply, strictlyUnitalHomEquiv_apply,
    DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
    GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom]

/-- **Strictly unital augmented `A∞` morphisms `A ⟶ D` into an augmented DG algebra are the
augmented DG algebra morphisms `U(A) ⟶ D`.** -/
noncomputable def envelopingAugmentedHomEquiv (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one ∧
          eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f =
            ε.toAInfinityStrictHom.toAInfinityHom} ≃
      {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation} where
  toFun f := ⟨ε.envelopingHomEquiv hD ⟨f.1, f.2.1⟩,
    (ε.comp_envelopingHomEquiv_eq_iff eD ⟨f.1, f.2.1⟩).2 f.2.2⟩
  invFun φ := ⟨((ε.envelopingHomEquiv hD).symm φ.1).1, ((ε.envelopingHomEquiv hD).symm φ.1).2,
    (ε.comp_envelopingHomEquiv_eq_iff eD _).1 <| by simpa using φ.2⟩
  left_inv f := by
    apply Subtype.ext
    dsimp only
    exact congrArg Subtype.val ((ε.envelopingHomEquiv hD).symm_apply_apply ⟨f.1, f.2.1⟩)
  right_inv φ := by
    apply Subtype.ext
    dsimp only
    exact (ε.envelopingHomEquiv hD).apply_symm_apply φ.1

/-- **The universal property of `U(A)` among strictly unital augmented `A∞` morphisms.**  Every
strictly unital augmented `A∞` morphism from `A` to an augmented DG algebra `(D, eD)` factors
uniquely through `A ⟶ U(A)` by an augmented DG algebra morphism `U(A) ⟶ D`. -/
theorem bijective_comp_toEnveloping_augmented (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD) :
    Function.Bijective fun φ :
        {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation} ↦
      (⟨φ.1.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        φ.1.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping,
        by
          rw [← AInfinityHom.comp_assoc, ← AInfinityStrictHom.toAInfinityHom_comp,
            ← NonUnitalDGAlgHom.toAInfinityStrictHom_comp, ← DGAlgHom.toNonUnitalDGAlgHom_comp,
            φ.2, ε.envelopingAugmentation_comp_toEnveloping]⟩ :
        {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one ∧
            eD.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f =
              ε.toAInfinityStrictHom.toAInfinityHom}) := by
  convert (ε.envelopingAugmentedHomEquiv eD).symm.bijective using 1
  funext φ
  exact Subtype.ext (ε.envelopingHomEquiv_symm_apply hD φ.1).symm

end UniversalProperty

/-! ### The homogeneous special contraction `U(A) ≃ A` and quasi-isomorphism -/

private theorem coe_reducedAlgebra_differential (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    (ε.reducedAlgebra.differential x : A) = 𝒜.differential x := by
  rw [AInfinityAlgebra.differential_apply, AInfinityAlgebra.differential_apply, ε.reducedAlgebra_m,
    ε.coe_reducedOperation]
  congr 1
  funext i
  fin_cases i
  rfl

private theorem reducedPart_envelopingDifferential (ε : 𝒜.Augmentation) (z : ε.Enveloping) :
    ε.envelopingAugmentation.reducedPart (ε.envelopingDifferential z) =
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential
        (ε.envelopingAugmentation.reducedPart z) := by
  apply Subtype.ext
  rw [DGAlgAugmentation.coe_reducedPart, ε.envelopingAugmentation.map_d, map_zero, sub_zero,
    IsNonCounitalDGCoalgebra.coe_cobarReducedDifferential, DGAlgAugmentation.coe_reducedPart,
    map_sub, ε.isDGAlgebra_enveloping.map_algebraMap, sub_zero]

private theorem envelopingAugmentation_linearPart_toEnveloping (ε : 𝒜.Augmentation) (a : A) :
    ε.envelopingAugmentation (ε.toEnveloping.linearPart a) = ε a := by
  rw [ε.linearPart_toEnveloping_apply, map_add, ε.envelopingAugmentation.map_algebraMap,
    ← AInfinityAlgebra.coe_cobarAugmentationIdealContraction_incl,
    (ε.envelopingAugmentation.mem_augmentationIdeal).mp
      (ε.reducedAlgebra.cobarAugmentationIdealContraction.incl (ε.reducedPart a)).2,
    add_zero]

private theorem reducedPart_linearPart_toEnveloping (ε : 𝒜.Augmentation) (a : A) :
    ε.envelopingAugmentation.reducedPart (ε.toEnveloping.linearPart a) =
      ε.reducedAlgebra.cobarAugmentationIdealContraction.incl (ε.reducedPart a) := by
  apply Subtype.ext
  rw [DGAlgAugmentation.coe_reducedPart, ε.envelopingAugmentation_linearPart_toEnveloping,
    ε.linearPart_toEnveloping_apply, AInfinityAlgebra.coe_cobarAugmentationIdealContraction_incl,
    add_sub_cancel_left]

/-- The projection `U(A) ⟶ A` extending the reduced bar--cobar contraction projection by the
augmentation on the scalar summand. -/
private noncomputable def envelopingProj (ε : 𝒜.Augmentation) : ε.Enveloping →ₗ[R] A :=
  ε.unitHom ∘ₗ ε.envelopingAugmentation.toGradedAlgHom.toAlgHom.toLinearMap +
    ε.augmentationIdeal.subtype ∘ₗ ε.reducedAlgebra.cobarAugmentationIdealContraction.proj ∘ₗ
      ε.envelopingAugmentation.reducedPart

/-- The contracting homotopy `U(A) ⟶ U(A)` extending the reduced bar--cobar homotopy by zero on
the scalar summand. -/
private noncomputable def envelopingHomotopy (ε : 𝒜.Augmentation) :
    Module.End R ε.Enveloping :=
  ε.envelopingAugmentation.augmentationIdeal.toSubmodule.subtype ∘ₗ
    ε.reducedAlgebra.cobarAugmentationIdealContraction.homotopy ∘ₗ
    ε.envelopingAugmentation.reducedPart

private theorem isHomogeneous_envelopingAugmentation_reducedPart (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.envelopingAugmentation.reducedPart
      ε.envelopingGrading
      ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [add_zero, IsNonCounitalDGCoalgebra.mem_cobarReducedGrading_piece,
    DGAlgAugmentation.coe_reducedPart]
  rcases eq_or_ne p 0 with rfl | hp
  · refine Submodule.sub_mem _ hz ?_
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (SetLike.one_mem_graded ε.envelopingGrading)
  · have h0 : ε.envelopingAugmentation z = 0 := by
      simpa only [DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
        GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom] using
        ε.envelopingAugmentation.toAInfinityAugmentation.map_of_mem_ne_zero p z
          (by simpa using hz) hp
    simpa only [h0, map_zero, sub_zero] using hz

/-- **The explicit special contraction of `U(A) = Ω Tᶜ(sA⁺)` onto `(A, m₁)`.**  It extends
`AInfinityAlgebra.cobarAugmentationIdealContraction` on the augmentation ideal by the identity on
the scalar unit summand `R`.  Its inclusion is the linear part of `toEnveloping : A ⟶ U(A)`. -/
noncomputable def envelopingContraction (ε : 𝒜.Augmentation) :
    LinearSpecialContraction ε.envelopingDifferential 𝒜.differential where
  incl := ε.toEnveloping.linearPart
  proj := ε.envelopingProj
  homotopy := ε.envelopingHomotopy
  dM_comp_incl := LinearMap.ext fun a ↦ by
    simpa [AInfinityAlgebra.differential_apply] using (ε.toEnveloping.linearPart_m_one a).symm
  proj_comp_dM := LinearMap.ext fun z ↦ by
    have hdu : 𝒜.differential ε.unit = 0 := by
      rw [AInfinityAlgebra.differential_apply, ε.isStrictUnit.unary_eq_zero]
    simp only [LinearMap.comp_apply, envelopingProj, LinearMap.add_apply, AlgHom.toLinearMap_apply,
      GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom, unitHom_apply, Submodule.coe_subtype,
      ε.envelopingAugmentation.map_d, zero_smul, zero_add, ε.reducedPart_envelopingDifferential,
      LinearContraction.proj_dM_apply, map_add, map_smul, hdu, smul_zero,
      ε.coe_reducedAlgebra_differential]
  proj_comp_incl := LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, LinearMap.id_apply, envelopingProj, LinearMap.add_apply,
      AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom,
      unitHom_apply, Submodule.coe_subtype, ε.envelopingAugmentation_linearPart_toEnveloping,
      ε.reducedPart_linearPart_toEnveloping, LinearContraction.proj_incl_apply, ε.coe_reducedPart,
      add_sub_cancel]
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun z ↦ by
    have hc := congrArg Subtype.val <|
      LinearMap.congr_fun
        ε.reducedAlgebra.cobarAugmentationIdealContraction.dM_comp_homotopy_add_homotopy_comp_dM
        (ε.envelopingAugmentation.reducedPart z)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.coe_add, Submodule.coe_sub,
      IsNonCounitalDGCoalgebra.coe_cobarReducedDifferential,
      DGAlgAugmentation.coe_reducedPart] at hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      envelopingHomotopy, Submodule.coe_subtype, ε.reducedPart_envelopingDifferential, hc,
      envelopingProj, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
      DGAlgHom.coe_toGradedAlgHom, unitHom_apply, map_add, map_smul,
      ε.linearPart_toEnveloping_unit, ε.linearPart_toEnveloping_coe,
      ← AInfinityAlgebra.coe_cobarAugmentationIdealContraction_incl,
      Algebra.algebraMap_eq_smul_one]
    abel
  homotopy_comp_incl := LinearMap.ext fun a ↦ by
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, envelopingHomotopy,
      Submodule.coe_subtype, ε.reducedPart_linearPart_toEnveloping,
      LinearSpecialContraction.homotopy_incl_apply, Submodule.coe_zero]
  proj_comp_homotopy := LinearMap.ext fun z ↦ by
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, envelopingProj, envelopingHomotopy,
      LinearMap.add_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
      DGAlgHom.coe_toGradedAlgHom, unitHom_apply, Submodule.coe_subtype,
      (ε.envelopingAugmentation.mem_augmentationIdeal).mp
        (ε.reducedAlgebra.cobarAugmentationIdealContraction.homotopy
          (ε.envelopingAugmentation.reducedPart z)).2,
      zero_smul, zero_add, ε.envelopingAugmentation.reducedPart_coe,
      LinearSpecialContraction.proj_homotopy_apply, Submodule.coe_zero]
  homotopy_comp_homotopy := LinearMap.ext fun z ↦ by
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, envelopingHomotopy,
      Submodule.coe_subtype, ε.envelopingAugmentation.reducedPart_coe,
      LinearSpecialContraction.homotopy_homotopy_apply, Submodule.coe_zero]

/-- The inclusion of the enveloping contraction is the linear part of `toEnveloping`. -/
@[simp]
theorem envelopingContraction_incl (ε : 𝒜.Augmentation) :
    ε.envelopingContraction.incl = ε.toEnveloping.linearPart := (rfl)

private theorem envelopingContraction_proj (ε : 𝒜.Augmentation) :
    ε.envelopingContraction.proj = ε.envelopingProj := (rfl)

private theorem envelopingContraction_homotopy (ε : 𝒜.Augmentation) :
    ε.envelopingContraction.homotopy = ε.envelopingHomotopy := (rfl)

/-- The inclusion of the enveloping contraction has degree zero. -/
theorem isHomogeneous_envelopingContraction_incl (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.envelopingContraction.incl 𝒜.grading.piece ε.envelopingGrading 0 := by
  simpa only [envelopingContraction_incl, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading,
    InternalGrading.ofDecomposition_piece] using ε.toEnveloping.isHomogeneous_linearPart

/-- The projection of the enveloping contraction has degree zero. -/
theorem isHomogeneous_envelopingContraction_proj (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.envelopingContraction.proj ε.envelopingGrading 𝒜.grading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [add_zero, envelopingContraction_proj, envelopingProj, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom, unitHom_apply, Submodule.coe_subtype]
  refine Submodule.add_mem _ ?_ ?_
  · rcases eq_or_ne p 0 with rfl | hp
    · exact Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero
    · have h0 : ε.envelopingAugmentation z = 0 := by
        simpa only [DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
          GradedAlgHom.coe_toAlgHom, DGAlgHom.coe_toGradedAlgHom] using
          ε.envelopingAugmentation.toAInfinityAugmentation.map_of_mem_ne_zero p z
            (by simpa using hz) hp
      rw [h0, zero_smul]
      exact Submodule.zero_mem _
  · have hred := ε.isHomogeneous_envelopingAugmentation_reducedPart.map_mem hz
    rw [add_zero] at hred
    have hproj :=
      ε.reducedAlgebra.isHomogeneous_cobarAugmentationIdealContraction_proj.map_mem hred
    set w := ε.reducedAlgebra.cobarAugmentationIdealContraction.proj
      (ε.envelopingAugmentation.reducedPart z)
    rw [add_zero, ε.reducedAlgebra_grading, ε.reducedGrading_piece] at hproj
    exact hproj

/-- The contracting homotopy of the enveloping contraction has degree `-1`. -/
theorem isHomogeneous_envelopingContraction_homotopy (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.envelopingContraction.homotopy
      ε.envelopingGrading ε.envelopingGrading (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [envelopingContraction_homotopy]
  have hred := ε.isHomogeneous_envelopingAugmentation_reducedPart.map_mem hz
  rw [add_zero] at hred
  have hhom :=
    ε.reducedAlgebra.isHomogeneous_cobarAugmentationIdealContraction_homotopy.map_mem hred
  exact ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.mem_cobarReducedGrading_piece.1 hhom

/-- **The canonical `A∞` morphism `A ⟶ U(A)` is a quasi-isomorphism.**  This holds over an
arbitrary commutative ring, directly from the explicit special contraction `envelopingContraction`
of `U(A) = Ω Tᶜ(sA⁺)` onto `(A, m₁)`. -/
theorem isQuasiIso_toEnveloping (ε : 𝒜.Augmentation) : ε.toEnveloping.IsQuasiIso := by
  let c := ε.envelopingContraction
  rw [AInfinityHom.isQuasiIso_iff_forall_cycles]
  refine ⟨fun y hy ↦ ?_, fun x _ hfx ↦ ?_⟩
  · have hy' : ε.envelopingDifferential y = 0 := by
      simpa [AInfinityAlgebra.mem_cycles] using hy
    have hpx : c.proj y ∈ 𝒜.cycles := by
      rw [AInfinityAlgebra.mem_cycles, ← AInfinityAlgebra.differential_apply,
        ← c.proj_dM_apply, hy', map_zero]
    refine ⟨c.proj y, hpx, ?_⟩
    rw [AInfinityAlgebra.mem_boundaries]
    refine ⟨-c.homotopy y, ?_⟩
    have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, hy', map_zero, add_zero] at hc
    simpa [c, envelopingContraction_incl, map_neg, neg_sub] using congrArg (- ·) hc
  · rw [AInfinityAlgebra.mem_boundaries] at hfx ⊢
    obtain ⟨w, hw⟩ := hfx
    refine ⟨c.proj w, ?_⟩
    have hw' : ε.envelopingDifferential w = c.incl x := by
      simpa [c, envelopingContraction_incl] using hw
    rw [← AInfinityAlgebra.differential_apply, ← c.proj_dM_apply, hw', c.proj_incl_apply]

/-! ### Functoriality of `U(-)` on strictly unital `A∞` morphisms -/

/-- The DG algebra morphism `U(f) : U(A) ⟶ U(B)` induced by a strictly unital `A∞` morphism
`f : A ⟶ B` between augmented `A∞` algebras. -/
noncomputable def envelopingMap (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    DGAlgHom εA.isDGAlgebra_enveloping εB.isDGAlgebra_enveloping :=
  εA.envelopingHomEquiv εB.isDGAlgebra_enveloping
    ⟨εB.toEnveloping.comp f, εB.isStrictlyUnital_toEnveloping.comp hf⟩

/-- Naturality of `η : A ⟶ U(A)`: `U(f) ∘ η_A = η_B ∘ f`. -/
@[simp]
theorem envelopingMap_comp_toEnveloping (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    (εA.envelopingMap εB f hf).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        εA.toEnveloping =
      εB.toEnveloping.comp f := by
  rw [← εA.envelopingHomEquiv_symm_apply εB.isDGAlgebra_enveloping, envelopingMap,
    Equiv.symm_apply_apply]

/-- `U` sends the identity `A∞` morphism to the identity DG algebra morphism. -/
@[simp]
theorem envelopingMap_id (ε : 𝒜.Augmentation) :
    ε.envelopingMap ε (AInfinityHom.id 𝒜) (AInfinityHom.isStrictlyUnital_id ε.isStrictUnit) =
      DGAlgHom.id _ := by
  apply (ε.bijective_comp_toEnveloping ε.isDGAlgebra_enveloping).1
  apply Subtype.ext
  simp

/-- `U` preserves composition of strictly unital `A∞` morphisms. -/
theorem envelopingMap_comp (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) (εC : 𝒞.Augmentation)
    {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ}
    (hg : g.IsStrictlyUnital εB.isStrictUnit εC.isStrictUnit)
    (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    εA.envelopingMap εC (g.comp f) (hg.comp hf) =
      (εB.envelopingMap εC g hg).comp (εA.envelopingMap εB f hf) := by
  apply (εA.bijective_comp_toEnveloping εC.isDGAlgebra_enveloping).1
  apply Subtype.ext
  dsimp only
  let φgf := εA.envelopingMap εC (g.comp f) (hg.comp hf)
  let Ugf := φgf.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom
  let Ug := (εB.envelopingMap εC g hg).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom
  let Uf := (εA.envelopingMap εB f hf).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom
  calc
    Ugf.comp εA.toEnveloping
      = εC.toEnveloping.comp (g.comp f) := εA.envelopingMap_comp_toEnveloping εC _ _
    _ = (εC.toEnveloping.comp g).comp f := (AInfinityHom.comp_assoc ..).symm
    _ = (Ug.comp εB.toEnveloping).comp f := by
        rw [εB.envelopingMap_comp_toEnveloping εC g hg]
    _ = Ug.comp (εB.toEnveloping.comp f) := AInfinityHom.comp_assoc ..
    _ = Ug.comp (Uf.comp εA.toEnveloping) := by
        rw [εA.envelopingMap_comp_toEnveloping εB f hf]
    _ = (Ug.comp Uf).comp εA.toEnveloping := (AInfinityHom.comp_assoc ..).symm
    _ = ((εB.envelopingMap εC g hg).comp
          (εA.envelopingMap εB f hf)).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
            εA.toEnveloping := by
        simp only [Ug, Uf, DGAlgHom.toNonUnitalDGAlgHom_comp,
          NonUnitalDGAlgHom.toAInfinityStrictHom_comp, AInfinityStrictHom.toAInfinityHom_comp]

/-- If a strictly unital `A∞` morphism `f : A ⟶ B` preserves augmentations, then `U(f)` preserves
the canonical augmentations of `U(A)` and `U(B)`. -/
theorem comp_envelopingMap (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    {f : AInfinityHom 𝒜 ℬ} (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit)
    (haug : εB.toAInfinityStrictHom.toAInfinityHom.comp f =
      εA.toAInfinityStrictHom.toAInfinityHom) :
    εB.envelopingAugmentation.comp (εA.envelopingMap εB f hf) = εA.envelopingAugmentation := by
  rw [envelopingMap, εA.comp_envelopingHomEquiv_eq_iff εB.envelopingAugmentation,
    ← AInfinityHom.comp_assoc, εB.envelopingAugmentation_comp_toEnveloping, haug]

/-- `U(f)` is a DG algebra quasi-isomorphism if and only if `f` is an `A∞` quasi-isomorphism. -/
theorem bijective_cohomologyMap_envelopingMap_iff (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : AInfinityHom 𝒜 ℬ) (hf : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit) :
    Function.Bijective (εA.envelopingMap εB f hf).cohomologyMap ↔ f.IsQuasiIso := by
  rw [DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso]
  constructor
  · intro hU
    refine εB.isQuasiIso_toEnveloping.of_postcomp ?_
    rw [← εA.envelopingMap_comp_toEnveloping εB f hf]
    exact hU.comp εA.isQuasiIso_toEnveloping
  · intro hqf
    refine εA.isQuasiIso_toEnveloping.of_precomp ?_
    rw [εA.envelopingMap_comp_toEnveloping εB f hf]
    exact εB.isQuasiIso_toEnveloping.comp hqf

end AInfinityAlgebra.Augmentation

/-! ### The bar--cobar counit `U(A) ⟶ A` for an augmented DG algebra -/

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- The canonical bar--cobar counit `U(A) ⟶ A` of an augmented DG algebra `(A, e)`, corresponding
to the identity `A∞` morphism of `A` under the universal property of `U(A)`. -/
noncomputable def fromEnveloping (e : DGAlgAugmentation hA) :
    DGAlgHom e.toAInfinityAugmentation.isDGAlgebra_enveloping hA :=
  e.toAInfinityAugmentation.envelopingHomEquiv hA
    ⟨AInfinityHom.id _,
      AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2
        (AInfinityHom.isStrictlyUnital_id hA.strictUnit_one)⟩

/-- On generators `s⁻¹ z` of `U(A) = Ω Tᶜ(sA⁺)`, the counit `U(A) ⟶ A` projects onto the
single-letter component with the Koszul twist `-σ` and annihilates bar words of length at least
two. -/
@[simp]
theorem fromEnveloping_ι (e : DGAlgAugmentation hA)
    (z : ReducedTensorWords R e.toAInfinityAugmentation.augmentationIdeal) :
    e.fromEnveloping (TensorAlgebra.ι R z) =
      -(InternalGrading.ofDecomposition 𝒜).koszulTwist 1
        (ReducedTensorWords.letter R e.toAInfinityAugmentation.augmentationIdeal z : A) := by
  simp [fromEnveloping, AInfinityStrictHom.taylor_toAInfinityHom]

/-- On a single-letter generator `s⁻¹ (s a)`, the counit evaluates to `-σ(a)`. -/
theorem fromEnveloping_ι_ofLetter (e : DGAlgAugmentation hA)
    (x : e.toAInfinityAugmentation.augmentationIdeal) :
    e.fromEnveloping (TensorAlgebra.ι R (ReducedTensorWords.ofLetter R _ x)) =
      -(InternalGrading.ofDecomposition 𝒜).koszulTwist 1 (x : A) := by
  simp

/-- The bar--cobar counit `U(A) ⟶ A` preserves augmentations. -/
@[simp]
theorem comp_fromEnveloping (e : DGAlgAugmentation hA) :
    e.comp e.fromEnveloping = e.toAInfinityAugmentation.envelopingAugmentation := by
  rw [fromEnveloping, e.toAInfinityAugmentation.comp_envelopingHomEquiv_eq_iff e,
    AInfinityHom.comp_id, e.toAInfinityAugmentation_toAInfinityStrictHom]

/-- The bar--cobar counit `U(A) ⟶ A` is a left inverse to the canonical `A∞` morphism
`A ⟶ U(A)`. -/
@[simp]
theorem fromEnveloping_comp_toEnveloping (e : DGAlgAugmentation hA) :
    e.fromEnveloping.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        e.toAInfinityAugmentation.toEnveloping =
      AInfinityHom.id _ := by
  rw [← e.toAInfinityAugmentation.envelopingHomEquiv_symm_apply hA, fromEnveloping,
    Equiv.symm_apply_apply]

/-- Naturality of the bar--cobar counit under DG algebra morphisms. -/
theorem comp_fromEnveloping_eq (eA : DGAlgAugmentation hA) (eB : DGAlgAugmentation hB)
    (g : DGAlgHom hA hB) :
    g.comp eA.fromEnveloping =
      eB.fromEnveloping.comp
        (eA.toAInfinityAugmentation.envelopingMap eB.toAInfinityAugmentation
          g.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom
          (AInfinityHom.isStrictlyUnital_iff_of_strictUnit.2
            g.isStrictlyUnital_toAInfinityHom)) := by
  apply (eA.toAInfinityAugmentation.bijective_comp_toEnveloping hB).1
  apply Subtype.ext
  dsimp only
  rw [DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc,
    eA.fromEnveloping_comp_toEnveloping, AInfinityHom.comp_id,
    DGAlgHom.toNonUnitalDGAlgHom_comp, NonUnitalDGAlgHom.toAInfinityStrictHom_comp,
    AInfinityStrictHom.toAInfinityHom_comp, AInfinityHom.comp_assoc,
    AInfinityAlgebra.Augmentation.envelopingMap_comp_toEnveloping, ← AInfinityHom.comp_assoc,
    eB.fromEnveloping_comp_toEnveloping, AInfinityHom.id_comp]

/-- The bar--cobar counit `U(A) ⟶ A` is an `A∞` quasi-isomorphism. -/
theorem isQuasiIso_fromEnveloping (e : DGAlgAugmentation hA) :
    e.fromEnveloping.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsQuasiIso :=
  e.toAInfinityAugmentation.isQuasiIso_toEnveloping.of_precomp
    (by rw [e.fromEnveloping_comp_toEnveloping]; exact AInfinityHom.isQuasiIso_id _)

/-- **The bar--cobar counit `U(A) ⟶ A` of an augmented DG algebra is a DG algebra
quasi-isomorphism.**  This holds over an arbitrary commutative ring. -/
theorem bijective_cohomologyMap_fromEnveloping (e : DGAlgAugmentation hA) :
    Function.Bijective e.fromEnveloping.cohomologyMap :=
  (DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso e.fromEnveloping).2 e.isQuasiIso_fromEnveloping

end DGAlgAugmentation

end TauCeti
