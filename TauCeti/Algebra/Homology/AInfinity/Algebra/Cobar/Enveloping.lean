/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation

/-!
# The enveloping DG algebra of an augmented `A∞` algebra

For an augmented `A∞` algebra `(A, ε)` over a commutative ring `R`, its augmentation ideal `ker ε`
carries the reduced nonunital `A∞` algebra structure `ε.reducedAlgebra`, whose bar construction
`Tᶜ(s (ker ε))` is a noncounital differential graded coalgebra.  The cobar construction
`U(A) = Ω Tᶜ(s (ker ε))` is the **enveloping differential graded algebra** of `(A, ε)`: a unital,
canonically augmented differential graded algebra receiving a canonical strictly unital, augmented
`A∞` morphism `A ⟶ U(A)` (`TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`).

Combining the strictly unital extension equivalence
(`TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`) with the cobar--bar universal
property of the reduced algebra (`TauCeti.AInfinityAlgebra.cobarBarHomEquiv`) yields the universal
property of the enveloping DG algebra over any commutative ring `R`, without field, flatness, or
conilpotence assumptions:

* Strictly unital `A∞` morphisms `A ⟶ D` into any unital DG algebra `D` correspond bijectively to
  DG algebra morphisms `U(A) ⟶ D` (`envelopingHomEquiv`, `bijective_comp_toEnveloping`).
* Strictly unital augmented `A∞` morphisms `A ⟶ D` into any augmented DG algebra `(D, eD)`
  correspond bijectively to augmented DG algebra morphisms `U(A) ⟶ D`
  (`envelopingAugmentedHomEquiv`).

Specializing to an augmented DG algebra `(D, eD)`, the identity `A∞` morphism of `D` corresponds to
the canonical augmented DG algebra counit `Ω Tᶜ(s (ker eD)) ⟶ D`
(`DGAlgAugmentation.envelopingCounit`), which retracts `toEnveloping`
(`envelopingCounit_comp_toEnveloping`) and commutes with the augmentations
(`comp_envelopingCounit`).

## Main definitions

* `TauCeti.DGAlgAugmentation.toAInfinityAugmentation`: an augmented DG algebra as an augmented
  `A∞` algebra.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentation`: the canonical augmentation on
  the enveloping DG algebra `Ω Tᶜ(s (ker ε))`.
* `TauCeti.AInfinityAlgebra.Augmentation.toEnveloping`: the canonical strictly unital, augmented
  `A∞` morphism `A ⟶ Ω Tᶜ(s (ker ε))`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingHomEquiv`: strictly unital `A∞` morphisms
  `A ⟶ D` correspond to DG algebra morphisms `Ω Tᶜ(s (ker ε)) ⟶ D`.
* `TauCeti.AInfinityAlgebra.Augmentation.envelopingAugmentedHomEquiv`: strictly unital augmented
  `A∞` morphisms `A ⟶ D` correspond to augmented DG algebra morphisms `Ω Tᶜ(s (ker ε)) ⟶ D`.
* `TauCeti.DGAlgAugmentation.envelopingCounit`: the canonical augmented DG algebra morphism
  `Ω Tᶜ(s (ker eD)) ⟶ D`.

## Main results

* `TauCeti.DGAlgHom.isAugmented_toAInfinityHom_iff`: a DG algebra morphism is augmented as an `A∞`
  morphism if and only if it commutes with the DG augmentations.
* `TauCeti.AInfinityAlgebra.Augmentation.bijective_comp_toEnveloping`: the universal property of
  the enveloping DG algebra for strictly unital `A∞` morphisms.
* `TauCeti.AInfinityAlgebra.Augmentation.comp_eq_envelopingAugmentation_iff`: characterization of
  augmented DG algebra morphisms out of `Ω Tᶜ(s (ker ε))`.
* `TauCeti.DGAlgAugmentation.envelopingCounit_comp_toEnveloping` and
  `TauCeti.DGAlgAugmentation.comp_envelopingCounit`: the bar--cobar counit retracts
  `toEnveloping` and respects augmentations.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the enveloping DG algebra `Ω B∞ A` and its universal property.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, PhD thesis (2003), Chapter 2, for the
  bar--cobar adjunction and counit `Ω B A ⟶ A`.
-/

public section

namespace TauCeti

universe uR uA uB uD

/-! ### Augmented DG algebras -/

section DGBridge

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGAlgAugmentation

/-- An augmentation of a differential graded algebra induces an augmentation of its associated
`A∞` algebra, with the algebra unit as strict unit. -/
noncomputable def toAInfinityAugmentation (e : DGAlgAugmentation hA) :
    hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := hA.strictUnit_one
  toLinearMap := e.toGradedAlgHom.toAlgHom.toLinearMap
  map_unit := map_one e
  map_of_mem_ne_zero p x hx hp := by
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading, InternalGrading.ofDecomposition_piece]
      at hx
    rcases (mem_trivialGrading_iff R R).1 (e.map_mem hx) with rfl | h0
    · exact absurd rfl hp
    · exact h0
  map_binary x y := by
    simp only [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, AlgHom.toLinearMap_apply,
      GradedAlgHom.coe_toAlgHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact map_mul e x y
  map_m_of_ne_two n hn0 hn2 x := by
    match n with
    | 0 => omega
    | 1 =>
      simp only [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, AlgHom.toLinearMap_apply,
        GradedAlgHom.coe_toAlgHom]
      exact e.map_d (x 0)
    | 2 => omega
    | n + 3 =>
      simp only [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_add_three, zero_apply, map_zero]

/-- The strict unit selected by `toAInfinityAugmentation` is `1`. -/
@[simp]
theorem toAInfinityAugmentation_unit (e : DGAlgAugmentation hA) :
    e.toAInfinityAugmentation.unit = 1 := (rfl)

/-- The underlying linear map of `toAInfinityAugmentation` is the DG augmentation. -/
@[simp]
theorem toAInfinityAugmentation_toLinearMap (e : DGAlgAugmentation hA) :
    e.toAInfinityAugmentation.toLinearMap = e.toGradedAlgHom.toAlgHom.toLinearMap := (rfl)

/-- Evaluating `toAInfinityAugmentation` agrees with evaluating the DG augmentation. -/
theorem toAInfinityAugmentation_apply (e : DGAlgAugmentation hA) (a : A) :
    e.toAInfinityAugmentation a = e a := (rfl)

end DGAlgAugmentation

namespace DGAlgHom

/-- A morphism of augmented DG algebras is augmented as an `A∞` morphism if and only if it
commutes with the DG augmentations. -/
theorem isAugmented_toAInfinityHom_iff (f : DGAlgHom hA hB) (eA : DGAlgAugmentation hA)
    (eB : DGAlgAugmentation hB) :
    f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
        eA.toAInfinityAugmentation eB.toAInfinityAugmentation ↔
      eB.comp f = eA := by
  constructor
  · intro hf
    ext a
    simpa only [DGAlgHom.comp_apply, AInfinityStrictHom.linearPart_toAInfinityHom,
      AInfinityStrictHom.coe_toLinearMap, NonUnitalDGAlgHom.coe_toAInfinityStrictHom,
      DGAlgHom.coe_toNonUnitalDGAlgHom, DGAlgAugmentation.toAInfinityAugmentation_apply] using
      hf.map_linearPart a
  · intro hf
    rw [AInfinityHom.isAugmented_def, AInfinityStrictHom.taylor_toAInfinityHom]
    refine LinearMap.ext fun z ↦ ?_
    have hz := DFunLike.congr_fun hf (ReducedTensorWords.letter R A z)
    rw [DGAlgHom.comp_apply] at hz
    simp only [LinearMap.comp_apply, DGAlgAugmentation.toAInfinityAugmentation_toLinearMap,
      AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom, AInfinityStrictHom.coe_toLinearMap,
      NonUnitalDGAlgHom.coe_toAInfinityStrictHom, DGAlgHom.coe_toNonUnitalDGAlgHom]
    exact hz

/-- A DG algebra morphism commuting with augmentations is an augmented `A∞` morphism. -/
theorem isAugmented_toAInfinityHom {eA : DGAlgAugmentation hA} {eB : DGAlgAugmentation hB}
    {f : DGAlgHom hA hB} (hf : eB.comp f = eA) :
    f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsAugmented
      eA.toAInfinityAugmentation eB.toAInfinityAugmentation :=
  (f.isAugmented_toAInfinityHom_iff eA eB).2 hf

/-- A morphism of differential graded algebras is strictly unital as an `A∞` morphism. -/
theorem isStrictlyUnital_toAInfinityHom (f : DGAlgHom hA hB) :
    f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsStrictlyUnital
      hA.strictUnit_one hB.strictUnit_one := by
  rw [← f.toAInfinityStrictHom_toAInfinityStrictUnitalHom]
  exact f.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom

end DGAlgHom

end DGBridge

/-! ### The enveloping DG algebra `Ω Tᶜ(s (ker ε))` and its universal property -/

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {D : Type uD}
  [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 : AInfinityAlgebra R A}

/-- The enveloping differential graded algebra structure on `Ω Tᶜ(s (ker ε))` for an augmented `A∞`
algebra `(A, ε)`. -/
theorem isDGAlgebra_enveloping (ε : 𝒜.Augmentation) :
    IsDGAlgebra
      (tensorAlgebraPiece
        ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).shift (-1)))
      (cobarDifferential (ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1))
        (ReducedTensorWords.deconcatenation R ε.augmentationIdeal)
        ε.reducedAlgebra.barDifferential) :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential

/-- The canonical augmentation on the enveloping DG algebra `Ω Tᶜ(s (ker ε))`, killing all
desuspended generators and acting as the identity on the ground ring. -/
noncomputable def envelopingAugmentation (ε : 𝒜.Augmentation) :
    DGAlgAugmentation ε.isDGAlgebra_enveloping :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation

/-- The canonical augmentation of the enveloping DG algebra vanishes on every desuspended
generator. -/
@[simp]
theorem envelopingAugmentation_ι (ε : 𝒜.Augmentation)
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingAugmentation (TensorAlgebra.ι R w) = 0 :=
  ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι w

/-- The canonical strictly unital, augmented `A∞` morphism `A ⟶ Ω Tᶜ(s (ker ε))` into the
enveloping DG algebra, extending `ε.reducedAlgebra.toCobarBar` from the augmentation ideal. -/
noncomputable def toEnveloping (ε : 𝒜.Augmentation) :
    AInfinityHom 𝒜 ε.isDGAlgebra_enveloping.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  ((ε.strictlyUnitalHomEquiv ε.isDGAlgebra_enveloping.strictUnit_one).symm
    ε.reducedAlgebra.toCobarBar).val

/-- The canonical morphism `A ⟶ Ω Tᶜ(s (ker ε))` is strictly unital. -/
theorem isStrictlyUnital_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsStrictlyUnital ε.isStrictUnit ε.isDGAlgebra_enveloping.strictUnit_one :=
  ((ε.strictlyUnitalHomEquiv ε.isDGAlgebra_enveloping.strictUnit_one).symm
    ε.reducedAlgebra.toCobarBar).property

/-- Restricting `A ⟶ Ω Tᶜ(s (ker ε))` to the augmentation ideal recovers the reduced bar--cobar
morphism `ker ε ⟶ Ω Tᶜ(s (ker ε))`. -/
@[simp]
theorem toEnveloping_comp_reducedAlgebraInclusion (ε : 𝒜.Augmentation) :
    ε.toEnveloping.comp ε.reducedAlgebraInclusion.toAInfinityHom =
      ε.reducedAlgebra.toCobarBar := by
  simpa only [toEnveloping, ← strictlyUnitalHomEquiv_apply] using
    (ε.strictlyUnitalHomEquiv ε.isDGAlgebra_enveloping.strictUnit_one).apply_symm_apply
      ε.reducedAlgebra.toCobarBar

/-- The Taylor map of the canonical morphism `A ⟶ Ω Tᶜ(s (ker ε))`. -/
@[simp]
theorem taylor_toEnveloping (ε : 𝒜.Augmentation) (z : ReducedTensorWords R A) :
    ε.toEnveloping.taylor z =
      algebraMap R (TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal))
        (ε (ReducedTensorWords.letter R A z)) +
        TensorAlgebra.ι R
          ((ReducedTensorWords.grading (ε.reducedAlgebra.grading.shift 1)).koszulTwist 1
            (ReducedTensorWords.map (R := R) ε.reducedPart z)) := by
  rw [toEnveloping, taylor_strictlyUnitalHomEquiv_symm, Algebra.algebraMap_eq_smul_one,
    AInfinityAlgebra.taylor_toCobarBar, LinearMap.comp_apply]

/-- The linear part of the canonical morphism `A ⟶ Ω Tᶜ(s (ker ε))` sends `a` to the scalar part
`ε a` plus the linear part of `toCobarBar` on the reduced part of `a`. -/
theorem linearPart_toEnveloping (ε : 𝒜.Augmentation) (a : A) :
    ε.toEnveloping.linearPart a =
      algebraMap R (TensorAlgebra R (ReducedTensorWords R ε.augmentationIdeal)) (ε a) +
        ε.reducedAlgebra.toCobarBar.linearPart (ε.reducedPart a) := by
  rw [toEnveloping, linearPart_strictlyUnitalHomEquiv_symm, Algebra.algebraMap_eq_smul_one]

/-- The canonical morphism `A ⟶ Ω Tᶜ(s (ker ε))` is augmented with respect to
`envelopingAugmentation`. -/
theorem isAugmented_toEnveloping (ε : 𝒜.Augmentation) :
    ε.toEnveloping.IsAugmented ε ε.envelopingAugmentation.toAInfinityAugmentation := by
  refine (isAugmented_strictlyUnitalHomEquiv_symm_iff ε
    ε.envelopingAugmentation.toAInfinityAugmentation ε.reducedAlgebra.toCobarBar).2 ?_
  refine LinearMap.ext fun w ↦ ?_
  simp [AInfinityAlgebra.taylor_toCobarBar]

section UniversalProperty

variable [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}

/-- **The universal property of the enveloping DG algebra (strictly unital form)**: strictly unital
`A∞` morphisms from an augmented `A∞` algebra `(A, ε)` to a unital DG algebra `D` correspond
bijectively to DG algebra morphisms `Ω Tᶜ(s (ker ε)) ⟶ D`. -/
noncomputable def envelopingHomEquiv (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one} ≃
      DGAlgHom ε.isDGAlgebra_enveloping hD :=
  (ε.strictlyUnitalHomEquiv hD.strictUnit_one).trans (ε.reducedAlgebra.cobarBarHomEquiv hD)

/-- The DG algebra morphism associated to a strictly unital `A∞` morphism `f : A ⟶ D` acts on a
desuspended generator `s⁻¹ w` by `-σ (f (map subtype w))`. -/
@[simp]
theorem envelopingHomEquiv_apply_ι (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD)
    (f : {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
      f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one})
    (w : ReducedTensorWords R ε.augmentationIdeal) :
    ε.envelopingHomEquiv hD f (TensorAlgebra.ι R w) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1
        (f.val.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype w)) := by
  simp [envelopingHomEquiv, AInfinityHom.taylor_comp,
    AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedAlgebraInclusion]

/-- The strictly unital `A∞` morphism corresponding to a DG algebra morphism
`φ : Ω Tᶜ(s (ker ε)) ⟶ D` is the composite of `φ` with the canonical morphism
`A ⟶ Ω Tᶜ(s (ker ε))`. -/
theorem envelopingHomEquiv_symm_apply (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD)
    (φ : DGAlgHom ε.isDGAlgebra_enveloping hD) :
    ((ε.envelopingHomEquiv hD).symm φ).val =
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping := by
  have hsu : (φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
      ε.toEnveloping).IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one :=
    φ.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping
  refine congrArg Subtype.val
    ((ε.strictlyUnitalHomEquiv hD.strictUnit_one).injective (a₁ := (ε.envelopingHomEquiv hD).symm φ)
      (a₂ := ⟨_, hsu⟩) ?_)
  rw [envelopingHomEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply,
    strictlyUnitalHomEquiv_apply, AInfinityHom.comp_assoc,
    toEnveloping_comp_reducedAlgebraInclusion]
  exact ε.reducedAlgebra.cobarBarHomEquiv_symm_apply hD φ

/-- **The universal property of `Ω Tᶜ(s (ker ε))`**: precomposition with `toEnveloping` induces a
bijection between DG algebra morphisms `Ω Tᶜ(s (ker ε)) ⟶ D` and strictly unital `A∞` morphisms
`A ⟶ D`. -/
theorem bijective_comp_toEnveloping (ε : 𝒜.Augmentation) (hD : IsDGAlgebra 𝒟 dD) :
    Function.Bijective fun φ : DGAlgHom ε.isDGAlgebra_enveloping hD ↦
      (⟨φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping,
        φ.isStrictlyUnital_toAInfinityHom.comp ε.isStrictlyUnital_toEnveloping⟩ :
        {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
          f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one}) := by
  convert (ε.envelopingHomEquiv hD).symm.bijective using 1
  funext φ
  exact Subtype.ext (ε.envelopingHomEquiv_symm_apply hD φ).symm

/-- A DG algebra morphism `φ : Ω Tᶜ(s (ker ε)) ⟶ D` commutes with augmentations if and only if the
corresponding strictly unital `A∞` morphism `A ⟶ D` is augmented. -/
theorem comp_eq_envelopingAugmentation_iff (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD) (φ : DGAlgHom ε.isDGAlgebra_enveloping hD) :
    eD.comp φ = ε.envelopingAugmentation ↔
      ((ε.envelopingHomEquiv hD).symm φ).val.IsAugmented ε eD.toAInfinityAugmentation := by
  have haug :
      ((ε.envelopingHomEquiv hD).symm φ).val.IsAugmented ε eD.toAInfinityAugmentation ↔
        eD.toAInfinityAugmentation.toLinearMap ∘ₗ
          ((ε.reducedAlgebra.cobarBarHomEquiv hD).symm φ).taylor = 0 :=
    isAugmented_strictlyUnitalHomEquiv_symm_iff ε eD.toAInfinityAugmentation
      ((ε.reducedAlgebra.cobarBarHomEquiv hD).symm φ)
  rw [haug, envelopingAugmentation,
    ε.reducedAlgebra.isNonCounitalDGCoalgebra_bar.comp_eq_cobarAugmentation_iff eD φ]
  have htwist_lm :
      eD.toGradedAlgHom.toAlgHom.toLinearMap ∘ₗ
        (InternalGrading.ofDecomposition 𝒟).koszulTwist 1 =
      eD.toGradedAlgHom.toAlgHom.toLinearMap := by
    refine (InternalGrading.ofDecomposition 𝒟).linearMap_ext fun p a ha ↦ ?_
    simp only [LinearMap.comp_apply,
      (InternalGrading.ofDecomposition 𝒟).koszulTwist_apply_of_mem ha]
    rw [InternalGrading.ofDecomposition_piece] at ha
    rcases (mem_trivialGrading_iff R R).1 (eD.map_mem ha) with rfl | h0
    · simp
    · simp only [AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom, map_smul,
        show eD.toGradedAlgHom a = 0 from h0, smul_zero]
  have htwist (x : D) :
      eD.toGradedAlgHom ((InternalGrading.ofDecomposition 𝒟).koszulTwist 1 x) = eD x :=
    LinearMap.congr_fun htwist_lm x
  constructor
  · intro h
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply,
      AInfinityAlgebra.taylor_cobarBarHomEquiv_symm, LinearMap.neg_apply,
      DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
      GradedAlgHom.coe_toAlgHom, map_neg, LinearMap.coe_ofClass, htwist, h w, neg_zero]
  · intro h w
    have hw := LinearMap.congr_fun h w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply,
      AInfinityAlgebra.taylor_cobarBarHomEquiv_symm, LinearMap.neg_apply,
      DGAlgAugmentation.toAInfinityAugmentation_toLinearMap, AlgHom.toLinearMap_apply,
      GradedAlgHom.coe_toAlgHom, map_neg, LinearMap.coe_ofClass, htwist, neg_eq_zero] at hw
    exact hw

/-- **The universal property of the enveloping DG algebra (augmented form)**: strictly unital
augmented `A∞` morphisms `A ⟶ D` correspond bijectively to augmented DG algebra morphisms
`Ω Tᶜ(s (ker ε)) ⟶ D`. -/
noncomputable def envelopingAugmentedHomEquiv (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD) :
    {f : AInfinityHom 𝒜 hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        f.IsStrictlyUnital ε.isStrictUnit hD.strictUnit_one ∧
        f.IsAugmented ε eD.toAInfinityAugmentation} ≃
      {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation} where
  toFun f :=
    ⟨ε.envelopingHomEquiv hD ⟨f.val, f.property.1⟩,
      (ε.comp_eq_envelopingAugmentation_iff eD _).2 <| by
        have hEq : ((ε.envelopingHomEquiv hD).symm
            (ε.envelopingHomEquiv hD ⟨f.val, f.property.1⟩)).val = f.val :=
          congrArg Subtype.val ((ε.envelopingHomEquiv hD).symm_apply_apply ⟨f.val, f.property.1⟩)
        rw [hEq]
        exact f.property.2⟩
  invFun φ :=
    ⟨((ε.envelopingHomEquiv hD).symm φ.val).val,
      ((ε.envelopingHomEquiv hD).symm φ.val).property,
      (ε.comp_eq_envelopingAugmentation_iff eD φ.val).1 φ.property⟩
  left_inv := fun ⟨f, hsu, haug⟩ ↦ by
    apply Subtype.ext
    have h1 := (ε.envelopingHomEquiv hD).symm_apply_apply ⟨f, hsu⟩
    have h2 := congrArg Subtype.val h1
    exact h2
  right_inv := fun ⟨φ, hφ⟩ ↦ by
    apply Subtype.ext
    exact (ε.envelopingHomEquiv hD).apply_symm_apply φ

/-- The inverse of `envelopingAugmentedHomEquiv` composes an augmented DG algebra morphism with
the canonical morphism `A ⟶ Ω Tᶜ(s (ker ε))`. -/
@[simp]
theorem envelopingAugmentedHomEquiv_symm_val (ε : 𝒜.Augmentation) {hD : IsDGAlgebra 𝒟 dD}
    (eD : DGAlgAugmentation hD)
    (φ : {φ : DGAlgHom ε.isDGAlgebra_enveloping hD // eD.comp φ = ε.envelopingAugmentation}) :
    ((ε.envelopingAugmentedHomEquiv eD).symm φ).val =
      φ.val.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp ε.toEnveloping :=
  ε.envelopingHomEquiv_symm_apply hD φ.val

end UniversalProperty

end AInfinityAlgebra.Augmentation

/-! ### The bar--cobar counit for augmented DG algebras -/

namespace DGAlgAugmentation

variable {R : Type uR} {D : Type uD} [CommRing R] [Ring D] [Algebra R D]
  {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}
  {hD : IsDGAlgebra 𝒟 dD}

/-- The canonical bar--cobar counit `Ω Tᶜ(s (ker eD)) ⟶ D` of an augmented DG algebra `(D, eD)`,
corresponding to the identity `A∞` morphism of `D` under the universal property of the enveloping
DG algebra. -/
noncomputable def envelopingCounit (eD : DGAlgAugmentation hD) :
    DGAlgHom eD.toAInfinityAugmentation.isDGAlgebra_enveloping hD :=
  eD.toAInfinityAugmentation.envelopingHomEquiv hD
    ⟨AInfinityHom.id _, AInfinityHom.isStrictlyUnital_id hD.strictUnit_one⟩

/-- On a desuspended generator `s⁻¹ w`, the bar--cobar counit extracts the single-letter component
of `w` and applies `-σ` (the negative Koszul twist of `D`). -/
@[simp]
theorem envelopingCounit_ι (eD : DGAlgAugmentation hD)
    (w : ReducedTensorWords R eD.toAInfinityAugmentation.augmentationIdeal) :
    eD.envelopingCounit (TensorAlgebra.ι R w) =
      -(InternalGrading.ofDecomposition 𝒟).koszulTwist 1
        (ReducedTensorWords.letter R eD.toAInfinityAugmentation.augmentationIdeal w : D) := by
  rw [envelopingCounit, AInfinityAlgebra.Augmentation.envelopingHomEquiv_apply_ι,
    AInfinityHom.taylor_id, ← LinearMap.comp_apply (ReducedTensorWords.letter R D),
    ReducedTensorWords.letter_comp_map]
  rfl

/-- Composing the bar--cobar counit `Ω Tᶜ(s (ker eD)) ⟶ D` with the canonical `A∞` morphism
`D ⟶ Ω Tᶜ(s (ker eD))` gives the identity `A∞` morphism of `D`. -/
@[simp]
theorem envelopingCounit_comp_toEnveloping (eD : DGAlgAugmentation hD) :
    eD.envelopingCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        eD.toAInfinityAugmentation.toEnveloping =
      AInfinityHom.id hD.toIsNonUnitalDGAlgebra.toAInfinityAlgebra := by
  rw [← eD.toAInfinityAugmentation.envelopingHomEquiv_symm_apply hD eD.envelopingCounit,
    envelopingCounit, Equiv.symm_apply_apply]

/-- The bar--cobar counit `Ω Tᶜ(s (ker eD)) ⟶ D` respects augmentations. -/
@[simp]
theorem comp_envelopingCounit (eD : DGAlgAugmentation hD) :
    eD.comp eD.envelopingCounit = eD.toAInfinityAugmentation.envelopingAugmentation := by
  rw [eD.toAInfinityAugmentation.comp_eq_envelopingAugmentation_iff eD eD.envelopingCounit,
    eD.toAInfinityAugmentation.envelopingHomEquiv_symm_apply hD eD.envelopingCounit,
    eD.envelopingCounit_comp_toEnveloping]
  exact AInfinityHom.isAugmented_id _

end DGAlgAugmentation

end TauCeti
