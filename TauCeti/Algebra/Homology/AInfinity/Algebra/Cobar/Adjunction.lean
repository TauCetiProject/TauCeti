/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain

/-!
# Functoriality, counit, and triangle identities of the `A∞` bar–cobar adjunction

Building on `TauCeti.AInfinityAlgebra.cobarBarHomEquiv` and `TauCeti.AInfinityAlgebra.toCobarBar`,
this file upgrades `Ω Tᶜ(s-)` to a functor from nonunital `A∞` algebras (with arbitrary `A∞`
morphisms) to differential graded algebras and completes the bar–cobar adjunction:

* any `A∞` morphism `g : A ⟶ A'` induces a strict DG algebra morphism
  `g.cobarMap : Ω Tᶜ(sA) → Ω Tᶜ(sA')` via `g.barMap`, preserving identities and composition and
  making `toCobarBar` natural;
* `cobarBarHomEquiv` is natural in both the source `A∞` algebra and the target DG algebra;
* for a DG algebra `B`, the counit `IsDGAlgebra.cobarCounit : Ω Tᶜ(sB) → B` projects desuspended
  generators onto single letters and satisfies both triangle identities with `toCobarBar`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 2.
-/

public section

open TensorAlgebra

namespace TauCeti

universe uR uA uA' uA'' uB uC

variable {R : Type uR} [CommRing R]

namespace AInfinityAlgebra

section Unit

variable {A : Type uA} [AddCommGroup A] [Module R A] (𝒜 : AInfinityAlgebra R A)

/-- On a single letter `a`, `toCobarBar.linearPart` is `s⁻¹ [s a]` twisted by `(-1)^(|a|-1)`. -/
theorem linearPart_toCobarBar_apply (a : A) :
    𝒜.toCobarBar.linearPart a =
      ι R (ReducedTensorWords.ofLetter R A ((𝒜.grading.shift 1).koszulTwist 1 a)) := by
  rw [AInfinityHom.linearPart_apply, taylor_toCobarBar, LinearMap.comp_apply,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

section Target

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)

/-- Evaluated via the source Koszul twist `σ` of `Tᶜ(sA)`, `cobarBarHomEquiv` sends `s⁻¹ z` to
`f.taylor (σ z)`. -/
theorem cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) (z : ReducedTensorWords R A) :
    𝒜.cobarBarHomEquiv hB f (ι R z) =
      f.taylor ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 z) := by
  have hg := f.isHomogeneous_taylor
  rw [← ReducedTensorWords.grading_piece] at hg
  have hz := hg.koszulTwist_apply 1 z
  rw [InternalGrading.koszulTwist_one_shift_one, IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading]
    at hz
  rw [cobarBarHomEquiv_apply_ι]
  simpa using hz

/-- In terms of the source Koszul twist `σ` of `Tᶜ(sA)`, `((cobarBarHomEquiv 𝒜 hB).symm φ).taylor`
restricts `φ` to desuspended generators after `σ`. -/
theorem taylor_cobarBarHomEquiv_symm_eq
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    ((𝒜.cobarBarHomEquiv hB).symm φ).taylor =
      (φ : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] B) ∘ₗ ι R ∘ₗ
        (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 := by
  rw [cobarBarHomEquiv_symm_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_toCobarBar]
  exact LinearMap.ext fun _ ↦ by simp

/-- Every `A∞` morphism `f : A ⟶ B` into a DG algebra factors through `toCobarBar` via
`cobarBarHomEquiv 𝒜 hB f`. -/
@[simp]
theorem toAInfinityHom_cobarBarHomEquiv_comp_toCobarBar
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    (𝒜.cobarBarHomEquiv hB f).toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        𝒜.toCobarBar = f := by
  rw [← 𝒜.cobarBarHomEquiv_symm_apply hB, Equiv.symm_apply_apply]

/-- A DG algebra morphism `φ : Ω Tᶜ(sA) → B` equals `cobarBarHomEquiv 𝒜 hB f` if and only if
postcomposing `toCobarBar` with `φ` recovers `f`. -/
theorem eq_cobarBarHomEquiv_iff
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    φ = 𝒜.cobarBarHomEquiv hB f ↔
      φ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar = f :=
  ⟨fun h ↦ h ▸ 𝒜.toAInfinityHom_cobarBarHomEquiv_comp_toCobarBar hB f,
    fun h ↦ by rw [← h, ← 𝒜.cobarBarHomEquiv_symm_apply hB, Equiv.apply_symm_apply]⟩

/-- Target naturality of `(cobarBarHomEquiv).symm` under postcomposition with `ψ : B → C`. -/
@[simp]
theorem cobarBarHomEquiv_symm_comp {C : Type uC} [Ring C] [Algebra R C]
    {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}
    (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (𝒜.cobarBarHomEquiv hC).symm (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ((𝒜.cobarBarHomEquiv hB).symm φ) := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_cobarBarHomEquiv_symm_eq,
    taylor_cobarBarHomEquiv_symm_eq]
  exact LinearMap.ext fun _ ↦ by simp

/-- Target naturality of `cobarBarHomEquiv` under postcomposition with `ψ : B → C`. -/
theorem cobarBarHomEquiv_comp {C : Type uC} [Ring C] [Algebra R C]
    {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞] {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}
    (ψ : DGAlgHom hB hC) (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    𝒜.cobarBarHomEquiv hC (ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f) =
      ψ.comp (𝒜.cobarBarHomEquiv hB f) :=
  (𝒜.cobarBarHomEquiv hC).symm.injective (by simp)

end Target

end Unit

end AInfinityAlgebra

namespace AInfinityHom

section Functoriality

variable {A : Type uA} [AddCommGroup A] [Module R A]

section Hom

variable {A' : Type uA'} [AddCommGroup A'] [Module R A']
  {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}

/-- Functoriality of `Ω Tᶜ(s-)`: any `A∞` morphism `g : A ⟶ A'` induces a strict DG algebra
morphism `Ω Tᶜ(sA) → Ω Tᶜ(sA')` via `g.barMap`. -/
noncomputable def cobarMap (g : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar g.barMap
    (by rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
        exact g.isHomogeneous_barMap)
    (ReducedTensorWords.isCoalgHom_iff.mp g.isCoalgHom_barMap) g.barDifferential_comp_barMap

/-- On a desuspended generator `s⁻¹ z`, `g.cobarMap` applies `g.barMap`. -/
@[simp]
theorem cobarMap_ι (g : AInfinityHom 𝒜 𝒜') (z : ReducedTensorWords R A) :
    g.cobarMap (ι R z) = ι R (g.barMap z) := by simp [cobarMap]

/-- Naturality of `toCobarBar` with respect to arbitrary `A∞` morphisms. -/
@[simp]
theorem toAInfinityHom_cobarMap_comp_toCobarBar (g : AInfinityHom 𝒜 𝒜') :
    g.cobarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar =
      𝒜'.toCobarBar.comp g := by
  have hg : LinearMap.IsHomogeneous g.barMap
      (ReducedTensorWords.grading (𝒜.grading.shift 1)).piece
      (ReducedTensorWords.grading (𝒜'.grading.shift 1)).piece 0 := by
    rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
    exact g.isHomogeneous_barMap
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp]
  refine LinearMap.ext fun z ↦ ?_
  have htwist := hg.koszulTwist_apply 1 z
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] at htwist
  simp [htwist]

/-- Source naturality of `(cobarBarHomEquiv).symm` under precomposition with `g.cobarMap`. -/
theorem cobarBarHomEquiv_symm_comp_cobarMap {B : Type uB} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (φ : DGAlgHom 𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (g : AInfinityHom 𝒜 𝒜') :
    (𝒜.cobarBarHomEquiv hB).symm (φ.comp g.cobarMap) =
      ((𝒜'.cobarBarHomEquiv hB).symm φ).comp g := by
  rw [𝒜.cobarBarHomEquiv_symm_comp _ φ g.cobarMap, 𝒜.cobarBarHomEquiv_symm_apply _ g.cobarMap,
    toAInfinityHom_cobarMap_comp_toCobarBar, ← AInfinityHom.comp_assoc,
    ← 𝒜'.cobarBarHomEquiv_symm_apply hB φ]

/-- Source naturality of `cobarBarHomEquiv` under precomposition with `g : A ⟶ A'`. -/
@[simp]
theorem cobarBarHomEquiv_comp {B : Type uB} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
    (f : AInfinityHom 𝒜' hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) (g : AInfinityHom 𝒜 𝒜') :
    𝒜.cobarBarHomEquiv hB (f.comp g) = (𝒜'.cobarBarHomEquiv hB f).comp g.cobarMap :=
  (𝒜.cobarBarHomEquiv hB).symm.injective <| by
    rw [cobarBarHomEquiv_symm_comp_cobarMap, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Passing to cobar DG algebras preserves composition of `A∞` morphisms. -/
@[simp]
theorem cobarMap_comp {A'' : Type uA''} [AddCommGroup A''] [Module R A'']
    {𝒜'' : AInfinityAlgebra R A''} (g' : AInfinityHom 𝒜' 𝒜'') (g : AInfinityHom 𝒜 𝒜') :
    (g'.comp g).cobarMap = g'.cobarMap.comp g.cobarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

end Hom

/-- The identity `A∞` morphism induces the identity DG algebra morphism on `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

end Functoriality

end AInfinityHom

namespace IsDGAlgebra

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)

/-- The **adjunction counit** `Ω Tᶜ(sB) → B` for a differential graded algebra `B`, corresponding
under `cobarBarHomEquiv` to `AInfinityHom.id`. -/
noncomputable def cobarCounit :
    DGAlgHom
      (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.isNonCounitalDGCoalgebra_bar
        ).isDGAlgebra_cobarDifferential hB :=
  hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv hB
    (AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)

/-- On `s⁻¹ z`, `cobarCounit` projects onto single letters after the Koszul involution. -/
@[simp]
theorem cobarCounit_ι (z : ReducedTensorWords R B) :
    hB.cobarCounit (ι R z) =
      ReducedTensorWords.letter R B
        ((ReducedTensorWords.grading
          (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.grading.shift 1)).koszulTwist 1 z) := by
  rw [cobarCounit, AInfinityAlgebra.cobarBarHomEquiv_apply_ι_eq_taylor_koszulTwist,
    AInfinityHom.taylor_id]

/-- First triangle identity of the bar–cobar adjunction for a DG algebra `B`. -/
@[simp]
theorem toAInfinityHom_cobarCounit_comp_toCobarBar :
    hB.cobarCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toCobarBar =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toAInfinityHom_cobarBarHomEquiv_comp_toCobarBar hB
    (AInfinityHom.id _)

end IsDGAlgebra

namespace AInfinityAlgebra

/-- Second triangle identity of the bar–cobar adjunction for an `A∞` algebra `A`. -/
@[simp]
theorem cobarCounit_comp_cobarMap_toCobarBar {A : Type uA} [AddCommGroup A] [Module R A]
    (𝒜 : AInfinityAlgebra R A) :
    𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential.cobarCounit.comp
        𝒜.toCobarBar.cobarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  let hΩ := 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
  apply (𝒜.cobarBarHomEquiv hΩ).symm.injective
  rw [AInfinityHom.cobarBarHomEquiv_symm_comp_cobarMap, IsDGAlgebra.cobarCounit,
    Equiv.symm_apply_apply, AInfinityHom.id_comp, ← 𝒜.cobarBarHomEquiv_toCobarBar,
    Equiv.symm_apply_apply]

end AInfinityAlgebra

end TauCeti
