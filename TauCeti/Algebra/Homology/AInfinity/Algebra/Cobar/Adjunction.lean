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
  `g.cobarBarMap : Ω Tᶜ(sA) → Ω Tᶜ(sA')` via `g.barMap`, preserving identities and composition and
  making `toCobarBar` natural;
* `cobarBarHomEquiv` is natural in both the source `A∞` algebra and the target DG algebra;
* for a DG algebra `B`, the counit `IsDGAlgebra.cobarBarCounit : Ω Tᶜ(sB) → B` projects
  desuspended generators onto single letters and applies the negated Koszul involution
  (`cobarBarCounit_ι`), is natural in `B`, and satisfies both triangle identities with `toCobarBar`.

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

section TargetNaturality

variable {A : Type uA} [AddCommGroup A] [Module R A] (𝒜 : AInfinityAlgebra R A)
  {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)
  {C : Type uC} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞]
  {dC : C →ₗ[R] C} {hC : IsDGAlgebra 𝒞 dC}

/-- Target naturality of `(cobarBarHomEquiv).symm` under postcomposition with `ψ : B → C`. -/
theorem cobarBarHomEquiv_symm_comp (ψ : DGAlgHom hB hC)
    (φ : DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB) :
    (𝒜.cobarBarHomEquiv hC).symm (ψ.comp φ) =
      ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        ((𝒜.cobarBarHomEquiv hB).symm φ) := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp,
    taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist,
    taylor_cobarBarHomEquiv_symm_eq_comp_koszulTwist]
  exact LinearMap.ext fun _ ↦ by simp

/-- Target naturality of `cobarBarHomEquiv` under postcomposition with `ψ : B → C`. -/
@[simp]
theorem cobarBarHomEquiv_toAInfinityHom_comp (ψ : DGAlgHom hB hC)
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    𝒜.cobarBarHomEquiv hC (ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp f) =
      ψ.comp (𝒜.cobarBarHomEquiv hB f) :=
  (𝒜.cobarBarHomEquiv hC).symm.injective <| by
    rw [Equiv.symm_apply_apply, 𝒜.cobarBarHomEquiv_symm_comp hB ψ, Equiv.symm_apply_apply]

end TargetNaturality

end AInfinityAlgebra

namespace AInfinityHom

section Functoriality

variable {A : Type uA} [AddCommGroup A] [Module R A]

section Hom

variable {A' : Type uA'} [AddCommGroup A'] [Module R A']
  {𝒜 : AInfinityAlgebra R A} {𝒜' : AInfinityAlgebra R A'}

/-- Functoriality of `Ω Tᶜ(s-)`: any `A∞` morphism `g : A ⟶ A'` induces a strict DG algebra
morphism `Ω Tᶜ(sA) → Ω Tᶜ(sA')` via `g.barMap`. -/
noncomputable def cobarBarMap (g : AInfinityHom 𝒜 𝒜') :
    DGAlgHom 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential
      𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarMap 𝒜'.isNonCounitalDGCoalgebra_bar g.barMap
    (by rw [ReducedTensorWords.grading_piece, ReducedTensorWords.grading_piece]
        exact g.isHomogeneous_barMap)
    (ReducedTensorWords.isCoalgHom_iff.mp g.isCoalgHom_barMap) g.barDifferential_comp_barMap

/-- On a desuspended generator `s⁻¹ z`, `g.cobarBarMap` applies `g.barMap`. -/
@[simp]
theorem cobarBarMap_ι (g : AInfinityHom 𝒜 𝒜') (z : ReducedTensorWords R A) :
    g.cobarBarMap (ι R z) = ι R (g.barMap z) := by simp [cobarBarMap]

/-- Naturality of `toCobarBar` with respect to arbitrary `A∞` morphisms. -/
@[simp]
theorem toAInfinityHom_cobarBarMap_comp_toCobarBar (g : AInfinityHom 𝒜 𝒜') :
    g.cobarBarMap.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp 𝒜.toCobarBar =
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

/-- Passing to cobar–bar DG algebras preserves composition of `A∞` morphisms. -/
@[simp]
theorem cobarBarMap_comp {A'' : Type uA''} [AddCommGroup A''] [Module R A'']
    {𝒜'' : AInfinityAlgebra R A''} (g' : AInfinityHom 𝒜' 𝒜'') (g : AInfinityHom 𝒜 𝒜') :
    (g'.comp g).cobarBarMap = g'.cobarBarMap.comp g.cobarBarMap :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

end Hom

/-- The identity `A∞` morphism induces the identity DG algebra morphism on `Ω Tᶜ(sA)`. -/
@[simp]
theorem cobarBarMap_id (𝒜 : AInfinityAlgebra R A) :
    (AInfinityHom.id 𝒜).cobarBarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarHom_ext _ fun _ ↦ by simp

end Functoriality

end AInfinityHom

namespace AInfinityAlgebra

section SourceNaturality

variable {A : Type uA} {A' : Type uA'} {B : Type uB}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  (𝒜 : AInfinityAlgebra R A) {𝒜' : AInfinityAlgebra R A'} (hB : IsDGAlgebra ℬ dB)

/-- Source naturality of `(cobarBarHomEquiv).symm` under precomposition with `g.cobarBarMap`. -/
@[simp]
theorem cobarBarHomEquiv_symm_comp_cobarBarMap
    (φ : DGAlgHom 𝒜'.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential hB)
    (g : AInfinityHom 𝒜 𝒜') :
    (𝒜.cobarBarHomEquiv hB).symm (φ.comp g.cobarBarMap) =
      ((𝒜'.cobarBarHomEquiv hB).symm φ).comp g := by
  rw [𝒜.cobarBarHomEquiv_symm_comp _ φ g.cobarBarMap,
    𝒜.cobarBarHomEquiv_symm_apply _ g.cobarBarMap,
    AInfinityHom.toAInfinityHom_cobarBarMap_comp_toCobarBar, ← AInfinityHom.comp_assoc,
    ← 𝒜'.cobarBarHomEquiv_symm_apply hB φ]

/-- Source naturality of `cobarBarHomEquiv` under precomposition with `g : A ⟶ A'`. -/
theorem cobarBarHomEquiv_comp
    (f : AInfinityHom 𝒜' hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)
    (g : AInfinityHom 𝒜 𝒜') :
    𝒜.cobarBarHomEquiv hB (f.comp g) = (𝒜'.cobarBarHomEquiv hB f).comp g.cobarBarMap :=
  (𝒜.cobarBarHomEquiv hB).symm.injective <| by
    rw [𝒜.cobarBarHomEquiv_symm_comp_cobarBarMap, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end SourceNaturality

end AInfinityAlgebra

namespace IsDGAlgebra

variable {B : Type uB} [Ring B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} (hB : IsDGAlgebra ℬ dB)

/-- The **adjunction counit** `Ω Tᶜ(sB) → B` for a differential graded algebra `B`, corresponding
under `cobarBarHomEquiv` to `AInfinityHom.id`. -/
noncomputable def cobarBarCounit :
    DGAlgHom
      (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.isNonCounitalDGCoalgebra_bar
        ).isDGAlgebra_cobarDifferential hB :=
  hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv hB
    (AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra)

/-- Under `cobarBarHomEquiv`, the identity `A∞` morphism of `B` corresponds to
`cobarBarCounit`. -/
theorem cobarBarHomEquiv_id :
    hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv hB
      (AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) = hB.cobarBarCounit :=
  (rfl)

/-- Under `(cobarBarHomEquiv).symm`, `cobarBarCounit` corresponds to the identity `A∞` morphism
of `B`. -/
@[simp]
theorem cobarBarHomEquiv_symm_cobarBarCounit :
    (hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv hB).symm
        hB.cobarBarCounit =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  Equiv.symm_apply_apply _ _

/-- On `s⁻¹ z`, `cobarBarCounit` projects onto single letters and applies the negated Koszul
involution. -/
@[simp]
theorem cobarBarCounit_ι (z : ReducedTensorWords R B) :
    hB.cobarBarCounit (ι R z) =
      -(InternalGrading.ofDecomposition ℬ).koszulTwist 1 (ReducedTensorWords.letter R B z) := by
  rw [cobarBarCounit, AInfinityAlgebra.cobarBarHomEquiv_apply_ι, AInfinityHom.taylor_id]

/-- First triangle identity of the bar–cobar adjunction for a DG algebra `B`. -/
@[simp]
theorem toAInfinityHom_cobarBarCounit_comp_toCobarBar :
    hB.cobarBarCounit.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.comp
        hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toCobarBar =
      AInfinityHom.id hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra :=
  hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.toAInfinityHom_cobarBarHomEquiv_comp_toCobarBar hB
    (AInfinityHom.id _)

/-- Factoring `cobarBarHomEquiv` through `cobarBarMap` and `cobarBarCounit`. -/
theorem cobarBarCounit_comp_cobarBarMap {A : Type uA} [AddCommGroup A] [Module R A]
    {𝒜 : AInfinityAlgebra R A}
    (f : AInfinityHom 𝒜 hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra) :
    hB.cobarBarCounit.comp f.cobarBarMap = 𝒜.cobarBarHomEquiv hB f := by
  rw [cobarBarCounit, ← 𝒜.cobarBarHomEquiv_comp hB (AInfinityHom.id _) f, AInfinityHom.id_comp]

/-- Naturality of `cobarBarCounit` along a DG algebra morphism `ψ : A → B`. -/
@[simp]
theorem cobarBarCounit_comp_cobarBarMap_toAInfinityHom {A : Type uA} [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}
    (ψ : DGAlgHom hA hB) :
    hB.cobarBarCounit.comp
        ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.cobarBarMap =
      ψ.comp hA.cobarBarCounit := by
  rw [hB.cobarBarCounit_comp_cobarBarMap,
    ← AInfinityHom.comp_id ψ.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom,
    hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv_toAInfinityHom_comp hA ψ,
    cobarBarCounit]

end IsDGAlgebra

namespace AInfinityAlgebra

/-- Second triangle identity of the bar–cobar adjunction for an `A∞` algebra `A`. -/
@[simp]
theorem cobarBarCounit_comp_cobarBarMap_toCobarBar {A : Type uA} [AddCommGroup A] [Module R A]
    (𝒜 : AInfinityAlgebra R A) :
    𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential.cobarBarCounit.comp
        𝒜.toCobarBar.cobarBarMap =
      DGAlgHom.id 𝒜.isNonCounitalDGCoalgebra_bar.isDGAlgebra_cobarDifferential := by
  rw [IsDGAlgebra.cobarBarCounit_comp_cobarBarMap, cobarBarHomEquiv_toCobarBar]

end AInfinityAlgebra

end TauCeti
