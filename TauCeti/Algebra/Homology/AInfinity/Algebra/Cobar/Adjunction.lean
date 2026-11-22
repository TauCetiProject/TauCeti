/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain

/-!
# Counit and triangle identities of the `A∞` bar–cobar adjunction

Building on `TauCeti.AInfinityAlgebra.cobarBarHomEquiv`, `TauCeti.AInfinityAlgebra.toCobarBar`, and
`TauCeti.AInfinityHom.cobarBarMap`, this file constructs the counit of the nonunital `A∞`
bar–cobar adjunction for an arbitrary (not necessarily augmented) differential graded algebra `B`:

* `TauCeti.IsDGAlgebra.cobarBarCounit`: the counit `Ω Tᶜ(sB) → B`, projecting desuspended
  generators onto single letters and applying the negated Koszul involution (`cobarBarCounit_ι`);
* `TauCeti.IsDGAlgebra.toAInfinityHom_cobarBarCounit_comp_toCobarBar` and
  `TauCeti.AInfinityAlgebra.cobarBarCounit_comp_cobarBarMap_toCobarBar`: both triangle identities
  of the bar–cobar adjunction;
* `TauCeti.IsDGAlgebra.cobarBarCounit_comp_cobarBarMap` and
  `TauCeti.IsDGAlgebra.cobarBarCounit_comp_cobarBarMap_toAInfinityHom`: factorization of
  `cobarBarHomEquiv` through `cobarBarMap` and naturality of `cobarBarCounit`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Section 4.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 2.
-/

public section

open TensorAlgebra

namespace TauCeti

universe uR uA uB

variable {R : Type uR} [CommRing R]

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
@[simp]
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
  rw [cobarBarCounit, ← AInfinityAlgebra.cobarBarHomEquiv_comp_right hB (AInfinityHom.id _) f,
    AInfinityHom.id_comp]

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
    hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cobarBarHomEquiv_comp_left ψ,
    cobarBarHomEquiv_id]

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
