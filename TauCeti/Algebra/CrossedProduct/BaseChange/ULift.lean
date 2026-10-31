/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.ULift
public import TauCeti.Algebra.CrossedProduct.Comparison
public import TauCeti.FieldTheory.GaloisCohomology.Congr
import TauCeti.Algebra.CrossedProduct.Congr
import TauCeti.Algebra.CrossedProduct.FieldCongr
import TauCeti.Algebra.CrossedProduct.ULift

/-!
# The Brauer–cohomology comparison and universe lifting

For a field `K : Type u`, the lift `ULift.{w} K` is a field in the universe `max u w`. Its Brauer
group is identified with that of `K` by scalar extension (`TauCeti.BrauerGroup.uliftEquiv`), and
its explicit second Galois cohomology group with unit coefficients is identified with that of `K`
by transporting the separable closure, the absolute Galois group and the unit coefficients along
`K ≃+* ULift K` (`RingEquiv.unitsH2Congr`). This file proves that the comparison isomorphisms
`brauerExplicitH2Equiv` of the two fields intertwine these identifications:

```text
Br(K)            ──≅──▶  H²(G_K, (Kˢ)ˣ)
  │ ULift K ⊗[K] -           │ transport along K ≃+* ULift K
  ▼                          ▼
Br(ULift K)      ──≅──▶  H²(G_{ULift K}, ((ULift K)ˢ)ˣ)
```

Both vertical maps are defined independently of the comparison: the left one by tensor products
of central simple algebras, the right one by the continuous cocycle map of the chosen
identification of separable closures.

It suffices to check the square on the class of the crossed product of a cocycle `c` of a finite
Galois `E ⊆ Kˢ`, since every Brauer class has this form. Transporting `ULift E` into
`(ULift K)ˢ` gives a finite Galois `F ⊆ (ULift K)ˢ` isomorphic to `ULift E` over `ULift K`.
The scalar extension of the crossed product of `c` is the lifted crossed product
(`TauCeti.CrossedProduct.uliftEquiv`), which is the crossed product of the cocycle transported
to `F` (`TauCeti.CrossedProduct.congr`); and transport of explicit cohomology sends the inflation
of `c` to the inflation of that transported cocycle (`TauCeti.TwoCocycle.unitsH2Congr_inflateH2`).

## Main results

* `TauCeti.brauerExplicitH2Equiv_uliftEquiv`: the comparison commutes with universe lifting, for
  every Brauer class.
* `TauCeti.brauerExplicitH2Equiv_symm_unitsH2Congr`: the same square for the inverse
  comparison.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4.
-/

public section

noncomputable section

universe u w

namespace TauCeti

open scoped TensorProduct

open ContCohomology

variable {K : Type u} [Field K]

/-- The `ULift K`-algebra structure on the lift of a `K`-algebra, as in
`TauCeti.CrossedProduct.uliftEquiv`. It is restricted to lifted carriers so that the
subextensions of `(ULift K)ˢ` keep their usual `ULift K`-algebra structure. -/
private abbrev uliftAlgebra (A : Type*) [Semiring A] [Algebra K A] :
    Algebra (ULift.{w} K) (ULift.{w} A) :=
  ULift.algebra' K (ULift.{w} A)

attribute [local instance] uliftAlgebra

section Generator

variable (E : IntermediateField K (SeparableClosure K))

/-- The embedding of `ULift E` into the separable closure of `ULift K` through the chosen
identification of separable closures along `K ≃+* ULift K`. -/
private def uliftEmbedding :
    ULift.{w} E →ₐ[ULift.{w} K] SeparableClosure (ULift.{w} K) where
  toRingHom :=
    ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm.toRingHom.comp
      E.val.toRingHom).comp (ULift.ringEquiv : ULift.{w} E ≃+* E).toRingHom
  commutes' r :=
    (congrArg (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm
      (E.val.commutes r.down)).trans
      ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr_symm_algebraMap r.down)

private theorem uliftEmbedding_apply (x : E) :
    uliftEmbedding E (ULift.up x) =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm (E.val x) :=
  (rfl)

/-- The finite Galois subextension of `(ULift K)ˢ` corresponding to `E`. -/
private abbrev uliftField : IntermediateField (ULift.{w} K) (SeparableClosure (ULift.{w} K)) :=
  (uliftEmbedding E).fieldRange

/-- The coefficient map `E → F`, through `ULift E`. -/
private def uliftCoeff : E →+* uliftField.{u, w} E :=
  (uliftEmbedding E).equivFieldRange.toRingHom.comp
    (ULift.ringEquiv.symm : E ≃+* ULift.{w} E).toRingHom

private theorem uliftCoeff_apply (x : E) :
    uliftCoeff E x = (uliftEmbedding E).equivFieldRange (ULift.up x) :=
  (rfl)

/-- The automorphism map `Gal(F / ULift K) → Gal(E / K)`, conjugation by `ULift E ≃ F`. -/
private def uliftAut :
    (uliftField.{u, w} E ≃ₐ[ULift.{w} K] uliftField.{u, w} E) →* (E ≃ₐ[K] E) :=
  AlgEquiv.uliftAutEquiv.symm.toMonoidHom.comp
    (uliftEmbedding E).equivFieldRange.autCongr.symm.toMonoidHom

private theorem uliftAut_autCongr (σ : ULift.{w} E ≃ₐ[ULift.{w} K] ULift.{w} E) :
    uliftAut E ((uliftEmbedding E).equivFieldRange.autCongr σ) =
      AlgEquiv.uliftAutEquiv.symm σ := by
  simp only [uliftAut, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

private theorem uliftCoeff_uliftAut (g : uliftField.{u, w} E ≃ₐ[ULift.{w} K] uliftField.{u, w} E)
    (x : E) : uliftCoeff E (uliftAut E g x) = g (uliftCoeff E x) := by
  obtain ⟨σ, rfl⟩ := (uliftEmbedding E).equivFieldRange.autCongr.surjective g
  rw [uliftAut_autCongr, uliftCoeff_apply, uliftCoeff_apply, AlgEquiv.autCongr_apply]
  simp

private theorem val_uliftCoeff (x : E) :
    (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm (E.val x) =
      (uliftField.{u, w} E).val (uliftCoeff E x) :=
  (uliftEmbedding_apply E x).symm

variable [FiniteDimensional K E] [IsGalois K E]

/- Instance search would find Mathlib's `ULift.module` here, which is not reducibly equal to the
module structure of the intermediate field used by the crossed-product and inflation API. -/
private instance finiteDimensional_uliftField :
    @FiniteDimensional (ULift.{w} K) (uliftField.{u, w} E) _ _ Algebra.toModule :=
  have : FiniteDimensional (ULift.{w} K) (ULift.{w} E) :=
    Module.Finite.of_equiv_equiv _ _ ULift.algebraMap_comp_ringEquiv_symm
  (uliftEmbedding E).toLinearMap.finiteDimensional_range

private instance isGalois_uliftField : IsGalois (ULift.{w} K) (uliftField.{u, w} E) :=
  have : IsGalois (ULift.{w} K) (ULift.{w} E) :=
    IsGalois.of_equiv_equiv ULift.algebraMap_comp_ringEquiv_symm
  IsGalois.of_algEquiv (uliftEmbedding E).equivFieldRange

private instance : Normal (ULift.{w} K) (uliftField.{u, w} E) :=
  (isGalois_uliftField E).to_normal

/-- Scalar extension to `ULift K` of the class of the crossed product of `c` is the class of the
crossed product of `c` transported to `F`. -/
private theorem uliftEquiv_crossedProductClass (c : TwoCocycle K E) :
    BrauerGroup.uliftEquiv.{u, w} K (BrauerGroup.crossedProductClass c) =
      BrauerGroup.crossedProductClass
        (c.comap (uliftAut E) (uliftCoeff E) (uliftCoeff_uliftAut E)) := by
  rw [BrauerGroup.crossedProductClass_def, BrauerGroup.uliftEquiv_mk,
    BrauerGroup.crossedProductClass_def]
  -- `ULift K ⊗[K] A ≃ ULift A ≃ (crossed product of the lifted cocycle) ≃ (crossed product on F)`
  let A := CrossedProduct c
  let tensorEquiv : ULift.{w} K ⊗[K] A ≃ₐ[ULift.{w} K] ULift.{w} A :=
    AlgEquiv.ofRingEquiv
      (f := (((Algebra.TensorProduct.congr (ULift.algEquiv (R := K) (A := K)) AlgEquiv.refl).trans
        (Algebra.TensorProduct.lid K A)).trans ULift.algEquiv.symm).toRingEquiv) fun r ↦ by
      apply ULift.down_injective
      simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
        TensorProduct.smul_tmul']
  refine BrauerGroup.mk_eq_mk_of_algEquiv (tensorEquiv.trans
    ((CrossedProduct.uliftEquiv c).symm.trans (CrossedProduct.congr _ _
      (uliftEmbedding E).equivFieldRange fun σ τ ↦ ?_)))
  rw [TwoCocycle.comap_toFun, uliftAut_autCongr, uliftAut_autCongr]
  ext
  simp [uliftCoeff_apply, ULift.ringEquiv]

/-- The square on the class of a crossed product. -/
private theorem brauerExplicitH2Equiv_uliftEquiv_crossedProductClass (c : TwoCocycle K E) :
    brauerExplicitH2Equiv (ULift.{w} K)
        (Additive.ofMul (BrauerGroup.uliftEquiv.{u, w} K (BrauerGroup.crossedProductClass c))) =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).unitsH2Congr
        (brauerExplicitH2Equiv K (Additive.ofMul (BrauerGroup.crossedProductClass c))) := by
  rw [uliftEquiv_crossedProductClass, brauerExplicitH2Equiv_crossedProductClass,
    brauerExplicitH2Equiv_crossedProductClass]
  exact (TwoCocycle.unitsH2Congr_inflateH2 _ E (uliftField E) (uliftCoeff E) (uliftAut E)
    (val_uliftCoeff E) (uliftCoeff_uliftAut E) c).symm

end Generator

/-- **The Brauer–cohomology comparison commutes with universe lifting.** Scalar extension of
Brauer classes from `K` to `ULift K` corresponds, under `brauerExplicitH2Equiv`, to transport of
explicit second Galois cohomology along `K ≃+* ULift K`. -/
@[simp]
theorem brauerExplicitH2Equiv_uliftEquiv (x : BrauerGroup K) :
    brauerExplicitH2Equiv (ULift.{w} K) (Additive.ofMul (BrauerGroup.uliftEquiv.{u, w} K x)) =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).unitsH2Congr
        (brauerExplicitH2Equiv K (Additive.ofMul x)) := by
  obtain ⟨g, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x
  rw [GaloisCocycle.brauerClass_def]
  exact brauerExplicitH2Equiv_uliftEquiv_crossedProductClass g.extension g.cocycle

/-- **The inverse comparison commutes with universe lifting.** The transported class of
`y ∈ H²(G_K, (Kˢ)ˣ)` corresponds to the scalar extension of the Brauer class of `y`. -/
@[simp]
theorem brauerExplicitH2Equiv_symm_unitsH2Congr (y : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    (brauerExplicitH2Equiv (ULift.{w} K)).symm
        ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).unitsH2Congr y) =
      Additive.ofMul
        (BrauerGroup.uliftEquiv.{u, w} K ((brauerExplicitH2Equiv K).symm y).toMul) := by
  rw [AddEquiv.symm_apply_eq, brauerExplicitH2Equiv_uliftEquiv, ofMul_toMul,
    AddEquiv.apply_symm_apply]

end TauCeti
