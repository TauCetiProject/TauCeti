/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.ULift
public import TauCeti.Algebra.CrossedProduct.Basic

/-!
# Crossed products under simultaneous universe lifting

Lift the base ring, coefficient ring and automorphism-indexed cocycle together. The crossed
product of the lifted cocycle is isomorphic to the actual universe lift of the original
crossed product. The coefficient and basis formulas specify this transport independently
of any comparison with cohomology.

The construction uses the unnormalized crossed-product universal property from
`TauCeti.Algebra.CrossedProduct.Basic`; no finiteness or Galois hypothesis is needed.
As in `CrossedProduct.congr`, bijectivity is checked by reindexing finitely supported
coordinates, while multiplication is supplied by the universal property.
-/

public noncomputable section

universe u v w

attribute [local instance] ULift.algebra'

namespace TauCeti

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]

namespace TwoCocycle

/-- Lift both rings and the values of a cocycle, identifying automorphisms by conjugation
with the up/down maps. -/
def ulift (c : TwoCocycle K L) : TwoCocycle (ULift.{w} K) (ULift.{w} L) where
  toFun σ τ := Units.map ULift.ringEquiv.symm.toMonoidHom
    (c.toFun (AlgEquiv.uliftAutEquiv.symm σ) (AlgEquiv.uliftAutEquiv.symm τ))
  isMulCocycle₂ σ τ ρ := by
    apply Units.ext
    apply ULift.down_injective
    simpa [AlgEquiv.smul_units_def, ULift.ringEquiv] using congrArg Units.val
      (c.isMulCocycle₂ (AlgEquiv.uliftAutEquiv.symm σ)
        (AlgEquiv.uliftAutEquiv.symm τ) (AlgEquiv.uliftAutEquiv.symm ρ))

@[simp]
theorem ulift_toFun (c : TwoCocycle K L)
    (σ τ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) :
    (c.ulift.toFun σ τ : ULift.{w} L) =
      ULift.up (c.toFun (AlgEquiv.uliftAutEquiv.symm σ)
        (AlgEquiv.uliftAutEquiv.symm τ) : L) := (rfl)

@[simp]
theorem ulift_one : (1 : TwoCocycle K L).ulift = (1 : TwoCocycle (ULift.{w} K) (ULift.{w} L)) := by
  ext σ τ
  simp [ulift]

@[simp]
theorem ulift_mul (c d : TwoCocycle K L) :
    (c * d).ulift = c.ulift * (d.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) := by
  ext σ τ
  simp [ulift]

end TwoCocycle

namespace CrossedProduct

variable (c : TwoCocycle K L)

private def uliftCoeffHom : ULift.{w} L →ₐ[ULift.{w} K] CrossedProduct c where
  __ := (inc c).toRingHom.comp (ULift.ringEquiv : ULift.{w} L ≃+* L).toRingHom
  commutes' r := by
    simp [ULift.ringEquiv, ULift.algebraMap_apply', ULift.down_algebraMap]

private theorem uliftCoeffHom_apply (x : ULift.{w} L) :
    uliftCoeffHom c x = inc c x.down := (rfl)

private theorem uliftDown_comm
    (σ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) (x : ULift.{w} L) :
    basis c (AlgEquiv.uliftAutEquiv.symm σ) * uliftCoeffHom c x =
      uliftCoeffHom c (σ x) * basis c (AlgEquiv.uliftAutEquiv.symm σ) := by
  simp [uliftCoeffHom_apply, AlgEquiv.uliftAutEquiv_symm_apply, basis_mul_inc]

private theorem uliftDown_mul
    (σ τ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) :
    basis c (AlgEquiv.uliftAutEquiv.symm σ) * basis c (AlgEquiv.uliftAutEquiv.symm τ) =
      uliftCoeffHom c (c.ulift.toFun σ τ) * basis c (AlgEquiv.uliftAutEquiv.symm (σ * τ)) := by
  simp [uliftCoeffHom_apply, basis_mul_basis]

private theorem uliftDown_one :
    basis c (AlgEquiv.uliftAutEquiv.symm (1 : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L)) =
      uliftCoeffHom c (c.ulift.toFun 1 1) := by
  simp [uliftCoeffHom_apply, basis_one]

private def uliftDownHom : CrossedProduct c.ulift →ₐ[ULift.{w} K] CrossedProduct c :=
  lift (uliftCoeffHom c) (fun σ ↦ basis c (AlgEquiv.uliftAutEquiv.symm σ))
    (uliftDown_comm c) (uliftDown_mul c) (uliftDown_one c)

private def uliftDownAddEquiv : CrossedProduct c.ulift ≃+ CrossedProduct c :=
  (basis c.ulift).repr.toAddEquiv.trans
    ((Finsupp.domCongr AlgEquiv.uliftAutEquiv.symm.toEquiv).trans
      ((Finsupp.mapRange.addEquiv ULift.ringEquiv.toAddEquiv).trans
        (basis c).repr.symm.toAddEquiv))

private theorem uliftDownAddEquiv_smul_basis
    (σ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) (x : ULift.{w} L) :
    uliftDownAddEquiv c (x • basis c.ulift σ) =
      x.down • basis c (AlgEquiv.uliftAutEquiv.symm σ) := by
  simp [uliftDownAddEquiv, Finsupp.smul_single, smul_eq_mul, ULift.ringEquiv]

private theorem coe_uliftDownHom : ⇑(uliftDownHom c) = uliftDownAddEquiv.{u, v, w} c := by
  funext a
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | smul_basis σ x =>
    rw [uliftDownAddEquiv_smul_basis, uliftDownHom,
      lift_smul_basis (c := c.ulift), uliftCoeffHom_apply, smul_def]

/-- The crossed product of the lifted cocycle is the lifted original algebra, over the
lifted base ring. This is an isomorphism of the actual algebras, not one defined via
Brauer classes or cohomology. -/
def uliftEquiv : CrossedProduct c.ulift ≃ₐ[ULift.{w} K] ULift.{w} (CrossedProduct c) :=
  (AlgEquiv.ofBijective (uliftDownHom c) (by
    rw [coe_uliftDownHom]
    exact (uliftDownAddEquiv c).bijective)).trans ULift.algEquiv.symm

@[simp]
theorem uliftEquiv_basis (σ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) :
    uliftEquiv c (basis c.ulift σ) =
      ULift.up (basis c (AlgEquiv.uliftAutEquiv.symm σ)) := by
  apply ULift.down_injective
  simp [uliftEquiv, uliftDownHom, ULift.down_algEquiv_symm_apply]

@[simp]
theorem uliftEquiv_inc (x : ULift.{w} L) :
    uliftEquiv c (inc c.ulift x) = ULift.up (inc c x.down) := by
  apply ULift.down_injective
  simp [uliftEquiv, uliftDownHom, uliftCoeffHom_apply,
    ULift.down_algEquiv_symm_apply]

/-- Coefficient scalar multiplication is carried to the lifted scalar multiplication. -/
@[simp]
theorem uliftEquiv_smul (x : ULift.{w} L) (a : CrossedProduct c.ulift) :
    uliftEquiv c (x • a) = ULift.up (x.down • (uliftEquiv c a).down) := by
  apply ULift.down_injective
  simp [smul_def, map_mul, uliftEquiv_inc]

@[simp]
theorem uliftEquiv_symm_basis (σ : L ≃ₐ[K] L) :
    (uliftEquiv c).symm (ULift.up (basis c σ)) =
      basis c.ulift (AlgEquiv.uliftAutEquiv σ) := by
  apply (uliftEquiv c).injective
  simp

@[simp]
theorem uliftEquiv_symm_inc (x : L) :
    (uliftEquiv c).symm (ULift.up (inc c x)) = inc c.ulift (ULift.up x) := by
  apply (uliftEquiv c).injective
  simp

/-- Transport acts coefficientwise in the two crossed-product bases. -/
@[simp]
theorem repr_uliftEquiv (a : CrossedProduct c.ulift) (σ : L ≃ₐ[K] L) :
    (basis c).repr (uliftEquiv c a).down σ =
      ((basis c.ulift).repr a (AlgEquiv.uliftAutEquiv σ)).down := by
  simp [uliftEquiv, ULift.down_algEquiv_symm_apply, coe_uliftDownHom,
    uliftDownAddEquiv, Finsupp.domCongr, ULift.ringEquiv]

end CrossedProduct
end TauCeti
