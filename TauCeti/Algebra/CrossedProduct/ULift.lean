/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.ULift
public import TauCeti.Algebra.CrossedProduct.RingCongr

/-!
# Crossed products under simultaneous universe lifting

Lift the base ring, coefficient ring and automorphism-indexed cocycle together. The crossed
product of the lifted cocycle is isomorphic to the actual universe lift of the original
crossed product. The coefficient and basis formulas specify this transport independently
of any comparison with cohomology.

No finiteness or Galois hypothesis is needed. Use `TauCeti.CrossedProduct.uliftEquiv` to
transport between these algebras. Its `uliftEquiv_inc` and `uliftEquiv_basis` lemmas describe
coefficients and basis elements, and `repr_uliftEquiv` computes the coordinates of any element.
-/

public noncomputable section

universe u v w

attribute [local instance] ULift.algebra'

namespace TauCeti

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]

namespace TwoCocycle

/-- Lift both rings and the values of a cocycle, identifying automorphisms by conjugation
with the up/down maps. -/
def ulift (c : TwoCocycle K L) : TwoCocycle (ULift.{w} K) (ULift.{w} L) :=
  c.comap (AlgEquiv.uliftAutEquiv (R := K) (A := L)).symm ULift.ringEquiv.symm
    AlgEquiv.uliftAutEquiv_symm_apply_up

/-- Simultaneous universe lifting is transport along the up maps and automorphism equivalence. -/
theorem ulift_eq_comap (c : TwoCocycle K L) :
    (c.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) =
      c.comap (AlgEquiv.uliftAutEquiv (R := K) (A := L)).symm ULift.ringEquiv.symm
        AlgEquiv.uliftAutEquiv_symm_apply_up := (rfl)

/-- The lifted cocycle evaluates by lifting its unit values. -/
@[simp]
theorem ulift_toFun (c : TwoCocycle K L)
    (σ τ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) :
    c.ulift.toFun σ τ = Units.map ULift.ringEquiv.symm.toMonoidHom
      (c.toFun (AlgEquiv.uliftAutEquiv.symm σ) (AlgEquiv.uliftAutEquiv.symm τ)) := by
  rw [ulift_eq_comap, comap_toFun]
  -- The ring-equivalence coercion and its toMonoidHom have the same bundled multiplication map.
  rfl

@[simp]
theorem ulift_one : (1 : TwoCocycle K L).ulift = (1 : TwoCocycle (ULift.{w} K) (ULift.{w} L)) := by
  ext σ τ
  simp [ulift]

@[simp]
theorem ulift_mul (c d : TwoCocycle K L) :
    (c * d).ulift = c.ulift * (d.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) := by
  ext σ τ
  simp [ulift]

/-- Lifting commutes with inversion of cocycles. -/
@[simp]
theorem ulift_inv (c : TwoCocycle K L) :
    c⁻¹.ulift = (c.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L))⁻¹ := by
  ext σ τ
  simp

/-- Lifting commutes with division of cocycles. -/
@[simp]
theorem ulift_div (c d : TwoCocycle K L) :
    (c / d).ulift = c.ulift / (d.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) := by
  ext σ τ
  simp

/-- Lifting commutes with natural powers of cocycles. -/
@[simp]
theorem ulift_pow (c : TwoCocycle K L) (n : ℕ) :
    (c ^ n).ulift = (c.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) ^ n := by
  ext σ τ
  simp

/-- Lifting commutes with integer powers of cocycles. -/
@[simp]
theorem ulift_zpow (c : TwoCocycle K L) (n : ℤ) :
    (c ^ n).ulift = (c.ulift : TwoCocycle (ULift.{w} K) (ULift.{w} L)) ^ n := by
  ext σ τ
  simp

end TwoCocycle

namespace CrossedProduct

variable (c : TwoCocycle K L)

/-- The crossed product of the lifted cocycle is the lifted original algebra, over the
lifted base ring. This is an isomorphism of the actual algebras, not one defined via
Brauer classes or cohomology. -/
def uliftEquiv : CrossedProduct c.ulift ≃ₐ[ULift.{w} K] ULift.{w} (CrossedProduct c) :=
  (AlgEquiv.ofRingEquiv (R := ULift.{w} K) (f := comapRingEquiv c ULift.ringEquiv.symm
    AlgEquiv.uliftAutEquiv.symm AlgEquiv.uliftAutEquiv_symm_apply_up) (by
      rintro ⟨r⟩
      exact
        comapRingEquiv_algebraMap c ULift.ringEquiv.symm AlgEquiv.uliftAutEquiv.symm
          AlgEquiv.uliftAutEquiv_symm_apply_up ULift.ringEquiv.symm.toRingHom
          (by
            intro k
            -- The up ring equivalence is ULift.up; use the lifted algebra instances.
            simp [ULift.algebraMap_apply', ULift.algebraMap_eq, ULift.ringEquiv]) r)).trans
    ULift.algEquiv.symm

-- Normalize dependent source types locally: rewriting ulift_eq_comap in a basis or
-- coefficient argument alone gives an ill-typed motive because uliftEquiv has that source.
-- The public equation is available for consumers without exposing the definition's body.
@[simp]
theorem uliftEquiv_basis (σ : ULift.{w} L ≃ₐ[ULift.{w} K] ULift.{w} L) :
    uliftEquiv c (basis c.ulift σ) =
      ULift.up (basis c (AlgEquiv.uliftAutEquiv.symm σ)) := by
  unfold TwoCocycle.ulift
  apply ULift.down_injective
  simp [uliftEquiv, ULift.down_algEquiv_symm_apply]

@[simp]
theorem uliftEquiv_inc (x : ULift.{w} L) :
    uliftEquiv c (inc c.ulift x) = ULift.up (inc c x.down) := by
  unfold TwoCocycle.ulift
  apply ULift.down_injective
  simp only [uliftEquiv, AlgEquiv.trans_apply, ULift.down_algEquiv_symm_apply,
    AlgEquiv.ofRingEquiv_apply, comapRingEquiv_inc, RingEquiv.symm_symm]
  -- ULift.ringEquiv evaluates by down.
  rfl

/-- Coefficient scalar multiplication is carried to the lifted scalar multiplication. -/
@[simp]
theorem uliftEquiv_smul (x : ULift.{w} L) (a : CrossedProduct c.ulift) :
    uliftEquiv c (x • a) = ULift.up (x.down • (uliftEquiv c a).down) := by
  unfold TwoCocycle.ulift at a ⊢
  apply ULift.down_injective
  simp only [uliftEquiv, AlgEquiv.trans_apply, ULift.down_algEquiv_symm_apply,
    AlgEquiv.ofRingEquiv_apply, comapRingEquiv_smul, RingEquiv.symm_symm]
  -- ULift.ringEquiv evaluates by down.
  rfl

@[simp]
theorem uliftEquiv_symm_basis (σ : L ≃ₐ[K] L) :
    (uliftEquiv c).symm (ULift.up (basis c σ)) =
      basis c.ulift (AlgEquiv.uliftAutEquiv σ) := by
  unfold TwoCocycle.ulift
  simp only [uliftEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm, ULift.algEquiv_apply,
    AlgEquiv.ofRingEquiv_symm_apply, comapRingEquiv_symm_basis, MulEquiv.symm_symm]

@[simp]
theorem uliftEquiv_symm_inc (x : L) :
    (uliftEquiv c).symm (ULift.up (inc c x)) = inc c.ulift (ULift.up x) := by
  unfold TwoCocycle.ulift
  simp only [uliftEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm, ULift.algEquiv_apply,
    AlgEquiv.ofRingEquiv_symm_apply, comapRingEquiv_symm_inc]
  -- The inverse of ULift.ringEquiv evaluates by up.
  rfl

/-- Transport acts coefficientwise in the two crossed-product bases. -/
@[simp]
theorem repr_uliftEquiv (a : CrossedProduct c.ulift) (σ : L ≃ₐ[K] L) :
    (basis c).repr (uliftEquiv c a).down σ =
      ((basis c.ulift).repr a (AlgEquiv.uliftAutEquiv σ)).down := by
  unfold TwoCocycle.ulift at a ⊢
  simp only [uliftEquiv, AlgEquiv.trans_apply, ULift.down_algEquiv_symm_apply,
    AlgEquiv.ofRingEquiv_apply]
  exact repr_comapRingEquiv c ULift.ringEquiv.symm AlgEquiv.uliftAutEquiv.symm
    AlgEquiv.uliftAutEquiv_symm_apply_up a σ

end CrossedProduct
end TauCeti
