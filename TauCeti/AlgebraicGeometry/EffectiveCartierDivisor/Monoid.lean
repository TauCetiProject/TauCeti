/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Sum
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Addition of relative effective Cartier divisors in families

Relative effective Cartier divisors on each base change `X_T` form a commutative monoid:
the empty divisor is the identity, and addition multiplies ideal sheaves. Pullback along
`T' ⟶ T` preserves this operation, including when the base change is not flat. This is the
monoid structure used by the Abel map and by the degree components of the divisor functor.

The construction follows the description of addition of effective Cartier divisors in the
Stacks Project, *Divisors*, Section "Effective Cartier divisors".
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Pointwise addition of relative effective Cartier divisors is a commutative monoid. -/
instance (T : (Over S)ᵒᵖ) :
    CommMonoid ((relativeEffectiveCartierSubfunctor f).toFunctor.obj T) := by
  let M : Submonoid (pullback T.unop.hom f).IdealSheafData := {
    carrier := (relativeEffectiveCartierSubfunctor f).obj T
    one_mem' := top_mem_relativeEffectiveCartierSubfunctor_obj f T
    mul_mem' := by
      intro I J hI hJ
      exact (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mpr
        (TauCeti.isRelativeEffectiveCartier_mul
          ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp hI)
          ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp hJ)) }
  -- The functor value and the submonoid have the same subtype carrier.
  have h : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T =
      M := rfl
  exact h.symm ▸ inferInstance

/-- Pullback of relative effective Cartier divisors preserves the empty divisor. -/
lemma relativeEffectiveCartier_map_one {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (relativeEffectiveCartierSubfunctor f).toFunctor.map φ
      (1 : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) = 1 := by
  apply Subtype.ext
  exact baseChangeIdealSheafFunctor_map_top f φ

/-- Pullback of relative effective Cartier divisors preserves their sum. -/
lemma relativeEffectiveCartier_map_mul {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    (relativeEffectiveCartierSubfunctor f).toFunctor.map φ (D * E) =
      (relativeEffectiveCartierSubfunctor f).toFunctor.map φ D *
        (relativeEffectiveCartierSubfunctor f).toFunctor.map φ E := by
  apply Subtype.ext
  exact Scheme.IdealSheafData.comap_mul D.1 E.1 _

end

end TauCeti.AlgebraicGeometry
