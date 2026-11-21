/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison

/-!
# Effectivity under the Weil–Cartier correspondence

On a Noetherian normal integral scheme, a Cartier divisor is effective if and only if its
associated Weil divisor has nonnegative coefficients
(`Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg`), proved from algebraic Hartogs'
principle on local equations. In particular, on a scheme of dimension at most one whose
codimension-one local rings are discrete valuation rings, `IsNormalScheme.of_forall_coheight_le_one`
gives `Scheme.CartierDivisor.isEffective_iff_toWeilDivisor`, and restricting
`SchemeWeilDivisor.equivCartierDivisor` identifies the effective submonoids of Weil and Cartier
divisors (`SchemeWeilDivisor.effectiveEquivCartierDivisor`), allowing effective divisors in linear
systems and Abel maps to be viewed as effective Cartier divisors.

## References

* R. Hartshorne, *Algebraic Geometry*, II.6.11.
* The Stacks Project, *Divisors*, Tag 0BE9.
-/

public section

open AlgebraicGeometry CategoryTheory Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- On a Noetherian normal integral scheme, a Cartier divisor is effective if and only if its
associated Weil divisor has nonnegative coefficients. -/
theorem isEffective_iff_toWeilDivisor_nonneg [IsNormalScheme X] (D : CartierDivisor X) :
    D.IsEffective ↔ 0 ≤ D.toWeilDivisor := by
  have : ∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X)) :=
    fun y ↦ IsNormalScheme.isDiscreteValuationRing_stalk y.val y.property
  refine ⟨fun hD ↦ (WeilDivisor.nonneg_iff _).mpr fun η ↦ ?_,
    fun hD ↦ isEffective_iff_exists.mpr fun x ↦ ?_⟩
  · obtain ⟨f, hf, b, hb⟩ := isEffective_iff_exists.mp hD η
    obtain ⟨U, hηU, hU⟩ := isLocalEquationAt_iff.mp hf
    have : Nonempty U := ⟨⟨η, hηU⟩⟩
    rw [D.coeff_toWeilDivisor_eq_ord η hηU f hU, ← hb]
    exact ord_algebraMap_stalk_nonneg η.property specializes_rfl b
  · obtain ⟨U, -, hxU, f, hf⟩ := D.exists_localEquation_le ⊤ (trivial : x ∈ (⊤ : X.Opens))
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    refine ⟨f, isLocalEquationAt_iff.mpr ⟨U, hxU, hf⟩,
      exists_algebraMap_stalk_eq_of_ord_nonneg_of_isNormalScheme fun η hηx ↦ ?_⟩
    rw [← D.coeff_toWeilDivisor_eq_ord η (hηx.mem_open U.isOpen hxU) f hf]
    exact WeilDivisor.coeff_nonneg hD η

/-- On a Noetherian integral scheme of dimension at most one, regular in codimension one, a
Cartier divisor is effective if and only if every coefficient of its associated Weil divisor is
nonnegative. -/
@[simp]
theorem isEffective_iff_toWeilDivisor
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hX : ∀ x : X, coheight x ≤ 1) (D : CartierDivisor X) :
    D.IsEffective ↔ 0 ≤ D.toWeilDivisor := by
  have : IsNormalScheme X := .of_forall_coheight_le_one hX
  exact isEffective_iff_toWeilDivisor_nonneg D

end Scheme.CartierDivisor

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- The Weil–Cartier equivalence preserves effectivity. -/
theorem isEffective_equivCartierDivisor_iff (hX : ∀ x : X, coheight x ≤ 1)
    (D : SchemeWeilDivisor X) :
    (equivCartierDivisor hX D).IsEffective ↔ 0 ≤ D := by
  rw [Scheme.CartierDivisor.isEffective_iff_toWeilDivisor hX]
  rw [← equivCartierDivisor_symm_apply hX (equivCartierDivisor hX D),
    AddEquiv.symm_apply_apply]

/-- The Weil–Cartier equivalence restricts to an additive equivalence of effective divisors. -/
def effectiveEquivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1) :
    AddSubmonoid.nonneg (WeilDivisor (CodimensionOnePoint X)) ≃+
      Scheme.CartierDivisor.effectiveSubmonoid X :=
  (equivCartierDivisor hX).addSubmonoidMap
      (AddSubmonoid.nonneg (WeilDivisor (CodimensionOnePoint X))) |>.trans
    (AddEquiv.addSubmonoidCongr (by
      ext E
      constructor
      · rintro ⟨D, hD, rfl⟩
        exact (Scheme.CartierDivisor.mem_effectiveSubmonoid _).mpr
          ((isEffective_equivCartierDivisor_iff hX D).mpr
            (AddSubmonoid.mem_nonneg.mp hD))
      · intro hE
        refine ⟨(equivCartierDivisor hX).symm E, ?_, ?_⟩
        · exact AddSubmonoid.mem_nonneg.mpr
            ((isEffective_equivCartierDivisor_iff hX _).mp (by
              simpa only [AddEquiv.apply_symm_apply] using
                (Scheme.CartierDivisor.mem_effectiveSubmonoid _).mp hE))
        · exact (equivCartierDivisor hX).apply_symm_apply E))

/-- On underlying divisors, the effective equivalence is the Weil–Cartier equivalence. -/
@[simp]
theorem effectiveEquivCartierDivisor_apply (hX : ∀ x : X, coheight x ≤ 1)
    (D : AddSubmonoid.nonneg (WeilDivisor (CodimensionOnePoint X))) :
    ((effectiveEquivCartierDivisor hX D :
      Scheme.CartierDivisor.effectiveSubmonoid X) : Scheme.CartierDivisor X) =
      equivCartierDivisor hX D :=
  AddEquiv.coe_addSubmonoidMap_apply _ _ _

/-- On underlying divisors, the inverse effective equivalence takes the associated Weil
divisor. -/
@[simp]
theorem effectiveEquivCartierDivisor_symm_apply (hX : ∀ x : X, coheight x ≤ 1)
    (D : Scheme.CartierDivisor.effectiveSubmonoid X) :
    ((effectiveEquivCartierDivisor hX).symm D : SchemeWeilDivisor X) =
      (D : Scheme.CartierDivisor X).toWeilDivisor := by
  have h : equivCartierDivisor hX
      ((effectiveEquivCartierDivisor hX).symm D : SchemeWeilDivisor X) =
        (D : Scheme.CartierDivisor X) := by
    rw [← effectiveEquivCartierDivisor_apply hX]
    exact congrArg Subtype.val ((effectiveEquivCartierDivisor hX).apply_symm_apply D)
  calc
    ((effectiveEquivCartierDivisor hX).symm D : SchemeWeilDivisor X) =
        (equivCartierDivisor hX).symm
          (equivCartierDivisor hX
            ((effectiveEquivCartierDivisor hX).symm D : SchemeWeilDivisor X)) :=
      ((equivCartierDivisor hX).left_inv _).symm
    _ = (D : Scheme.CartierDivisor X).toWeilDivisor := by
      rw [h, equivCartierDivisor_symm_apply]

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
