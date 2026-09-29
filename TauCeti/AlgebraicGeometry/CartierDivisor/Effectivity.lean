/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective
public import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison

/-!
# Effectivity under the Weil–Cartier correspondence

On a Noetherian integral scheme of dimension at most one, regular in codimension one, the Cartier
divisor associated with a Weil divisor is effective exactly when the Weil divisor has nonnegative
coefficients. The comparison uses the common sheaf of rational sections: effectivity says that the
constant rational section `1` belongs to `𝒪_X(D)`.

The result identifies the effective submonoids of Weil and Cartier divisors. It allows effective
divisors used in linear systems and Abel maps to be viewed as effective Cartier divisors.

The comparison uses `Scheme.CartierDivisor.isEffective_iff_one_mem_sections` and
`Scheme.CartierDivisor.sections_eq_toWeilDivisor`; the effective monoid equivalence is the
restriction of `SchemeWeilDivisor.equivCartierDivisor`.

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
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- On a Noetherian integral scheme of dimension at most one, regular in codimension one, a
Cartier divisor is effective if and only if every coefficient of its associated Weil divisor is
nonnegative. -/
@[simp]
theorem isEffective_iff_toWeilDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) :
    D.IsEffective ↔ WeilDivisor.IsEffective D.toWeilDivisor := by
  rw [isEffective_iff_one_mem_sections,
    SchemeWeilDivisor.isEffective_iff_one_mem_sections,
    sections_eq_toWeilDivisor hX]

end Scheme.CartierDivisor

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- The Weil–Cartier equivalence preserves effectivity. -/
@[simp]
theorem isEffective_equivCartierDivisor_iff (hX : ∀ x : X, coheight x ≤ 1)
    (D : SchemeWeilDivisor X) :
    (equivCartierDivisor hX D).IsEffective ↔
      WeilDivisor.IsEffective D := by
  rw [Scheme.CartierDivisor.isEffective_iff_toWeilDivisor hX]
  rw [← equivCartierDivisor_symm_apply hX (equivCartierDivisor hX D),
    AddEquiv.symm_apply_apply]

/-- The Weil–Cartier equivalence restricts to an additive equivalence of effective divisors. -/
def effectiveEquivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1) :
    WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X) ≃+
      Scheme.CartierDivisor.effectiveSubmonoid X :=
  (equivCartierDivisor hX).addSubmonoidMap
      (WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X)) |>.trans
    (AddEquiv.addSubmonoidCongr (by
      ext E
      constructor
      · rintro ⟨D, hD, rfl⟩
        exact (Scheme.CartierDivisor.mem_effectiveSubmonoid _).mpr
          ((isEffective_equivCartierDivisor_iff hX D).mpr
            ((WeilDivisor.mem_effectiveSubmonoid _).mp hD))
      · intro hE
        refine ⟨(equivCartierDivisor hX).symm E, ?_, ?_⟩
        · exact (WeilDivisor.mem_effectiveSubmonoid _).mpr
            ((isEffective_equivCartierDivisor_iff hX _).mp (by
              simpa only [AddEquiv.apply_symm_apply] using
                (Scheme.CartierDivisor.mem_effectiveSubmonoid _).mp hE))
        · exact (equivCartierDivisor hX).apply_symm_apply E))

/-- On underlying divisors, the effective equivalence is the Weil–Cartier equivalence. -/
@[simp]
theorem effectiveEquivCartierDivisor_apply (hX : ∀ x : X, coheight x ≤ 1)
    (D : WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X)) :
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
