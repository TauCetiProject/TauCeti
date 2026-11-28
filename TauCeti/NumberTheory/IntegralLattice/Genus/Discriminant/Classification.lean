/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Genus.Discriminant.Basic
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Oddity
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Classification

/-!
# Classification of genera via discriminant forms

This file establishes the even-lattice dyadic reduction of the genus via the discriminant quadratic
form and the odd-discriminant cases of Nikulin's Corollaries 1.9.4 and 1.16.3.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9, §1.16.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Dyadic reduction of the genus -/

/-- **Dyadic reduction of the genus for even lattices via the discriminant quadratic form.** Two
even nondegenerate integral lattices lie in one genus if and only if their real signatures agree,
their dyadic localizations are integrally isometric, and their discriminant quadratic modules are
isometric. -/
theorem sameGenus_iff_localIntegralForm_two_and_discriminantQuadratic
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) :
    L.SameGenus M ↔
      L.signature = M.signature ∧
        (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          (L.discriminantQuadraticModule hL) (M.discriminantQuadraticModule hM)) :=
  ⟨fun h ↦ ⟨h.signature_eq, h.localIntegralForm_equivalent 2,
      h.nonempty_isometry_discriminantQuadraticModule hL⟩,
    fun ⟨hsig, htwo, ⟨e⟩⟩ ↦ sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent.mpr
      ⟨hsig, ⟨e.toFiniteBilinearModule⟩, htwo⟩⟩

/-! ### Odd-discriminant genera -/

/-- **The genus of lattices of odd discriminant (Nikulin, Corollary 1.16.3, odd-discriminant
case).** Let `L` and `M` be nondegenerate integral lattices with `L.discriminant` odd. Then `L` and
`M` lie in the same genus if and only if they have the same real signature, `L` is even if and only
if `M` is, and their discriminant bilinear modules are isometric. -/
theorem sameGenus_iff_discriminantBilinear_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : Odd L.discriminant) :
    L.SameGenus M ↔
      L.signature = M.signature ∧ (L.IsEven ↔ M.IsEven) ∧
        Nonempty (FiniteBilinearModule.Isometry
          L.discriminantBilinearModule M.discriminantBilinearModule) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.isEven_iff, h.nonempty_isometry_discriminantBilinearModule⟩,
    fun ⟨hsig, heven, ⟨e⟩⟩ ↦ ?_⟩
  have hdisc := discriminant_eq_of_isometry_discriminantBilinearModule e
  obtain ⟨w, hw⟩ := L.exists_isCharacteristicVector
  obtain ⟨w', hw'⟩ := M.exists_isCharacteristicVector
  have hpos : L.sigPos = M.sigPos := congrArg (fun s ↦ s.1) hsig
  have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) hsig
  refine sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent.mpr ⟨hsig, ⟨e⟩, ?_⟩
  exact (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M
    (L.isUnit_determinant_two_iff_odd_discriminant.mpr hL)
    (M.isUnit_determinant_two_iff_odd_discriminant.mpr (hdisc ▸ hL)) hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven,
      determinant_eq_of_signature_eq_of_discriminant_eq hsig hdisc ▸ IsSquare.mul_self _,
      integralNorm_modEq_eight_of_odd_discriminant hL (by rw [hpos, hneg]) e hw hw'⟩

/-- **The genus of even lattices of odd discriminant (Nikulin, Corollary 1.9.4, odd-discriminant
case).** Let `L` and `M` be even nondegenerate integral lattices with `L.discriminant` odd. Then
`L` and `M` lie in the same genus if and only if they have the same real signature and their
discriminant quadratic modules are isometric. -/
theorem sameGenus_iff_discriminantQuadratic_of_isEven_of_odd_discriminant
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hLe : L.IsEven) (hMe : M.IsEven) (hL : Odd L.discriminant) :
    L.SameGenus M ↔ L.signature = M.signature ∧
      Nonempty (FiniteQuadraticModule.Isometry
        (L.discriminantQuadraticModule hLe) (M.discriminantQuadraticModule hMe)) := by
  rw [sameGenus_iff_discriminantBilinear_of_odd_discriminant L M hL,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hLe,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hMe,
    ← FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd
      (by rwa [L.natCard_discriminantQuadraticModule hLe, L.natCard_discriminantGroup])]
  simp [hLe, hMe]

end TauCeti.IntegralLattice
