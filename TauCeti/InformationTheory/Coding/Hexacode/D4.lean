/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.D4
public import TauCeti.InformationTheory.Coding.Hexacode.WeightEnumerator

/-!
# The hexacode in the `D₄` discriminant alphabet

The hexacode has only weights `0`, `4`, and `6`, so its image in six copies of the `D₄`
discriminant alphabet is quadratic-isotropic. Its cardinality makes it a Lagrangian both in the
quaternary model and in the actual discriminant module.

## Main declarations

* `TauCeti.Hexacode.isIsotropic_typeD4`: isotropy in the quaternary coordinate alphabet.
* `TauCeti.Hexacode.isLagrangian_typeD4`: the hexacode is a quadratic Lagrangian there.
* `TauCeti.Hexacode.isLagrangian_codeInTypeD4Discriminant`: the transported hexacode is a
  quadratic Lagrangian in six copies of the `D₄` discriminant group.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3 and
  Chapter 7, §§8–9.
* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Example 1.3.4.
-/

public section

namespace TauCeti

open IntegralLattice

variable {F : Type*} [Field F] [Finite F]

namespace Hexacode

variable (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
include hF hω

/-- The hexacode is quadratic-isotropic in the `D₄` coordinate alphabet, since its weights
`0, 4, 6` are even. -/
theorem isIsotropic_typeD4 :
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower (Fin 6)).IsIsotropic
      (code ω).toAddSubgroup := by
  classical
  let := Fintype.ofFinite F
  rw [isIsotropic_coordinatePower_typeD4QuaternaryQuadraticModule_iff]
  intro x hx
  rcases hammingNorm_eq_zero_or_eq_four_or_eq_six_of_mem_code
      (Nat.card_eq_fintype_card.symm.trans hF) hω hx with h | h | h <;>
    rw [h] <;> norm_num

/-- **The hexacode is a quadratic Lagrangian in the `D₄` coordinate alphabet.** -/
theorem isLagrangian_typeD4 :
    ((typeD4QuaternaryQuadraticModule hF).coordinatePower (Fin 6)).IsLagrangian
      (code ω).toAddSubgroup := by
  apply FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq _ (isIsotropic_typeD4 hF hω)
    ((isNondegenerate_typeD4QuaternaryQuadraticModule hF).coordinatePower (Fin 6))
  have hcard : Nat.card (code ω).toAddSubgroup = Nat.card F ^ 3 := natCard_code ω
  rw [hcard, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF]
  norm_num

/-- **The hexacode, transported to six copies of the actual `D₄` discriminant group, is a
quadratic-isotropic Lagrangian subgroup.** The coordinate identification may use either root of
`X² + X + 1`, independently of the root defining the hexacode. -/
theorem isLagrangian_codeInTypeD4Discriminant {ω' : F} (hω' : ω' ^ 2 + ω' + 1 = 0) :
    (((checkerboardLattice 4).discriminantQuadraticModule
        (isEven_checkerboardLattice 4)).coordinatePower (Fin 6)).IsLagrangian
      (codeInTypeD4Discriminant hF hω' (code ω).toAddSubgroup) := by
  rw [isLagrangian_codeInTypeD4Discriminant_iff]
  exact isLagrangian_typeD4 hF hω

end Hexacode

end TauCeti
