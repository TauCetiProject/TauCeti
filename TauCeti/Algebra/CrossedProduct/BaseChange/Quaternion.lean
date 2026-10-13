/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.TwoTorsionBaseChange
public import TauCeti.Algebra.CrossedProduct.CupProduct
public import TauCeti.Algebra.Quaternion.BaseChange
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer
public import TauCeti.FieldTheory.GaloisCohomology.Restriction

/-!
# Restriction compatibility for the quaternion-symbol part of the Brauer comparison

Scalar extension carries quaternion symbols to the symbols with the extended coefficients. Since
the comparison `ι` sends each quaternion symbol to a cup of Kummer classes, and both Kummer classes
and cups commute with restriction, this proves the base-change square for `ι` on quaternion
symbols.

The general base-change naturality of `ι` for arbitrary `2`-torsion Brauer classes is not proved
here; it requires compatibility of the full crossed-product comparison with scalar extension.
-/

public section

noncomputable section

namespace TauCeti

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : K)] [Invertible (2 : L)] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- **Base-change naturality of `ι` on quaternion symbols**: extending a quaternion Brauer class
and then applying `ι` gives the same class as restricting its Kummer cup product to `L`. -/
theorem brauer2EquivH2_baseChange_quaternionClass (a b : Kˣ) :
    brauer2EquivH2 L (Additive.ofMul (BrauerGroup.twoTorsionBaseChange K L ⟨
      BrauerGroup.quaternionClass a b,
      BrauerGroup.mem_twoTorsion.2 (BrauerGroup.quaternionClass_sq a b)⟩)) =
      galoisRes K L σ 2
        (brauer2EquivH2 K (Additive.ofMul ⟨BrauerGroup.quaternionClass a b,
          BrauerGroup.mem_twoTorsion.2 (BrauerGroup.quaternionClass_sq a b)⟩)) := by
  have hclass : BrauerGroup.twoTorsionBaseChange K L ⟨
      BrauerGroup.quaternionClass a b,
      BrauerGroup.mem_twoTorsion.2 (BrauerGroup.quaternionClass_sq a b)⟩ =
      ⟨BrauerGroup.quaternionClass
          (Units.map (algebraMap K L).toMonoidHom a)
          (Units.map (algebraMap K L).toMonoidHom b),
        BrauerGroup.mem_twoTorsion.2 (BrauerGroup.quaternionClass_sq _ _)⟩ := by
    apply Subtype.ext
    simp
  rw [hclass, brauer2EquivH2_quaternionClass, brauer2EquivH2_quaternionClass]
  rw [galoisRes_cup K L σ 1 1 (kummerClass a) (kummerClass b),
    galoisRes_kummerClass K L σ a, galoisRes_kummerClass K L σ b]

end TauCeti

end
