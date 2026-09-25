/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Basic

/-!
# The type-D spin and half-spin Lie representations

An even polarization identifies the split type-`D` matrix Lie algebra with the quadratic
elements of its Clifford algebra. Composing this equivalence with the Fock action gives the
spin representation on the full exterior algebra.

Quadratic Clifford elements are even, so they preserve exterior parity. The same matrix Lie
algebra therefore acts separately on the even and odd exterior summands, giving the two
half-spin Lie representations. Their application formulas below compare both restricted
actions directly with the full spin action after coercion to the exterior algebra.

## Main definitions and results

* `TauCeti.SpinPolarizationData.typeDSpinLieRep`: the spin representation of the split type-`D`
  matrix Lie algebra.
* `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.typeDSpinMinusLieRep`: its restrictions to the two exterior
  parity summands.
* `TauCeti.SpinPolarizationData.coe_typeDSpinPlusLieRep_apply` and
  `TauCeti.SpinPolarizationData.coe_typeDSpinMinusLieRep_apply`: the restricted actions agree
  with the full action after coercion.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  [Invertible (2 : K)]

/-! ## The full spin representation -/

/-- The split type-`D` matrix Lie algebra acting on the exterior spinor module through its
quadratic Clifford realization. -/
noncomputable def typeDSpinLieRep (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Module.End K (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toLieHom.comp <|
    (quadraticLieSubalgebra Q).incl.comp (P.typeDQuadraticEquiv b hline).toLieHom

/-- A split type-`D` matrix acts through its corresponding quadratic Clifford element. -/
@[simp]
theorem typeDSpinLieRep_apply (hline : P.line = ⊥)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.typeDSpinLieRep b hline x =
      spinAction Q P (P.typeDQuadraticEquiv b hline x : CliffordAlgebra Q) := by
  rw [typeDSpinLieRep, LieHom.comp_apply, LieHom.comp_apply, LieSubalgebra.coe_incl,
    AlgHom.toLieHom_apply]
  rfl

/-! ## The half-spin representations -/

/-- The map from the split type-`D` matrix Lie algebra to the even Clifford subalgebra. -/
private noncomputable def typeDToEvenLieHom (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ CliffordAlgebra.even Q := by
  let f : LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ CliffordAlgebra Q :=
    (quadraticLieSubalgebra Q).incl.comp (P.typeDQuadraticEquiv b hline).toLieHom
  exact {
    toFun := fun x => ⟨f x,
      quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property⟩
    map_add' := fun x y => SetCoe.ext (f.map_add x y)
    map_smul' := fun r x => SetCoe.ext (f.map_smul r x)
    map_lie' := @fun x y => SetCoe.ext (f.map_lie x y) }

/-- The split type-`D` matrix Lie algebra acting on the even half-spin summand. -/
noncomputable def typeDSpinPlusLieRep (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Module.End K (spinPlus Q P) :=
  (spinPlusAction Q P hline).toLieHom.comp (P.typeDToEvenLieHom b hline)

/-- After coercion to the exterior algebra, the even half-spin action agrees with the full spin
action. -/
@[simp]
theorem coe_typeDSpinPlusLieRep_apply (hline : P.line = ⊥)
    (x : LieAlgebra.Orthogonal.typeD ι K) (s : spinPlus Q P) :
    ((P.typeDSpinPlusLieRep b hline x s : spinPlus Q P) : ExteriorAlgebra K P.W) =
      P.typeDSpinLieRep b hline x s := by
  rw [typeDSpinPlusLieRep, LieHom.comp_apply, AlgHom.toLieHom_apply,
    coe_spinPlusAction_apply, typeDSpinLieRep_apply]
  rfl

/-- The split type-`D` matrix Lie algebra acting on the odd half-spin summand. -/
noncomputable def typeDSpinMinusLieRep (hline : P.line = ⊥) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Module.End K (spinMinus Q P) :=
  (spinMinusAction Q P hline).toLieHom.comp (P.typeDToEvenLieHom b hline)

/-- After coercion to the exterior algebra, the odd half-spin action agrees with the full spin
action. -/
@[simp]
theorem coe_typeDSpinMinusLieRep_apply (hline : P.line = ⊥)
    (x : LieAlgebra.Orthogonal.typeD ι K) (s : spinMinus Q P) :
    ((P.typeDSpinMinusLieRep b hline x s : spinMinus Q P) : ExteriorAlgebra K P.W) =
      P.typeDSpinLieRep b hline x s := by
  rw [typeDSpinMinusLieRep, LieHom.comp_apply, AlgHom.toLieHom_apply,
    coe_spinMinusAction_apply, typeDSpinLieRep_apply]
  rfl

end TauCeti.SpinPolarizationData
