/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ExteriorAlgebra
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Sign actions on free algebras and their skew products

The two-element permutation group acts on `ℤ` by its sign. Its transposition negates the
canonical generator but fixes its square. In the skew product, moving the transposition
past the generator introduces a minus sign. These checks fix the left-skew convention
and exercise scalar compatibility and Mathlib's algebra-automorphism API.
-/

public noncomputable section

namespace TauCeti.Examples.AlgebraActions

local notation "ρ" => (MonoidHom.comp (Representation.ofDistribMulAction ℤ ℤˣ ℤ)
  (Equiv.Perm.sign : Equiv.Perm (Fin 2) →* ℤˣ) : Representation ℤ (Equiv.Perm (Fin 2)) ℤ)
local notation "s" => Equiv.swap (0 : Fin 2) 1

/-- The sign action on the tensor algebra fixes the square of the degree-one generator. -/
theorem tensorAlgebra_sign_square :
    Representation.tensorAlgebra ρ s (TensorAlgebra.ι ℤ (1 : ℤ) ^ 2) =
      TensorAlgebra.ι ℤ (1 : ℤ) ^ 2 := by
  simp [Representation.tensorAlgebra_apply]

section Tensor

private local instance : MulSemiringAction (Equiv.Perm (Fin 2)) (TensorAlgebra ℤ ℤ) :=
  Representation.tensorAlgebraMulSemiringAction ρ
private local instance : SMulCommClass (Equiv.Perm (Fin 2)) ℤ (TensorAlgebra ℤ ℤ) :=
  Representation.smulCommClass_tensorAlgebraMulSemiringAction ρ

example : Algebra ℤ (SkewMonoidAlgebra (TensorAlgebra ℤ ℤ) (Equiv.Perm (Fin 2))) :=
  inferInstance

example : SkewMonoidAlgebra.single s (1 : TensorAlgebra ℤ ℤ) *
      SkewMonoidAlgebra.single 1 (TensorAlgebra.ι ℤ (1 : ℤ)) =
    SkewMonoidAlgebra.single s (-TensorAlgebra.ι ℤ (1 : ℤ)) := by
  simp [SkewMonoidAlgebra.single_mul_single,
    Representation.tensorAlgebraMulSemiringAction_smul]

example : SkewMonoidAlgebra.single (1 : Equiv.Perm (Fin 2)) (TensorAlgebra.ι ℤ (1 : ℤ)) *
      SkewMonoidAlgebra.single s (1 : TensorAlgebra ℤ ℤ) =
    SkewMonoidAlgebra.single s (TensorAlgebra.ι ℤ (1 : ℤ)) := by
  simp [SkewMonoidAlgebra.single_mul_single]

example (g : Equiv.Perm (Fin 2)) (v : ℤ) :
    MulSemiringAction.toAlgAut (Equiv.Perm (Fin 2)) ℤ (TensorAlgebra ℤ ℤ) g
        (TensorAlgebra.ι ℤ v) = TensorAlgebra.ι ℤ (ρ g v) := by
  simp [MulSemiringAction.toAlgAut, Representation.tensorAlgebraMulSemiringAction_smul]

end Tensor

section Exterior

private local instance : MulSemiringAction (Equiv.Perm (Fin 2)) (ExteriorAlgebra ℤ ℤ) :=
  Representation.exteriorAlgebraMulSemiringAction ρ
private local instance : SMulCommClass (Equiv.Perm (Fin 2)) ℤ (ExteriorAlgebra ℤ ℤ) :=
  Representation.smulCommClass_exteriorAlgebraMulSemiringAction ρ

example : Algebra ℤ (SkewMonoidAlgebra (ExteriorAlgebra ℤ ℤ) (Equiv.Perm (Fin 2))) :=
  inferInstance

example : SkewMonoidAlgebra.single s (1 : ExteriorAlgebra ℤ ℤ) *
      SkewMonoidAlgebra.single 1 (ExteriorAlgebra.ι ℤ (1 : ℤ)) =
    SkewMonoidAlgebra.single s (-ExteriorAlgebra.ι ℤ (1 : ℤ)) := by
  simp [SkewMonoidAlgebra.single_mul_single,
    Representation.exteriorAlgebraMulSemiringAction_smul]

end Exterior

end TauCeti.Examples.AlgebraActions
