/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Orthogonal.Basic

/-!
# The orthogonal tangent equation

Specializing the constant-form tangent criterion to the identity form gives `X + Xᵀ = 0`
over every commutative coefficient algebra. This criterion also supplies the orthogonality
part of the special-orthogonal tangent identification.
-/

public section

open Matrix

namespace TauCeti.Orthogonal

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- An ambient tangent derivation belongs to the orthogonal Lie algebra exactly when its
matrix satisfies the linearized orthogonality equation. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) ↔
      GeneralLinear.tangentMatrix n d + (GeneralLinear.tangentMatrix n d)ᵀ = 0 := by
  simpa only [Matrix.map_one _ (map_zero _) (map_one _), mul_one, one_mul] using
    ConstantForm.mem_lieSubalgebra_definingHopfIdeal_iff
      (C := (1 : Matrix (Fin n) (Fin n) R)) (n := n) d

end TauCeti.Orthogonal
