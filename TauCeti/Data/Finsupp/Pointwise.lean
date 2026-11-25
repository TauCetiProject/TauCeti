/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.Finsupp.SMulWithZero

/-!
# Scalars and the pointwise product of finitely supported functions

If scalars from `R` associate, respectively commute, with the multiplication of `M`, then they
associate, respectively commute, with the pointwise product on `ι →₀ M`. With `M = R` a
commutative semiring, this makes `ι →₀ R` a nonunital `R`-algebra in the sense of
`IsScalarTower R (ι →₀ R) (ι →₀ R)` and `SMulCommClass R (ι →₀ R) (ι →₀ R)`.
-/

public section

namespace Finsupp

variable (ι R M : Type*) [MulZeroClass M] [SMulZeroClass R M]

/-- Scalars associate with the pointwise product of finitely supported functions on the left. -/
instance instIsScalarTowerPointwise [IsScalarTower R M M] : IsScalarTower R (ι →₀ M) (ι →₀ M) :=
  ⟨fun a f g ↦ Finsupp.ext fun i ↦ by simp [smul_mul_assoc]⟩

/-- Scalars commute past the pointwise product of finitely supported functions on the right. -/
instance instSMulCommClassPointwise [SMulCommClass R M M] : SMulCommClass R (ι →₀ M) (ι →₀ M) :=
  ⟨fun a f g ↦ Finsupp.ext fun i ↦ by simp [mul_smul_comm]⟩

end Finsupp
