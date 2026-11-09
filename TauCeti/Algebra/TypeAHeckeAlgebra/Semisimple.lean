/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form
public import TauCeti.RingTheory.Semisimple.Star

/-!
# Semisimplicity for real Hecke parameters

The finite type-A Hecke algebra over `ℝ` or `ℂ` is semisimple whenever its unit parameter is
real. This includes negative parameters and `q = ±1`, as well as zero and one strands.
Consequently every module over this algebra is semisimple, using Mathlib's semisimple-ring
API. This supplies the algebraic complete reducibility underlying orthogonal decompositions
of positive-real Hecke modules.

The PBW basis makes the algebra finite-dimensional, and the canonical trace form makes its
involution proper. The general Artinian proper-star criterion then gives semisimplicity.
This does not assert the arbitrary-field quantum-integer criterion, nor does it construct or
label Specht modules. Over `ℝ`, semisimplicity alone is not a claim of split semisimplicity.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Chapter 3.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {n : ℕ}
variable [Fact (IsSelfAdjoint (q : 𝕜))]

/-- The finite Hecke algebra at a real nonzero parameter is semisimple. In particular,
every module over this algebra is completely reducible. -/
instance : IsSemisimpleRing (TypeAHeckeAlgebra 𝕜 q n) := by
  let : Module.Finite 𝕜 (TypeAHeckeAlgebra 𝕜 q n) :=
    .of_basis (basisTw q (permCoxeterSystem n))
  let := IsArtinianRing.of_finite 𝕜 (TypeAHeckeAlgebra 𝕜 q n)
  exact isSemisimpleRing_of_isProperStar _

end TauCeti.TypeAHeckeAlgebra
