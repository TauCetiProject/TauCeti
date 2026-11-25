/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.ClassFunction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Character

/-!
# Characters of representations are class functions

Let `M` be a comodule over a commutative Hopf algebra `H` over `k`, finite free as a `k`-module,
that is a finite-dimensional representation of `G = Spec H`. Its character, the regular function
`g ↦ tr(g | M)`, is a regular class function, and so is every coefficient of its characteristic
polynomial `g ↦ det(X - g | M)`. Both follow from the conjugation invariance of the trace and the
characteristic polynomial of point actions, tested on points with values in every commutative
algebra.

The coefficients of the characteristic polynomial are the coordinates of the morphism of
conjugacy quotients `Conj(G) → Conj(GL(M))` attached to the representation, and characters of
representations are the class functions from which the conjugacy quotient of a reductive group is
computed.

## Main declarations

* `TauCeti.Comodule.character_mem_classFunctions`: characters are regular class functions.
* `TauCeti.Comodule.coeff_charpoly_mem_classFunctions`: the coefficients of the characteristic
  polynomial are regular class functions.

## References

* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  §6, where the characters of representations span the class functions of a semisimple group.
* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945, §5.3.
-/

public section

namespace TauCeti

namespace Comodule

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}

section Semiring

variable [CommSemiring k] [CommSemiring H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M] [Module.Free k M] [Module.Finite k M]

/-- **Characters are class functions.** The character of a finite free comodule is a regular
class function. -/
theorem character_mem_classFunctions :
    character k H M ∈ HopfAlgebra.classFunctions k H := by
  rw [HopfAlgebra.mem_classFunctions_iff_forall]
  intro A _ _ g x
  rw [apply_character, apply_character, trace_endOfPoint_mul_mul_inv]

end Semiring

section Ring

variable [CommSemiring k] [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M] [Module.Free k M] [Module.Finite k M]

/-- **The coefficients of the characteristic polynomial are class functions.** Every coefficient
of the characteristic polynomial of a finite free comodule is a regular class function. These
are the coordinates of the morphism of conjugacy quotients `Conj(G) → Conj(GL(M))`. -/
theorem coeff_charpoly_mem_classFunctions (n : ℕ) :
    (charpoly k H M).coeff n ∈ HopfAlgebra.classFunctions k H := by
  rw [HopfAlgebra.mem_classFunctions_iff_forall_commRing]
  intro A _ _ g x
  rw [apply_coeff_charpoly, apply_coeff_charpoly, charpoly_endOfPoint_mul_mul_inv]

end Ring

end Comodule

end TauCeti
