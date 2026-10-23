/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite
public import TauCeti.KnotTheory.Jimbo.Basic

/-!
# The Jimbo representation factors through the type-A Hecke algebra

The Jimbo R-matrix `TauCeti.KnotTheory.jimboGenerator q j k` on the q-tensor space
`(Fin n → ι) →₀ R` satisfies the quadratic relation `T * T = (q - q⁻¹) • T + 1`, in the same
convention as the generators of `TauCeti.TypeAHeckeAlgebra R q n`, and the operators on adjacent
strands satisfy the braid and distant-commutation relations. So the generator `T i` acting by the
R-matrix on the strands `i` and `i + 1` defines a representation of the type-A Hecke algebra on
the q-tensor space, `TauCeti.TypeAHeckeAlgebra.jimbo`; no change of generators is involved.
Composed with the braid homomorphism `TauCeti.TypeAHeckeAlgebra.braidHom`, it is the Jimbo
representation `TauCeti.KnotTheory.jimbo` of the braid group
(`TauCeti.TypeAHeckeAlgebra.jimbo_braidHom`): the Jimbo representation factors through the Hecke
algebra.

For `ι = Fin N` this is the action on the `n`-th tensor power of the vector representation of
`U_q(gl_N)` in quantum Schur–Weyl duality. It is one particular representation of the Hecke
algebra, not to be identified with its regular representation.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.jimbo`: the representation of the type-A Hecke algebra on the
  q-tensor space.

## Main results

* `TauCeti.TypeAHeckeAlgebra.jimbo_T`: the generator `T i` acts by the Jimbo R-matrix on the
  strands `i` and `i + 1`.
* `TauCeti.TypeAHeckeAlgebra.jimbo_braidHom`: the Jimbo representation of the braid group factors
  through the Hecke algebra.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247-252.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] (ι : Type*) [LinearOrder ι] (q : Rˣ) {n : ℕ}

/-- The Jimbo representation of the type-A Hecke algebra on `n` strands on the q-tensor space
`(Fin n → ι) →₀ R`: the generator `T i` acts by the Jimbo R-matrix on the strands `i` and
`i + 1`. -/
noncomputable def jimbo : TypeAHeckeAlgebra R q n →ₐ[R] Module.End R ((Fin n → ι) →₀ R) :=
  lift (fun i ↦ KnotTheory.jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i))
    (fun i ↦ KnotTheory.jimboGenerator_mul_self q (BraidGroup.strand_ne_strandSucc i))
    (fun {i j} h ↦ by
      have hij : i ≠ j := by
        rintro rfl
        omega
      rw [BraidGroup.strand_eq_strandSucc_of_succ h]
      exact KnotTheory.jimboGenerator_braid q (BraidGroup.strand_ne_strandSucc i)
        (BraidGroup.strandSucc_ne_strandSucc hij) (BraidGroup.strand_ne_strandSucc_of_succ h))
    (fun h ↦ KnotTheory.jimboGenerator_mul_comm q
      (BraidGroup.nodup_strand_strandSucc_strand_strandSucc (Or.inl h)))

/-- In the Jimbo representation, the generator `T i` acts by the Jimbo R-matrix on the strands `i`
and `i + 1`. -/
@[simp]
theorem jimbo_T (i : Fin (n - 1)) :
    jimbo ι q (T q i) =
      KnotTheory.jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i) := by
  rw [jimbo, lift_T]

/-- The Jimbo representation of the braid group factors through the type-A Hecke algebra: a braid
acts on the q-tensor space as its image under the braid homomorphism does. -/
@[simp]
theorem jimbo_braidHom (b : BraidGroup n) :
    jimbo ι q (braidHom R q n b : TypeAHeckeAlgebra R q n) = KnotTheory.jimbo ι q b := by
  have h : (Units.map ((jimbo ι q (n := n)).toMonoidHom)).comp (braidHom R q n) =
      KnotTheory.jimbo ι q :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg Units.val (DFunLike.congr_fun h b)

end TauCeti.TypeAHeckeAlgebra
