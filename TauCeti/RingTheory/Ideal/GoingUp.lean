/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lying over along an integral ring homomorphism

An integral ring homomorphism `g : S →+* T` lifts each prime ideal of `S` containing its kernel
to a prime ideal of `T`. This is Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral` stated
directly for `g`, so callers need not install an algebra structure.

Along an integral algebra, maximal ideals contract to maximal ideals, so the extension of an
ideal contained in the Jacobson radical is again contained in the Jacobson radical.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
* `Ideal.map_le_jacobson_bot_of_isIntegral`: along an integral algebra, the extension of an ideal
  in the Jacobson radical lies in the Jacobson radical.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/FiniteAlgebraIdempotents.lean`: `map_le_jacobson_bot_of_isIntegral` is
  the algebra form of its `Pcf.Stacks.map_le_jacobson_bot_of_le_jacobson_of_isIntegral`.
-/

public section

namespace Ideal

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Lying over along an integral ring homomorphism `g : S →+* T`: a prime `P` of `S`
containing the kernel of `g` is the contraction along `g` of a prime of `T`. -/
theorem exists_comap_eq_of_isIntegral (P : Ideal S) [P.IsPrime]
    (g : S →+* T) (hg : g.IsIntegral) (hP : RingHom.ker g ≤ P) :
    ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap g = P := by
  let _ : Algebra S T := g.toAlgebra
  have : Algebra.IsIntegral S T := ⟨hg⟩
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal T)
    (by rwa [under_def, RingHom.algebraMap_toAlgebra, ← RingHom.ker_eq_comap_bot])
  exact ⟨Q, hQ, hQP⟩

/-- Along an integral algebra, the extension of an ideal in the Jacobson radical lies in the
Jacobson radical, since maximal ideals contract to maximal ideals. -/
theorem map_le_jacobson_bot_of_isIntegral [Algebra S T] [Algebra.IsIntegral S T] {I : Ideal S}
    (hI : I ≤ jacobson ⊥) : I.map (algebraMap S T) ≤ jacobson ⊥ := by
  refine le_sInf fun M ⟨_, hM⟩ ↦ map_le_iff_le_comap.mpr <| hI.trans <| sInf_le
    ⟨bot_le, isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap S T)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) M⟩

end Ideal
