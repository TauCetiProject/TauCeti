/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Base change of linear independence from a field

A family of vectors in a finite coordinate space over a field `K` is linearly independent
exactly when its image under `algebraMap K S` is linearly independent over `S`, for any
nontrivial commutative semiring `S`. Mathlib's `linearIndependent_algebraMap_comp_iff` proves
this for a faithful algebra between commutative rings whose target is a domain; a field source
removes every hypothesis on the target beyond nontriviality.

## References

* The reflecting direction adapts the converse direction of Oliver Nash's Mathlib lemma
  `linearIndependent_algebraMap_comp_iff` in
  `Mathlib/LinearAlgebra/LinearIndependent/BaseChange.lean`. The preserving direction uses
  flatness of `S` over the field `K`, through Mathlib's `Module.Flat.linearIndependent_one_tmul`.
-/

public section

namespace TauCeti

/-- Over a field source, applying `algebraMap K S` to every coordinate preserves and reflects
linear independence of a family in a finite coordinate space, for any nontrivial commutative
semiring `S`. -/
@[simp]
theorem linearIndependent_algebraMap_comp_iff_of_field {K S ι ι' : Type*} [Field K]
    [CommSemiring S] [Nontrivial S] [Algebra K S] [Finite ι'] {v : ι → ι' → K} :
    LinearIndependent S (fun i ↦ algebraMap K S ∘ v i) ↔ LinearIndependent K v := by
  have hcomp : (fun i ↦ algebraMap K S ∘ v i) = Pi.algebraMap ι' K S ∘ v := by
    ext
    simp [Pi.algebraMap]
  constructor
  · intro h
    have : FaithfulSMul K S :=
      (faithfulSMul_iff_algebraMap_injective K S).2 (algebraMap K S).injective
    rw [hcomp] at h
    exact (h.restrict_scalars' K).of_comp
  · intro h
    classical
    cases nonempty_fintype ι'
    let := Module.addCommMonoidToAddCommGroup K (M := S)
    let e := TensorProduct.piScalarRight K S S ι'
    have h' := (e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn).2
      (Module.Flat.linearIndependent_one_tmul (S := S) h)
    convert h' using 1
    ext
    simp [e, Algebra.algebraMap_eq_smul_one]

end TauCeti
