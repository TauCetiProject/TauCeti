/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Base change of linear independence from a field

A family of vectors in a finite coordinate space over a field `K` is linearly independent
exactly when its image under `algebraMap K S` is linearly independent over `S`, for any
nontrivial commutative semiring `S`. More generally this holds whenever `S` is a flat and
faithful algebra over a commutative semiring `K`. Mathlib's `linearIndependent_algebraMap_comp_iff`
proves this for a faithful algebra between commutative rings whose target is a domain; a field
source removes every hypothesis on the target beyond nontriviality.

## References

* The reflecting direction adapts the converse direction of Oliver Nash's Mathlib lemma
  `linearIndependent_algebraMap_comp_iff` in
  `Mathlib/LinearAlgebra/LinearIndependent/BaseChange.lean`. The preserving direction uses
  flatness of `S` over `K`, through Mathlib's `Module.Flat.linearIndependent_one_tmul`.
-/

public section

namespace TauCeti

/-- For a flat and faithful algebra `S` over `K`, applying `algebraMap K S` to every coordinate
preserves and reflects linear independence of a family in a finite coordinate space. -/
theorem linearIndependent_algebraMap_comp_iff_of_flat {K S ι ι' : Type*} [CommSemiring K]
    [CommSemiring S] [Algebra K S] [Module.Flat K S] [FaithfulSMul K S] [Finite ι']
    {v : ι → ι' → K} :
    LinearIndependent S (fun i ↦ algebraMap K S ∘ v i) ↔ LinearIndependent K v := by
  constructor
  · intro h
    have hcomp : (fun i ↦ algebraMap K S ∘ v i) = Pi.algebraMap ι' K S ∘ v := by
      ext
      simp [Pi.algebraMap]
    rw [hcomp] at h
    exact (h.restrict_scalars' K).of_comp
  · intro h
    classical
    cases nonempty_fintype ι'
    let e := TensorProduct.piScalarRight K S S ι'
    have he : (fun i ↦ algebraMap K S ∘ v i) = e ∘ fun i ↦ (1 : S) ⊗ₜ[K] v i := by
      ext
      simp [e, Algebra.algebraMap_eq_smul_one]
    rw [he]
    exact (e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn).2
      (Module.Flat.linearIndependent_one_tmul h)

/-- Over a field source, applying `algebraMap K S` to every coordinate preserves and reflects
linear independence of a family in a finite coordinate space, for any nontrivial commutative
semiring `S`. -/
@[simp]
theorem linearIndependent_algebraMap_comp_iff_of_field {K S ι ι' : Type*} [Field K]
    [CommSemiring S] [Nontrivial S] [Algebra K S] [Finite ι'] {v : ι → ι' → K} :
    LinearIndependent S (fun i ↦ algebraMap K S ∘ v i) ↔ LinearIndependent K v := by
  have : FaithfulSMul K S :=
    (faithfulSMul_iff_algebraMap_injective K S).2 (algebraMap K S).injective
  -- `S` is free, hence flat, over the field `K`; Mathlib's freeness instance
  -- `Module.Free.of_divisionRing` needs an additive group, which exists only locally here.
  have : Module.Flat K S := by
    let := Module.addCommMonoidToAddCommGroup K (M := S)
    infer_instance
  exact linearIndependent_algebraMap_comp_iff_of_flat

end TauCeti
