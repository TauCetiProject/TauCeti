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
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Base change of linear independence from a field

A family of vectors in a finite coordinate space over a field `K` is linearly independent
exactly when its image under `algebraMap K S` is linearly independent over `S`, for any
nontrivial commutative semiring `S`. Mathlib's `linearIndependent_algebraMap_comp_iff` proves
this for a faithful algebra between commutative rings whose target is a domain; a field source
removes every hypothesis on the target beyond nontriviality.

## References

* The proof adapts Oliver Nash's private Mathlib lemma
  `LinearIndependent.linearIndependent_algebraMap_comp_aux` and the converse direction of
  `linearIndependent_algebraMap_comp_iff`, both in
  `Mathlib/LinearAlgebra/LinearIndependent/BaseChange.lean`: extend the family to a basis and
  base change that basis along `Module.Basis.baseChange`.
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
    let I : Set (ι' → K) := h.linearIndepOn_id.extend (Set.subset_univ _)
    let b : Module.Basis I K (ι' → K) := .extend h.linearIndepOn_id
    let b' := (b.baseChange S).map (TensorProduct.piScalarRight K S S ι')
    let w (i : ι) : I := ⟨v i, h.linearIndepOn_id.subset_extend _ (Set.mem_range_self i)⟩
    have hw : b' ∘ w = fun i ↦ algebraMap K S ∘ v i := by
      ext
      simp [b', b, w, Module.Basis.extend, Algebra.algebraMap_eq_smul_one]
    rw [← hw]
    exact b'.linearIndependent.comp w (fun i j hij ↦ h.injective (congrArg Subtype.val hij))

end TauCeti
