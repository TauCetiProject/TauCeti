/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Base change of linear independence of coordinate vectors

A family of vectors in a finite coordinate space over a field `K` is linearly independent
exactly when its image under `algebraMap K S` is linearly independent over `S`, for any
nontrivial commutative semiring `S`. More generally this holds whenever `S` is a flat and
faithful algebra over a commutative semiring `K`. Mathlib's `linearIndependent_algebraMap_comp_iff`
proves this for a faithful algebra between commutative rings whose target is a domain; a field
source removes every hypothesis on the target beyond nontriviality.

Without flatness, a family `v` of coordinate vectors `ι → R` that admits a dual family of linear
forms, `φ x (v y)` being `1` for `x = y` and `0` otherwise, is linearly independent
(`LinearIndependent.of_pairwise_dual_eq_zero_one`). Applying any ring homomorphism `f : R →+* A`
to every coordinate keeps it linearly independent over `A`, since the linear forms can be written
as row vectors and mapped along `f` as well. For instance, a basis over `R` of a direct summand of
`ι → R` stays linearly independent over every `R`-algebra.

## Main results

* `TauCeti.linearIndependent_algebraMap_comp_iff_of_flat`,
  `TauCeti.linearIndependent_algebraMap_comp_iff_of_field`: base change of linear independence
  along a flat and faithful algebra, or from a field.
* `LinearIndependent.map_of_pairwise_dual_eq_zero_one`: the coordinatewise images `f ∘ v x` of a
  family with a dual family are linearly independent over `A`.

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

variable {X ι R A : Type*} [Finite ι] [CommSemiring R] [CommRing A]

/-- If a family `v` of coordinate vectors over `R` admits linear forms `φ` with `φ x (v y)` equal
to `1` for `x = y` and to `0` otherwise, then its coordinatewise images `f ∘ v x` under a ring
homomorphism `f : R →+* A` are linearly independent over `A`. -/
theorem LinearIndependent.map_of_pairwise_dual_eq_zero_one (f : R →+* A) (v : X → ι → R)
    (φ : X → Module.Dual R (ι → R)) (h1 : Pairwise fun x y ↦ φ x (v y) = 0)
    (h2 : ∀ x, φ x (v x) = 1) : LinearIndependent A fun x ↦ f ∘ v x := by
  classical
  have := Fintype.ofFinite ι
  -- The linear form `φ x` is the row vector of its values on the standard basis, mapped by `f`.
  let ψ : X → Module.Dual A (ι → A) := fun x ↦
    Fintype.linearCombination A fun j ↦ f (φ x fun j' ↦ if j = j' then 1 else 0)
  have hψ (x y : X) : ψ x (f ∘ v y) = f (φ x (v y)) := by
    rw [LinearMap.pi_apply_eq_sum_univ (φ x) (v y), map_sum, Fintype.linearCombination_apply]
    simp
  refine .of_pairwise_dual_eq_zero_one _ ψ (fun x y hxy ↦ ?_) fun x ↦ ?_
  · simp only [hψ, h1 hxy, map_zero]
  · rw [hψ, h2, map_one]
