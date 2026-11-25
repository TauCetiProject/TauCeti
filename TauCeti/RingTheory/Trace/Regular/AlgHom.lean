/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.Trace.Basic
public import TauCeti.RingTheory.Localization.Module.Basis
public import TauCeti.RingTheory.Trace.Regular

/-!
# The regular trace form along injective algebra maps

The regular trace form `Algebra.regularTraceForm R S` pairs `x` and `y` to the trace over `R` of
left multiplication by `x * y` on `S`. This file compares it along two kinds of injective algebra
maps `f`, neither of which need be surjective.

If `f : S' → S` is an injective algebra map between finite free `R`-algebras of the same rank,
then `f` preserves the regular trace form, although its image may be a proper sublattice: over
`ℤ`, the inclusion of `ℤ[2i]` in `ℤ[i]` has index `2`. Left multiplication by `f x` on `S` and by
`x` on `S'` are intertwined by the matrix of `f`, whose determinant is a non-zero-divisor.

If `f : S → E` is an injective algebra map from a finite free `R`-algebra into an algebra `E` over
the fraction field `K` of `R` whose image spans `E` over `K`, then the regular trace form of `S`
maps to that of `E` over `K`: an `R`-basis of `S` is carried to a `K`-basis of `E` in which left
multiplication has the same matrix.

## Main results

* `Algebra.regularTraceForm_algHom_apply`: an injective algebra map between finite free algebras of
  the same rank preserves the regular trace form.
* `Algebra.algebraMap_regularTraceForm`: the regular trace form of an order `S` maps to the regular
  trace form over the fraction field of the algebra `E` that `S` spans.
-/

public section

open LinearMap Module Submodule

namespace Algebra

section AlgHom

variable {R S S' : Type*} [CommRing R] [Ring S] [Algebra R S] [Ring S'] [Algebra R S']

/-- The regular trace form is preserved by an injective algebra map between algebras with bases of
the same finite size. -/
private theorem regularTraceForm_algHom_apply_of_basis {ι : Type*} [Finite ι] (f : S' →ₐ[R] S)
    (hf : Function.Injective f) (b' : Basis ι R S') (b : Basis ι R S) (x y : S') :
    regularTraceForm R S (f x) (f y) = regularTraceForm R S' x y := by
  classical
  have := Fintype.ofFinite ι
  have hP : b.toMatrix (f ∘ b') = LinearMap.toMatrix b' b f.toLinearMap := by
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  have hdet := b.det_mem_nonZeroDivisors
    (b'.linearIndependent.map' f.toLinearMap (LinearMap.ker_eq_bot.2 hf))
  rw [Basis.det_apply, AlgHom.coe_toLinearMap, hP] at hdet
  rw [regularTraceForm_apply, regularTraceForm_apply, ← map_mul,
    LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace R b']
  refine Matrix.trace_eq_of_mul_eq_mul hdet ?_
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  congr 1
  ext z
  simp [mul_assoc]

/-- **An injective algebra map between finite free algebras of the same rank preserves the regular
trace form**, although its image may be a proper sublattice: for `x` in `S'`, left multiplication
by `f x` on `S` and by `x` on `S'` have the same trace. -/
theorem regularTraceForm_algHom_apply [Module.Free R S] [Module.Finite R S] [Module.Free R S']
    [Module.Finite R S'] (f : S' →ₐ[R] S) (hf : Function.Injective f)
    (hrank : finrank R S' = finrank R S) (x y : S') :
    regularTraceForm R S (f x) (f y) = regularTraceForm R S' x y := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  exact regularTraceForm_algHom_apply_of_basis f hf (finBasisOfFinrankEq R S' hrank)
    (finBasis R S) x y

end AlgHom

section FractionRing

variable {R K S E : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Ring S] [Algebra R S] [Ring E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]

/-- **The regular trace of an order is the rational regular trace.** Let `S` be a finite free
`R`-algebra and `f : S → E` an injective algebra map into an algebra `E` over the fraction field `K`
of `R`, whose image spans `E` over `K`. Then the regular trace form of `S` over `R` maps to that of
`E` over `K`. -/
theorem algebraMap_regularTraceForm [Module.Free R S] [Module.Finite R S] (f : S →ₐ[R] E)
    (hf : Function.Injective f) (hspan : span K (Set.range f) = ⊤) (x y : S) :
    algebraMap R K (regularTraceForm R S x y) = regularTraceForm K E (f x) (f y) := by
  classical
  let b := Free.chooseBasis R S
  have hf' : Function.Injective f.toLinearMap := by simpa using hf
  have hspan' : span K (Set.range f.toLinearMap) = ⊤ := by simpa using hspan
  let bK := b.ofFractionRingOfSpan f.toLinearMap hf' hspan'
  have hmat : LinearMap.toMatrix bK bK (lmul K E (f (x * y))) =
      (LinearMap.toMatrix b b (lmul R S (x * y))).map (algebraMap R K) := by
    ext i j
    simpa [bK, LinearMap.toMatrix_apply, ← map_mul] using
      b.ofFractionRingOfSpan_repr_apply f.toLinearMap hf' hspan' (x * y * b j) i
  rw [regularTraceForm_apply, regularTraceForm_apply, ← map_mul,
    LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace K bK, hmat,
    AddMonoidHom.map_trace]

end FractionRing

end Algebra
