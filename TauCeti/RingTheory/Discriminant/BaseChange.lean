/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Discriminant
public import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Discriminants under base change

The trace matrix of an arbitrary family, and the discriminant of a finite family, in a finite
free algebra commute with scalar extension. In particular, for a basis `b` of `S` over `R` and
an `R`-algebra `A`, the discriminant of the base-changed basis of `A ⊗[R] S` over `A` is the
image of the discriminant of `b`. This lets statements about discriminants pass to residue
fields and localizations.

## Main results

* `TauCeti.Algebra.traceMatrix_baseChange`: the trace matrix of a base-changed family is
  the image of its original trace matrix.
* `TauCeti.Algebra.discr_baseChange`: the discriminant of a base-changed finite family is the
  image of its original discriminant.
* `TauCeti.Algebra.discr_basis_baseChange`: the basis specialization.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/DiscriminantFiber.lean`: `traceMatrix_baseChange` and `discr_baseChange`
  are its `Pcf.Stacks.Algebra.traceMatrix_baseChange` and `Pcf.Stacks.Algebra.discr_baseChange`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R S A ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]

/-- The trace matrix of a base-changed family is the image of its original trace matrix. -/
@[simp]
theorem Algebra.traceMatrix_baseChange [Module.Free R S] [Module.Finite R S]
    (b : ι → S) :
    Algebra.traceMatrix A (fun i ↦ (1 : A) ⊗ₜ[R] b i) =
      (Algebra.traceMatrix R b).map (algebraMap R A) := by
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.trace_baseChange_tmul]

/-- The discriminant of a base-changed finite family is the image of its original discriminant. -/
@[simp]
theorem Algebra.discr_baseChange [Module.Free R S] [Module.Finite R S] [Fintype ι]
    [DecidableEq ι] (b : ι → S) :
    Algebra.discr A (fun i ↦ (1 : A) ⊗ₜ[R] b i) = algebraMap R A (Algebra.discr R b) := by
  rw [Algebra.discr_def, Algebra.discr_def, Algebra.traceMatrix_baseChange, RingHom.map_det,
    RingHom.mapMatrix_apply]

/-- The discriminant of a base-changed basis is the image of its original discriminant. -/
@[simp]
theorem Algebra.discr_basis_baseChange [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) :
    Algebra.discr A (Algebra.TensorProduct.basis A b) = algebraMap R A (Algebra.discr R b) := by
  have : Module.Free R S := Module.Free.of_basis b
  have : Module.Finite R S := Module.Finite.of_basis b
  have hb : (Algebra.TensorProduct.basis A b : ι → A ⊗[R] S) =
      (fun i ↦ (1 : A) ⊗ₜ[R] b i) := by
    funext i
    simp [Algebra.TensorProduct.basis_apply]
  rw [hb]
  exact Algebra.discr_baseChange (R := R) (S := S) (A := A) (b := b)

end TauCeti
