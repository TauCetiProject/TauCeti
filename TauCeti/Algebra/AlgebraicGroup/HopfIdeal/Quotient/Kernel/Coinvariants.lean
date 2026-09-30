/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Functions on a faithfully flat quotient

For a faithfully flat morphism `f : H ⟶ K` of commutative Hopf algebras, the functions on
`Spec K` invariant under its scheme-theoretic kernel are exactly the functions pulled back
from `Spec H`. In coordinates, `(kernelHopfIdeal f).coinvariants = f.hom.toAlgHom.range`.
This is the coordinate exactness statement for a faithfully flat quotient of affine groups.
No finite presentation or smoothness hypothesis is needed.

The proof uses the functor-of-points characterization of coinvariants and Mathlib's
`Algebra.IsEffective.of_faithfullyFlat`. The two universal points with values in `K ⊗[H] K`
have the same image in `Spec H`, so their ratio belongs to the kernel. Invariance therefore
gives the descent equalizer equation, which recovers a unique function on `Spec H`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- A function is invariant under the kernel exactly when it takes the same value on any two
points with the same image, over every value algebra. -/
theorem mem_coinvariants_kernelHopfIdeal_iff (f : H ⟶ K) (x : K) :
    x ∈ (kernelHopfIdeal f).coinvariants ↔
      ∀ (A : CommAlgCat.{v} R) (g g' : HopfAlgebra.points (R := R) (H := K) A),
        (mapPointsFunctor f).app A g = (mapPointsFunctor f).app A g' →
          g.ofConv x = g'.ofConv x := by
  rw [HopfIdeal.mem_coinvariants_iff_forall_mul]
  constructor
  · intro hx A g g' hgg'
    simp only [mapPointsFunctor_app_apply, ← AlgHom.mapDomain_apply] at hgg'
    have hn : g⁻¹ * g' ∈ quotientPointsSubgroup K (kernelHopfIdeal f) A := by
      apply (mapPointsFunctor_app_eq_one_iff f A _).mp
      rw [← AlgHom.mapDomain_apply, map_mul, map_inv, hgg', inv_mul_cancel]
    simpa using (hx A g (g⁻¹ * g') hn).symm
  · intro hx A g n hn
    apply hx A (g * n) g
    have hn' := (mapPointsFunctor_app_eq_one_iff f A n).mpr hn
    simp only [mapPointsFunctor_app_apply, ← AlgHom.mapDomain_apply]
    rw [← AlgHom.mapDomain_apply] at hn'
    rw [map_mul, hn', mul_one]

/-- The functions invariant under the kernel of a faithfully flat affine-group morphism are
precisely the pullbacks of functions on its target. -/
theorem coinvariants_kernelHopfIdeal_eq_range (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    (kernelHopfIdeal f).coinvariants = f.hom.toAlgHom.range := by
  let : Algebra H K := f.hom.toAlgHom.toAlgebra
  let : Module.FaithfullyFlat H K := hf
  ext x
  constructor
  · intro hx
    let A : CommAlgCat.{v} R := CommAlgCat.of R (K ⊗[H] K)
    let g : HopfAlgebra.points (R := R) (H := K) A :=
      toConv Algebra.TensorProduct.includeLeft
    let g' : HopfAlgebra.points (R := R) (H := K) A :=
      toConv (Algebra.TensorProduct.includeRight.restrictScalars R)
    have hgg' : (mapPointsFunctor f).app A g = (mapPointsFunctor f).app A g' := by
      rw [mapPointsFunctor_app_apply, mapPointsFunctor_app_apply]
      apply ofConv_injective
      ext a
      exact RingHom.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := H) (A := K) (B := K)) a
    have heq := (mem_coinvariants_kernelHopfIdeal_iff f x).mp hx A g g' hgg'
    have hx' : x ∈ Set.range (algebraMap H K) := by
      rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
        (Algebra.IsEffective.of_faithfullyFlat H K)]
      exact heq
    exact hx'
  · rintro ⟨a, rfl⟩
    apply (mem_coinvariants_kernelHopfIdeal_iff f _).mpr
    intro A g g' hgg'
    exact congrArg (fun p : HopfAlgebra.points (R := R) (H := H) A ↦ p.ofConv a) hgg'

end TauCeti.CommHopfAlgCat
