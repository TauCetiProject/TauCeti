/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Functions on a faithfully flat quotient

For a faithfully flat morphism `f : H ⟶ K` of commutative Hopf algebras, the functions on
`Spec K` invariant under its scheme-theoretic kernel are exactly the functions pulled back
from `Spec H`. In coordinates, `(kernelHopfIdeal f).coinvariants = f.hom.toAlgHom.range`.
This is the coordinate exactness statement for a faithfully flat quotient of affine groups.
No finite presentation or smoothness hypothesis is needed.

More generally, the equality holds whenever the coordinate map satisfies
`Algebra.IsEffective`. The kernel-invariance characterization identifies invariant functions
with functions constant on fibers over every value algebra, connecting the functor-of-points
and coordinate-algebra descriptions of affine-group quotients.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
* Mathlib's `Algebra.IsEffective.eqLocus_includeLeft_includeRight` and
  `Algebra.IsEffective.of_faithfullyFlat`.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- A function invariant under the kernel takes the same value on points with the same image,
over a value algebra in any universe. -/
theorem ofConv_apply_eq_of_mem_coinvariants_kernelHopfIdeal (f : H ⟶ K) {x : K}
    (hx : x ∈ (kernelHopfIdeal f).coinvariants) {A : CommAlgCat.{w} R}
    (g g' : HopfAlgebra.points (R := R) (H := K) A)
    (hgg' : (mapPointsFunctor f).app A g = (mapPointsFunctor f).app A g') :
    g.ofConv x = g'.ofConv x := by
  have hn : g⁻¹ * g' ∈ quotientPointsSubgroup K (kernelHopfIdeal f) A := by
    apply (mapPointsFunctor_app_eq_one_iff f A _).mp
    rw [← mapPointsFunctor_app_apply]
    exact ((mapPointsFunctor f).app A).hom.eq_iff.mp hgg'.symm
  simpa only [mul_inv_cancel_left] using
    (HopfIdeal.ofConv_mul_apply_of_mem_coinvariants hx g hn).symm

/-- A function is invariant under the kernel exactly when it takes the same value on any two
points with the same image, over every value algebra in the coordinate algebras' universe. -/
theorem mem_coinvariants_kernelHopfIdeal_iff (f : H ⟶ K) (x : K) :
    x ∈ (kernelHopfIdeal f).coinvariants ↔
      ∀ (A : CommAlgCat.{v} R) (g g' : HopfAlgebra.points (R := R) (H := K) A),
        (mapPointsFunctor f).app A g = (mapPointsFunctor f).app A g' →
          g.ofConv x = g'.ofConv x := by
  constructor
  · intro hx A g g' hgg'
    exact ofConv_apply_eq_of_mem_coinvariants_kernelHopfIdeal f hx g g' hgg'
  · intro hx
    apply HopfIdeal.mem_coinvariants_iff_forall_mul.mpr
    intro A g n hn
    apply hx A (g * n) g
    simp only [mapPointsFunctor_app_apply, ← AlgHom.mapDomain_apply]
    apply (AlgHom.mapDomain (A := A) f.hom).eq_iff.mpr
    simpa only [inv_mul_cancel_left, MonoidHom.mem_ker, AlgHom.mapDomain_apply] using
      (mapPointsFunctor_app_eq_one_iff f A n).mpr hn

/-- If the coordinate map is effective, the functions invariant under its kernel are precisely
the pullbacks of functions on its target. -/
theorem coinvariants_kernelHopfIdeal_eq_range_of_isEffective (f : H ⟶ K)
    (hf : letI := f.hom.toAlgHom.toAlgebra; Algebra.IsEffective H K) :
    (kernelHopfIdeal f).coinvariants = f.hom.toAlgHom.range := by
  let : Algebra H K := f.hom.toAlgHom.toAlgebra
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
    dsimp only [g, g', A, ofConv_toConv, AlgHom.restrictScalars_apply] at heq
    have hx' : x ∈ Set.range (algebraMap H K) := by
      rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight hf]
      apply RingHom.mem_eqLocus.mpr
      simpa only [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using heq
    simpa only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Set.mem_range, AlgHom.mem_range] using hx'
  · rintro ⟨a, rfl⟩
    apply (mem_coinvariants_kernelHopfIdeal_iff f _).mpr
    intro A g g' hgg'
    simpa only [mapPointsFunctor_app_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom] using
      congrArg (fun p : HopfAlgebra.points (R := R) (H := H) A ↦ p.ofConv a) hgg'

/-- The functions invariant under the kernel of a faithfully flat affine-group morphism are
precisely the pullbacks of functions on its target. -/
@[simp]
theorem coinvariants_kernelHopfIdeal_eq_range (f : H ⟶ K)
    (hf : (f.hom.toAlgHom : H →+* K).FaithfullyFlat) :
    (kernelHopfIdeal f).coinvariants = f.hom.toAlgHom.range := by
  let : Algebra H K := f.hom.toAlgHom.toAlgebra
  let : Module.FaithfullyFlat H K := hf
  exact coinvariants_kernelHopfIdeal_eq_range_of_isEffective f
    (Algebra.IsEffective.of_faithfullyFlat H K)

end TauCeti.CommHopfAlgCat
