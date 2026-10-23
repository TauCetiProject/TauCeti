/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD

/-!
# The simple-root basis of the checkerboard lattice

`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic` builds the checkerboard lattice
`Dₙ = {x ∈ ℤⁿ | ∑ xᵢ even}` in the Conway--Sloane coordinate model and computes its discriminant
group.  That model is the one the glue calculations need, but it does not by itself exhibit the
lattice as the root lattice of type `Dₙ`: nothing so far relates it to the Bourbaki simple roots
or to the Cartan matrix `CartanMatrix.D n`.

This file supplies that bridge, for `4 ≤ n`.  The Bourbaki-numbered simple roots

```text
αᵢ = eᵢ - eᵢ₊₁   (i + 1 < n),      α_{n-1} = e_{n-2} + e_{n-1},
```

are already pinned in classical orthogonal coordinates by
`TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD`, together with their Gram matrix and their
linear independence.  Read in the rational ambient space `ℚⁿ` they lie in the checkerboard
carrier, and they are proved here to be a `ℤ`-basis of it.  Consequently the Gram matrix of the
checkerboard lattice in that basis is exactly `CartanMatrix.D n`, which is what makes the name
"type `Dₙ` root lattice" a theorem rather than a convention.

Spanning comes from the classical expansion: the integral span of the simple roots is exactly the
lattice of integer vectors of even coordinate sum
(`TauCeti.DynkinType.mem_span_range_typeDSimpleRoot_iff`).

Two numerical consequences close the loop with the discriminant computation of the base file.  The
basis-free signed determinant of the checkerboard lattice is the determinant of the Cartan matrix,
and, since the discriminant group has order four and the Cartan matrix is a Gram matrix of a
positive form, `(CartanMatrix.D n).det = 4`.  This derives the determinant of `CartanMatrix.D` from
the lattice.

## Main declarations

* `TauCeti.IntegralLattice.checkerboardSimpleRoot`: the Bourbaki simple roots of type `Dₙ`, as
  vectors of the rational ambient space of the checkerboard lattice.
* `TauCeti.IntegralLattice.checkerboardLattice_form_checkerboardSimpleRoot_checkerboardSimpleRoot`:
  **their Gram matrix is `CartanMatrix.D n`.**
* `TauCeti.IntegralLattice.span_range_checkerboardSimpleRoot` and
  `TauCeti.IntegralLattice.linearIndependent_checkerboardSimpleRoot`: they span the checkerboard
  carrier over `ℤ`, and are `ℤ`-linearly independent.
* `TauCeti.IntegralLattice.checkerboardSimpleRootBasis`: **the simple roots are a `ℤ`-basis of the
  checkerboard lattice.**
* `TauCeti.IntegralLattice.gramMatrix_checkerboardSimpleRootBasis`: the Gram matrix of that basis
  is `CartanMatrix.D n`.
* `TauCeti.IntegralLattice.determinant_checkerboardLattice`: the signed determinant of the
  checkerboard lattice is `4`.
* `CartanMatrix.D_det`: `(CartanMatrix.D n).det = 4` for `2 ≤ n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, §4.7.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 5, the `Dₙ` rows of the ADE table.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Module

variable {n : ℕ}

/-! ## The simple roots in the rational ambient space -/

/-- The `i`-th Bourbaki-numbered simple root of type `Dₙ`, read in the rational ambient space of
the checkerboard lattice: the chain roots are `eᵢ - eᵢ₊₁` and the fork root is
`e_{n-2} + e_{n-1}`. -/
def checkerboardSimpleRoot (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : Fin n → ℚ :=
  fun j ↦ (DynkinType.typeDSimpleRoot n hn i j : ℚ)

@[simp]
theorem checkerboardSimpleRoot_apply (hn : 4 ≤ n) (i j : Fin n) :
    checkerboardSimpleRoot n hn i j = (DynkinType.typeDSimpleRoot n hn i j : ℚ) :=
  (rfl)

/-- The coordinatewise cast of an integer vector into the rational ambient space, as a
`ℤ`-linear map.  It is the comparison used to transport the classical root-system statements of
`TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD` into the ambient space of the lattice. -/
private def ratOfIntVec (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] Fin n → ℚ :=
  (Algebra.linearMap ℤ ℚ).compLeft (Fin n)

private theorem ratOfIntVec_apply (w : Fin n → ℤ) (j : Fin n) :
    ratOfIntVec n w j = (w j : ℚ) := by
  simp [ratOfIntVec]

private theorem ratOfIntVec_typeDSimpleRoot (hn : 4 ≤ n) (i : Fin n) :
    ratOfIntVec n (DynkinType.typeDSimpleRoot n hn i) = checkerboardSimpleRoot n hn i := by
  funext j
  rw [ratOfIntVec_apply, checkerboardSimpleRoot_apply]

private theorem ratOfIntVec_injective : Function.Injective (ratOfIntVec n) := by
  intro u v huv
  funext j
  exact Int.cast_injective (congrFun huv j)

/-- Every simple root lies in the checkerboard carrier: its coordinates are integers and their
sum is `0` or `2`. -/
theorem checkerboardSimpleRoot_mem_checkerboardCarrier (hn : 4 ≤ n) (i : Fin n) :
    checkerboardSimpleRoot n hn i ∈ checkerboardCarrier n :=
  mem_checkerboardCarrier_of (DynkinType.typeDSimpleRoot n hn i)
    (checkerboardSimpleRoot_apply hn i) (DynkinType.even_sum_typeDSimpleRoot hn i)

/-! ## The Gram matrix -/

/-- **The Gram matrix of the Bourbaki simple roots in the checkerboard lattice is the Cartan
matrix of type `Dₙ`.**

Not a `simp` lemma: `checkerboardLattice_form` is `@[simp]`, so `simp` rewrites the head of the
left-hand side to `Matrix.toBilin' 1` before this equation can fire.  Every sibling
`checkerboardLattice_form_*` lemma is untagged for the same reason. -/
theorem checkerboardLattice_form_checkerboardSimpleRoot_checkerboardSimpleRoot
    (hn : 4 ≤ n) (i j : Fin n) :
    (checkerboardLattice n).form (checkerboardSimpleRoot n hn i) (checkerboardSimpleRoot n hn j) =
      ((CartanMatrix.D n i j : ℤ) : ℚ) := by
  rw [checkerboardLattice_form_apply,
    ← DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j]
  push_cast [dotProduct]
  simp only [checkerboardSimpleRoot_apply]

/-! ## Spanning the checkerboard carrier -/

/-- The image of the integral span of the simple roots is their rational span. -/
private theorem map_span_typeDSimpleRoot (hn : 4 ≤ n) :
    Submodule.map (ratOfIntVec n)
        (Submodule.span ℤ (Set.range (DynkinType.typeDSimpleRoot n hn))) =
      Submodule.span ℤ (Set.range (checkerboardSimpleRoot n hn)) := by
  have hcomp : ratOfIntVec n ∘ DynkinType.typeDSimpleRoot n hn = checkerboardSimpleRoot n hn :=
    funext (ratOfIntVec_typeDSimpleRoot hn)
  rw [Submodule.map_span, ← Set.range_comp, hcomp]

/-- **The Bourbaki simple roots of type `Dₙ` span the checkerboard carrier over `ℤ`.** -/
theorem span_range_checkerboardSimpleRoot (hn : 4 ≤ n) :
    Submodule.span ℤ (Set.range (checkerboardSimpleRoot n hn)) = checkerboardCarrier n := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact checkerboardSimpleRoot_mem_checkerboardCarrier hn i
  · obtain ⟨hint, m, hm⟩ := (mem_checkerboardCarrier_iff x).mp hx
    choose w hw using hint
    have hxw : x = ratOfIntVec n w := funext fun j ↦ (ratOfIntVec_apply w j).symm ▸ hw j
    have hsum : ∑ j, w j = 2 * m := by
      have hcast : ((∑ j, w j : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by
        push_cast
        rw [← hm]
        exact (Finset.sum_congr rfl fun j _ ↦ hw j).symm
      exact_mod_cast hcast
    have heven : Even (∑ j, w j) := by
      rw [hsum]
      exact even_two_mul m
    have hmem := Submodule.mem_map_of_mem (f := ratOfIntVec n)
      ((DynkinType.mem_span_range_typeDSimpleRoot_iff hn).2 heven)
    rw [map_span_typeDSimpleRoot hn] at hmem
    rwa [hxw]

/-- **The Bourbaki simple roots of type `Dₙ` are `ℤ`-linearly independent** in the rational
ambient space of the checkerboard lattice. -/
theorem linearIndependent_checkerboardSimpleRoot (hn : 4 ≤ n) :
    LinearIndependent ℤ (checkerboardSimpleRoot n hn) := by
  rw [← funext (ratOfIntVec_typeDSimpleRoot hn)]
  exact (DynkinType.linearIndependent_typeDSimpleRoot hn).map' _
    (LinearMap.ker_eq_bot.mpr ratOfIntVec_injective)

/-- **The Bourbaki simple roots of type `Dₙ` are a `ℤ`-basis of the checkerboard lattice.**  This
is what identifies the Conway--Sloane checkerboard model with the root lattice of type `Dₙ`. -/
noncomputable def checkerboardSimpleRootBasis (n : ℕ) (hn : 4 ≤ n) :
    Basis (Fin n) ℤ (checkerboardLattice n) :=
  (Basis.span (linearIndependent_checkerboardSimpleRoot hn)).map
    (LinearEquiv.ofEq _ _ (by
      rw [span_range_checkerboardSimpleRoot hn, checkerboardLattice_carrier]))

@[simp]
theorem coe_checkerboardSimpleRootBasis_apply (hn : 4 ≤ n) (i : Fin n) :
    (checkerboardSimpleRootBasis n hn i : Fin n → ℚ) = checkerboardSimpleRoot n hn i := by
  simp [checkerboardSimpleRootBasis]

/-! ## The Gram matrix and the determinant -/

/-- **The Gram matrix of the checkerboard lattice in the simple-root basis is the Cartan matrix
of type `Dₙ`.** -/
@[simp]
theorem gramMatrix_checkerboardSimpleRootBasis (hn : 4 ≤ n) :
    (checkerboardLattice n).gramMatrix (checkerboardSimpleRootBasis n hn) = CartanMatrix.D n := by
  ext i j
  have h :=
    intCast_gramMatrix_apply (checkerboardLattice n) (checkerboardSimpleRootBasis n hn) i j
  rw [coe_checkerboardSimpleRootBasis_apply, coe_checkerboardSimpleRootBasis_apply,
    checkerboardLattice_form_checkerboardSimpleRoot_checkerboardSimpleRoot hn] at h
  exact_mod_cast h

/-- **The signed determinant of the checkerboard lattice is the determinant of the Cartan matrix
of type `Dₙ`.** -/
theorem determinant_checkerboardLattice_eq_det_cartanMatrixD (hn : 4 ≤ n) :
    (checkerboardLattice n).determinant = (CartanMatrix.D n).det := by
  rw [determinant_eq_gramDet _ (checkerboardSimpleRootBasis n hn), gramDet_def,
    gramMatrix_checkerboardSimpleRootBasis hn]

end IntegralLattice

end TauCeti

namespace CartanMatrix

/-- **The determinant of the Cartan matrix of type `Dₙ` is `4`.**

For `4 ≤ n` the argument is lattice-theoretic rather than a direct expansion: the Cartan matrix is
the Gram matrix of the checkerboard lattice in its simple-root basis, so its determinant is a
square, and its absolute value is the order of the checkerboard discriminant group, which is four.
The two smaller ranks follow from Mathlib's explicit matrices. -/
theorem D_det (hn : 2 ≤ n) : (D n).det = 4 := by
  by_cases hn4 : 4 ≤ n
  swap
  · have hn_small : n = 2 ∨ n = 3 := by omega
    rcases hn_small with rfl | rfl
    · rw [D_two, Matrix.det_fin_two_of]
      norm_num
    · rw [D_three, Matrix.det_fin_three]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_fin_one]
  have : NeZero n := ⟨by omega⟩
  have hsq := TauCeti.DynkinType.det_cartanMatrixD_eq_det_typeDSimpleRoot_sq hn4
  have hnonneg : 0 ≤ (D n).det := by
    rw [hsq]
    exact sq_nonneg _
  have habs : ((D n).det).natAbs = 4 := by
    rw [← TauCeti.IntegralLattice.determinant_checkerboardLattice_eq_det_cartanMatrixD hn4,
      ← TauCeti.IntegralLattice.discriminant_def]
    exact TauCeti.IntegralLattice.discriminant_checkerboardLattice n
  omega

end CartanMatrix

namespace TauCeti

namespace IntegralLattice

/-- **The signed determinant of the checkerboard lattice is `4`.** -/
@[simp]
theorem determinant_checkerboardLattice (hn : 4 ≤ n) :
    (checkerboardLattice n).determinant = 4 := by
  rw [determinant_checkerboardLattice_eq_det_cartanMatrixD hn, CartanMatrix.D_det (by omega)]

end IntegralLattice

end TauCeti
