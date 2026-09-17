/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

/-!
# Coordinate powers of finite bilinear and quadratic modules

A finite bilinear module `A` determines a bilinear module on words `ι → A` by summing its
pairing coordinatewise.  Thus the orthogonal complement of an additive subgroup of words is its
standard dual additive code.  Nondegeneracy of the alphabet pairing passes to every finite
coordinate power, so the existing orthogonal-complement cardinality and double-complement
theorems apply to these codes.

For a finite quadratic module the quadratic value of a word is likewise the sum of its coordinate
values.  Its polar bilinear module is definitionally the corresponding coordinate power.  These
constructions are the finite-form interface used when code coordinates are identified with
discriminant-module coordinates.

## Main declarations

* `TauCeti.FiniteBilinearModule.coordinatePower`: the summed pairing on `ι → A`.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.coordinatePower`: nondegeneracy of a coordinate
  power.
* `TauCeti.FiniteBilinearModule.mem_orthogonalComplement_coordinatePower_iff`: membership in the
  dual additive code.
* `TauCeti.FiniteBilinearModule.Isometry.coordinatePower`: the coordinatewise isometry induced by
  an alphabet isometry.
* `TauCeti.FiniteQuadraticModule.coordinatePower`: the summed quadratic map on `ι → A`.
* `TauCeti.FiniteQuadraticModule.isIsotropic_coordinatePower_iff`: the coordinate-sum criterion
  for quadratic isotropy.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §§1.2–1.4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
-/

public section

namespace TauCeti

universe u v w

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule.{u})

/-- The finite bilinear module on words `ι → A`, with pairing obtained by summing the
coordinate pairings.

This is reducible, as `FiniteBilinearModule.prod` is, so that additive codes in the raw function
type are directly subgroups of the coordinate power. -/
abbrev coordinatePower (ι : Type v) [Fintype ι] : FiniteBilinearModule where
  carrier := ι → A
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ∑ i, A.pairing (x i) (y i)
          map_zero' := by simp
          map_add' := fun y z ↦ by simp only [Pi.add_apply, A.pairing_add_right,
            Finset.sum_add_distrib] }
      map_zero' := by
        ext y
        simp only [Pi.zero_apply, A.pairing_zero_left, Finset.sum_const_zero]
        rfl
      map_add' := fun x y ↦ by
        ext z
        simp only [Pi.add_apply, A.pairing_add_left, Finset.sum_add_distrib]
        rfl }
  pairing_comm := fun x y ↦
    Finset.sum_congr rfl fun i _ ↦ A.pairing_comm (x i) (y i)

/-- The pairing on a coordinate power is the sum of the coordinate pairings. -/
theorem coordinatePower_pairing (ι : Type v) [Fintype ι] (x y : ι → A) :
    (A.coordinatePower ι).pairing x y = ∑ i, A.pairing (x i) (y i) :=
  (rfl)

/-- Pairing a word with a word supported at one coordinate extracts that coordinate pairing. -/
theorem coordinatePower_pairing_single_right (ι : Type v) [Fintype ι] [DecidableEq ι]
    (x : ι → A) (i : ι) (a : A) :
    (A.coordinatePower ι).pairing x (Pi.single i a) = A.pairing (x i) a := by
  rw [A.coordinatePower_pairing, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, A.pairing_zero_right]
  · simp

/-- Pairing a word supported at one coordinate with an arbitrary word extracts that coordinate
pairing. -/
theorem coordinatePower_pairing_single_left (ι : Type v) [Fintype ι] [DecidableEq ι]
    (i : ι) (a : A) (y : ι → A) :
    (A.coordinatePower ι).pairing (Pi.single i a) y = A.pairing a (y i) := by
  rw [(A.coordinatePower ι).pairing_comm, A.coordinatePower_pairing_single_right,
    A.pairing_comm]

/-- A coordinate power of a nondegenerate finite bilinear module is nondegenerate. -/
theorem IsNondegenerate.coordinatePower {A : FiniteBilinearModule.{u}} (hA : A.IsNondegenerate)
    (ι : Type v) [Fintype ι] : (A.coordinatePower ι).IsNondegenerate := by
  rw [(A.coordinatePower ι).isNondegenerate_iff_injective]
  intro x y hxy
  funext i
  apply hA.injective
  ext a
  classical
  have h : (A.coordinatePower ι).pairing x (Pi.single i a) =
      (A.coordinatePower ι).pairing y (Pi.single i a) :=
    DFunLike.congr_fun hxy (Pi.single i a)
  simpa only [A.coordinatePower_pairing_single_right] using h

/-- Membership in the orthogonal complement of an additive code is vanishing of every summed
coordinate pairing. -/
@[simp]
theorem mem_orthogonalComplement_coordinatePower_iff (ι : Type v) [Fintype ι]
    (C : AddSubgroup (ι → A)) (x : ι → A) :
    x ∈ (A.coordinatePower ι).orthogonalComplement C ↔
      ∀ y ∈ C, ∑ i, A.pairing (x i) (y i) = 0 := by
  rw [(A.coordinatePower ι).mem_orthogonalComplement_iff]
  simp only [A.coordinatePower_pairing]

section Isometry

variable {A : FiniteBilinearModule.{u}} {B : FiniteBilinearModule.{w}}

/-- An isometry of finite bilinear alphabets induces an isometry on every finite coordinate
power by acting coordinatewise. -/
def Isometry.coordinatePower (f : Isometry A B) (ι : Type v) [Fintype ι] :
    Isometry (A.coordinatePower ι) (B.coordinatePower ι) where
  toAddEquiv := AddEquiv.piCongrRight fun _ ↦ f.toAddEquiv
  map_pairing' x y := by
    rw [coordinatePower_pairing, coordinatePower_pairing]
    exact Finset.sum_congr rfl fun i _ ↦ f.map_pairing (x i) (y i)

/-- A coordinatewise bilinear-module isometry acts at each coordinate by the alphabet
isometry. -/
@[simp]
theorem Isometry.coordinatePower_apply (f : Isometry A B) (ι : Type v) [Fintype ι]
    (x : ι → A) (i : ι) : f.coordinatePower ι x i = f (x i) :=
  (rfl)

end Isometry

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule.{u})

/-- The finite quadratic module on words `ι → A`, with quadratic value obtained by summing
the coordinate values.

This is reducible so that its carrier is literally the raw function type and its polar module is
definitionally the bilinear coordinate power. -/
abbrev coordinatePower (ι : Type v) [Fintype ι] : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.coordinatePower ι
  quadratic := QuadraticMap.pi fun _ : ι ↦ A.quadratic
  polar_eq_pairing' x y := by
    rw [QuadraticMap.Ring.polar_pi, FiniteBilinearModule.coordinatePower_pairing]
    exact Finset.sum_congr rfl fun i _ ↦ A.polar_eq_pairing (x i) (y i)

/-- The quadratic value on a coordinate power is the sum of the coordinate quadratic values. -/
theorem coordinatePower_quadratic (ι : Type v) [Fintype ι] (x : ι → A) :
    (A.coordinatePower ι).quadratic x = ∑ i, A.quadratic (x i) := by
  exact QuadraticMap.pi_apply _ _

/-- The pairing on a quadratic coordinate power is the sum of the coordinate polar pairings. -/
theorem coordinatePower_pairing (ι : Type v) [Fintype ι] (x y : ι → A) :
    (A.coordinatePower ι).toFiniteBilinearModule.pairing x y =
      ∑ i, A.toFiniteBilinearModule.pairing (x i) (y i) :=
  (rfl)

/-- Forgetting the quadratic map from a coordinate power gives the coordinate power of the polar
finite bilinear module. -/
@[simp]
theorem coordinatePower_toFiniteBilinearModule (ι : Type v) [Fintype ι] :
    (A.coordinatePower ι).toFiniteBilinearModule =
      A.toFiniteBilinearModule.coordinatePower ι :=
  (rfl)

/-- A coordinate power of a nondegenerate finite quadratic module is nondegenerate. -/
theorem IsNondegenerate.coordinatePower {A : FiniteQuadraticModule.{u}} (hA : A.IsNondegenerate)
    (ι : Type v) [Fintype ι] : (A.coordinatePower ι).IsNondegenerate :=
  FiniteBilinearModule.IsNondegenerate.coordinatePower hA ι

/-- A subgroup of a quadratic coordinate power is isotropic exactly when the sum of the
coordinate quadratic values vanishes on every one of its words. -/
@[simp]
theorem isIsotropic_coordinatePower_iff (ι : Type v) [Fintype ι]
    (C : AddSubgroup (ι → A)) :
    (A.coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, ∑ i, A.quadratic (x i) = 0 := by
  rw [(A.coordinatePower ι).isIsotropic_def]
  simp only [A.coordinatePower_quadratic]

section Isometry

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{w}}

/-- An isometry of finite quadratic alphabets induces an isometry on every finite coordinate
power by acting coordinatewise. -/
def Isometry.coordinatePower (f : Isometry A B) (ι : Type v) [Fintype ι] :
    Isometry (A.coordinatePower ι) (B.coordinatePower ι) :=
  QuadraticMap.IsometryEquiv.pi fun _ ↦ f

/-- A coordinatewise quadratic-module isometry acts at each coordinate by the alphabet
isometry. -/
@[simp]
theorem Isometry.coordinatePower_apply (f : Isometry A B) (ι : Type v) [Fintype ι]
    (x : ι → A) (i : ι) : f.coordinatePower ι x i = f (x i) :=
  (rfl)

/-- Forgetting the quadratic data from a coordinatewise isometry gives the corresponding
coordinatewise bilinear isometry. -/
@[simp]
theorem Isometry.coordinatePower_toFiniteBilinearModule (f : Isometry A B)
    (ι : Type v) [Fintype ι] :
    (f.coordinatePower ι).toFiniteBilinearModule =
      f.toFiniteBilinearModule.coordinatePower ι := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  ext x i
  have hleft : ((f.coordinatePower ι).toAddEquiv x) i = (f.coordinatePower ι x) i :=
    congrFun (congrFun
      (QuadraticMap.IsometryEquiv.coe_toLinearEquiv (f.coordinatePower ι)) x) i
  have hf : f.toFiniteBilinearModule (x i) = f (x i) :=
    congrArg (fun g : A ≃+ B ↦ g (x i)) (Isometry.toFiniteBilinearModule_toAddEquiv f)
  calc
    ((f.coordinatePower ι).toFiniteBilinearModule.toAddEquiv x) i =
        (f.coordinatePower ι x) i := by
      rw [Isometry.toFiniteBilinearModule_toAddEquiv]
      exact hleft
    _ = f (x i) := Isometry.coordinatePower_apply f ι x i
    _ = f.toFiniteBilinearModule (x i) := hf.symm
    _ = (f.toFiniteBilinearModule.coordinatePower ι x) i :=
      (FiniteBilinearModule.Isometry.coordinatePower_apply f.toFiniteBilinearModule ι x i).symm
    _ = ((f.toFiniteBilinearModule.coordinatePower ι).toAddEquiv x) i := (rfl)

end Isometry

end FiniteQuadraticModule

end TauCeti
