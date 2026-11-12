/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.LowDimTopology.Plumbing.Cube.Face.Exponent
public import TauCeti.LowDimTopology.Plumbing.Cube.Orientation

/-!
# The oriented lattice-homology differential over `R[U]`

This file constructs Némethi's oriented cubical differential of a plumbing lattice with
coefficients in `R[U]`, for an arbitrary commutative ring `R`; the case `R = ℤ` is lattice
homology over `ℤ[U]`. Order the vertices of the plumbing graph linearly. For a cube `(x, S)` and a
direction `v ∈ S` in position `i` of `S` listed in increasing order (counting from one), the
differential has the term

`(-1) ^ i (U ^ a_v (x, S \ v) - U ^ b_v (x + E_v, S \ v))`,

where `a_v` and `b_v` are the drops from the characteristic weight of the cube to the weights of
its lower and upper faces in direction `v`.

Applying the differential twice produces, for every ordered pair `(v, w)` of distinct directions,
the four codimension-two faces of the square they span. Reversing the pair reaches the same four
faces with the same `U`-exponents, by the commuting-face and exponent-square lemmas, but with the
opposite sign: removing the smaller of the two directions first lowers the position of the larger
one by one, while removing the larger one first leaves the position of the smaller one unchanged
(`PlumbingCube.neg_one_pow_directionIndex_add_eraseDirection_eq_neg`). So the terms cancel in pairs
and the differential squares to zero over every coefficient ring
(`PlumbingGraph.signedLatticeDifferential_comp_self`).

The construction is natural in the coefficient ring: a ring homomorphism `R →+* S`, applied to
all coefficients, intertwines the two differentials
(`PlumbingGraph.signedLatticeDifferential_mapRange`). In characteristic two the signs disappear,
and the differential over `𝔽₂[U]` is the unsigned one of
`TauCeti.LowDimTopology.Plumbing.Differential`.

The positions of directions and their sign rule are in
`TauCeti.LowDimTopology.Plumbing.Cube.Orientation`.

## Main definitions

* `TauCeti.PlumbingGraph.signedLatticeDifferentialOnGenerator`: the oriented weighted boundary of
  one cube.
* `TauCeti.PlumbingGraph.signedLatticeDifferential`: the `R[U]`-linear oriented lattice
  differential.

## Main results

* `TauCeti.PlumbingGraph.signedLatticeDifferential_single`: the differential on a basis cube.
* `TauCeti.PlumbingGraph.signedLatticeDifferential_comp_self`: the oriented lattice differential
  squares to zero.
* `TauCeti.PlumbingGraph.signedLatticeDifferential_mapRange`: naturality in the coefficient ring.

## References

The oriented cubical differential is that of A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3, in its homological form over
`ℤ[U]`.
-/

public section

open Polynomial

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [LinearOrder V] [Fintype V] (R : Type*) [CommRing R]

/-- The oriented lattice differential of one plumbing-cube generator over `R[U]`.

For every direction `v` of the cube, in position `i`, this is `(-1) ^ i` times the lower face
minus the upper face, each weighted by the drop in characteristic cube weight. -/
noncomputable def signedLatticeDifferentialOnGenerator
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    PlumbingCube V →₀ R[X] :=
  C.directions.attach.sum fun v =>
    (-1 : R[X]) ^ C.directionIndex v •
      (Finsupp.single (C.lowerFace v v.property)
          (X ^ PlumbingCube.characteristicLowerFaceExponent P k C v) -
        Finsupp.single (C.upperFace v v.property)
          (X ^ PlumbingCube.characteristicUpperFaceExponent P k C v.property))

/-- The defining oriented face-sum formula for the generator differential. -/
theorem signedLatticeDifferentialOnGenerator_def
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    P.signedLatticeDifferentialOnGenerator R k C =
      C.directions.attach.sum fun v =>
        (-1 : R[X]) ^ C.directionIndex v •
          (Finsupp.single (C.lowerFace v v.property)
              (X ^ PlumbingCube.characteristicLowerFaceExponent P k C v) -
            Finsupp.single (C.upperFace v v.property)
              (X ^ PlumbingCube.characteristicUpperFaceExponent P k C v.property)) :=
  by rw [signedLatticeDifferentialOnGenerator]

/-- The `R[U]`-linear oriented lattice differential on plumbing chains with coefficients in
`R[U]`. -/
noncomputable def signedLatticeDifferential
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (PlumbingCube V →₀ R[X]) →ₗ[R[X]] PlumbingCube V →₀ R[X] :=
  Finsupp.linearCombination R[X] (P.signedLatticeDifferentialOnGenerator R k)

/-- The oriented lattice differential sends a single cube with coefficient `a` to `a` times its
oriented weighted sum of codimension-one faces. -/
@[simp]
theorem signedLatticeDifferential_single
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) (a : R[X]) :
    P.signedLatticeDifferential R k (Finsupp.single C a) =
      a • P.signedLatticeDifferentialOnGenerator R k C := by
  rw [signedLatticeDifferential, Finsupp.linearCombination_single]

/-- The oriented lattice differential is the finite linear combination of its values on the
generators in the support of a chain. -/
theorem signedLatticeDifferential_apply
    (P : PlumbingGraph V) (k : P.characteristicVectors) (c : PlumbingCube V →₀ R[X]) :
    P.signedLatticeDifferential R k c =
      c.sum fun C a => a • P.signedLatticeDifferentialOnGenerator R k C := by
  rw [signedLatticeDifferential, Finsupp.linearCombination_apply]

/-! ### Cancellation around codimension-two faces -/

/-- Reindex the directions of a lower face by the ambient directions other than the removed
one. -/
private def lowerFaceDirectionEquiv (C : PlumbingCube V) (v : V)
    (hv : v ∈ C.directions) :
    (C.lowerFace v hv).directions ≃ C.directions.erase v where
  toFun w := ⟨w, by simpa using w.property⟩
  invFun w := ⟨w, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex the directions of an upper face by the ambient directions other than the removed
one. -/
private def upperFaceDirectionEquiv (C : PlumbingCube V) (v : V)
    (hv : v ∈ C.directions) :
    (C.upperFace v hv).directions ≃ C.directions.erase v where
  toFun w := ⟨w, by simpa using w.property⟩
  invFun w := ⟨w, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identify a direction followed by a remaining direction with an ordered pair of distinct
ambient directions. -/
private def directionPairEquiv (C : PlumbingCube V) :
    (Σ v : C.directions, C.directions.erase v) ≃ C.directions.offDiag where
  toFun p :=
    ⟨(p.1, p.2), Finset.mem_offDiag.mpr
      ⟨p.1.property, Finset.mem_of_mem_erase p.2.property,
        (Finset.ne_of_mem_erase p.2.property).symm⟩⟩
  invFun p :=
    ⟨⟨p.1.1, (Finset.mem_offDiag.mp p.property).1⟩,
      ⟨p.1.2, Finset.mem_erase_of_ne_of_mem
        (Finset.mem_offDiag.mp p.property).2.2.symm
        (Finset.mem_offDiag.mp p.property).2.1⟩⟩
  left_inv p := by
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := p
    rfl
  right_inv p := by
    obtain ⟨⟨v, w⟩, hp⟩ := p
    rfl

/-- The four terms obtained by taking two faces in the ordered pair of distinct directions
recorded by `p`, before the sign of the pair: lower-lower and upper-upper with sign `+`, the two
mixed corners with sign `-`. -/
private noncomputable def latticeTwoDirectionFaces
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V)
    (p : {p // p ∈ C.directions.offDiag}) : PlumbingCube V →₀ R[X] :=
  let v := p.1.1
  let w := p.1.2
  let hp := Finset.mem_offDiag.mp p.2
  let hv := hp.1
  let hw := hp.2.1
  let hvw := hp.2.2
  let hwLower : w ∈ (C.lowerFace v hv).directions := by
    rw [PlumbingCube.lowerFace_directions]
    exact Finset.mem_erase_of_ne_of_mem hvw.symm hw
  let hwUpper : w ∈ (C.upperFace v hv).directions := by
    rw [PlumbingCube.upperFace_directions]
    exact Finset.mem_erase_of_ne_of_mem hvw.symm hw
  Finsupp.single ((C.lowerFace v hv).lowerFace w hwLower)
      (X ^ (PlumbingCube.characteristicLowerFaceExponent P k C v +
        PlumbingCube.characteristicLowerFaceExponent P k (C.lowerFace v hv) w)) -
    Finsupp.single ((C.lowerFace v hv).upperFace w hwLower)
      (X ^ (PlumbingCube.characteristicLowerFaceExponent P k C v +
        PlumbingCube.characteristicUpperFaceExponent P k (C.lowerFace v hv) hwLower)) -
    Finsupp.single ((C.upperFace v hv).lowerFace w hwUpper)
      (X ^ (PlumbingCube.characteristicUpperFaceExponent P k C hv +
        PlumbingCube.characteristicLowerFaceExponent P k (C.upperFace v hv) w)) +
    Finsupp.single ((C.upperFace v hv).upperFace w hwUpper)
      (X ^ (PlumbingCube.characteristicUpperFaceExponent P k C hv +
        PlumbingCube.characteristicUpperFaceExponent P k (C.upperFace v hv) hwUpper))

/-- The sign of an ordered pair of distinct directions: the product of the position signs of
the first direction in the cube and of the second one in the face. -/
private def directionPairSign (C : PlumbingCube V) (p : {p // p ∈ C.directions.offDiag}) :
    ℕ :=
  C.directionIndex p.1.1 + (C.eraseDirection p.1.1).directionIndex p.1.2

/-- Reversing an ordered off-diagonal pair of cube directions. -/
private def swapOffDiag (C : PlumbingCube V)
    (p : {p // p ∈ C.directions.offDiag}) :
    {p // p ∈ C.directions.offDiag} :=
  ⟨p.1.swap, by
    have hp := Finset.mem_offDiag.mp p.property
    exact Finset.mem_offDiag.mpr ⟨hp.2.1, hp.1, hp.2.2.symm⟩⟩

/-- Both paths to the lower-lower corner of the square spanned by `v` and `w` give the same
weighted generator. -/
private theorem single_lowerFace_lowerFace_swap
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) {v w : V}
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hvw : v ≠ w) :
    Finsupp.single ((C.lowerFace v hv).lowerFace w
        (by rw [PlumbingCube.lowerFace_directions]
            exact Finset.mem_erase_of_ne_of_mem hvw.symm hw))
      (X ^ (PlumbingCube.characteristicLowerFaceExponent P k C v +
        PlumbingCube.characteristicLowerFaceExponent P k (C.lowerFace v hv) w) : R[X]) =
    Finsupp.single ((C.lowerFace w hw).lowerFace v
        (by rw [PlumbingCube.lowerFace_directions]; exact Finset.mem_erase_of_ne_of_mem hvw hv))
      (X ^ (PlumbingCube.characteristicLowerFaceExponent P k C w +
        PlumbingCube.characteristicLowerFaceExponent P k (C.lowerFace w hw) v)) := by
  rw [C.lowerFace_lowerFace_comm hv hw hvw,
    PlumbingCube.characteristicLowerFaceExponent_add_lowerFace_comm P k C hv hw hvw]

/-- Both paths to the upper-upper corner of the square spanned by `v` and `w` give the same
weighted generator. -/
private theorem single_upperFace_upperFace_swap
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) {v w : V}
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hvw : v ≠ w) :
    Finsupp.single ((C.upperFace v hv).upperFace w
        (by rw [PlumbingCube.upperFace_directions]
            exact Finset.mem_erase_of_ne_of_mem hvw.symm hw))
      (X ^ (PlumbingCube.characteristicUpperFaceExponent P k C hv +
        PlumbingCube.characteristicUpperFaceExponent P k (C.upperFace v hv)
          (by rw [PlumbingCube.upperFace_directions]
              exact Finset.mem_erase_of_ne_of_mem hvw.symm hw)) : R[X]) =
    Finsupp.single ((C.upperFace w hw).upperFace v
        (by rw [PlumbingCube.upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hvw hv))
      (X ^ (PlumbingCube.characteristicUpperFaceExponent P k C hw +
        PlumbingCube.characteristicUpperFaceExponent P k (C.upperFace w hw)
          (by rw [PlumbingCube.upperFace_directions]
              exact Finset.mem_erase_of_ne_of_mem hvw hv))) := by
  rw [C.upperFace_upperFace_comm hv hw hvw,
    PlumbingCube.characteristicUpperFaceExponent_add_upperFace_comm P k C hv hw hvw]

/-- The lower-then-upper path and the upper-then-lower path to the mixed corner of the square
spanned by `v` and `w` give the same weighted generator. -/
private theorem single_lowerFace_upperFace_eq_single_upperFace_lowerFace
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) {v w : V}
    (hv : v ∈ C.directions) (hw : w ∈ C.directions) (hvw : v ≠ w) :
    Finsupp.single ((C.lowerFace v hv).upperFace w
        (by rw [PlumbingCube.lowerFace_directions]
            exact Finset.mem_erase_of_ne_of_mem hvw.symm hw))
      (X ^ (PlumbingCube.characteristicLowerFaceExponent P k C v +
        PlumbingCube.characteristicUpperFaceExponent P k (C.lowerFace v hv)
          (by rw [PlumbingCube.lowerFace_directions]
              exact Finset.mem_erase_of_ne_of_mem hvw.symm hw)) : R[X]) =
    Finsupp.single ((C.upperFace w hw).lowerFace v
        (by rw [PlumbingCube.upperFace_directions]; exact Finset.mem_erase_of_ne_of_mem hvw hv))
      (X ^ (PlumbingCube.characteristicUpperFaceExponent P k C hw +
        PlumbingCube.characteristicLowerFaceExponent P k (C.upperFace w hw) v)) := by
  rw [C.lowerFace_upperFace_comm hv hw hvw,
    PlumbingCube.characteristicLowerFaceExponent_add_upperFace_comm P k C hv hw hvw]

/-- Reversing the two directions leaves the four faces and their `U`-exponents unchanged. The
lower-lower and upper-upper terms match their counterparts, while the two mixed terms are
exchanged. -/
private theorem latticeTwoDirectionFaces_swap
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V)
    (p : {p // p ∈ C.directions.offDiag}) :
    latticeTwoDirectionFaces R P k C (swapOffDiag C p) =
      latticeTwoDirectionFaces R P k C p := by
  obtain ⟨⟨v, w⟩, hp⟩ := p
  rw [Finset.mem_offDiag] at hp
  obtain ⟨hv, hw, hvw⟩ := hp
  simp only [latticeTwoDirectionFaces, swapOffDiag, Prod.swap_prod_mk]
  rw [single_lowerFace_lowerFace_swap R P k C hw hv hvw.symm,
    single_upperFace_upperFace_swap R P k C hw hv hvw.symm,
    single_lowerFace_upperFace_eq_single_upperFace_lowerFace R P k C hw hv hvw.symm,
    ← single_lowerFace_upperFace_eq_single_upperFace_lowerFace R P k C hv hw hvw]
  abel

omit [Fintype V] in
/-- Reversing the two directions reverses the sign of the pair. -/
private theorem neg_one_pow_directionPairSign_swap (C : PlumbingCube V)
    (p : {p // p ∈ C.directions.offDiag}) :
    (-1 : R[X]) ^ directionPairSign C (swapOffDiag C p) =
      -(-1 : R[X]) ^ directionPairSign C p := by
  obtain ⟨⟨v, w⟩, hp⟩ := p
  rw [Finset.mem_offDiag] at hp
  obtain ⟨hv, hw, hvw⟩ := hp
  simp only [directionPairSign, swapOffDiag, Prod.swap_prod_mk]
  exact C.neg_one_pow_directionIndex_add_eraseDirection_eq_neg R[X] hw hv hvw.symm

/-- The signed contributions over ordered pairs of distinct directions cancel: pair `(v, w)`
with `(w, v)`. -/
private theorem sum_latticeTwoDirectionFaces_eq_zero
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    C.directions.offDiag.attach.sum
        (fun p => (-1 : R[X]) ^ directionPairSign C p • latticeTwoDirectionFaces R P k C p) =
      0 := by
  apply Finset.sum_involution (fun p _ => swapOffDiag C p)
  · intro p _
    rw [latticeTwoDirectionFaces_swap, neg_one_pow_directionPairSign_swap, neg_smul,
      add_neg_cancel]
  · intro p _ _
    have hp := Finset.mem_offDiag.mp p.property
    intro h
    have hval := congrArg Subtype.val h
    exact hp.2.2 (congrArg Prod.fst hval).symm
  · intro p _
    simp [swapOffDiag]
  · intro p _
    apply Subtype.ext
    exact Prod.swap_swap p.1

/-- Expanding the differential twice on a cube gives the signed sum of the four-face
contributions over ordered pairs of distinct directions. -/
private theorem signedLatticeDifferential_signedLatticeDifferentialOnGenerator_eq_sum
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    P.signedLatticeDifferential R k (P.signedLatticeDifferentialOnGenerator R k C) =
      C.directions.offDiag.attach.sum
        (fun p => (-1 : R[X]) ^ directionPairSign C p • latticeTwoDirectionFaces R P k C p) := by
  rw [signedLatticeDifferentialOnGenerator, map_sum]
  simp_rw [map_smul, map_sub, signedLatticeDifferential_single]
  simp_rw [signedLatticeDifferentialOnGenerator]
  trans C.directions.attach.sum fun v =>
    (C.directions.erase v).attach.sum fun w =>
      (-1 : R[X]) ^ directionPairSign C
          ⟨(v, w), Finset.mem_offDiag.mpr
            ⟨v.property, Finset.mem_of_mem_erase w.property,
              (Finset.ne_of_mem_erase w.property).symm⟩⟩ •
        latticeTwoDirectionFaces R P k C
          ⟨(v, w), Finset.mem_offDiag.mpr
            ⟨v.property, Finset.mem_of_mem_erase w.property,
              (Finset.ne_of_mem_erase w.property).symm⟩⟩
  · apply Finset.sum_congr rfl
    intro v _
    simp only [Finset.attach_eq_univ]
    let lowerEquiv := lowerFaceDirectionEquiv C v v.property
    let upperEquiv := upperFaceDirectionEquiv C v v.property
    rw [← lowerEquiv.symm.sum_comp, ← upperEquiv.symm.sum_comp]
    simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    simp only [latticeTwoDirectionFaces, directionPairSign, lowerEquiv, upperEquiv,
      lowerFaceDirectionEquiv, upperFaceDirectionEquiv, Equiv.coe_fn_symm_mk,
      PlumbingCube.directionIndex_lowerFace, PlumbingCube.directionIndex_upperFace,
      smul_add, smul_sub, Finsupp.smul_single, smul_eq_mul, pow_add, mul_assoc,
      mul_left_comm (X ^ _ : R[X])]
    abel
  · simp only [Finset.attach_eq_univ]
    rw [← Fintype.sum_sigma']
    exact (directionPairEquiv C).sum_comp
      (fun p => (-1 : R[X]) ^ directionPairSign C p • latticeTwoDirectionFaces R P k C p)

/-- The oriented differential of the weighted boundary of a single plumbing cube vanishes. -/
@[simp]
theorem signedLatticeDifferential_signedLatticeDifferentialOnGenerator_eq_zero
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    P.signedLatticeDifferential R k (P.signedLatticeDifferentialOnGenerator R k C) = 0 := by
  rw [signedLatticeDifferential_signedLatticeDifferentialOnGenerator_eq_sum,
    sum_latticeTwoDirectionFaces_eq_zero]

/-- The oriented lattice differential squares to zero. -/
theorem signedLatticeDifferential_comp_self
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.signedLatticeDifferential R k).comp (P.signedLatticeDifferential R k) = 0 := by
  refine Finsupp.lhom_ext' fun C => LinearMap.ext_ring ?_
  simp [LinearMap.comp_apply]

/-! ### Change of coefficients -/

section ChangeOfCoefficients

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

/-- Applying a ring homomorphism to the coefficients of the oriented boundary of a cube gives its
oriented boundary over the target ring. -/
@[simp]
theorem mapRange_signedLatticeDifferentialOnGenerator
    (P : PlumbingGraph V) (k : P.characteristicVectors) (C : PlumbingCube V) :
    Finsupp.mapRange (Polynomial.map f) (Polynomial.map_zero f)
        (P.signedLatticeDifferentialOnGenerator R k C) =
      P.signedLatticeDifferentialOnGenerator S k C := by
  classical
  refine Finsupp.ext fun D => ?_
  simp only [Finsupp.mapRange_apply, signedLatticeDifferentialOnGenerator_def,
    Finsupp.finsetSum_apply, Polynomial.map_sum, Finsupp.smul_apply, Finsupp.sub_apply,
    smul_eq_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one, Finsupp.single_apply, apply_ite (Polynomial.map f), Polynomial.map_X,
    Polynomial.map_zero]

/-- Applying a ring homomorphism to all coefficients intertwines the oriented lattice
differentials over the two coefficient rings. In particular the oriented complex over `ℤ[U]`
reduces modulo two to the oriented complex over `𝔽₂[U]`. -/
@[simp]
theorem signedLatticeDifferential_mapRange
    (P : PlumbingGraph V) (k : P.characteristicVectors) (c : PlumbingCube V →₀ R[X]) :
    P.signedLatticeDifferential S k
        (Finsupp.mapRange (Polynomial.map f) (Polynomial.map_zero f) c) =
      Finsupp.mapRange (Polynomial.map f) (Polynomial.map_zero f)
        (P.signedLatticeDifferential R k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [Finsupp.mapRange_add (fun _ _ => Polynomial.map_add f), map_add, hc, hd, map_add,
      Finsupp.mapRange_add (fun _ _ => Polynomial.map_add f)]
  | single C a =>
    rw [Finsupp.mapRange_single, signedLatticeDifferential_single,
      signedLatticeDifferential_single, Finsupp.mapRange_smul' a (Polynomial.map f a) _
        (fun x => Polynomial.map_mul f), mapRange_signedLatticeDifferentialOnGenerator]

end ChangeOfCoefficients

end PlumbingGraph

end TauCeti
