/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The symplectic root subgroups and their underlying transvection formulas are used below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic

/-!
# Weyl elements in the standard symplectic group

For distinct coordinate indices `i` and `j`, this file constructs the standard representative

```text
n_{i,j} = x_{e_i-e_j}(1) x_{e_j-e_i}(-1) x_{e_i-e_j}(1)
```

of the Weyl reflection exchanging `i` and `j`. It also constructs the long-root representative
`n_{2e_i}`, which exchanges the two symplectic coordinates belonging to `i`. Conjugation by these
representatives transports the root subgroups and acts on the paired diagonal torus by the
corresponding type-`C_m` reflections. These identities work over an arbitrary commutative ring, so
no division or characteristic restriction is needed.

The short-root representatives permute torus coordinates, while the long-root representatives
invert individual coordinates. Together these give the permutation and sign-change generators of
the signed permutation group, the Weyl group of the standard symplectic torus.

## Main definitions and results

* `TauCeti.GLSymplecticFin.differenceShortRootWeylElement`: the standard representative of the
  reflection in `e_i-e_j`.
* `TauCeti.GLSymplecticFin.positiveLongRootWeylElement` and
  `TauCeti.GLSymplecticFin.negativeLongRootWeylElement`: the two opposite representatives of the
  reflection in `2e_i`.
* `positiveLongRootWeylElement_mul_diagonal_mul_inv`: the long-root reflection inverts one
  diagonal-torus coordinate.
* `positiveLongRootWeylElement_mem_normalizer_diagonalTorus` and
  `negativeLongRootWeylElement_mem_normalizer_diagonalTorus`: both long-root representatives belong
  to the normalizer of the paired diagonal torus.
* `differenceShortRootWeylElement_mem`: a subgroup containing the two difference-root elements
  forming a Weyl word contains the corresponding Weyl representative.
* `coe_differenceShortRootWeylElement`: in sum coordinates it is a product of two type-`A` Weyl
  representatives.
* `differenceShortRootWeylElement_inv`: the representative for the opposite root is its inverse.
* `differenceShortRootWeylElement_mul_differenceShortRootUnit_mul_inv`: its reflection action on
  the short-root subgroup.
* `differenceShortRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv`: it
  transports `x_{2e_j}(c)` to `x_{2e_i}(c)`.
* `differenceShortRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv`:
  the corresponding transport of `x_{-2e_j}(c)`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §3.

Both the short-root and the long-root representatives follow the Chevalley Weyl-word
construction `n_α = x_α(1) x_{-α}(-1) x_α(1)` of these references.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u v

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- The standard representative of the Weyl reflection in the short root `e_i-e_j`:
`x_{e_i-e_j}(1) x_{e_j-e_i}(-1) x_{e_i-e_j}(1)`. -/
def differenceShortRootWeylElement (hij : i ≠ j) : GLSymplecticFin m R :=
  differenceShortRootUnit hij 1 * differenceShortRootUnit hij.symm (-1) *
    differenceShortRootUnit hij 1

/-- A subgroup containing the two difference-root elements forming a Weyl word contains the
corresponding Weyl reflection representative. -/
theorem differenceShortRootWeylElement_mem (H : Subgroup (GLSymplecticFin m R))
    (hij : i ≠ j) (hforward : differenceShortRootUnit hij 1 ∈ H)
    (hbackward : differenceShortRootUnit hij.symm (-1) ∈ H) :
    differenceShortRootWeylElement hij ∈ H := by
  rw [differenceShortRootWeylElement]
  exact H.mul_mem (H.mul_mem hforward hbackward) hforward

/-- In sum coordinates the short-root Weyl representative is the product of the type-`A` Weyl
representative on the first block and the inverse of the one on the second block. -/
@[simp]
theorem coe_differenceShortRootWeylElement (hij : i ≠ j) :
    ((differenceShortRootWeylElement (R := R) hij : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      TauCeti.transvectionWeylElement (differenceShortRoot_first_indices_ne hij) *
        (TauCeti.transvectionWeylElement
          (differenceShortRoot_second_indices_ne hij))⁻¹ := by
  -- The inverse of the second block's Weyl word is that word with opposite parameters.
  have hinv : (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_second_indices_ne hij))⁻¹ =
        TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1) *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm 1 *
          TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1) := by
    simp [TauCeti.transvectionWeylElement_def, _root_.mul_inv_rev, mul_assoc]
  rw [differenceShortRootWeylElement, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_differenceShortRootUnit, coe_differenceShortRootUnit (hij := hij.symm),
    hinv, TauCeti.transvectionWeylElement_def]
  simp only [neg_neg]
  let a := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R)
  let b := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R)
  let c := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-1 : R)
  let d := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm (1 : R)
  -- Fold the four transvections so that only their three cross-commutations remain visible;
  -- the `Ne` proof arguments for `hij.symm` are identified here by proof irrelevance.
  change (a * c) * (b * d) * (a * c) = (a * b * a) * (c * d * c)
  have hac : Commute a c := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inr_ne_inl i i) 1 (-1)
  have had : Commute a d := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inr_ne_inl j i) 1 1
  have hbc : Commute b c := TauCeti.commute_transvectionUnit _ _
    (finSumFinEquiv_inl_ne_inr i j) (finSumFinEquiv_inr_ne_inl i j) (-1) (-1)
  calc
    (a * c) * (b * d) * (a * c) = a * (c * b) * d * a * c := by group
    _ = a * (b * c) * d * a * c := by rw [hbc.eq]
    _ = a * b * c * (d * a) * c := by group
    _ = a * b * c * (a * d) * c := by rw [had.eq]
    _ = a * b * (c * a) * d * c := by group
    _ = a * b * (a * c) * d * c := by rw [hac.eq]
    _ = (a * b * a) * (c * d * c) := by group

private theorem commute_differenceShortRootWeylElements (hij : i ≠ j) : Commute
    (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_first_indices_ne hij))
    (TauCeti.transvectionWeylElement (A := R)
      (differenceShortRoot_second_indices_ne hij)) := by
  have houter : Commute
      (TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) (1 : R))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij)) :=
    TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij)
      (differenceShortRoot_first_indices_ne hij)
      (finSumFinEquiv_inr_ne_inl i i) (finSumFinEquiv_inl_ne_inr j j)
      (finSumFinEquiv_inr_ne_inl j i) (finSumFinEquiv_inl_ne_inr j i) 1
  have hmiddle : Commute
      (TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-1 : R))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij)) :=
    TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij)
      (differenceShortRoot_first_indices_ne hij).symm
      (finSumFinEquiv_inr_ne_inl i j) (finSumFinEquiv_inl_ne_inr i j)
      (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inl_ne_inr i i) (-1)
  rw [TauCeti.transvectionWeylElement_def]
  exact (houter.mul_left hmiddle).mul_left houter

/-- The inverse of the Weyl representative for `e_i-e_j` is the representative for the
opposite root `e_j-e_i`. -/
@[simp]
theorem differenceShortRootWeylElement_inv (hij : i ≠ j) :
    (differenceShortRootWeylElement (R := R) hij)⁻¹ =
      differenceShortRootWeylElement hij.symm := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_differenceShortRootWeylElement (R := R) hij.symm]
  rw [← TauCeti.transvectionWeylElement_inv
    (differenceShortRoot_first_indices_ne hij),
    TauCeti.transvectionWeylElement_inv
      (differenceShortRoot_second_indices_ne hij.symm)]
  rw [_root_.mul_inv_rev, inv_inv]
  exact (commute_differenceShortRootWeylElements (R := R) hij).inv_left.eq.symm

/-- Conjugation by the Weyl representative for `e_i-e_j` sends its short-root subgroup to
the opposite short-root subgroup and negates the parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_differenceShortRootUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * differenceShortRootUnit hij c *
        differenceShortRootWeylElement hij.symm =
      differenceShortRootUnit hij.symm (-c) := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_differenceShortRootUnit, coe_differenceShortRootUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  simp only [neg_neg]
  set left := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_first_indices_ne hij)
  set right := TauCeti.transvectionWeylElement (A := R)
    (differenceShortRoot_second_indices_ne hij).symm
  set x := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij) c
  set y := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij) (-c)
  set u := TauCeti.transvectionUnit (differenceShortRoot_first_indices_ne hij).symm (-c)
  set v := TauCeti.transvectionUnit (differenceShortRoot_second_indices_ne hij).symm c
  have hleft : left * x * left⁻¹ = u :=
    by simpa only [left, x, u, TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_self
        (differenceShortRoot_first_indices_ne hij) c
  have hright : right * y * right⁻¹ = v :=
    by simpa only [right, y, v, TauCeti.transvectionWeylElement_inv, neg_neg] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_symm
        (differenceShortRoot_second_indices_ne hij).symm (-c)
  have hright_x : Commute right x :=
    (TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_second_indices_ne hij).symm
      (differenceShortRoot_first_indices_ne hij)
      (finSumFinEquiv_inr_ne_inl j i) (finSumFinEquiv_inl_ne_inr j i)
      (finSumFinEquiv_inr_ne_inl i i) (finSumFinEquiv_inl_ne_inr j j) c).symm
  have hleft_v : Commute left v :=
    (TauCeti.commute_transvectionUnit_transvectionWeylElement
      (differenceShortRoot_first_indices_ne hij)
      (differenceShortRoot_second_indices_ne hij).symm
      (finSumFinEquiv_inl_ne_inr j i) (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inl_ne_inr i i) (finSumFinEquiv_inr_ne_inl j j) c).symm
  calc
    (left * right) * (x * y) * (left * right)⁻¹ =
        left * (right * x * right⁻¹) * (right * y * right⁻¹) * left⁻¹ := by group
    _ = left * (x * v) * left⁻¹ := by
      rw [hright_x.mul_inv_cancel, hright]
      simp only [mul_assoc]
    _ = (left * x * left⁻¹) * (left * v * left⁻¹) := by group
    _ = u * v := by rw [hleft, hleft_v.mul_inv_cancel]

private theorem conjugate_crossBlockTransvectionByWeylPair
    {pi pj qi qj : Fin (m + m)} (hpij : pi ≠ pj) (hqij : qi ≠ qj)
    (hpjqj : pj ≠ qj) (hpjqi : pj ≠ qi) (hpiqi : pi ≠ qi) (c : R) :
    (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij) *
        TauCeti.transvectionUnit hpjqj c *
        (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij)⁻¹ =
      TauCeti.transvectionUnit hpiqi c := by
  have hright :
      TauCeti.transvectionWeylElement hqij * TauCeti.transvectionUnit hpjqj c *
          (TauCeti.transvectionWeylElement hqij)⁻¹ =
        TauCeti.transvectionUnit hpjqi c := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_right
        hqij hpjqj hpjqi c
  have hleft :
      TauCeti.transvectionWeylElement hpij * TauCeti.transvectionUnit hpjqi c *
          (TauCeti.transvectionWeylElement hpij)⁻¹ =
        TauCeti.transvectionUnit hpiqi c := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_left
        hpij hpjqi hpiqi c
  calc
    (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij) *
          TauCeti.transvectionUnit hpjqj c *
          (TauCeti.transvectionWeylElement hpij * TauCeti.transvectionWeylElement hqij)⁻¹ =
        TauCeti.transvectionWeylElement hpij *
          (TauCeti.transvectionWeylElement hqij * TauCeti.transvectionUnit hpjqj c *
            (TauCeti.transvectionWeylElement hqij)⁻¹) *
          (TauCeti.transvectionWeylElement hpij)⁻¹ := by group
    _ = TauCeti.transvectionUnit hpiqi c := by rw [hright, hleft]

/-- **A short-root Weyl element transports positive long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{2e_j}(c)` to `x_{2e_i}(c)`, with no change of parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * positiveLongRootTransvectionUnit j c *
        differenceShortRootWeylElement hij.symm =
      positiveLongRootTransvectionUnit i c := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_positiveLongRootTransvectionUnit, coe_positiveLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  exact conjugate_crossBlockTransvectionByWeylPair
    (differenceShortRoot_first_indices_ne hij)
    (differenceShortRoot_second_indices_ne hij).symm
    (finSumFinEquiv_inl_ne_inr j j) (finSumFinEquiv_inl_ne_inr j i)
    (finSumFinEquiv_inl_ne_inr i i) c

/-- **A short-root Weyl element transports negative long roots.** Conjugation by the reflection
representative for `e_i-e_j` sends `x_{-2e_j}(c)` to `x_{-2e_i}(c)`, with no change of parameter. -/
@[simp]
theorem differenceShortRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv
    (hij : i ≠ j) (c : R) :
    differenceShortRootWeylElement hij * negativeLongRootTransvectionUnit j c *
        differenceShortRootWeylElement hij.symm =
      negativeLongRootTransvectionUnit i c := by
  rw [← differenceShortRootWeylElement_inv hij]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_differenceShortRootWeylElement (R := R) hij,
    coe_negativeLongRootTransvectionUnit, coe_negativeLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  have hcomm : Commute
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_first_indices_ne hij))
      (TauCeti.transvectionWeylElement (A := R)
        (differenceShortRoot_second_indices_ne hij).symm) := by
    simpa only [TauCeti.transvectionWeylElement_inv] using
      (commute_differenceShortRootWeylElements (R := R) hij).inv_right
  rw [hcomm.eq]
  exact conjugate_crossBlockTransvectionByWeylPair
    (differenceShortRoot_second_indices_ne hij).symm
    (differenceShortRoot_first_indices_ne hij)
    (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inr_ne_inl j i)
    (finSumFinEquiv_inr_ne_inl i i) c

/-- Applying a ring homomorphism entrywise to a short-root Weyl element gives the corresponding
Weyl element over the target ring. -/
@[simp]
theorem map_differenceShortRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (hij : i ≠ j) :
    GLSymplecticFin.map m R f (differenceShortRootWeylElement hij) =
      differenceShortRootWeylElement hij := by
  simp [differenceShortRootWeylElement]

/-! ## Long-root reflections -/

/-- The standard representative of the reflection in the long root `2e_i`:
`x_{2e_i}(1) x_{-2e_i}(-1) x_{2e_i}(1)`. -/
def positiveLongRootWeylElement (i : Fin m) : GLSymplecticFin m R :=
  positiveLongRootTransvectionUnit i 1 * negativeLongRootTransvectionUnit i (-1) *
    positiveLongRootTransvectionUnit i 1

/-- The standard representative of the reflection in the opposite long root `-2e_i`:
`x_{-2e_i}(1) x_{2e_i}(-1) x_{-2e_i}(1)`. -/
def negativeLongRootWeylElement (i : Fin m) : GLSymplecticFin m R :=
  negativeLongRootTransvectionUnit i 1 * positiveLongRootTransvectionUnit i (-1) *
    negativeLongRootTransvectionUnit i 1

/-- A subgroup containing the two opposite long-root elements in the Weyl word contains the
positive long-root Weyl representative. -/
theorem positiveLongRootWeylElement_mem (H : Subgroup (GLSymplecticFin m R)) (i : Fin m)
    (hpositive : positiveLongRootTransvectionUnit i 1 ∈ H)
    (hnegative : negativeLongRootTransvectionUnit i (-1) ∈ H) :
    positiveLongRootWeylElement i ∈ H := by
  rw [positiveLongRootWeylElement]
  exact H.mul_mem (H.mul_mem hpositive hnegative) hpositive

/-- A subgroup containing the two opposite long-root elements in the Weyl word contains the
negative long-root Weyl representative. -/
theorem negativeLongRootWeylElement_mem (H : Subgroup (GLSymplecticFin m R)) (i : Fin m)
    (hnegative : negativeLongRootTransvectionUnit i 1 ∈ H)
    (hpositive : positiveLongRootTransvectionUnit i (-1) ∈ H) :
    negativeLongRootWeylElement i ∈ H := by
  rw [negativeLongRootWeylElement]
  exact H.mul_mem (H.mul_mem hnegative hpositive) hnegative

/-- The matrix underlying the positive long-root Weyl representative is the elementary Weyl
matrix exchanging the two symplectic coordinates belonging to `i`. -/
@[simp]
theorem coe_positiveLongRootWeylElement (i : Fin m) :
    ((positiveLongRootWeylElement (R := R) i : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      TauCeti.transvectionWeylElement (finSumFinEquiv_inl_ne_inr i i) := by
  rw [positiveLongRootWeylElement, TauCeti.transvectionWeylElement_def]
  simp

/-- The matrix underlying the negative long-root Weyl representative is the elementary Weyl
matrix for the opposite ordered pair of symplectic coordinates. -/
@[simp]
theorem coe_negativeLongRootWeylElement (i : Fin m) :
    ((negativeLongRootWeylElement (R := R) i : GLSymplecticFin m R) :
        GL (Fin (m + m)) R) =
      TauCeti.transvectionWeylElement (finSumFinEquiv_inr_ne_inl i i) := by
  rw [negativeLongRootWeylElement, TauCeti.transvectionWeylElement_def]
  simp

/-- The representative for the opposite long root is the inverse of the positive long-root
representative. -/
@[simp]
theorem positiveLongRootWeylElement_inv (i : Fin m) :
    (positiveLongRootWeylElement (R := R) i)⁻¹ = negativeLongRootWeylElement i := by
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_inv, Subgroup.coe_subtype, coe_positiveLongRootWeylElement,
    coe_negativeLongRootWeylElement, TauCeti.transvectionWeylElement_inv]

/-- The inverse of the negative long-root representative is the positive long-root
representative. -/
@[simp]
theorem negativeLongRootWeylElement_inv (i : Fin m) :
    (negativeLongRootWeylElement (R := R) i)⁻¹ = positiveLongRootWeylElement i := by
  rw [← positiveLongRootWeylElement_inv, inv_inv]

/-- Conjugation by the long-root Weyl representative exchanges the positive and negative long
root subgroups and negates the parameter. -/
@[simp]
theorem positiveLongRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv
    (i : Fin m) (c : R) :
    positiveLongRootWeylElement i * positiveLongRootTransvectionUnit i c *
        negativeLongRootWeylElement i =
      negativeLongRootTransvectionUnit i (-c) := by
  rw [← positiveLongRootWeylElement_inv]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_positiveLongRootWeylElement, coe_positiveLongRootTransvectionUnit,
    coe_negativeLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  exact TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_self
    (finSumFinEquiv_inl_ne_inr i i) c

/-- Conjugation by the long-root Weyl representative exchanges the negative and positive long
root subgroups and negates the parameter. -/
@[simp]
theorem positiveLongRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv
    (i : Fin m) (c : R) :
    positiveLongRootWeylElement i * negativeLongRootTransvectionUnit i c *
        negativeLongRootWeylElement i =
      positiveLongRootTransvectionUnit i (-c) := by
  rw [← positiveLongRootWeylElement_inv]
  apply (GLSymplecticFin m R).subtype_injective
  rw [map_mul, map_mul, map_inv, Subgroup.coe_subtype,
    coe_positiveLongRootWeylElement, coe_negativeLongRootTransvectionUnit,
    coe_positiveLongRootTransvectionUnit]
  rw [TauCeti.transvectionWeylElement_inv]
  exact TauCeti.transvectionWeylElement_mul_transvectionUnit_mul_inv_symm
    (finSumFinEquiv_inl_ne_inr i i) c

/-- Conjugation by the long-root Weyl representative inverts the corresponding coordinate of
the paired diagonal torus and fixes every other coordinate. -/
@[simp]
theorem positiveLongRootWeylElement_mul_diagonal_mul_inv
    (i : Fin m) (t : Fin m → Rˣ) :
    positiveLongRootWeylElement i * diagonal t * negativeLongRootWeylElement i =
      diagonal (Function.update t i (t i)⁻¹) := by
  rw [← positiveLongRootWeylElement_inv]
  apply (GLSymplecticFin m R).subtype_injective
  simp only [map_mul, map_inv, Subgroup.coe_subtype, coe_positiveLongRootWeylElement,
    coe_diagonal]
  rw [TauCeti.transvectionWeylElement_inv, TauCeti.transvectionWeylElement_mul_diagGL_mul_inv]
  congr 1
  funext a
  obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat]
    by_cases hai : a = i
    · subst a
      simp
    · have hleft : Fin.castAdd m a ≠ Fin.castAdd m i :=
        (Fin.castAdd_injective m m).ne hai
      have hright : Fin.castAdd m a ≠ i.addNat m := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using finSumFinEquiv_inl_ne_inr a i
      rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
      simp [Function.update_of_ne hai]
  · simp only [Function.comp_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat]
    by_cases hai : a = i
    · subst a
      simp
    · have hleft : a.addNat m ≠ Fin.castAdd m i := by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using finSumFinEquiv_inr_ne_inl a i
      have hright : a.addNat m ≠ i.addNat m := by
        simpa only [Fin.natAdd_eq_addNat] using (Fin.natAdd_injective m m).ne hai
      rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
      simp [Function.update_of_ne hai]

/-- Conjugation by the opposite long-root representative has the same reflection action on the
paired diagonal torus. -/
@[simp]
theorem negativeLongRootWeylElement_mul_diagonal_mul_inv
    (i : Fin m) (t : Fin m → Rˣ) :
    negativeLongRootWeylElement i * diagonal t * positiveLongRootWeylElement i =
      diagonal (Function.update t i (t i)⁻¹) := by
  have hu : Function.update (Function.update t i (t i)⁻¹) i
      ((Function.update t i (t i)⁻¹) i)⁻¹ = t := by
    simp
  have hconj := positiveLongRootWeylElement_mul_diagonal_mul_inv (R := R) i
    (Function.update t i (t i)⁻¹)
  rw [hu] at hconj
  rw [← positiveLongRootWeylElement_inv, ← hconj,
    ← positiveLongRootWeylElement_inv]
  group

/-- The long-root Weyl representative normalizes the paired diagonal torus. -/
theorem positiveLongRootWeylElement_mem_normalizer_diagonalTorus (i : Fin m) :
    positiveLongRootWeylElement (R := R) i ∈
      Subgroup.normalizer (diagonalTorus R m : Set (GLSymplecticFin m R)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rw [mem_diagonalTorus_iff_exists_diagonal]
    rintro ⟨t, rfl⟩
    rw [positiveLongRootWeylElement_inv,
      positiveLongRootWeylElement_mul_diagonal_mul_inv]
    rw [mem_diagonalTorus_iff_exists_diagonal]
    exact ⟨Function.update t i (t i)⁻¹, rfl⟩
  · intro hd
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagonal.mp hd
    have hback := negativeLongRootWeylElement_mul_diagonal_mul_inv (R := R) i t
    rw [← positiveLongRootWeylElement_inv, ht] at hback
    have heq : (positiveLongRootWeylElement i)⁻¹ *
        (positiveLongRootWeylElement i * d * (positiveLongRootWeylElement i)⁻¹) *
          positiveLongRootWeylElement i = d := by
      group
    rw [heq] at hback
    rw [mem_diagonalTorus_iff_exists_diagonal]
    exact ⟨Function.update t i (t i)⁻¹, hback.symm⟩

/-- The opposite long-root Weyl representative normalizes the paired diagonal torus. -/
theorem negativeLongRootWeylElement_mem_normalizer_diagonalTorus (i : Fin m) :
    negativeLongRootWeylElement (R := R) i ∈
      Subgroup.normalizer (diagonalTorus R m : Set (GLSymplecticFin m R)) := by
  rw [← positiveLongRootWeylElement_inv]
  exact inv_mem (positiveLongRootWeylElement_mem_normalizer_diagonalTorus i)

/-- Applying a ring homomorphism entrywise to a long-root Weyl representative gives the
corresponding representative over the target ring. -/
@[simp]
theorem map_positiveLongRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (i : Fin m) :
    GLSymplecticFin.map m R f (positiveLongRootWeylElement i) =
      positiveLongRootWeylElement i := by
  simp [positiveLongRootWeylElement]

/-- Applying a ring homomorphism entrywise to a negative long-root Weyl representative gives the
corresponding representative over the target ring. -/
@[simp]
theorem map_negativeLongRootWeylElement {S : Type v} [CommRing S]
    (f : R →+* S) (i : Fin m) :
    GLSymplecticFin.map m R f (negativeLongRootWeylElement i) =
      negativeLongRootWeylElement i := by
  simp [negativeLongRootWeylElement]

end TauCeti.GLSymplecticFin
