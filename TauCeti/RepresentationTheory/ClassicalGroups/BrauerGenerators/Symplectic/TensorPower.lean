/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.sum_sum_smul_tprod_update_pair_mulVec`, the congruence at two slots the cup
-- invariance below runs on.
public import TauCeti.LinearAlgebra.PiTensorProduct.BasisExpansion
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Basic
-- The entrywise identities for `Matrix.J` the relations below contract with.
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The symplectic Brauer arc on a tensor power

A Brauer diagram on `d` strands acts on the `d`-th tensor power of `V = k^{2n}` by permuting the
slots along its through strands, contracting each pair of bottom points against the invariant
alternating form, and expanding each pair of top points through the inverse copairing. The
horizontal arcs are therefore all built from the *single-arc* diagrams: a cap on the two bottom
points `i` and `j`, closed off by a cup on the two top points `i` and `j`. This file builds that
operator, `TauCeti.symplecticCupCapAt`, on the `d`-th tensor power of the symplectic standard
module, and proves what an action of the Brauer algebra must respect of it: the loop rule, the
absorption of two arcs sharing a strand, the commutation of arcs on disjoint pairs of strands, and
the commutation with the diagonal action of the symplectic group.

The two-strand case is `TauCeti.symplecticCupCap` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`, which this
file reproduces at `d = 2` (`TauCeti.symplecticCupCapAt_zero_one`). There the generator is
assembled as a composite `cup ∘ₗ cap` through the tensor square, a route unavailable for two
strands sitting inside a larger tensor power, because splitting two of the `d` slots off a tensor
power is not an equality of tensor powers. The operator here is instead built in one step, by
pushing the `a`-th coordinate followed by the `x`-th basis vector through the strand `i`, the
`b`-th coordinate followed by the `y`-th basis vector through the strand `j`, and the identity
through all the others, weighted by `J a b` for the cap and `-J x y` for the cup and summed over
all four indices.

## The arc is an unordered pair of strands

The cap and the cup are each antisymmetric: exchanging their two endpoints changes the sign,
because the standard symplectic form is alternating
(`TauCeti.symplecticCap_comp_symplecticFlip` and `TauCeti.symplecticFlip_comp_symplecticCup`). On
a single arc the two sign changes cancel, so the generator `e i j` built here is unchanged by
exchanging `i` and `j` (`TauCeti.symplecticCupCapAt_comm`), exactly as in the orthogonal case: an
arc carries no orientation and is the unordered pair of the two strands it joins. What the
antisymmetry does force instead is the sign on the *crossing*, which is minus the flip of the two
slots (`TauCeti.symplecticCrossing` on two strands), and the negative loop value below.

## The relations

Writing `e i j` for the generator, the relations proved here are

* `e i j * e i j = (-2n) • e i j`, the loop rule at the symplectic loop value `δ = -2n = -dim V`;
* `e i j = e j i`, the cancellation of the two sign changes just described;
* `e i j * e j l * e i j = e i j` for two arcs sharing the strand `j`;
* `e i j * e a b = e a b * e i j` for two arcs on disjoint pairs of strands;
* `e i j * ρ g = ρ g * e i j` for `g` in the symplectic group acting diagonally.

The relations involving a crossing are not stated here: the Brauer crossing on two of `d` strands
is the sign-twisted transposition of those two slots, and the sign-twisted action of the symmetric
group on `V^{⊗d}` and its relations with the arcs are in
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Crossing.lean`.

## Implementation notes

The cap and the cup are read through the entries of `Matrix.J` rather than through a partner
involution of the index type `Fin n ⊕ Fin n`, matching
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`: the
definition is then a fourfold sum, and the cap half of it is the double sum that
`Matrix.toBilin'` already is.

At `i = j` the two strands coincide. The first branch of `TauCeti.symplecticCupCapStrand` then
wins, the second plug of the definition is dead, and the operator is not an arc of a Brauer
diagram but the rank-one map of `TauCeti.symplecticCupCapAt_self_tprod`: the slot `i` is paired
with the all-ones vector and replaced by the row sums of `J`. Every statement that reads an arc
through the form therefore carries the hypothesis `i ≠ j`; `TauCeti.symplecticCupCapAt_comm` and
`TauCeti.commute_symplecticCupCapAt_of_disjoint`, which are strandwise statements, hold for
coincident strands too.

## Main definitions

* `TauCeti.symplecticCupCapAt`: the symplectic Brauer generator `e i j` on the `d`-th tensor power
  of `k^{2n}`.

## Main results

* `TauCeti.symplecticCupCapAt_tprod`: the value of the generator on a pure tensor at distinct
  strands, the invariant form of the two chosen factors times the cup re-expanding those slots.
* `TauCeti.symplecticCupCapAt_tprod_single`: the same on a monomial tensor of standard basis
  vectors, where the form is an entry of `J`.
* `TauCeti.symplecticCupCapAt_self_tprod`: the degenerate value at `i = j`, where the second plug
  is dead and the operator is not an arc.
* `TauCeti.symplecticCupCapAt_comm`: **the generator depends only on the unordered pair of
  strands**, the two sign changes of the cap and the cup cancelling.
* `TauCeti.symplecticCupCapAt_zero_one`: on two strands the generator is
  `TauCeti.symplecticCupCap`.
* `TauCeti.symplecticCupCapAt_mul_self`: **the loop rule** `e * e = (-2n) • e`.
* `TauCeti.commute_symplecticCupCapAt_of_disjoint`: **disjoint arcs commute.**
* `TauCeti.symplecticCupCapAt_mul_mul_self`: **two arcs sharing a strand absorb**,
  `e i j * e j l * e i j = e i j`.
* `TauCeti.commute_symplecticCupCapAt_piTensorProductMap`: the generator commutes with the
  diagonal action of every matrix `A` preserving the standard alternating form, `Aᵀ * J * A = J`.
* `TauCeti.commute_symplecticCupCapAt_tensorPower`: **the generator commutes with the diagonal
  action of the symplectic group**, so every single-arc diagram acts by an intertwiner.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9, for the action of the Brauer algebra on a tensor power and its role as the
  centralizer of the symplectic group.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ) [CommRing k]

/-- The family of linear maps that `TauCeti.symplecticCupCapAt` pushes through the `d` strands:
the `a`-th coordinate followed by the `x`-th standard basis vector on the strand `i`, the `b`-th
coordinate followed by the `y`-th standard basis vector on the strand `j`, and the identity on
every other strand. This is an implementation detail of `TauCeti.symplecticCupCapAt`, whose
interface is `TauCeti.symplecticCupCapAt_tprod`. -/
private def symplecticCupCapStrand (i j : Fin d) (a b x y : Fin n ⊕ Fin n) (t : Fin d) :
    ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k) :=
  if t = i then (LinearMap.proj a).smulRight (Pi.single x (1 : k))
  else if t = j then (LinearMap.proj b).smulRight (Pi.single y (1 : k))
  else LinearMap.id

/-- **The symplectic Brauer generator `e` on the strands `i` and `j`** of the `d`-th tensor power
of `k^{2n}`: a cap contracting the slots `i` and `j` against the standard alternating form, closed
off by a cup re-expanding those two slots through the inverse copairing, the bivector of `-J`.

The cap contributes the weight `J a b` to the pair of coordinates it reads off the two slots, and
the cup the weight `-J x y` to the pair of basis vectors it writes back into them. At `i = j` the
two strands coincide and the result is not an arc of a Brauer diagram
(`TauCeti.symplecticCupCapAt_self_tprod`); see the module docstring. -/
noncomputable def symplecticCupCapAt (i j : Fin d) :
    Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
    (-(Matrix.J (Fin n) k a b * Matrix.J (Fin n) k x y)) •
      PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y)

variable {k n d}

/-! ### The value on a pure tensor -/

/-- One summand of `TauCeti.symplecticCupCapAt` on a pure tensor. -/
private theorem symplecticCupCapAt_map_tprod {i j : Fin d} (hij : i ≠ j)
    (a b x y : Fin n ⊕ Fin n) (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y) (PiTensorProduct.tprod k v) =
      (v i a * v j b) • PiTensorProduct.tprod k (Function.update
        (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
  have hval : PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y)
      (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (Function.update
        (Function.update v i (v i a • Pi.single x (1 : k))) j (v j b • Pi.single y (1 : k))) := by
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext t
    rcases eq_or_ne t i with hi | hi
    · subst hi
      rw [Function.update_of_ne hij, Function.update_self]
      simp [symplecticCupCapStrand]
    · rcases eq_or_ne t j with hj | hj
      · subst hj
        rw [Function.update_self]
        simp [symplecticCupCapStrand, hi]
      · rw [Function.update_of_ne hj, Function.update_of_ne hi]
        simp [symplecticCupCapStrand, hi, hj]
  rw [hval]
  conv_lhs => rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm hij,
    (PiTensorProduct.tprod k).map_update_smul, Function.update_comm (Ne.symm hij)]
  rw [smul_smul, mul_comm]

/-- **The generator on a pure tensor**: the two chosen factors are contracted against one another
by the standard alternating form, and the two slots are re-expanded through the cup. -/
@[simp]
theorem symplecticCupCapAt_tprod {i j : Fin d} (hij : i ≠ j)
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticCupCapAt k n d i j (PiTensorProduct.tprod k v) =
      stdSymplecticBilinForm k n (v i) (v j) •
        -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
  have hform : stdSymplecticBilinForm k n (v i) (v j) =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, v i a * Matrix.J (Fin n) k a b * v j b := by
    rw [stdSymplecticBilinForm_apply, ← Matrix.toBilin'_apply' (Matrix.J (Fin n) k),
      Matrix.toBilin'_apply]
  have hneg : (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, (-Matrix.J (Fin n) k x y) •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ =>
      (neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)) _ _).symm
  have hsummand : ∀ a b x y : Fin n ⊕ Fin n,
      (-(Matrix.J (Fin n) k a b * Matrix.J (Fin n) k x y)) •
          PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y)
            (PiTensorProduct.tprod k v) =
        (v i a * Matrix.J (Fin n) k a b * v j b * -Matrix.J (Fin n) k x y) •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
    intro a b x y
    rw [symplecticCupCapAt_map_tprod hij, smul_smul]
    congr 1
    ring
  rw [symplecticCupCapAt]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsummand a b x y, hform, hneg]
  -- the cap scalars depend on `a` and `b` and the cup ones on `x` and `y`, so the fourfold sum is
  -- the product of the two double sums: distribute the scalar action over both of them
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]

/-- **The generator on a monomial tensor of standard basis vectors**, at distinct strands: the entry
of `J` at the two labels, times the cup re-expanding the two slots as standard basis vectors. -/
theorem symplecticCupCapAt_tprod_single {i j : Fin d} (hij : i ≠ j)
    (f : Fin d → Fin n ⊕ Fin n) :
    symplecticCupCapAt k n d i j (PiTensorProduct.tprod k fun t => Pi.single (f t) (1 : k)) =
      -(Matrix.J (Fin n) k (f i) (f j) • ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x y • PiTensorProduct.tprod k fun t =>
          (Pi.single (Function.update (Function.update f i x) j y t) (1 : k) :
            (Fin n ⊕ Fin n) → k)) := by
  have hplug : ∀ x y : Fin n ⊕ Fin n,
      Function.update (Function.update (fun t => Pi.single (f t) (1 : k)) i (Pi.single x 1)) j
          (Pi.single y 1) =
        fun t => (Pi.single (Function.update (Function.update f i x) j y t) (1 : k) :
          (Fin n ⊕ Fin n) → k) := by
    intro x y
    funext t
    simp only [Function.update_apply]
    split_ifs <;> rfl
  rw [symplecticCupCapAt_tprod hij, stdSymplecticBilinForm_single_single, smul_neg]
  simp only [hplug]

/-- One summand of `TauCeti.symplecticCupCapAt` at coincident strands: the strand `i` wins the
first branch of `TauCeti.symplecticCupCapStrand`, so the second plug is dead and only the `a`-th
coordinate and the `x`-th basis vector survive. -/
private theorem symplecticCupCapAt_self_map_tprod (i : Fin d) (a b x y : Fin n ⊕ Fin n)
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    PiTensorProduct.map (symplecticCupCapStrand k n d i i a b x y) (PiTensorProduct.tprod k v) =
      v i a • PiTensorProduct.tprod k (Function.update v i (Pi.single x (1 : k))) := by
  have hval : PiTensorProduct.map (symplecticCupCapStrand k n d i i a b x y)
      (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (Function.update v i (v i a • Pi.single x (1 : k))) := by
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext t
    rcases eq_or_ne t i with hi | hi
    · subst hi
      rw [Function.update_self]
      simp [symplecticCupCapStrand]
    · rw [Function.update_of_ne hi]
      simp [symplecticCupCapStrand, hi]
  rw [hval, (PiTensorProduct.tprod k).map_update_smul]

/-- **The degenerate value at coincident strands**: at `i = j` the cap and the cup land on the same
slot, and the second plug of `TauCeti.symplecticCupCapAt` is dead. The operator is then *not* the
contraction of that slot against itself -- which would be quadratic in `v i`, not linear -- but the
rank-one map pairing the slot with the all-ones vector and refilling it with the row sums of `J`.
This is why the relations that read the arc through the form assume `i ≠ j`. -/
@[simp]
theorem symplecticCupCapAt_self_tprod (i : Fin d) (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticCupCapAt k n d i i (PiTensorProduct.tprod k v) =
      stdSymplecticBilinForm k n (v i) 1 •
        -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update v i (Pi.single x (1 : k))) := by
  have hform : stdSymplecticBilinForm k n (v i) 1 =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, v i a * Matrix.J (Fin n) k a b := by
    rw [stdSymplecticBilinForm_apply, ← Matrix.toBilin'_apply' (Matrix.J (Fin n) k),
      Matrix.toBilin'_apply]
    simp
  have hneg : (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update v i (Pi.single x (1 : k)))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, (-Matrix.J (Fin n) k x y) •
        PiTensorProduct.tprod k (Function.update v i (Pi.single x (1 : k))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ =>
      (neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)) _ _).symm
  have hsummand : ∀ a b x y : Fin n ⊕ Fin n,
      (-(Matrix.J (Fin n) k a b * Matrix.J (Fin n) k x y)) •
          PiTensorProduct.map (symplecticCupCapStrand k n d i i a b x y)
            (PiTensorProduct.tprod k v) =
        (v i a * Matrix.J (Fin n) k a b * -Matrix.J (Fin n) k x y) •
          PiTensorProduct.tprod k (Function.update v i (Pi.single x (1 : k))) := by
    intro a b x y
    rw [symplecticCupCapAt_self_map_tprod, smul_smul]
    congr 1
    ring
  rw [symplecticCupCapAt]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsummand a b x y, hform, hneg]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]

/-! ### The orientation of the arc -/

/-- **The generator depends only on the unordered pair of strands.** Exchanging the two endpoints
of the arc changes the sign of the cap and the sign of the cup, and the two changes cancel, so an
arc of a diagram carries no orientation. The sign the alternating form does force is the one on the
crossing, not one on an arc. -/
theorem symplecticCupCapAt_comm (i j : Fin d) :
    symplecticCupCapAt k n d i j = symplecticCupCapAt k n d j i := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hstrand : ∀ a b x y : Fin n ⊕ Fin n,
      symplecticCupCapStrand k n d j i b a y x = symplecticCupCapStrand k n d i j a b x y := by
    intro a b x y
    funext t
    rcases eq_or_ne t i with hi | hi
    · subst hi
      simp [symplecticCupCapStrand, hij]
    · rcases eq_or_ne t j with hj | hj
      · subst hj
        simp [symplecticCupCapStrand, hi]
      · simp [symplecticCupCapStrand, hi, hj]
  rw [symplecticCupCapAt, symplecticCupCapAt]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hstrand a b x y, Matrix.J_apply_swap (Fin n) k a b, Matrix.J_apply_swap (Fin n) k x y]
  congr 1
  ring

/-! ### Two strands -/

/-- **On two strands the generator is the two-strand one**: the operator built here at `d = 2` and
the arc `0, 1` is the composite `cup ∘ₗ cap` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`. -/
theorem symplecticCupCapAt_zero_one :
    symplecticCupCapAt k n 2 0 1 = symplecticCupCap k n := by
  have hij : (0 : Fin 2) ≠ 1 := by decide
  refine PiTensorProduct.ext ?_
  ext v
  have htuple : ∀ x y : Fin n ⊕ Fin n,
      Function.update (Function.update v 0 (Pi.single x (1 : k))) 1 (Pi.single y (1 : k)) =
        ![Pi.single x (1 : k), Pi.single y (1 : k)] := by
    intro x y
    funext t
    fin_cases t <;> simp
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    symplecticCupCapAt_tprod hij, symplecticCupCap_apply, symplecticCap_tprod,
    symplecticCup_apply]
  refine congrArg _ ?_
  rw [neg_inj]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [htuple x y]

/-! ### The loop rule -/

/-- **The loop rule `e² = δ e`** at the symplectic loop value `δ = -2n = -dim V`: a cup stacked
under a cap closes into a loop, which contracts the pairing `J` against the copairing `-J`. -/
@[simp]
theorem symplecticCupCapAt_mul_self {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j * symplecticCupCapAt k n d i j =
      -(2 * n : k) • symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hterm : ∀ x : Fin n ⊕ Fin n,
      symplecticCupCapAt k n d i j
          (∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y • PiTensorProduct.tprod k
            (Function.update (Function.update v i (Pi.single x (1 : k))) j
              (Pi.single y (1 : k)))) =
        (∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y) •
          -∑ x' : Fin n ⊕ Fin n, ∑ y' : Fin n ⊕ Fin n, Matrix.J (Fin n) k x' y' •
            PiTensorProduct.tprod k (Function.update
              (Function.update v i (Pi.single x' (1 : k))) j (Pi.single y' (1 : k))) := by
    intro x
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, symplecticCupCapAt_tprod hij, Function.update_of_ne hij,
      Function.update_self, Function.update_self, stdSymplecticBilinForm_single_single,
      smul_smul]
    refine congrArg (fun z => (Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y) • -z) ?_
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by
      -- Plugging twice at the same pair of slots keeps only the second plug.
      rw [Function.update_comm hij.symm, Function.update_idem, Function.update_idem]
  have hT : symplecticCupCapAt k n d i j
        (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)))) =
      -(2 * n : k) • -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
    rw [map_neg, map_sum, Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_smul,
      Matrix.sum_sum_J_mul_J, Fintype.card_fin]
    exact (neg_smul _ _).symm
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, LinearMap.smul_apply, symplecticCupCapAt_tprod hij, map_smul, hT]
  exact smul_comm _ _ _

/-! ### Two arcs -/

/-- Two summands of `TauCeti.symplecticCupCapAt` on disjoint pairs of strands commute: at every
strand one of the two families `TauCeti.symplecticCupCapStrand` is the identity, so the two
pointwise composites agree and `PiTensorProduct.map_comp` turns them into the same operator.
Nothing here reads an arc through the form, so the two strands of a pair may coincide. -/
private theorem commute_map_symplecticCupCapStrand {i j p q : Fin d} (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (a b x y a' b' x' y' : Fin n ⊕ Fin n) :
    Commute (PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y))
      (PiTensorProduct.map (symplecticCupCapStrand k n d p q a' b' x' y')) := by
  have hstrand :
      (fun t => symplecticCupCapStrand k n d i j a b x y t ∘ₗ
          symplecticCupCapStrand k n d p q a' b' x' y' t) =
        fun t => symplecticCupCapStrand k n d p q a' b' x' y' t ∘ₗ
          symplecticCupCapStrand k n d i j a b x y t := by
    funext t
    rcases eq_or_ne t i with hi | hi
    · subst hi
      simp [symplecticCupCapStrand, hip, hiq]
    · rcases eq_or_ne t j with hj | hj
      · subst hj
        simp [symplecticCupCapStrand, hi, hjp, hjq]
      · simp [symplecticCupCapStrand, hi, hj]
  have hmul : (PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y) :
        Module.End k _) * PiTensorProduct.map (symplecticCupCapStrand k n d p q a' b' x' y') =
      PiTensorProduct.map (symplecticCupCapStrand k n d p q a' b' x' y') *
        PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y) := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp, hstrand]
  exact hmul

/-- **Disjoint arcs commute**: two generators whose pairs of strands are disjoint act in disjoint
groups of slots. The two strands of either pair may coincide, since the proof never reads an arc
through the form: it only needs each strand to be touched by at most one of the two generators. -/
theorem commute_symplecticCupCapAt_of_disjoint {i j p q : Fin d} (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) :
    Commute (symplecticCupCapAt k n d i j) (symplecticCupCapAt k n d p q) := by
  rw [symplecticCupCapAt, symplecticCupCapAt]
  exact Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ =>
    Commute.sum_left _ _ _ fun x _ => Commute.sum_left _ _ _ fun y _ =>
      Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ =>
        Commute.sum_right _ _ _ fun x' _ => Commute.sum_right _ _ _ fun y' _ =>
          ((commute_map_symplecticCupCapStrand hip hiq hjp hjq a b x y a' b' x'
            y').smul_right _).smul_left _

/-- **Two arcs sharing one strand**: `e i j * e j l * e i j = e i j`, the relation that makes two
generators on overlapping pairs of strands absorb one another. The middle arc contracts the shared
strand `j`, which the outer one has filled with a basis vector, against the strand `l`, and the
outer arc then contracts the two slots it had filled against each other. Both contractions are the
column pairing `Jᵀ * J = 1` of the alternating form, so the zigzag straightens and the three signs
carried by the cups cancel against it. -/
theorem symplecticCupCapAt_mul_mul_self {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) :
    symplecticCupCapAt k n d i j * symplecticCupCapAt k n d j l * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  -- the middle arc pairs the strand `j`, carrying the `y`-th basis vector, against the strand `l`
  have hmid : ∀ x y : Fin n ⊕ Fin n,
      symplecticCupCapAt k n d j l (PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)))) =
        stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) •
          -∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single x (1 : k))) j (Pi.single p (1 : k)))
              l (Pi.single q (1 : k))) := by
    intro x y
    rw [symplecticCupCapAt_tprod hjl, Function.update_self, Function.update_of_ne hjl.symm,
      Function.update_of_ne hil.symm]
    simp only [Function.update_idem]
  -- the outer arc then pairs the two slots it had filled against each other
  have hout : ∀ x p q : Fin n ⊕ Fin n,
      symplecticCupCapAt k n d i j (PiTensorProduct.tprod k (Function.update
          (Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single p (1 : k)))
          l (Pi.single q (1 : k)))) =
        Matrix.J (Fin n) k x p •
          -∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := by
    intro x p q
    have hplug : ∀ r s : Fin n ⊕ Fin n,
        Function.update (Function.update (Function.update (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single p (1 : k)))
            l (Pi.single q (1 : k))) i (Pi.single r (1 : k))) j (Pi.single s (1 : k)) =
          Function.update (Function.update (Function.update v i (Pi.single r (1 : k))) j
            (Pi.single s (1 : k))) l (Pi.single q (1 : k)) := by
      intro r s
      funext t
      rcases eq_or_ne t j with rfl | htj
      · simp only [Function.update_self, Function.update_of_ne hjl]
      rcases eq_or_ne t i with rfl | hti
      · simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hil]
      rcases eq_or_ne t l with rfl | htl
      · simp only [Function.update_self, Function.update_of_ne hjl.symm,
          Function.update_of_ne hil.symm]
      simp only [Function.update_of_ne htj, Function.update_of_ne hti, Function.update_of_ne htl]
    rw [symplecticCupCapAt_tprod hij, Function.update_of_ne hil, Function.update_of_ne hij,
      Function.update_self, Function.update_of_ne hjl, Function.update_self,
      stdSymplecticBilinForm_single_single]
    simp only [hplug]
  -- the two steps composed, with every scalar collected in front of the `q`-th cup
  have hfull : ∀ x y : Fin n ⊕ Fin n,
      symplecticCupCapAt k n d i j (symplecticCupCapAt k n d j l (PiTensorProduct.tprod k
          (Function.update (Function.update v i (Pi.single x (1 : k))) j
            (Pi.single y (1 : k))))) =
        ∑ q : Fin n ⊕ Fin n, (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
            ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p) •
          ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := by
    intro x y
    have hinner : ∀ p : Fin n ⊕ Fin n, symplecticCupCapAt k n d i j
        (∑ q : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q • PiTensorProduct.tprod k
          (Function.update (Function.update (Function.update v i (Pi.single x (1 : k))) j
            (Pi.single p (1 : k))) l (Pi.single q (1 : k)))) =
        ∑ q : Fin n ⊕ Fin n, (Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p) •
          -∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := by
      intro p
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, hout x p q, smul_smul]
    rw [hmid x y, map_smul, map_neg, map_sum, Finset.sum_congr rfl fun p _ => hinner p]
    simp only [smul_neg, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul, smul_smul]
  -- the same, summed over the cup of the outer arc
  have hrow : ∀ x : Fin n ⊕ Fin n,
      symplecticCupCapAt k n d i j (symplecticCupCapAt k n d j l
          (∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y • PiTensorProduct.tprod k
            (Function.update (Function.update v i (Pi.single x (1 : k))) j
              (Pi.single y (1 : k))))) =
        ∑ y : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, (Matrix.J (Fin n) k x y *
            (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
              ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) •
          ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := by
    intro x
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, map_smul, hfull x y, Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => smul_smul _ _ _
  -- the scalars contract to the `q`-th coordinate of the strand `l`, by the column pairing twice
  have hscalar : ∀ q : Fin n ⊕ Fin n,
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, (Matrix.J (Fin n) k x y *
          (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
            ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) = v l q := by
    intro q
    have hc : ∀ y : Fin n ⊕ Fin n,
        stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) =
          ∑ b : Fin n ⊕ Fin n, Matrix.J (Fin n) k y b * v l b := by
      intro y
      rw [stdSymplecticBilinForm_apply, single_dotProduct, one_mul]
      simp [Matrix.mulVec, dotProduct]
    have hre : ∀ y p x : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x y * (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
            (Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) =
          stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) * Matrix.J (Fin n) k p q *
            (Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x p) := by
      intro y p x
      ring
    have key : ∀ y : Fin n ⊕ Fin n,
        ∑ x : Fin n ⊕ Fin n, (Matrix.J (Fin n) k x y *
            (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
              ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) =
          stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) * Matrix.J (Fin n) k y q := by
      intro y
      simp only [Finset.mul_sum]
      calc ∑ x : Fin n ⊕ Fin n, ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y *
            (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
              (Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p))
          = ∑ p : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n,
              stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) * Matrix.J (Fin n) k p q *
                (Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x p) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => hre y p x
        _ = ∑ p : Fin n ⊕ Fin n,
              stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) * Matrix.J (Fin n) k p q *
                (if y = p then (1 : k) else 0) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.mul_sum, Matrix.sum_J_mul_J_eq_ite]
        _ = stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) * Matrix.J (Fin n) k y q := by
            simp
    rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => key y]
    calc ∑ y : Fin n ⊕ Fin n, stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
          Matrix.J (Fin n) k y q
        = ∑ y : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
            v l b * (Matrix.J (Fin n) k y b * Matrix.J (Fin n) k y q) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hc y, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b : Fin n ⊕ Fin n, v l b *
            ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k y b * Matrix.J (Fin n) k y q := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      _ = v l q := by
          simp only [Matrix.sum_J_mul_J_eq_ite]
          simp
  -- summing the surviving coordinate over `q` rebuilds the strand `l`
  have hrestore : ∀ r s : Fin n ⊕ Fin n,
      ∑ q : Fin n ⊕ Fin n, v l q • PiTensorProduct.tprod k (Function.update
          (Function.update (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
          l (Pi.single q (1 : k))) =
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k))) := by
    intro r s
    have hl : Function.update
        (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)) l = v l := by
      rw [Function.update_of_ne hjl.symm, Function.update_of_ne hil.symm]
    rw [Finset.sum_congr rfl fun q _ => ((PiTensorProduct.tprod k).map_update_smul
        (Function.update (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k))) l
        (v l q) (Pi.single q (1 : k))).symm,
      ← (PiTensorProduct.tprod k).map_update_sum, ← pi_eq_sum_univ' (v l), ← hl,
      Function.update_eq_self]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, symplecticCupCapAt_tprod hij, map_smul, map_smul]
  refine congrArg _ ?_
  rw [map_neg, map_sum, map_neg, map_sum, Finset.sum_congr rfl fun x _ => hrow x, neg_inj]
  calc ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n, (Matrix.J (Fin n) k x y *
          (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
            ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) •
        ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
          PiTensorProduct.tprod k (Function.update (Function.update
            (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
            l (Pi.single q (1 : k)))
      = ∑ q : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y *
            (stdSymplecticBilinForm k n (Pi.single y (1 : k)) (v l) *
              ∑ p : Fin n ⊕ Fin n, Matrix.J (Fin n) k p q * Matrix.J (Fin n) k x p)) •
          ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := Finset.sum_comm_cycle
    _ = ∑ q : Fin n ⊕ Fin n, v l q •
          ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k)))
              l (Pi.single q (1 : k))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [← Finset.sum_smul]
        rw [hscalar q]
    _ = ∑ q : Fin n ⊕ Fin n, ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n,
          (v l q * Matrix.J (Fin n) k r s) • PiTensorProduct.tprod k (Function.update
            (Function.update (Function.update v i (Pi.single r (1 : k))) j
              (Pi.single s (1 : k))) l (Pi.single q (1 : k))) := by
        simp only [Finset.smul_sum, smul_smul]
    _ = ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n,
          (v l q * Matrix.J (Fin n) k r s) • PiTensorProduct.tprod k (Function.update
            (Function.update (Function.update v i (Pi.single r (1 : k))) j
              (Pi.single s (1 : k))) l (Pi.single q (1 : k))) := by
        rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    _ = ∑ r : Fin n ⊕ Fin n, ∑ s : Fin n ⊕ Fin n, Matrix.J (Fin n) k r s •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single r (1 : k))) j (Pi.single s (1 : k))) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        rw [← hrestore r s, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => by
          rw [smul_smul, mul_comm (Matrix.J (Fin n) k r s) (v l q)]

/-! ### The arc as an intertwiner -/

/-- **The generator commutes with the diagonal action of a symplectic matrix**: the cap consumes
`Aᵀ * J * A = J`, which is exactly preservation of the standard alternating form, and the cup the
other one-sided identity `A * J * Aᵀ = J`, which `SymplecticGroup.mem_iff` derives from it. -/
theorem commute_symplecticCupCapAt_piTensorProductMap
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k) {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j)
      (PiTensorProduct.map fun _ : Fin d => Matrix.mulVecLin A) := by
  have hcup : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k :=
    SymplecticGroup.mem_iff.mp (SymplecticGroup.mem_iff'.mpr hA)
  refine PiTensorProduct.ext ?_
  ext v
  have hform : stdSymplecticBilinForm k n (A *ᵥ v i) (A *ᵥ v j) =
      stdSymplecticBilinForm k n (v i) (v j) := by
    rw [stdSymplecticBilinForm_apply, stdSymplecticBilinForm_apply, Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hA, ← Matrix.dotProduct_mulVec]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, PiTensorProduct.map_tprod,
    symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod hij, map_smul, map_neg, map_sum]
  simp only [Matrix.mulVecLin_apply]
  rw [hform]
  refine congrArg _ ?_
  -- the cup at the slots `i` and `j` is invariant: pushing `A` through them congruates `J`
  have hbivector := sum_sum_smul_tprod_update_pair_mulVec A (Matrix.J (Fin n) k) hij
    fun t => A *ᵥ v t
  rw [hcup] at hbivector
  rw [neg_inj, ← hbivector]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, PiTensorProduct.map_tprod]
  simp only [Matrix.mulVecLin_apply]
  refine congrArg _ (congrArg _ ?_)
  funext t
  rcases eq_or_ne t i with hi | hi
  · subst hi
    rw [Function.update_of_ne hij, Function.update_self, Function.update_of_ne hij,
      Function.update_self]
  · rcases eq_or_ne t j with hj | hj
    · subst hj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hi, Function.update_of_ne hj,
        Function.update_of_ne hi]

/-- **The symplectic Brauer arc commutes with the symplectic group.** Membership in
`Matrix.symplecticGroup` supplies preservation of the standard alternating form, so every
single-arc diagram acts on the tensor power by an intertwiner of the diagonal symplectic
action. -/
theorem commute_symplecticCupCapAt_tensorPower (g : Matrix.symplecticGroup (Fin n) k)
    {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_symplecticCupCapAt_piTensorProductMap
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop) hij

end TauCeti
