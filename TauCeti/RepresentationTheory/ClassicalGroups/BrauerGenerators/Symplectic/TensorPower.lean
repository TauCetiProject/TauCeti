/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.tprod_update_pair_expand`, the standard-basis expansion at two slots.
public import TauCeti.LinearAlgebra.PiTensorProduct.BasisExpansion
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Basic

/-!
# The symplectic Brauer arc on a tensor power

A Brauer diagram on `d` strands acts on the `d`-th tensor power of `V = k^{2n}` by permuting the
slots along its through strands, contracting each pair of bottom points against the invariant
alternating form, and expanding each pair of top points through the inverse copairing. The
horizontal arcs are therefore all built from the *single-arc* diagrams: a cap on the two bottom
points `i` and `j`, closed off by a cup on the two top points `i` and `j`. This file builds that
operator, `TauCeti.symplecticCupCapAt`, on the `d`-th tensor power of the symplectic standard
module, and proves what an action of the Brauer algebra must respect of it: the loop rule, the
commutation of arcs on disjoint pairs of strands, and the commutation with the diagonal action of
the symplectic group.

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

## The orientation of an arc cancels

The cap and the cup each change sign when their two endpoints are exchanged, because the standard
symplectic form is alternating (`TauCeti.symplecticCap_comp_symplecticFlip` and
`TauCeti.symplecticFlip_comp_symplecticCup`). That is why a Brauer *diagram* acting on `V^{⊗d}`
needs a chosen ordering of each of its arcs, and why the crossing is the sign-twisted flip rather
than the bare one. On a *single* arc the two sign changes cancel: the generator `e i j` built here
is unchanged by exchanging `i` and `j` (`TauCeti.symplecticCupCapAt_comm`), exactly as in the
orthogonal case. So the ordering convention is invisible to the relations proved here, and it is
the relative orientation of *different* arcs of one diagram that it will pin down.

## The relations

Writing `e i j` for the generator, the relations proved here are

* `e i j * e i j = (-2n) • e i j`, the loop rule at the symplectic loop value `δ = -2n = -dim V`;
* `e i j = e j i`, the cancellation of the orientation just described;
* `e i j * e a b = e a b * e i j` for two arcs on disjoint pairs of strands;
* `e i j * ρ g = ρ g * e i j` for `g` in the symplectic group acting diagonally.

The relations involving a crossing are not stated here: the Brauer crossing on two of `d` strands
is the sign-twisted transposition of those two slots, and the sign-twisted action of the symmetric
group on `V^{⊗d}` is not built yet. Nothing below uses it.

## Implementation notes

The cap and the cup are read through the entries of `Matrix.J` rather than through a partner
involution of the index type `Fin n ⊕ Fin n`, matching
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`: the
definition is then a fourfold sum, and the cap half of it is the double sum that
`Matrix.toBilin'` already is.

At `i = j` the two strands coincide. The first branch of `TauCeti.symplecticCupCapStrand` then
wins and the operator is not an arc of a Brauer diagram; nothing is proved about that degenerate
value, and every statement that reads an arc through the form carries the hypothesis `i ≠ j`. Only
`TauCeti.commute_symplecticCupCapAt_of_disjoint`, which is a strandwise statement, holds for
coincident strands too.

## Main definitions

* `TauCeti.symplecticCupCapAt`: the symplectic Brauer generator `e i j` on the `d`-th tensor power
  of `k^{2n}`.

## Main results

* `TauCeti.symplecticCupCapAt_tprod`: the value of the generator on a pure tensor at distinct
  strands, the invariant form of the two chosen factors times the cup re-expanding those slots.
* `TauCeti.symplecticCupCapAt_comm`: **the generator depends only on the unordered pair of
  strands**, the two sign changes of the cap and the cup cancelling.
* `TauCeti.symplecticCupCapAt_zero_one`: on two strands the generator is
  `TauCeti.symplecticCupCap`.
* `TauCeti.symplecticCupCapAt_mul_self`: **the loop rule** `e * e = (-2n) • e`.
* `TauCeti.commute_symplecticCupCapAt_of_disjoint`: **disjoint arcs commute.**
* `TauCeti.commute_symplecticCupCapAt_piTensorProductMap`: the generator commutes with the
  diagonal action of every matrix `A` with `Aᵀ * J * A = J` and `A * J * Aᵀ = J`; the cap consumes
  the first identity and the cup the second.
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
two strands coincide and the result is not an arc of a Brauer diagram; see the module docstring. -/
noncomputable def symplecticCupCapAt (i j : Fin d) :
    Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
    (-(Matrix.J (Fin n) k a b * Matrix.J (Fin n) k x y)) •
      PiTensorProduct.map (symplecticCupCapStrand k n d i j a b x y)

variable {k n d}

/-! ### The value on a pure tensor -/

section Plug

variable {i j : Fin d} {x y x' y' : Fin n ⊕ Fin n} (v : Fin d → ((Fin n ⊕ Fin n) → k))

/-- The first of the two plugged slots. -/
private theorem update_pair_apply_left (hij : i ≠ j) :
    Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)) i =
      Pi.single x (1 : k) := by
  rw [Function.update_of_ne hij, Function.update_self]

/-- The second of the two plugged slots. -/
private theorem update_pair_apply_right :
    Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)) j =
      Pi.single y (1 : k) :=
  Function.update_self _ _ _

/-- Plugging twice at the same pair of slots keeps only the second plug. -/
private theorem update_pair_update_pair (hij : i ≠ j) :
    Function.update (Function.update
        (Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)))
        i (Pi.single x' (1 : k))) j (Pi.single y' (1 : k)) =
      Function.update (Function.update v i (Pi.single x' (1 : k))) j (Pi.single y' (1 : k)) := by
  funext t
  rcases eq_or_ne t j with hj | hj
  · subst hj
    simp
  · rcases eq_or_ne t i with hi | hi
    · subst hi
      simp [hij]
    · simp [hi, hj]

end Plug

/-- The regrouping that reads `TauCeti.symplecticCupCapAt` on a pure tensor: the cap contributes a
scalar depending on the first two indices and the cup a vector depending on the last two, so the
fourfold sum is the product of the two double sums. This is bookkeeping for
`TauCeti.symplecticCupCapAt_tprod`. -/
private theorem sum_mul_smul_eq_smul_sum {K : Type u} [CommRing K] {ι M : Type*} [Fintype ι]
    [AddCommMonoid M] [Module K M] (C D : ι → ι → K) (P : ι → ι → M) :
    ∑ a : ι, ∑ b : ι, ∑ x : ι, ∑ y : ι, (C a b * D x y) • P x y =
      (∑ a : ι, ∑ b : ι, C a b) • ∑ x : ι, ∑ y : ι, D x y • P x y := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun y _ => (smul_smul _ _ _).symm

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
  rw [symplecticCupCapAt]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [symplecticCupCapAt_map_tprod hij, smul_smul,
        show (-(Matrix.J (Fin n) k a b * Matrix.J (Fin n) k x y)) * (v i a * v j b) =
          (v i a * Matrix.J (Fin n) k a b * v j b) * (-Matrix.J (Fin n) k x y) by ring]]
  rw [sum_mul_smul_eq_smul_sum, hform, hneg]

/-! ### The orientation of the arc -/

/-- **The generator depends only on the unordered pair of strands.** Exchanging the two endpoints
of the arc changes the sign of the cap and the sign of the cup, and the two changes cancel: the
alternating form forces an orientation on each arc of a diagram, but not on a single arc. -/
theorem symplecticCupCapAt_comm {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j = symplecticCupCapAt k n d j i := by
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
  have hJ : ∀ p q : Fin n ⊕ Fin n,
      Matrix.J (Fin n) k q p = -Matrix.J (Fin n) k p q := by
    intro p q
    have h := congrFun (congrFun (Matrix.J_transpose (Fin n) k) p) q
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  rw [symplecticCupCapAt, symplecticCupCapAt]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hstrand a b x y, hJ a b, hJ x y]
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
theorem symplecticCupCapAt_mul_self {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j * symplecticCupCapAt k n d i j =
      -(2 * n : k) • symplecticCupCapAt k n d i j := by
  have hJ : Matrix.J (Fin n) k * (Matrix.J (Fin n) k)ᵀ = 1 := by
    rw [Matrix.J_transpose, Matrix.mul_neg, Matrix.J_squared, neg_neg]
  have hrow : ∀ x : Fin n ⊕ Fin n,
      ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y = 1 := by
    intro x
    have h := congrFun (congrFun hJ x) x
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.transpose_apply] using h
  have hloop : ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
      Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y = (2 * n : k) := by
    rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_const, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hform : ∀ x y : Fin n ⊕ Fin n,
      stdSymplecticBilinForm k n (Pi.single x (1 : k)) (Pi.single y (1 : k)) =
        Matrix.J (Fin n) k x y := by
    intro x y
    simp [stdSymplecticBilinForm_apply]
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
    rw [map_smul, symplecticCupCapAt_tprod hij, update_pair_apply_left v hij,
      update_pair_apply_right v, hform, smul_smul]
    refine congrArg (fun z => (Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y) • -z) ?_
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by
      rw [update_pair_update_pair v hij]
  have hT : symplecticCupCapAt k n d i j
        (-∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k)))) =
      -(2 * n : k) • -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
    rw [map_neg, map_sum, Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_smul, hloop]
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

/-! ### The arc as an intertwiner -/

/-- **The cup at two slots is invariant** under every matrix `A` with `A * J * Aᵀ = J`: expanding
the two slots in the standard basis turns the bivector of `J` into the bivector of the congruate
`A * J * Aᵀ`. This is the general-slot form of
`TauCeti.piTensorProductMap_comp_symplecticCup`. -/
private theorem sum_sum_tprod_update_pair_mulVec
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k) {i j : Fin d} (hij : i ≠ j)
    (u : Fin d → ((Fin n ⊕ Fin n) → k)) :
    ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Pi.single y (1 : k))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (Pi.single x (1 : k))) j (Pi.single y (1 : k))) := by
  have hcoef : ∀ a b : Fin n ⊕ Fin n,
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          Matrix.J (Fin n) k x y * (A a x * A b y) =
        (A * Matrix.J (Fin n) k * Aᵀ) a b := by
    intro a b
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  calc ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Pi.single y (1 : k)))
      = ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y * (A a x * A b y)) • PiTensorProduct.tprod k
            (Function.update (Function.update u i (Pi.single a (1 : k))) j
              (Pi.single b (1 : k))) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [tprod_update_pair_expand hij u, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_smul]
        simp only [Matrix.mulVec_single_one, Matrix.col_apply]
    -- move the two outer sums past the two inner ones, one adjacent swap at a time
    _ = ∑ x : Fin n ⊕ Fin n, ∑ a : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y * (A a x * A b y)) • PiTensorProduct.tprod k
            (Function.update (Function.update u i (Pi.single a (1 : k))) j
              (Pi.single b (1 : k))) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y * (A a x * A b y)) • PiTensorProduct.tprod k
            (Function.update (Function.update u i (Pi.single a (1 : k))) j
              (Pi.single b (1 : k))) := Finset.sum_comm
    _ = ∑ a : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y * (A a x * A b y)) • PiTensorProduct.tprod k
            (Function.update (Function.update u i (Pi.single a (1 : k))) j
              (Pi.single b (1 : k))) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          (Matrix.J (Fin n) k x y * (A a x * A b y)) • PiTensorProduct.tprod k
            (Function.update (Function.update u i (Pi.single a (1 : k))) j
              (Pi.single b (1 : k))) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, Matrix.J (Fin n) k a b •
          PiTensorProduct.tprod k (Function.update
            (Function.update u i (Pi.single a (1 : k))) j (Pi.single b (1 : k))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [← Finset.sum_smul]
        rw [hcoef a b, hA]

/-- **The generator commutes with the diagonal action of a symplectic matrix**: the cap consumes
`Aᵀ * J * A = J`, which is exactly preservation of the standard alternating form, and the cup
consumes the other one-sided identity `A * J * Aᵀ = J`. -/
theorem commute_symplecticCupCapAt_piTensorProductMap
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hcap : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k)
    (hcup : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k) {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j)
      (PiTensorProduct.map fun _ : Fin d => Matrix.mulVecLin A) := by
  refine PiTensorProduct.ext ?_
  ext v
  have hform : stdSymplecticBilinForm k n (A *ᵥ v i) (A *ᵥ v j) =
      stdSymplecticBilinForm k n (v i) (v j) := by
    rw [stdSymplecticBilinForm_apply, stdSymplecticBilinForm_apply, Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hcap, ← Matrix.dotProduct_mulVec]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, PiTensorProduct.map_tprod,
    symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod hij, map_smul, map_neg, map_sum]
  simp only [Matrix.mulVecLin_apply]
  rw [hform]
  refine congrArg _ ?_
  rw [neg_inj, ← sum_sum_tprod_update_pair_mulVec hcup hij fun t => A *ᵥ v t]
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
`Matrix.symplecticGroup` supplies both one-sided identities, so every single-arc diagram acts on
the tensor power by an intertwiner of the diagonal symplectic action. -/
theorem commute_symplecticCupCapAt_tensorPower (g : Matrix.symplecticGroup (Fin n) k)
    {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_symplecticCupCapAt_piTensorProductMap
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop)
      ((SymplecticGroup.mem_iff (l := Fin n) (R := k)).mp g.prop) hij

end TauCeti
