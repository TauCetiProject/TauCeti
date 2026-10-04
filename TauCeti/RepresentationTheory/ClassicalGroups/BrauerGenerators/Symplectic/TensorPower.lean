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
# The symplectic Brauer generators on a tensor power, and the relations they satisfy

A Brauer diagram on `d` strands acts on the `d`-th tensor power of `V = k^{2n}` by permuting the
slots along its through strands, contracting each pair of bottom points against the standard
alternating form, and expanding each pair of top points along the bivector of `-J`. The horizontal
arcs are therefore all built from the *single-arc* diagrams: a cap on the two bottom points `i` and
`j`, closed off by a cup on the two top points `i` and `j`. This file builds that operator on the
`d`-th tensor power, `TauCeti.symplecticCupCapAt`, together with the crossing
`TauCeti.symplecticCrossingAt` of two strands, and proves the relations they satisfy, which is what
an algebra homomorphism out of the Brauer algebra has to check.

The two-strand case is `TauCeti.symplecticCupCap` and `TauCeti.symplecticCrossing` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`, which this
file reproduces at `d = 2` (`TauCeti.symplecticCupCapAt_zero_one` and
`TauCeti.symplecticCrossingAt_zero_one`). There the generator is assembled as a composite
`cup ∘ₗ cap` through the tensor square, a route unavailable for two strands sitting inside a larger
tensor power, because splitting two of the `d` slots off a tensor power is not an equality of
tensor powers. The operator here is instead built in one step, by pushing the `p`-th coordinate
followed by the `x`-th basis vector through the strand `i`, the `q`-th coordinate followed by the
`y`-th basis vector through the strand `j`, and the identity through all the others, weighted by
`-J x y * J p q` and summed: the `(p, q)` sum is the cap, which contracts the two slots against the
alternating form, and the `(x, y)` sum is the cup, which re-expands them along the bivector of
`-J`.

## The sign conventions

Everything that distinguishes this file from its orthogonal twin
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Orthogonal/TensorPower.lean` is a
sign, and the signs are forced rather than chosen, exactly as in the two-strand file. The dot
product is symmetric, so there the arc contracts a pair of *unordered* slots and the crossing is
the bare permutation of tensor factors. The standard symplectic form is alternating, so here:

* the generator is *built* from an ordered pair of slots -- the strand `i` carries the first index
  of each copy of `J` and the strand `j` the second -- and that it nevertheless depends only on the
  unordered pair (`TauCeti.symplecticCupCapAt_comm`) is a theorem, the sign change of the cap and
  the sign change of the cup cancelling;
* the crossing is **minus** the permutation of the two tensor factors
  (`TauCeti.symplecticCrossingAt`), since with the bare permutation the relations `s e = e = e s`
  would force `2 • e = 0`.

## The relations

Writing `e i j` for the generator, `s i j` for the crossing of the strands `i` and `j`, and `r σ`
for the bare permutation action `PiTensorProduct.reindexRepresentation`, the relations proved here
are

* `e i j * e i j = (-2n) • e i j`, the loop rule at the loop value `δ = -2n = -dim V`;
* `s i j * s i j = 1`;
* `s i j * e i j = e i j` and `e i j * s i j = e i j`, the two absorptions of the crossing on the
  arc;
* `r σ * e i j = e (σ i) (σ j) * r σ`, the renaming of the arc by a permutation of the strands,
  which carries no sign because the two sides carry the same copy of `r σ`;
* `e i j * e a b = e a b * e i j` for two arcs on disjoint pairs of strands;
* `e i j * e j l * e i j = e i j` for two arcs sharing exactly one strand, which carries no sign
  even though each of the three generators does.

The braid relations need nothing new: `r` is a monoid homomorphism, so `r σ * r τ = r (σ * τ)`
already gives them, and the crossings differ from the permutations by signs that cancel in pairs.

## Implementation notes

Every proof here reduces to the same piece of plumbing: the tuple obtained from `v` by setting the
slot `i` to the `x`-th and the slot `j` to the `y`-th standard basis vector of `V`, spelled as a
pair of nested `Function.update`s. The four `update_pair_*` lemmas read its three kinds of entry
and compose two such plugs; they are `private` because they are steps of this file's argument. The
one genuinely linear-algebraic step is the expansion of those two slots in the standard basis,
which the invariance of the cup runs on; it is general infrastructure and lives in
`TauCeti/LinearAlgebra/PiTensorProduct/BasisExpansion.lean` as
`TauCeti.tprod_update_pair_expand`.

Each summand of the generator is a `PiTensorProduct.map`, so the relations that do not read the arc
through the alternating form are strandwise statements about the family
`TauCeti.symplecticCupCapStrand`: `PiTensorProduct.map_comp` turns a product of two summands into
the summand of the pointwise composite, and the commutation of two arcs on disjoint pairs of
strands is then the observation that at every strand one of the two factors is the identity. The
sign of the cup is carried inside the coefficient rather than as a negation of the whole sum, so
that those strandwise arguments see a plain sum of scaled maps.

## Main definitions

* `TauCeti.symplecticCupCapAt`: the Brauer generator `e i j` on the `d`-th tensor power of
  `k^{2n}`.
* `TauCeti.symplecticCrossingAt`: the Brauer crossing `s i j`, minus the permutation of the two
  tensor factors `i` and `j`.

## Main results

* `TauCeti.symplecticCupCapAt_tprod`: the value of the generator on a pure tensor, the formula
  every relation below but the renaming one runs on.
* `TauCeti.symplecticCupCapAt_comm`: the generator depends only on the unordered pair of strands,
  although the alternating form and the bivector are each antisymmetric.
* `TauCeti.symplecticCupCapAt_mul_self`, `TauCeti.symplecticCrossingAt_mul_self`,
  `TauCeti.symplecticCrossingAt_mul_symplecticCupCapAt`,
  `TauCeti.symplecticCupCapAt_mul_symplecticCrossingAt`,
  `TauCeti.reindexRepresentation_mul_symplecticCupCapAt`,
  `TauCeti.commute_symplecticCupCapAt_of_disjoint` and
  `TauCeti.symplecticCupCapAt_mul_mul_self`: the relations listed above, with
  `TauCeti.commute_reindexRepresentation_symplecticCupCapAt` the distant-crossing case of the
  renaming relation.
* `TauCeti.symplecticCupCapAt_zero_one` and `TauCeti.symplecticCrossingAt_zero_one`: on two strands
  the two generators are `TauCeti.symplecticCupCap` and `TauCeti.symplecticCrossing`.
* `TauCeti.commute_symplecticCupCapAt_piTensorProductMap`: the generator commutes with the diagonal
  action of every matrix `A` satisfying *both* symplectic identities `Aᵀ * J * A = J` and
  `A * J * Aᵀ = J` -- the cap consumes the first and the cup the second.
* `TauCeti.commute_symplecticCupCapAt_tensorPower` and
  `TauCeti.commute_symplecticCrossingAt_tensorPower`: membership in `Matrix.symplecticGroup`
  records both identities, so both generators commute with the diagonal action of the symplectic
  group and every single-arc diagram acts by an intertwiner.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9, for the action of the Brauer algebra on a tensor power and its role as the
  centralizer of the symplectic group.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, "The invariant form and the action on `V^{⊗k}`", the symplectic case.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ) [CommRing k]

/-- The family of linear maps that `TauCeti.symplecticCupCapAt` pushes through the `d` strands: the
`p`-th coordinate followed by the `x`-th standard basis vector on the strand `i`, the `q`-th
coordinate followed by the `y`-th standard basis vector on the strand `j`, and the identity on
every other strand. This is an implementation detail of `TauCeti.symplecticCupCapAt`, whose
interface is `TauCeti.symplecticCupCapAt_tprod`. -/
private def symplecticCupCapStrand (i j : Fin d) (p q x y : Fin n ⊕ Fin n) (t : Fin d) :
    ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k) :=
  if t = i then (LinearMap.proj p).smulRight (Pi.single x (1 : k))
  else if t = j then (LinearMap.proj q).smulRight (Pi.single y (1 : k))
  else LinearMap.id

/-- **The symplectic Brauer generator `e` on the strands `i` and `j`** of the `d`-th tensor power of
`k^{2n}`: a cap contracting the slots `i` and `j` against the standard alternating form, closed off
by a cup re-expanding those two slots along the bivector of `-J`.

The strand `i` carries the first index of each of the two copies of `J` and the strand `j` the
second, so the definition reads the pair of strands as ordered; that the generator nevertheless
depends only on the unordered pair is `TauCeti.symplecticCupCapAt_comm`. At `i = j` the two strands
coincide, so the cap and the cup land on the same slot and the result is not an arc of a Brauer
diagram; the relations below that read the arc through the alternating form therefore carry the
hypothesis `i ≠ j`, while the strandwise ones hold for coincident strands too. -/
noncomputable def symplecticCupCapAt (i j : Fin d) :
    Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n,
    (-Matrix.J (Fin n) k x y * Matrix.J (Fin n) k p q) •
      PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y)

/-- **The symplectic Brauer crossing `s` on the strands `i` and `j`** of the `d`-th tensor power of
`k^{2n}`: *minus* the permutation exchanging those two tensor factors. The sign is forced by the
alternating form; see the module docstring of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`. -/
noncomputable def symplecticCrossingAt (i j : Fin d) :
    Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  -PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) (Equiv.swap i j)

variable {k n d}

/-! ### Plugging two slots -/

section Plug

omit [CommRing k] in
/-- The first of the two plugged slots. -/
private theorem update_pair_apply_left {i j : Fin d} (v : Fin d → ((Fin n ⊕ Fin n) → k))
    (a b : (Fin n ⊕ Fin n) → k) (hij : i ≠ j) :
    Function.update (Function.update v i a) j b i = a := by
  rw [Function.update_of_ne hij, Function.update_self]

omit [CommRing k] in
/-- The second of the two plugged slots. -/
private theorem update_pair_apply_right {i j : Fin d} (v : Fin d → ((Fin n ⊕ Fin n) → k))
    (a b : (Fin n ⊕ Fin n) → k) :
    Function.update (Function.update v i a) j b j = b :=
  Function.update_self _ _ _

omit [CommRing k] in
/-- Away from the two plugged slots the tuple is unchanged. -/
private theorem update_pair_apply_of_ne {i j t : Fin d} (v : Fin d → ((Fin n ⊕ Fin n) → k))
    (a b : (Fin n ⊕ Fin n) → k) (hi : t ≠ i) (hj : t ≠ j) :
    Function.update (Function.update v i a) j b t = v t := by
  rw [Function.update_of_ne hj, Function.update_of_ne hi]

omit [CommRing k] in
/-- Plugging twice at the same pair of slots keeps only the second plug. -/
private theorem update_pair_update_pair {i j : Fin d} (v : Fin d → ((Fin n ⊕ Fin n) → k))
    (a b c e : (Fin n ⊕ Fin n) → k) :
    Function.update (Function.update (Function.update (Function.update v i a) j b) i c) j e =
      Function.update (Function.update v i c) j e := by
  funext s
  rcases eq_or_ne s j with rfl | hj
  · simp
  · rcases eq_or_ne s i with rfl | hi
    · simp [hj]
    · simp [hi, hj]

end Plug

/-! ### The value on a pure tensor -/

/-- One summand of `TauCeti.symplecticCupCapAt` on a pure tensor. -/
private theorem map_symplecticCupCapStrand_tprod {i j : Fin d} (hij : i ≠ j)
    (p q x y : Fin n ⊕ Fin n) (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y) (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (Function.update
        (Function.update v i (v i p • Pi.single x (1 : k))) j (v j q • Pi.single y (1 : k))) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext t
  by_cases hj : t = j
  · subst hj
    simp [symplecticCupCapStrand, Ne.symm hij]
  · by_cases hi : t = i
    · subst hi
      simp [symplecticCupCapStrand, hj]
    · simp [symplecticCupCapStrand, hi, hj]

/-- **The generator on a pure tensor**: the two chosen factors are contracted against one another
by the standard alternating form, and the two slots are re-expanded along the bivector of `-J`.
Every relation below but the renaming one is proved from this formula; renaming is bookkeeping on
the index set and is read off the definition. -/
@[simp]
theorem symplecticCupCapAt_tprod {i j : Fin d} (hij : i ≠ j)
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticCupCapAt k n d i j (PiTensorProduct.tprod k v) =
      -stdSymplecticBilinForm k n (v i) (v j) •
        ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
  have key : ∀ p q x y : Fin n ⊕ Fin n,
      PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y) (PiTensorProduct.tprod k v) =
        (v i p * v j q) • PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
    intro p q x y
    rw [map_symplecticCupCapStrand_tprod hij]
    conv_lhs => rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm hij,
      (PiTensorProduct.tprod k).map_update_smul, Function.update_comm (Ne.symm hij)]
    rw [smul_smul, mul_comm]
  have hscal : ∀ x y : Fin n ⊕ Fin n,
      ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n,
          (-Matrix.J (Fin n) k x y * Matrix.J (Fin n) k p q) * (v i p * v j q) =
        -stdSymplecticBilinForm k n (v i) (v j) * Matrix.J (Fin n) k x y := by
    intro x y
    rw [stdSymplecticBilinForm_eq_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [symplecticCupCapAt]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, ← hscal x y, Finset.sum_smul]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_smul.symm

/-- Exchanging the two plugged slots of the cup negates it: the bivector of `J` is antisymmetric.
This is the sum form of `TauCeti.symplecticFlip_comp_symplecticCup`, and it is what makes the
generator symmetric in its two strands and absorb the crossing. -/
private theorem sum_J_smul_tprod_update_pair_swap {i j : Fin d}
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single y (1 : k))) j (Pi.single x 1))) =
      -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.J_apply_swap]
  exact neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)) _ _

/-- **The generator depends only on the unordered pair of strands**: the arc joining `i` to `j` is
the arc joining `j` to `i`. Unlike its orthogonal counterpart this is not immediate from the
definition, which reads the pair as ordered; the cap and the cup each change sign under the
exchange, and the two changes cancel. -/
theorem symplecticCupCapAt_comm (i j : Fin d) :
    symplecticCupCapAt k n d i j = symplecticCupCapAt k n d j i := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  refine PiTensorProduct.ext ?_
  ext v
  have hupd : ∀ x y : Fin n ⊕ Fin n,
      PiTensorProduct.tprod k (Function.update
          (Function.update v j (Pi.single x (1 : k))) i (Pi.single y 1)) =
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single y (1 : k))) j (Pi.single x 1)) :=
    fun x y => congrArg _ (Function.update_comm (Ne.symm hij) _ _ v)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod (Ne.symm hij)]
  simp only [hupd]
  rw [sum_J_smul_tprod_update_pair_swap v,
    ((isAlt_stdSymplecticBilinForm k n).neg_eq (v i) (v j)).symm, neg_neg, smul_neg]
  exact neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)) _ _

/-! ### The loop rule -/

/-- The entries of `J` square-sum to `2n`, the dimension of the symplectic space: this is the trace
of `J * Jᵀ = 1`, read one row at a time. -/
private theorem sum_sum_J_mul_J_self :
    ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x y * Matrix.J (Fin n) k x y = (2 * n : k) := by
  rw [Finset.sum_congr rfl fun x _ => Matrix.sum_J_mul_J_self (Fin n) k x, Finset.sum_const,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **The loop rule `e² = δ e`** at the loop value `δ = -2n = -dim V`: stacking the arc on itself
closes a loop in the middle, and a closed loop contracts the pairing `J` against the copairing
`-J`, which is `-tr (J * Jᵀ) = -2n`. -/
theorem symplecticCupCapAt_mul_self {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j * symplecticCupCapAt k n d i j =
      -(2 * n : k) • symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hone : ∀ x y : Fin n ⊕ Fin n, symplecticCupCapAt k n d i j (PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1))) =
      -Matrix.J (Fin n) k x y • ∑ x' : Fin n ⊕ Fin n, ∑ y' : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x' y' • PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x' (1 : k))) j (Pi.single y' 1)) := by
    intro x y
    rw [symplecticCupCapAt_tprod hij, update_pair_apply_left v _ _ hij, update_pair_apply_right,
      stdSymplecticBilinForm_single_single]
    exact congrArg _ (Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ =>
      congrArg _ (congrArg _ (update_pair_update_pair v _ _ _ _)))
  have hJ : ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
      Matrix.J (Fin n) k x y * -Matrix.J (Fin n) k x y = -(2 * n : k) := by
    rw [← sum_sum_J_mul_J_self (k := k) (n := n), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => mul_neg _ _
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, LinearMap.smul_apply, symplecticCupCapAt_tprod hij]
  simp only [map_smul, map_sum, hone, smul_smul, ← Finset.sum_smul]
  rw [hJ]
  ring_nf

/-! ### The crossing on the arc, and the renaming of the arc -/

/-- The crossing swaps the two chosen tensor factors of a pure tensor and changes its sign. -/
@[simp]
theorem symplecticCrossingAt_tprod (i j : Fin d) (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticCrossingAt k n d i j (PiTensorProduct.tprod k v) =
      -PiTensorProduct.tprod k fun t => v (Equiv.swap i j t) := by
  rw [symplecticCrossingAt, LinearMap.neg_apply, PiTensorProduct.reindexRepresentation_apply,
    LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, Equiv.symm_swap]

/-- **The relation `s² = 1`**: the crossing is an involution, the two signs cancelling. -/
@[simp]
theorem symplecticCrossingAt_mul_self (i j : Fin d) :
    symplecticCrossingAt k n d i j * symplecticCrossingAt k n d i j = 1 := by
  have h : symplecticCrossingAt k n d i j * symplecticCrossingAt k n d i j =
      PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) (Equiv.swap i j) *
        PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d)
          (Equiv.swap i j) := by
    refine LinearMap.ext fun z => ?_
    simp only [Module.End.mul_apply, symplecticCrossingAt, LinearMap.neg_apply, map_neg, neg_neg]
  rw [h, ← map_mul, Equiv.swap_mul_self, map_one]

/-- **The relation `s e = e`**: the crossing of the two strands of the arc is absorbed by the cup
on top of the generator, the bivector of `-J` being antisymmetric and the crossing carrying the
compensating sign. -/
theorem symplecticCrossingAt_mul_symplecticCupCapAt {i j : Fin d} (hij : i ≠ j) :
    symplecticCrossingAt k n d i j * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hfix : ∀ x y : Fin n ⊕ Fin n,
      PiTensorProduct.tprod k (fun t => Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1) (Equiv.swap i j t)) =
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single y (1 : k))) j (Pi.single x 1)) := by
    intro x y
    refine congrArg _ (funext fun t => ?_)
    by_cases hi : t = i
    · subst hi
      rw [Equiv.swap_apply_left, update_pair_apply_right, update_pair_apply_left _ _ _ hij]
    · by_cases hj : t = j
      · subst hj
        rw [Equiv.swap_apply_right, update_pair_apply_left _ _ _ hij, update_pair_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj, update_pair_apply_of_ne _ _ _ hi hj,
          update_pair_apply_of_ne _ _ _ hi hj]
  have hS : symplecticCrossingAt k n d i j
        (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
    simp only [map_sum, map_smul, symplecticCrossingAt_tprod, hfix, smul_neg,
      Finset.sum_neg_distrib]
    rw [sum_J_smul_tprod_update_pair_swap v, neg_neg]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, symplecticCupCapAt_tprod hij, map_smul, hS]

/-- **The relation `e s = e`**: the crossing of the two strands of the arc is absorbed by the cap
at the bottom of the generator, the standard alternating form changing sign under the exchange and
the crossing carrying the compensating sign. -/
theorem symplecticCupCapAt_mul_symplecticCrossingAt {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j * symplecticCrossingAt k n d i j =
      symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hw : (fun t => v (Equiv.swap i j t)) =
      Function.update (Function.update v i (v j)) j (v i) := by
    funext t
    rcases eq_or_ne t j with rfl | hj
    · rw [Equiv.swap_apply_right, update_pair_apply_right]
    · rcases eq_or_ne t i with rfl | hi
      · rw [Equiv.swap_apply_left, update_pair_apply_left _ _ _ hij]
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj, update_pair_apply_of_ne _ _ _ hi hj]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, symplecticCrossingAt_tprod, hw, map_neg,
    symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod hij,
    update_pair_apply_left v (v j) (v i) hij, update_pair_apply_right v (v j) (v i)]
  simp only [update_pair_update_pair]
  rw [((isAlt_stdSymplecticBilinForm k n).neg_eq (v i) (v j)).symm, neg_neg]
  exact (neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)) _ _).symm

/-- Renaming the two plugged strands of `TauCeti.symplecticCupCapStrand` along a permutation: the
family for the strands `i` and `j`, read at `σ.symm t`, is the family for the strands `σ i` and
`σ j`, read at `t`. This is the whole content of the renaming relation
`TauCeti.reindexRepresentation_mul_symplecticCupCapAt`. -/
private theorem symplecticCupCapStrand_symm_apply (σ : Equiv.Perm (Fin d)) (i j : Fin d)
    (p q x y : Fin n ⊕ Fin n) (t : Fin d) :
    symplecticCupCapStrand k n d i j p q x y (σ.symm t) =
      symplecticCupCapStrand k n d (σ i) (σ j) p q x y t := by
  simp only [symplecticCupCapStrand, Equiv.symm_apply_eq]

/-- **The renaming relation**: permuting the strands renames the arc. Every mixed relation between
a crossing and a generator is an instance of this one, the sign of the crossing cancelling because
the two sides carry the same copy of it. Renaming is bookkeeping on the index set and does not read
the arc through the alternating form, so it needs no hypothesis on `i` and `j`. -/
theorem reindexRepresentation_mul_symplecticCupCapAt (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) σ *
        symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d (σ i) (σ j) *
        PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) σ := by
  have hstrand : ∀ p q x y : Fin n ⊕ Fin n,
      PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) σ *
          PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y) =
        PiTensorProduct.map (symplecticCupCapStrand k n d (σ i) (σ j) p q x y) *
          PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) σ := by
    intro p q x y
    refine PiTensorProduct.ext ?_
    ext v
    simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply,
      PiTensorProduct.reindexRepresentation_apply, LinearEquiv.coe_coe,
      PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]
    exact congrArg _ (funext fun t =>
      LinearMap.congr_fun (symplecticCupCapStrand_symm_apply σ i j p q x y t) _)
  simp only [symplecticCupCapAt, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    hstrand]

/-- A permutation fixing both strands of the arc commutes with the generator: the mixed relation
between a distant crossing and a generator. -/
theorem commute_reindexRepresentation_symplecticCupCapAt {σ : Equiv.Perm (Fin d)} {i j : Fin d}
    (hi : σ i = i) (hj : σ j = j) :
    Commute (PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d) σ)
      (symplecticCupCapAt k n d i j) := by
  have h := reindexRepresentation_mul_symplecticCupCapAt (k := k) (n := n) σ i j
  rwa [hi, hj] at h

/-! ### Two arcs -/

/-- Two summands of `TauCeti.symplecticCupCapAt` on disjoint pairs of strands commute: at every
strand one of the two families `TauCeti.symplecticCupCapStrand` is the identity, so the two
pointwise composites agree and `PiTensorProduct.map_comp` turns them into the same operator.
Nothing here reads the arc through the alternating form, so the two strands of a pair may
coincide. -/
private theorem commute_map_symplecticCupCapStrand {i j a b : Fin d} (hia : i ≠ a) (hib : i ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) (p q x y p' q' x' y' : Fin n ⊕ Fin n) :
    Commute (PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y))
      (PiTensorProduct.map (symplecticCupCapStrand k n d a b p' q' x' y')) := by
  have hstrand : (fun t => symplecticCupCapStrand k n d i j p q x y t ∘ₗ
        symplecticCupCapStrand k n d a b p' q' x' y' t) =
      fun t => symplecticCupCapStrand k n d a b p' q' x' y' t ∘ₗ
        symplecticCupCapStrand k n d i j p q x y t := by
    funext t
    rcases eq_or_ne t i with rfl | hi
    · simp [symplecticCupCapStrand, hia, hib]
    · rcases eq_or_ne t j with rfl | hj
      · simp [symplecticCupCapStrand, hi, hja, hjb]
      · simp [symplecticCupCapStrand, hi, hj]
  have hmul : (PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y) :
        Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k))) *
        PiTensorProduct.map (symplecticCupCapStrand k n d a b p' q' x' y') =
      PiTensorProduct.map (symplecticCupCapStrand k n d a b p' q' x' y') *
        PiTensorProduct.map (symplecticCupCapStrand k n d i j p q x y) := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp, hstrand]
  exact hmul

/-- **Disjoint arcs commute**: two generators whose pairs of strands are disjoint act in disjoint
groups of slots. The two strands of either pair may coincide, since the proof never reads an arc
through the alternating form: it only needs each strand to be touched by at most one of the two
generators. -/
theorem commute_symplecticCupCapAt_of_disjoint {i j a b : Fin d} (hia : i ≠ a) (hib : i ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) :
    Commute (symplecticCupCapAt k n d i j) (symplecticCupCapAt k n d a b) := by
  rw [symplecticCupCapAt, symplecticCupCapAt]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_left _ _ _ fun y _ =>
    Commute.sum_left _ _ _ fun p _ => Commute.sum_left _ _ _ fun q _ =>
      Commute.sum_right _ _ _ fun x' _ => Commute.sum_right _ _ _ fun y' _ =>
        Commute.sum_right _ _ _ fun p' _ => Commute.sum_right _ _ _ fun q' _ =>
          ((commute_map_symplecticCupCapStrand hia hib hja hjb p q x y p' q' x' y').smul_left
            _).smul_right _

/-- **Two arcs sharing one strand**: `e i j * e j l * e i j = e i j`, the relation that makes two
generators on overlapping pairs absorb one another. The two sides carry the same sign, although
each of the three generators on the left carries one of its own: the shared strand `j` is
contracted twice, `Matrix.J_squared` makes each of those two contractions contribute a further
sign, and of the five signs four cancel in pairs, leaving the one that `e i j` carries. -/
theorem symplecticCupCapAt_mul_mul_self {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) :
    symplecticCupCapAt k n d i j * symplecticCupCapAt k n d j l * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  -- The middle generator reads the plugged strand `j` against the untouched strand `l`, and
  -- replants those two strands; the plug at `i` survives, `i` being neither `j` nor `l`.
  have hmid : ∀ x y : Fin n ⊕ Fin n, symplecticCupCapAt k n d j l (PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1))) =
      (-((Matrix.J (Fin n) k *ᵥ v l) y)) • ∑ x' : Fin n ⊕ Fin n, ∑ y' : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k x' y' • PiTensorProduct.tprod k (Function.update (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single x' 1))
          l (Pi.single y' 1)) := by
    intro x y
    rw [symplecticCupCapAt_tprod hjl, update_pair_apply_right,
      update_pair_apply_of_ne _ _ _ (Ne.symm hil) (Ne.symm hjl), stdSymplecticBilinForm_apply,
      single_dotProduct, one_mul]
    simp only [Function.update_idem]
  -- The outer generator contracts the two plugged strands `i` and `j` against one another and
  -- replants them; the plug at `l` survives, `l` being neither `i` nor `j`.
  have hout : ∀ x x' y' : Fin n ⊕ Fin n, symplecticCupCapAt k n d i j (PiTensorProduct.tprod k
        (Function.update (Function.update (Function.update v i (Pi.single x (1 : k))) j
          (Pi.single x' 1)) l (Pi.single y' 1))) =
      (-Matrix.J (Fin n) k x x') • ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update (Function.update
          (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
          l (Pi.single y' 1)) := by
    intro x x' y'
    have hi' : Function.update (Function.update (Function.update v i (Pi.single x (1 : k))) j
        (Pi.single x' 1)) l (Pi.single y' 1) i = Pi.single x (1 : k) := by
      rw [Function.update_of_ne hil, update_pair_apply_left _ _ _ hij]
    have hj' : Function.update (Function.update (Function.update v i (Pi.single x (1 : k))) j
        (Pi.single x' 1)) l (Pi.single y' 1) j = Pi.single x' (1 : k) := by
      rw [Function.update_of_ne hjl, update_pair_apply_right]
    have hplug : ∀ f g : Fin n ⊕ Fin n, Function.update (Function.update (Function.update
          (Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single x' 1))
          l (Pi.single y' 1)) i (Pi.single f (1 : k))) j (Pi.single g 1) =
        Function.update (Function.update (Function.update v i (Pi.single f (1 : k))) j
          (Pi.single g 1)) l (Pi.single y' 1) := by
      intro f g
      funext t
      by_cases h1 : t = i <;> by_cases h2 : t = j <;> by_cases h3 : t = l <;> simp_all
    rw [symplecticCupCapAt_tprod hij, hi', hj', stdSymplecticBilinForm_single_single]
    exact congrArg _ (Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ =>
      congrArg _ (congrArg _ (hplug f g)))
  -- Stacking the two: the cup of the first generator and the cap of the third are contracted
  -- against the cup of the middle one, and `J * J = -1` collapses that sum, forcing the strand
  -- `l` to carry the basis vector the first cup put on the strand `i`.
  have hstep : ∀ x y : Fin n ⊕ Fin n, symplecticCupCapAt k n d i j (symplecticCupCapAt k n d j l
        (PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)))) =
      (-((Matrix.J (Fin n) k *ᵥ v l) y)) • ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n,
        Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update (Function.update
          (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
          l (Pi.single x 1)) := by
    intro x y
    have hcol : ∀ y' : Fin n ⊕ Fin n,
        (∑ x' : Fin n ⊕ Fin n, Matrix.J (Fin n) k x' y' * -Matrix.J (Fin n) k x x') =
          if x = y' then (1 : k) else 0 := by
      intro y'
      have hJ := congrFun (congrFun (Matrix.J_squared (Fin n) k) x) y'
      simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply] at hJ
      rw [Finset.sum_congr rfl fun x' _ => (by ring :
          Matrix.J (Fin n) k x' y' * -Matrix.J (Fin n) k x x' =
            -(Matrix.J (Fin n) k x x' * Matrix.J (Fin n) k x' y')),
        Finset.sum_neg_distrib, hJ, neg_neg]
    have hinner : ∀ y' : Fin n ⊕ Fin n,
        (∑ x' : Fin n ⊕ Fin n, (Matrix.J (Fin n) k x' y' * -Matrix.J (Fin n) k x x') •
            ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n, Matrix.J (Fin n) k f g •
              PiTensorProduct.tprod k (Function.update (Function.update
                (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
                l (Pi.single y' 1))) =
          (if x = y' then (1 : k) else 0) • ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n,
            Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
              l (Pi.single y' 1)) :=
      fun y' => by rw [← Finset.sum_smul, hcol y']
    rw [hmid x y, map_smul]
    refine congrArg _ ?_
    simp only [map_sum, map_smul, hout, smul_smul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun y' _ => hinner y']
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, reduceIte]
  -- The last contraction of the shared strand restores the `l`-th entry of `v`: `J * J = -1` once
  -- more, against the cup of the first generator.
  have hvec : ∀ x : Fin n ⊕ Fin n, (∑ y : Fin n ⊕ Fin n,
      Matrix.J (Fin n) k x y * -((Matrix.J (Fin n) k *ᵥ v l) y)) = v l x := by
    intro x
    have hJ : (Matrix.J (Fin n) k *ᵥ Matrix.J (Fin n) k *ᵥ v l) x = -(v l x) := by
      rw [Matrix.mulVec_mulVec, Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec,
        Pi.neg_apply]
    rw [Matrix.mulVec_apply_eq_sum] at hJ
    rw [Finset.sum_congr rfl fun y _ => (by ring : Matrix.J (Fin n) k x y *
        -((Matrix.J (Fin n) k *ᵥ v l) y) =
          -(Matrix.J (Fin n) k x y * (Matrix.J (Fin n) k *ᵥ v l) y)),
      Finset.sum_neg_distrib, hJ, neg_neg]
  -- Summing the surviving basis vector on the strand `l` against the `l`-th entry of `v` rebuilds
  -- that strand.
  have hrestore : ∀ f g : Fin n ⊕ Fin n, (∑ z : Fin n ⊕ Fin n, v l z •
        PiTensorProduct.tprod k (Function.update (Function.update
          (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1)) l (Pi.single z 1))) =
      PiTensorProduct.tprod k (Function.update
        (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1)) := by
    intro f g
    -- The slot `l` is untouched by the plug at `i` and `j`, so rewriting `v l` backwards along
    -- this identity turns the reassembled sum into a plug of the tuple's own `l`-th entry.
    have hplugged : Function.update (Function.update v i (Pi.single f (1 : k))) j
        (Pi.single g 1) l = v l :=
      update_pair_apply_of_ne _ _ _ (Ne.symm hil) (Ne.symm hjl)
    rw [Finset.sum_congr rfl fun z _ => ((PiTensorProduct.tprod k).map_update_smul
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1)) l (v l z)
        (Pi.single z (1 : k))).symm,
      ← (PiTensorProduct.tprod k).map_update_sum, ← pi_eq_sum_univ' (v l), ← hplugged,
      Function.update_eq_self]
  have hS : symplecticCupCapAt k n d i j (symplecticCupCapAt k n d j l
        (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
          PiTensorProduct.tprod k (Function.update
            (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
    have hcollapse : ∀ z : Fin n ⊕ Fin n,
        (∑ y : Fin n ⊕ Fin n, (Matrix.J (Fin n) k z y *
            -((Matrix.J (Fin n) k *ᵥ v l) y)) • ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n,
              Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update (Function.update
                (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
                l (Pi.single z 1))) =
          v l z • ∑ f : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n, Matrix.J (Fin n) k f g •
            PiTensorProduct.tprod k (Function.update (Function.update
              (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
              l (Pi.single z 1)) :=
      fun z => by rw [← Finset.sum_smul, hvec z]
    have hpull : ∀ f g : Fin n ⊕ Fin n, (∑ z : Fin n ⊕ Fin n, v l z • (Matrix.J (Fin n) k f g •
          PiTensorProduct.tprod k (Function.update (Function.update
            (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
            l (Pi.single z 1)))) =
        Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1)) := by
      intro f g
      rw [← hrestore f g, Finset.smul_sum]
      exact Finset.sum_congr rfl fun z _ => smul_comm _ _ _
    have hswap : ∀ f : Fin n ⊕ Fin n, (∑ z : Fin n ⊕ Fin n, ∑ g : Fin n ⊕ Fin n,
          v l z • (Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update
            (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
            l (Pi.single z 1)))) =
        ∑ g : Fin n ⊕ Fin n, ∑ z : Fin n ⊕ Fin n,
          v l z • (Matrix.J (Fin n) k f g • PiTensorProduct.tprod k (Function.update
            (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single g 1))
            l (Pi.single z 1))) :=
      fun _ => Finset.sum_comm
    simp only [map_sum, map_smul, hstep, smul_smul]
    rw [Finset.sum_congr rfl fun z _ => hcollapse z]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun f _ => hswap f,
      Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => hpull f g]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, symplecticCupCapAt_tprod hij, map_smul, map_smul,
    hS]

/-! ### The arc as an intertwiner -/

/-- The cup, with its two slots plugged one row of `J` at a time rather than one entry at a time:
summing the inner index against the standard basis reassembles the row. -/
private theorem sum_sum_J_smul_tprod_eq_sum_row {i j : Fin d}
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1))) =
      ∑ x : Fin n ⊕ Fin n, PiTensorProduct.tprod k (Function.update
        (Function.update v i (Pi.single x (1 : k))) j (Matrix.J (Fin n) k x)) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [pi_eq_sum_univ' (Matrix.J (Fin n) k x),
    (PiTensorProduct.tprod k).map_update_sum]
  exact Finset.sum_congr rfl fun y _ =>
    ((PiTensorProduct.tprod k).map_update_smul _ j (Matrix.J (Fin n) k x y) _).symm

/-- **The cup at two slots is invariant** under every matrix `A` with `A * J * Aᵀ = J`: pushing `A`
through both plugged slots rewrites the bivector of `J` by `A J Aᵀ`, which is `J` again. This is
the general-slot form of `TauCeti.piTensorProductMap_comp_symplecticCup`. -/
private theorem sum_sum_J_smul_tprod_update_pair_mulVec
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k) {i j : Fin d} (hij : i ≠ j)
    (u : Fin d → ((Fin n ⊕ Fin n) → k)) :
    (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Pi.single y 1))) =
      ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y •
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (Pi.single x (1 : k))) j (Pi.single y 1)) := by
  have hmv : ∀ c a : Fin n ⊕ Fin n, (A *ᵥ Pi.single c (1 : k)) a = A a c := by
    intro c a
    rw [Matrix.mulVec, dotProduct_single, mul_one]
  have hrow : ∀ a : Fin n ⊕ Fin n,
      (∑ x : Fin n ⊕ Fin n, A a x • (A *ᵥ Matrix.J (Fin n) k x)) = Matrix.J (Fin n) k a := by
    intro a
    funext b
    have h := congrFun (congrFun hA a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at h
    have hgoal : (∑ x : Fin n ⊕ Fin n, A a x • (A *ᵥ Matrix.J (Fin n) k x)) b =
        ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
          A a x * Matrix.J (Fin n) k x y * A b y := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hgoal, Finset.sum_comm]
    exact h
  -- Reassemble the inner sum into a row of `J` on both sides, then expand the slot `i`.
  rw [sum_sum_J_smul_tprod_eq_sum_row (i := i) (j := j) u]
  have hleft : ∀ x : Fin n ⊕ Fin n,
      (∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) k x y • PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Pi.single y 1))) =
        PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Matrix.J (Fin n) k x)) := by
    intro x
    conv_rhs => rw [pi_eq_sum_univ' (Matrix.J (Fin n) k x), Matrix.mulVec_sum]
    rw [(PiTensorProduct.tprod k).map_update_sum]
    exact Finset.sum_congr rfl fun y _ => by
      rw [Matrix.mulVec_smul, (PiTensorProduct.tprod k).map_update_smul]
  rw [Finset.sum_congr rfl fun x _ => hleft x]
  have hexp : ∀ x : Fin n ⊕ Fin n,
      PiTensorProduct.tprod k (Function.update
          (Function.update u i (A *ᵥ Pi.single x (1 : k))) j (A *ᵥ Matrix.J (Fin n) k x)) =
        ∑ a : Fin n ⊕ Fin n, A a x • PiTensorProduct.tprod k (Function.update
          (Function.update u i (Pi.single a (1 : k))) j (A *ᵥ Matrix.J (Fin n) k x)) := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' (A *ᵥ Pi.single x (1 : k)), Function.update_comm hij,
      (PiTensorProduct.tprod k).map_update_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm (Ne.symm hij), hmv]
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [← hrow a, (PiTensorProduct.tprod k).map_update_sum]
  exact Finset.sum_congr rfl fun x _ =>
    ((PiTensorProduct.tprod k).map_update_smul _ j (A a x) _).symm

/-- **The generator commutes with the diagonal action of a two-sidedly symplectic matrix**: the cap
consumes `Aᵀ * J * A = J`, which is exactly preservation of the standard alternating form, and the
cup consumes `A * J * Aᵀ = J`. Mathlib's `Matrix.symplecticGroup` records both
(`SymplecticGroup.mem_iff'` and `SymplecticGroup.mem_iff`), which is how
`TauCeti.commute_symplecticCupCapAt_tensorPower` discharges them. -/
theorem commute_symplecticCupCapAt_piTensorProductMap
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k)
    (hA' : A * Matrix.J (Fin n) k * Aᵀ = Matrix.J (Fin n) k) {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j)
      (PiTensorProduct.map fun _ : Fin d => Matrix.mulVecLin A) := by
  refine PiTensorProduct.ext ?_
  ext v
  have hcap : stdSymplecticBilinForm k n (A *ᵥ v i) (A *ᵥ v j) =
      stdSymplecticBilinForm k n (v i) (v j) := by
    rw [stdSymplecticBilinForm_apply, stdSymplecticBilinForm_apply, Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.mul_assoc, hA, ← Matrix.dotProduct_mulVec]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, PiTensorProduct.map_tprod,
    symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod hij, map_smul, map_sum]
  simp only [Matrix.mulVecLin_apply]
  rw [hcap]
  refine congrArg _ ?_
  rw [← sum_sum_J_smul_tprod_update_pair_mulVec hA' hij fun t => A *ᵥ v t]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, PiTensorProduct.map_tprod]
  simp only [Matrix.mulVecLin_apply]
  refine congrArg _ (congrArg _ (funext fun t => ?_))
  by_cases hj : t = j
  · subst hj
    rw [update_pair_apply_right, Function.update_self]
  · by_cases hi : t = i
    · subst hi
      rw [update_pair_apply_left _ _ _ hij, Function.update_of_ne hj, Function.update_self]
    · rw [update_pair_apply_of_ne _ _ _ hi hj, Function.update_of_ne hj, Function.update_of_ne hi]

/-! ### The two-strand case -/

/-- On two strands the generator is `TauCeti.symplecticCupCap`, the composite `cup ∘ₗ cap` through
the tensor square. -/
theorem symplecticCupCapAt_zero_one :
    symplecticCupCapAt k n 2 0 1 = symplecticCupCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  have hv : ∀ x y : Fin n ⊕ Fin n,
      PiTensorProduct.tprod k (Function.update
          (Function.update v 0 (Pi.single x (1 : k))) 1 (Pi.single y 1)) =
        PiTensorProduct.tprod k ![Pi.single x (1 : k), Pi.single y (1 : k)] := by
    intro x y
    refine congrArg _ (funext fun t => ?_)
    fin_cases t <;> simp
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    symplecticCupCapAt_tprod (by decide : (0 : Fin 2) ≠ 1), symplecticCupCap_apply,
    symplecticCap_tprod, symplecticCup_apply]
  simp only [hv]
  exact (neg_smul (M := ⨂[k]^2 ((Fin n ⊕ Fin n) → k)) _ _).trans (smul_neg _ _).symm

/-- On two strands the crossing is `TauCeti.symplecticCrossing`, minus the flip of the two tensor
factors. -/
theorem symplecticCrossingAt_zero_one :
    symplecticCrossingAt k n 2 0 1 = symplecticCrossing k n := by
  refine PiTensorProduct.ext ?_
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    symplecticCrossingAt_tprod, symplecticCrossing_tprod]
  refine congrArg Neg.neg (congrArg _ (funext fun t => ?_))
  fin_cases t <;> simp [Equiv.swap_apply_def]

/-! ### The symplectic group -/

/-- **Every single-arc Brauer diagram acts by an intertwiner**: the generator commutes with the
diagonal action of the symplectic group on the `d`-th tensor power, membership in the group
supplying both symplectic identities that
`TauCeti.commute_symplecticCupCapAt_piTensorProductMap` asks for. The two-strand case is
`TauCeti.commute_symplecticCupCap_tensorPower`. -/
theorem commute_symplecticCupCapAt_tensorPower (g : Matrix.symplecticGroup (Fin n) k)
    {i j : Fin d} (hij : i ≠ j) :
    Commute (symplecticCupCapAt k n d i j) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_symplecticCupCapAt_piTensorProductMap
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop)
      ((SymplecticGroup.mem_iff (l := Fin n) (R := k)).mp g.prop) hij

/-- **The crossing acts by an intertwiner**: permuting two tensor factors commutes with applying
the same matrix in each of them, and the sign is central. The two-strand case is
`TauCeti.commute_symplecticCrossing_tensorPower`. -/
theorem commute_symplecticCrossingAt_tensorPower (g : Matrix.symplecticGroup (Fin n) k)
    (i j : Fin d) :
    Commute (symplecticCrossingAt k n d i j) ((stdSymplecticRep k n).tensorPower d g) := by
  have h := PiTensorProduct.commute_reindexRepresentation_map k ((Fin n ⊕ Fin n) → k) (Fin d)
    (Equiv.swap i j) (Matrix.mulVecLin (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k))
  rw [Representation.tensorPower_apply, stdSymplecticRep_apply]
  refine LinearMap.ext fun z => ?_
  have hz := LinearMap.congr_fun h z
  simp only [Module.End.mul_apply] at hz ⊢
  simp only [symplecticCrossingAt, LinearMap.neg_apply, map_neg, hz]

end TauCeti
