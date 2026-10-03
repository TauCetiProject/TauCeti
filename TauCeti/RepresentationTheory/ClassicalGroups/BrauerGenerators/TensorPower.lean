/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal

/-!
# The Brauer generators on a tensor power, and the relations they satisfy

A Brauer diagram on `d` strands acts on the `d`-th tensor power of `V = kⁿ` by permuting the slots
along its through strands, contracting each pair of bottom points against the coordinate dot
product, and expanding each pair of top points through the dual copairing. The horizontal arcs are
therefore all built from the *single-arc* diagrams: a cap on the two bottom points `i` and `j`,
closed off by a cup on the two top points `i` and `j`. This file builds that operator on the `d`-th
tensor power, `TauCeti.orthogonalCupCapAt`, and proves the relations it satisfies, which is what an
algebra homomorphism out of the Brauer algebra has to check.

The two-strand case is `TauCeti.orthogonalCupCap` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Orthogonal.lean`, which this file
reproduces at `d = 2` (`TauCeti.orthogonalCupCapAt_zero_one`). There the generator is assembled as
a composite `cup ∘ₗ cap` through the tensor square, a route unavailable for a pair of strands
sitting inside a larger tensor power, because splitting two of the `d` slots off a tensor power is
not an equality of tensor powers. The operator here is instead built in one step, by pushing the
`a`-th coordinate followed by the `c`-th basis vector through the two chosen strands and the
identity through all the others, and summing over `a` and `c`: the sum over `a` is the cap, which
contracts the two slots coordinatewise, and the sum over `c` is the cup, which re-expands them
diagonally.

## The relations

Writing `e i j` for the generator and `s σ` for the permutation action
`TauCeti.permTensorAction` of the symmetric group on the tensor factors, the relations proved
here are

* `e i j * e i j = n • e i j`, the loop rule at the loop value `δ = n = dim V`;
* `s (Equiv.swap i j) * e i j = e i j` and `e i j * s (Equiv.swap i j) = e i j`, the two
  absorptions of the crossing on the arc;
* `s σ * e i j = e (σ i) (σ j) * s σ`, the renaming of the arc by a permutation of the strands;
* `e i j * e a b = e a b * e i j` for two disjoint arcs;
* `e i j * e j l * e i j = e i j` for two arcs sharing exactly one strand.

Together with `s` being a monoid homomorphism — which already gives `s σ * s τ = s (σ * τ)`, hence
`s² = 1` for a transposition and the braid relations — these are the defining relations of the
Brauer algebra `B_d(n)`, and the renaming relation specializes to the mixed relation
`s σ * e i j = e i j * s σ` whenever `σ` fixes both `i` and `j`
(`TauCeti.commute_permTensorAction_orthogonalCupCapAt`). They are the tensor-power mirror of the
diagram-level relations of `TauCeti/Combinatorics/Brauer/Generator.lean` and
`TauCeti/Combinatorics/Brauer/Relations.lean`, which prove the same identities for the stacking of
Brauer diagrams and its middle-loop count.

The generator and all five relations need no subtraction and no inverses, so they are stated over a
commutative semiring; only the orthogonal group itself, and hence the closing commutation theorem,
needs a commutative ring. Everything here is the symmetric (orthogonal) form: the arc is an
unordered pair of strands (`TauCeti.orthogonalCupCapAt_comm`), which is exactly what fails for an
alternating form, so the symplectic mirror is not a relabelling of this file but needs a chosen
ordering of each arc.

## Implementation notes

Every proof here reduces to the same piece of plumbing: the tuple obtained from `v` by setting the
two slots `i` and `j` to the `c`-th standard basis vector of `kⁿ`, spelled as a pair of nested
`Function.update`s. The four `update_pair_*` lemmas read its three kinds of entry and compose two
such plugs; they are `private` because they are steps of this file's argument, specific to the
shape the cup produces, and say nothing about tensor powers. The one genuinely linear-algebraic
step, `tprod_update_pair_expand`, expands those two slots in the standard basis and is what both
the overlapping relation and the invariance of the cup run on; it too is `private`, having no use
outside this file.

## Main definitions

* `TauCeti.orthogonalCupCapAt`: the Brauer generator `e i j` on the `d`-th tensor power of `kⁿ`.

## Main results

* `TauCeti.orthogonalCupCapAt_tprod`: the value of the generator on a pure tensor, the formula
  every proof below runs on.
* `TauCeti.orthogonalCupCapAt_self_tprod`: the degenerate value at `i = j`, which is a rank-one
  map at the single slot and not a self-contraction, so it is not an arc.
* `TauCeti.orthogonalCupCapAt_comm`: the generator depends only on the unordered pair of strands.
* `TauCeti.orthogonalCupCapAt_mul_self`, `TauCeti.permTensorAction_swap_mul_orthogonalCupCapAt`,
  `TauCeti.orthogonalCupCapAt_mul_permTensorAction_swap`,
  `TauCeti.permTensorAction_mul_orthogonalCupCapAt`,
  `TauCeti.commute_orthogonalCupCapAt_of_disjoint` and
  `TauCeti.orthogonalCupCapAt_mul_mul_self`: the five relations listed above, with
  `TauCeti.commute_permTensorAction_orthogonalCupCapAt` the distant-crossing case of the renaming
  relation.
* `TauCeti.orthogonalCupCapAt_zero_one`: on two strands the generator is
  `TauCeti.orthogonalCupCap`.
* `TauCeti.commute_orthogonalCupCapAt_piTensorProductMap` and
  `TauCeti.commute_orthogonalCupCapAt_tensorPower`: the generator commutes with every matrix
  preserving the dot product, hence with the diagonal action of the orthogonal group, so every
  single-arc diagram acts by an intertwiner.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 9, for the action of the Brauer algebra on a tensor power and its role as the
  centralizer of the orthogonal group.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommSemiring

variable [CommSemiring k]

/-- The family of linear maps that `TauCeti.orthogonalCupCapAt` pushes through the `d` strands: the
`a`-th coordinate followed by the `c`-th standard basis vector on the two strands `i` and `j`, and
the identity on every other strand. This is an implementation detail of
`TauCeti.orthogonalCupCapAt`, whose interface is `TauCeti.orthogonalCupCapAt_tprod`. -/
private def cupCapStrand (i j : Fin d) (a c : Fin n) (t : Fin d) :
    (Fin n → k) →ₗ[k] (Fin n → k) :=
  if t = i ∨ t = j then (LinearMap.proj a).smulRight (Pi.single c (1 : k)) else LinearMap.id

/-- **The Brauer generator `e` on the strands `i` and `j`** of the `d`-th tensor power of `kⁿ`: a
cap contracting the slots `i` and `j` against the coordinate dot product, closed off by a cup
re-expanding those two slots as `∑_c e_c ⊗ e_c`.

At `i = j` the two strands coincide, so the cap and the cup land on the same slot and the result is
not an arc of a Brauer diagram: it is not a contraction of the slot `i` against itself, which would
be quadratic rather than linear, but the rank-one map replacing that slot by the sum of its
coordinates times the all-ones vector (`TauCeti.orthogonalCupCapAt_self_tprod`). Every relation
below therefore carries the hypothesis `i ≠ j`. -/
noncomputable def orthogonalCupCapAt (i j : Fin d) : Module.End k (⨂[k]^d (Fin n → k)) :=
  ∑ a : Fin n, ∑ c : Fin n,
    PiTensorProduct.lift ((PiTensorProduct.tprod k).compLinearMap (cupCapStrand k n d i j a c))

variable {k n d}

/-! ### The value on a pure tensor -/

section Plug

variable {i j t : Fin d} {c e : Fin n} (v : Fin d → (Fin n → k))

/-- The first of the two plugged slots. -/
private theorem update_pair_apply_left (hij : i ≠ j) :
    Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1) i =
      Pi.single c (1 : k) := by
  rw [Function.update_of_ne hij, Function.update_self]

/-- The second of the two plugged slots. -/
private theorem update_pair_apply_right :
    Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1) j =
      Pi.single c (1 : k) :=
  Function.update_self _ _ _

/-- Away from the two plugged slots the tuple is unchanged. -/
private theorem update_pair_apply_of_ne (hi : t ≠ i) (hj : t ≠ j) :
    Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1) t = v t := by
  rw [Function.update_of_ne hj, Function.update_of_ne hi]

/-- Plugging twice at the same pair of slots keeps only the second plug. -/
private theorem update_pair_update_pair (hij : i ≠ j) :
    Function.update (Function.update
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
        i (Pi.single e (1 : k))) j (Pi.single e 1) =
      Function.update (Function.update v i (Pi.single e (1 : k))) j (Pi.single e 1) := by
  funext t
  rcases eq_or_ne t j with hj | hj
  · subst hj
    simp
  · rcases eq_or_ne t i with hi | hi
    · subst hi
      simp [hij]
    · simp [hi, hj]

end Plug

/-- **The bilinear expansion at two slots**: a pure tensor whose slots `i` and `j` carry arbitrary
vectors is the standard-basis expansion of those two slots. -/
private theorem tprod_update_pair_expand {i j : Fin d} (hij : i ≠ j) (u : Fin d → (Fin n → k))
    (x y : Fin n → k) :
    PiTensorProduct.tprod k (Function.update (Function.update u i x) j y) =
      ∑ a : Fin n, ∑ b : Fin n, (x a * y b) • PiTensorProduct.tprod k
        (Function.update (Function.update u i (Pi.single a (1 : k))) j (Pi.single b 1)) := by
  calc PiTensorProduct.tprod k (Function.update (Function.update u i x) j y)
      = PiTensorProduct.tprod k (Function.update (Function.update u i
          (∑ a : Fin n, x a • Pi.single a (1 : k))) j
            (∑ b : Fin n, y b • Pi.single b (1 : k))) := by
        rw [← pi_eq_sum_univ' x, ← pi_eq_sum_univ' y]
    _ = ∑ b : Fin n, ∑ a : Fin n, (x a * y b) • PiTensorProduct.tprod k
          (Function.update (Function.update u i (Pi.single a (1 : k))) j (Pi.single b 1)) := by
        rw [(PiTensorProduct.tprod k).map_update_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm hij,
          (PiTensorProduct.tprod k).map_update_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm (Ne.symm hij),
          smul_smul, mul_comm]
    _ = _ := Finset.sum_comm

/-- One summand of `TauCeti.orthogonalCupCapAt` on a pure tensor. -/
private theorem orthogonalCupCapAt_lift_tprod (i j : Fin d) (a c : Fin n)
    (v : Fin d → (Fin n → k)) :
    PiTensorProduct.lift ((PiTensorProduct.tprod k).compLinearMap (cupCapStrand k n d i j a c))
        (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (Function.update
        (Function.update v i (v i a • Pi.single c (1 : k))) j (v j a • Pi.single c (1 : k))) := by
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply]
  congr 1
  funext t
  by_cases hj : t = j
  · subst hj
    simp [cupCapStrand]
  · by_cases hi : t = i
    · subst hi
      simp [cupCapStrand, hj]
    · simp [cupCapStrand, hi, hj]

/-- **The generator on a pure tensor**: the two chosen factors are contracted against one another
by the dot product, and both slots are replaced by the `c`-th standard basis vector, summed over
`c`. Every relation below is proved from this formula. -/
theorem orthogonalCupCapAt_tprod {i j : Fin d} (hij : i ≠ j) (v : Fin d → (Fin n → k)) :
    orthogonalCupCapAt k n d i j (PiTensorProduct.tprod k v) =
      (v i ⬝ᵥ v j) • ∑ c : Fin n, PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1)) := by
  have key : ∀ a c : Fin n,
      PiTensorProduct.tprod k (Function.update
          (Function.update v i (v i a • Pi.single c (1 : k))) j (v j a • Pi.single c (1 : k))) =
        (v i a * v j a) • PiTensorProduct.tprod k
          (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1)) := by
    intro a c
    conv_lhs => rw [(PiTensorProduct.tprod k).map_update_smul, Function.update_comm hij,
      (PiTensorProduct.tprod k).map_update_smul, Function.update_comm (Ne.symm hij)]
    rw [smul_smul, mul_comm]
  rw [orthogonalCupCapAt]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    (orthogonalCupCapAt_lift_tprod i j a c v).trans (key a c), Finset.sum_comm]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  rfl

/-- **The degenerate value at coincident strands**: at `i = j` the cap and the cup land on the
same slot, and `TauCeti.orthogonalCupCapAt k n d i i` is *not* the contraction of that slot against
itself — which would be quadratic in `v i`, not linear — but the rank-one map replacing it by
`(∑ a, v i a) • 1`. This is why the arc relations all assume `i ≠ j`. -/
theorem orthogonalCupCapAt_self_tprod (i : Fin d) (v : Fin d → (Fin n → k)) :
    orthogonalCupCapAt k n d i i (PiTensorProduct.tprod k v) =
      (∑ a : Fin n, v i a) • ∑ c : Fin n, PiTensorProduct.tprod k
        (Function.update v i (Pi.single c (1 : k))) := by
  have key : ∀ a c : Fin n,
      PiTensorProduct.lift ((PiTensorProduct.tprod k).compLinearMap (cupCapStrand k n d i i a c))
          (PiTensorProduct.tprod k v) =
        v i a • PiTensorProduct.tprod k (Function.update v i (Pi.single c (1 : k))) := by
    intro a c
    rw [orthogonalCupCapAt_lift_tprod, Function.update_idem,
      (PiTensorProduct.tprod k).map_update_smul]
  rw [orthogonalCupCapAt]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => key a c, Finset.sum_comm,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_smul.symm

/-- The generator depends only on the unordered pair of strands: the arc joining `i` to `j` is the
arc joining `j` to `i`. -/
theorem orthogonalCupCapAt_comm (i j : Fin d) :
    orthogonalCupCapAt k n d i j = orthogonalCupCapAt k n d j i := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  refine PiTensorProduct.ext ?_
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    orthogonalCupCapAt_tprod hij, orthogonalCupCapAt_tprod (Ne.symm hij),
    dotProduct_comm (v j) (v i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ (Function.update_comm hij _ _ v))

/-! ### The loop rule -/

/-- **The loop rule `e² = δ e`** at the loop value `δ = n = dim V`: stacking the arc on itself
closes a loop in the middle, and a closed loop evaluates to the trace `n` of the dot product. -/
theorem orthogonalCupCapAt_mul_self {i j : Fin d} (hij : i ≠ j) :
    orthogonalCupCapAt k n d i j * orthogonalCupCapAt k n d i j =
      (n : k) • orthogonalCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hone : ∀ c : Fin n, orthogonalCupCapAt k n d i j (PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))) =
      ∑ e : Fin n, PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single e (1 : k))) j (Pi.single e 1)) := by
    intro c
    rw [orthogonalCupCapAt_tprod hij, update_pair_apply_left v hij, update_pair_apply_right v,
      show (Pi.single c (1 : k) : Fin n → k) ⬝ᵥ Pi.single c (1 : k) = 1 by simp, one_smul]
    exact Finset.sum_congr rfl fun e _ => congrArg _ (update_pair_update_pair v hij)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, LinearMap.smul_apply, orthogonalCupCapAt_tprod hij, map_smul, map_sum,
    Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul k, smul_comm]

/-! ### The crossing on the arc, and the renaming of the arc -/

/-- **The relation `s e = e`**: the crossing of the two strands of the arc is absorbed by the cup
on top of the generator. -/
theorem permTensorAction_swap_mul_orthogonalCupCapAt {i j : Fin d} (hij : i ≠ j) :
    permTensorAction k n d (Equiv.swap i j) * orthogonalCupCapAt k n d i j =
      orthogonalCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  have hfix : ∀ c : Fin n, (fun t => Function.update
        (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1) ((Equiv.swap i j).symm t)) =
      Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1) := by
    intro c
    funext t
    rw [Equiv.symm_swap]
    by_cases hi : t = i
    · subst hi
      rw [Equiv.swap_apply_left, update_pair_apply_right v, update_pair_apply_left v hij]
    · by_cases hj : t = j
      · subst hj
        rw [Equiv.swap_apply_right, update_pair_apply_left v hij, update_pair_apply_right v]
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, orthogonalCupCapAt_tprod hij, map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [permTensorAction_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod, hfix c]

/-- **The relation `e s = e`**: the crossing of the two strands of the arc is absorbed by the cap
at the bottom of the generator, the dot product being symmetric. -/
theorem orthogonalCupCapAt_mul_permTensorAction_swap {i j : Fin d} (hij : i ≠ j) :
    orthogonalCupCapAt k n d i j * permTensorAction k n d (Equiv.swap i j) =
      orthogonalCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, permTensorAction_apply, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod, orthogonalCupCapAt_tprod hij, orthogonalCupCapAt_tprod hij]
  rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right,
    dotProduct_comm (v j) (v i)]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ ?_)
  funext t
  by_cases hj : t = j
  · subst hj
    rw [update_pair_apply_right, update_pair_apply_right]
  · by_cases hi : t = i
    · subst hi
      rw [update_pair_apply_left _ hij, update_pair_apply_left _ hij]
    · rw [update_pair_apply_of_ne _ hi hj, update_pair_apply_of_ne _ hi hj,
        Equiv.swap_apply_of_ne_of_ne hi hj]

/-- **The renaming relation**: permuting the strands renames the arc. Every mixed relation between
a crossing and a generator is an instance of this one. -/
theorem permTensorAction_mul_orthogonalCupCapAt (σ : Equiv.Perm (Fin d)) {i j : Fin d}
    (hij : i ≠ j) :
    permTensorAction k n d σ * orthogonalCupCapAt k n d i j =
      orthogonalCupCapAt k n d (σ i) (σ j) * permTensorAction k n d σ := by
  refine PiTensorProduct.ext ?_
  ext v
  have hplug : ∀ c : Fin n, Function.update (Function.update (fun t => v (σ.symm t)) (σ i)
        (Pi.single c (1 : k))) (σ j) (Pi.single c 1) =
      fun t => Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1)
        (σ.symm t) := by
    intro c
    funext t
    by_cases hj : t = σ j
    · subst hj
      rw [update_pair_apply_right, Equiv.symm_apply_apply, update_pair_apply_right]
    · by_cases hi : t = σ i
      · subst hi
        rw [update_pair_apply_left _ (σ.injective.ne hij), Equiv.symm_apply_apply,
          update_pair_apply_left _ hij]
      · rw [update_pair_apply_of_ne _ hi hj, update_pair_apply_of_ne _
          (fun h => hi (by rw [← h, Equiv.apply_symm_apply]))
          (fun h => hj (by rw [← h, Equiv.apply_symm_apply]))]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, orthogonalCupCapAt_tprod hij,
    permTensorAction_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod,
    orthogonalCupCapAt_tprod (σ.injective.ne hij), Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [PiTensorProduct.reindex_tprod, ← hplug c]

/-- A permutation fixing both strands of the arc commutes with the generator: the mixed relation
between a distant crossing and a generator. -/
theorem commute_permTensorAction_orthogonalCupCapAt {σ : Equiv.Perm (Fin d)} {i j : Fin d}
    (hij : i ≠ j) (hi : σ i = i) (hj : σ j = j) :
    Commute (permTensorAction k n d σ) (orthogonalCupCapAt k n d i j) := by
  have h := permTensorAction_mul_orthogonalCupCapAt (k := k) (n := n) σ hij
  rwa [hi, hj] at h

/-! ### Two arcs -/

/-- **Disjoint arcs commute**: two generators on four distinct strands act in disjoint groups of
slots. -/
theorem commute_orthogonalCupCapAt_of_disjoint {i j a b : Fin d} (hij : i ≠ j) (hab : a ≠ b)
    (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    Commute (orthogonalCupCapAt k n d i j) (orthogonalCupCapAt k n d a b) := by
  refine PiTensorProduct.ext ?_
  ext v
  -- Each generator plugs into two slots that the other leaves alone, so the two plugs commute and
  -- each one reads the other's slots off the original tuple.
  have hswap : ∀ (c e : Fin n) (w : Fin d → (Fin n → k)),
      Function.update (Function.update
          (Function.update (Function.update w i (Pi.single c (1 : k))) j (Pi.single c 1))
          a (Pi.single e (1 : k))) b (Pi.single e 1) =
        Function.update (Function.update
          (Function.update (Function.update w a (Pi.single e (1 : k))) b (Pi.single e 1))
          i (Pi.single c (1 : k))) j (Pi.single c 1) := by
    intro c e w
    conv_lhs => rw [Function.update_comm hja, Function.update_comm hia,
      Function.update_comm hjb, Function.update_comm hib]
  have hab' : ∀ c : Fin n, orthogonalCupCapAt k n d a b (PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))) =
      (v a ⬝ᵥ v b) • ∑ e : Fin n, PiTensorProduct.tprod k (Function.update (Function.update
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
        a (Pi.single e (1 : k))) b (Pi.single e 1)) := by
    intro c
    rw [orthogonalCupCapAt_tprod hab, update_pair_apply_of_ne v (Ne.symm hia) (Ne.symm hja),
      update_pair_apply_of_ne v (Ne.symm hib) (Ne.symm hjb)]
  have hij' : ∀ e : Fin n, orthogonalCupCapAt k n d i j (PiTensorProduct.tprod k
        (Function.update (Function.update v a (Pi.single e (1 : k))) b (Pi.single e 1))) =
      (v i ⬝ᵥ v j) • ∑ c : Fin n, PiTensorProduct.tprod k (Function.update (Function.update
        (Function.update (Function.update v a (Pi.single e (1 : k))) b (Pi.single e 1))
        i (Pi.single c (1 : k))) j (Pi.single c 1)) := by
    intro e
    rw [orthogonalCupCapAt_tprod hij, update_pair_apply_of_ne v hia hib,
      update_pair_apply_of_ne v hja hjb]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply]
  rw [orthogonalCupCapAt_tprod hab, map_smul, map_sum,
    Finset.sum_congr rfl fun e _ => hij' e, ← Finset.smul_sum]
  rw [orthogonalCupCapAt_tprod hij, map_smul, map_sum,
    Finset.sum_congr rfl fun c _ => hab' c, ← Finset.smul_sum]
  rw [smul_comm (v a ⬝ᵥ v b) (v i ⬝ᵥ v j), Finset.sum_comm]
  exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun e _ => congrArg _ (hswap c e v).symm))

/-- **Two arcs sharing one strand**: `e i j * e j l * e i j = e i j`, the relation that makes two
generators on overlapping pairs absorb one another. -/
theorem orthogonalCupCapAt_mul_mul_self {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) :
    orthogonalCupCapAt k n d i j * orthogonalCupCapAt k n d j l * orthogonalCupCapAt k n d i j =
      orthogonalCupCapAt k n d i j := by
  refine PiTensorProduct.ext ?_
  ext v
  -- The middle generator replaces the slots `j` and `l` by the `e`-th basis vector, at the cost of
  -- the `c`-th coordinate of `v l`.
  have hmid : ∀ c : Fin n, orthogonalCupCapAt k n d j l (PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))) =
      v l c • ∑ e : Fin n, PiTensorProduct.tprod k (Function.update (Function.update
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
        j (Pi.single e (1 : k))) l (Pi.single e 1)) := by
    intro c
    rw [orthogonalCupCapAt_tprod hjl, update_pair_apply_right v,
      update_pair_apply_of_ne v (Ne.symm hil) (Ne.symm hjl), single_dotProduct, one_mul]
  -- The outer generator then contracts the `c`-th against the `e`-th basis vector, so only the
  -- diagonal term `e = c` survives, and it restores the slots `i` and `j` to the variable `f`.
  have hout : ∀ c e : Fin n, orthogonalCupCapAt k n d i j (PiTensorProduct.tprod k
        (Function.update (Function.update
          (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
          j (Pi.single e (1 : k))) l (Pi.single e 1))) =
      (if c = e then (1 : k) else 0) • ∑ f : Fin n, PiTensorProduct.tprod k (Function.update
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1))
        l (Pi.single e 1)) := by
    intro c e
    have hi' : Function.update (Function.update
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
        j (Pi.single e (1 : k))) l (Pi.single e 1) i = Pi.single c (1 : k) := by
      rw [Function.update_of_ne hil, Function.update_of_ne hij, update_pair_apply_left v hij]
    have hj' : Function.update (Function.update
        (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1))
        j (Pi.single e (1 : k))) l (Pi.single e 1) j = Pi.single e (1 : k) := by
      rw [Function.update_of_ne hjl, Function.update_self]
    have hplug : ∀ f : Fin n, Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update v i (Pi.single c (1 : k))) j
            (Pi.single c 1)) j (Pi.single e (1 : k))) l (Pi.single e 1))
          i (Pi.single f (1 : k))) j (Pi.single f 1) =
        Function.update (Function.update (Function.update v i (Pi.single f (1 : k))) j
          (Pi.single f 1)) l (Pi.single e 1) := by
      intro f
      funext t
      by_cases h1 : t = i <;> by_cases h2 : t = j <;> by_cases h3 : t = l <;> simp_all
    rw [orthogonalCupCapAt_tprod hij, hi', hj', single_dotProduct, one_mul, Pi.single_apply,
      Finset.sum_congr rfl fun f _ => congrArg _ (hplug f)]
  -- Summing the surviving diagonal over `c` rebuilds the slot `l`.
  have hrestore : ∀ f : Fin n, ∑ c : Fin n, v l c • PiTensorProduct.tprod k (Function.update
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1))
        l (Pi.single c (1 : k))) =
      PiTensorProduct.tprod k
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1)) := by
    intro f
    rw [Finset.sum_congr rfl fun c _ => ((PiTensorProduct.tprod k).map_update_smul
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1)) l (v l c)
        (Pi.single c (1 : k))).symm,
      ← (PiTensorProduct.tprod k).map_update_sum, ← pi_eq_sum_univ' (v l),
      show v l = Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1) l
        from (update_pair_apply_of_ne v (Ne.symm hil) (Ne.symm hjl)).symm,
      Function.update_eq_self]
  have hfull : ∀ c : Fin n, orthogonalCupCapAt k n d i j (orthogonalCupCapAt k n d j l
        (PiTensorProduct.tprod k
          (Function.update (Function.update v i (Pi.single c (1 : k))) j (Pi.single c 1)))) =
      ∑ f : Fin n, v l c • PiTensorProduct.tprod k (Function.update
        (Function.update (Function.update v i (Pi.single f (1 : k))) j (Pi.single f 1))
        l (Pi.single c (1 : k))) := by
    intro c
    rw [hmid c, map_smul, map_sum, Finset.sum_congr rfl fun e _ => hout c e]
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, reduceIte]
    rw [Finset.smul_sum]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, orthogonalCupCapAt_tprod hij]
  simp only [map_smul, map_sum]
  refine congrArg _ ?_
  rw [Finset.sum_congr rfl fun c _ => hfull c, Finset.sum_comm]
  exact Finset.sum_congr rfl fun f _ => hrestore f

/-! ### The arc as an intertwiner -/

/-- **The cup at two slots is invariant** under every matrix `A` with `A * Aᵀ = 1`: the rows of `A`
are orthonormal, so the diagonal expansion of the two slots is unchanged. This is the general-slot
form of `TauCeti.piTensorProductMap_comp_orthogonalCup`. -/
private theorem sum_tprod_update_pair_mulVec {A : Matrix (Fin n) (Fin n) k} (hA : A * Aᵀ = 1)
    {i j : Fin d} (hij : i ≠ j) (u : Fin d → (Fin n → k)) :
    ∑ c : Fin n, PiTensorProduct.tprod k (Function.update
        (Function.update u i (A *ᵥ Pi.single c (1 : k))) j (A *ᵥ Pi.single c (1 : k))) =
      ∑ c : Fin n, PiTensorProduct.tprod k
        (Function.update (Function.update u i (Pi.single c (1 : k))) j (Pi.single c 1)) := by
  have hmv : ∀ c a : Fin n, (A *ᵥ Pi.single c (1 : k)) a = A a c := by
    intro c a
    rw [Matrix.mulVec, dotProduct_single, mul_one]
  have hrow : ∀ a b : Fin n,
      ∑ c : Fin n, A a c * A b c = (1 : Matrix (Fin n) (Fin n) k) a b := by
    intro a b
    rw [← hA]
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  -- Expand the two slots in the standard basis; the coefficient of the `(a, b)` term is the
  -- `(a, b)` entry of `A * Aᵀ`, which is `1`, so only the diagonal terms survive.
  calc ∑ c : Fin n, PiTensorProduct.tprod k (Function.update
        (Function.update u i (A *ᵥ Pi.single c (1 : k))) j (A *ᵥ Pi.single c (1 : k)))
      = ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, (A a c * A b c) • PiTensorProduct.tprod k
          (Function.update (Function.update u i (Pi.single a (1 : k))) j (Pi.single b 1)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [tprod_update_pair_expand hij u]
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by rw [hmv c a, hmv c b]
    _ = ∑ a : Fin n, ∑ b : Fin n, ((1 : Matrix (Fin n) (Fin n) k) a b) • PiTensorProduct.tprod k
          (Function.update (Function.update u i (Pi.single a (1 : k))) j (Pi.single b 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_smul, hrow a b]
    _ = ∑ c : Fin n, PiTensorProduct.tprod k
          (Function.update (Function.update u i (Pi.single c (1 : k))) j (Pi.single c 1)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, reduceIte]

/-- **The generator commutes with every matrix** preserving the coordinate dot product, acting
diagonally on the tensor power: the cap consumes `Aᵀ * A = 1` and the cup consumes `A * Aᵀ = 1`. -/
theorem commute_orthogonalCupCapAt_piTensorProductMap {A : Matrix (Fin n) (Fin n) k}
    (hA : Aᵀ * A = 1) (hA' : A * Aᵀ = 1) {i j : Fin d} (hij : i ≠ j) :
    Commute (orthogonalCupCapAt k n d i j)
      (PiTensorProduct.map fun _ : Fin d => Matrix.mulVecLin A) := by
  refine PiTensorProduct.ext ?_
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, PiTensorProduct.map_tprod,
    orthogonalCupCapAt_tprod hij, orthogonalCupCapAt_tprod hij, map_smul, map_sum]
  simp only [Matrix.mulVecLin_apply]
  rw [show (A *ᵥ v i) ⬝ᵥ (A *ᵥ v j) = v i ⬝ᵥ v j by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hA, Matrix.vecMul_one]]
  refine congrArg _ ?_
  rw [← sum_tprod_update_pair_mulVec hA' hij fun t => A *ᵥ v t]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PiTensorProduct.map_tprod]
  simp only [Matrix.mulVecLin_apply]
  congr 1
  funext t
  by_cases hj : t = j
  · subst hj
    rw [update_pair_apply_right, Function.update_self]
  · by_cases hi : t = i
    · subst hi
      rw [update_pair_apply_left _ hij, Function.update_of_ne hj, Function.update_self]
    · rw [update_pair_apply_of_ne _ hi hj, Function.update_of_ne hj, Function.update_of_ne hi]

/-- On two strands the generator is `TauCeti.orthogonalCupCap`, the composite `cup ∘ₗ cap` through
the tensor square. -/
theorem orthogonalCupCapAt_zero_one : orthogonalCupCapAt k n 2 0 1 = orthogonalCupCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    orthogonalCupCapAt_tprod (by decide : (0 : Fin 2) ≠ 1), orthogonalCupCap_apply,
    orthogonalCap_tprod, orthogonalCup_apply]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => congrArg _ ?_)
  funext t
  fin_cases t <;> simp

end CommSemiring

section CommRing

variable [CommRing k]

/-- **Every single-arc Brauer diagram acts by an intertwiner**: the generator commutes with the
diagonal action of the orthogonal group on the `d`-th tensor power. The two-strand case is
`TauCeti.commute_orthogonalCupCap_tensorPower`. -/
theorem commute_orthogonalCupCapAt_tensorPower (g : Matrix.orthogonalGroup (Fin n) k)
    {i j : Fin d} (hij : i ≠ j) :
    Commute (orthogonalCupCapAt k n d i j) ((stdOrthogonalRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    commute_orthogonalCupCapAt_piTensorProductMap
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) k).mp g.prop)
      ((Matrix.mem_orthogonalGroup_iff (Fin n) k).mp g.prop) hij

end CommRing

end TauCeti
