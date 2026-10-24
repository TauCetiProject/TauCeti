/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TensorPower
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
-- The entrywise identities for `Matrix.J` the relations below contract with.
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The symplectic Brauer crossing on a tensor power

The permutation diagrams of the Brauer algebra act on the `d`-th tensor power of the standard
symplectic module `V = k^{2n}` not by the bare permutation of the tensor factors but by its
**sign twist**: a permutation `σ` of the strands acts by `sign σ` times the reindexing of the slots
along `σ`. This file builds that action, `TauCeti.symplecticPermTensorAction`, as the twist
`Representation.charTwist` of the reindexing representation by the sign character, and proves the
relations it satisfies with the symplectic arcs `TauCeti.symplecticCupCapAt`.

## Why the sign

The cap and the cup of the standard alternating form each change sign when their two endpoints are
exchanged. So the bare transposition of the two slots of an arc *negates* the arc instead of
absorbing it, and it is minus that transposition which satisfies the Brauer relation `s e = e`.
On two strands this is the crossing `TauCeti.symplecticCrossing` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Basic.lean`, which this
file reproduces at `d = 2` (`TauCeti.symplecticPermTensorAction_swap_zero_one`). On `d` strands the
crossings must still satisfy the Coxeter relations of the symmetric group, so the transposition
`(i j)` acting by minus the reindexing extends uniquely to `σ ↦ sign σ • reindex σ`: the sign twist
is forced, not chosen.

## The relations

Writing `s σ` for the action of the permutation `σ` and `e i j` for the arc on the strands `i` and
`j`, the relations proved here are

* `s σ * e i j = e (σ i) (σ j) * s σ`, the renaming of the arc by a permutation of the strands;
* `s (i j) * e i j = e i j` and `e i j * s (i j) = e i j`, the two absorptions of the crossing on
  the arc;
* `e i l * e i j = e i l * s (j l)` for three distinct strands, both sides being the diagram with a
  cap on `i, j`, a cup on `i, l` and a through strand from `l` to `j`;
* the mixed relations `s (i j) * e j l * e i j = s (j l) * e i j`,
  `e i j * e j l * s (i j) = e i j * s (j l)` and `e i j * s (j l) * e i j = e i j` that follow.

Together with `s` being a monoid homomorphism, which gives `s² = 1` and the braid relations, and
with the relations among arcs alone of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/TensorPower.lean`, these
are the relations of the Brauer algebra `B_d(-2n)` between crossings and arcs, at the symplectic
loop value. That the crossings and arcs assemble into an algebra map from `B_d(-2n)` is not proved
here. Finally `s σ` commutes with the diagonal action of every linear map, so in particular with
the symplectic group.

## Main definitions

* `TauCeti.symplecticPermTensorAction`: the sign-twisted permutation action of `S_d` on the `d`-th
  tensor power of `k^{2n}`.

## Main results

* `TauCeti.symplecticPermTensorAction_tprod`: a permutation reindexes a pure tensor and multiplies
  it by its sign.
* `TauCeti.symplecticPermTensorAction_swap_zero_one`: on two strands the transposition acts by the
  crossing `TauCeti.symplecticCrossing`.
* `TauCeti.commute_symplecticPermTensorAction_map` and
  `TauCeti.commute_symplecticPermTensorAction_tensorPower`: the action commutes with the diagonal
  action of a linear map, and of the symplectic group.
* `TauCeti.symplecticPermTensorAction_mul_symplecticCupCapAt`: **the renaming relation**.
* `TauCeti.symplecticPermTensorAction_swap_mul_symplecticCupCapAt` and
  `TauCeti.symplecticCupCapAt_mul_symplecticPermTensorAction_swap`: **the crossing on an arc is
  absorbed**.
* `TauCeti.symplecticCupCapAt_mul_symplecticCupCapAt`: two arcs sharing one strand compose to an arc
  followed by a crossing.
* `TauCeti.symplecticPermTensorAction_swap_mul_symplecticCupCapAt_mul_symplecticCupCapAt`,
  `TauCeti.symplecticCupCapAt_mul_symplecticCupCapAt_mul_symplecticPermTensorAction_swap` and
  `TauCeti.symplecticCupCapAt_mul_symplecticPermTensorAction_swap_mul_symplecticCupCapAt`: **the
  mixed relations**.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for the Brauer algebra acting on the tensor powers of a symplectic space.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ) [CommRing k]

/-- **The sign-twisted permutation action** of the symmetric group `S_d` on the `d`-th tensor power
of the standard symplectic module `k^{2n}`: a permutation reindexes the tensor factors and
multiplies by its sign. This is the action of the permutation diagrams in the symplectic Brauer
action; on two strands the transposition acts by `TauCeti.symplecticCrossing`. -/
noncomputable def symplecticPermTensorAction :
    Representation k (Equiv.Perm (Fin d)) (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  (PiTensorProduct.reindexRepresentation k ((Fin n ⊕ Fin n) → k) (Fin d)).charTwist
    (signLinearCharacter k (Fin d))

variable {k n d}

/-- A permutation acts by its sign times `PiTensorProduct.reindex`. -/
theorem symplecticPermTensorAction_apply (σ : Equiv.Perm (Fin d)) :
    symplecticPermTensorAction k n d σ =
      ((Equiv.Perm.sign σ : ℤ) : k) •
        (PiTensorProduct.reindex k (fun _ : Fin d => (Fin n ⊕ Fin n) → k) σ).toLinearMap := by
  rw [symplecticPermTensorAction, Representation.charTwist_apply, coe_signLinearCharacter_apply,
    PiTensorProduct.reindexRepresentation_apply]

/-- **A permutation on a pure tensor**: the factors are reindexed and the result is multiplied by
the sign of the permutation. -/
@[simp]
theorem symplecticPermTensorAction_tprod (σ : Equiv.Perm (Fin d))
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticPermTensorAction k n d σ (PiTensorProduct.tprod k v) =
      ((Equiv.Perm.sign σ : ℤ) : k) • PiTensorProduct.tprod k fun t => v (σ.symm t) := by
  rw [symplecticPermTensorAction_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod]

/-- A transposition of two distinct strands acts by minus the reindexing. -/
theorem symplecticPermTensorAction_swap {i j : Fin d} (hij : i ≠ j) :
    symplecticPermTensorAction k n d (Equiv.swap i j) =
      -(PiTensorProduct.reindex k (fun _ : Fin d => (Fin n ⊕ Fin n) → k)
        (Equiv.swap i j)).toLinearMap := by
  rw [symplecticPermTensorAction_apply, Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one,
    Int.cast_neg, Int.cast_one, neg_smul (M := Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k))),
    one_smul]

/-- **A transposition of two distinct strands on a pure tensor** exchanges the two factors and
changes the sign. -/
theorem symplecticPermTensorAction_swap_tprod {i j : Fin d} (hij : i ≠ j)
    (v : Fin d → ((Fin n ⊕ Fin n) → k)) :
    symplecticPermTensorAction k n d (Equiv.swap i j) (PiTensorProduct.tprod k v) =
      -PiTensorProduct.tprod k fun t => v (Equiv.swap i j t) := by
  rw [symplecticPermTensorAction_swap hij, LinearMap.neg_apply, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod, Equiv.symm_swap]

/-- **On two strands the transposition acts by the Brauer crossing** `TauCeti.symplecticCrossing`,
minus the flip of the two tensor factors. -/
theorem symplecticPermTensorAction_swap_zero_one :
    symplecticPermTensorAction k n 2 (Equiv.swap 0 1) = symplecticCrossing k n := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have hv : (fun t => v (Equiv.swap 0 1 t)) = ![v 1, v 0] := by
    funext t
    fin_cases t <;> rfl
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    symplecticPermTensorAction_swap_tprod (by decide), symplecticCrossing_tprod, hv]

/-! ### Commuting with the diagonal action -/

/-- **The sign-twisted permutation action commutes with the diagonal action** of every linear
map: permuting the tensor factors commutes with applying the same map in each of them, and the
sign is a scalar. -/
theorem commute_symplecticPermTensorAction_map (σ : Equiv.Perm (Fin d))
    (f : ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k)) :
    Commute (symplecticPermTensorAction k n d σ) (PiTensorProduct.map fun _ : Fin d => f) := by
  rw [symplecticPermTensorAction, Representation.charTwist_apply]
  exact (PiTensorProduct.commute_reindexRepresentation_map k _ (Fin d) σ f).smul_left _

/-- **The sign-twisted permutation action commutes with the symplectic group** acting diagonally
on the tensor power, so every permutation diagram acts by an intertwiner. -/
theorem commute_symplecticPermTensorAction_tensorPower (σ : Equiv.Perm (Fin d))
    (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (symplecticPermTensorAction k n d σ) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  exact commute_symplecticPermTensorAction_map σ _

/-! ### The crossing on an arc, and the renaming of an arc -/

/-- **The renaming relation**: permuting the strands renames the arc, `s σ * e i j =
e (σ i) (σ j) * s σ`. The sign of `σ` appears on both sides, so this is bookkeeping on the index
set; it does not read the arc through the form and holds at coincident strands too. -/
theorem symplecticPermTensorAction_mul_symplecticCupCapAt (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    symplecticPermTensorAction k n d σ * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d (σ i) (σ j) * symplecticPermTensorAction k n d σ := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    Module.End.mul_apply, Module.End.mul_apply, symplecticPermTensorAction_tprod, map_smul]
  rcases eq_or_ne i j with rfl | hij
  · rw [symplecticCupCapAt_self_tprod, symplecticCupCapAt_self_tprod, Equiv.symm_apply_apply]
    simp only [map_smul, map_neg, map_sum, symplecticPermTensorAction_tprod,
      Function.update_apply_equiv_apply, Equiv.symm_symm, Function.comp_def]
    simp only [Finset.smul_sum, smul_neg, smul_comm ((Equiv.Perm.sign σ : ℤ) : k)]
  · rw [symplecticCupCapAt_tprod hij, symplecticCupCapAt_tprod (σ.injective.ne hij),
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp only [map_smul, map_neg, map_sum, symplecticPermTensorAction_tprod,
      Function.update_apply_equiv_apply, Equiv.symm_symm, Function.comp_def]
    simp only [Finset.smul_sum, smul_neg, smul_comm ((Equiv.Perm.sign σ : ℤ) : k)]

/-- **The relation `s e = e`**: the crossing of the two strands of an arc is absorbed by the cup on
top of it. The bare transposition negates the cup, because the copairing is antisymmetric, and the
sign of the transposition cancels that. -/
theorem symplecticPermTensorAction_swap_mul_symplecticCupCapAt (i j : Fin d) :
    symplecticPermTensorAction k n d (Equiv.swap i j) * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Equiv.swap_self, Equiv.Perm.one_def.symm, map_one, one_mul]
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  -- exchanging the two plugged slots exchanges the two basis vectors plugged into them
  have hswap : ∀ x y : Fin n ⊕ Fin n,
      (fun t => Function.update (Function.update v i (Pi.single x (1 : k))) j (Pi.single y 1)
          (Equiv.swap i j t)) =
        Function.update (Function.update v i (Pi.single y (1 : k))) j (Pi.single x 1) := by
    intro x y
    funext t
    rcases eq_or_ne t i with rfl | hti
    · simp [hij]
    rcases eq_or_ne t j with rfl | htj
    · simp [hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hti htj, hti, htj]
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, Module.End.mul_apply,
    symplecticCupCapAt_tprod hij, map_smul, map_neg]
  refine congrArg _ (congrArg Neg.neg ?_)
  simp only [map_sum, map_smul, symplecticPermTensorAction_swap_tprod hij, hswap, smul_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.J_apply_swap, neg_smul (M := ⨂[k]^d ((Fin n ⊕ Fin n) → k)), neg_neg]

/-- **The relation `e s = e`**: the crossing of the two strands of an arc is absorbed by the cap at
the bottom of it. By the renaming relation the transposition of the two strands commutes with the
arc, so this is `TauCeti.symplecticPermTensorAction_swap_mul_symplecticCupCapAt` read from the
other side. -/
theorem symplecticCupCapAt_mul_symplecticPermTensorAction_swap (i j : Fin d) :
    symplecticCupCapAt k n d i j * symplecticPermTensorAction k n d (Equiv.swap i j) =
      symplecticCupCapAt k n d i j := by
  have h := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n)
    (Equiv.swap i j) i j
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, ← symplecticCupCapAt_comm i j,
    symplecticPermTensorAction_swap_mul_symplecticCupCapAt] at h
  exact h.symm

/-- A permutation preserving the unordered pair of strands of an arc commutes with the arc. This
includes the permutations fixing both strands and those exchanging them. -/
theorem commute_symplecticPermTensorAction_symplecticCupCapAt {σ : Equiv.Perm (Fin d)}
    {i j : Fin d} (hσ : ({σ i, σ j} : Set (Fin d)) = {i, j}) :
    Commute (symplecticPermTensorAction k n d σ) (symplecticCupCapAt k n d i j) := by
  have h := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n) σ i j
  rcases Set.pair_eq_pair_iff.mp hσ with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rwa [hi, hj] at h
  · rwa [hi, hj, symplecticCupCapAt_comm j i] at h

/-! ### Two arcs sharing a strand -/

/-- An arc on a monomial tensor of standard basis vectors, at distinct strands: the entry of `J` at
the two labels, times the cup re-expanding the two slots. -/
private theorem symplecticCupCapAt_tprod_single {i j : Fin d} (hij : i ≠ j)
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

/-- **Two arcs sharing one strand compose to an arc after a crossing**: for three distinct strands,
`e i l * e i j = e i l * s (j l)`. Both sides are the diagram with a cap on `i, j`, a cup on `i, l`
and a through strand from `l` to `j`. On the left the strand is the zigzag through the middle cup
on `i, j` and the cap on `i, l`, which straightens by the column pairing `Jᵀ * J = 1`; on the right
the crossing carries the slot `l` to the slot `j`, and its sign cancels the sign of the two cups. -/
theorem symplecticCupCapAt_mul_symplecticCupCapAt {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) :
    symplecticCupCapAt k n d i l * symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i l * symplecticPermTensorAction k n d (Equiv.swap j l) := by
  classical
  -- the monomial tensors of standard basis vectors form a basis
  let b := Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n)
  have hb : ∀ f : Fin d → Fin n ⊕ Fin n, b f = PiTensorProduct.tprod k fun t =>
      (Pi.single (f t) (1 : k) : (Fin n ⊕ Fin n) → k) := by
    intro f
    simp [b, Basis.piTensorProduct_apply]
  -- the outer arc on a tensor the inner arc has written
  have hstep : ∀ (f : Fin d → Fin n ⊕ Fin n) (x y : Fin n ⊕ Fin n),
      symplecticCupCapAt k n d i l (PiTensorProduct.tprod k fun t =>
          (Pi.single (Function.update (Function.update f i x) j y t) (1 : k) :
            (Fin n ⊕ Fin n) → k)) =
        -(Matrix.J (Fin n) k x (f l) • ∑ p : Fin n ⊕ Fin n, ∑ q : Fin n ⊕ Fin n,
          Matrix.J (Fin n) k p q • PiTensorProduct.tprod k fun t => (Pi.single
            (Function.update (Function.update (Function.update f i p) j y) l q t) (1 : k) :
              (Fin n ⊕ Fin n) → k)) := by
    intro f x y
    -- the outer arc overwrites the slot `i` the inner one had filled
    have hfun : ∀ p q : Fin n ⊕ Fin n,
        Function.update (Function.update (Function.update (Function.update f i x) j y) i p) l q =
          Function.update (Function.update (Function.update f i p) j y) l q := by
      intro p q
      funext t
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [symplecticCupCapAt_tprod_single hil, Function.update_of_ne hij, Function.update_self,
      Function.update_of_ne hjl.symm, Function.update_of_ne hil.symm]
    simp only [hfun]
  refine b.ext fun f => ?_
  -- the crossing carries the label of the strand `l` to the strand `j`
  have hcross : ∀ p q : Fin n ⊕ Fin n,
      Function.update (Function.update (fun t => f (Equiv.swap j l t)) i p) l q =
        Function.update (Function.update (Function.update f i p) j (f l)) l q := by
    intro p q
    funext t
    rcases eq_or_ne t l with rfl | htl
    · simp only [Function.update_self]
    rcases eq_or_ne t i with rfl | hti
    · simp only [Function.update_of_ne htl, Function.update_self, Function.update_of_ne hij]
    rcases eq_or_ne t j with rfl | htj
    · simp only [Function.update_of_ne htl, Function.update_of_ne hti, Function.update_self,
        Equiv.swap_apply_left]
    · simp only [Function.update_of_ne htl, Function.update_of_ne hti, Function.update_of_ne htj,
        Equiv.swap_apply_of_ne_of_ne htj htl]
  have hright := symplecticCupCapAt_tprod_single (k := k) hil fun t => f (Equiv.swap j l t)
  rw [Equiv.swap_apply_of_ne_of_ne hij hil, Equiv.swap_apply_right] at hright
  simp only [hcross] at hright
  rw [hb, Module.End.mul_apply, Module.End.mul_apply, symplecticCupCapAt_tprod_single hij,
    symplecticPermTensorAction_swap_tprod hjl, map_neg, map_neg, hright, neg_neg]
  simp only [map_sum, map_smul, hstep, smul_neg, Finset.sum_neg_distrib, neg_neg, smul_smul]
  refine congrArg _ ?_
  -- the zigzag straightens: summing over the label of the middle cup leaves the label of `l`
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, Matrix.sum_J_mul_J_eq_ite, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ### The mixed relations -/

/-- **The mixed Brauer relation `sᵢ eᵢ₊₁ eᵢ = sᵢ₊₁ eᵢ`**, on any three distinct strands. Moving
the crossings past the arcs by the renaming relation, both sides become
`TauCeti.symplecticCupCapAt_mul_symplecticCupCapAt`. -/
theorem symplecticPermTensorAction_swap_mul_symplecticCupCapAt_mul_symplecticCupCapAt
    {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    symplecticPermTensorAction k n d (Equiv.swap i j) *
        (symplecticCupCapAt k n d j l * symplecticCupCapAt k n d i j) =
      symplecticPermTensorAction k n d (Equiv.swap j l) * symplecticCupCapAt k n d i j := by
  have hleft := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n)
    (Equiv.swap i j) j l
  have hright := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n)
    (Equiv.swap j l) i j
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] at hleft
  rw [Equiv.swap_apply_of_ne_of_ne hij hil, Equiv.swap_apply_left] at hright
  rw [← mul_assoc, hleft, mul_assoc, symplecticPermTensorAction_swap_mul_symplecticCupCapAt,
    hright, symplecticCupCapAt_mul_symplecticCupCapAt hij hjl hil]

/-- **The mixed Brauer relation `eᵢ eᵢ₊₁ sᵢ = eᵢ sᵢ₊₁`**, the reverse product form of
`TauCeti.symplecticPermTensorAction_swap_mul_symplecticCupCapAt_mul_symplecticCupCapAt`, on any
three distinct strands. -/
theorem symplecticCupCapAt_mul_symplecticCupCapAt_mul_symplecticPermTensorAction_swap
    {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (symplecticCupCapAt k n d i j * symplecticCupCapAt k n d j l) *
        symplecticPermTensorAction k n d (Equiv.swap i j) =
      symplecticCupCapAt k n d i j * symplecticPermTensorAction k n d (Equiv.swap j l) := by
  have h := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n)
    (Equiv.swap i j) i l
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm] at h
  rw [mul_assoc, ← h, ← mul_assoc, symplecticCupCapAt_mul_symplecticPermTensorAction_swap,
    symplecticCupCapAt_mul_symplecticCupCapAt hil hjl.symm hij, Equiv.swap_comm]

/-- **The mixed Brauer relation `eᵢ sᵢ₊₁ eᵢ = eᵢ`**, on any three distinct strands: a crossing
between two copies of an arc, on a strand of the arc and a third strand, straightens out. -/
theorem symplecticCupCapAt_mul_symplecticPermTensorAction_swap_mul_symplecticCupCapAt
    {i j l : Fin d} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    symplecticCupCapAt k n d i j * symplecticPermTensorAction k n d (Equiv.swap j l) *
        symplecticCupCapAt k n d i j =
      symplecticCupCapAt k n d i j := by
  have h := symplecticPermTensorAction_mul_symplecticCupCapAt (k := k) (n := n)
    (Equiv.swap j l) i j
  rw [Equiv.swap_apply_of_ne_of_ne hij hil, Equiv.swap_apply_left] at h
  rw [mul_assoc, h, ← mul_assoc, symplecticCupCapAt_mul_symplecticCupCapAt hil hjl.symm hij,
    Equiv.swap_comm, mul_assoc, ← map_mul, Equiv.swap_mul_self, map_one, mul_one]

end TauCeti
