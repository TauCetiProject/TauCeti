/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Realization
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SpecialNodePermutations
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.CharacterMap

/-!
# The special isogeny of the rank-two symplectic B₂ Chevalley datum

Over a field `K` of characteristic two, the rank-two symplectic carrier carries the special isogeny
`TauCeti.SpStd.specialIsogeny K : points 1 K →* points 1 K`, constructed from the `2 × 2` minor
map on `Sp₄(K)`. Conjugating it across `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv K` yields an
endomorphism `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny K` of the points of the full-weight
`B₂` Chevalley datum `TauCeti.SpStd.b2ChevalleyDatum`.

Reading the carrier in Bourbaki `B₂` numbering aligns the represented matrix endomorphism directly
with the pinned root-datum isogeny `TauCeti.DynkinType.b2SpecialIsogeny`:

* Over any commutative ring `A`, `b2ChevalleyDatumPointsEquiv A` identifies the torus
  `b2ChevalleyDatum.torusPoints A` with `TauCeti.SpStd.b2WeightTorusPoints A` across
  `finCongr (DynkinType.rank_B 2)`.
* Over a field `K` of characteristic two, `b2ChevalleyDatumSpecialIsogeny K` squares to the prime
  Frobenius `b2ChevalleyDatum.frobenius 2 1 K`.
* On the positive and negative simple root subgroups, Weyl elements, and simple coroots at node
  `i`, it acts by the Bourbaki length-exchanging permutation `TauCeti.SpStd.b2LengthPerm` and
  raises the parameter to `((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat`, which is `1` at
  the long node `0` and `2` at the short node `1`.
* On the full-weight torus `b2ChevalleyDatum.torusPoints K`, it sends `s` to
  `fun i => s (b2LengthPerm i) ^ ((DynkinType.B 2).rootLength i).toNat` and pulls characters back
  by `TauCeti.SpStd.b2SpecialIsogenyWeightMap` (the transport of
  `TauCeti.DynkinType.b2SpecialIsogeny.weightMap` along `finCongr (DynkinType.rank_B 2)`).

No odd power of the isogeny or fixed-point subgroup is formed here.

## Main definitions

* `TauCeti.SpStd.b2LengthPerm`: the Bourbaki length-exchanging node permutation on
  `Fin (DynkinType.B 2).rank`.
* `TauCeti.SpStd.b2SpecialIsogenyWeightMap`: `DynkinType.b2SpecialIsogeny.weightMap` transported to
  `Fin (DynkinType.B 2).rank → ℤ`.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny`: the special isogeny of
  `b2ChevalleyDatum.points K` over a field `K` of characteristic two.

## Main results

* `TauCeti.SpStd.isSpecialNodePerm_b2LengthPerm`: `b2LengthPerm` is the unique special node
  permutation of `DynkinType.B 2`.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints`: identification of the datum
  torus with `b2WeightTorusPoints` over any commutative ring.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny` and
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_comp_self`: the square of the special isogeny is
  the prime Frobenius `b2ChevalleyDatum.frobenius 2 1 K`.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_reflectionPerm_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_weylElement_simpleIndex`, and
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_simpleCorootPoints`: the pinning equations on
  simple root subgroups, Weyl elements, and simple coroots.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_torusPoints` and
  `TauCeti.SpStd.isCharacterMap_b2ChevalleyDatumSpecialIsogeny`: torus action and character
  pullback by `b2SpecialIsogenyWeightMap`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.

The point-group transport and character-pullback equations parallel
`TauCeti.SpStd.specialIsogeny` and `TauCeti.SpStd.isCharacterMap_specialIsogeny`.
-/

public section

namespace TauCeti.SpStd

open _root_.Matrix

universe v

/-! ## The length permutation and character map on `Fin (DynkinType.B 2).rank` -/

/-- **The length-exchanging permutation of the Bourbaki-numbered nodes of `B₂`**, typed on
`Fin (DynkinType.B 2).rank` by transporting `TauCeti.lengthPermRankTwo` along
`finCongr (DynkinType.rank_B 2)`. -/
def b2LengthPerm : Equiv.Perm (Fin (DynkinType.B 2).rank) :=
  (finCongr (DynkinType.rank_B 2)).symm.permCongr lengthPermRankTwo

/-- `b2LengthPerm` conjugates `lengthPermRankTwo` by `finCongr (DynkinType.rank_B 2)`. -/
theorem b2LengthPerm_def :
    b2LengthPerm = (finCongr (DynkinType.rank_B 2)).symm.permCongr lengthPermRankTwo :=
  (rfl)

/-- Evaluating `b2LengthPerm` casts to `Fin 2`, applies `lengthPermRankTwo`, and casts back. -/
theorem b2LengthPerm_apply (i : Fin (DynkinType.B 2).rank) :
    b2LengthPerm i =
      (finCongr (DynkinType.rank_B 2)).symm
        (lengthPermRankTwo (finCongr (DynkinType.rank_B 2) i)) := by
  rw [b2LengthPerm_def, Equiv.permCongr_apply, Equiv.symm_symm]

/-- Applying `b2LengthPerm` twice fixes every node of `B₂`. -/
@[simp↓]
theorem b2LengthPerm_b2LengthPerm (i : Fin (DynkinType.B 2).rank) :
    b2LengthPerm (b2LengthPerm i) = i := by
  rw [b2LengthPerm_apply, b2LengthPerm_apply, Equiv.apply_symm_apply,
    lengthPermRankTwo_lengthPermRankTwo, Equiv.symm_apply_apply]

/-- `b2LengthPerm` is its own inverse. -/
@[simp]
theorem b2LengthPerm_symm : b2LengthPerm.symm = b2LengthPerm :=
  Equiv.ext fun i => b2LengthPerm.symm_apply_eq.mpr (b2LengthPerm_b2LengthPerm i).symm

/-- **The node swap `b2LengthPerm` is the special node permutation of `DynkinType.B 2`.** -/
theorem isSpecialNodePerm_b2LengthPerm : (DynkinType.B 2).IsSpecialNodePerm b2LengthPerm := by
  have heq : b2LengthPerm = lengthPermRankTwo :=
    Equiv.ext fun i => by rw [b2LengthPerm_apply]; rfl
  exact heq ▸ DynkinType.isSpecialNodePerm_B2

/-- Composing `b2NodeEquiv` with `b2LengthPerm` cancels the node swap, leaving the rank cast. -/
@[simp↓]
theorem b2NodeEquiv_b2LengthPerm (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv (b2LengthPerm i) = finCongr (DynkinType.rank_B 2) i := by
  rw [b2NodeEquiv_apply_eq_lengthPermRankTwo, b2LengthPerm_apply, Equiv.apply_symm_apply,
    lengthPermRankTwo_lengthPermRankTwo]

private theorem rootLength_B2_finCongr_symm (j : Fin 2) :
    (DynkinType.B 2).rootLength ((finCongr (DynkinType.rank_B 2)).symm j) =
      if j = 1 then 1 else 2 := by
  rw [DynkinType.rootLength_B]
  fin_cases j <;> decide

noncomputable section

/-- **The character-lattice map of `DynkinType.b2SpecialIsogeny`, typed on
`Fin (DynkinType.B 2).rank → ℤ`.** -/
def b2SpecialIsogenyWeightMap : Module.End ℤ (Fin (DynkinType.B 2).rank → ℤ) :=
  (LinearEquiv.funCongrLeft ℤ ℤ (finCongr (DynkinType.rank_B 2))).conj
    DynkinType.b2SpecialIsogeny.weightMap

/-- `b2SpecialIsogenyWeightMap` conjugates `DynkinType.b2SpecialIsogeny.weightMap` by
`LinearEquiv.funCongrLeft ℤ ℤ (finCongr (DynkinType.rank_B 2))`. -/
theorem b2SpecialIsogenyWeightMap_def :
    b2SpecialIsogenyWeightMap =
      (LinearEquiv.funCongrLeft ℤ ℤ (finCongr (DynkinType.rank_B 2))).conj
        DynkinType.b2SpecialIsogeny.weightMap :=
  (rfl)

/-- In fundamental-weight coordinates, `b2SpecialIsogenyWeightMap` evaluates `χ` at
`b2LengthPerm i` and rescales by the squared root length at `b2LengthPerm i`. -/
@[simp↓]
theorem b2SpecialIsogenyWeightMap_apply (χ : Fin (DynkinType.B 2).rank → ℤ)
    (i : Fin (DynkinType.B 2).rank) :
    b2SpecialIsogenyWeightMap χ i =
      (DynkinType.B 2).rootLength (b2LengthPerm i) * χ (b2LengthPerm i) := by
  obtain ⟨j, rfl⟩ := (finCongr (DynkinType.rank_B 2)).symm.surjective i
  rw [b2SpecialIsogenyWeightMap_def, LinearEquiv.conj_apply_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, DynkinType.b2SpecialIsogeny_weightMap,
    b2LengthPerm_apply, Equiv.apply_symm_apply, rootLength_B2_finCongr_symm]
  fin_cases j <;> simp [DynkinType.b2SpecialIsogenyMatrix_def] <;> rfl

/-! ## Identification of the Bourbaki `B₂` torus over any commutative ring -/

/-- **Across `b2ChevalleyDatumPointsEquiv`, the torus of `b2ChevalleyDatum` is
`b2WeightTorusPoints`.** This is not a `simp` lemma because
`b2ChevalleyDatumPointsEquiv_torusPoints` already normalizes the left-hand side to
`weightTorusPoints 1`. -/
theorem b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatumPointsEquiv A (b2ChevalleyDatum.torusPoints A s) =
      b2WeightTorusPoints A (s ∘ (finCongr (DynkinType.rank_B 2)).symm) := by
  rw [b2ChevalleyDatumPointsEquiv_torusPoints, b2WeightTorusPoints_apply]
  congr 1
  funext i
  rw [Function.comp_apply, b2NodeEquiv_symm_apply]
  fin_cases i <;> rfl

/-- The inverse point isomorphism carries `b2WeightTorusPoints A` to
`b2ChevalleyDatum.torusPoints A` with the same Bourbaki `B₂` coordinates. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) :
    (b2ChevalleyDatumPointsEquiv A).symm (b2WeightTorusPoints A s) =
      b2ChevalleyDatum.torusPoints A (s ∘ finCongr (DynkinType.rank_B 2)) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints]
  rfl

/-! ## The special isogeny in characteristic two -/

section CharacteristicTwo

variable (K : Type v) [Field K] [CharP K 2]

/-- **The special isogeny of the rank-two symplectic `B₂` Chevalley datum in characteristic two**,
transported from `TauCeti.SpStd.specialIsogeny K` across `b2ChevalleyDatumPointsEquiv K`. -/
def b2ChevalleyDatumSpecialIsogeny :
    b2ChevalleyDatum.points K →* b2ChevalleyDatum.points K :=
  (b2ChevalleyDatumPointsEquiv K).symm.toMonoidHom.comp
    ((specialIsogeny K).comp (b2ChevalleyDatumPointsEquiv K).toMonoidHom)

/-- `b2ChevalleyDatumSpecialIsogeny` conjugates `specialIsogeny K` by
`b2ChevalleyDatumPointsEquiv K`. -/
theorem b2ChevalleyDatumSpecialIsogeny_def :
    b2ChevalleyDatumSpecialIsogeny K =
      (b2ChevalleyDatumPointsEquiv K).symm.toMonoidHom.comp
        ((specialIsogeny K).comp (b2ChevalleyDatumPointsEquiv K).toMonoidHom) :=
  (rfl)

/-- `b2ChevalleyDatumPointsEquiv` intertwines `b2ChevalleyDatumSpecialIsogeny` with
`specialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points K) :
    b2ChevalleyDatumPointsEquiv K (b2ChevalleyDatumSpecialIsogeny K g) =
      specialIsogeny K (b2ChevalleyDatumPointsEquiv K g) := by
  rw [b2ChevalleyDatumSpecialIsogeny_def, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

/-- The inverse point isomorphism intertwines `specialIsogeny` with
`b2ChevalleyDatumSpecialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_specialIsogeny (g : points 1 K) :
    (b2ChevalleyDatumPointsEquiv K).symm (specialIsogeny K g) =
      b2ChevalleyDatumSpecialIsogeny K ((b2ChevalleyDatumPointsEquiv K).symm g) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    MulEquiv.apply_symm_apply]

/-- On underlying `4 × 4` matrices, `b2ChevalleyDatumSpecialIsogeny` is the matrix of `2 × 2`
minors `Matrix.symplecticSpecialIsogeny`. -/
@[simp]
theorem coe_b2ChevalleyDatumSpecialIsogeny (g : b2ChevalleyDatum.points K) :
    ((b2ChevalleyDatumSpecialIsogeny K g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) K) :
        Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) K) =
      Matrix.symplecticSpecialIsogeny
        ((g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) K) :
          Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) K) := by
  rw [← coe_b2ChevalleyDatumPointsEquiv K (b2ChevalleyDatumSpecialIsogeny K g),
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny]
  exact (coe_specialIsogeny K (b2ChevalleyDatumPointsEquiv K g)).trans
    (by rw [coe_b2ChevalleyDatumPointsEquiv])

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` is the prime Frobenius of
`b2ChevalleyDatum`.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points K) :
    b2ChevalleyDatumSpecialIsogeny K (b2ChevalleyDatumSpecialIsogeny K g) =
      b2ChevalleyDatum.frobenius 2 1 K g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (b2ChevalleyDatumPointsEquiv K).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    specialIsogeny_specialIsogeny, b2ChevalleyDatumPointsEquiv_frobenius]

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` as a monoid homomorphism is the prime
Frobenius.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_comp_self :
    (b2ChevalleyDatumSpecialIsogeny K).comp (b2ChevalleyDatumSpecialIsogeny K) =
      b2ChevalleyDatum.frobenius 2 1 K :=
  MonoidHom.ext (b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny K)

/-! ## Action on simple root subgroups, Weyl elements, coroots, and torus points -/

/-- **Pinning equation on positive simple root subgroups.** At Bourbaki node `i` of `B₂`, the
special isogeny permutes the node by `b2LengthPerm` and raises the additive parameter to
`((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat`, namely `1` at the long node `0` and `2` at
the short node `1`. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (t : K) :
    b2ChevalleyDatumSpecialIsogeny K
        (b2ChevalleyDatum.rootSubgroupPoints ((DynkinType.B 2).simpleIndex ht i) K
          (Multiplicative.ofAdd t)) =
      b2ChevalleyDatum.rootSubgroupPoints
        ((DynkinType.B 2).simpleIndex ht (b2LengthPerm i)) K
        (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat)) := by
  obtain ⟨j, rfl⟩ := (finCongr (DynkinType.rank_B 2)).symm.surjective i
  apply (b2ChevalleyDatumPointsEquiv K).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex, b2NodeEquiv_b2LengthPerm,
    b2NodeEquiv_apply, b2LengthPerm_apply, Equiv.apply_symm_apply,
    rootLength_B2_finCongr_symm]
  fin_cases j
  · simp only [Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Equiv.swap_apply_left,
      lengthPermRankTwo_apply_zero, ↓reduceIte, Int.toNat_one, pow_one]
    exact specialIsogeny_rootSubgroupPoints_inl_last K t
  · simp only [Nat.reduceAdd, Fin.isValue, Fin.mk_one, Equiv.swap_apply_right,
      lengthPermRankTwo_apply_one, zero_ne_one, ↓reduceIte, Int.reduceToNat]
    exact specialIsogeny_rootSubgroupPoints_inl_zero K t

/-- **Pinning equation on negative simple root subgroups.** At Bourbaki node `i` of `B₂`, the
special isogeny permutes the negative simple root by `b2LengthPerm` with the same root-length
exponent. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_reflectionPerm_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (t : K) :
    b2ChevalleyDatumSpecialIsogeny K
        (b2ChevalleyDatum.rootSubgroupPoints
          (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.B 2).simpleIndex ht i) ((DynkinType.B 2).simpleIndex ht i)) K
          (Multiplicative.ofAdd t)) =
      b2ChevalleyDatum.rootSubgroupPoints
        (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((DynkinType.B 2).simpleIndex ht (b2LengthPerm i))
          ((DynkinType.B 2).simpleIndex ht (b2LengthPerm i))) K
        (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat)) := by
  obtain ⟨j, rfl⟩ := (finCongr (DynkinType.rank_B 2)).symm.surjective i
  apply (b2ChevalleyDatumPointsEquiv K).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex,
    b2NodeEquiv_b2LengthPerm, b2NodeEquiv_apply, b2LengthPerm_apply, Equiv.apply_symm_apply,
    rootLength_B2_finCongr_symm]
  fin_cases j
  · simp only [Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Equiv.swap_apply_left,
      lengthPermRankTwo_apply_zero, ↓reduceIte, Int.toNat_one, pow_one]
    exact specialIsogeny_rootSubgroupPoints_inr_last K t
  · simp only [Nat.reduceAdd, Fin.isValue, Fin.mk_one, Equiv.swap_apply_right,
      lengthPermRankTwo_apply_one, zero_ne_one, ↓reduceIte, Int.reduceToNat]
    exact specialIsogeny_rootSubgroupPoints_inr_zero K t

/-- **The special isogeny carries Steinberg's simple-root Weyl element `nᵢ(s)` to
`n_{σ i}(s ^ eᵢ)`.** -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_weylElement_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (s : Kˣ) :
    b2ChevalleyDatumSpecialIsogeny K
        (b2ChevalleyDatum.weylElement ((DynkinType.B 2).simpleIndex ht i) K s) =
      b2ChevalleyDatum.weylElement
        ((DynkinType.B 2).simpleIndex ht (b2LengthPerm i)) K
        (s ^ ((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat) := by
  obtain rfl : ht = DynkinType.valid_B.mpr le_rfl := Subsingleton.elim _ _
  simpa only [one_mul] using
    b2ChevalleyDatum.map_weylElement_eq_weylElement_mul_pow b2ChevalleyDatum
      (b2ChevalleyDatumSpecialIsogeny K) (j := b2LengthPerm i) 1
      (e := ((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat)
      (by rw [CharTwo.neg_one_eq_one, one_pow])
      (fun u => by simp)
      (fun u => by simp) s

/-- **The special isogeny carries the simple coroot `hᵢ(s)` to `h_{σ i}(s ^ eᵢ)`.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_simpleCorootPoints
    (i : Fin (DynkinType.B 2).rank) (s : Kˣ) :
    b2ChevalleyDatumSpecialIsogeny K (b2ChevalleyDatum.simpleCorootPoints i K s) =
      b2ChevalleyDatum.simpleCorootPoints (b2LengthPerm i) K
        (s ^ ((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat) :=
  b2ChevalleyDatum.map_simpleCorootPoints_eq_simpleCorootPoints_pow b2ChevalleyDatum
    (b2ChevalleyDatumSpecialIsogeny K) 1
    (by rw [CharTwo.neg_one_eq_one, one_pow])
    (fun u => by simp)
    (fun u => by simp) s

/-- **In Bourbaki `B₂` fundamental-weight coordinates, `b2ChevalleyDatumSpecialIsogeny` sends
`(s₀, s₁)` to `(s₁ ^ 2, s₀)`, i.e. `i ↦ s (b2LengthPerm i) ^ ((B 2).rootLength i).toNat`.** -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_torusPoints (s : Fin (DynkinType.B 2).rank → Kˣ) :
    b2ChevalleyDatumSpecialIsogeny K (b2ChevalleyDatum.torusPoints K s) =
      b2ChevalleyDatum.torusPoints K
        (fun i => s (b2LengthPerm i) ^ ((DynkinType.B 2).rootLength i).toNat) := by
  apply (b2ChevalleyDatumPointsEquiv K).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints,
    specialIsogeny_b2WeightTorusPoints,
    b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [b2LengthPerm_apply, Equiv.apply_symm_apply, rootLength_B2_finCongr_symm]
  fin_cases j <;> simp

/-- **The character pullback of `b2ChevalleyDatumSpecialIsogeny` on the torus of `b2ChevalleyDatum`
is `b2SpecialIsogenyWeightMap`.** -/
theorem isCharacterMap_b2ChevalleyDatumSpecialIsogeny :
    IsCharacterMap (b2ChevalleyDatum.torusPoints K) (b2ChevalleyDatumSpecialIsogeny K)
      b2SpecialIsogenyWeightMap := by
  have hcast (i : Fin (DynkinType.B 2).rank) :
      ((DynkinType.B 2).rootLength (b2LengthPerm i) : ℤ) =
        (((DynkinType.B 2).rootLength (b2LengthPerm i)).toNat : ℤ) := by
    obtain ⟨j, rfl⟩ := (finCongr (DynkinType.rank_B 2)).symm.surjective i
    rw [b2LengthPerm_apply, Equiv.apply_symm_apply, rootLength_B2_finCongr_symm]
    fin_cases j <;> simp
  simpa only [MonoidHom.comp_id,
    show b2ChevalleyDatum.fullWeightTorusRestriction K = MonoidHom.id _ from
      MonoidHom.ext b2ChevalleyDatum_fullWeightTorusRestriction] using
    b2ChevalleyDatum.isCharacterMap_of_rootSubgroupPoints (b2ChevalleyDatumSpecialIsogeny K)
      b2LengthPerm (fun _ => 1)
      (fun j => ((DynkinType.B 2).rootLength (b2LengthPerm j)).toNat)
      (fun _ => by rw [CharTwo.neg_one_eq_one, one_pow])
      (fun j u => by simp)
      (fun j u => by simp)
      b2SpecialIsogenyWeightMap
      (fun χ j => by rw [b2SpecialIsogenyWeightMap_apply, ← hcast j])

end CharacteristicTwo

end

end TauCeti.SpStd
