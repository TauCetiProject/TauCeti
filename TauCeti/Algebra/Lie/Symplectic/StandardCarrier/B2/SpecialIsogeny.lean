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
import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Basic

/-!
# The special isogeny of the rank-two symplectic B₂ Chevalley datum

Over any commutative ring `A`, the integral defining-ideal identifications
`TauCeti.SpStd.kostantToralDefiningIdeal_b2ChevalleyDatum_eq_definingIdeal` and
`TauCeti.SpStd.definingIdeal_eq_symplecticDefiningHopfIdeal` identify the point group
`b2ChevalleyDatum.points A` of the full-weight `B₂` Chevalley datum `TauCeti.SpStd.b2ChevalleyDatum`
with `TauCeti.GLSymplecticFin 2 A` (`TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin`).
When `A` has characteristic two, conjugating the `2 × 2` minor endomorphism
`TauCeti.specialIsogeny` across that equivalence yields
`TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny A`;
over a field `K` of characteristic two, `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv K` intertwines it
with `TauCeti.SpStd.specialIsogeny K`.

Reading the carrier in Bourbaki `B₂` numbering aligns the represented matrix endomorphism directly
with the pinned root-datum isogeny `TauCeti.DynkinType.b2SpecialIsogeny` and the Bourbaki
length-exchanging permutation `TauCeti.lengthPermRankTwo`
(`TauCeti.DynkinType.isSpecialNodePerm_B2`, unique by
`TauCeti.DynkinType.IsSpecialNodePerm.unique`):

* Over any commutative ring `A`, `b2ChevalleyDatumPointsEquiv A` identifies the torus
  `b2ChevalleyDatum.torusPoints A` with `TauCeti.SpStd.b2WeightTorusPoints A`.
* Over any commutative ring `A` of characteristic two, `b2ChevalleyDatumSpecialIsogeny A` squares to
  the prime Frobenius `b2ChevalleyDatum.frobenius 2 1 A`.
* On the positive and negative simple root subgroups, Weyl elements, and simple coroots at node
  `i`, it acts by `TauCeti.lengthPermRankTwo` and raises the parameter to
  `((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat`, which is `1` at the long node `0` and
  `2` at the short node `1`.
* On the full-weight torus `b2ChevalleyDatum.torusPoints A`, it sends `s` to
  `fun i => s (lengthPermRankTwo i) ^ ((DynkinType.B 2).rootLength i).toNat` and pulls characters
  back by `TauCeti.DynkinType.b2SpecialIsogeny.weightMap`.

No odd power of the isogeny or fixed-point subgroup is formed here.

## Main definitions

* `TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin`: the matrix-preserving isomorphism
  between `b2ChevalleyDatum.points A` and `GLSymplecticFin 2 A` over any commutative ring `A`.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny`: the special isogeny of
  `b2ChevalleyDatum.points A` over any commutative ring `A` of characteristic two.

## Main results

* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints`: identification of the datum
  torus with `b2WeightTorusPoints` over any commutative ring.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny` and
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_comp_self`: the square of the special isogeny is
  the prime Frobenius `b2ChevalleyDatum.frobenius 2 1 A`.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_reflectionPerm_simpleIndex`,
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_weylElement_simpleIndex`, and
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_simpleCorootPoints`: the pinning equations on
  simple root subgroups, Weyl elements, and simple coroots.
* `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_torusPoints` and
  `TauCeti.SpStd.isCharacterMap_b2ChevalleyDatumSpecialIsogeny`: torus action and character
  pullback by `DynkinType.b2SpecialIsogeny.weightMap`.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_symm_specialIsogeny`: intertwining with
  `SpStd.specialIsogeny` over a field of characteristic two.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.

The point-group transport and character-pullback equations parallel
`TauCeti.SpStd.specialIsogeny`, `TauCeti.SpStd.isCharacterMap_specialIsogeny`, and
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.CharacterMap`.
-/

public section

namespace TauCeti.SpStd

open _root_.Matrix

universe v

/-- Composing `b2NodeEquiv` with `lengthPermRankTwo` cancels the node swap. -/
@[simp↓]
theorem b2NodeEquiv_lengthPermRankTwo (i : Fin (DynkinType.B 2).rank) :
    b2NodeEquiv (lengthPermRankTwo i) = i :=
  (b2NodeEquiv_apply_eq_lengthPermRankTwo _).trans (lengthPermRankTwo_lengthPermRankTwo i)

noncomputable section

/-! ## Identification of the Bourbaki `B₂` torus and symplectic points over commutative rings -/

/-- **Across `b2ChevalleyDatumPointsEquiv`, the torus of `b2ChevalleyDatum` is
`b2WeightTorusPoints`.** This is not a `simp` lemma because
`b2ChevalleyDatumPointsEquiv_torusPoints` already normalizes the left-hand side to
`weightTorusPoints 1`. -/
theorem b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatumPointsEquiv A (b2ChevalleyDatum.torusPoints A s) =
      b2WeightTorusPoints A s := by
  refine (b2ChevalleyDatumPointsEquiv_torusPoints A s).trans ((?_ : _ = _).trans
    (b2WeightTorusPoints_apply A s).symm)
  congr 1
  funext i
  rw [Function.comp_apply, b2NodeEquiv_symm_apply]
  fin_cases i <;> simp

/-- The inverse point isomorphism carries `b2WeightTorusPoints A` to
`b2ChevalleyDatum.torusPoints A` with the same Bourbaki `B₂` coordinates. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) :
    (b2ChevalleyDatumPointsEquiv A).symm (b2WeightTorusPoints A s) =
      b2ChevalleyDatum.torusPoints A s :=
  (MulEquiv.symm_apply_eq (b2ChevalleyDatumPointsEquiv A)).mpr
    (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A s).symm

/-- **Over any commutative ring `A`, the point group of `b2ChevalleyDatum` is canonically
isomorphic as a matrix subgroup to `GLSymplecticFin 2 A`.** -/
def b2ChevalleyDatumPointsMulEquivGLSymplecticFin (A : Type v) [CommRing A] :
    b2ChevalleyDatum.points A ≃* GLSymplecticFin 2 A :=
  (b2ChevalleyDatumPointsEquiv A).trans <| MulEquiv.subgroupCongr <| by
    ext g
    have h := ConstantForm.mem_definingPointsSubgroup_iff ℤ ((1 + 1) + (1 + 1)) (JFin (1 + 1) ℤ)
      ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) ((1 + 1) + (1 + 1))).symm g)
    rw [MulEquiv.apply_symm_apply, CommHopfAlgCat.mem_quotientPointsSubgroup_iff, JFin_map,
      ← GLSymplecticFin.mem_iff] at h
    rwa [points_def, definingIdeal_eq_symplecticDefiningHopfIdeal,
      GeneralLinear.mem_hopfIdealPointsSubgroup_iff]

/-- `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` preserves the underlying invertible `4 × 4`
matrix. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply (A : Type v) [CommRing A]
    (g : b2ChevalleyDatum.points A) :
    ((b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g : GLSymplecticFin 2 A) :
        GL (Fin (2 + 2)) A) =
      (g : GL (Fin b2ChevalleyDatum.dim) A) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.trans_apply]
  exact (MulEquiv.subgroupCongr_apply _ _).trans (coe_b2ChevalleyDatumPointsEquiv A g)

/-- The inverse of `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` preserves the underlying
invertible `4 × 4` matrix. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_symm_apply (A : Type v) [CommRing A]
    (g : GLSymplecticFin 2 A) :
    (((b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm g : b2ChevalleyDatum.points A) :
        GL (Fin b2ChevalleyDatum.dim) A) =
      (g : GL (Fin (2 + 2)) A) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.symm_trans_apply,
    coe_b2ChevalleyDatumPointsEquiv_symm]
  exact MulEquiv.subgroupCongr_symm_apply _ g

/-! ## The special isogeny in characteristic two -/

section CharacteristicTwo

variable (A : Type v) [CommRing A] [CharP A 2]

/-- **The special isogeny of the rank-two symplectic `B₂` Chevalley datum in characteristic two**,
transported from `TauCeti.specialIsogeny` across
`b2ChevalleyDatumPointsMulEquivGLSymplecticFin`. -/
def b2ChevalleyDatumSpecialIsogeny :
    b2ChevalleyDatum.points A →* b2ChevalleyDatum.points A :=
  (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := A)).comp
      (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).toMonoidHom)

/-- `b2ChevalleyDatumSpecialIsogeny` conjugates `TauCeti.specialIsogeny` by
`b2ChevalleyDatumPointsMulEquivGLSymplecticFin`. -/
theorem b2ChevalleyDatumSpecialIsogeny_def :
    b2ChevalleyDatumSpecialIsogeny A =
      (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm.toMonoidHom.comp
        ((TauCeti.specialIsogeny (R := A)).comp
          (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).toMonoidHom) :=
  (rfl)

/-- `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` intertwines `b2ChevalleyDatumSpecialIsogeny`
with `TauCeti.specialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin A (b2ChevalleyDatumSpecialIsogeny A g) =
      TauCeti.specialIsogeny (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g) := by
  simp [b2ChevalleyDatumSpecialIsogeny_def]

/-- On underlying `4 × 4` matrices, `b2ChevalleyDatumSpecialIsogeny` is the matrix of `2 × 2`
minors `Matrix.symplecticSpecialIsogeny`. -/
@[simp]
theorem coe_b2ChevalleyDatumSpecialIsogeny (g : b2ChevalleyDatum.points A) :
    ((b2ChevalleyDatumSpecialIsogeny A g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) A) :
        Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) A) =
      Matrix.symplecticSpecialIsogeny
        ((g : GeneralLinearGroup (Fin b2ChevalleyDatum.dim) A) :
          Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) A) := by
  rw [b2ChevalleyDatumSpecialIsogeny_def, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  exact (congrArg Units.val
    (coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_symm_apply A _)).trans
    ((TauCeti.coe_specialIsogeny _).trans
      (congrArg Matrix.symplecticSpecialIsogeny
        (congrArg Units.val
          (coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply A g))))

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` is the prime Frobenius of
`b2ChevalleyDatum`.** Marked `@[simp↓]` so nested applications reduce to `frobenius` before inner
`@[simp↓]` generator rules fire. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatumSpecialIsogeny A g) =
      b2ChevalleyDatum.frobenius 2 1 A g := by
  let M := b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g
  have hsq : (((TauCeti.specialIsogeny (TauCeti.specialIsogeny M) : GLSymplecticFin 2 A) :
      GL (Fin (2 + 2)) A) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A) =
      ((M : GL (Fin (2 + 2)) A) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A).map (· ^ 2) := by
    rw [TauCeti.coe_specialIsogeny, TauCeti.coe_specialIsogeny,
      Matrix.symplecticSpecialIsogeny_symplecticSpecialIsogeny (GLSymplecticFin.mem_iff.mp M.2)]
  have hfrob :
      ((g : GL (Fin b2ChevalleyDatum.dim) A) :
        Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) A).map (· ^ 2) =
      (((b2ChevalleyDatum.frobenius 2 1 A g : b2ChevalleyDatum.points A) :
        GL (Fin b2ChevalleyDatum.dim) A) :
        Matrix (Fin b2ChevalleyDatum.dim) (Fin b2ChevalleyDatum.dim) A) := by
    ext i j
    rw [Matrix.map_apply]
    have hij := b2ChevalleyDatum.coe_frobenius_apply 2 1 A g i j
    rw [pow_one] at hij
    exact hij.symm
  apply Subtype.ext
  apply Units.ext
  exact (congrArg Units.val
    (coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply A _)).symm.trans
    ((congrArg (fun x : GLSymplecticFin 2 A => Units.val (x : GL (Fin (2 + 2)) A))
      ((b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny A _).trans
        (congrArg TauCeti.specialIsogeny
          (b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny A
            g)))).trans
      (hsq.trans
        ((congrArg (fun X : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A => X.map (· ^ 2))
          (congrArg Units.val
            (coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply A g))).trans
          hfrob)))

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` as a monoid homomorphism is the prime
Frobenius.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_comp_self :
    (b2ChevalleyDatumSpecialIsogeny A).comp (b2ChevalleyDatumSpecialIsogeny A) =
      b2ChevalleyDatum.frobenius 2 1 A :=
  MonoidHom.ext (b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny A)

/-! ## Action on simple root subgroups, Weyl elements, coroots, and torus points -/

private theorem b2ChevalleyDatumSpecialIsogeny_eq_of_coe_eq
    {x y : b2ChevalleyDatum.points A} {u v : GLSymplecticFin 2 A}
    (hx : (b2ChevalleyDatumPointsEquiv A x : GL (Fin ((1 + 1) + (1 + 1))) A) = u.1)
    (hy : (b2ChevalleyDatumPointsEquiv A y : GL (Fin ((1 + 1) + (1 + 1))) A) = v.1)
    (huv : TauCeti.specialIsogeny u = v) :
    b2ChevalleyDatumSpecialIsogeny A x = y := by
  apply (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).injective
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny]
  have hxu : b2ChevalleyDatumPointsMulEquivGLSymplecticFin A x = u :=
    Subtype.ext hx
  have hyv : b2ChevalleyDatumPointsMulEquivGLSymplecticFin A y = v :=
    Subtype.ext hy
  rw [hxu, hyv, huv]

omit [CharP A 2] in
private theorem rootSubgroupPoints_inl_zero_coe_eq (t : A) :
    (rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd t) : GL (Fin ((1 + 1) + (1 + 1))) A) =
      (GLSymplecticFin.differenceShortRootUnit (show (0 : Fin (1 + 1)) ≠ 1 by decide) t :
        GLSymplecticFin 2 A).1 := by
  rw [rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last 1 0 (by decide),
    _root_.toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _ rfl
      (by simpa using Fin.orderSucc_castSucc (0 : Fin 1) : Order.succ (0 : Fin (1 + 1)) = 1)]

omit [CharP A 2] in
private theorem rootSubgroupPoints_inl_one_coe_eq (t : A) :
    (rootSubgroupPoints 1 (.inl 1) A (Multiplicative.ofAdd t) : GL (Fin ((1 + 1) + (1 + 1))) A) =
      (GLSymplecticFin.positiveLongRootTransvectionUnit 1 t : GLSymplecticFin 2 A).1 := by
  have hlast : (1 : Fin (1 + 1)) = Fin.last 1 := by simp [Fin.last]
  rw [hlast, rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit,
    _root_.toAdd_ofAdd, ← hlast]

omit [CharP A 2] in
private theorem rootSubgroupPoints_inr_zero_coe_eq (t : A) :
    (rootSubgroupPoints 1 (.inr 0) A (Multiplicative.ofAdd t) : GL (Fin ((1 + 1) + (1 + 1))) A) =
      (GLSymplecticFin.differenceShortRootUnit (show (1 : Fin (1 + 1)) ≠ 0 by decide) t :
        GLSymplecticFin 2 A).1 := by
  rw [rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last 1 0 (by decide),
    _root_.toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _
      (by simpa using Fin.orderSucc_castSucc (0 : Fin 1) : Order.succ (0 : Fin (1 + 1)) = 1) rfl]

omit [CharP A 2] in
private theorem rootSubgroupPoints_inr_one_coe_eq (t : A) :
    (rootSubgroupPoints 1 (.inr 1) A (Multiplicative.ofAdd t) : GL (Fin ((1 + 1) + (1 + 1))) A) =
      (GLSymplecticFin.negativeLongRootTransvectionUnit 1 t : GLSymplecticFin 2 A).1 := by
  have hlast : (1 : Fin (1 + 1)) = Fin.last 1 := by simp [Fin.last]
  rw [hlast, rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit,
    _root_.toAdd_ofAdd, ← hlast]

/-- **Pinning equation on positive simple root subgroups.** At Bourbaki node `i` of `B₂`, the
special isogeny permutes the node by `lengthPermRankTwo` and raises the additive parameter to
`((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat`, namely `1` at the long node `0` and `2`
at the short node `1`. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (t : A) :
    b2ChevalleyDatumSpecialIsogeny A
        (b2ChevalleyDatum.rootSubgroupPoints ((DynkinType.B 2).simpleIndex ht i) A
          (Multiplicative.ofAdd t)) =
      b2ChevalleyDatum.rootSubgroupPoints
        ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo i)) A
        (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat)) := by
  obtain ⟨j, rfl⟩ := b2NodeEquiv.symm.surjective i
  have hswap : lengthPermRankTwo (b2NodeEquiv.symm j) = j :=
    (b2NodeEquiv_apply_eq_lengthPermRankTwo (b2NodeEquiv.symm j)).symm.trans
      (b2NodeEquiv.apply_symm_apply j)
  have h₁ :
      (b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints ((DynkinType.B 2).simpleIndex ht (b2NodeEquiv.symm j))
          A (Multiplicative.ofAdd t)) : GL (Fin ((1 + 1) + (1 + 1))) A) =
        (rootSubgroupPoints 1 (.inl j) A (Multiplicative.ofAdd t) :
          GL (Fin ((1 + 1) + (1 + 1))) A) := by
    rw [b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex, Equiv.apply_symm_apply]
  have h₂ :
      (b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints
          ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo (b2NodeEquiv.symm j))) A
          (Multiplicative.ofAdd
            (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo (b2NodeEquiv.symm j))).toNat))) :
          GL (Fin ((1 + 1) + (1 + 1))) A) =
        (rootSubgroupPoints 1 (.inl ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) j)) A
          (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength j).toNat)) :
          GL (Fin ((1 + 1) + (1 + 1))) A) :=
    (congrArg Subtype.val
      (b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex (ht := ht)
        (lengthPermRankTwo (b2NodeEquiv.symm j)) A _)).trans
      (congrArg₂
        (fun (k : Fin 2) (m : ℕ) =>
          (rootSubgroupPoints 1 (.inl k) A (Multiplicative.ofAdd (t ^ m)) :
            GL (Fin ((1 + 1) + (1 + 1))) A))
        ((congrArg (fun x : Fin 2 => b2NodeEquiv x) hswap).trans (b2NodeEquiv_apply j))
        (congrArg (fun k : Fin 2 => ((DynkinType.B 2).rootLength k).toNat) hswap))
  fin_cases j
  · refine b2ChevalleyDatumSpecialIsogeny_eq_of_coe_eq A
      (h₁.trans (rootSubgroupPoints_inl_zero_coe_eq A t)) (h₂.trans ?_)
      (TauCeti.specialIsogeny_differenceShortRootUnit t)
    simpa [DynkinType.rootLength_B] using rootSubgroupPoints_inl_one_coe_eq A (t ^ 2)
  · refine b2ChevalleyDatumSpecialIsogeny_eq_of_coe_eq A
      (h₁.trans (rootSubgroupPoints_inl_one_coe_eq A t)) (h₂.trans ?_)
      (TauCeti.specialIsogeny_positiveLongRootTransvectionUnit t)
    simpa [DynkinType.rootLength_B] using rootSubgroupPoints_inl_zero_coe_eq A t

/-- **Pinning equation on negative simple root subgroups.** At Bourbaki node `i` of `B₂`, the
special isogeny permutes the negative simple root by `lengthPermRankTwo` with the same root-length
exponent. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_rootSubgroupPoints_reflectionPerm_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (t : A) :
    b2ChevalleyDatumSpecialIsogeny A
        (b2ChevalleyDatum.rootSubgroupPoints
          (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
             ((DynkinType.B 2).simpleIndex ht i) ((DynkinType.B 2).simpleIndex ht i)) A
          (Multiplicative.ofAdd t)) =
      b2ChevalleyDatum.rootSubgroupPoints
        (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo i))
          ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo i))) A
        (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat)) := by
  obtain ⟨j, rfl⟩ := b2NodeEquiv.symm.surjective i
  have hswap : lengthPermRankTwo (b2NodeEquiv.symm j) = j :=
    (b2NodeEquiv_apply_eq_lengthPermRankTwo (b2NodeEquiv.symm j)).symm.trans
      (b2NodeEquiv.apply_symm_apply j)
  have h₁ :
      (b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints
          (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.B 2).simpleIndex ht (b2NodeEquiv.symm j))
            ((DynkinType.B 2).simpleIndex ht (b2NodeEquiv.symm j))) A
          (Multiplicative.ofAdd t)) : GL (Fin ((1 + 1) + (1 + 1))) A) =
        (rootSubgroupPoints 1 (.inr j) A (Multiplicative.ofAdd t) :
          GL (Fin ((1 + 1) + (1 + 1))) A) := by
    rw [b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex,
      Equiv.apply_symm_apply]
  have h₂ :
      (b2ChevalleyDatumPointsEquiv A
        (b2ChevalleyDatum.rootSubgroupPoints
          (((DynkinType.B 2).simplyConnectedRootDatum ht).reflectionPerm
            ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo (b2NodeEquiv.symm j)))
            ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo (b2NodeEquiv.symm j)))) A
          (Multiplicative.ofAdd
            (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo (b2NodeEquiv.symm j))).toNat))) :
          GL (Fin ((1 + 1) + (1 + 1))) A) =
        (rootSubgroupPoints 1 (.inr ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) j)) A
          (Multiplicative.ofAdd (t ^ ((DynkinType.B 2).rootLength j).toNat)) :
          GL (Fin ((1 + 1) + (1 + 1))) A) :=
    (congrArg Subtype.val
      (b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex (ht := ht)
        (lengthPermRankTwo (b2NodeEquiv.symm j)) A _)).trans
      (congrArg₂
        (fun (k : Fin 2) (m : ℕ) =>
          (rootSubgroupPoints 1 (.inr k) A (Multiplicative.ofAdd (t ^ m)) :
            GL (Fin ((1 + 1) + (1 + 1))) A))
        ((congrArg (fun x : Fin 2 => b2NodeEquiv x) hswap).trans (b2NodeEquiv_apply j))
        (congrArg (fun k : Fin 2 => ((DynkinType.B 2).rootLength k).toNat) hswap))
  fin_cases j
  · refine b2ChevalleyDatumSpecialIsogeny_eq_of_coe_eq A
      (h₁.trans (rootSubgroupPoints_inr_zero_coe_eq A t)) (h₂.trans ?_)
      (TauCeti.specialIsogeny_differenceShortRootUnit_one_zero t)
    simpa [DynkinType.rootLength_B] using rootSubgroupPoints_inr_one_coe_eq A (t ^ 2)
  · refine b2ChevalleyDatumSpecialIsogeny_eq_of_coe_eq A
      (h₁.trans (rootSubgroupPoints_inr_one_coe_eq A t)) (h₂.trans ?_)
      (TauCeti.specialIsogeny_negativeLongRootTransvectionUnit t)
    simpa [DynkinType.rootLength_B] using rootSubgroupPoints_inr_zero_coe_eq A t

/-- **The special isogeny carries Steinberg's simple-root Weyl element `nᵢ(s)` to
`n_{σ i}(s ^ eᵢ)`.** -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_weylElement_simpleIndex
    {ht : (DynkinType.B 2).Valid} (i : Fin (DynkinType.B 2).rank) (s : Aˣ) :
    b2ChevalleyDatumSpecialIsogeny A
        (b2ChevalleyDatum.weylElement ((DynkinType.B 2).simpleIndex ht i) A s) =
      b2ChevalleyDatum.weylElement
        ((DynkinType.B 2).simpleIndex ht (lengthPermRankTwo i)) A
        (s ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat) := by
  obtain rfl : ht = DynkinType.valid_B.mpr le_rfl := Subsingleton.elim _ _
  simpa only [one_mul] using
    b2ChevalleyDatum.map_weylElement_eq_weylElement_mul_pow b2ChevalleyDatum
      (b2ChevalleyDatumSpecialIsogeny A) (j := lengthPermRankTwo i) 1
      (e := ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat)
      (by rw [CharTwo.neg_one_eq_one, one_pow])
      (fun u => by simp)
      (fun u => by simp) s

/-- **The special isogeny carries the simple coroot `hᵢ(s)` to `h_{σ i}(s ^ eᵢ)`.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_simpleCorootPoints
    (i : Fin (DynkinType.B 2).rank) (s : Aˣ) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatum.simpleCorootPoints i A s) =
      b2ChevalleyDatum.simpleCorootPoints (lengthPermRankTwo i) A
        (s ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat) :=
  b2ChevalleyDatum.map_simpleCorootPoints_eq_simpleCorootPoints_pow b2ChevalleyDatum
    (b2ChevalleyDatumSpecialIsogeny A) 1
    (by rw [CharTwo.neg_one_eq_one, one_pow])
    (fun u => by simp)
    (fun u => by simp) s

/-- **The character pullback of `b2ChevalleyDatumSpecialIsogeny` on the torus of `b2ChevalleyDatum`
is `DynkinType.b2SpecialIsogeny.weightMap`.** -/
theorem isCharacterMap_b2ChevalleyDatumSpecialIsogeny :
    IsCharacterMap (b2ChevalleyDatum.torusPoints A) (b2ChevalleyDatumSpecialIsogeny A)
      DynkinType.b2SpecialIsogeny.weightMap :=
  isCharacterMap_iff.mpr fun s => by
    simpa only [MonoidHom.comp_apply, b2ChevalleyDatum_fullWeightTorusRestriction] using
      (b2ChevalleyDatum.isCharacterMap_of_rootSubgroupPoints (b2ChevalleyDatumSpecialIsogeny A)
        lengthPermRankTwo (fun _ => 1)
        (fun j => ((DynkinType.B 2).rootLength (lengthPermRankTwo j)).toNat)
        (fun _ => by rw [CharTwo.neg_one_eq_one, one_pow])
        (fun j u => by simp)
        (fun j u => by simp)
        DynkinType.b2SpecialIsogeny.weightMap
        (fun χ j => (DynkinType.b2SpecialIsogeny_weightMap_apply χ j).trans
          (congrArg (· * χ (lengthPermRankTwo j))
            (Int.toNat_of_nonneg
              (DynkinType.rootLength_pos (DynkinType.B 2) _).le).symm))).map_apply s

/-- **In Bourbaki `B₂` fundamental-weight coordinates, `b2ChevalleyDatumSpecialIsogeny` sends
`(s₀, s₁)` to `(s₁ ^ 2, s₀)`, i.e. `i ↦ s (lengthPermRankTwo i) ^ ((B 2).rootLength i).toNat`.** -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_torusPoints (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatum.torusPoints A s) =
      b2ChevalleyDatum.torusPoints A
        (fun i => s (lengthPermRankTwo i) ^ ((DynkinType.B 2).rootLength i).toNat) := by
  rw [(isCharacterMap_b2ChevalleyDatumSpecialIsogeny A).map_apply s]
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := b2NodeEquiv.symm.surjective i
  rw [b2NodeEquiv_symm_apply]
  let s' : Fin 2 → Aˣ := s
  -- Unify `(DynkinType.B 2).rank` with `2` on the torus parameter so `torusPointMap_apply` fires.
  change torusPointMap DynkinType.b2SpecialIsogeny.weightMap s'
      ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) j) =
    s' (lengthPermRankTwo ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) j)) ^
      ((DynkinType.B 2).rootLength ((Equiv.swap 0 1 : Equiv.Perm (Fin 2)) j)).toNat
  fin_cases j <;>
    simp [torusPointMap_apply, DynkinType.b2SpecialIsogeny_weightMap,
      DynkinType.b2SpecialIsogenyMatrix_def, torusCharacter_def, Fin.prod_univ_two,
      DynkinType.rootLength_B]

end CharacteristicTwo

/-! ## Intertwining with `SpStd.specialIsogeny` over fields of characteristic two -/

section Field

variable (K : Type v) [Field K] [CharP K 2]

/-- Over a field of characteristic two, `b2ChevalleyDatumPointsEquiv` intertwines
`b2ChevalleyDatumSpecialIsogeny` with `SpStd.specialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points K) :
    b2ChevalleyDatumPointsEquiv K (b2ChevalleyDatumSpecialIsogeny K g) =
      specialIsogeny K (b2ChevalleyDatumPointsEquiv K g) := by
  have hg (x : b2ChevalleyDatum.points K) :
      pointsMulEquivGLSymplecticFin 1 K (b2ChevalleyDatumPointsEquiv K x) =
        b2ChevalleyDatumPointsMulEquivGLSymplecticFin K x :=
    Subtype.ext ((coe_pointsMulEquivGLSymplecticFin_apply 1 _).trans
      ((coe_b2ChevalleyDatumPointsEquiv K x).trans
        (coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply K x).symm))
  apply (pointsMulEquivGLSymplecticFin 1 K).injective
  rw [hg, pointsMulEquivGLSymplecticFin_specialIsogeny, hg,
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny]

/-- Over a field of characteristic two, the inverse point isomorphism intertwines
`SpStd.specialIsogeny` with `b2ChevalleyDatumSpecialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_specialIsogeny (g : points 1 K) :
    (b2ChevalleyDatumPointsEquiv K).symm (specialIsogeny K g) =
      b2ChevalleyDatumSpecialIsogeny K ((b2ChevalleyDatumPointsEquiv K).symm g) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    MulEquiv.apply_symm_apply]

end Field

end

end TauCeti.SpStd
