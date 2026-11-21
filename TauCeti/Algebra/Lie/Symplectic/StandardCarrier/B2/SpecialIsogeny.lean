/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.B2.Realization
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.CharacterMap
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.CharacterMap

/-!
# The special isogeny of the rank-two symplectic B₂ Chevalley datum

Over any commutative ring `A`, combining `TauCeti.SpStd.b2ChevalleyDatum_points` with
`TauCeti.SpStd.points_eq_GLSymplecticFin` identifies the point group
`b2ChevalleyDatum.points A` of the full-weight `B₂` Chevalley datum `TauCeti.SpStd.b2ChevalleyDatum`
with `TauCeti.GLSymplecticFin 2 A` (`TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin`).
When `A` has characteristic two, conjugating `TauCeti.SpStd.specialIsogeny A` across
`TauCeti.SpStd.b2ChevalleyDatumPointsEquiv A` yields
`TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny A`, intertwined with `TauCeti.specialIsogeny` across
`TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin A`.

Reading the carrier in Bourbaki `B₂` numbering aligns the represented matrix endomorphism directly
with the pinned root-datum isogeny `TauCeti.DynkinType.b2SpecialIsogeny` and the Bourbaki
length-exchanging permutation `TauCeti.lengthPermRankTwo`:

* Over any commutative ring `A`, `b2ChevalleyDatumPointsEquiv A` identifies the torus
  `b2ChevalleyDatum.torusPoints A` with `TauCeti.SpStd.b2WeightTorusPoints A`.
* Over any commutative ring `A` of characteristic two, `b2ChevalleyDatumSpecialIsogeny A` is
  natural in `A`, commutes with Frobenius, and squares to the prime Frobenius
  `b2ChevalleyDatum.frobenius 2 1 A`.
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

* `TauCeti.SpStd.b2ChevalleyDatum_points_eq_GLSymplecticFin` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin_map`: subgroup equality and
  ring-change naturality with `GLSymplecticFin 2`.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints` and
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints`: identification of the datum
  torus with `b2WeightTorusPoints` over any commutative ring.
* `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny`,
  `TauCeti.SpStd.b2ChevalleyDatumPointsEquiv_symm_specialIsogeny`,
  `TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny`, and
  `TauCeti.SpStd.b2ChevalleyDatumPointsMulEquivGLSymplecticFin_symm_specialIsogeny`: intertwining
  with `SpStd.specialIsogeny` and `TauCeti.specialIsogeny`.
* `TauCeti.SpStd.map_b2ChevalleyDatumSpecialIsogeny` and
  `TauCeti.SpStd.b2ChevalleyDatumSpecialIsogeny_frobenius`: naturality in characteristic-two
  commutative rings and commutation with Frobenius.
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

universe v v'

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
  have hswap (s' : Fin 2 → Aˣ) :
      weightTorusPoints 1 A (s' ∘ lengthPermRankTwo) = b2WeightTorusPoints A s' := by
    refine (congrArg (weightTorusPoints 1 A) ?_).trans (b2WeightTorusPoints_apply A s').symm
    funext i
    fin_cases i <;> simp
  exact (b2ChevalleyDatumPointsEquiv_torusPoints A s).trans (hswap s)

/-- The inverse point isomorphism carries `b2WeightTorusPoints A` to
`b2ChevalleyDatum.torusPoints A` with the same Bourbaki `B₂` coordinates. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_b2WeightTorusPoints
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) :
    (b2ChevalleyDatumPointsEquiv A).symm (b2WeightTorusPoints A s) =
      b2ChevalleyDatum.torusPoints A s :=
  (MulEquiv.symm_apply_eq (b2ChevalleyDatumPointsEquiv A)).mpr
    (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A s).symm

/-- **Over any commutative ring `A`, the point subgroup of `b2ChevalleyDatum` equals
`GLSymplecticFin 2 A`.** -/
theorem b2ChevalleyDatum_points_eq_GLSymplecticFin (A : Type v) [CommRing A] :
    b2ChevalleyDatum.points A = GLSymplecticFin 2 A :=
  (b2ChevalleyDatum_points A).trans (points_eq_GLSymplecticFin 1 A)

/-- **Over any commutative ring `A`, the point group of `b2ChevalleyDatum` is canonically
isomorphic as a matrix subgroup to `GLSymplecticFin 2 A`.** -/
def b2ChevalleyDatumPointsMulEquivGLSymplecticFin (A : Type v) [CommRing A] :
    b2ChevalleyDatum.points A ≃* GLSymplecticFin 2 A :=
  (b2ChevalleyDatumPointsEquiv A).trans (pointsMulEquivGLSymplecticFin 1 A)

/-- `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` preserves the underlying invertible `4 × 4`
matrix. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_apply (A : Type v) [CommRing A]
    (g : b2ChevalleyDatum.points A) :
    ((b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g : GLSymplecticFin 2 A) :
        GL (Fin (2 + 2)) A) =
      (g : GL (Fin b2ChevalleyDatum.dim) A) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.trans_apply,
    coe_pointsMulEquivGLSymplecticFin_apply, coe_b2ChevalleyDatumPointsEquiv]

/-- The inverse of `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` preserves the underlying
invertible `4 × 4` matrix. -/
@[simp]
theorem coe_b2ChevalleyDatumPointsMulEquivGLSymplecticFin_symm_apply (A : Type v) [CommRing A]
    (g : GLSymplecticFin 2 A) :
    (((b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm g : b2ChevalleyDatum.points A) :
        GL (Fin b2ChevalleyDatum.dim) A) =
      (g : GL (Fin (2 + 2)) A) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.symm_trans_apply,
    coe_b2ChevalleyDatumPointsEquiv_symm, coe_pointsMulEquivGLSymplecticFin_symm_apply]

/-- `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` is natural with respect to ring homomorphisms
`f : A →+* B` across universes. -/
theorem b2ChevalleyDatumPointsMulEquivGLSymplecticFin_map {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin B
        ((b2ChevalleyDatum.pointsPresentation A).map
          (b2ChevalleyDatum.pointsPresentation B) f g) =
      GLSymplecticFin.map 2 A f (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.trans_apply,
    b2ChevalleyDatumPointsEquiv_map, pointsMulEquivGLSymplecticFin_map,
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.trans_apply]

/-! ## The special isogeny in characteristic two -/

section CharacteristicTwo

variable (A : Type v) [CommRing A] [CharP A 2]

/-- **The special isogeny of the rank-two symplectic `B₂` Chevalley datum in characteristic two**,
transported from `TauCeti.SpStd.specialIsogeny` across `b2ChevalleyDatumPointsEquiv`. -/
def b2ChevalleyDatumSpecialIsogeny :
    b2ChevalleyDatum.points A →* b2ChevalleyDatum.points A :=
  (b2ChevalleyDatumPointsEquiv A).symm.toMonoidHom.comp
    ((specialIsogeny A).comp (b2ChevalleyDatumPointsEquiv A).toMonoidHom)

/-- `b2ChevalleyDatumSpecialIsogeny` conjugates `SpStd.specialIsogeny` by
`b2ChevalleyDatumPointsEquiv`. -/
theorem b2ChevalleyDatumSpecialIsogeny_def :
    b2ChevalleyDatumSpecialIsogeny A =
      (b2ChevalleyDatumPointsEquiv A).symm.toMonoidHom.comp
        ((specialIsogeny A).comp (b2ChevalleyDatumPointsEquiv A).toMonoidHom) :=
  (rfl)

/-- `b2ChevalleyDatumPointsEquiv` intertwines `b2ChevalleyDatumSpecialIsogeny` with
`SpStd.specialIsogeny` over any commutative ring of characteristic two. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsEquiv A (b2ChevalleyDatumSpecialIsogeny A g) =
      specialIsogeny A (b2ChevalleyDatumPointsEquiv A g) := by
  simp [b2ChevalleyDatumSpecialIsogeny_def]

/-- The inverse point isomorphism intertwines `SpStd.specialIsogeny` with
`b2ChevalleyDatumSpecialIsogeny` over any commutative ring of characteristic two. -/
@[simp]
theorem b2ChevalleyDatumPointsEquiv_symm_specialIsogeny (g : points 1 A) :
    (b2ChevalleyDatumPointsEquiv A).symm (specialIsogeny A g) =
      b2ChevalleyDatumSpecialIsogeny A ((b2ChevalleyDatumPointsEquiv A).symm g) := by
  rw [MulEquiv.symm_apply_eq, b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    MulEquiv.apply_symm_apply]

/-- `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` intertwines `b2ChevalleyDatumSpecialIsogeny`
with `TauCeti.specialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin A (b2ChevalleyDatumSpecialIsogeny A g) =
      TauCeti.specialIsogeny (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A g) := by
  rw [b2ChevalleyDatumPointsMulEquivGLSymplecticFin, MulEquiv.trans_apply, MulEquiv.trans_apply,
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    pointsMulEquivGLSymplecticFin_specialIsogeny]

/-- The inverse of `b2ChevalleyDatumPointsMulEquivGLSymplecticFin` intertwines
`TauCeti.specialIsogeny` with `b2ChevalleyDatumSpecialIsogeny`. -/
@[simp]
theorem b2ChevalleyDatumPointsMulEquivGLSymplecticFin_symm_specialIsogeny
    (g : GLSymplecticFin 2 A) :
    (b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm (TauCeti.specialIsogeny g) =
      b2ChevalleyDatumSpecialIsogeny A
        ((b2ChevalleyDatumPointsMulEquivGLSymplecticFin A).symm g) := by
  rw [MulEquiv.symm_apply_eq,
    b2ChevalleyDatumPointsMulEquivGLSymplecticFin_b2ChevalleyDatumSpecialIsogeny,
    MulEquiv.apply_symm_apply]

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
  exact (congrArg Units.val (coe_b2ChevalleyDatumPointsEquiv_symm A _)).trans
    ((coe_specialIsogeny A _).trans
      (congrArg Matrix.symplecticSpecialIsogeny
        (congrArg Units.val (coe_b2ChevalleyDatumPointsEquiv A g))))

omit [CommRing A] [CharP A 2] in
/-- `b2ChevalleyDatumSpecialIsogeny` is natural with respect to ring homomorphisms `f : A →+* B`
between commutative rings of characteristic two. -/
@[simp]
theorem map_b2ChevalleyDatumSpecialIsogeny {A : Type v} {B : Type v'}
    [CommRing A] [CharP A 2] [CommRing B] [CharP B 2] (f : A →+* B)
    (g : b2ChevalleyDatum.points A) :
    (b2ChevalleyDatum.pointsPresentation A).map (b2ChevalleyDatum.pointsPresentation B) f
        (b2ChevalleyDatumSpecialIsogeny A g) =
      b2ChevalleyDatumSpecialIsogeny B
        ((b2ChevalleyDatum.pointsPresentation A).map
          (b2ChevalleyDatum.pointsPresentation B) f g) := by
  apply (b2ChevalleyDatumPointsEquiv B).injective
  rw [b2ChevalleyDatumPointsEquiv_map,
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_map, map_specialIsogeny]

/-- `b2ChevalleyDatumSpecialIsogeny` commutes with the `2 ^ k`-power Frobenius endomorphism of
`b2ChevalleyDatum`. -/
theorem b2ChevalleyDatumSpecialIsogeny_frobenius (k : ℕ) (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatum.frobenius 2 k A g) =
      b2ChevalleyDatum.frobenius 2 k A (b2ChevalleyDatumSpecialIsogeny A g) := by
  rw [DynkinType.ChevalleyDatum.frobenius_def, map_b2ChevalleyDatumSpecialIsogeny]

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` is the prime Frobenius of
`b2ChevalleyDatum`.** Marked `@[simp↓]` so nested applications reduce to `frobenius` before inner
`@[simp↓]` generator rules fire. -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny
    (g : b2ChevalleyDatum.points A) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatumSpecialIsogeny A g) =
      b2ChevalleyDatum.frobenius 2 1 A g := by
  apply (b2ChevalleyDatumPointsEquiv A).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    specialIsogeny_specialIsogeny, b2ChevalleyDatumPointsEquiv_frobenius]

/-- **The square of `b2ChevalleyDatumSpecialIsogeny` as a monoid homomorphism is the prime
Frobenius.** -/
@[simp]
theorem b2ChevalleyDatumSpecialIsogeny_comp_self :
    (b2ChevalleyDatumSpecialIsogeny A).comp (b2ChevalleyDatumSpecialIsogeny A) =
      b2ChevalleyDatum.frobenius 2 1 A :=
  MonoidHom.ext (b2ChevalleyDatumSpecialIsogeny_b2ChevalleyDatumSpecialIsogeny A)

/-! ## Action on simple root subgroups, Weyl elements, coroots, and torus points -/

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
  apply (b2ChevalleyDatumPointsEquiv A).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex i,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_simpleIndex (lengthPermRankTwo i)]
  have hpin (j : Fin 2) :
      specialIsogeny A
          (rootSubgroupPoints 1 (.inl (lengthPermRankTwo j)) A (Multiplicative.ofAdd t)) =
        rootSubgroupPoints 1 (.inl (lengthPermRankTwo (lengthPermRankTwo j))) A
          (Multiplicative.ofAdd
            (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo j)).toNat)) := by
    fin_cases j
    · simpa [DynkinType.rootLength_B] using specialIsogeny_rootSubgroupPoints_inl_last A t
    · simpa [DynkinType.rootLength_B] using specialIsogeny_rootSubgroupPoints_inl_zero A t
  exact hpin i

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
  apply (b2ChevalleyDatumPointsEquiv A).injective
  rw [b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex i,
    b2ChevalleyDatumPointsEquiv_rootSubgroupPoints_reflectionPerm_simpleIndex
      (lengthPermRankTwo i)]
  have hpin (j : Fin 2) :
      specialIsogeny A
          (rootSubgroupPoints 1 (.inr (lengthPermRankTwo j)) A (Multiplicative.ofAdd t)) =
        rootSubgroupPoints 1 (.inr (lengthPermRankTwo (lengthPermRankTwo j))) A
          (Multiplicative.ofAdd
            (t ^ ((DynkinType.B 2).rootLength (lengthPermRankTwo j)).toNat)) := by
    fin_cases j
    · simpa [DynkinType.rootLength_B] using specialIsogeny_rootSubgroupPoints_inr_last A t
    · simpa [DynkinType.rootLength_B] using specialIsogeny_rootSubgroupPoints_inr_zero A t
  exact hpin i

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
    (b2ChevalleyDatumSpecialIsogeny A) (j := lengthPermRankTwo i) 1
    (e := ((DynkinType.B 2).rootLength (lengthPermRankTwo i)).toNat)
    (by rw [CharTwo.neg_one_eq_one, one_pow])
    (fun u => by simp)
    (fun u => by simp) s

/-- **The character pullback of `b2ChevalleyDatumSpecialIsogeny` on the torus of `b2ChevalleyDatum`
is `DynkinType.b2SpecialIsogeny.weightMap`.** -/
theorem isCharacterMap_b2ChevalleyDatumSpecialIsogeny :
    IsCharacterMap (b2ChevalleyDatum.torusPoints A) (b2ChevalleyDatumSpecialIsogeny A)
      DynkinType.b2SpecialIsogeny.weightMap :=
  isCharacterMap_iff.mpr fun s => (b2ChevalleyDatumPointsEquiv A).injective <|
    (b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny A _).trans <|
      (congrArg (specialIsogeny A)
        (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A s)).trans <|
        ((isCharacterMap_specialIsogeny A).map_apply s).trans
          (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A
            (torusPointMap DynkinType.b2SpecialIsogeny.weightMap s)).symm

/-- **In Bourbaki `B₂` fundamental-weight coordinates, `b2ChevalleyDatumSpecialIsogeny` sends
`(s₀, s₁)` to `(s₁ ^ 2, s₀)`, i.e. `i ↦ s (lengthPermRankTwo i) ^ ((B 2).rootLength i).toNat`.** -/
@[simp↓]
theorem b2ChevalleyDatumSpecialIsogeny_torusPoints (s : Fin (DynkinType.B 2).rank → Aˣ) :
    b2ChevalleyDatumSpecialIsogeny A (b2ChevalleyDatum.torusPoints A s) =
      b2ChevalleyDatum.torusPoints A
        (fun i => s (lengthPermRankTwo i) ^ ((DynkinType.B 2).rootLength i).toNat) := by
  have hcoord (s' : Fin 2 → Aˣ) :
      specialIsogeny A (b2WeightTorusPoints A s') =
        b2WeightTorusPoints A
          (fun j => s' (lengthPermRankTwo j) ^ ((DynkinType.B 2).rootLength j).toNat) := by
    rw [specialIsogeny_b2WeightTorusPoints A s']
    congr 1
    funext j
    fin_cases j <;> simp [DynkinType.rootLength_B]
  exact (b2ChevalleyDatumPointsEquiv A).injective <|
    (b2ChevalleyDatumPointsEquiv_b2ChevalleyDatumSpecialIsogeny A _).trans <|
      (congrArg (specialIsogeny A)
        (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A s)).trans <|
        (hcoord s).trans
          (b2ChevalleyDatumPointsEquiv_torusPoints_eq_b2WeightTorusPoints A _).symm

end CharacteristicTwo

end

end TauCeti.SpStd
