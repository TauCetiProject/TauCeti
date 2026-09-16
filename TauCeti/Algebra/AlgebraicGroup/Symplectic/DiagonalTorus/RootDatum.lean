/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Classical
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced

/-!
# The root datum of the symplectic group relative to its diagonal torus

The paired diagonal torus `diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)` of `Sp₂ₘ` has character lattice
`X*(T) = ULift (Fin m) →₀ ℤ` and cocharacter lattice `X_*(T) = ULift (Fin m) → ℤ`. This file
equips these lattices with the root datum of type `Cₘ`, indexed by the standard symplectic root
subgroups themselves. Writing `eᵢ` for the coordinate vectors, its roots are

```text
2eᵢ,  -2eᵢ,  eᵢ - eⱼ,  eᵢ + eⱼ,  -eᵢ - eⱼ,
```

with coroots `eᵢ`, `-eᵢ` on the long roots and the same vectors as the roots on the short ones,
and its pairing is the split-torus dot pairing.

The datum is obtained by transporting the pinned simply connected datum
`TauCeti.DynkinType.typeCSimplyConnectedRootDatum` with `RootPairing.map` along the classical
coordinates `TauCeti.DynkinType.TypeC.classicalWeightEquiv` and
`TauCeti.DynkinType.TypeC.classicalCoweightEquiv`. What ties it to the group is
`TauCeti.Symplectic.charOfPoint_ofAdd_diagonalRootDatum_root`: the root indexed by a root subgroup
is exactly the character through which the diagonal torus rescales that subgroup. Consequently
the conjugation formula for the diagonal torus on root subgroups takes the form of the pinning
equation, with the roots of the datum as exponents.

## Main definitions

* `TauCeti.GLSymplecticFin.RootSubgroupIndex.equivTypeCIndex`: the symplectic root subgroups are
  indexed by the type `C` root indices.
* `TauCeti.Symplectic.diagonalRootDatum`: the type `Cₘ` root datum on the lattices of the diagonal
  torus.

## Main results

* `TauCeti.Symplectic.diagonalRootDatum_toLinearMap`: its pairing is the split-torus dot pairing.
* `TauCeti.Symplectic.diagonalRootDatum_root_positiveLong` and its companions: the roots in
  coordinates.
* `TauCeti.Symplectic.diagonalRootDatum_coroot_positiveLong` and its companions: the coroots in
  coordinates.
* `TauCeti.Symplectic.charOfPoint_ofAdd_diagonalRootDatum_root`: the roots are the characters of
  the diagonal torus on the root subgroups.
* `TauCeti.Symplectic.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv_eq_root`: the pinning
  equation with the roots of the datum as exponents.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21 and Example 21.2 (the symplectic groups).
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3 and §27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
-/

public section

open WithConv

namespace TauCeti

open DynkinType

namespace GLSymplecticFin.RootSubgroupIndex

variable {m : ℕ}

/-- The type `C` root index `(a, b, s)` of a symplectic root subgroup. The root indexed by
`(a, b, s)` is `(-1) ^ s * (e_a + e_b)` when `b ≤ a` and `(-1) ^ s * (e_a - e_b)` when `a < b`. -/
private def toTypeCIndex : RootSubgroupIndex m → TypeCIndex m
  | .positiveLong i => (i, i, false)
  | .negativeLong i => (i, i, true)
  | .difference i j _ => if i < j then (i, j, false) else (j, i, true)
  | .positiveSum i j _ => (j, i, false)
  | .negativeSum i j _ => (j, i, true)

/-- The symplectic root subgroup belonging to a type `C` root index. -/
private def ofTypeCIndex (x : TypeCIndex m) : RootSubgroupIndex m :=
  if h : x.1 < x.2.1 then
    if x.2.2 then .difference x.2.1 x.1 h.ne' else .difference x.1 x.2.1 h.ne
  else if h' : x.2.1 < x.1 then
    if x.2.2 then .negativeSum x.2.1 x.1 h' else .positiveSum x.2.1 x.1 h'
  else if x.2.2 then .negativeLong x.1 else .positiveLong x.1

private lemma ofTypeCIndex_toTypeCIndex (r : RootSubgroupIndex m) :
    ofTypeCIndex (toTypeCIndex r) = r := by
  cases r with
  | positiveLong i => simp [toTypeCIndex, ofTypeCIndex]
  | negativeLong i => simp [toTypeCIndex, ofTypeCIndex]
  | difference i j hij =>
      rcases lt_or_gt_of_ne hij with h | h
      · simp [toTypeCIndex, ofTypeCIndex, h]
      · simp [toTypeCIndex, ofTypeCIndex, h, not_lt_of_gt h]
  | positiveSum i j h => simp [toTypeCIndex, ofTypeCIndex, h, not_lt_of_gt h]
  | negativeSum i j h => simp [toTypeCIndex, ofTypeCIndex, h, not_lt_of_gt h]

private lemma toTypeCIndex_ofTypeCIndex (x : TypeCIndex m) :
    toTypeCIndex (ofTypeCIndex x) = x := by
  obtain ⟨a, b, s⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases s <;> simp [toTypeCIndex, ofTypeCIndex, h, not_lt_of_gt h]
  · cases s <;> simp [toTypeCIndex, ofTypeCIndex]
  · cases s <;> simp [toTypeCIndex, ofTypeCIndex, h, not_lt_of_gt h]

/-- **The symplectic root subgroups are indexed by the type `C` root indices.** A root subgroup
with root `(-1) ^ s * (e_a ± e_b)` is sent to `(a, b, s)`, in the normalization of
`TauCeti.DynkinType.TypeCIndex`. -/
def equivTypeCIndex (m : ℕ) : RootSubgroupIndex m ≃ TypeCIndex m where
  toFun := toTypeCIndex
  invFun := ofTypeCIndex
  left_inv := ofTypeCIndex_toTypeCIndex
  right_inv := toTypeCIndex_ofTypeCIndex

/-- The long root `2eᵢ` has type `C` index `(i, i, false)`. -/
@[simp]
theorem equivTypeCIndex_positiveLong (i : Fin m) :
    equivTypeCIndex m (.positiveLong i) = (i, i, false) :=
  (rfl)

/-- The long root `-2eᵢ` has type `C` index `(i, i, true)`. -/
@[simp]
theorem equivTypeCIndex_negativeLong (i : Fin m) :
    equivTypeCIndex m (.negativeLong i) = (i, i, true) :=
  (rfl)

/-- For `i < j`, the short root `eᵢ - eⱼ` has type `C` index `(i, j, false)`. -/
@[simp]
theorem equivTypeCIndex_difference_of_lt {i j : Fin m} (h : i < j) :
    equivTypeCIndex m (.difference i j h.ne) = (i, j, false) := by
  simp only [equivTypeCIndex, Equiv.coe_fn_mk, toTypeCIndex, h, ↓reduceIte]

/-- For `j < i`, the short root `eᵢ - eⱼ = -(eⱼ - eᵢ)` has type `C` index `(j, i, true)`. -/
@[simp]
theorem equivTypeCIndex_difference_of_gt {i j : Fin m} (h : j < i) :
    equivTypeCIndex m (.difference i j h.ne') = (j, i, true) := by
  simp only [equivTypeCIndex, Equiv.coe_fn_mk, toTypeCIndex, not_lt_of_gt h, ↓reduceIte]

/-- For `i < j`, the short root `eᵢ + eⱼ` has type `C` index `(j, i, false)`. -/
@[simp]
theorem equivTypeCIndex_positiveSum {i j : Fin m} (h : i < j) :
    equivTypeCIndex m (.positiveSum i j h) = (j, i, false) :=
  (rfl)

/-- For `i < j`, the short root `-eᵢ - eⱼ` has type `C` index `(j, i, true)`. -/
@[simp]
theorem equivTypeCIndex_negativeSum {i j : Fin m} (h : i < j) :
    equivTypeCIndex m (.negativeSum i j h) = (j, i, true) :=
  (rfl)

end GLSymplecticFin.RootSubgroupIndex

namespace Symplectic

open GLSymplecticFin

universe u v

variable {m : ℕ}

/-- Classical coordinates carry the pinned type `Cₘ` character lattice to the character lattice
of the diagonal torus. -/
private noncomputable def characterEquiv (m : ℕ) :
    (Fin m → ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin m) →₀ ℤ) :=
  (TypeC.classicalWeightEquiv m).trans
    ((LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift).trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm)

/-- Classical coordinates carry the pinned type `Cₘ` cocharacter lattice to the cocharacter
lattice of the diagonal torus. -/
private noncomputable def cocharacterEquiv (m : ℕ) :
    (Fin m → ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin m) → ℤ) :=
  (TypeC.classicalCoweightEquiv m).trans (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift)

private lemma characterEquiv_weight (a : Fin m) :
    characterEquiv.{u} m (TypeC.weight m a) = Finsupp.single (ULift.up a) 1 := by
  ext b
  simp [characterEquiv, Finsupp.single_apply, Pi.single_apply, ULift.ext_iff, eq_comm]

private lemma cocharacterEquiv_coweight (a : Fin m) :
    cocharacterEquiv.{u} m (TypeC.coweight m a) = Pi.single (ULift.up a) 1 := by
  ext b
  simp [cocharacterEquiv, Pi.single_apply, ULift.ext_iff]

private lemma characterEquiv_signedWeight (x : TypeC.Signed m) :
    characterEquiv.{u} m (TypeC.signedWeight x) =
      (if x.2 then -1 else 1) • Finsupp.single (ULift.up x.1) 1 := by
  obtain ⟨a, s⟩ := x
  cases s <;> simp [characterEquiv_weight]

private lemma cocharacterEquiv_signedCoweight (x : TypeC.Signed m) :
    cocharacterEquiv.{u} m (TypeC.signedCoweight x) =
      (if x.2 then -1 else 1) • Pi.single (ULift.up x.1) 1 := by
  obtain ⟨a, s⟩ := x
  cases s <;> simp [cocharacterEquiv_coweight]

private lemma dotPairing_characterEquiv_cocharacterEquiv (x y : Fin m → ℤ) :
    SplitTorus.dotPairing (characterEquiv.{u} m x) (cocharacterEquiv.{u} m y) = x ⬝ᵥ y := by
  rw [← TypeC.classicalWeightEquiv_dotProduct_classicalCoweightEquiv, SplitTorus.dotPairing_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _, dotProduct]
  exact Fintype.sum_equiv Equiv.ulift _ _ fun _ => by simp [characterEquiv, cocharacterEquiv]

/-- **The root datum of `Sp₂ₘ` relative to its diagonal torus.** It is the pinned simply connected
datum of type `Cₘ`, written on the character and cocharacter lattices of the diagonal torus and
indexed by the standard symplectic root subgroups. -/
noncomputable def diagonalRootDatum (m : ℕ) :
    RootDatum (RootSubgroupIndex m) (ULift.{u} (Fin m) →₀ ℤ) (ULift.{u} (Fin m) → ℤ) :=
  (typeCSimplyConnectedRootDatum m).map
    ((RootSubgroupIndex.equivTypeCIndex m).trans (typeCIndexEquiv m)).symm
    (characterEquiv m) (cocharacterEquiv m)

/-- The root datum of the symplectic diagonal torus is reduced. -/
instance instIsReducedDiagonalRootDatum (m : ℕ) : (diagonalRootDatum.{u} m).IsReduced := by
  let P := typeCSimplyConnectedRootDatum m
  let e := ((RootSubgroupIndex.equivTypeCIndex m).trans (typeCIndexEquiv m)).symm
  let f := characterEquiv.{u} m
  constructor
  intro i j h
  have h' : ¬ LinearIndependent ℤ ![P.root (e.symm i), P.root (e.symm j)] := by
    intro hli
    apply h
    change LinearIndependent ℤ ![f (P.root (e.symm i)), f (P.root (e.symm j))]
    have hm := hli.map' f.toLinearMap f.ker
    have hfun : f.toLinearMap ∘ ![P.root (e.symm i), P.root (e.symm j)] =
        ![f (P.root (e.symm i)), f (P.root (e.symm j))] := by
      funext k
      fin_cases k <;> rfl
    rw [hfun] at hm
    exact hm
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) (e.symm i) (e.symm j) h' with hij | hij
  · left
    simpa [diagonalRootDatum, P, e, f, RootPairing.map] using congrArg f hij
  · right
    simpa [diagonalRootDatum, P, e, f, RootPairing.map] using congrArg f hij

/-- The root of `diagonalRootDatum` indexed by a root subgroup is the classical form of the pinned
type `Cₘ` root with the corresponding index. -/
private lemma diagonalRootDatum_root (r : RootSubgroupIndex m) :
    (diagonalRootDatum.{u} m).root r =
      characterEquiv.{u} m ((typeCSimplyConnectedRootDatum m).root
        (typeCIndexEquiv m (RootSubgroupIndex.equivTypeCIndex m r))) := by
  simp [diagonalRootDatum, RootPairing.map]

/-- The coroot of `diagonalRootDatum` indexed by a root subgroup is the classical form of the
pinned type `Cₘ` coroot with the corresponding index. -/
private lemma diagonalRootDatum_coroot (r : RootSubgroupIndex m) :
    (diagonalRootDatum.{u} m).coroot r =
      cocharacterEquiv.{u} m ((typeCSimplyConnectedRootDatum m).coroot
        (typeCIndexEquiv m (RootSubgroupIndex.equivTypeCIndex m r))) := by
  simp [diagonalRootDatum, RootPairing.map]

/-- The pairing of `diagonalRootDatum` is the split-torus dot pairing. -/
@[simp]
theorem diagonalRootDatum_toLinearMap (m : ℕ) :
    (diagonalRootDatum.{u} m).toLinearMap = SplitTorus.dotPairing := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (characterEquiv.{u} m).surjective x
  obtain ⟨y, rfl⟩ := (cocharacterEquiv.{u} m).surjective y
  rw [dotPairing_characterEquiv_cocharacterEquiv]
  simp [diagonalRootDatum, RootPairing.map]

/-! ### The roots in coordinates -/

/-- The root of the positive long root subgroup is `2eᵢ`. -/
@[simp]
theorem diagonalRootDatum_root_positiveLong (i : Fin m) :
    (diagonalRootDatum.{u} m).root (.positiveLong i) = Finsupp.single (ULift.up i) 2 := by
  rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_positiveLong,
    root_typeCIndexEquiv_of_not_lt (lt_irrefl i), map_add, characterEquiv_signedWeight]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
  rw [← Finsupp.single_add, one_add_one_eq_two]

/-- The root of the negative long root subgroup is `-2eᵢ`. -/
@[simp]
theorem diagonalRootDatum_root_negativeLong (i : Fin m) :
    (diagonalRootDatum.{u} m).root (.negativeLong i) = -Finsupp.single (ULift.up i) 2 := by
  rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_negativeLong,
    root_typeCIndexEquiv_of_not_lt (lt_irrefl i), map_add, characterEquiv_signedWeight]
  simp only [↓reduceIte, neg_smul, one_smul]
  rw [← neg_add, ← Finsupp.single_add, one_add_one_eq_two]

/-- The root of the difference root subgroup is `eᵢ - eⱼ`. -/
@[simp]
theorem diagonalRootDatum_root_difference {i j : Fin m} (hij : i ≠ j) :
    (diagonalRootDatum.{u} m).root (.difference i j hij) =
      Finsupp.single (ULift.up i) 1 - Finsupp.single (ULift.up j) 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_difference_of_lt h,
      root_typeCIndexEquiv_of_lt h, map_sub, characterEquiv_signedWeight,
      characterEquiv_signedWeight]
    simp
  · rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_difference_of_gt h,
      root_typeCIndexEquiv_of_lt h, map_sub, characterEquiv_signedWeight,
      characterEquiv_signedWeight]
    simp only [↓reduceIte, neg_smul, one_smul, sub_neg_eq_add]
    abel

/-- The root of the positive sum root subgroup is `eᵢ + eⱼ`. -/
@[simp]
theorem diagonalRootDatum_root_positiveSum {i j : Fin m} (hij : i < j) :
    (diagonalRootDatum.{u} m).root (.positiveSum i j hij) =
      Finsupp.single (ULift.up i) 1 + Finsupp.single (ULift.up j) 1 := by
  rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_positiveSum,
    root_typeCIndexEquiv_of_not_lt (not_lt_of_gt hij), map_add, characterEquiv_signedWeight,
    characterEquiv_signedWeight]
  simp [add_comm]

/-- The root of the negative sum root subgroup is `-(eᵢ + eⱼ)`. -/
@[simp]
theorem diagonalRootDatum_root_negativeSum {i j : Fin m} (hij : i < j) :
    (diagonalRootDatum.{u} m).root (.negativeSum i j hij) =
      -(Finsupp.single (ULift.up i) 1 + Finsupp.single (ULift.up j) 1) := by
  rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_negativeSum,
    root_typeCIndexEquiv_of_not_lt (not_lt_of_gt hij), map_add, characterEquiv_signedWeight,
    characterEquiv_signedWeight]
  simp only [↓reduceIte, neg_smul, one_smul, neg_add_rev]

/-! ### The coroots in coordinates -/

/-- The coroot of the long root `2eᵢ` is the halved cocharacter `eᵢ`. -/
@[simp]
theorem diagonalRootDatum_coroot_positiveLong (i : Fin m) :
    (diagonalRootDatum.{u} m).coroot (.positiveLong i) = Pi.single (ULift.up i) 1 := by
  rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_positiveLong,
    coroot_typeCIndexEquiv_diag, cocharacterEquiv_signedCoweight]
  simp

/-- The coroot of the long root `-2eᵢ` is `-eᵢ`. -/
@[simp]
theorem diagonalRootDatum_coroot_negativeLong (i : Fin m) :
    (diagonalRootDatum.{u} m).coroot (.negativeLong i) = -Pi.single (ULift.up i) 1 := by
  rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_negativeLong,
    coroot_typeCIndexEquiv_diag, cocharacterEquiv_signedCoweight]
  simp

/-- The coroot of the short root `eᵢ - eⱼ` is the cocharacter `eᵢ - eⱼ`. -/
@[simp]
theorem diagonalRootDatum_coroot_difference {i j : Fin m} (hij : i ≠ j) :
    (diagonalRootDatum.{u} m).coroot (.difference i j hij) =
      Pi.single (ULift.up i) 1 - Pi.single (ULift.up j) 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_difference_of_lt h,
      coroot_typeCIndexEquiv_of_lt h, map_sub, cocharacterEquiv_signedCoweight,
      cocharacterEquiv_signedCoweight]
    simp
  · rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_difference_of_gt h,
      coroot_typeCIndexEquiv_of_lt h, map_sub, cocharacterEquiv_signedCoweight,
      cocharacterEquiv_signedCoweight]
    simp only [↓reduceIte, neg_smul, one_smul, sub_neg_eq_add]
    abel

/-- The coroot of the short root `eᵢ + eⱼ` is the cocharacter `eᵢ + eⱼ`. -/
@[simp]
theorem diagonalRootDatum_coroot_positiveSum {i j : Fin m} (hij : i < j) :
    (diagonalRootDatum.{u} m).coroot (.positiveSum i j hij) =
      Pi.single (ULift.up i) 1 + Pi.single (ULift.up j) 1 := by
  rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_positiveSum,
    coroot_typeCIndexEquiv_of_gt hij, map_add, cocharacterEquiv_signedCoweight,
    cocharacterEquiv_signedCoweight]
  simp [add_comm]

/-- The coroot of the short root `-(eᵢ + eⱼ)` is the cocharacter `-(eᵢ + eⱼ)`. -/
@[simp]
theorem diagonalRootDatum_coroot_negativeSum {i j : Fin m} (hij : i < j) :
    (diagonalRootDatum.{u} m).coroot (.negativeSum i j hij) =
      -(Pi.single (ULift.up i) 1 + Pi.single (ULift.up j) 1) := by
  rw [diagonalRootDatum_coroot, RootSubgroupIndex.equivTypeCIndex_negativeSum,
    coroot_typeCIndexEquiv_of_gt hij, map_add, cocharacterEquiv_signedCoweight,
    cocharacterEquiv_signedCoweight]
  simp only [↓reduceIte, neg_smul, one_smul, neg_add_rev]

/-! ### The roots as characters of the diagonal torus -/

section Points

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- **The roots are the characters of the diagonal torus on the root subgroups.** Evaluated at a
point of the diagonal torus, the root of `diagonalRootDatum` indexed by a root subgroup is the
character by which conjugation by that point rescales the subgroup. -/
theorem charOfPoint_ofAdd_diagonalRootDatum_root (r : RootSubgroupIndex m)
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint t.ofConv
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root r)) =
      r.character (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) := by
  have hw (x : ULift.{u} (Fin m) →₀ ℤ) :
      Multiplicative.ofAdd x = SplitTorus.weightCharacter ⇑x := by
    apply Multiplicative.toAdd.injective
    ext j
    rw [SplitTorus.toAdd_weightCharacter, toAdd_ofAdd]
  classical
  rw [hw, SplitTorus.charOfPoint_weightCharacter]
  cases r with
  | positiveLong i => simp [Finsupp.single_eq_pi_single, sq]
  | negativeLong i =>
      simp [Finsupp.single_eq_pi_single, torusCharacter_neg, sq]
  | difference i j hij =>
      simp [Finsupp.single_eq_pi_single, torusCharacter_sub, div_eq_mul_inv]
  | positiveSum i j hij => simp [Finsupp.single_eq_pi_single, torusCharacter_add]
  | negativeSum i j hij =>
      simp [Finsupp.single_eq_pi_single, torusCharacter_neg, torusCharacter_add]

/-- **The pinning equation for `Sp₂ₘ` in root-datum form.** Conjugation by a point of the diagonal
torus scales the parameter of each root subgroup by the value of the corresponding root of
`diagonalRootDatum`. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv_eq_root (r : RootSubgroupIndex m)
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints t * rootSubgroupPoints r c * (diagonalTorusPoints t)⁻¹ =
      rootSubgroupPoints r
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            ((DiagonalizableGroup.charOfPoint t.ofConv
                (Multiplicative.ofAdd ((diagonalRootDatum.{u} m).root r)) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  rw [charOfPoint_ofAdd_diagonalRootDatum_root]
  exact diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv r t c

end Points

end Symplectic

end TauCeti
