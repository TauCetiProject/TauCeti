/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A

/-!
# The root datum of the special linear group relative to its diagonal torus

The diagonal torus of `SL_{r+1}` is the rank-`r` split torus embedded through the standard weights
`ε₀, …, ε_r`, written in fundamental-weight coordinates by
`TauCeti.SpecialLinear.diagonalTorusWeight`. Its character lattice is
`X*(T) = ULift (Fin r) →₀ ℤ` in the fundamental-weight basis, and its cocharacter lattice is
`X_*(T) = ULift (Fin r) → ℤ` in the dual basis, which is the basis of simple coroots. This file
equips these lattices with the root datum of type `A_r`, indexed by the ordered pairs `(a, b)` of
distinct matrix indices, that is, by the root subgroups `x_{ab}` of `SL_{r+1}`. The root indexed
by `(a, b)` is `ε_a - ε_b`, its coroot is `e_a - e_b`, and the pairing is the split-torus dot
pairing.

The datum is obtained by transporting the pinned simply connected datum
`TauCeti.DynkinType.typeASimplyConnectedRootDatum` with `RootPairing.map` along the universe lift
of both lattices, the roots being reindexed by `TauCeti.DynkinType.typeAIndexEquiv`. Consequently
its coroots span the cocharacter lattice: `SL_{r+1}` has the simply connected root datum of type
`A_r`. What ties the datum to the group is
`TauCeti.SpecialLinear.charOfPoint_ofAdd_diagonalRootDatum_root`: the root indexed by `(a, b)` is
exactly the character through which the diagonal torus rescales the root subgroup `x_{ab}`.

## Main definitions

* `TauCeti.SpecialLinear.diagonalRootDatum`: the type `A_r` root datum on the lattices of the
  diagonal torus of `SL_{r+1}`.
* `TauCeti.SpecialLinear.diagonalRootDatumEquiv`: the identification with the pinned simply
  connected type-`A_r` datum, allowing its base to be transported to these lattices.

## Main results

* `TauCeti.SpecialLinear.diagonalRootDatum_toLinearMap`: its pairing is the split-torus dot
  pairing.
* `TauCeti.SpecialLinear.diagonalRootDatum_root_apply` and
  `TauCeti.SpecialLinear.diagonalRootDatum_coroot_apply`: the roots `ε_a - ε_b` and coroots
  `e_a - e_b` in coordinates.
* `TauCeti.SpecialLinear.diagonalRootDatum_pairing_apply`: the Cartan integers.
* `TauCeti.SpecialLinear.diagonalRootDatum_reflectionPerm`: reflections act on root indices by
  transposing matrix indices.
* `TauCeti.SpecialLinear.diagonalRootDatum_coroot_castSucc_succ`: the simple coroots are the
  standard basis, and `TauCeti.SpecialLinear.corootSpan_diagonalRootDatum_eq_top`: the coroots
  span the cocharacter lattice.
* `TauCeti.SpecialLinear.charOfPoint_ofAdd_diagonalRootDatum_root`: the roots are the characters
  of the diagonal torus on the root subgroups.
* `TauCeti.SpecialLinear.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv_eq_root`: the pinning
  equation, with the scaling character given by `diagonalRootDatum`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21 and Example 21.2.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3 and §27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* The construction follows `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.RootDatum`.
-/

public section

open WithConv

namespace TauCeti.SpecialLinear

open DynkinType

universe u w

variable {r : ℕ}

/-- The universe lift carries the pinned type `A_r` character lattice to the character lattice of
the diagonal torus. -/
private noncomputable def characterEquiv (r : ℕ) : (Fin r → ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin r) →₀ ℤ) :=
  (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift).trans (Finsupp.linearEquivFunOnFinite ℤ ℤ _).symm

/-- The universe lift carries the pinned type `A_r` cocharacter lattice to the cocharacter lattice
of the diagonal torus. -/
private noncomputable def cocharacterEquiv (r : ℕ) : (Fin r → ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin r) → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift

private lemma characterEquiv_apply (x : Fin r → ℤ) (i : ULift.{u} (Fin r)) :
    characterEquiv.{u} r x i = x i.down :=
  (rfl)

private lemma cocharacterEquiv_apply (y : Fin r → ℤ) (i : ULift.{u} (Fin r)) :
    cocharacterEquiv.{u} r y i = y i.down :=
  (rfl)

private lemma dotPairing_characterEquiv_cocharacterEquiv (x y : Fin r → ℤ) :
    SplitTorus.dotPairing (characterEquiv.{u} r x) (cocharacterEquiv.{u} r y) = x ⬝ᵥ y := by
  rw [SplitTorus.dotPairing_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _, dotProduct]
  exact Fintype.sum_equiv Equiv.ulift _ _ fun _ => by
    rw [characterEquiv_apply, cocharacterEquiv_apply, Equiv.ulift_apply]

/-- **The root datum of `SL_{r+1}` relative to its diagonal torus.** It is the pinned simply
connected datum of type `A_r`, written on the character and cocharacter lattices of the diagonal
torus and indexed by the ordered pairs of distinct matrix indices. -/
noncomputable def diagonalRootDatum (r : ℕ) :
    RootDatum (SplitTorus.CoordinateRootIndex (Fin (r + 1))) (ULift.{u} (Fin r) →₀ ℤ)
      (ULift.{u} (Fin r) → ℤ) :=
  (typeASimplyConnectedRootDatum r).map (typeAIndexEquiv r).symm (characterEquiv r)
    (cocharacterEquiv r)

/-- The identification of the pinned simply connected type-`A` datum with the root datum
on the diagonal torus lattices of `SL_{r+1}`. -/
noncomputable def diagonalRootDatumEquiv (r : ℕ) :
    (typeASimplyConnectedRootDatum r).Equiv (diagonalRootDatum.{u} r) where
  weightMap := (characterEquiv r).toLinearMap
  coweightMap := (cocharacterEquiv r).symm.toLinearMap
  indexEquiv := (typeAIndexEquiv r).symm
  weight_coweight_transpose := by
    ext y x
    simp [diagonalRootDatum, RootPairing.map]
  root_weightMap := by
    ext i
    simp [diagonalRootDatum, RootPairing.map]
  coroot_coweightMap := by
    ext i
    simp [diagonalRootDatum, RootPairing.map]
  bijective_weightMap := (characterEquiv r).bijective
  bijective_coweightMap := (cocharacterEquiv r).symm.bijective

/-- The root indices are transported by the ordered-pair enumeration. -/
@[simp] theorem diagonalRootDatumEquiv_indexEquiv (r : ℕ) :
    (diagonalRootDatumEquiv.{u} r).indexEquiv = (typeAIndexEquiv r).symm := (rfl)

/-- The weight map writes a weight in the universe-lifted fundamental-weight coordinates. -/
@[simp] theorem diagonalRootDatumEquiv_weightMap_apply (x : Fin r → ℤ)
    (i : ULift.{u} (Fin r)) :
    (diagonalRootDatumEquiv.{u} r).weightMap x i = x i.down := (rfl)

/-- The contravariant coweight map removes the universe lift on simple-coroot coordinates. -/
@[simp] theorem diagonalRootDatumEquiv_coweightMap_apply (y : ULift.{u} (Fin r) → ℤ)
    (i : Fin r) :
    (diagonalRootDatumEquiv.{u} r).coweightMap y i = y (ULift.up i) := (rfl)

private lemma diagonalRootDatum_root_eq (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).root p =
      characterEquiv.{u} r ((typeASimplyConnectedRootDatum r).root (typeAIndexEquiv r p)) := by
  simp [diagonalRootDatum, RootPairing.map]

private lemma diagonalRootDatum_coroot_eq (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).coroot p =
      cocharacterEquiv.{u} r ((typeASimplyConnectedRootDatum r).coroot (typeAIndexEquiv r p)) := by
  simp [diagonalRootDatum, RootPairing.map]

/-- The pairing of `diagonalRootDatum` is the split-torus dot pairing. -/
@[simp]
theorem diagonalRootDatum_toLinearMap (r : ℕ) :
    (diagonalRootDatum.{u} r).toLinearMap = SplitTorus.dotPairing := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (characterEquiv.{u} r).surjective x
  obtain ⟨y, rfl⟩ := (cocharacterEquiv.{u} r).surjective y
  rw [dotPairing_characterEquiv_cocharacterEquiv]
  simp [diagonalRootDatum, RootPairing.map]

/-- **The roots are the differences of standard weights.** The root indexed by `(a, b)` is
`ε_a - ε_b`, written in fundamental-weight coordinates. -/
@[simp]
theorem diagonalRootDatum_root_apply (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (i : ULift.{u} (Fin r)) :
    (diagonalRootDatum.{u} r).root p i =
      diagonalTorusWeight r p.1.1 i - diagonalTorusWeight r p.1.2 i := by
  simp [diagonalRootDatum_root_eq, characterEquiv_apply, diagonalTorusWeight_apply,
    SlStd.weight_def]

/-- **The coroots in simple-coroot coordinates.** The coroot indexed by `(a, b)` is `e_a - e_b`,
whose `i`-th simple-coroot coordinate is `[a ≤ i] - [b ≤ i]`. -/
@[simp]
theorem diagonalRootDatum_coroot_apply (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (i : ULift.{u} (Fin r)) :
    (diagonalRootDatum.{u} r).coroot p i =
      (if p.1.1 ≤ i.down.castSucc then 1 else 0) - (if p.1.2 ≤ i.down.castSucc then 1 else 0) := by
  rw [diagonalRootDatum_coroot_eq, cocharacterEquiv_apply, coroot_typeAIndexEquiv]

/-- The pairing of `diagonalRootDatum` is the pinned type `A_r` pairing, read on ordered pairs. -/
private lemma diagonalRootDatum_pairing_eq (p q : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).pairing p q =
      (typeASimplyConnectedRootDatum r).pairing (typeAIndexEquiv r p) (typeAIndexEquiv r q) := by
  simp only [← RootPairing.root_coroot_eq_pairing, diagonalRootDatum_toLinearMap,
    diagonalRootDatum_root_eq, diagonalRootDatum_coroot_eq,
    dotPairing_characterEquiv_cocharacterEquiv, toLinearMap_typeASimplyConnectedRootDatum]

/-- **The Cartan integers.** The pairing of the root `ε_a - ε_b` with the coroot `e_c - e_d` is
`[a = c] - [a = d] - ([b = c] - [b = d])`. -/
@[simp]
theorem diagonalRootDatum_pairing_apply (p q : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).pairing p q =
      (if p.1.1 = q.1.1 then 1 else 0) - (if p.1.1 = q.1.2 then 1 else 0) -
        ((if p.1.2 = q.1.1 then 1 else 0) - (if p.1.2 = q.1.2 then 1 else 0)) := by
  rw [diagonalRootDatum_pairing_eq, pairing_typeAIndexEquiv]

/-- The root--coroot pairing of the diagonal root datum is symmetric. -/
theorem diagonalRootDatum_pairing_comm (p q : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).pairing p q = (diagonalRootDatum.{u} r).pairing q p := by
  rw [diagonalRootDatum_pairing_eq, diagonalRootDatum_pairing_eq,
    pairing_typeASimplyConnectedRootDatum_comm]

/-- The root datum of the diagonal torus of `SL_{r+1}` is reduced. -/
instance isReduced_diagonalRootDatum (r : ℕ) : (diagonalRootDatum.{u} r).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ diagonalRootDatum_pairing_comm

/-- **Reflections transpose matrix indices.** The reflection in the root indexed by `(a, b)` sends
the root indexed by `(c, d)` to the one indexed by `(s c, s d)`, where `s` is the transposition of
`a` and `b`. -/
@[simp]
theorem diagonalRootDatum_reflectionPerm (p q : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootDatum.{u} r).reflectionPerm p q =
      SplitTorus.coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q := by
  apply Subtype.ext
  rw [SplitTorus.coordinatePermRootIndex_coe, ← typeAIndexEquiv_symm_reflectionPerm]
  simp [diagonalRootDatum, RootPairing.map]

/-- **The simple coroots are the standard basis.** The coroot of the simple root
`ε_i - ε_{i+1}` is the `i`-th basis vector of the cocharacter lattice. -/
theorem diagonalRootDatum_coroot_castSucc_succ (i : Fin r) :
    (diagonalRootDatum.{u} r).coroot ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ.ne⟩ =
      Pi.single (ULift.up i) 1 := by
  funext k
  simp only [diagonalRootDatum_coroot_apply, Pi.single_apply, ULift.ext_iff, Fin.ext_iff,
    Fin.le_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- **The root datum of `SL_{r+1}` is simply connected**: its coroots span the cocharacter lattice
of the diagonal torus. -/
theorem corootSpan_diagonalRootDatum_eq_top (r : ℕ) :
    (diagonalRootDatum.{u} r).corootSpan ℤ = ⊤ := by
  classical
  exact corootSpan_eq_top_of_coroot_eq_single (e := fun i : ULift.{u} (Fin r) =>
      (⟨(i.down.castSucc, i.down.succ), Fin.castSucc_lt_succ.ne⟩ :
        SplitTorus.CoordinateRootIndex (Fin (r + 1))))
    fun i => diagonalRootDatum_coroot_castSucc_succ i.down

/-! ### The roots as characters of the diagonal torus -/

section Points

variable {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]

/-- **The roots are characters of the diagonal torus.** Evaluated at a point of the split torus,
the root `ε_a - ε_b` of `diagonalRootDatum` is the quotient of the values of the standard weights
`ε_a` and `ε_b`. -/
theorem charOfPoint_ofAdd_diagonalRootDatum_root
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] A)) :
    DiagonalizableGroup.charOfPoint t.ofConv
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight r p.1.1) /
        torusCharacter (SplitTorus.pointsMulEquiv t) (diagonalTorusWeight r p.1.2) := by
  have hw : Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) =
      SplitTorus.weightCharacter (diagonalTorusWeight r p.1.1 - diagonalTorusWeight r p.1.2) := by
    apply Multiplicative.toAdd.injective
    ext i
    rw [SplitTorus.toAdd_weightCharacter, toAdd_ofAdd, diagonalRootDatum_root_apply, Pi.sub_apply]
  rw [hw, SplitTorus.charOfPoint_weightCharacter, torusCharacter_sub]

/-- **The pinning equation of `SL_{r+1}`, with the roots of `diagonalRootDatum`.** Conjugation by a
point of the diagonal torus scales the parameter of the root subgroup `x_{ab}` by the value of the
root indexed by `(a, b)`. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv_eq_root
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints r R A t * rootSubgroupPoints p.2 c * (diagonalTorusPoints r R A t)⁻¹ =
      rootSubgroupPoints p.2
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            (((DiagonalizableGroup.charOfPoint t.ofConv
                (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) : Aˣ) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  apply (pointsMulEquiv (R := R) (A := A) (r + 1)).injective
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [map_mul, map_inv]
  -- `simp` does not fire these point-map lemmas here, while `rw` matches them up to instances.
  rw [toGL_pointsMulEquiv_diagonalTorusPoints, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints]
  simp [toGL_transvection_eq_transvectionUnit, diagGL_mul_transvectionUnit_mul_inv,
    charOfPoint_ofAdd_diagonalRootDatum_root, div_eq_mul_inv, mul_right_comm]

end Points

end TauCeti.SpecialLinear
