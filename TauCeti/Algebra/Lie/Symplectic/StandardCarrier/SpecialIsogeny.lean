/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny

/-!
# The special isogeny of the rank-two type-`C` carrier

The rank-two member of the explicit full-weight type-`C` Chevalley carrier is the ambient group
of the two classification-list families on the `B₂` diagram, the untwisted `B₂(q)` and the Suzuki
family `²B₂(2^(2m+1))`. Over a commutative ring of characteristic two its points carry the special
isogeny, the endomorphism exchanging the two root lengths whose odd powers cut out the Suzuki
groups. This file transports that endomorphism from the symplectic group to the carrier.

The transport is possible because the two point groups coincide:
`TauCeti.SpStd.points_eq_GLSymplecticFin_of_commRing` identifies the carrier's points with the
symplectic matrices over every commutative ring, so the special isogeny of `Sp₄` restricts to an
endomorphism of the carrier rather than merely mapping it into a larger group. The four pinning
equations, naturality in the value ring, and the square relation below are the symplectic-group
statements read through `TauCeti.SpStd.pointsMulEquivGLSymplecticFinOfCommRing`.

## Main definitions

* `TauCeti.SpStd.specialIsogeny`: the special isogeny of the carrier over any commutative ring of
  characteristic two.

## Main results

* `TauCeti.SpStd.pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny`,
  `TauCeti.SpStd.pointsMulEquivGLSymplecticFinOfCommRing_symm_specialIsogeny`, and
  `TauCeti.SpStd.pointsMulEquivGLSymplecticFin_specialIsogeny`: intertwining with
  `TauCeti.specialIsogeny`.
* `TauCeti.SpStd.map_specialIsogeny` and `TauCeti.SpStd.specialIsogeny_frobenius`: naturality
  along homomorphisms of characteristic-two commutative rings and commutation with Frobenius.
* `TauCeti.SpStd.specialIsogeny_rootSubgroupPoints_inl_zero` and its three siblings: the pinning
  equations on the four numbered simple root subgroups. The short root at the nonfinal node goes to
  the long root at the final one with the parameter squared, and the long root goes back to the
  short one with the parameter unchanged, which is the exponent convention `1` on a long simple
  root and the defining characteristic on a short one.
* `TauCeti.SpStd.specialIsogeny_specialIsogeny`: the square relation, that the isogeny composed
  with itself is the Frobenius `TauCeti.SpStd.frobenius 1 2 1`, transported from the symplectic
  group along the identification, with `TauCeti.SpStd.specialIsogeny_comp_specialIsogeny` stating
  it for the composite endomorphism itself.

## What is not here

No fixed-point subgroup is formed, no odd power `τ ^ (2m+1)` is taken, and nothing is claimed to be
finite or simple. The isogeny is built on the carrier alone, with no Lie-type index in sight.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v v'

variable (A : Type v) [CommRing A] [CharP A 2]

/-- **The special isogeny of the rank-two type-`C` carrier in characteristic two.** -/
noncomputable def specialIsogeny : points 1 A →* points 1 A :=
  (pointsMulEquivGLSymplecticFinOfCommRing 1 A).symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := A)).comp
      (pointsMulEquivGLSymplecticFinOfCommRing 1 A).toMonoidHom)

/-- The matrix of the carrier's special isogeny is the matrix of `2 × 2` minors. -/
@[simp]
theorem coe_specialIsogeny (g : points 1 A) :
    ((specialIsogeny A g : GL (Fin (1 + 1 + (1 + 1))) A) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) =
      Matrix.symplecticSpecialIsogeny ((g : GL (Fin (1 + 1 + (1 + 1))) A) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) A) := by
  rw [specialIsogeny, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_symm_apply, TauCeti.coe_specialIsogeny,
    coe_pointsMulEquivGLSymplecticFinOfCommRing_apply]

/-- The special isogeny of the carrier, read in the symplectic group. -/
theorem coe_specialIsogeny_gl (g : points 1 A) :
    ((specialIsogeny A g : points 1 A) : GL (Fin (1 + 1 + (1 + 1))) A) =
      ((TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFinOfCommRing 1 A g) :
        GLSymplecticFin 2 A) : GL (Fin (2 + 2)) A) := by
  rw [specialIsogeny, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_symm_apply]

/-- `pointsMulEquivGLSymplecticFinOfCommRing` intertwines the two special isogenies. -/
@[simp]
theorem pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny (g : points 1 A) :
    pointsMulEquivGLSymplecticFinOfCommRing 1 A (specialIsogeny A g) =
      TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFinOfCommRing 1 A g) := by
  rw [specialIsogeny]
  simp

/-- The inverse of `pointsMulEquivGLSymplecticFinOfCommRing` intertwines `TauCeti.specialIsogeny`
with `specialIsogeny`. -/
@[simp]
theorem pointsMulEquivGLSymplecticFinOfCommRing_symm_specialIsogeny (g : GLSymplecticFin 2 A) :
    (pointsMulEquivGLSymplecticFinOfCommRing 1 A).symm (TauCeti.specialIsogeny g) =
      specialIsogeny A ((pointsMulEquivGLSymplecticFinOfCommRing 1 A).symm g) := by
  rw [MulEquiv.symm_apply_eq, pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny,
    MulEquiv.apply_symm_apply]

omit [CommRing A] [CharP A 2] in
/-- Over a field of characteristic two, `pointsMulEquivGLSymplecticFin` intertwines the two special
isogenies. -/
@[simp]
theorem pointsMulEquivGLSymplecticFin_specialIsogeny (K : Type v) [Field K] [CharP K 2]
    (g : points 1 K) :
    pointsMulEquivGLSymplecticFin 1 K (specialIsogeny K g) =
      TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFin 1 K g) := by
  have hg (x : points 1 K) :
      pointsMulEquivGLSymplecticFin 1 K x = pointsMulEquivGLSymplecticFinOfCommRing 1 K x :=
    Subtype.ext ((coe_pointsMulEquivGLSymplecticFin_apply 1 x).trans
      (coe_pointsMulEquivGLSymplecticFinOfCommRing_apply 1 x).symm)
  rw [hg, hg, pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny]

omit [CommRing A] [CharP A 2] in
/-- `specialIsogeny` is natural with respect to ring homomorphisms `f : A →+* B` between
commutative rings of characteristic two. -/
@[simp]
theorem map_specialIsogeny {A : Type v} {B : Type v'} [CommRing A] [CharP A 2]
    [CommRing B] [CharP B 2] (f : A →+* B) (g : points 1 A) :
    (pointsPresentation 1 A).map (pointsPresentation 1 B) f (specialIsogeny A g) =
      specialIsogeny B ((pointsPresentation 1 A).map (pointsPresentation 1 B) f g) := by
  apply (pointsMulEquivGLSymplecticFinOfCommRing 1 B).injective
  rw [pointsMulEquivGLSymplecticFinOfCommRing_map,
    pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny,
    pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny,
    pointsMulEquivGLSymplecticFinOfCommRing_map, TauCeti.map_specialIsogeny]

/-- `specialIsogeny` commutes with the `2 ^ k`-power Frobenius endomorphism. -/
theorem specialIsogeny_frobenius (k : ℕ) (g : points 1 A) :
    specialIsogeny A (frobenius 1 2 k A g) = frobenius 1 2 k A (specialIsogeny A g) := by
  rw [frobenius_eq_map, map_specialIsogeny]

/-- **The square of the carrier's special isogeny is the Frobenius.** -/
@[simp]
theorem specialIsogeny_specialIsogeny (g : points 1 A) :
    specialIsogeny A (specialIsogeny A g) = frobenius 1 2 1 A g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny_gl, pointsMulEquivGLSymplecticFinOfCommRing_specialIsogeny,
    TauCeti.specialIsogeny_specialIsogeny, GLSymplecticFin.coe_map,
    coe_pointsMulEquivGLSymplecticFinOfCommRing_apply]
  ext i j
  rw [coe_frobenius_apply]
  simp [frobenius_def]

/-- **The square of the carrier's special isogeny is the Frobenius**, as an identity of monoid
homomorphisms, so a consumer taking odd powers can rewrite the composite itself. -/
@[simp]
theorem specialIsogeny_comp_specialIsogeny :
    (specialIsogeny A).comp (specialIsogeny A) = frobenius 1 2 1 A :=
  MonoidHom.ext fun g => specialIsogeny_specialIsogeny A g

private theorem zero_ne_last : (0 : Fin (1 + 1)) ≠ Fin.last 1 := by decide

private theorem last_one : Fin.last 1 = (1 : Fin (1 + 1)) := rfl

-- The two rank-two transports below name the successor node in one form and the numeral in the
-- other, so they need the index pair of a difference short-root element to be all that matters.
omit [CharP A 2] in
private theorem shortRootUnit_eq (t : A) :
    pointsMulEquivGLSymplecticFinOfCommRing 1 A
        (rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (0 : Fin (1 + 1)) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply,
    rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last 1 0 zero_ne_last,
    toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _ rfl
      (by simpa using Fin.orderSucc_castSucc (0 : Fin 1) : Order.succ (0 : Fin (1 + 1)) = 1)]

omit [CharP A 2] in
private theorem longRootUnit_eq (t : A) :
    pointsMulEquivGLSymplecticFinOfCommRing 1 A
        (rootSubgroupPoints 1 (.inl (Fin.last 1)) A (Multiplicative.ofAdd t)) =
      GLSymplecticFin.positiveLongRootTransvectionUnit 1 t := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply,
    rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit, toAdd_ofAdd, last_one]

/-- The isogeny carries the short simple root subgroup to the long one, squaring the parameter. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inl_zero (t : A) :
    specialIsogeny A (rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl (Fin.last 1)) A (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, shortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply] using
    congrArg (fun x : GLSymplecticFin 2 A => (x : GL (Fin (2 + 2)) A))
      (longRootUnit_eq A (t ^ 2)).symm

/-- The isogeny carries the long simple root subgroup to the short one, keeping the parameter. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inl_last (t : A) :
    specialIsogeny A (rootSubgroupPoints 1 (.inl (Fin.last 1)) A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, longRootUnit_eq,
    TauCeti.specialIsogeny_positiveLongRootTransvectionUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply] using
    congrArg (fun x : GLSymplecticFin 2 A => (x : GL (Fin (2 + 2)) A))
      (shortRootUnit_eq A t).symm

omit [CharP A 2] in
private theorem negShortRootUnit_eq (t : A) :
    pointsMulEquivGLSymplecticFinOfCommRing 1 A
        (rootSubgroupPoints 1 (.inr 0) A (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (1 : Fin (1 + 1)) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply,
    rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last 1 0 zero_ne_last,
    toAdd_ofAdd, GLSymplecticFin.differenceShortRootUnit_congr _ _
      (by simpa using Fin.orderSucc_castSucc (0 : Fin 1) : Order.succ (0 : Fin (1 + 1)) = 1) rfl]

omit [CharP A 2] in
private theorem negLongRootUnit_eq (t : A) :
    pointsMulEquivGLSymplecticFinOfCommRing 1 A
        (rootSubgroupPoints 1 (.inr (Fin.last 1)) A (Multiplicative.ofAdd t)) =
      GLSymplecticFin.negativeLongRootTransvectionUnit 1 t := by
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply,
    rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit, toAdd_ofAdd, last_one]

/-- The isogeny on the negative short simple root subgroup. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inr_zero (t : A) :
    specialIsogeny A (rootSubgroupPoints 1 (.inr 0) A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr (Fin.last 1)) A (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negShortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit_one_zero]
  simpa only [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply] using
    congrArg (fun x : GLSymplecticFin 2 A => (x : GL (Fin (2 + 2)) A))
      (negLongRootUnit_eq A (t ^ 2)).symm

/-- The isogeny on the negative long simple root subgroup. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints_inr_last (t : A) :
    specialIsogeny A (rootSubgroupPoints 1 (.inr (Fin.last 1)) A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr 0) A (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negLongRootUnit_eq,
    TauCeti.specialIsogeny_negativeLongRootTransvectionUnit]
  simpa only [coe_pointsMulEquivGLSymplecticFinOfCommRing_apply] using
    congrArg (fun x : GLSymplecticFin 2 A => (x : GL (Fin (2 + 2)) A))
      (negShortRootUnit_eq A t).symm

end TauCeti.SpStd
