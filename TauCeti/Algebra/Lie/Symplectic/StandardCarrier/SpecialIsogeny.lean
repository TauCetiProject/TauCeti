/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny

/-!
# The special isogeny of the rank-two type-`C` carrier

The rank-two member of the explicit full-weight type-`C` Chevalley carrier is the ambient group
of the two classification-list families on the `B₂` diagram, the untwisted `B₂(q)` and the Suzuki
family `²B₂(2^(2m+1))`. Over a field of characteristic two its points carry the special isogeny,
the endomorphism exchanging the two root lengths whose odd powers cut out the Suzuki groups. This
file transports that endomorphism from the symplectic group to the carrier.

The transport is possible because the two point groups coincide:
`TauCeti.SpStd.points_eq_GLSymplecticFin` identifies the carrier's points with the symplectic
matrices over any field, so the special isogeny of `Sp₄` restricts to an endomorphism of the
carrier rather than merely mapping it into a larger group. Nothing else is needed, and in
particular no new matrix computation appears below: the four pinning equations and the square
relation are the symplectic-group statements read through that identification.

## Main definitions

* `TauCeti.SpStd.pointsMulEquivGLSymplecticFin`: the identification of the rank-two carrier's
  points with the symplectic group.
* `TauCeti.SpStd.specialIsogeny`: the special isogeny of the carrier in characteristic two.

## Main results

* `TauCeti.SpStd.specialIsogeny_rootSubgroupPoints_inl_zero` and its three siblings: the pinning
  equations on the four numbered simple root subgroups. The short root at the nonfinal node goes to
  the long root at the final one with the parameter squared, and the long root goes back to the
  short one with the parameter unchanged, which is the exponent convention `1` on a long simple
  root and the defining characteristic on a short one.
* `TauCeti.SpStd.specialIsogeny_specialIsogeny`: the square relation, that the isogeny composed
  with itself is the Frobenius `TauCeti.SpStd.frobenius 1 2 1`.

## What is not here

No fixed-point subgroup is formed, no odd power `τ ^ (2m+1)` is taken, and nothing is claimed to be
finite or simple. The isogeny is built on the carrier alone, with no Lie-type index in sight.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.

## Roadmap

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`, which lists the special isogenies in characteristics
two and three among its targets. Its consumer is milestone `L2` of
`TauCetiRoadmap/CFSGStatement/README.md`, which owns the selection of this isogeny for a
`SuzukiReeIndex` and the odd power `τ ^ (2m+1)`; neither is taken here.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (K : Type v) [Field K]

/-- The rank-two carrier's points are the symplectic group. -/
noncomputable def pointsMulEquivGLSymplecticFin :
    points 1 K ≃* GLSymplecticFin 2 K :=
  MulEquiv.subgroupCongr (points_eq_GLSymplecticFin 1)

@[simp]
theorem coe_pointsMulEquivGLSymplecticFin (g : points 1 K) :
    ((pointsMulEquivGLSymplecticFin K g : GLSymplecticFin 2 K) :
        GL (Fin (1 + 1 + (1 + 1))) K) = (g : GL (Fin (1 + 1 + (1 + 1))) K) := by
  rw [pointsMulEquivGLSymplecticFin]
  rfl

variable [CharP K 2]

/-- **The special isogeny of the rank-two type-`C` carrier in characteristic two.** -/
noncomputable def specialIsogeny : points 1 K →* points 1 K :=
  (pointsMulEquivGLSymplecticFin K).symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := K)).comp (pointsMulEquivGLSymplecticFin K).toMonoidHom)

/-- The matrix of the carrier's special isogeny is the matrix of `2 × 2` minors. -/
@[simp]
theorem coe_specialIsogeny (g : points 1 K) :
    ((specialIsogeny K g : GL (Fin (1 + 1 + (1 + 1))) K) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) K) =
      specialIsogenyMatrix ((g : GL (Fin (1 + 1 + (1 + 1))) K) :
        Matrix (Fin (1 + 1 + (1 + 1))) (Fin (1 + 1 + (1 + 1))) K) := by
  rw [specialIsogeny]
  simp [pointsMulEquivGLSymplecticFin]

/-- The special isogeny of the carrier, read in the symplectic group. -/
theorem coe_specialIsogeny_gl (g : points 1 K) :
    ((specialIsogeny K g : points 1 K) : GL (Fin (1 + 1 + (1 + 1))) K) =
      ((TauCeti.specialIsogeny (pointsMulEquivGLSymplecticFin K g) :
        GLSymplecticFin 2 K) : GL (Fin (2 + 2)) K) := by
  rw [specialIsogeny]
  simp [pointsMulEquivGLSymplecticFin]

/-- **The square of the carrier's special isogeny is the Frobenius.** -/
theorem specialIsogeny_specialIsogeny (g : points 1 K) :
    specialIsogeny K (specialIsogeny K g) = frobenius 1 2 1 K g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [coe_specialIsogeny, coe_specialIsogeny,
    specialIsogenyMatrix_specialIsogenyMatrix
      (GLSymplecticFin.mem_iff.mp (mem_GLSymplecticFin_of_mem_points 1 g.2)),
    Matrix.map_apply, coe_frobenius_apply]
  norm_num

private theorem zero_ne_last : (0 : Fin (1 + 1)) ≠ Fin.last 1 := by decide

private theorem next_zero : next 1 0 zero_ne_last = 1 := Fin.ext (by rw [val_next]; rfl)

private theorem last_one : Fin.last 1 = (1 : Fin (1 + 1)) := rfl

/-- The difference short-root element depends on its index pair only. -/
theorem differenceShortRootUnit_congr {m : ℕ} {R : Type*} [CommRing R] {i j i' j' : Fin m}
    (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j') (c : R) :
    GLSymplecticFin.differenceShortRootUnit hij c =
      GLSymplecticFin.differenceShortRootUnit hij' c := by
  subst hi
  subst hj
  rfl

omit [CharP K 2] in
private theorem shortRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin K (rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (0 : Fin (1 + 1)) ≠ 1 by decide) t := by
  rw [← differenceShortRootUnit_congr (ne_next 1 0 zero_ne_last)
    (show (0 : Fin (1 + 1)) ≠ 1 by decide) rfl next_zero t]
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin,
    rootSubgroupPoints_inl_of_ne_last 1 0 zero_ne_last (Multiplicative.ofAdd t)]
  rfl

omit [CharP K 2] in
private theorem longRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin K
        (rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.positiveLongRootTransvectionUnit 1 t := by
  rw [← last_one]
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin,
    rootSubgroupPoints_inl_last 1 (Multiplicative.ofAdd t)]
  rfl

/-- The isogeny carries the short simple root subgroup to the long one, squaring the parameter. -/
theorem specialIsogeny_rootSubgroupPoints_inl_zero (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, shortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit]
  have h := congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
    (longRootUnit_eq K (t ^ 2))
  rw [coe_pointsMulEquivGLSymplecticFin] at h
  exact h.symm

/-- The isogeny carries the long simple root subgroup to the short one, keeping the parameter. -/
theorem specialIsogeny_rootSubgroupPoints_inl_last (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inl (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inl 0) K (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, longRootUnit_eq,
    TauCeti.specialIsogeny_positiveLongRootTransvectionUnit]
  have h := congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
    (shortRootUnit_eq K t)
  rw [coe_pointsMulEquivGLSymplecticFin] at h
  exact h.symm

omit [CharP K 2] in
private theorem negShortRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin K (rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.differenceShortRootUnit (show (1 : Fin (1 + 1)) ≠ 0 by decide) t := by
  rw [← differenceShortRootUnit_congr (ne_next 1 0 zero_ne_last).symm
    (show (1 : Fin (1 + 1)) ≠ 0 by decide) next_zero rfl t]
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin,
    rootSubgroupPoints_inr_of_ne_last 1 0 zero_ne_last (Multiplicative.ofAdd t)]
  rfl

omit [CharP K 2] in
private theorem negLongRootUnit_eq (t : K) :
    pointsMulEquivGLSymplecticFin K
        (rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      GLSymplecticFin.negativeLongRootTransvectionUnit 1 t := by
  rw [← last_one]
  apply Subtype.ext
  rw [coe_pointsMulEquivGLSymplecticFin,
    rootSubgroupPoints_inr_last 1 (Multiplicative.ofAdd t)]
  rfl

/-- The isogeny on the negative short simple root subgroup. -/
theorem specialIsogeny_rootSubgroupPoints_inr_zero (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd (t ^ 2)) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negShortRootUnit_eq,
    TauCeti.specialIsogeny_differenceShortRootUnit_one_zero]
  have h := congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
    (negLongRootUnit_eq K (t ^ 2))
  rw [coe_pointsMulEquivGLSymplecticFin] at h
  exact h.symm

/-- The isogeny on the negative long simple root subgroup. -/
theorem specialIsogeny_rootSubgroupPoints_inr_last (t : K) :
    specialIsogeny K (rootSubgroupPoints 1 (.inr (Fin.last 1)) K (Multiplicative.ofAdd t)) =
      rootSubgroupPoints 1 (.inr 0) K (Multiplicative.ofAdd t) := by
  apply Subtype.ext
  rw [coe_specialIsogeny_gl, negLongRootUnit_eq,
    TauCeti.specialIsogeny_negativeLongRootTransvectionUnit]
  have h := congrArg (fun x : GLSymplecticFin 2 K => (x : GL (Fin (2 + 2)) K))
    (negShortRootUnit_eq K t)
  rw [coe_pointsMulEquivGLSymplecticFin] at h
  exact h.symm

end TauCeti.SpStd
