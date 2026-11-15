/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints

/-!
# Congruence subgroups of the general linear group

Under the identification `TauCeti.GeneralLinear.pointsMulEquiv` of the points of `GL_n` with
invertible matrices, the congruence subgroup of level `I` is the classical principal congruence
subgroup `{g ∈ GL_n(A) : g ≡ 1 mod I}`, the kernel of reduction of matrix entries modulo `I`.

## Main declarations

* `TauCeti.GeneralLinear.map_congruenceSubgroup`: the image of the congruence subgroup of level
  `I` is the kernel of `Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)`.
* `TauCeti.GeneralLinear.mem_congruenceSubgroup_iff`: a point lies in the congruence subgroup of
  level `I` exactly when its matrix is congruent to the identity matrix entrywise modulo `I`.
-/

public section

namespace TauCeti

namespace GeneralLinear

variable {R : Type*} [CommRing R] (n : ℕ) {A : Type*} [CommRing A] [Algebra R A]

/-- Under `pointsMulEquiv`, the congruence subgroup of level `I` of `GL_n` is the kernel of the
reduction map `GL_n(A) → GL_n(A ⧸ I)`. -/
theorem map_congruenceSubgroup (I : Ideal A) :
    (HopfAlgebra.congruenceSubgroup R (coordinateHopfAlgebra R n) I).map
        (pointsMulEquiv (R := R) (A := A) n).toMonoidHom =
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).ker := by
  ext g
  rw [Subgroup.mem_map_equiv, HopfAlgebra.mem_congruenceSubgroup_iff_mapValue_eq_one,
    MonoidHom.mem_ker, ← (pointsMulEquiv (R := R) (A := A ⧸ I) n).map_eq_one_iff,
    pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, ← AlgHom.toRingHom_eq_coe,
    Ideal.Quotient.mkₐ_toRingHom]

/-- A point of `GL_n` lies in the congruence subgroup of level `I` exactly when its matrix is
congruent to the identity matrix entrywise modulo `I`. -/
theorem mem_congruenceSubgroup_iff {I : Ideal A}
    {x : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)} :
    x ∈ HopfAlgebra.congruenceSubgroup R (coordinateHopfAlgebra R n) I ↔
      ∀ i j, (pointsMulEquiv n x : Matrix (Fin n) (Fin n) A) i j -
        (1 : Matrix (Fin n) (Fin n) A) i j ∈ I := by
  rw [← Subgroup.mem_map_iff_mem (f := (pointsMulEquiv (R := R) (A := A) n).toMonoidHom)
    (pointsMulEquiv n).injective, map_congruenceSubgroup, MonoidHom.mem_ker,
    MulEquiv.coe_toMonoidHom, Matrix.GeneralLinearGroup.ext_iff]
  refine forall₂_congr fun i j ↦ ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, ← Ideal.Quotient.eq,
    Matrix.one_apply, Matrix.one_apply, apply_ite (Ideal.Quotient.mk I), map_one, map_zero]

end GeneralLinear

end TauCeti
