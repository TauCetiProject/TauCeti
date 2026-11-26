/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Special.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Reductive
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.LinearAlgebra.BilinearForm.SepClosed

/-!
# Special orthogonal groups of nonsingular symmetric forms

Over a field of characteristic different from two, the determinant-one subgroup scheme of a
nonsingular symmetric matrix is reductive. Over an algebraic closure the matrix is congruent
to the identity, so the geometric fibre is the standard special orthogonal group. This uses
the standard reductivity theorem in every rank and the same descent theorem as the
antidiagonal special orthogonal case.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.ConstantForm.Special

universe u

/-- For the identity form, the determinant-one Hopf ideal is the standard special orthogonal
Hopf ideal. -/
theorem definingHopfIdeal_one (R : Type u) [CommRing R] (n : ℕ) :
    definingHopfIdeal R n (1 : Matrix (Fin n) (Fin n) R) =
      SpecialOrthogonal.definingHopfIdeal R n := by
  rw [definingHopfIdeal_def, SpecialOrthogonal.definingHopfIdeal_def]

/-- When `P C Pᵀ = 1`, the finite-type coordinate Hopf algebra of the determinant-one
subgroup for `C` is isomorphic to that of the standard special orthogonal group. -/
noncomputable def finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal
    {R : Type u} [CommRing R] {n : ℕ} {C : Matrix (Fin n) (Fin n) R} (P : GL (Fin n) R)
    (hP : (P : Matrix (Fin n) (Fin n) R) * C * (P : Matrix (Fin n) (Fin n) R)ᵀ = 1) :
    finiteTypeCoordinateHopfAlgebra R n C ≅ SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra R n :=
  ObjectProperty.isoMk _ (eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n C) ≪≫
    coordinateHopfAlgebraCongr P hP ≪≫
    eqToIso (congrArg (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R n))
      (definingHopfIdeal_one R n)) ≪≫
    eqToIso (SpecialOrthogonal.finiteTypeCoordinateHopfAlgebra_obj R n).symm)

/-- The special orthogonal group of a nonsingular symmetric form over a field of characteristic
different from two is reductive. This includes smoothness and geometric connectedness. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    {k : Type u} [Field k] [NeZero (2 : k)] {n : ℕ} {C : Matrix (Fin n) (Fin n) k}
    (hC : C.IsSymm) (hdet : C.det ≠ 0) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n C) := by
  let K := AlgebraicClosure k
  let f := algebraMap k K
  let _ : NeZero (2 : K) := ⟨by
    simpa only [map_ofNat] using (map_ne_zero f).2 (NeZero.ne (2 : k))⟩
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  have hdetK : (C.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 hdet
  obtain ⟨P, hP⟩ := (hC.map f).exists_mul_mul_transpose_eq_one_of_isSepClosed hdetK
  let e := finiteTypeCoordinateHopfAlgebraBaseChangeIso
      (R := k) (S := K) (C := C) (C' := C.map f) rfl ≪≫
    finiteTypeCoordinateHopfAlgebraIsoSpecialOrthogonal P hP
  exact reductiveCommHopfAlgProperty.of_baseChange_algebraicClosure <|
    (reductiveCommHopfAlgProperty K).prop_of_iso e.symm
      (SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra K n)

end TauCeti.ConstantForm.Special
