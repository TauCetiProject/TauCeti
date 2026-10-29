/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Map

/-!
# Extension of scalars for the Lipschitz group

Extension of scalars sends each invertible Clifford generator to the corresponding pure tensor,
so it induces a homomorphism of Lipschitz groups. It sends the unit of a vector `v` to the unit of
`1 ⊗ₜ v`, and the scalar unit `a` to the scalar unit given by the image of `a`. The
twisted-conjugation action commutes with this homomorphism: on a pure tensor, the extended element
acts by extending the original action. Consequently the resulting map to the orthogonal group
agrees with scalar extension of orthogonal automorphisms.

## Main results

* `CliffordAlgebra.lipschitzGroupBaseChange` extends a Lipschitz element's scalars.
* `CliffordAlgebra.lipschitzGroupBaseChange_unitι` and
  `CliffordAlgebra.lipschitzGroupBaseChange_scalarUnits` show that the distinguished vector and
  scalar units are compatible with extension of scalars.
* `CliffordAlgebra.lipschitzVectorAction_baseChange_tmul` computes the extended action on pure
  tensors.
* `CliffordAlgebra.lipschitzToOrthogonal_baseChange` gives the commuting square with extension of
  orthogonal automorphisms.
* `CliffordAlgebra.lipschitzGroupBaseChange_baseChange` identifies direct and successive scalar
  extension.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]
variable (Q : QuadraticForm R M)

/-- The homomorphism of Lipschitz groups induced by extension of scalars. -/
def lipschitzGroupBaseChange : lipschitzGroup Q →* lipschitzGroup (Q.baseChange A) :=
  lipschitzGroupMapOf (ofBaseChangeAux A Q).toRingHom (fun m ↦ 1 ⊗ₜ m)
    (ofBaseChangeAux_ι A Q)

/-- The Clifford value of a scalar-extended Lipschitz element is obtained from the canonical
Clifford map. -/
@[simp]
theorem coe_lipschitzGroupBaseChange_apply (x : lipschitzGroup Q) :
    (((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
      (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) :=
  coe_lipschitzGroupMapOf_apply (ofBaseChangeAux A Q).toRingHom (fun m ↦ 1 ⊗ₜ m)
    (ofBaseChangeAux_ι A Q) x

/-- Extending the inverse of a Lipschitz unit agrees with taking the inverse after extension. -/
@[simp]
theorem lipschitzGroupBaseChange_inv_coe (x : lipschitzGroup Q) :
    ofBaseChangeAux A Q
        ((((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      ((((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
          (CliffordAlgebra (Q.baseChange A))ˣ)⁻¹ :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) :=
  lipschitzGroupMapOf_inv_coe (ofBaseChangeAux A Q).toRingHom (fun m ↦ 1 ⊗ₜ m)
    (ofBaseChangeAux_ι A Q) x

/-! ### The distinguished units -/

/-- Extension of scalars maps the Clifford unit represented by a vector `v` to the unit
represented by `1 ⊗ₜ v`. -/
@[simp]
theorem ofBaseChangeAux_unitι (v : M) [Invertible (Q v)] :
    Units.map (ofBaseChangeAux A Q) (unitι Q v) = unitι (Q.baseChange A) (1 ⊗ₜ v) := by
  ext
  simp

/-- The Lipschitz-group homomorphism induced by extension of scalars preserves the distinguished
vector units. -/
@[simp]
theorem lipschitzGroupBaseChange_unitι (v : M) [Invertible (Q v)] :
    lipschitzGroupBaseChange (A := A) Q ⟨unitι Q v, unitι_mem_lipschitzGroup v⟩ =
      ⟨unitι (Q.baseChange A) (1 ⊗ₜ v), unitι_mem_lipschitzGroup _⟩ := by
  ext
  simp

/-- The Lipschitz-group homomorphism induced by extension of scalars sends the scalar unit `a` to
the scalar unit given by the image of `a`. -/
@[simp]
theorem lipschitzGroupBaseChange_scalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    lipschitzGroupBaseChange (A := A) Q (scalarUnits Q hQ a) =
      scalarUnits (Q.baseChange A) (QuadraticForm.exists_isUnit_baseChange_apply A hQ)
        (Units.map (algebraMap R A) a) := by
  ext
  simp [IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A))]

/-- Extension of scalars on Lipschitz groups restricts, on scalar units, to the map on units
induced by `algebraMap`. -/
theorem lipschitzGroupBaseChange_comp_scalarUnits (hQ : ∃ v, IsUnit (Q v)) :
    (lipschitzGroupBaseChange (A := A) Q).comp (scalarUnits Q hQ) =
      (scalarUnits (Q.baseChange A) (QuadraticForm.exists_isUnit_baseChange_apply A hQ)).comp
        (Units.map (algebraMap R A)) :=
  MonoidHom.ext (lipschitzGroupBaseChange_scalarUnits Q hQ)

/-! ### The vector action -/

/-- On a pure tensor, the scalar-extended Lipschitz action is the extension of the original
action. -/
@[simp]
theorem lipschitzVectorAction_baseChange_tmul (x : lipschitzGroup Q) (a : A) (m : M) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    lipschitzVectorAction (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x) (a ⊗ₜ m) =
      a ⊗ₜ lipschitzVectorAction Q x m := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  suffices hOne :
      lipschitzVectorAction (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x)
          (1 ⊗ₜ m) =
        1 ⊗ₜ lipschitzVectorAction Q x m by
    have ha (n : M) : a ⊗ₜ[R] n = a • (1 ⊗ₜ[R] n) := by
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' a (1 : A) n).symm
    rw [ha, map_smul, hOne, ← ha]
  apply ι_injective (Q.baseChange A)
  have hinv :
      ((((lipschitzGroupBaseChange (A := A) Q x : lipschitzGroup (Q.baseChange A)) :
          (CliffordAlgebra (Q.baseChange A))ˣ)⁻¹ :
        (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
        ofBaseChangeAux A Q
          ((((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
            CliffordAlgebra Q)) :=
    (lipschitzGroupBaseChange_inv_coe (A := A) Q x).symm
  rw [ι_lipschitzVectorAction_apply, coe_lipschitzGroupBaseChange_apply,
    ← ofBaseChangeAux_involute, hinv, ← ofBaseChangeAux_ι A Q m,
    ← map_mul, ← map_mul, ← ι_lipschitzVectorAction_apply, ofBaseChangeAux_ι]

/-- Extension of scalars commutes with the Lipschitz homomorphism to the orthogonal group. -/
@[simp]
theorem lipschitzToOrthogonal_baseChange (x : lipschitzGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.QuadraticMap.orthogonalGroupBaseChange (A := A) Q (lipschitzToOrthogonal Q x) =
      lipschitzToOrthogonal (Q.baseChange A) (lipschitzGroupBaseChange (A := A) Q x) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [TauCeti.QuadraticMap.orthogonalGroupBaseChange_apply_tmul,
        coe_lipschitzToOrthogonal_apply, coe_lipschitzToOrthogonal_apply,
        lipschitzVectorAction_baseChange_tmul]
  | add z w hz hw =>
      simp only [map_add, hz, hw]

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Direct and successive scalar extension of a Lipschitz element agree after transport along the
canonical scalar-tower isometry. -/
@[simp]
theorem lipschitzGroupBaseChange_baseChange (x : lipschitzGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry.lipschitzGroupMap
        (lipschitzGroupBaseChange (A := B) Q x) =
      lipschitzGroupBaseChange (A := B) (Q.baseChange A)
        (lipschitzGroupBaseChange (A := A) Q x) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  apply Units.ext
  rw [QuadraticMap.Isometry.coe_lipschitzGroupMap_apply,
    coe_lipschitzGroupBaseChange_apply, coe_lipschitzGroupBaseChange_apply,
    coe_lipschitzGroupBaseChange_apply]
  exact ofBaseChangeAux_baseChange Q _

end ScalarTower

end CliffordAlgebra
