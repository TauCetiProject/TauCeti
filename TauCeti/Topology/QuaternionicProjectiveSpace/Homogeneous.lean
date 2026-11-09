/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.UnitaryMatrix
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.CornerBlock
public import TauCeti.Topology.QuaternionicProjectiveSpace.Basic
import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# Quaternionic projective space as the homogeneous space `Sp(n + 1) / (Sp(1) × Sp(n))`

The compact symplectic group `Sp(n + 1) = unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)` acts
on quaternionic projective space `HPⁿ` by `A • [x] = [A x]`
(`TauCeti.QuaternionicProjectiveSpace.smul_mk`): a quaternionic unitary matrix maps the unit
sphere `S⁴ⁿ⁺³` of `ℍⁿ⁺¹` to itself and commutes with unit quaternions acting on the right, so it
descends to the quotient by right multiplication. The action is continuous, and it is
transitive, because `Sp(n + 1)` already acts transitively on the unit sphere
(`TauCeti.exists_quaternionUnitaryIsometry_apply_single_eq`).

The stabilizer of the base point `[e₀]` consists of the unitary matrices whose column `0` is a
unit quaternion multiple of `e₀`; these are exactly the block-diagonal matrices `diag(q, B)` with
`q ∈ Sp(1)`, the unit quaternions, and `B ∈ Sp(n)`
(`TauCeti.QuaternionicProjectiveSpace.range_unitaryProdBlockSucc_eq_stabilizer`, through
`Matrix.mem_range_unitaryProdBlockSucc_iff`). As `Sp(n + 1)` is compact and `HPⁿ` is Hausdorff,
the orbit map `A ↦ [A e₀]` induces a homeomorphism

`Sp(n + 1) ⧸ (Sp(1) × Sp(n)) ≃ₜ HPⁿ`

(`TauCeti.QuaternionicProjectiveSpace.unitaryQuotientHomeomorph`), equivariant for the left
actions of `Sp(n + 1)`.

## Main definitions

* `TauCeti.QuaternionicProjectiveSpace.instMulActionUnitary`: the action `A • [x] = [A x]`.
* `TauCeti.QuaternionicProjectiveSpace.basePoint`: the point `[e₀]`.
* `TauCeti.QuaternionicProjectiveSpace.unitaryQuotientHomeomorph`: the homeomorphism
  `Sp(n + 1) ⧸ (Sp(1) × Sp(n)) ≃ₜ HPⁿ`, `[A] ↦ [A e₀]`.

## Main results

* `TauCeti.QuaternionicProjectiveSpace.instContinuousSMulUnitary`,
  `TauCeti.QuaternionicProjectiveSpace.instIsPretransitiveUnitary`: the action is continuous and
  transitive.
* `TauCeti.QuaternionicProjectiveSpace.mem_stabilizer_basePoint_iff`: a quaternionic unitary
  matrix fixes `[e₀]` exactly when its column `0` vanishes below the corner.
* `TauCeti.QuaternionicProjectiveSpace.range_unitaryProdBlockSucc_eq_stabilizer`: the stabilizer
  of `[e₀]` is the block-diagonal subgroup `Sp(1) × Sp(n)`.
* `TauCeti.QuaternionicProjectiveSpace.unitaryQuotientHomeomorph_mk`,
  `TauCeti.QuaternionicProjectiveSpace.unitaryQuotientHomeomorph_smul`: the homeomorphism sends
  the coset of `A` to `A • [e₀]` and is equivariant.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (coset
  spaces of the classical groups).
-/

public section

noncomputable section

open Metric MulOpposite
open scoped Matrix Quaternion RightActions

namespace TauCeti

namespace QuaternionicProjectiveSpace

variable {n : ℕ}

/-- A quaternionic unitary matrix commutes with unit quaternions acting on the right of the unit
sphere. -/
private theorem quaternionUnitaryIsometry_smul_op_smul
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (q : sphere (0 : ℍ) 1)
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    quaternionUnitaryIsometry _ A • (x <• q) = (quaternionUnitaryIsometry _ A • x) <• q :=
  Subtype.ext <| by
    simp only [LinearIsometryEquiv.coe_smul_unitSphere, Sphere.coe_op_sphere_smul, unop_op,
      quaternionUnitaryIsometry_op_smul]

/-- A quaternionic unitary matrix acts on `HPⁿ` by `A • [x] = [A x]`. -/
instance instSMulUnitary :
    SMul (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (QuaternionicProjectiveSpace n) where
  smul A := QuaternionicProjectiveSpace.lift n
    (fun x ↦ mk n (quaternionUnitaryIsometry _ A • x)) fun q x ↦ by
      rw [quaternionUnitaryIsometry_smul_op_smul, mk_op_smul]

/-- A quaternionic unitary matrix acts on `HPⁿ` by acting on representatives in the unit
sphere. -/
@[simp]
theorem smul_mk (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    A • mk n x = mk n (quaternionUnitaryIsometry _ A • x) :=
  QuaternionicProjectiveSpace.lift_mk n _ _ x

/-- **The compact symplectic group `Sp(n + 1)` acts on `HPⁿ`** by `A • [x] = [A x]`. -/
instance instMulActionUnitary :
    MulAction (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (QuaternionicProjectiveSpace n) where
  one_smul p := by
    induction p using QuaternionicProjectiveSpace.inductionOn with
    | h x => rw [smul_mk, map_one, one_smul]
  mul_smul A B p := by
    induction p using QuaternionicProjectiveSpace.inductionOn with
    | h x => rw [smul_mk, smul_mk, smul_mk, map_mul, mul_smul]

/-- The action of `Sp(n + 1)` on `HPⁿ` is continuous. -/
instance instContinuousSMulUnitary :
    ContinuousSMul (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
      (QuaternionicProjectiveSpace n) where
  continuous_smul := by
    -- `id × mk` is a quotient map, through which the action is the projection of the action on
    -- the unit sphere.
    have hq := ((IsOpenQuotientMap.id
      (X := unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))).prodMap
        (isOpenQuotientMap_mk n)).isQuotientMap
    rw [hq.continuous_iff]
    have hsphere : Continuous fun p : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ×
        sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 ↦ quaternionUnitaryIsometry _ p.1 • p.2 :=
      continuous_induced_rng.2 <| (continuous_quaternionUnitaryIsometry_apply.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).congr fun p ↦ by
          simp
    exact ((continuous_mk n).comp hsphere).congr fun p ↦ (smul_mk p.1 p.2).symm

variable (n) in
/-- The **base point** `[e₀]` of `HPⁿ`, the quaternionic line spanned by the first standard
basis vector. -/
def basePoint : QuaternionicProjectiveSpace n :=
  mk n ⟨WithLp.toLp 2 (Pi.single 0 1), by simp⟩

/-- **The compact symplectic group acts transitively on `HPⁿ`**: every point is `[A e₀]` for some
quaternionic unitary matrix `A`. -/
instance instIsPretransitiveUnitary :
    MulAction.IsPretransitive (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
      (QuaternionicProjectiveSpace n) := by
  refine .of_orbit (x₀ := basePoint n) fun p ↦ ?_
  induction p using QuaternionicProjectiveSpace.inductionOn with
  | h x =>
    obtain ⟨A, hA⟩ := exists_quaternionUnitaryIsometry_apply_single_eq 0
      (mem_sphere_zero_iff_norm.1 x.2)
    refine ⟨A, ?_⟩
    rw [basePoint, smul_mk]
    exact congrArg (mk n) (Subtype.ext ((LinearIsometryEquiv.coe_smul_unitSphere _ _).trans hA))

/-- **The stabilizer of `[e₀]`**: a quaternionic unitary matrix fixes the base point of `HPⁿ`
exactly when its column `0` vanishes below the corner, that is, when it maps `e₀` to a
quaternionic multiple of `e₀`. -/
theorem mem_stabilizer_basePoint_iff {A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)} :
    A ∈ MulAction.stabilizer (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (basePoint n) ↔
      ∀ i : Fin n, A.1 i.succ 0 = 0 := by
  rw [MulAction.mem_stabilizer_iff, basePoint, smul_mk, mk_eq_mk_iff]
  constructor
  · rintro ⟨q, hq⟩ i
    have h := congrArg (fun v : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 ↦
      WithLp.ofLp (v : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) i.succ) hq
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Fin.succ_ne_zero, eq_comm] using h
  · intro hA
    -- The image of `e₀` is its column `0`, the multiple `e₀ A₀₀`, and `A₀₀` is a unit quaternion.
    obtain ⟨⟨q, B⟩, hqB⟩ := Matrix.mem_range_unitaryProdBlockSucc_iff.2 hA
    refine ⟨⟨q, by simp [CStarRing.norm_of_mem_unitary q.2]⟩, Subtype.ext ?_⟩
    refine PiLp.ext fun i ↦ ?_
    simp only [Sphere.coe_op_sphere_smul, LinearIsometryEquiv.coe_smul_unitSphere,
      quaternionUnitaryIsometry_apply, WithLp.ofLp_smul, WithLp.ofLp_toLp,
      Matrix.mulVec_single_one, unop_op]
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [← hqB, Fin.succ_ne_zero]

/-- **The stabilizer of `[e₀]` is `Sp(1) × Sp(n)`**: it is the image of the block-diagonal
embedding `(q, B) ↦ diag(q, B)` of `Sp(1) × Sp(n)` in `Sp(n + 1)`. -/
theorem range_unitaryProdBlockSucc_eq_stabilizer :
    (Matrix.unitaryProdBlockSucc ℍ n).range =
      MulAction.stabilizer (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (basePoint n) := by
  ext A
  rw [Matrix.mem_range_unitaryProdBlockSucc_iff, mem_stabilizer_basePoint_iff]

/-- The orbit map `A ↦ A • [e₀]` of `Sp(n + 1)` on `HPⁿ` is continuous. -/
private theorem continuous_smul_basePoint :
    Continuous fun A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ↦ A • basePoint n :=
  continuous_id.smul continuous_const

variable (n) in
/-- **Quaternionic projective space is the homogeneous space `Sp(n + 1) / (Sp(1) × Sp(n))`**: the
orbit map `A ↦ [A e₀]` induces a homeomorphism from the quotient of the compact symplectic group
`Sp(n + 1)` by the block-diagonal subgroup `Sp(1) × Sp(n)` onto `HPⁿ`. -/
def unitaryQuotientHomeomorph :
    unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ⧸ (Matrix.unitaryProdBlockSucc ℍ n).range ≃ₜ
      QuaternionicProjectiveSpace n :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by
      rw [range_unitaryProdBlockSucc_eq_stabilizer]).trans
    (quotientStabilizerHomeomorph _ (basePoint n) continuous_smul_basePoint)

/-- The homeomorphism `Sp(n + 1) ⧸ (Sp(1) × Sp(n)) ≃ₜ HPⁿ` sends the coset of `A` to
`A • [e₀]`. -/
@[simp]
theorem unitaryQuotientHomeomorph_mk (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    unitaryQuotientHomeomorph n (QuotientGroup.mk A) = A • basePoint n :=
  quotientStabilizerHomeomorph_mk _ (basePoint n) continuous_smul_basePoint A

/-- The homeomorphism `Sp(n + 1) ⧸ (Sp(1) × Sp(n)) ≃ₜ HPⁿ` is equivariant for the left actions of
`Sp(n + 1)`. -/
theorem unitaryQuotientHomeomorph_smul (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
    (q : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ⧸ (Matrix.unitaryProdBlockSucc ℍ n).range) :
    unitaryQuotientHomeomorph n (A • q) = A • unitaryQuotientHomeomorph n q := by
  induction q using QuotientGroup.induction_on with
  | H B => rw [MulAction.Quotient.smul_mk, unitaryQuotientHomeomorph_mk,
      unitaryQuotientHomeomorph_mk, smul_eq_mul, mul_smul]

end QuaternionicProjectiveSpace

end TauCeti
