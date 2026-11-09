/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.ComplexProjectiveSpace.Basic
import TauCeti.Topology.Algebra.GroupAction.Transitive
import TauCeti.Topology.Grassmannian.FrameQuotient

/-!
# Complex projective space as the homogeneous space `U(n + 1) / (U(1) × U(n))`

The unitary group `U(n + 1) = Matrix.unitaryGroup (Fin (n + 1)) ℂ` acts on complex projective
space `CPⁿ` by `A • [x] = [A x]` (`TauCeti.ComplexProjectiveSpace.smul_mk`): a unitary matrix
maps the unit sphere `S²ⁿ⁺¹` to itself and commutes with unit complex scalars, so it descends to
the circle quotient. The action is continuous, and it is transitive: a unit vector extends to an
orthonormal basis, whose vectors are the columns of a unitary matrix
(`TauCeti.finiteOrthonormalFrame.unitaryMap_standard_surjective`, for frames of one vector).

The stabilizer of the base point `[e₀]` consists of the unitary matrices whose column `0` is a
unit multiple of `e₀`; these are exactly the block-diagonal matrices `diag(c, B)` with `c ∈ U(1)`
and `B ∈ U(n)` (`TauCeti.ComplexProjectiveSpace.range_prodBlockSucc_eq_stabilizer`, through
`Matrix.UnitaryGroup.mem_range_prodBlockSucc_iff`). As `U(n + 1)` is compact and `CPⁿ` is
Hausdorff, the orbit map `A ↦ [A e₀]` induces a homeomorphism

`U(n + 1) ⧸ (U(1) × U(n)) ≃ₜ CPⁿ`

(`TauCeti.ComplexProjectiveSpace.unitaryQuotientHomeomorph`), equivariant for the left actions of
`U(n + 1)`. This compares the circle-quotient model of `CPⁿ` with its description as a homogeneous
space of the unitary group, with isotropy group `U(1) × U(n)` at `[e₀]`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.instMulActionUnitaryGroup`: the action `A • [x] = [A x]`.
* `TauCeti.ComplexProjectiveSpace.basePoint`: the point `[e₀]`.
* `TauCeti.ComplexProjectiveSpace.unitaryQuotientHomeomorph`: the homeomorphism
  `U(n + 1) ⧸ (U(1) × U(n)) ≃ₜ CPⁿ`, `[A] ↦ [A e₀]`.

## Main results

* `TauCeti.ComplexProjectiveSpace.instContinuousSMulUnitaryGroup`,
  `TauCeti.ComplexProjectiveSpace.instIsPretransitiveUnitaryGroup`: the action is continuous and
  transitive.
* `TauCeti.ComplexProjectiveSpace.mem_stabilizer_basePoint_iff`: a unitary matrix fixes `[e₀]`
  exactly when its column `0` vanishes below the corner.
* `TauCeti.ComplexProjectiveSpace.range_prodBlockSucc_eq_stabilizer`: the stabilizer of `[e₀]` is
  the block-diagonal subgroup `U(1) × U(n)`.
* `TauCeti.ComplexProjectiveSpace.unitaryQuotientHomeomorph_mk`,
  `TauCeti.ComplexProjectiveSpace.unitaryQuotientHomeomorph_smul`: the homeomorphism sends the
  coset of `A` to `A • [e₀]` and is equivariant.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (coset
  spaces of the classical groups).
-/

public section

noncomputable section

open Matrix Metric

namespace TauCeti

namespace ComplexProjectiveSpace

variable {n : ℕ}

/-- A unitary matrix maps unit complex multiples of a unit vector to unit complex multiples of its
image: it commutes with the action of the circle on the unit sphere. -/
private theorem toLinearIsometryEquiv_smul_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (c : sphere (0 : ℂ) 1) (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    UnitaryGroup.toLinearIsometryEquiv A • (c • x) =
      c • (UnitaryGroup.toLinearIsometryEquiv A • x) :=
  Subtype.ext <| by
    simp only [LinearIsometryEquiv.coe_smul_unitSphere, Sphere.coe_sphere_smul, map_smul]

/-- A unitary matrix acts on `CPⁿ` by `A • [x] = [A x]`. -/
instance instSMulUnitaryGroup : SMul (unitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) where
  smul A := ComplexProjectiveSpace.lift n
    (fun x ↦ mk n (UnitaryGroup.toLinearIsometryEquiv A • x)) fun c x ↦ by
      rw [toLinearIsometryEquiv_smul_smul, mk_smul]

/-- A unitary matrix acts on `CPⁿ` by acting on representatives in the unit sphere. -/
@[simp]
theorem smul_mk (A : unitaryGroup (Fin (n + 1)) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    A • mk n x = mk n (UnitaryGroup.toLinearIsometryEquiv A • x) :=
  ComplexProjectiveSpace.lift_mk n _ _ x

/-- **The unitary group `U(n + 1)` acts on `CPⁿ`** by `A • [x] = [A x]`. -/
instance instMulActionUnitaryGroup :
    MulAction (unitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) where
  one_smul p := by
    induction p using ComplexProjectiveSpace.inductionOn with
    | h x => rw [smul_mk, map_one, one_smul]
  mul_smul A B p := by
    induction p using ComplexProjectiveSpace.inductionOn with
    | h x => rw [smul_mk, smul_mk, smul_mk, map_mul, mul_smul]

/-- The action of a unitary matrix on the unit sphere is jointly continuous. -/
private theorem continuous_toLinearIsometryEquiv_smul :
    Continuous fun p : unitaryGroup (Fin (n + 1)) ℂ ×
        sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
      UnitaryGroup.toLinearIsometryEquiv p.1 • p.2 := by
  refine continuous_induced_rng.2 <| (continuous_uncurry_toEuclideanCLM.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).congr fun p ↦ ?_
  simp

/-- The action of `U(n + 1)` on `CPⁿ` is continuous. -/
instance instContinuousSMulUnitaryGroup :
    ContinuousSMul (unitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) where
  continuous_smul := by
    -- `id × mk` is a quotient map, through which the action is the projection of the action on
    -- the unit sphere.
    have hq := ((IsOpenQuotientMap.id (X := unitaryGroup (Fin (n + 1)) ℂ)).prodMap
      (isOpenQuotientMap_mk n)).isQuotientMap
    rw [hq.continuous_iff]
    exact ((continuous_mk n).comp continuous_toLinearIsometryEquiv_smul).congr fun p ↦
      (smul_mk p.1 p.2).symm

variable (n) in
/-- The **base point** `[e₀]` of `CPⁿ`, the complex line spanned by the first standard basis
vector. -/
def basePoint : ComplexProjectiveSpace n :=
  mk n ⟨EuclideanSpace.single 0 1, by simp⟩

/-- **The unitary group acts transitively on `CPⁿ`**: every point is `[A e₀]` for some unitary
`A`, the matrix of an orthonormal basis extending a unit representative of the point. -/
instance instIsPretransitiveUnitaryGroup :
    MulAction.IsPretransitive (unitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) := by
  refine .of_orbit (x₀ := basePoint n) fun p ↦ ?_
  induction p using ComplexProjectiveSpace.inductionOn with
  | h x =>
    -- The unit vector `x` is an orthonormal frame of one vector, the image of the standard frame
    -- `e₀` under a unitary matrix.
    let f : finiteOrthonormalFrame ℂ 1 (n + 1) :=
      ⟨fun _ ↦ WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))), by
        rw [orthonormal_iff_ite]
        intro i j
        simp [Subsingleton.elim i j, inner_self_eq_norm_sq_to_K]⟩
    obtain ⟨A, hA⟩ := finiteOrthonormalFrame.unitaryMap_standard_surjective
      (𝕜 := ℂ) (Nat.le_add_left 1 n) f
    refine ⟨A, ?_⟩
    rw [basePoint, smul_mk]
    refine congrArg (mk n) (Subtype.ext ?_)
    have h := congrFun (congrArg Subtype.val hA) 0
    simp only [finiteOrthonormalFrame.coe_unitaryMap, finiteOrthonormalFrame.coe_standard, f] at h
    rw [LinearIsometryEquiv.coe_smul_unitSphere, UnitaryGroup.toLinearIsometryEquiv_apply]
    ext i
    simpa [mulVec, dotProduct, EuclideanSpace.single] using congrFun h i

/-- **The stabilizer of `[e₀]`**: a unitary matrix fixes the base point of `CPⁿ` exactly when its
column `0` vanishes below the corner, that is, when it maps `e₀` to a multiple of `e₀`. -/
theorem mem_stabilizer_basePoint_iff {A : unitaryGroup (Fin (n + 1)) ℂ} :
    A ∈ MulAction.stabilizer (unitaryGroup (Fin (n + 1)) ℂ) (basePoint n) ↔
      ∀ i : Fin n, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.succ 0 = 0 := by
  rw [MulAction.mem_stabilizer_iff, basePoint, smul_mk, mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩ i
    have h := congrArg (fun v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
      (v : EuclideanSpace ℂ (Fin (n + 1))) i.succ) hc
    simpa [mulVec, dotProduct, EuclideanSpace.single, Pi.single_apply, Fin.succ_ne_zero,
      eq_comm] using h
  · intro hA
    -- The image of `e₀` is its column `0`, the multiple `A₀₀ • e₀`, and `A₀₀` is a unit scalar.
    obtain ⟨⟨c, B⟩, hcB⟩ := UnitaryGroup.mem_range_prodBlockSucc_iff.2 hA
    refine ⟨⟨c, by simp⟩, Subtype.ext ?_⟩
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [← hcB, mulVec, dotProduct, EuclideanSpace.single, Pi.single_apply, Fin.succ_ne_zero]

/-- **The stabilizer of `[e₀]` is `U(1) × U(n)`**: it is the image of the block-diagonal
embedding `(c, B) ↦ diag(c, B)` of `U(1) × U(n)` in `U(n + 1)`. -/
theorem range_prodBlockSucc_eq_stabilizer :
    (UnitaryGroup.prodBlockSucc ℂ n).range =
      MulAction.stabilizer (unitaryGroup (Fin (n + 1)) ℂ) (basePoint n) := by
  ext A
  rw [UnitaryGroup.mem_range_prodBlockSucc_iff, mem_stabilizer_basePoint_iff]

/-- The orbit map `A ↦ A • [e₀]` of `U(n + 1)` on `CPⁿ` is continuous. -/
private theorem continuous_smul_basePoint :
    Continuous fun A : unitaryGroup (Fin (n + 1)) ℂ ↦ A • basePoint n :=
  continuous_id.smul continuous_const

variable (n) in
/-- **Complex projective space is the homogeneous space `U(n + 1) / (U(1) × U(n))`**: the orbit
map `A ↦ [A e₀]` induces a homeomorphism from the quotient of the unitary group `U(n + 1)` by the
block-diagonal subgroup `U(1) × U(n)` onto `CPⁿ`. -/
def unitaryQuotientHomeomorph :
    unitaryGroup (Fin (n + 1)) ℂ ⧸ (UnitaryGroup.prodBlockSucc ℂ n).range ≃ₜ
      ComplexProjectiveSpace n :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by rw [range_prodBlockSucc_eq_stabilizer]).trans
    (quotientStabilizerHomeomorph _ (basePoint n) continuous_smul_basePoint)

/-- The homeomorphism `U(n + 1) ⧸ (U(1) × U(n)) ≃ₜ CPⁿ` sends the coset of `A` to `A • [e₀]`. -/
@[simp]
theorem unitaryQuotientHomeomorph_mk (A : unitaryGroup (Fin (n + 1)) ℂ) :
    unitaryQuotientHomeomorph n (QuotientGroup.mk A) = A • basePoint n :=
  quotientStabilizerHomeomorph_mk _ (basePoint n) continuous_smul_basePoint A

/-- The homeomorphism `U(n + 1) ⧸ (U(1) × U(n)) ≃ₜ CPⁿ` is equivariant for the left actions of
`U(n + 1)`. -/
theorem unitaryQuotientHomeomorph_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (q : unitaryGroup (Fin (n + 1)) ℂ ⧸ (UnitaryGroup.prodBlockSucc ℂ n).range) :
    unitaryQuotientHomeomorph n (A • q) = A • unitaryQuotientHomeomorph n q := by
  induction q using QuotientGroup.induction_on with
  | H B => rw [MulAction.Quotient.smul_mk, unitaryQuotientHomeomorph_mk,
      unitaryQuotientHomeomorph_mk, smul_eq_mul, mul_smul]

end ComplexProjectiveSpace

end TauCeti
