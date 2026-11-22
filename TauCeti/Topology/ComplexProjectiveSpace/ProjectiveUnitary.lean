/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
import Mathlib.LinearAlgebra.Center

/-!
# The projective unitary group acting on `CPⁿ`

The unitary group `U(n + 1)` acts on complex projective space `CPⁿ` by `A • [x] = [A x]`
(`TauCeti.ComplexProjectiveSpace.instMulActionUnitaryGroup`). A unitary matrix fixes every point
of `CPⁿ` exactly when it is a unit scalar `c • 1`
(`TauCeti.ComplexProjectiveSpace.forall_smul_eq_iff_mem_range_scalarHom`): if `A x` is a multiple
of `x` for every vector `x`, then `A` is a homothety
(`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`). So the kernel of the action is the
subgroup of unit scalars (`TauCeti.ComplexProjectiveSpace.ker_toPermHom_unitaryGroup`), and the
action descends to a faithful, transitive action of the projective unitary group

`PU(n + 1) = U(n + 1) ⧸ {c • 1 : |c| = 1}`

(`TauCeti.ProjectiveUnitaryGroup (Fin (n + 1)) ℂ`) on `CPⁿ`. This is the symmetry group of the
Fubini–Study metric, which unitary matrices preserve
(`LinearIsometry.fubiniStudyHermitian_map_map_map`) and on which `PU(n + 1)` acts without kernel.

In `U(n + 1)` the stabilizer of the base point `[e₀]` is the block-diagonal subgroup
`U(1) × U(n)` of the matrices `diag(c, B)`
(`TauCeti.ComplexProjectiveSpace.range_prodBlockSucc_eq_stabilizer`). In `PU(n + 1)` the class of
`diag(c, B)` is also the class of `diag(1, star c • B)`
(`TauCeti.ProjectiveUnitaryGroup.mk_prodBlockSucc`), and the stabilizer of `[e₀]` is
isomorphic to `U(n)` (`TauCeti.ComplexProjectiveSpace.stabilizerBasePointEquiv`), the class of
`diag(c, B)` corresponding to `star c • B`. This matches the description of `U(1) × U(n)` modulo
its diagonal circle (`Matrix.UnitaryGroup.prodQuotientDiagonalEquiv`).

For `n = 0`, `CP⁰` is a point, the whole of `U(1)` is the scalar kernel and `PU(1)` is trivial
(`TauCeti.ProjectiveUnitaryGroup.instSubsingletonFinOne`).

## Main declarations

* `TauCeti.ComplexProjectiveSpace.forall_smul_eq_iff_mem_range_scalarHom`,
  `TauCeti.ComplexProjectiveSpace.ker_toPermHom_unitaryGroup`: the kernel of the action of
  `U(n + 1)` is the subgroup of unit scalars.
* `TauCeti.ComplexProjectiveSpace.instMulActionProjectiveUnitaryGroup`: the action of
  `PU(n + 1)` on `CPⁿ`, with `TauCeti.ComplexProjectiveSpace.mk_smul_projectiveUnitaryGroup`.
* `TauCeti.ComplexProjectiveSpace.instFaithfulSMulProjectiveUnitaryGroup`,
  `TauCeti.ComplexProjectiveSpace.instIsPretransitiveProjectiveUnitaryGroup`: it is faithful and
  transitive.
* `TauCeti.ComplexProjectiveSpace.stabilizerBasePointEquiv`: the stabilizer of `[e₀]` in
  `PU(n + 1)` is isomorphic to `U(n)`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
* W. Ballmann, *Lectures on Kähler Manifolds*, ESI Lectures in Mathematics and Physics, 2006, §4,
  Example 5.
-/

public section

noncomputable section

open Matrix Metric

namespace TauCeti

namespace ComplexProjectiveSpace

variable {n : ℕ}

/-- A unit scalar `c • 1` fixes every point of `CPⁿ`. -/
@[simp]
theorem scalarHom_smul (c : unitary ℂ) (p : ComplexProjectiveSpace n) :
    UnitaryGroup.scalarHom (Fin (n + 1)) ℂ c • p = p := by
  induction p using ComplexProjectiveSpace.inductionOn with
  | h x =>
    rw [smul_mk, mk_eq_mk_iff]
    refine ⟨⟨c, by simp [CStarRing.norm_of_mem_unitary c.property]⟩, Subtype.ext ?_⟩
    ext i
    simp [scalar_apply]

/-- A unitary matrix fixing every point of `CPⁿ` maps every vector to a multiple of itself. -/
private theorem exists_toLinearIsometryEquiv_apply_eq_smul {A : unitaryGroup (Fin (n + 1)) ℂ}
    (hA : ∀ p : ComplexProjectiveSpace n, A • p = p) (v : EuclideanSpace ℂ (Fin (n + 1))) :
    ∃ c : ℂ, UnitaryGroup.toLinearIsometryEquiv A v = c • v := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨0, by simp⟩
  -- Apply `hA` to the line of the unit vector `‖v‖⁻¹ • v`.
  have hr : ((‖v‖⁻¹ : ℝ) : ℂ) ≠ 0 := by simpa using hv
  let x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
    ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, by simpa using norm_smul_inv_norm (𝕜 := ℂ) hv⟩
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff n _ _).1 (smul_mk A x ▸ hA (mk n x))
  refine ⟨c, smul_right_injective _ hr ?_⟩
  have h := congrArg Subtype.val hc
  rw [Sphere.coe_sphere_smul, LinearIsometryEquiv.coe_smul_unitSphere] at h
  simp only [x, map_smul] at h
  dsimp only
  rw [← h, smul_comm]

/-- **The kernel of the unitary action on `CPⁿ`**: a unitary matrix fixes every point of `CPⁿ`
exactly when it is a unit scalar `c • 1`. -/
theorem forall_smul_eq_iff_mem_range_scalarHom {A : unitaryGroup (Fin (n + 1)) ℂ} :
    (∀ p : ComplexProjectiveSpace n, A • p = p) ↔
      A ∈ (UnitaryGroup.scalarHom (Fin (n + 1)) ℂ).range := by
  refine ⟨fun hA ↦ ?_, by rintro ⟨c, rfl⟩; exact scalarHom_smul c⟩
  -- The linear map of `A` sends every vector to a multiple of itself, so it is a homothety.
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := (UnitaryGroup.toLinearIsometryEquiv A).toLinearEquiv.toLinearMap) fun v hli ↦ by
      obtain ⟨c, hc⟩ := exists_toLinearIsometryEquiv_apply_eq_smul hA v
      have h := (LinearIndependent.pair_iff.1 hli) c (-1)
        (by simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, hc]; simp)
      exact neg_ne_zero.2 one_ne_zero h.2
  have hAa : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = scalar (Fin (n + 1)) a := by
    ext i j
    have h := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) ↦ v i)
      (LinearMap.congr_fun ha (EuclideanSpace.single j 1))
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      UnitaryGroup.toLinearIsometryEquiv_single] at h
    simpa [scalar_apply, diagonal_apply, Pi.single_apply, eq_comm] using h
  -- The scalar `a` is unitary because `A` is.
  have hau : a ∈ unitary ℂ := by
    have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 A.property) 0) 0
    rw [hAa] at h
    simpa [scalar_apply, star_eq_conjTranspose, Unitary.mem_iff_star_mul_self] using h
  exact ⟨⟨a, hau⟩, Subtype.ext (by rw [UnitaryGroup.coe_scalarHom]; exact hAa.symm)⟩

/-- The kernel of the action of `U(n + 1)` on `CPⁿ` is the subgroup of unit scalars. -/
theorem ker_toPermHom_unitaryGroup :
    (MulAction.toPermHom (unitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n)).ker =
      (UnitaryGroup.scalarHom (Fin (n + 1)) ℂ).range := by
  ext A
  simp only [MonoidHom.mem_ker, Equiv.Perm.ext_iff, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  exact forall_smul_eq_iff_mem_range_scalarHom

/-! ### The action of `PU(n + 1)` -/

/-- **The projective unitary group `PU(n + 1)` acts on `CPⁿ`**, through the action
`A • [x] = [A x]` of representatives `A ∈ U(n + 1)`. -/
instance instMulActionProjectiveUnitaryGroup :
    MulAction (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) :=
  MulAction.compHom _ <|
    QuotientGroup.lift _ (MulAction.toPermHom _ _) ker_toPermHom_unitaryGroup.ge

/-- The class of a unitary matrix acts on `CPⁿ` as the matrix does. -/
@[simp]
theorem mk_smul_projectiveUnitaryGroup (A : unitaryGroup (Fin (n + 1)) ℂ)
    (p : ComplexProjectiveSpace n) :
    (A : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) • p = A • p :=
  (rfl)

/-- **`PU(n + 1)` acts faithfully on `CPⁿ`**: only the identity fixes every point. -/
instance instFaithfulSMulProjectiveUnitaryGroup :
    FaithfulSMul (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) (ComplexProjectiveSpace n) where
  eq_of_smul_eq_smul {g h} hgh := by
    induction g using QuotientGroup.induction_on with | H A =>
    induction h using QuotientGroup.induction_on with | H B =>
    rw [QuotientGroup.eq]
    refine forall_smul_eq_iff_mem_range_scalarHom.1 fun p ↦ ?_
    rw [mul_smul, inv_smul_eq_iff, ← mk_smul_projectiveUnitaryGroup,
      ← mk_smul_projectiveUnitaryGroup, hgh]

/-- **`PU(n + 1)` acts transitively on `CPⁿ`.** -/
instance instIsPretransitiveProjectiveUnitaryGroup :
    MulAction.IsPretransitive (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ)
      (ComplexProjectiveSpace n) where
  exists_smul_eq p q := by
    obtain ⟨A, hA⟩ := MulAction.exists_smul_eq (unitaryGroup (Fin (n + 1)) ℂ) p q
    exact ⟨A, by rw [mk_smul_projectiveUnitaryGroup, hA]⟩

/-! ### The stabilizer of the base point in `PU(n + 1)` -/

/-- The morphism `U(n) →* PU(n + 1)` stabilizing `[e₀]`, `B ↦ [diag(1, B)]`. -/
private def unitaryToStabilizerBasePoint :
    unitaryGroup (Fin n) ℂ →*
      MulAction.stabilizer (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) (basePoint n) :=
  (((QuotientGroup.mk' _).comp ((UnitaryGroup.prodBlockSucc ℂ n).comp
    (MonoidHom.inr _ _)))).codRestrict _ fun B ↦ by
      rw [MulAction.mem_stabilizer_iff]
      exact (range_prodBlockSucc_eq_stabilizer (n := n)).le ⟨(1, B), rfl⟩

private theorem coe_unitaryToStabilizerBasePoint (B : unitaryGroup (Fin n) ℂ) :
    (unitaryToStabilizerBasePoint B : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) =
      (UnitaryGroup.prodBlockSucc ℂ n (1, B) : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) :=
  (rfl)

private theorem bijective_unitaryToStabilizerBasePoint :
    Function.Bijective (unitaryToStabilizerBasePoint (n := n)) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun B hB ↦ ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · -- If `diag(1, B)` is a unit scalar, its corner forces that scalar to be `1`.
    have h := congrArg Subtype.val hB
    rw [coe_unitaryToStabilizerBasePoint, OneMemClass.coe_one, QuotientGroup.eq_one_iff] at h
    obtain ⟨c, hc⟩ := h
    obtain rfl : c = 1 := Subtype.ext <| by
      simpa [scalar_apply] using congrFun (congrFun (congrArg Subtype.val hc) 0) 0
    rw [map_one, ← map_one (UnitaryGroup.prodBlockSucc ℂ n)] at hc
    exact (congrArg Prod.snd (UnitaryGroup.prodBlockSucc_injective hc)).symm
  · -- A stabilizing class is represented by some `diag(c, B)`, of class `[diag(1, star c • B)]`.
    induction g using QuotientGroup.induction_on with | H A =>
    rw [MulAction.mem_stabilizer_iff, mk_smul_projectiveUnitaryGroup,
      ← MulAction.mem_stabilizer_iff, ← range_prodBlockSucc_eq_stabilizer] at hg
    obtain ⟨cB, rfl⟩ := hg
    exact ⟨UnitaryGroup.starSMulHom (Fin n) ℂ cB,
      Subtype.ext (ProjectiveUnitaryGroup.mk_prodBlockSucc cB).symm⟩

variable (n) in
/-- **The stabilizer of `[e₀]` in `PU(n + 1)` is `U(n)`**: the class of `diag(c, B)` corresponds to
`star c • B`, and `B` to the class of `diag(1, B)`. -/
def stabilizerBasePointEquiv :
    MulAction.stabilizer (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) (basePoint n) ≃*
      unitaryGroup (Fin n) ℂ :=
  (MulEquiv.ofBijective _ bijective_unitaryToStabilizerBasePoint).symm

/-- The isomorphism of the stabilizer of `[e₀]` in `PU(n + 1)` with `U(n)` sends `B` back to the
class of `diag(1, B)`. -/
@[simp]
theorem coe_stabilizerBasePointEquiv_symm (B : unitaryGroup (Fin n) ℂ) :
    ((stabilizerBasePointEquiv n).symm B : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) =
      (UnitaryGroup.prodBlockSucc ℂ n (1, B) : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) :=
  (rfl)

/-- The isomorphism of the stabilizer of `[e₀]` in `PU(n + 1)` with `U(n)` sends the class of
`diag(c, B)` to `star c • B`. -/
theorem stabilizerBasePointEquiv_mk_prodBlockSucc (cB : unitary ℂ × unitaryGroup (Fin n) ℂ)
    (h : (UnitaryGroup.prodBlockSucc ℂ n cB : ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) ∈
      MulAction.stabilizer (ProjectiveUnitaryGroup (Fin (n + 1)) ℂ) (basePoint n)) :
    stabilizerBasePointEquiv n ⟨_, h⟩ = UnitaryGroup.starSMulHom (Fin n) ℂ cB := by
  rw [← MulEquiv.eq_symm_apply]
  exact Subtype.ext (ProjectiveUnitaryGroup.mk_prodBlockSucc cB)

end ComplexProjectiveSpace

end TauCeti
