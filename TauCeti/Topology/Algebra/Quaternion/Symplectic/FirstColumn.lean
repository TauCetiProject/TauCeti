/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.UnitaryMatrix
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.Topology.Algebra.Group.Quotient.LocalSection
public import TauCeti.Topology.Algebra.Matrix.CornerBlock
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Algebra.Quaternion.NormForm
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder
import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# The first-column fibration `Sp(n) → Sp(n + 1) → S^(4n + 3)`

The compact symplectic group `Sp(n + 1) = unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)` acts
continuously and transitively by isometries on the unit sphere `S^(4n + 3)` of the quaternionic
coordinate space `ℍⁿ⁺¹ = PiLp 2 (fun _ : Fin (n + 1) ↦ ℍ)`. Evaluating this action at the first
standard basis vector `e₀` gives the **first-column projection**
`TauCeti.quaternionUnitaryFirstColumn : Sp(n + 1) → S^(4n + 3)`, `A ↦ A e₀`.

The stabilizer of `e₀` consists of the quaternionic unitary matrices whose column `0` is `e₀`;
by `Matrix.mem_range_unitaryOneBlockSucc_iff`, this subgroup is the image of the block-diagonal
embedding `Matrix.unitaryOneBlockSucc ℍ n : Sp(n) →* Sp(n + 1)`, `B ↦ diag(1, B)`. Since
`Sp(n + 1)` is compact and `S^(4n + 3)` is Hausdorff, the orbit map induces an `Sp(n + 1)`-
equivariant homeomorphism
`Sp(n + 1) ⧸ (Matrix.unitaryOneBlockSucc ℍ n).range ≃ₜ S^(4n + 3)`
(`TauCeti.quaternionUnitarySphereQuotientHomeomorph`), while
`TauCeti.quaternionUnitaryFirstColumnFiberHomeomorph` identifies the fibre over `e₀` with `Sp(n)`.

To prove that `quaternionUnitaryFirstColumn` is locally trivial with fibre `Sp(n)` — and hence a
Serre fibration (`TauCeti.quaternionUnitaryFirstColumn_mem_serreFibrations`) — we construct an
explicit continuous local section over the open set `U = {x ∈ S^(4n + 3) | x₀ ≠ 0}` containing
`e₀`:
* for `x ∈ U`, the unit quaternion `u(x) = ‖x₀‖⁻¹ • star x₀` rotates `x` on the right to the unit
  vector `y(x) = x <• u(x)` whose `0`-th coordinate is the positive real number `‖x₀‖`;
* the vector `w(x) = e₀ + y(x)` has Hermitian square `w(x)ᴴ w(x) = 2 (1 + ‖x₀‖) ≥ 2`, so the
  quaternionic Householder reflection `H(x) = 1 - (2 / |w(x)|²) w(x) w(x)ᴴ` is non-singular on all
  of `U` and satisfies `H(x) e₀ = -y(x)`;
* multiplying on the right by the block-diagonal unitary matrix `diag(-star (u(x)), 1)` sends `e₀`
  to `(-y(x)) <• (-star (u(x))) = x`, depends continuously on `x ∈ U`, and evaluates to `1` at
  `e₀`.

Translating this section by the transitive action of `Sp(n + 1)` yields local product charts with
fibre `Sp(n)` around every point of `S^(4n + 3)`
(`TauCeti.exists_trivialization_quaternionUnitaryFirstColumn`).

## Main definitions

* `TauCeti.instMulActionUnitaryMatrixQuaternionSphere`: the isometric left action of
  `unitary (Matrix ι ι ℍ)` on the unit sphere of `PiLp 2 (fun _ : ι ↦ ℍ)`.
* `TauCeti.quaternionUnitaryFirstColumn`: the first-column projection
  `Sp(n + 1) → S^(4n + 3)`, `A ↦ A e₀`.
* `TauCeti.quaternionUnitarySphereQuotientHomeomorph`: the homogeneous-space homeomorphism
  `Sp(n + 1) ⧸ Sp(n) ≃ₜ S^(4n + 3)`.
* `TauCeti.quaternionUnitaryFirstColumnFiberHomeomorph`: the homeomorphism identifying `Sp(n)` with
  the fibre of `quaternionUnitaryFirstColumn` over `e₀`.

## Main results

* `TauCeti.exists_quaternionUnitaryFirstColumn_localSection`: existence of a normalized continuous
  local section of `quaternionUnitaryFirstColumn` on an open neighborhood of `e₀`.
* `TauCeti.exists_trivialization_quaternionUnitaryFirstColumn`: local trivializations of
  `quaternionUnitaryFirstColumn` with fibre `Sp(n)` around every point of `S^(4n + 3)`.
* `TauCeti.quaternionUnitaryFirstColumn_mem_serreFibrations`: the first-column projection
  `Sp(n + 1) → S^(4n + 3)` is a Serre fibration.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.4 and §7.6
  (coset spaces and sphere fibrations of the classical symplectic groups).
* C. Chevalley, *Theory of Lie Groups I*, Princeton University Press, 1946, Chapter I, §§VII–IX.
* The coset-bundle and Householder local-section layout parallels the complex Stiefel fibration in
  `TauCeti.Topology.Grassmannian.StiefelFibration.Unitary` and the homogeneous model of `ℍPⁿ` in
  `TauCeti.Topology.QuaternionicProjectiveSpace.Homogeneous`.
-/

public section

noncomputable section

open Metric MulOpposite Quaternion Set Topology
open scoped Matrix RightActions

namespace TauCeti

section SphereAction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A quaternionic unitary matrix acts on the unit sphere of `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)` by
left multiplication `A • x = A x`. -/
instance instSMulUnitaryMatrixQuaternionSphere :
    SMul (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) where
  smul A x := quaternionUnitaryIsometry ι A • x

theorem quaternionUnitary_smul_sphere_def (A : unitary (Matrix ι ι ℍ))
    (x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :
    A • x = quaternionUnitaryIsometry ι A • x :=
  (rfl)

@[simp]
theorem coe_quaternionUnitary_smul_sphere (A : unitary (Matrix ι ι ℍ))
    (x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :
    ((A • x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) : PiLp 2 fun _ : ι ↦ ℍ) =
      quaternionUnitaryIsometry ι A x :=
  LinearIsometryEquiv.coe_smul_unitSphere (quaternionUnitaryIsometry ι A) x

/-- The compact symplectic group acts on the unit sphere of `ℍⁿ`. -/
instance instMulActionUnitaryMatrixQuaternionSphere :
    MulAction (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) where
  one_smul x := by rw [quaternionUnitary_smul_sphere_def, map_one, one_smul]
  mul_smul A B x := by
    rw [quaternionUnitary_smul_sphere_def, quaternionUnitary_smul_sphere_def,
      quaternionUnitary_smul_sphere_def, map_mul, mul_smul]

/-- The compact symplectic group acts on the unit sphere of `ℍⁿ` by isometries. -/
instance instIsIsometricSMulUnitaryMatrixQuaternionSphere :
    IsIsometricSMul (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :=
  ⟨fun A ↦ isometry_smul _ (quaternionUnitaryIsometry ι A)⟩

/-- The action of the compact symplectic group on the unit sphere of `ℍⁿ` is jointly continuous. -/
instance instContinuousSMulUnitaryMatrixQuaternionSphere :
    ContinuousSMul (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) where
  continuous_smul := continuous_induced_rng.2 <|
    (continuous_quaternionUnitaryIsometry_apply.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).congr fun p ↦
        (coe_quaternionUnitary_smul_sphere p.1 p.2).symm

/-- The compact symplectic group `Sp(ι)` acts transitively on the unit sphere of `ℍⁿ` (vacuously
when `ι` is empty, since the unit sphere is then empty). -/
instance instIsPretransitiveUnitaryMatrixQuaternionSphere :
    MulAction.IsPretransitive (unitary (Matrix ι ι ℍ))
      (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · refine ⟨fun x ↦ False.elim ?_⟩
    have hx : (x : PiLp 2 fun _ : ι ↦ ℍ) = 0 := Subsingleton.elim _ _
    simpa [hx] using mem_sphere_zero_iff_norm.1 x.2
  · refine .of_orbit (x₀ := ⟨WithLp.toLp 2 (Pi.single i 1), by simp⟩) fun x ↦ ?_
    obtain ⟨A, hA⟩ := exists_quaternionUnitaryIsometry_apply_single_eq i
      (mem_sphere_zero_iff_norm.1 x.2)
    exact ⟨A, Subtype.ext ((coe_quaternionUnitary_smul_sphere A _).trans hA)⟩

end SphereAction

/-! ### The first-column projection, its fibres, and the homogeneous quotient -/

section Projection

variable {n : ℕ}

variable (n) in
/-- **The first-column projection `Sp(n + 1) → S^(4n + 3)`**, sending a quaternionic unitary matrix
`A` to `A e₀`, its column `0` viewed as a unit vector in `ℍⁿ⁺¹`. -/
def quaternionUnitaryFirstColumn
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 :=
  A • ⟨WithLp.toLp 2 (Pi.single 0 1), by simp⟩

@[simp]
theorem quaternionUnitaryFirstColumn_one :
    quaternionUnitaryFirstColumn n 1 = ⟨WithLp.toLp 2 (Pi.single 0 1), by simp⟩ :=
  one_smul _ _

theorem quaternionUnitaryFirstColumn_eq_smul_one
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    quaternionUnitaryFirstColumn n A = A • quaternionUnitaryFirstColumn n 1 := by
  rw [quaternionUnitaryFirstColumn_one]
  rfl

theorem quaternionUnitaryFirstColumn_mul
    (A B : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    quaternionUnitaryFirstColumn n (A * B) = A • quaternionUnitaryFirstColumn n B :=
  mul_smul A B _

@[simp]
theorem coe_quaternionUnitaryFirstColumn
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    (quaternionUnitaryFirstColumn n A : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) =
      WithLp.toLp 2 (A.1 *ᵥ Pi.single 0 1) := by
  simp [quaternionUnitaryFirstColumn]

variable (n) in
/-- The first-column projection `Sp(n + 1) → S^(4n + 3)` is continuous. -/
@[fun_prop]
theorem continuous_quaternionUnitaryFirstColumn :
    Continuous (quaternionUnitaryFirstColumn n) :=
  continuous_id.smul continuous_const

variable (n) in
/-- The first-column projection `Sp(n + 1) → S^(4n + 3)` is surjective: every unit vector of
`ℍⁿ⁺¹` is column `0` of some quaternionic unitary matrix. -/
theorem surjective_quaternionUnitaryFirstColumn :
    Function.Surjective (quaternionUnitaryFirstColumn n) := fun b ↦ by
  obtain ⟨A, hA⟩ := MulAction.exists_smul_eq
    (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) (quaternionUnitaryFirstColumn n 1) b
  exact ⟨A, (quaternionUnitaryFirstColumn_eq_smul_one A).trans hA⟩

@[simp]
theorem quaternionUnitaryFirstColumn_unitaryOneBlockSucc
    (B : unitary (Matrix (Fin n) (Fin n) ℍ)) :
    quaternionUnitaryFirstColumn n (Matrix.unitaryOneBlockSucc ℍ n B) =
      quaternionUnitaryFirstColumn n 1 :=
  Subtype.ext <| by
    rw [coe_quaternionUnitaryFirstColumn, Matrix.unitaryOneBlockSucc_mulVec_single_zero,
      quaternionUnitaryFirstColumn_one]

/-- A quaternionic unitary matrix maps `e₀` to `e₀` if and only if it belongs to the block-diagonal
subgroup `diag(1, Sp(n))`. -/
theorem quaternionUnitaryFirstColumn_eq_one_iff
    {A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)} :
    quaternionUnitaryFirstColumn n A = quaternionUnitaryFirstColumn n 1 ↔
      A ∈ (Matrix.unitaryOneBlockSucc ℍ n).range := by
  rw [Subtype.ext_iff, coe_quaternionUnitaryFirstColumn, quaternionUnitaryFirstColumn_one,
    Matrix.mem_range_unitaryOneBlockSucc_iff]
  exact ⟨congrArg WithLp.ofLp, congrArg (WithLp.toLp 2)⟩

/-- The fibres of `quaternionUnitaryFirstColumn` are the left cosets of the block-diagonal subgroup
`diag(1, Sp(n))`. -/
theorem quaternionUnitaryFirstColumn_eq_iff
    {A B : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)} :
    quaternionUnitaryFirstColumn n A = quaternionUnitaryFirstColumn n B ↔
      A⁻¹ * B ∈ (Matrix.unitaryOneBlockSucc ℍ n).range := by
  rw [← quaternionUnitaryFirstColumn_eq_one_iff, quaternionUnitaryFirstColumn_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h, quaternionUnitaryFirstColumn_eq_smul_one, inv_smul_smul]
  · rw [quaternionUnitaryFirstColumn_eq_smul_one, ← h, smul_inv_smul]

variable (n) in
/-- **The stabilizer of `e₀` in `Sp(n + 1)` is `Sp(n)`**: it equals the range of the block-diagonal
embedding `B ↦ diag(1, B)`. -/
theorem range_unitaryOneBlockSucc_eq_stabilizer :
    (Matrix.unitaryOneBlockSucc ℍ n).range =
      MulAction.stabilizer (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
        (quaternionUnitaryFirstColumn n 1) := by
  ext A
  rw [MulAction.mem_stabilizer_iff, ← quaternionUnitaryFirstColumn_eq_smul_one,
    quaternionUnitaryFirstColumn_eq_one_iff]

variable (n) in
/-- **The quaternionic sphere is the homogeneous space `Sp(n + 1) / Sp(n)`**: the first-column map
`A ↦ A e₀` induces a homeomorphism from the quotient of `Sp(n + 1)` by the block-diagonal subgroup
`Sp(n)` onto `S^(4n + 3)`. -/
def quaternionUnitarySphereQuotientHomeomorph :
    unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ⧸ (Matrix.unitaryOneBlockSucc ℍ n).range ≃ₜ
      sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 :=
  (Homeomorph.Quotient.congrRight fun _ _ ↦ by
      rw [range_unitaryOneBlockSucc_eq_stabilizer]).trans
    (quotientStabilizerHomeomorph _ (quaternionUnitaryFirstColumn n 1)
      (continuous_id.smul continuous_const))

@[simp]
theorem quaternionUnitarySphereQuotientHomeomorph_mk
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) :
    quaternionUnitarySphereQuotientHomeomorph n (QuotientGroup.mk A) =
      quaternionUnitaryFirstColumn n A :=
  (quotientStabilizerHomeomorph_mk _ (quaternionUnitaryFirstColumn n 1)
    (continuous_id.smul continuous_const) A).trans
    (quaternionUnitaryFirstColumn_eq_smul_one A).symm

/-- The homeomorphism `Sp(n + 1) ⧸ Sp(n) ≃ₜ S^(4n + 3)` is equivariant for the left actions of
`Sp(n + 1)`. -/
theorem quaternionUnitarySphereQuotientHomeomorph_smul
    (A : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))
    (q : unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) ⧸
      (Matrix.unitaryOneBlockSucc ℍ n).range) :
    quaternionUnitarySphereQuotientHomeomorph n (A • q) =
      A • quaternionUnitarySphereQuotientHomeomorph n q := by
  induction q using QuotientGroup.induction_on with
  | H B =>
    rw [MulAction.Quotient.smul_mk, quaternionUnitarySphereQuotientHomeomorph_mk,
      quaternionUnitarySphereQuotientHomeomorph_mk, smul_eq_mul, quaternionUnitaryFirstColumn_mul]

variable (n) in
/-- The first-column projection `Sp(n + 1) → S^(4n + 3)` is a topological quotient map. -/
theorem isQuotientMap_quaternionUnitaryFirstColumn :
    IsQuotientMap (quaternionUnitaryFirstColumn n) :=
  funext (quaternionUnitarySphereQuotientHomeomorph_mk (n := n)) ▸
    (quaternionUnitarySphereQuotientHomeomorph n).isQuotientMap.comp
      (QuotientGroup.isQuotientMap_mk _)

variable (n) in
/-- **The fibre of `quaternionUnitaryFirstColumn` over `e₀` is homeomorphic to `Sp(n)`** via the
block-diagonal embedding `B ↦ diag(1, B)`. -/
def quaternionUnitaryFirstColumnFiberHomeomorph :
    unitary (Matrix (Fin n) (Fin n) ℍ) ≃ₜ
      quaternionUnitaryFirstColumn n ⁻¹' {quaternionUnitaryFirstColumn n 1} :=
  (Matrix.unitaryOneBlockSuccEquivRange ℍ n).toHomeomorph.trans
    ((Homeomorph.refl _).subtype fun _ ↦ by
      rw [Set.mem_preimage, Set.mem_singleton_iff, quaternionUnitaryFirstColumn_eq_one_iff]
      rfl)

@[simp]
theorem coe_quaternionUnitaryFirstColumnFiberHomeomorph_apply
    (B : unitary (Matrix (Fin n) (Fin n) ℍ)) :
    (quaternionUnitaryFirstColumnFiberHomeomorph n B :
        unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) =
      Matrix.unitaryOneBlockSucc ℍ n B :=
  Matrix.coe_unitaryOneBlockSuccEquivRange_apply B

@[simp]
theorem unitaryOneBlockSucc_quaternionUnitaryFirstColumnFiberHomeomorph_symm_apply
    (A : quaternionUnitaryFirstColumn n ⁻¹' {quaternionUnitaryFirstColumn n 1}) :
    Matrix.unitaryOneBlockSucc ℍ n
      ((quaternionUnitaryFirstColumnFiberHomeomorph n).symm A) = A := by
  rw [← coe_quaternionUnitaryFirstColumnFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

end Projection

/-! ### Householder local section and local triviality -/

section LocalSection

variable {n : ℕ}

/-- The open domain `{x ∈ S^(4n + 3) | x₀ ≠ 0}` of the Householder local section around `e₀`. -/
private def firstColumnSectionDomain (n : ℕ) :
    Set (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
  {x | WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 0 ≠ 0}

private theorem isOpen_firstColumnSectionDomain (n : ℕ) :
    IsOpen (firstColumnSectionDomain n) :=
  isOpen_compl_singleton.preimage
    ((continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val))

private theorem one_mem_firstColumnSectionDomain (n : ℕ) :
    quaternionUnitaryFirstColumn n 1 ∈ firstColumnSectionDomain n := by
  simp [firstColumnSectionDomain]

private def firstColumnCoord0 (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) : ℍ :=
  WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 0

private theorem continuous_firstColumnCoord0 : Continuous (firstColumnCoord0 (n := n)) :=
  (continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)

private theorem firstColumnCoord0_one :
    firstColumnCoord0 (quaternionUnitaryFirstColumn n 1) = 1 := by
  simp [firstColumnCoord0]

/-- The unit quaternion `‖x₀‖⁻¹ • star x₀` rotating `x₀` to the positive real axis on
`firstColumnSectionDomain`. -/
private def firstColumnPhase (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) : ℍ :=
  (‖firstColumnCoord0 x‖⁻¹ : ℝ) • star (firstColumnCoord0 x)

private theorem continuousOn_firstColumnPhase :
    ContinuousOn (firstColumnPhase (n := n)) (firstColumnSectionDomain n) :=
  ((continuous_norm.comp continuous_firstColumnCoord0).continuousOn.inv₀
    fun _ hx ↦ norm_ne_zero_iff.2 hx).smul continuous_firstColumnCoord0.star.continuousOn

private theorem firstColumnPhase_one :
    firstColumnPhase (quaternionUnitaryFirstColumn n 1) = 1 := by
  rw [firstColumnPhase, firstColumnCoord0_one]
  simp

private theorem normSq_firstColumnPhase
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    normSq (firstColumnPhase x) = 1 := by
  have hn : ‖firstColumnCoord0 x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [firstColumnPhase, normSq_smul, normSq_star, normSq_eq_norm_mul_self]
  field_simp

private theorem firstColumnCoord0_mul_phase
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1} :
    firstColumnCoord0 x * firstColumnPhase x = ((‖firstColumnCoord0 x‖ : ℝ) : ℍ) := by
  by_cases hx : firstColumnCoord0 x = 0
  · simp [firstColumnPhase, hx]
  · have hn : ‖firstColumnCoord0 x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    rw [firstColumnPhase, mul_smul_comm, self_mul_star, normSq_eq_norm_mul_self]
    ext <;> simp; field_simp

private theorem neg_star_firstColumnPhase_mem_unitary
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    -star (firstColumnPhase x) ∈ unitary ℍ := by
  rw [mem_unitary_iff_normSq_eq_one, normSq_eq_norm_mul_self, norm_neg,
    ← normSq_eq_norm_mul_self, normSq_star]
  exact normSq_firstColumnPhase hx

/-- The phase-aligned unit vector `y(x) = x <• u(x)` whose `0`-th coordinate is `‖x₀‖`. -/
private def firstColumnAligned
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) : Fin (n + 1) → ℍ :=
  WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• firstColumnPhase x

private theorem firstColumnAligned_zero
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    firstColumnAligned x 0 = ((‖firstColumnCoord0 x‖ : ℝ) : ℍ) :=
  firstColumnCoord0_mul_phase

private theorem firstColumnAligned_one :
    firstColumnAligned (quaternionUnitaryFirstColumn n 1) = Pi.single 0 1 := by
  rw [firstColumnAligned, firstColumnPhase_one]
  funext i
  simp [Pi.single_apply]

private theorem star_dotProduct_firstColumnAligned
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    star (firstColumnAligned x) ⬝ᵥ firstColumnAligned x = 1 := by
  have hnu : ‖firstColumnPhase x‖ = 1 := by
    have h := normSq_firstColumnPhase hx
    rw [normSq_eq_norm_mul_self] at h
    nlinarith [norm_nonneg (firstColumnPhase x)]
  have hnorm : ‖(x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• firstColumnPhase x‖ = 1 := by
    rw [norm_smul, norm_op, hnu, mem_sphere_zero_iff_norm.1 x.2, mul_one]
  simpa [firstColumnAligned, hnorm] using
    star_dotProduct_self_ofLp ((x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) <• firstColumnPhase x)

/-- The Householder reflection vector `w(x) = e₀ + y(x)` and its Hermitian square
`s(x) = 2 (1 + ‖x₀‖) ≥ 2`. -/
private def firstColumnHouseholderVec
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) : Fin (n + 1) → ℍ :=
  Pi.single 0 1 + firstColumnAligned x

private def firstColumnScale
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) : ℝ :=
  2 * (1 + ‖firstColumnCoord0 x‖)

private theorem firstColumnScale_pos
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    0 < firstColumnScale x := by
  unfold firstColumnScale
  positivity

private theorem star_dotProduct_firstColumnHouseholderVec
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    star (firstColumnHouseholderVec x) ⬝ᵥ firstColumnHouseholderVec x =
      ((firstColumnScale x : ℝ) : ℍ) := by
  suffices (1 : ℍ) + ((‖firstColumnCoord0 x‖ : ℝ) : ℍ) + (((‖firstColumnCoord0 x‖ : ℝ) : ℍ) + 1) =
      ((firstColumnScale x : ℝ) : ℍ) by
    simpa [firstColumnHouseholderVec, add_dotProduct, dotProduct_add, firstColumnAligned_zero,
      star_dotProduct_firstColumnAligned hx]
  rw [firstColumnScale]
  ext <;> simp; ring

/-- The Householder reflection `H(x) = 1 - (2 / s(x)) w(x) w(x)ᴴ` sending `e₀` to `-y(x)`. -/
private def firstColumnHouseholder
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  1 - (2 / firstColumnScale x) •
    Matrix.vecMulVec (firstColumnHouseholderVec x) (star (firstColumnHouseholderVec x))

private theorem firstColumnHouseholder_mem_unitary
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    firstColumnHouseholder x ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) := by
  have hs : firstColumnScale x ≠ 0 := (firstColumnScale_pos x).ne'
  have hcs : 2 / firstColumnScale x * (2 / firstColumnScale x) * firstColumnScale x =
      2 * (2 / firstColumnScale x) := by field_simp
  refine Matrix.one_sub_smul_vecMulVec_mem_unitary ?_ hcs
  rw [star_dotProduct_firstColumnHouseholderVec hx, Quaternion.algebraMap_def]

private theorem firstColumnHouseholder_mulVec_single
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1} :
    firstColumnHouseholder x *ᵥ Pi.single 0 1 = -firstColumnAligned x := by
  have hw0 : star (firstColumnHouseholderVec x) ⬝ᵥ Pi.single 0 1 =
      ((1 + ‖firstColumnCoord0 x‖ : ℝ) : ℍ) := by
    simp [firstColumnHouseholderVec, dotProduct_single, firstColumnAligned_zero]
  have hop : op ((1 + ‖firstColumnCoord0 x‖ : ℝ) : ℍ) • firstColumnHouseholderVec x =
      (1 + ‖firstColumnCoord0 x‖) • firstColumnHouseholderVec x := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, op_smul_eq_mul, mul_coe_eq_smul]
  have hr : 1 + ‖firstColumnCoord0 x‖ ≠ 0 := by positivity
  have hcancel : 2 / firstColumnScale x * (1 + ‖firstColumnCoord0 x‖) = 1 := by
    unfold firstColumnScale
    field_simp
  rw [firstColumnHouseholder, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hw0, hop]
  simp [smul_smul, hcancel, firstColumnHouseholderVec]

private theorem continuousOn_firstColumnHouseholder :
    ContinuousOn (firstColumnHouseholder (n := n)) (firstColumnSectionDomain n) := by
  have hvec (i : Fin (n + 1)) :
      ContinuousOn (fun x ↦ firstColumnHouseholderVec (n := n) x i)
        (firstColumnSectionDomain n) :=
    continuousOn_const.add <|
      (((continuous_apply i).comp
        ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)).continuousOn).mul
        continuousOn_firstColumnPhase
  have hscale : Continuous (firstColumnScale (n := n)) :=
    continuous_const.mul (continuous_const.add (continuous_norm.comp continuous_firstColumnCoord0))
  have hc : Continuous fun x ↦ (2 : ℝ) / firstColumnScale (n := n) x :=
    continuous_const.div hscale fun x ↦ (firstColumnScale_pos x).ne'
  refine continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ ?_
  exact continuousOn_const.sub (hc.continuousOn.smul ((hvec i).mul (hvec j).star))

/-- The raw matrix local section `H(x) * diag(-star (u(x)), 1)` sending `e₀` to `x`. -/
private def firstColumnRawSection
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  firstColumnHouseholder x * Matrix.cornerBlockSucc (-star (firstColumnPhase x)) 1

private theorem firstColumnRawSection_mem_unitary
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    firstColumnRawSection x ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :=
  mul_mem (firstColumnHouseholder_mem_unitary hx)
    (Matrix.cornerBlockSucc_mem_unitary_iff.2
      ⟨neg_star_firstColumnPhase_mem_unitary hx, one_mem _⟩)

private theorem continuousOn_firstColumnRawSection :
    ContinuousOn (firstColumnRawSection (n := n)) (firstColumnSectionDomain n) :=
  continuousOn_firstColumnHouseholder.mul
    (continuousOn_firstColumnPhase.star.neg.matrix_cornerBlockSucc continuousOn_const)

private theorem firstColumnRawSection_mulVec_single
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    firstColumnRawSection x *ᵥ Pi.single 0 1 =
      WithLp.ofLp (x : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) := by
  have hD0 : Matrix.cornerBlockSucc (-star (firstColumnPhase x)) (1 : Matrix (Fin n) (Fin n) ℍ) *ᵥ
      Pi.single 0 1 = Pi.single 0 (1 : ℍ) <• (-star (firstColumnPhase x)) := by
    funext i
    rw [Matrix.mulVec_single_one, Pi.smul_apply, op_smul_eq_mul]
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hu : firstColumnPhase x * star (firstColumnPhase x) = 1 := by
    rw [self_mul_star, normSq_firstColumnPhase hx, coe_one]
  rw [firstColumnRawSection, ← Matrix.mulVec_mulVec, hD0, Matrix.mulVec_smul,
    firstColumnHouseholder_mulVec_single, firstColumnAligned]
  funext i
  simp [mul_assoc, hu]

private theorem firstColumnRawSection_one :
    firstColumnRawSection (quaternionUnitaryFirstColumn n 1) = 1 := by
  have hw : firstColumnHouseholderVec (quaternionUnitaryFirstColumn n 1) =
      Pi.single 0 ((2 : ℝ) : ℍ) := by
    rw [firstColumnHouseholderVec, firstColumnAligned_one]
    funext i
    by_cases hi : i = 0
    · subst hi; ext <;> simp; norm_num
    · simp [hi]
  have hs : firstColumnScale (quaternionUnitaryFirstColumn n 1) = 4 := by
    rw [firstColumnScale, firstColumnCoord0_one]
    norm_num
  have hH : firstColumnHouseholder (quaternionUnitaryFirstColumn n 1) =
      Matrix.cornerBlockSucc (-1) 1 := by
    rw [firstColumnHouseholder, hw, hs]
    refine Matrix.ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) fun i j ↦ ?_
    · ext <;> simp [Matrix.vecMulVec_apply]; norm_num
    · simp [Matrix.vecMulVec_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero j).symm]
    · simp [Matrix.vecMulVec_apply, Fin.succ_ne_zero]
    · simp [Matrix.vecMulVec_apply, Fin.succ_ne_zero, Matrix.one_apply]
  rw [firstColumnRawSection, hH, firstColumnPhase_one, star_one,
    Matrix.cornerBlockSucc_mul_cornerBlockSucc]
  simp [Matrix.cornerBlockSucc_one]

/-- The local section of `quaternionUnitaryFirstColumn` on `firstColumnSectionDomain`, extended by
`1` outside `firstColumnSectionDomain`. -/
private def firstColumnSection (n : ℕ)
    (x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :=
  letI := Classical.dec (x ∈ firstColumnSectionDomain n)
  if hx : x ∈ firstColumnSectionDomain n then
    ⟨firstColumnRawSection x, firstColumnRawSection_mem_unitary hx⟩
  else 1

private theorem coe_firstColumnSection
    {x : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1}
    (hx : x ∈ firstColumnSectionDomain n) :
    (firstColumnSection n x).1 = firstColumnRawSection x := by
  simp only [firstColumnSection, hx, ↓reduceDIte]

variable (n) in
/-- **Normalized continuous local section of `Sp(n + 1) → S^(4n + 3)`.** On the open neighborhood
`{x ∈ S^(4n + 3) | x₀ ≠ 0}` of `e₀`, there is a continuous map `s` into `Sp(n + 1)` with
`s e₀ = 1` and `s(x) e₀ = x`. -/
theorem exists_quaternionUnitaryFirstColumn_localSection :
    ∃ U : Set (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1),
      IsOpen U ∧ quaternionUnitaryFirstColumn n 1 ∈ U ∧
      ∃ s : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 →
          unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ),
        ContinuousOn s U ∧ s (quaternionUnitaryFirstColumn n 1) = 1 ∧
        ∀ x ∈ U, quaternionUnitaryFirstColumn n (s x) = x := by
  refine ⟨firstColumnSectionDomain n, isOpen_firstColumnSectionDomain n,
    one_mem_firstColumnSectionDomain n, firstColumnSection n, ?_, ?_, fun x hx ↦ ?_⟩
  · rw [IsInducing.subtypeVal.continuousOn_iff]
    exact continuousOn_firstColumnRawSection.congr fun _ hx ↦ coe_firstColumnSection hx
  · exact Subtype.ext ((coe_firstColumnSection (one_mem_firstColumnSectionDomain n)).trans
      firstColumnRawSection_one)
  · refine Subtype.ext ?_
    rw [coe_quaternionUnitaryFirstColumn, coe_firstColumnSection hx,
      firstColumnRawSection_mulVec_single hx, WithLp.toLp_ofLp]

/-- **Local triviality of the first-column projection**: around every point `b` of `S^(4n + 3)`,
`quaternionUnitaryFirstColumn n : Sp(n + 1) → S^(4n + 3)` admits a local trivialization with fibre
`Sp(n)`. -/
theorem exists_trivialization_quaternionUnitaryFirstColumn
    (b : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :
    ∃ e : Bundle.Trivialization (unitary (Matrix (Fin n) (Fin n) ℍ))
      (quaternionUnitaryFirstColumn n), b ∈ e.baseSet := by
  obtain ⟨g, rfl⟩ := surjective_quaternionUnitaryFirstColumn n b
  obtain ⟨U, hU, h1, s, hs, -, hsec⟩ := exists_quaternionUnitaryFirstColumn_localSection n
  let t : sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 →
      sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1 := fun x ↦ g⁻¹ • x
  have ht : Continuous t := continuous_const_smul g⁻¹
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (Matrix.unitaryOneBlockSucc ℍ n).range (continuous_quaternionUnitaryFirstColumn n)
    (fun _ _ ↦ quaternionUnitaryFirstColumn_eq_iff) (t ⁻¹' U) (hU.preimage ht)
    (fun x ↦ g * s (t x)) (continuousOn_const.mul (hs.comp ht.continuousOn fun _ hx ↦ hx))
    fun x hx ↦ by rw [quaternionUnitaryFirstColumn_mul, hsec _ hx, smul_inv_smul]
  refine ⟨e.transFiberHomeomorph (Matrix.unitaryOneBlockSuccEquivRange ℍ n).symm.toHomeomorph, ?_⟩
  simp only [Bundle.Trivialization.transFiberHomeomorph, e,
    Subgroup.localSectionTrivializationOfCosetFibers_baseSet, Set.mem_preimage, t]
  rwa [quaternionUnitaryFirstColumn_eq_smul_one, inv_smul_smul]

variable (n) in
/-- **The first-column projection `Sp(n + 1) → S^(4n + 3)` is a Serre fibration**: it is locally
trivial with fibre `Sp(n)`. -/
theorem quaternionUnitaryFirstColumn_mem_serreFibrations :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom
        ⟨quaternionUnitaryFirstColumn n, continuous_quaternionUnitaryFirstColumn n⟩ :
        _root_.TopCat.of (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) ⟶
          _root_.TopCat.of (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    exists_trivialization_quaternionUnitaryFirstColumn

end LocalSection

end TauCeti
