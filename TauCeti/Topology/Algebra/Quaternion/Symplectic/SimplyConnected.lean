/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
public import TauCeti.Topology.Algebra.Quaternion.Symplectic.FirstColumn
public import TauCeti.Topology.Algebra.Quaternion.Unitary
public import TauCeti.Topology.Homotopy.SerreFibration.Connected
public import TauCeti.Topology.Homotopy.SerreFibration.TotalSpace

/-!
# Connectivity and homotopy stability of the compact symplectic groups

The first-column projection `Sp(n + 1) → S^(4n + 3)` is locally trivial with fibre `Sp(n)`
(`TauCeti.exists_trivialization_quaternionUnitaryFirstColumn`), and hence a Serre fibration
(`TauCeti.quaternionUnitaryFirstColumn_mem_serreFibrations`). Every base sphere `S^(4n + 3)`
(`n ≥ 0`) has real dimension at least `3`, so it is simply connected
(`TauCeti.simplyConnectedSpace_sphere_piLp_quaternion`) and `2`-connected
(`TauCeti.subsingleton_homotopyGroup_sphere_piLp_quaternion`).

Starting from the one-point group `Sp(0)`, induction along the fibration tower
`Sp(0) → Sp(1) → Sp(2) → ⋯` shows that the compact symplectic group
`Sp(ι) = unitary (Matrix ι ι ℍ)` is simply connected — and hence path-connected and connected — for
every finite index type `ι` (`TauCeti.instSimplyConnectedSpaceUnitaryMatrixQuaternion`), and in
fact `2`-connected (`TauCeti.subsingleton_homotopyGroup_unitary_matrix_quaternion`). In rank one,
reading off the unique matrix entry identifies `Sp(1)` with the unit Hamilton quaternions `S³` and
with `SU(2)` (`TauCeti.unitaryMatrixQuaternionUniqueHomeomorphSphere`,
`TauCeti.unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup`).

Furthermore, since `S^(4n + 3)` is `(4n + 2)`-connected, the long exact homotopy sequence of the
first-column fibration implies that the block-diagonal embedding `Sp(n) → Sp(n + 1)`,
`B ↦ diag(1, B)`, is `(4n + 2)`-connected (`TauCeti.isNConnected_unitaryOneBlockSucc_quaternion`):
it induces bijections on `π_k` for `k < 4n + 2` and a surjection for `k = 4n + 2`.

## Main definitions

* `TauCeti.unitaryMatrixQuaternionUniqueHomeomorphSphere`: for a singleton index type `ι`, the
  homeomorphism `unitary (Matrix ι ι ℍ) ≃ₜ sphere (0 : ℍ) 1`.
* `TauCeti.unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup`: for a singleton
  index type `ι`, the topological group isomorphism
  `unitary (Matrix ι ι ℍ) ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ`.

## Main results

* `TauCeti.instSimplyConnectedSpaceUnitaryMatrixQuaternion`: `unitary (Matrix ι ι ℍ)` is simply
  connected (and hence path-connected and connected) for every finite index type `ι`.
* `TauCeti.subsingleton_homotopyGroup_unitary_matrix_quaternion`: `unitary (Matrix ι ι ℍ)` is
  `2`-connected (`π_N(Sp(ι), A)` is trivial whenever `Nat.card N ≤ 2`).
* `TauCeti.isNConnected_unitaryOneBlockSucc_quaternion`: the block-diagonal embedding
  `Sp(n) → Sp(n + 1)` is `(4n + 2)`-connected.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.6 and §25.4.
* C. Chevalley, *Theory of Lie Groups I*, Princeton University Press, 1946, Chapter II, §VIII,
  Theorem 5.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, Theorem 4.41 and
  Example 4.55.
* The fibre-inclusion stability argument follows
  `TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne` in
  `TauCeti.Topology.Grassmannian.StiefelFibration.Stability`.
-/

public section

noncomputable section

open Metric CategoryTheory
open scoped Quaternion Topology Topology.Homotopy

namespace TauCeti

section RankOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

variable (ι) in
/-- **Rank-one symplectic group and the `3`-sphere**: on a singleton index type `ι`, reading off the
unique entry identifies `Sp(1) = unitary (Matrix ι ι ℍ)` homeomorphically with the unit quaternion
sphere `S³ ⊆ ℍ`. -/
def unitaryMatrixQuaternionUniqueHomeomorphSphere :
    unitary (Matrix ι ι ℍ) ≃ₜ sphere (0 : ℍ) 1 :=
  (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).toHomeomorph.trans
    Quaternion.unitaryHomeomorphSphere

@[simp]
theorem coe_unitaryMatrixQuaternionUniqueHomeomorphSphere_apply
    (A : unitary (Matrix ι ι ℍ)) :
    (unitaryMatrixQuaternionUniqueHomeomorphSphere ι A : ℍ) = A.1 default default := by
  rw [unitaryMatrixQuaternionUniqueHomeomorphSphere, Homeomorph.trans_apply,
    Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact Matrix.coe_unitaryUniqueContinuousMulEquiv_apply A

@[simp]
theorem coe_unitaryMatrixQuaternionUniqueHomeomorphSphere_symm_apply
    (q : sphere (0 : ℍ) 1) :
    ((unitaryMatrixQuaternionUniqueHomeomorphSphere ι).symm q).1 =
      Matrix.of fun _ _ ↦ (q : ℍ) := by
  rw [unitaryMatrixQuaternionUniqueHomeomorphSphere, Homeomorph.symm_trans_apply,
    ContinuousMulEquiv.toHomeomorph_eq_coe, ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact (Matrix.coe_unitaryUniqueContinuousMulEquiv_symm_apply _).trans (by simp)

variable (ι) in
/-- **Rank-one symplectic group and `SU(2)`**: on a singleton index type `ι`, `Sp(1)` is isomorphic
as a topological group to `Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
def unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup :
    unitary (Matrix ι ι ℍ) ≃ₜ* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).trans
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup

@[simp]
theorem unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup_apply
    (A : unitary (Matrix ι ι ℍ)) :
    unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup ι A =
      Quaternion.unitaryEquivSpecialUnitaryGroup
        (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ A) := by
  simp [unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup]

@[simp]
theorem unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup_symm_apply
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup ι).symm g =
      (Matrix.unitaryUniqueContinuousMulEquiv ι ℍ).symm
        (Quaternion.unitaryEquivSpecialUnitaryGroup.symm g) := by
  simp [unitaryMatrixQuaternionUniqueContinuousMulEquivSpecialUnitaryGroup]

end RankOne

section Connectivity

private theorem simplyConnectedSpace_unitary_matrix_fin_quaternion :
    ∀ n : ℕ, SimplyConnectedSpace (unitary (Matrix (Fin n) (Fin n) ℍ))
  | 0 => inferInstance
  | n + 1 =>
    let _ := simplyConnectedSpace_unitary_matrix_fin_quaternion n
    let _ := simplyConnectedSpace_sphere_piLp_quaternion (p := 2) (ι := Fin (n + 1))
    simplyConnectedSpace_of_exists_trivialization
      exists_trivialization_quaternionUnitaryFirstColumn

/-- **The compact symplectic group `Sp(ι)` is simply connected** (and therefore path-connected and
connected) for every finite index type `ι`. -/
instance instSimplyConnectedSpaceUnitaryMatrixQuaternion
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    SimplyConnectedSpace (unitary (Matrix ι ι ℍ)) :=
  let _ := simplyConnectedSpace_unitary_matrix_fin_quaternion (Fintype.card ι)
  (Matrix.unitaryReindexContinuousMulEquiv ℍ
    (Fintype.equivFin ι)).toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

private theorem subsingleton_homotopyGroup_fin_unitary_matrix_fin_quaternion :
    ∀ (n k : ℕ), k ≤ 2 → ∀ A : unitary (Matrix (Fin n) (Fin n) ℍ),
      Subsingleton (π_ k (unitary (Matrix (Fin n) (Fin n) ℍ)) A)
  | 0, _, _, _ => inferInstance
  | n + 1, k, hk, A =>
    forall_subsingleton_homotopyGroup_of_exists_trivialization (n := 2)
      exists_trivialization_quaternionUnitaryFirstColumn
      (quaternionUnitaryFirstColumn n 1)
      (fun m hm ↦ subsingleton_homotopyGroup_sphere_piLp_quaternion (by simp; omega) _)
      (fun m hm ↦ subsingleton_homotopyGroup_fin_unitary_matrix_fin_quaternion n m hm)
      k hk A

/-- **The compact symplectic group `Sp(ι)` is `2`-connected**: its homotopy set `π_N(Sp(ι), A)` is
trivial whenever `Nat.card N ≤ 2` (in particular `π₀`, `π₁`, and `π₂` vanish at every basepoint). -/
theorem subsingleton_homotopyGroup_unitary_matrix_quaternion
    {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Type*} (hN : Nat.card N ≤ 2)
    (A : unitary (Matrix ι ι ℍ)) :
    Subsingleton (HomotopyGroup N (unitary (Matrix ι ι ℍ)) A) := by
  by_cases hfin : Finite N
  swap
  · have := not_finite_iff_infinite.1 hfin
    infer_instance
  have := Fintype.ofFinite N
  let e := (Matrix.unitaryReindexContinuousMulEquiv ℍ (Fintype.equivFin ι)).toHomeomorph
  have hcard : Fintype.card N ≤ 2 := by simpa using hN
  have := subsingleton_homotopyGroup_fin_unitary_matrix_fin_quaternion
    (Fintype.card ι) (Fintype.card N) hcard (e A)
  have := (HomotopyGroup.congrEquiv (X := unitary (Matrix (Fin (Fintype.card ι))
    (Fin (Fintype.card ι)) ℍ)) (x := e A) (Fintype.equivFin N)).subsingleton
  exact (HomotopyGroup.homeomorphEquiv (N := N) e A).subsingleton

/-- **Homotopy stability of the compact symplectic groups.** The block-diagonal embedding
`Sp(n) → Sp(n + 1)`, `B ↦ diag(1, B)`, is `(4n + 2)`-connected: it induces bijections on `π_k` for
`k < 4n + 2` and a surjection for `k = 4n + 2`. -/
theorem isNConnected_unitaryOneBlockSucc_quaternion (n : ℕ) :
    (⟨Matrix.unitaryOneBlockSucc ℍ n, Matrix.continuous_unitaryOneBlockSucc⟩ :
      C(unitary (Matrix (Fin n) (Fin n) ℍ),
        unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ))).IsNConnected (4 * n + 2) := by
  let p : _root_.TopCat.of (unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)) ⟶
      _root_.TopCat.of (sphere (0 : PiLp 2 fun _ : Fin (n + 1) ↦ ℍ) 1) :=
    _root_.TopCat.ofHom
      ⟨quaternionUnitaryFirstColumn n, continuous_quaternionUnitaryFirstColumn n⟩
  have hfib : (p.fiberι (quaternionUnitaryFirstColumn n 1)).hom.IsNConnected (4 * n + 2) :=
    TopCat.isNConnected_fiberι_of_mem_serreFibrations
      (quaternionUnitaryFirstColumn_mem_serreFibrations n) fun k hk ↦
        subsingleton_homotopyGroup_sphere_piLp_quaternion (by simp; omega) _
  let φ := quaternionUnitaryFirstColumnFiberHomeomorph n
  convert hfib.comp (φ.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected (4 * n + 2))
    using 1
  ext B : 1
  exact (coe_quaternionUnitaryFirstColumnFiberHomeomorph_apply B).symm.trans
    (TopCat.Hom.fiberι_apply p _ (φ B)).symm

end Connectivity

end TauCeti
