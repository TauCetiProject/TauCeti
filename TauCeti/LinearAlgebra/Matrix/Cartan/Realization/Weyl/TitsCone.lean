/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter
public import TauCeti.GroupTheory.Coxeter.Parabolic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.Geometry.Convex.Cone.Face.Simplicial

/-!
# The fundamental domain of a Cartan realization

The Tits cone is the Weyl saturation of the dominant chamber. Each orbit in it meets
the chamber in a unique weight. The stabilizer of that weight is the standard parabolic
subgroup on the simple coroots where it vanishes, so its orbit identifies with the
corresponding parabolic quotient.

Along a length-increasing step `v → v sᵢ`, the difference between the two images of a
weight `λ` is `v(λ) - v sᵢ(λ) = λ(hᵢ) • v(αᵢ)`. The right-descent criterion puts `v(αᵢ)`
in the positive root monoid. This also gives the root-order bound on dominant integral Weyl orbits.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Proposition 3.12(a).
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]

section TitsCone

variable {B : Matrix I I K} (R : CartanRealization B H)

/-- The closed dominant chamber consists of the weights nonnegative on all simple coroots. -/
def dominantChamber [LE K] : Set (Dual K H) := {lam | R.IsDominant lam}

/-- The dominant chamber as a set of dominant weights. -/
theorem dominantChamber_def [LE K] :
    R.dominantChamber = {lam | R.IsDominant lam} := (rfl)

/-- Chamber membership is dominance on the simple coroots. -/
@[simp]
theorem mem_dominantChamber [LE K] {lam : Dual K H} :
    lam ∈ R.dominantChamber ↔ R.IsDominant lam := Iff.rfl

variable [LE K] (hA : ∀ i, B i i = 2)

/-- The Tits cone consists of the weights that some Weyl group element sends into
the dominant chamber. -/
def titsCone : Set (Dual K H) := {lam | ∃ w : R.weylGroup hA, R.IsDominant (w • lam)}

/-- The Tits cone as the set of weights admitting a dominant Weyl translate. -/
theorem titsCone_def :
    R.titsCone hA = {lam | ∃ w : R.weylGroup hA, R.IsDominant (w • lam)} := (rfl)

/-- A weight belongs to the Tits cone exactly when its orbit contains a dominant weight. -/
theorem mem_titsCone_iff {lam : Dual K H} :
    lam ∈ R.titsCone hA ↔ ∃ w : R.weylGroup hA, R.IsDominant (w • lam) := Iff.rfl

/-- The Tits cone is the union of the Weyl translates of the closed dominant chamber. -/
theorem titsCone_eq_iUnion :
    R.titsCone hA = ⋃ w : R.weylGroup hA, (w • ·) '' R.dominantChamber := by
  simp only [titsCone_def, Set.image_smul, Set.iUnion_smul_eq_ofPred_exists, mem_dominantChamber]

/-- Every dominant weight belongs to the Tits cone. -/
theorem dominantChamber_subset_titsCone : R.dominantChamber ⊆ R.titsCone hA :=
  fun _ h ↦ (R.mem_titsCone_iff hA).mpr ⟨1, by simpa using h⟩

/-- The Tits cone is stable under the Weyl group. -/
@[simp]
theorem smul_mem_titsCone_iff (w : R.weylGroup hA) {lam : Dual K H} :
    w • lam ∈ R.titsCone hA ↔ lam ∈ R.titsCone hA := by
  simp only [mem_titsCone_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v * w, by simpa only [mul_smul] using hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v * w⁻¹, by simpa only [mul_smul, inv_smul_smul] using hv⟩

end TitsCone

variable {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
  (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)

local notation "W" => R.weylGroup (diag_map_intCast hdiag)

section RootOrder

variable [CharZero K]

private theorem exists_mul_simple_of_ne_one [DecidableEq I] {w : W} (hw : w ≠ 1) :
    let cs := R.weylCoxeterSystem hdiag hoff hzero
    ∃ (v : W) (i : I), cs.length v < cs.length w ∧ v * cs.simple i = w ∧
      v • R.root i ∈ R.posRootCone := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
  refine ⟨w * cs.simple i, i, hi, cs.simple_mul_simple_cancel_right i, ?_⟩
  exact (R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero _ i).mp
    (cs.isRightDescent_iff_not_isRightDescent_mul.mp hi)

include hoff hzero in
/-- Sum the changes across length-increasing right multiplication steps. -/
private theorem sub_smul_mem_of_step (w : W) (lam : Dual K H) (S : AddSubmonoid (Dual K H))
    (hstep : ∀ β ∈ R.posRootCone, ∀ i, lam (R.coroot i) • β ∈ S) :
    lam - w • lam ∈ S := by
  classical
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  induction hn : cs.length w using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases hw : w = 1
    · simp [hw]
    obtain ⟨v, i, hv, hvi, hβ⟩ := R.exists_mul_simple_of_ne_one hdiag hoff hzero hw
    have hdiff : v • lam - w • lam = lam (R.coroot i) • (v • R.root i) := by
      simpa only [← R.weylCoxeterSystem_simple hdiag hoff hzero, hvi] using
        R.smul_sub_mul_weylSimple_smul (diag_map_intCast hdiag) v i lam
    rw [← sub_add_sub_cancel lam (v • lam) (w • lam), hdiff]
    exact add_mem (ih _ (hn ▸ hv) v rfl) (hstep _ hβ i)

include hoff hzero in
/-- Every Weyl translate of a dominant integral weight lies below it in the root order. -/
theorem rootLE_smul_of_forall_apply_coroot_eq_natCast (w : W) {lam : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, lam (R.coroot i) = n) : R.RootLE (w • lam) lam := by
  apply R.rootLE_iff.mpr
  refine R.sub_smul_mem_of_step hdiag hoff hzero w lam R.posRootCone.toAddSubmonoid ?_
  intro β hβ i
  obtain ⟨n, hn⟩ := hlam i
  rw [hn, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hβ n

end RootOrder

variable [PartialOrder K] [IsOrderedRing K] [CharZero K]

local notation "Δ" => PointedCone.hull K (Set.range R.root)

omit [CharZero K] in
private theorem posRootCone_le_hull :
    R.posRootCone ≤ (Δ : Submodule (Nonneg K) (Dual K H)).restrictScalars ℕ :=
  R.posRootCone_def ▸ Submodule.span_le.mpr (PointedCone.subset_hull (R := K))

include hoff hzero in
/-- The difference between a dominant weight and any of its Weyl translates is a nonnegative
linear combination of simple roots. -/
theorem sub_smul_mem_root_hull (w : W) {lam : Dual K H} (hlam : R.IsDominant lam) :
    lam - w • lam ∈ Δ :=
  R.sub_smul_mem_of_step hdiag hoff hzero w lam (Δ).toAddSubmonoid
    fun _ hβ i ↦ PointedCone.smul_mem Δ (R.isDominant_iff.mp hlam i) (R.posRootCone_le_hull hβ)

omit [CharZero K] in
private theorem eq_zero_of_mem_root_hull_of_neg_mem {β : Dual K H}
    (hβ : β ∈ Δ) (hneg : -β ∈ Δ) : β = 0 := by
  by_contra hn
  exact PointedCone.salient_hull_range R.root_linearIndependent β hβ hn hneg

include hoff hzero in
/-- A Weyl translate of a dominant weight is dominant exactly when it equals that weight. -/
theorem isDominant_smul_iff_eq (w : W) {lam : Dual K H} (hlam : R.IsDominant lam) :
    R.IsDominant (w • lam) ↔ w • lam = lam := by
  refine ⟨fun hwlam ↦ ?_, fun he ↦ he.symm ▸ hlam⟩
  have hneg : -(lam - w • lam) ∈ Δ := by
    simpa only [inv_smul_smul, neg_sub] using
      R.sub_smul_mem_root_hull hdiag hoff hzero w⁻¹ hwlam
  have hpos := R.sub_smul_mem_root_hull hdiag hoff hzero w hlam
  exact (sub_eq_zero.mp (R.eq_zero_of_mem_root_hull_of_neg_mem hpos hneg)).symm

include hoff hzero in
/-- The dominant chamber is a fundamental domain for the Weyl action on the Tits cone. -/
theorem existsUnique_mem_orbit_inter_dominantChamber {lam : Dual K H}
    (hlam : lam ∈ R.titsCone (diag_map_intCast hdiag)) :
    ∃! μ, μ ∈ MulAction.orbit W lam ∩ R.dominantChamber := by
  obtain ⟨w, hw⟩ := (R.mem_titsCone_iff _).mp hlam
  refine ⟨w • lam, ⟨MulAction.mem_orbit _ _, hw⟩, ?_⟩
  rintro μ ⟨⟨v, rfl⟩, hv⟩
  simpa only [mul_smul, inv_smul_smul] using
    (R.isDominant_smul_iff_eq hdiag hoff hzero (v * w⁻¹) hw).mp
      (by simpa only [mul_smul, inv_smul_smul, mem_dominantChamber] using hv)

variable [DecidableEq I]

/-- The stabilizer of a dominant weight is the standard parabolic subgroup generated by the
simple reflections through walls containing the weight. -/
theorem parabolic_eq_stabilizer {lam : Dual K H} (hlam : R.IsDominant lam) :
    (R.weylCoxeterSystem hdiag hoff hzero).parabolic {i | lam (R.coroot i) = 0} =
      MulAction.stabilizer W lam := by
  classical
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  apply le_antisymm
  · refine (cs.parabolic_le_iff).mpr fun i hi ↦ ?_
    rw [MulAction.mem_stabilizer_iff]
    simpa [cs, Subgroup.smul_def, coe_weylSimple] using
      R.simpleReflection_of_apply_coroot_eq_zero (diag_map_intCast hdiag) hi
  suffices key : ∀ (w : W), w • lam = lam → w ∈ cs.parabolic {i | lam (R.coroot i) = 0} from
    fun w hw ↦ key w (MulAction.mem_stabilizer_iff.mp hw)
  intro w hwlam
  induction hn : cs.length w using Nat.strong_induction_on generalizing w with
  | ind n ih =>
    by_cases hw : w = 1
    · simp [hw]
    obtain ⟨v, i, hv, hvi, hβ⟩ := R.exists_mul_simple_of_ne_one hdiag hoff hzero hw
    have hdiff : v • lam - lam = lam (R.coroot i) • (v • R.root i) := by
      simpa only [← R.weylCoxeterSystem_simple hdiag hoff hzero, hvi, hwlam] using
        R.smul_sub_mul_weylSimple_smul (diag_map_intCast hdiag) v i lam
    -- Both differences lie in the salient cone, so this reflection step fixes the weight.
    have hstep : v • lam - lam ∈ Δ :=
      hdiff ▸ PointedCone.smul_mem Δ (R.isDominant_iff.mp hlam i) (R.posRootCone_le_hull hβ)
    have hvlam := sub_eq_zero.mp (R.eq_zero_of_mem_root_hull_of_neg_mem hstep (by
      simpa only [neg_sub] using R.sub_smul_mem_root_hull hdiag hoff hzero v hlam))
    have hzero_smul : lam (R.coroot i) • (v • R.root i) = 0 :=
      hdiff ▸ sub_eq_zero.mpr hvlam
    have hilam : lam (R.coroot i) = 0 :=
      (smul_eq_zero.mp hzero_smul).resolve_right
        ((smul_eq_zero_iff_eq v).not.mpr (R.root_linearIndependent.ne_zero i))
    exact hvi ▸ mul_mem (ih _ (hn ▸ hv) v hvlam rfl) (cs.simple_mem_parabolic hilam)

/-- Cosets of the standard parabolic on the walls through a dominant weight are the weights
in its orbit. -/
noncomputable def parabolicQuotientEquivOrbit {lam : Dual K H} (hlam : R.IsDominant lam) :
    W ⧸ (R.weylCoxeterSystem hdiag hoff hzero).parabolic {i | lam (R.coroot i) = 0} ≃
      MulAction.orbit W lam :=
  (Subgroup.quotientEquivOfEq (R.parabolic_eq_stabilizer hdiag hoff hzero hlam)).trans
    (MulAction.orbitEquivQuotientStabilizer W lam).symm

/-- The equivalence sends the coset of `w` to its action on the chosen weight. -/
@[simp]
theorem coe_parabolicQuotientEquivOrbit_mk {lam : Dual K H} (hlam : R.IsDominant lam) (w : W) :
    (R.parabolicQuotientEquivOrbit hdiag hoff hzero hlam ↑w : Dual K H) = w • lam := by
  simp only [parabolicQuotientEquivOrbit, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

end TauCeti.CartanRealization
