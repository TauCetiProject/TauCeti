/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Basic
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Normalized cusp data of a Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup and `c ∈ OnePoint ℝ` a cusp point of `Γ`, that is, a
point fixed by a parabolic element of `Γ`. Choose `σ ∈ PSL(2, ℝ)` with `σ • c = ∞`. Then the
stabilizer of `c` in `Γ` is infinite cyclic, and `σ` conjugates it onto the group of translations
`z ↦ z + n * w`, `n ∈ ℤ`, for a unique `w > 0`, the *width* of the cusp relative to `σ`.

The result is packaged as a *normalized cusp datum* `Subgroup.CuspDatum`: a cusp, a scaling, a
generator of the full stabilizer, and a positive width with the conjugation formula. Such a datum
records exactly the choices from which cusp neighbourhoods and the `q`-coordinate
`exp (2 * π * I * σ z / w)` are built. The width is not an invariant of the cusp alone; it depends
on the scaling, and the datum is unique once the cusp and the scaling are fixed.

## Main declarations

* `Subgroup.CuspDatum`: normalized cusp data of `Γ ≤ PSL(2, ℝ)`.
* `Subgroup.CuspDatum.mem_stabilizer_iff_conj`: the conjugated stabilizer of the cusp is exactly
  the group of translations by `width * ℤ`.
* `Subgroup.CuspDatum.eq_of_cusp_eq_of_scaling_eq`: a cusp datum is determined by its cusp and
  scaling.
* `Subgroup.IsCuspPoint.exists_cuspDatum`: for a discrete `Γ`, every cusp point and every scaling
  sending it to `∞` carry a cusp datum.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§5.1 and 9.2.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§2.2 and 4.2.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
-/

public section

open Matrix MulAction OnePoint
open scoped MatrixGroups

namespace Subgroup

open ProjectiveSpecialLinearGroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The periods of `Γ` at the scaling `σ`: the `x : ℝ` such that `Γ` contains the element that
`σ` conjugates to the translation `z ↦ z + x`. -/
private def cuspPeriods (Γ : Subgroup PSL(2, ℝ)) (σ : PSL(2, ℝ)) : AddSubgroup ℝ :=
  (Γ.comap (MulAut.conj σ⁻¹).toMonoidHom).toAddSubgroup.comap upperRightHom.toAddMonoidHom

private theorem mem_cuspPeriods {σ : PSL(2, ℝ)} {x : ℝ} :
    x ∈ cuspPeriods Γ σ ↔ σ⁻¹ * upperRightHom x * σ ∈ Γ := by
  simp [cuspPeriods]

/-- The discreteness transfer follows the proof pattern of David Loeffler's
`Subgroup.instDiscreteTopStrictPeriods` in `Mathlib/NumberTheory/ModularForms/Cusps.lean`. -/
private theorem discreteTopology_cuspPeriods [DiscreteTopology Γ] (σ : PSL(2, ℝ)) :
    DiscreteTopology (cuspPeriods Γ σ) := by
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : cuspPeriods Γ σ ↦ (⟨σ⁻¹ * upperRightHom (x : ℝ) * σ, mem_cuspPeriods.mp x.2⟩ : Γ))
    (continuous_induced_rng.mpr ?_) fun x y h ↦ ?_
  · exact (continuous_const.mul (continuous_upperRightHom.comp continuous_subtype_val)).mul
      continuous_const
  · exact Subtype.ext (upperRightHom_injective (by simpa using congrArg Subtype.val h))

/-- If `σ` conjugates `γ` to translation by `w`, it conjugates `γ ^ n` to translation by
`n * w`. -/
private theorem mul_zpow_mul_inv_eq_upperRightHom {σ γ : PSL(2, ℝ)} {w : ℝ}
    (h : σ * γ * σ⁻¹ = upperRightHom w) (n : ℤ) :
    σ * γ ^ n * σ⁻¹ = upperRightHom (n * w) := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, ← zsmul_eq_mul,
    AddChar.map_zsmul_eq_zpow]

/-- At a cusp point `c` of a discrete group, with `σ • c = ∞`, the periods form the multiples of a
positive width. -/
private theorem exists_pos_zmultiples_eq_cuspPeriods [DiscreteTopology Γ] {c : OnePoint ℝ}
    (hc : Γ.IsCuspPoint c) {σ : PSL(2, ℝ)} (hσ : σ • c = ∞) :
    ∃ w : ℝ, 0 < w ∧ AddSubgroup.zmultiples w = cuspPeriods Γ σ := by
  obtain ⟨p, hpc, hp⟩ := isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mp hc
  have hfix : (σ * p * σ⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hσ.symm, ← Subgroup.smul_def,
      mem_stabilizer_iff.mp hpc, hσ]
  obtain ⟨x, hx, hpx⟩ := (isParabolic_iff_exists_eq_upperRightHom hfix).mp
    ((isParabolic_conj_iff σ p).mpr hp)
  have hxP : x ∈ cuspPeriods Γ σ := by
    rw [mem_cuspPeriods, ← hpx]
    simp [mul_assoc]
  have := discreteTopology_cuspPeriods (Γ := Γ) σ
  have := AddSubgroup.discrete_iff_addCyclic.mpr this
  have : Nontrivial (cuspPeriods Γ σ) := ⟨⟨⟨x, hxP⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨a, ha, haP⟩ := LinearOrderedAddCommGroup.Subgroup.exists_neg_generator
    (cuspPeriods Γ σ)
  exact ⟨-a, neg_pos.mpr ha, by rw [AddSubgroup.zmultiples_neg, haP]⟩

/-- If the periods of `Γ` at `σ` are the multiples of `w > 0`, then an element of `Γ` fixes
`σ⁻¹ • ∞` exactly when its conjugate by `σ` is translation by an integer multiple of `w`. -/
private theorem mem_stabilizer_iff_of_zmultiples_eq_cuspPeriods {c : OnePoint ℝ}
    {σ : PSL(2, ℝ)} (hσ : σ • c = ∞) {w : ℝ} (hw : 0 < w)
    (hP : AddSubgroup.zmultiples w = cuspPeriods Γ σ) (g : Γ) :
    g ∈ stabilizer Γ c ↔ ∃ n : ℤ, σ * g * σ⁻¹ = upperRightHom (n * w) := by
  have hc : σ⁻¹ • (∞ : OnePoint ℝ) = c := inv_smul_eq_iff.mpr hσ.symm
  rw [mem_stabilizer_iff, Subgroup.smul_def]
  refine ⟨fun hg ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · have hfix : (σ * g * σ⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
      rw [mul_smul, mul_smul, hc, hg, hσ]
    obtain ⟨t, ht, hconj⟩ := exists_conj_upperRightHom_of_smul_infty hfix
    have hwP : w ∈ cuspPeriods Γ σ := hP ▸ AddSubgroup.mem_zmultiples w
    -- conjugation by `g` rescales the periods by `t ^ 2`, in both directions; since the periods
    -- are `w * ℤ`, this forces `t ^ 2 = 1`, so `σ * g * σ⁻¹` commutes with translations
    have hmul : t ^ 2 * w ∈ cuspPeriods Γ σ := by
      rw [mem_cuspPeriods, ← hconj]
      convert Γ.mul_mem (Γ.mul_mem g.2 (mem_cuspPeriods.mp hwP)) (Γ.inv_mem g.2) using 1
      group
    have hinv : (t ^ 2)⁻¹ * w ∈ cuspPeriods Γ σ := by
      have h := hconj ((t ^ 2)⁻¹ * w)
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht), one_mul] at h
      have h' : upperRightHom ((t ^ 2)⁻¹ * w) =
          (σ * g * σ⁻¹)⁻¹ * upperRightHom w * (σ * g * σ⁻¹) := by
        rw [← h]
        group
      rw [mem_cuspPeriods, h']
      convert Γ.mul_mem (Γ.mul_mem (Γ.inv_mem g.2) (mem_cuspPeriods.mp hwP)) g.2 using 1
      group
    rw [← hP, AddSubgroup.mem_zmultiples_iff] at hmul hinv
    obtain ⟨m, hm⟩ := hmul
    obtain ⟨k, hk⟩ := hinv
    rw [zsmul_eq_mul] at hm hk
    have hm' : (m : ℝ) = t ^ 2 := mul_right_cancel₀ hw.ne' hm
    have hk' : (k : ℝ) = (t ^ 2)⁻¹ := mul_right_cancel₀ hw.ne' hk
    have hmk : m * k = 1 := by
      exact_mod_cast (by rw [hm', hk', mul_inv_cancel₀ (pow_ne_zero 2 ht)] : (m : ℝ) * k = 1)
    have hm1 : m = 1 := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hm' ▸ sq_nonneg t) hmk
    have hcomm : Commute (σ * g * σ⁻¹) (upperRightHom w) := by
      have h := hconj w
      rw [← hm', hm1, Int.cast_one, one_mul, mul_inv_eq_iff_eq_mul] at h
      exact h
    obtain ⟨y, hy⟩ := exists_eq_upperRightHom_of_commute hfix hw.ne' hcomm
    have hyP : y ∈ cuspPeriods Γ σ := by
      rw [mem_cuspPeriods, ← hy]
      simp [mul_assoc]
    rw [← hP, AddSubgroup.mem_zmultiples_iff] at hyP
    obtain ⟨n, rfl⟩ := hyP
    exact ⟨n, by rw [hy, zsmul_eq_mul]⟩
  · have hg : (g : PSL(2, ℝ)) = σ⁻¹ * upperRightHom (n * w) * σ := by
      rw [← hn]
      group
    rw [hg, mul_smul, mul_smul, hσ, upperRightHom_smul_infty, hc]

/-- **Normalized cusp data.** A cusp datum of `Γ ≤ PSL(2, ℝ)` consists of a boundary point
`cusp`, a *scaling* `σ ∈ PSL(2, ℝ)`, an element `generator` of `Γ` generating the full stabilizer
of `cusp` in `Γ`, and a positive `width` such that `σ * generator * σ⁻¹` is the translation
`z ↦ z + width`. Consequently `σ` sends `cusp` to `∞` (`Subgroup.CuspDatum.scaling_smul_cusp`),
`cusp` is a cusp point (`Subgroup.CuspDatum.isCuspPoint`), and conjugation by `σ` identifies the
full stabilizer with the translations by `width * ℤ`
(`Subgroup.CuspDatum.mem_stabilizer_iff_conj`).

The width depends on the scaling and not only on the cusp; given the cusp and the scaling, the
datum is unique (`Subgroup.CuspDatum.eq_of_cusp_eq_of_scaling_eq`). In particular a proper power
of the generator, although also conjugate to a positive translation, never forms a cusp datum.
For a discrete `Γ`, every cusp point and every scaling sending it to `∞` carry a cusp datum
(`Subgroup.IsCuspPoint.exists_cuspDatum`). -/
structure CuspDatum (Γ : Subgroup PSL(2, ℝ)) where
  /-- The cusp point. -/
  cusp : OnePoint ℝ
  /-- A projective transformation, which sends `cusp` to `∞`. -/
  scaling : PSL(2, ℝ)
  /-- The selected generator of the stabilizer of `cusp` in `Γ`. -/
  generator : Γ
  /-- The width of the cusp relative to `scaling`. -/
  width : ℝ
  width_pos : 0 < width
  zpowers_generator : zpowers generator = stabilizer Γ cusp
  scaling_mul_generator_mul_inv : scaling * generator * scaling⁻¹ = upperRightHom width

namespace CuspDatum

variable (D : Γ.CuspDatum)

/-- The selected generator fixes the cusp. -/
theorem generator_mem_stabilizer : D.generator ∈ stabilizer Γ D.cusp :=
  D.zpowers_generator ▸ mem_zpowers _

/-- The selected generator of the stabilizer of a cusp is parabolic. -/
theorem isParabolic_generator : IsParabolic (D.generator : PSL(2, ℝ)) := by
  rw [← isParabolic_conj_iff D.scaling, D.scaling_mul_generator_mul_inv,
    isParabolic_upperRightHom_iff]
  exact D.width_pos.ne'

/-- The scaling of a cusp datum sends the cusp to `∞`. -/
@[simp]
theorem scaling_smul_cusp : D.scaling • D.cusp = ∞ := by
  have hfix : upperRightHom D.width • D.scaling • D.cusp = D.scaling • D.cusp := by
    rw [← D.scaling_mul_generator_mul_inv, mul_smul, mul_smul, inv_smul_smul, ← Subgroup.smul_def,
      D.generator_mem_stabilizer]
  rwa [(isParabolic_upperRightHom_iff.mpr D.width_pos.ne').smul_eq_self_iff,
    parabolicFixedPoint_upperRightHom] at hfix

/-- The point of a cusp datum is a cusp point. -/
theorem isCuspPoint : Γ.IsCuspPoint D.cusp :=
  isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mpr
    ⟨D.generator, D.generator_mem_stabilizer, D.isParabolic_generator⟩

/-- The stabilizer of the cusp consists of the integer powers of the selected generator. -/
theorem mem_stabilizer_iff {g : Γ} : g ∈ stabilizer Γ D.cusp ↔ ∃ n : ℤ, D.generator ^ n = g := by
  rw [← D.zpowers_generator, mem_zpowers_iff]

/-- Conjugation by the scaling sends the `n`-th power of the generator to translation by
`n * width`. -/
@[simp]
theorem scaling_mul_generator_zpow_mul_inv (n : ℤ) :
    D.scaling * (D.generator : PSL(2, ℝ)) ^ n * D.scaling⁻¹ =
      upperRightHom (n * D.width) := by
  rw [mul_zpow_mul_inv_eq_upperRightHom D.scaling_mul_generator_mul_inv]

/-- **The conjugated cusp stabilizer is `width * ℤ`.** An element of `Γ` fixes the cusp exactly
when its conjugate by the scaling is translation by an integer multiple of the width. -/
theorem mem_stabilizer_iff_conj {g : Γ} :
    g ∈ stabilizer Γ D.cusp ↔
      ∃ n : ℤ, D.scaling * g * D.scaling⁻¹ = upperRightHom (n * D.width) := by
  rw [D.mem_stabilizer_iff]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, hn ▸ D.scaling_mul_generator_zpow_mul_inv n⟩, fun ⟨n, hn⟩ ↦
    ⟨n, Subtype.ext ((MulAut.conj D.scaling).injective ?_)⟩⟩
  rw [MulAut.conj_apply, MulAut.conj_apply, Subgroup.coe_zpow,
    D.scaling_mul_generator_zpow_mul_inv, hn]

/-- **Uniqueness of normalized cusp data.** A cusp datum is determined by its cusp and its
scaling: the width is then the positive generator of the conjugated stabilizer, and the
generator is the corresponding element of `Γ`. -/
@[ext]
theorem eq_of_cusp_eq_of_scaling_eq {D D' : Γ.CuspDatum} (hc : D.cusp = D'.cusp)
    (hσ : D.scaling = D'.scaling) : D = D' := by
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp (hc ▸ D'.generator_mem_stabilizer)
  obtain ⟨m, hm⟩ := D'.mem_stabilizer_iff_conj.mp (hc ▸ D.generator_mem_stabilizer)
  rw [hσ, D'.scaling_mul_generator_mul_inv] at hn
  rw [← hσ, D.scaling_mul_generator_mul_inv] at hm
  have hn' := upperRightHom_injective hn
  have hm' := upperRightHom_injective hm
  have hmn : (m : ℝ) * n = 1 := mul_right_cancel₀ D.width_pos.ne' (by
    rw [one_mul, mul_assoc, ← hn', ← hm'])
  have hn0 : 0 ≤ n := by
    have : (0 : ℝ) < n * D.width := hn' ▸ D'.width_pos
    exact_mod_cast (pos_of_mul_pos_left this D.width_pos.le).le
  have hn1 : n = 1 := Int.eq_one_of_mul_eq_one_left hn0 (by exact_mod_cast hmn)
  have hw : D.width = D'.width := by rw [hn', hn1, Int.cast_one, one_mul]
  have hgen : D.generator = D'.generator := by
    refine Subtype.ext ((MulAut.conj D.scaling).injective ?_)
    rw [MulAut.conj_apply, MulAut.conj_apply, D.scaling_mul_generator_mul_inv, hσ,
      D'.scaling_mul_generator_mul_inv, hw]
  cases D
  cases D'
  simp_all

end CuspDatum

/-- **Existence of normalized cusp data.** Let `Γ ≤ PSL(2, ℝ)` be discrete and `c` a cusp point
of `Γ`. For every `σ ∈ PSL(2, ℝ)` with `σ • c = ∞` there is a cusp datum with cusp `c` and
scaling `σ`: the stabilizer of `c` in `Γ` is infinite cyclic, generated by an element that `σ`
conjugates to a positive translation. -/
theorem IsCuspPoint.exists_cuspDatum [DiscreteTopology Γ] {c : OnePoint ℝ}
    (hc : Γ.IsCuspPoint c) {σ : PSL(2, ℝ)} (hσ : σ • c = ∞) :
    ∃ D : Γ.CuspDatum, D.cusp = c ∧ D.scaling = σ := by
  obtain ⟨w, hw, hP⟩ := exists_pos_zmultiples_eq_cuspPeriods hc hσ
  have hwP : σ⁻¹ * upperRightHom w * σ ∈ Γ :=
    mem_cuspPeriods.mp (hP ▸ AddSubgroup.mem_zmultiples w)
  let γ : Γ := ⟨σ⁻¹ * upperRightHom w * σ, hwP⟩
  have hγ : σ * γ * σ⁻¹ = upperRightHom w := by
    simp [γ, mul_assoc]
  refine ⟨⟨c, σ, γ, w, hw, le_antisymm ?_ fun g hg ↦ ?_, hγ⟩, rfl, rfl⟩
  · exact zpowers_le.mpr ((mem_stabilizer_iff_of_zmultiples_eq_cuspPeriods hσ hw hP γ).mpr
      ⟨1, by rw [hγ, Int.cast_one, one_mul]⟩)
  · obtain ⟨n, hn⟩ := (mem_stabilizer_iff_of_zmultiples_eq_cuspPeriods hσ hw hP g).mp hg
    refine mem_zpowers_iff.mpr ⟨n, Subtype.ext ((MulAut.conj σ).injective ?_)⟩
    rw [MulAut.conj_apply, MulAut.conj_apply, hn, Subgroup.coe_zpow,
      mul_zpow_mul_inv_eq_upperRightHom hγ]

/-- Every cusp point of a discrete subgroup of `PSL(2, ℝ)` is the cusp of a cusp datum. -/
theorem IsCuspPoint.exists_cuspDatum_cusp_eq [DiscreteTopology Γ] {c : OnePoint ℝ}
    (hc : Γ.IsCuspPoint c) : ∃ D : Γ.CuspDatum, D.cusp = c := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq PSL(2, ℝ) c ∞
  obtain ⟨D, hD, -⟩ := hc.exists_cuspDatum hσ
  exact ⟨D, hD⟩

end Subgroup
