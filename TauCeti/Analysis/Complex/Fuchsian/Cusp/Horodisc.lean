/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Coordinate
import TauCeti.Analysis.Complex.Fuchsian.Shimizu

/-!
# Precisely invariant horodiscs at a cusp

Let `D` be a normalized cusp datum of `Γ ≤ PSL(2, ℝ)`, with scaling `σ` and width `w`. The
*horodisc of height `A`* at the cusp of `D` is the set `{z | A < (σ • z).im}`: in the scaling
coordinate it is the half-plane above height `A`, and it is exactly the preimage of a punctured
disc under the exponential coordinate
(`TauCeti.Subgroup.CuspDatum.norm_qCoordinate_lt_iff`).

The cusp stabilizer permutes each horodisc, because in the scaling coordinate it acts by
translations. The point of this file is the converse for a discrete `Γ`: as soon as the height is
at least the width, nothing else does. An element of `Γ` moving a point of the horodisc back into
the horodisc lies in the cusp stabilizer, so two elements of `Γ` in different cosets of the
stabilizer carry the horodisc to disjoint sets. This is the *precise invariance* that makes the
horodisc descend to a punctured-disc neighbourhood of the cusp in the quotient.

The bound `w ≤ A` is exactly Shimizu's lemma
(`Subgroup.im_smul_mul_im_le_sq_of_upperRightHom_mem`), applied to the conjugate group
`σ Γ σ⁻¹`, which contains the translation by `w` and is again discrete.

## Main results

* `TauCeti.Subgroup.CuspDatum.smul_horodisc_of_mem_stabilizer`: the cusp stabilizer preserves
  every horodisc.
* `TauCeti.Subgroup.CuspDatum.mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc`: precise
  invariance.
* `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodisc` and
  `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodisc_self`: the translates of a high horodisc
  by two elements lying in different cosets of the cusp stabilizer are disjoint.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint UpperHalfPlane
open scoped Complex.UnitDisc MatrixGroups Pointwise

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- The horodisc of height `A` at the cusp represented by `D`, in its normalized scaling
coordinate. -/
def horodisc (A : ℝ) : Set ℍ := {z | A < (D.scaling • z).im}

/-- Membership in a horodisc is the corresponding lower bound on the scaled imaginary part. -/
@[simp]
theorem mem_horodisc {A : ℝ} {z : ℍ} : z ∈ horodisc D A ↔ A < (D.scaling • z).im := Iff.rfl

/-- A horodisc is the inverse image of the corresponding punctured disc under the normalized
q-coordinate. -/
theorem norm_qCoordinate_lt_iff_mem_horodisc (A : ℝ) (z : ℍ) :
    ‖((qCoordinate D z : 𝔻) : ℂ)‖ < Real.exp (-2 * Real.pi * A / D.width) ↔
      z ∈ horodisc D A := by
  rw [norm_qCoordinate_lt_iff, mem_horodisc]

/-- In the scaling coordinate the cusp stabilizer acts by translations, so it preserves the
height above the real axis. -/
@[simp]
theorem im_scaling_smul_smul_of_mem_stabilizer {g : Γ} (hg : g ∈ stabilizer Γ D.cusp) (z : ℍ) :
    (D.scaling • (g • z)).im = (D.scaling • z).im := by
  obtain ⟨n, rfl⟩ := D.mem_stabilizer_iff.mp hg
  rw [scaling_smul_generator_zpow, vadd_im]

/-- **The cusp stabilizer preserves every horodisc at its cusp.** -/
@[simp]
theorem smul_horodisc_of_mem_stabilizer {g : Γ} (hg : g ∈ stabilizer Γ D.cusp) (A : ℝ) :
    g • horodisc D A = horodisc D A := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_horodisc, mem_horodisc,
    im_scaling_smul_smul_of_mem_stabilizer D (inv_mem hg)]

/-- **Precise invariance of high horodiscs.** Let `D` be a normalized cusp datum of a discrete
`Γ ≤ PSL(2, ℝ)` and let the height `A` be at least the width of `D`. If an element of `Γ` carries
a point of the horodisc of height `A` back into that horodisc, then it fixes the cusp. -/
theorem mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc [DiscreteTopology Γ] {A : ℝ}
    (hA : D.width ≤ A) {g : Γ} {z : ℍ} (hz : z ∈ horodisc D A)
    (hgz : g • z ∈ horodisc D A) :
    g ∈ stabilizer Γ D.cusp := by
  by_contra hstab
  -- the conjugate group `σ Γ σ⁻¹` is discrete and contains the translation by the width
  set Δ : Subgroup PSL(2, ℝ) := ConjAct.toConjAct D.scaling • Γ
  have hconj : ∀ x : PSL(2, ℝ), ConjAct.toConjAct D.scaling • x = D.scaling * x * D.scaling⁻¹ :=
    fun x => by rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  have hT : upperRightHom D.width ∈ Δ := by
    rw [← D.scaling_mul_generator_mul_inv, ← hconj]
    exact _root_.Subgroup.smul_mem_pointwise_smul _ _ _ D.generator.2
  have hgΔ : D.scaling * (g : PSL(2, ℝ)) * D.scaling⁻¹ ∈ Δ := by
    rw [← hconj]
    exact _root_.Subgroup.smul_mem_pointwise_smul _ _ _ g.2
  -- an element of `Γ` outside the cusp stabilizer conjugates to one not fixing `∞`
  have hfix : ∀ x : PSL(2, ℝ), (D.scaling * x * D.scaling⁻¹) • (∞ : OnePoint ℝ) =
      D.scaling • (x • D.cusp) := fun x => by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm]
  have hginf : (D.scaling * (g : PSL(2, ℝ)) * D.scaling⁻¹) • (∞ : OnePoint ℝ) ≠ ∞ := by
    rw [hfix]
    intro h
    exact hstab (mem_stabilizer_iff.mpr ((MulAction.injective D.scaling)
      (h.trans D.scaling_smul_cusp.symm)))
  -- Shimizu's lemma bounds the product of the two heights by the squared width
  have hkey := _root_.Subgroup.im_smul_mul_im_le_sq_of_upperRightHom_mem D.width_pos.ne' hT hgΔ
    hginf (D.scaling • z)
  rw [mul_smul, mul_smul, inv_smul_smul, ← _root_.Subgroup.smul_def] at hkey
  have hApos : 0 < A := D.width_pos.trans_le hA
  rw [mem_horodisc] at hz hgz
  have hprod : A * A < (D.scaling • g • z).im * (D.scaling • z).im :=
    mul_lt_mul'' hgz hz hApos.le hApos.le
  nlinarith [D.width_pos]

/-- **Precise invariance of high horodiscs, disjointness form.** Two elements of `Γ` carrying a
horodisc of height at least the width to sets that meet differ by an element of the cusp
stabilizer. -/
theorem disjoint_smul_horodisc [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A) {g h : Γ}
    (hgh : g⁻¹ * h ∉ stabilizer Γ D.cusp) :
    Disjoint (g • horodisc D A) (h • horodisc D A) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨y, hy, hyz⟩
  replace hyz : h • y = g • z := hyz
  refine hgh (mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc D hA hy ?_)
  rwa [mul_smul, hyz, inv_smul_smul]

/-- An element of `Γ` outside the cusp stabilizer moves every horodisc of height at least the
width off itself. -/
theorem disjoint_smul_horodisc_self [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A) {g : Γ}
    (hg : g ∉ stabilizer Γ D.cusp) :
    Disjoint (g • horodisc D A) (horodisc D A) := by
  simpa using disjoint_smul_horodisc D hA (g := g) (h := 1) (by simpa using hg)

end TauCeti.Subgroup.CuspDatum
