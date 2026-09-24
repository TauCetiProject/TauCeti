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

The same argument separates horodiscs at two different cusps. If `g ∈ Γ` does not carry the cusp
of a second datum `D'` to the cusp of `D`, then the heights of `g • z` above the cusp of `D` and
of `z` above the cusp of `D'` have product at most `D.width * D'.width`. Hence horodiscs whose
heights are at least the widths never meet across such an element, and at two cusps that are not
`Γ`-equivalent their images in the orbit space `Γ \ ℍ` are disjoint. These disjoint punctured-disc
neighbourhoods of inequivalent cusps are what separate distinct cusp points once they are adjoined
to the quotient.

All of these bounds are Shimizu's lemma
(`Subgroup.im_smul_mul_im_le_abs_mul_of_upperRightHom_mem`), applied to the conjugate group
`σ Γ σ⁻¹`, which contains the translation by `w` and is again discrete.

## Main results

* `TauCeti.Subgroup.CuspDatum.smul_horodisc_of_mem_stabilizer`: the cusp stabilizer preserves
  every horodisc.
* `TauCeti.Subgroup.CuspDatum.im_scaling_smul_smul_mul_im_scaling_smul_le`: Shimizu's inequality
  comparing the heights above two cusps.
* `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodisc_horodisc`: an element of `Γ` not carrying one
  cusp to the other carries a high horodisc at the first off a high horodisc at the second.
* `TauCeti.Subgroup.CuspDatum.mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc`: precise
  invariance.
* `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodisc` and
  `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodisc_self`: the translates of a high horodisc
  by two elements lying in different cosets of the cusp stabilizer are disjoint.
* `TauCeti.Subgroup.CuspDatum.disjoint_image_quotientMk_horodisc_iff`: high horodiscs at two cusps
  have disjoint images in the orbit space exactly when the cusps are not `Γ`-equivalent.

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

/-- **Shimizu's inequality at two cusps.** Let `D` and `D'` be normalized cusp data of a discrete
`Γ ≤ PSL(2, ℝ)`. If `g ∈ Γ` does not carry the cusp of `D'` to the cusp of `D`, then the height of
`g • z` above the cusp of `D` and the height of `z` above the cusp of `D'`, each measured in the
scaling coordinate of its datum, have product at most `D.width * D'.width`.

This is Shimizu's lemma (`Subgroup.im_smul_mul_im_le_abs_mul_of_upperRightHom_mem`) for the
conjugate group `σ Γ σ⁻¹`, which contains the translation by `D.width`, applied to `σ g σ'⁻¹`,
which conjugates the translation by `D'.width` into it. -/
theorem im_scaling_smul_smul_mul_im_scaling_smul_le [DiscreteTopology Γ] (D' : Γ.CuspDatum)
    {g : Γ} (hg : g • D'.cusp ≠ D.cusp) (z : ℍ) :
    (D.scaling • g • z).im * (D'.scaling • z).im ≤ D.width * D'.width := by
  -- the conjugate group `σ Γ σ⁻¹` is discrete and contains the translation by the width of `D`
  set Δ : Subgroup PSL(2, ℝ) := ConjAct.toConjAct D.scaling • Γ
  have hmem : ∀ x ∈ Γ, D.scaling * x * D.scaling⁻¹ ∈ Δ := fun x hx => by
    rw [← ConjAct.ofConjAct_toConjAct D.scaling, ← ConjAct.smul_def]
    exact _root_.Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hT : upperRightHom D.width ∈ Δ := by
    rw [← D.scaling_mul_generator_mul_inv]
    exact hmem _ D.generator.2
  -- `σ g σ'⁻¹` conjugates the translation by the width of `D'` into `σ Γ σ⁻¹`
  have hh : D.scaling * g * D'.scaling⁻¹ * upperRightHom D'.width *
      (D.scaling * g * D'.scaling⁻¹)⁻¹ ∈ Δ := by
    have heq : D.scaling * g * D'.scaling⁻¹ * upperRightHom D'.width *
        (D.scaling * g * D'.scaling⁻¹)⁻¹ =
          D.scaling * ((g : PSL(2, ℝ)) * D'.generator * (g : PSL(2, ℝ))⁻¹) * D.scaling⁻¹ := by
      rw [← D'.scaling_mul_generator_mul_inv]
      group
    rw [heq]
    exact hmem _ (Γ.mul_mem (Γ.mul_mem g.2 D'.generator.2) (Γ.inv_mem g.2))
  -- it does not fix `∞`, because `g` does not carry the cusp of `D'` to the cusp of `D`
  have hinf : (D.scaling * g * D'.scaling⁻¹) • (∞ : OnePoint ℝ) ≠ ∞ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr D'.scaling_smul_cusp.symm,
      ← D.scaling_smul_cusp]
    exact fun h => hg (MulAction.injective D.scaling h)
  have hkey := _root_.Subgroup.im_smul_mul_im_le_abs_mul_of_upperRightHom_mem
    D.width_pos.ne' D'.width_pos.ne' hT hh hinf (D'.scaling • z)
  rwa [mul_smul, mul_smul, inv_smul_smul, ← _root_.Subgroup.smul_def,
    abs_of_pos (mul_pos D.width_pos D'.width_pos)] at hkey

/-- **Horodiscs at two cusps.** Let `D` and `D'` be normalized cusp data of a discrete
`Γ ≤ PSL(2, ℝ)`, and let the heights satisfy `0 ≤ A` and `D.width * D'.width ≤ A * A'`, for
instance `D.width ≤ A` and `D'.width ≤ A'`. If `g ∈ Γ` does not carry the cusp of `D'` to the cusp
of `D`, it carries the horodisc of height `A'` at `D'` off the horodisc of height `A` at `D`. -/
theorem disjoint_smul_horodisc_horodisc [DiscreteTopology Γ] (D' : Γ.CuspDatum) {A A' : ℝ}
    (hA : 0 ≤ A) (hAA' : D.width * D'.width ≤ A * A') {g : Γ} (hg : g • D'.cusp ≠ D.cusp) :
    Disjoint (g • horodisc D' A') (horodisc D A) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ hgz
  rw [mem_horodisc] at hz hgz
  have hA' : 0 < A' := pos_of_mul_pos_right
    ((mul_pos D.width_pos D'.width_pos).trans_le hAA') hA
  have hprod : A * A' < (D.scaling • g • z).im * (D'.scaling • z).im :=
    mul_lt_mul'' hgz hz hA hA'.le
  linarith [im_scaling_smul_smul_mul_im_scaling_smul_le D D' hg z]

/-- **Precise invariance of high horodiscs.** Let `D` be a normalized cusp datum of a discrete
`Γ ≤ PSL(2, ℝ)` and let the height `A` be at least the width of `D`. If an element of `Γ` carries
a point of the horodisc of height `A` back into that horodisc, then it fixes the cusp. -/
theorem mem_stabilizer_of_mem_horodisc_of_smul_mem_horodisc [DiscreteTopology Γ] {A : ℝ}
    (hA : D.width ≤ A) {g : Γ} {z : ℍ} (hz : z ∈ horodisc D A)
    (hgz : g • z ∈ horodisc D A) :
    g ∈ stabilizer Γ D.cusp := by
  by_contra hstab
  refine Set.disjoint_left.mp (disjoint_smul_horodisc_horodisc D D (D.width_pos.le.trans hA)
    (mul_le_mul hA hA D.width_pos.le (D.width_pos.le.trans hA)) (g := g) ?_)
    (Set.smul_mem_smul_set hz) hgz
  exact fun h => hstab (mem_stabilizer_iff.mpr h)

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

/-- Horodiscs at two `Γ`-equivalent cusps have intersecting images in the orbit space, whatever
their heights: a point high enough above the first cusp is carried by `Γ` to a point high above
the second. -/
theorem not_disjoint_image_quotientMk_horodisc_of_mem_orbit (D' : Γ.CuspDatum)
    (hc : D'.cusp ∈ orbit Γ D.cusp) (A A' : ℝ) :
    ¬Disjoint (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A)
      (Quotient.mk (orbitRel Γ ℍ) '' horodisc D' A') := by
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp hc
  -- `σ' k σ⁻¹` fixes `∞`, so it acts on the upper half-plane by a positive real affine map
  have hfix : (D'.scaling * (k : PSL(2, ℝ)) * D.scaling⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm,
      ← _root_.Subgroup.smul_def, hk, D'.scaling_smul_cusp]
  obtain ⟨M, hM⟩ := QuotientGroup.mk_surjective (D'.scaling * (k : PSL(2, ℝ)) * D.scaling⁻¹)
  rw [← hM, OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hfix
  obtain ⟨a, b, hab⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero M hfix
  -- a point at height `t` in the scaling coordinate of `D`, with `t` large, lies in both
  -- horodiscs up to the action of `k`
  set t := max (max A (A' / a)) 0 + 1
  have ht : 0 < t := by positivity
  set x : ℍ := D.scaling⁻¹ • ((⟨t, ht⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I)
  have hσx : D.scaling • x = (⟨t, ht⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I :=
    smul_inv_smul _ _
  have hkx : D'.scaling • k • x = M • (D.scaling • x) := by
    rw [← UpperHalfPlane.pslMk_smul, hM, mul_smul, mul_smul, inv_smul_smul,
      _root_.Subgroup.smul_def]
  have hx : (D.scaling • x).im = t := by
    simp [hσx, pos_real_im]
  have hkx' : (D'.scaling • k • x).im = a * t := by
    rw [hkx, ← hx, congrFun hab]
    simp [pos_real_im]
  rw [Set.not_disjoint_iff]
  refine ⟨Quotient.mk _ x, ⟨x, ?_, rfl⟩, ⟨k • x, ?_, ?_⟩⟩
  · rw [mem_horodisc, hx]
    linarith [le_max_left (max A (A' / a)) 0, le_max_left A (A' / a)]
  · rw [mem_horodisc, hkx', ← div_lt_iff₀' a.2]
    linarith [le_max_left (max A (A' / a)) 0, le_max_right A (A' / a)]
  · exact Quotient.sound (mem_orbit_iff.mpr ⟨k, rfl⟩)

/-- **Horodiscs at inequivalent cusps have disjoint images.** Let `D` and `D'` be normalized cusp
data of a discrete `Γ ≤ PSL(2, ℝ)`, and let the heights satisfy `0 ≤ A` and
`D.width * D'.width ≤ A * A'`, for instance `D.width ≤ A` and `D'.width ≤ A'`. The images of the
horodiscs of heights `A` at `D` and `A'` at `D'` in the orbit space `Γ \ ℍ` are disjoint exactly
when the two cusps are not `Γ`-equivalent. -/
theorem disjoint_image_quotientMk_horodisc_iff [DiscreteTopology Γ] (D' : Γ.CuspDatum)
    {A A' : ℝ} (hA : 0 ≤ A) (hAA' : D.width * D'.width ≤ A * A') :
    Disjoint (Quotient.mk (orbitRel Γ ℍ) '' horodisc D A)
        (Quotient.mk (orbitRel Γ ℍ) '' horodisc D' A') ↔
      D'.cusp ∉ orbit Γ D.cusp := by
  refine ⟨fun h hc => not_disjoint_image_quotientMk_horodisc_of_mem_orbit D D' hc A A' h,
    fun hc => ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨y, hy, hyz⟩
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (Quotient.exact hyz)
  refine Set.disjoint_left.mp (disjoint_smul_horodisc_horodisc D D' hA hAA' (g := g⁻¹) ?_)
    (Set.smul_mem_smul_set hy) (by rwa [inv_smul_smul])
  intro h
  exact hc (mem_orbit_iff.mpr ⟨g, by rw [← h, smul_inv_smul]⟩)

end TauCeti.Subgroup.CuspDatum
