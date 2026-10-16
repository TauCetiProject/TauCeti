/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Basic
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Translation

/-!
# Finite Dirichlet constraints near a cusp

For any Dirichlet centre and any normalized cusp datum of a discrete Fuchsian group, finitely
many distance inequalities describe the Dirichlet domain on a sufficiently high horodisc.
The centre need not lie in that horodisc, and the intersection is allowed to be empty.
This controls the unbounded cusp ends when assembling a finite-sided Dirichlet polygon.

The two constraints from the positive cusp generator and its inverse restrict the horizontal
coordinate to a strip of width equal to the cusp width. Low orbit points cannot compete high
in this strip. The remaining orbit points have uniformly bounded height by Shimizu's lemma;
translation by the cusp stabilizer reduces them to a compact rectangle, which meets the orbit
in only finitely many acting elements.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §§3.2 and 4.2.

We use the orbit-height bound
`TauCeti.Subgroup.CuspDatum.exists_isOpen_mem_forall_im_scaling_smul_smul_le`, the hyperbolic
cosine distance formula, and Mathlib's proper-discontinuity finiteness theorem.
-/

public section

open Set UpperHalfPlane TauCeti
open TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- The scaled image of the Dirichlet domain lies in the vertical strip of width `D.width`
centred at `(D.scaling • p).re`. -/
theorem abs_re_scaling_smul_sub_le {p z : ℍ} (hz : z ∈ dirichletDomain Γ p) :
    |(D.scaling • z).re - (D.scaling • p).re| ≤ D.width / 2 := by
  apply (dist_le_dist_vadd_and_neg_vadd_iff D.width_pos _ _).mp
  have h (k : ℤ) := mem_dirichletDomain.mp hz (D.generator ^ k)
  have hscaled (k : ℤ) : dist (D.scaling • z) (D.scaling • p) ≤
      dist (D.scaling • z) ((k : ℝ) * D.width +ᵥ (D.scaling • p)) := by
    simpa only [← D.scaling_smul_generator_zpow, dist_smul] using h k
  constructor
  · simpa using hscaled 1
  · simpa using hscaled (-1)

/-- The part of a Dirichlet domain between two cusp heights is bounded, provided the lower
height is positive. The upper height is arbitrary, and the band may be empty. -/
theorem isBounded_dirichletDomain_inter_horodisc_diff (p : ℍ) {A : ℝ} (hA : 0 < A)
    (B : ℝ) :
    Bornology.IsBounded (sdiff (dirichletDomain Γ p ∩ D.horodisc A) (D.horodisc B)) := by
  let P := D.scaling • p
  let R : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹'
    (Icc (P.re - D.width / 2) (P.re + D.width / 2) ×ℂ Icc A B)
  have hR : IsCompact R :=
    (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff fun w hw ↦ by
      rw [range_coe]
      exact hA.trans_le (Complex.mem_reProdIm.mp hw).2.1).mpr
      (isCompact_Icc.reProdIm isCompact_Icc)
  refine ((Homeomorph.smul D.scaling).isCompact_preimage.mpr hR).isBounded.subset ?_
  rintro z ⟨⟨hz, hzA⟩, hzB⟩
  have hre := abs_le.mp (D.abs_re_scaling_smul_sub_le hz)
  have him : (D.scaling • z).im ∈ Icc A B :=
    ⟨((D.mem_horodisc).mp hzA).le, not_lt.mp (by simpa only [D.mem_horodisc] using hzB)⟩
  simp only [Set.mem_preimage, Homeomorph.smul_apply, R, Complex.mem_reProdIm, coe_re, coe_im]
  exact ⟨⟨by dsimp only [P]; linarith,
    by dsimp only [P]; linarith⟩, him⟩

variable [DiscreteTopology Γ]

private theorem finite_setOf_scaling_smul_mem_rectangle (p : ℍ) {a b c d : ℝ} (hc : 0 < c) :
    {g : Γ | (D.scaling • g • p).re ∈ Icc a b ∧
      (D.scaling • g • p).im ∈ Icc c d}.Finite := by
  let R : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' (Icc a b ×ℂ Icc c d)
  have hR : IsCompact R :=
    (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff fun w hw ↦ by
      rw [range_coe]
      exact hc.trans_le (Complex.mem_reProdIm.mp hw).2.1).mpr
      (isCompact_Icc.reProdIm isCompact_Icc)
  have hK : IsCompact ((fun z : ℍ ↦ D.scaling • z) ⁻¹' R) :=
    (Homeomorph.smul D.scaling).isCompact_preimage.mpr hR
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (K := {p})
    isCompact_singleton hK).subset ?_
  intro g hg
  refine ⟨g • p, ⟨⟨p, mem_singleton p, rfl⟩, ?_⟩⟩
  exact Complex.mem_reProdIm.mpr hg

/-- A single finite family of distance constraints defines the Dirichlet domain on every
horodisc of height at least `(D.scaling • p).im + D.width / 2`. This holds for every centre,
without cofiniteness or a trivial-centre-stabilizer assumption. -/
theorem exists_finset_dirichletDomain_inter_horodisc_eq (p : ℍ) :
    ∃ s : Finset Γ, ∀ A : ℝ, (D.scaling • p).im + D.width / 2 ≤ A →
      dirichletDomain Γ p ∩ horodisc D A =
        (⋂ g ∈ s, {z : ℍ | dist z p ≤ dist z (g • p)}) ∩ horodisc D A := by
  classical
  let P := D.scaling • p
  obtain ⟨S, -, hpS, M, hM⟩ := D.exists_isOpen_mem_forall_im_scaling_smul_smul_le p
  let T : Set Γ := {g | (D.scaling • g • p).re ∈ Icc (P.re - D.width) (P.re + D.width) ∧
    (D.scaling • g • p).im ∈ Icc (P.im / 2) M}
  have hT : T.Finite := D.finite_setOf_scaling_smul_mem_rectangle p (by dsimp [P]; positivity)
  let s := insert D.generator (insert D.generator⁻¹ hT.toFinset)
  refine ⟨s, fun A hA ↦ ?_⟩
  ext z
  simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_dirichletDomain]
  refine and_congr_left fun hzA ↦ ⟨fun hz g _ ↦ hz g, fun hz g ↦ ?_⟩
  let Z := D.scaling • z
  have hs (g : Γ) (hg : g ∈ s) : dist Z P ≤ dist Z (D.scaling • g • p) := by
    simpa only [Z, P, dist_smul] using hz g hg
  have hgen : dist Z P ≤ dist Z (D.width +ᵥ P) := by
    have hg : D.scaling • D.generator • p = D.width +ᵥ P := by
      simpa only [zpow_one, Int.cast_one, one_mul] using D.scaling_smul_generator_zpow 1 p
    simpa only [hg] using hs D.generator (by simp [s])
  have hinv : dist Z P ≤ dist Z ((-D.width) +ᵥ P) := by
    have hg : D.scaling • D.generator⁻¹ • p = (-D.width) +ᵥ P := by
      simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] using
        D.scaling_smul_generator_zpow (-1) p
    simpa only [hg] using hs D.generator⁻¹ (by simp [s])
  have hstrip : |Z.re - P.re| ≤ D.width / 2 :=
    (dist_le_dist_vadd_and_neg_vadd_iff D.width_pos Z P).mp ⟨hgen, hinv⟩
  have hhigh : P.im + D.width / 2 ≤ Z.im := hA.trans ((mem_horodisc D).mp hzA).le
  suffices dist Z P ≤ dist Z (D.scaling • g • p) by
    simpa only [Z, P, dist_smul] using this
  by_cases hlow : (D.scaling • g • p).im ≤ P.im / 2
  · exact TauCeti.UpperHalfPlane.dist_le_dist_of_im_le_half hstrip hhigh hlow
  -- Reduce a remaining orbit point to its nearest horizontal translate in the cusp strip.
  obtain ⟨n, hnre, hndist⟩ := exists_int_vadd_re_sub_le_and_dist_le D.width D.width_pos Z
    (D.scaling • g • p)
  let k : Γ := D.generator ^ n * g
  have hk : D.scaling • k • p = (n : ℝ) * D.width +ᵥ (D.scaling • g • p) := by
    simp only [k, mul_smul, D.scaling_smul_generator_zpow]
  have hkT : k ∈ T := by
    have hreal := abs_le.mp hstrip
    have hnreal := abs_le.mp hnre
    refine ⟨?_, ⟨?_, hM k p hpS⟩⟩
    · rw [hk, mem_Icc]
      constructor <;> dsimp only [Z] at * <;> linarith
    · rw [hk, vadd_im]
      exact (not_le.mp hlow).le
  have hkdist := hs k (by
    simp only [s, Finset.mem_insert]
    exact Or.inr (Or.inr (hT.mem_toFinset.mpr hkT)))
  exact hkdist.trans (by simpa only [hk, Int.cast_zero, zero_mul, zero_vadd] using hndist 0)

end TauCeti.Subgroup.CuspDatum
