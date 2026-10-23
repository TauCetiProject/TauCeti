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
import TauCeti.Topology.MetricSpace.IsometricSMul

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

The same comparison controls the translates of a high horodisc at the cusp. If `g • y`, with `y`
high above the cusp, lies in the Dirichlet domain of `p`, then `g⁻¹ • p` cannot be much lower than
`p` above the cusp, so `g` lies in finitely many cosets of the cusp stabilizer. Hence a Dirichlet
domain meets only finitely many translates of a high horodisc, and its part in all translates of
a lower horodisc consists of those finitely many horodiscs together with a bounded set. Combined
with the description of the thin part of a cusp stabilizer as a horodisc
(`TauCeti.Subgroup.CuspDatum.mem_horodisc_iff_exists_dist_smul_lt`), this confines the points of
a Dirichlet domain moved a short distance by a parabolic element fixing a cusp `Γ`-equivalent to
that of the datum to finitely many horodiscs and a bounded set.

## Main results

In the following, all names are in the namespace `TauCeti.Subgroup`.

* `CuspDatum.exists_finset_dirichletDomain_inter_horodisc_eq`: finitely many distance constraints
  describe the Dirichlet domain on a high horodisc.
* `CuspDatum.exists_finset_dirichletDomain_inter_iUnion_smul_horodisc_subset`: only finitely many
  translates of a high horodisc meet a Dirichlet domain.
* `CuspDatum.exists_finset_isBounded_dirichletDomain_inter_iUnion_smul_horodisc_diff`: away from
  finitely many high horodiscs, the part of a Dirichlet domain in the translates of any horodisc
  is bounded.
* `CuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff`: away from
  finitely many high horodiscs, the points of a Dirichlet domain moved a short distance by a
  parabolic element fixing a cusp equivalent to that of the datum form a bounded set.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §§3.2 and 4.2.

We use the orbit-height bound
`TauCeti.Subgroup.CuspDatum.exists_isOpen_mem_forall_im_scaling_smul_smul_le`, the hyperbolic
cosine distance formula, and Mathlib's proper-discontinuity finiteness theorem.
-/

public section

open MulAction Set UpperHalfPlane TauCeti
open TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups Pointwise

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

/-- The points whose scaled coordinates lie in a closed rectangle of positive height form a
compact set. -/
private theorem isCompact_setOf_scaling_smul_mem_rectangle {a b c d : ℝ} (hc : 0 < c) :
    IsCompact {z : ℍ | (D.scaling • z).re ∈ Icc a b ∧ (D.scaling • z).im ∈ Icc c d} := by
  have hR : IsCompact (((↑) : ℍ → ℂ) ⁻¹' (Icc a b ×ℂ Icc c d)) :=
    (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff fun w hw ↦ by
      rw [range_coe]
      exact hc.trans_le (Complex.mem_reProdIm.mp hw).2.1).mpr
      (isCompact_Icc.reProdIm isCompact_Icc)
  exact (Homeomorph.smul D.scaling).isCompact_preimage.mpr hR

/-- The part of a Dirichlet domain between two cusp heights is bounded, provided the lower
height is positive. The upper height is arbitrary, and the band may be empty. -/
theorem isBounded_dirichletDomain_inter_horodisc_diff (p : ℍ) {A : ℝ} (hA : 0 < A)
    (B : ℝ) :
    Bornology.IsBounded (sdiff (dirichletDomain Γ p ∩ D.horodisc A) (D.horodisc B)) := by
  refine (D.isCompact_setOf_scaling_smul_mem_rectangle (a := (D.scaling • p).re - D.width / 2)
    (b := (D.scaling • p).re + D.width / 2) (d := B) hA).isBounded.subset ?_
  rintro z ⟨⟨hz, hzA⟩, hzB⟩
  have hre := abs_le.mp (D.abs_re_scaling_smul_sub_le hz)
  exact ⟨⟨by linarith, by linarith⟩, ((D.mem_horodisc).mp hzA).le,
    not_lt.mp (by simpa only [D.mem_horodisc] using hzB)⟩

/-- The points of a Dirichlet domain lying in some `Γ`-translate of the band between two cusp
heights form a bounded set, provided the lower height is positive. -/
theorem isBounded_dirichletDomain_inter_iUnion_smul_horodisc_diff (p : ℍ) {A : ℝ} (hA : 0 < A)
    (B : ℝ) :
    Bornology.IsBounded
      (dirichletDomain Γ p ∩ ⋃ g : Γ, g • sdiff (D.horodisc A) (D.horodisc B)) := by
  refine (isBounded_dirichletDomain_inter_iUnion_smul (G := Γ) p
    (D.isCompact_setOf_scaling_smul_mem_rectangle (a := -(D.width / 2)) (b := D.width / 2)
      (d := B) hA).isBounded).subset ?_
  rintro x ⟨hx, hxu⟩
  refine ⟨hx, ?_⟩
  obtain ⟨g, y, ⟨hyA, hyB⟩, rfl⟩ := mem_iUnion.mp hxu
  -- translate `y` by the cusp stabilizer into the strip of width `D.width` about `re = 0`
  obtain ⟨n, hn, -⟩ :=
    exists_int_vadd_re_sub_le_and_dist_le D.width D.width_pos UpperHalfPlane.I (D.scaling • y)
  rw [I_re, zero_sub, abs_neg] at hn
  refine mem_iUnion.mpr ⟨g * D.generator ^ (-n), D.generator ^ n • y, ⟨?_, ?_⟩, ?_⟩
  · rw [D.scaling_smul_generator_zpow]
    exact abs_le.mp hn
  · rw [D.scaling_smul_generator_zpow, vadd_im]
    exact ⟨((D.mem_horodisc).mp hyA).le, not_lt.mp (by simpa only [D.mem_horodisc] using hyB)⟩
  · simp only [mul_smul, zpow_neg, inv_smul_smul]

variable [DiscreteTopology Γ]

private theorem finite_setOf_scaling_smul_mem_rectangle (p : ℍ) {a b c d : ℝ} (hc : 0 < c) :
    {g : Γ | (D.scaling • g • p).re ∈ Icc a b ∧
      (D.scaling • g • p).im ∈ Icc c d}.Finite :=
  (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (K := {p}) isCompact_singleton
    (D.isCompact_setOf_scaling_smul_mem_rectangle (a := a) (b := b) (d := d) hc)).subset
    fun g hg ↦ ⟨g • p, ⟨p, mem_singleton p, rfl⟩, hg⟩

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

/-- **Finitely many translates of a high horodisc meet a Dirichlet domain.** For a discrete `Γ`,
a cusp datum `D` and any centre `p`, there is a finite set `s ⊆ Γ` such that, at every height
`A ≥ (D.scaling • p).im + D.width / 2`, every point of the Dirichlet domain lying in some
`Γ`-translate of the horodisc of height `A` already lies in a translate by an element of `s`. -/
theorem exists_finset_dirichletDomain_inter_iUnion_smul_horodisc_subset (p : ℍ) :
    ∃ s : Finset Γ, ∀ A : ℝ, (D.scaling • p).im + D.width / 2 ≤ A →
      dirichletDomain Γ p ∩ ⋃ g : Γ, g • horodisc D A ⊆ ⋃ g ∈ s, g • horodisc D A := by
  classical
  let P := D.scaling • p
  obtain ⟨S, -, hpS, M, hM⟩ := D.exists_isOpen_mem_forall_im_scaling_smul_smul_le p
  let T : Set Γ := {t | (D.scaling • t • p).re ∈ Icc (P.re - D.width / 2) (P.re + D.width / 2) ∧
    (D.scaling • t • p).im ∈ Icc (P.im / 2) M}
  have hT : T.Finite := D.finite_setOf_scaling_smul_mem_rectangle p (by dsimp [P]; positivity)
  refine ⟨hT.toFinset.image (·⁻¹), fun A hA x ⟨hx, hxA⟩ ↦ ?_⟩
  obtain ⟨g, y, hy, rfl⟩ := mem_iUnion.mp hxA
  let Y := D.scaling • y
  let Q := D.scaling • g⁻¹ • p
  -- the Dirichlet inequalities at `g • y`, in the scaling coordinate of the cusp
  have hdir (k : Γ) : dist Y Q ≤ dist Y (D.scaling • k • p) := by
    have e (q : ℍ) : dist (g • y) q = dist y (g⁻¹ • q) := by
      rw [← dist_smul g⁻¹, inv_smul_smul]
    have h := mem_dirichletDomain.mp hx (g * k)
    rw [e, e, mul_smul, inv_smul_smul] at h
    simpa only [Y, Q, dist_smul] using h
  -- `y` is at least as close to `g⁻¹ • p` as to the translate of `p` horizontally nearest to it,
  -- so `g⁻¹ • p` is not much lower than `p` above the cusp
  obtain ⟨n, hn, -⟩ := exists_int_vadd_re_sub_le_and_dist_le D.width D.width_pos Y P
  have hQ : P.im / 2 ≤ Q.im := by
    by_contra hlt
    have hY : ((n : ℝ) * D.width +ᵥ P).im + D.width / 2 ≤ Y.im := by
      rw [vadd_im]
      exact hA.trans ((D.mem_horodisc).mp hy).le
    have h := hdir (D.generator ^ n)
    rw [D.scaling_smul_generator_zpow] at h
    have hlow : Q.im < ((n : ℝ) * D.width +ᵥ P).im / 2 := by
      rw [vadd_im]
      exact not_le.mp hlt
    exact (h.trans_lt (TauCeti.UpperHalfPlane.dist_lt_dist_of_im_lt_half hn hY hlow)).false
  -- translate `g⁻¹ • p` by the cusp stabilizer into the strip about `P`; Shimizu's lemma bounds
  -- the heights of the orbit, so the result lies in a compact rectangle
  obtain ⟨m, hm, -⟩ := exists_int_vadd_re_sub_le_and_dist_le D.width D.width_pos P Q
  have ht : D.generator ^ m * g⁻¹ ∈ T := by
    have e : D.scaling • (D.generator ^ m * g⁻¹) • p = (m : ℝ) * D.width +ᵥ Q := by
      rw [mul_smul, D.scaling_smul_generator_zpow]
    have hre := abs_le.mp hm
    rw [mem_ofPred_eq, e, vadd_im]
    exact ⟨⟨by linarith, by linarith⟩, hQ, hM g⁻¹ p hpS⟩
  refine mem_iUnion₂.mpr ⟨(D.generator ^ m * g⁻¹)⁻¹,
    Finset.mem_image_of_mem _ (hT.mem_toFinset.mpr ht), ?_⟩
  rw [mul_inv_rev, inv_inv, mul_smul,
    smul_horodisc_of_mem_stabilizer D (inv_mem (zpow_mem D.generator_mem_stabilizer m))]
  exact smul_mem_smul_set hy

/-- **The cusp ends of a Dirichlet domain.** For a discrete `Γ`, a cusp datum `D` and any centre
`p`, there is a finite set `s ⊆ Γ` such that, at every height
`A ≥ (D.scaling • p).im + D.width / 2` and every positive height `B`, the points of the Dirichlet
domain lying in a `Γ`-translate of the horodisc of height `B` lie in the translates of the horodisc
of height `A` by elements of `s`, apart from a bounded set.

By `TauCeti.Subgroup.CuspDatum.horodisc_conj`, each translate `g • horodisc D A` is the horodisc
of height `A` of the conjugate cusp datum at `g • D.cusp`. -/
theorem exists_finset_isBounded_dirichletDomain_inter_iUnion_smul_horodisc_diff (p : ℍ) :
    ∃ s : Finset Γ, ∀ A : ℝ, (D.scaling • p).im + D.width / 2 ≤ A → ∀ B : ℝ, 0 < B →
      Bornology.IsBounded (sdiff (dirichletDomain Γ p ∩ ⋃ g : Γ, g • horodisc D B)
        (⋃ g ∈ s, g • horodisc D A)) := by
  obtain ⟨s, hs⟩ := D.exists_finset_dirichletDomain_inter_iUnion_smul_horodisc_subset p
  refine ⟨s, fun A hA B hB ↦
    (D.isBounded_dirichletDomain_inter_iUnion_smul_horodisc_diff p hB A).subset ?_⟩
  rintro x ⟨⟨hx, hxB⟩, hxs⟩
  obtain ⟨g, y, hy, rfl⟩ := mem_iUnion.mp hxB
  exact ⟨hx, mem_iUnion.mpr ⟨g, y, ⟨hy, fun hyA ↦
    hxs (hs A hA ⟨hx, mem_iUnion.mpr ⟨g, smul_mem_smul_set hyA⟩⟩)⟩, rfl⟩⟩

/-- **The parabolic thin part of a Dirichlet domain.** For a discrete `Γ`, a cusp datum `D`, any
centre `p` and `ε > 0`, there is a finite set `s ⊆ Γ` such that, at every height
`A ≥ (D.scaling • p).im + D.width / 2`, the points of the Dirichlet domain moved less than `ε` by a
nonidentity element of `Γ` fixing a cusp `Γ`-equivalent to that of `D` lie in the translates of the
horodisc of height `A` by elements of `s`, apart from a bounded set. -/
theorem exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff (p : ℍ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : Finset Γ, ∀ A : ℝ, (D.scaling • p).im + D.width / 2 ≤ A →
      Bornology.IsBounded (sdiff (dirichletDomain Γ p ∩
        {x | ∃ γ : Γ, ∃ g ∈ stabilizer Γ (γ • D.cusp), g ≠ 1 ∧ dist (g • x) x < ε})
        (⋃ g ∈ s, g • horodisc D A)) := by
  obtain ⟨s, hs⟩ := D.exists_finset_isBounded_dirichletDomain_inter_iUnion_smul_horodisc_diff p
  have hB : 0 < D.width / (2 * Real.sinh (ε / 2)) :=
    div_pos D.width_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr (half_pos hε)))
  refine ⟨s, fun A hA ↦ (hs A hA _ hB).subset ?_⟩
  rintro x ⟨⟨hx, γ, g, hg, hg1, hgx⟩, hxs⟩
  refine ⟨⟨hx, mem_iUnion.mpr ⟨γ, γ⁻¹ • x, ?_, smul_inv_smul γ x⟩⟩, hxs⟩
  -- conjugating `g` by `γ` gives a nonidentity element of the stabilizer of the cusp of `D`
  refine (D.mem_horodisc_iff_exists_dist_smul_lt hε _).mpr ⟨γ⁻¹ * g * γ, ?_, fun h ↦ hg1 ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hg,
      inv_smul_smul]
  · calc g = γ * (γ⁻¹ * g * γ) * γ⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rwa [mul_smul, mul_smul, smul_inv_smul, dist_smul]

end TauCeti.Subgroup.CuspDatum
