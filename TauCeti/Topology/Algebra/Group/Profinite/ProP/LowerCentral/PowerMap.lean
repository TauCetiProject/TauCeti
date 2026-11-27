/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Uniform

/-!
# Power maps on the lower `p`-series

In a uniform pro-`p` group every element of the next term of the lower `p`-series has a unique
`p`-th root in the preceding term. The power map also detects membership in these terms.
The lifting uses the power operator on consecutive graded pieces and compactness.

## References

* Dixon, du Sautoy, Mann and Segal, *Analytic pro-p groups*, second edition, Lemma 4.10.
-/

public section

namespace TauCeti

open scoped Topology

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- In a uniform group, taking the `p`-th power advances membership in the lower
`p`-series by exactly one term. -/
theorem IsUniform.pow_mem_pLowerCentralSeries_succ_iff (hG : IsUniform p G)
    {n : ℕ} {x : G} :
    x ^ p ∈ pLowerCentralSeries p G (n + 1) ↔ x ∈ pLowerCentralSeries p G n := by
  refine ⟨?_, pow_mem_pLowerCentralSeries⟩
  induction n with
  | zero => exact fun _ ↦ mem_pLowerCentralSeries_zero p x
  | succ n ih =>
    intro hx
    have hx' := ih (pLowerCentralSeries_succ_le _ hx)
    let x' : pLowerCentralSeries p G n := ⟨x, hx'⟩
    have hz : gradedPow p G n (gradedMk p G n x') = 0 := by
      rw [gradedPow_gradedMk, gradedMk_eq_zero_iff]
      exact hx
    exact gradedMk_eq_zero_iff.mp ((hG.gradedPow_bijective n).injective
      (hz.trans (gradedPow_zero (p := p) (G := G) (k := n)).symm))

/-- The `p`-th power map on a uniform group is injective. Its injectivity on graded
pieces forces two putative roots to agree modulo every term of the lower `p`-series. -/
theorem IsUniform.pow_injective (hG : IsUniform p G) : Function.Injective (fun x : G ↦ x ^ p) := by
  intro x y hxy
  suffices ∀ n, x⁻¹ * y ∈ pLowerCentralSeries p G n by
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp
      (hG.isProP.iInf_pLowerCentralSeries_eq_bot hp.out ▸ Subgroup.mem_iInf.mpr this))
  intro n
  induction n with
  | zero => exact mem_pLowerCentralSeries_zero p _
  | succ n ih =>
    let w : pLowerCentralSeries p G n := ⟨x⁻¹ * y, ih⟩
    have he : (x * (w : G)) ^ p = x ^ p := by simpa [w] using hxy.symm
    have hm := hG.isPowerful.mk_mul_pow hp.out
      (hG.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries hp.out _) x w.property
    rw [he] at hm
    simp only [← QuotientGroup.mk'_apply, map_mul, left_eq_mul] at hm
    have hw : (w : G) ^ p ∈ pLowerCentralSeries p G (n + 1 + 1) :=
      (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using hm)
    exact hG.pow_mem_pLowerCentralSeries_succ_iff.mp hw

/-- The `p`-th power map gives a homeomorphism between consecutive terms of the lower
`p`-series of a uniform group. -/
noncomputable def IsUniform.powHomeomorph (hG : IsUniform p G) (n : ℕ) :
    pLowerCentralSeries p G n ≃ₜ pLowerCentralSeries p G (n + 1) := by
  let f (x : pLowerCentralSeries p G n) : pLowerCentralSeries p G (n + 1) :=
    ⟨(x : G) ^ p, pow_mem_pLowerCentralSeries x.property⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h ↦ Subtype.ext (hG.pow_injective (congrArg Subtype.val h)), ?_⟩
    intro x
    have hx : ((1 : G) ^ p)⁻¹ * x ∈ pLowerCentralSeries p G (n + 1) := by
      simpa only [one_pow, inv_one, one_mul] using x.property
    obtain ⟨y, hy, hyx⟩ := hG.isPowerful.exists_pow_eq_of_inv_mul_mem_pLowerCentralSeries_succ
      hp.out hG.isProP hG.isTopologicallyFinitelyGenerated hx
    exact ⟨⟨y, by simpa only [inv_one, one_mul] using hy⟩, Subtype.ext hyx⟩
  letI : CompactSpace (pLowerCentralSeries p G n) :=
    isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries n).isCompact
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    ((continuous_subtypeVal.pow p).subtype_mk _)

@[simp]
theorem IsUniform.coe_powHomeomorph_apply (hG : IsUniform p G) (n : ℕ)
    (x : pLowerCentralSeries p G n) : (hG.powHomeomorph n x : G) = (x : G) ^ p :=
  (rfl)

/-- The inverse of the power homeomorphism takes the `p`-th root in the preceding term. -/
@[simp]
theorem IsUniform.coe_powHomeomorph_symm_apply_pow (hG : IsUniform p G) (n : ℕ)
    (x : pLowerCentralSeries p G (n + 1)) : ((hG.powHomeomorph n).symm x : G) ^ p = x := by
  rw [← hG.coe_powHomeomorph_apply, Homeomorph.apply_symm_apply]

end TauCeti
