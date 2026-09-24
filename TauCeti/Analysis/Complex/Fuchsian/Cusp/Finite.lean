/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc

/-!
# A cofinite Fuchsian group has finitely many cusp orbits

Let `D` be a normalized cusp datum of a discrete `Γ ≤ PSL(2, ℝ)`, with scaling `σ` and width `w`.
The *horodisc strip* of height `A` is the part of the horodisc of height `A` lying over one
period: the set of `z` with `0 ≤ re (σ • z) < w` and `A < im (σ • z)`. Its hyperbolic area is
`w / A`; in particular the strip of height `w` has area exactly `1`.

Once the height is at least the width, the translates of a horodisc strip by the elements of `Γ`
are pairwise disjoint: two translates can only meet through an element of the cusp stabilizer, by
the precise invariance of high horodiscs, and a nontrivial element of the stabilizer shifts
`re (σ • z)` by a nonzero multiple of `w`. Strips at two inequivalent cusps have disjoint
translates as well, by Shimizu's inequality at two cusps.

Consequently, choosing one strip of height equal to the width for each cusp orbit produces a
family of sets of area `1` whose translates are pairwise disjoint, and a fundamental domain of `Γ`
has at least as much area as their union. Hence the number of cusp orbits is at most the covolume
(`Subgroup.card_cuspOrbit_le_covolume`), and a cofinite Fuchsian group has only finitely many cusp
orbits (`Subgroup.IsCofinite.finite_cuspOrbit`).

## Main results

* `TauCeti.Subgroup.CuspDatum.volume_horodiscStrip`: the horodisc strip of height `A` has area
  `w / A`.
* `TauCeti.Subgroup.CuspDatum.pairwise_disjoint_smul_horodiscStrip`: for a height at least the
  width, the `Γ`-translates of a horodisc strip are pairwise disjoint.
* `TauCeti.Subgroup.CuspDatum.disjoint_smul_horodiscStrip_smul_horodiscStrip`: the translates
  of strips at two inequivalent cusps are disjoint.
* `Subgroup.card_cuspOrbit_le_covolume`: the number of cusp orbits of a discrete `Γ` is at most
  its covolume.
* `Subgroup.IsCofinite.finite_cuspOrbit`: a cofinite Fuchsian group has finitely many cusp orbits.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§4.1–4.2.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.2 and 10.4.
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : _root_.Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- The horodisc strip of height `A` at the cusp represented by `D`: the part of the horodisc of
height `A` lying over one period `[0, width)` in the scaling coordinate. -/
def horodiscStrip (A : ℝ) : Set ℍ :=
  {z | (D.scaling • z).re ∈ Ico 0 D.width ∧ A < (D.scaling • z).im}

/-- Membership in a horodisc strip is a bound on the real part and a lower bound on the imaginary
part in the scaling coordinate. -/
@[simp]
theorem mem_horodiscStrip {A : ℝ} {z : ℍ} :
    z ∈ horodiscStrip D A ↔ (D.scaling • z).re ∈ Ico 0 D.width ∧ A < (D.scaling • z).im :=
  Iff.rfl

/-- A horodisc strip lies in the horodisc of the same height. -/
theorem horodiscStrip_subset_horodisc (A : ℝ) : horodiscStrip D A ⊆ horodisc D A :=
  fun _ hz ↦ (mem_horodisc D).mpr hz.2

/-- The horodisc strip is the image under `σ⁻¹` of the region over `[0, width)` above height `A`. -/
theorem horodiscStrip_eq_inv_smul (A : ℝ) :
    horodiscStrip D A = D.scaling⁻¹ • {z : ℍ | z.re ∈ Ico 0 D.width ∧ A < z.im} := by
  ext z
  rw [mem_inv_smul_set_iff, mem_horodiscStrip, mem_ofPred_eq]

/-- A horodisc strip is measurable. -/
theorem measurableSet_horodiscStrip (A : ℝ) : MeasurableSet (horodiscStrip D A) := by
  rw [horodiscStrip_eq_inv_smul]
  exact ((measurableSet_Ico.preimage continuous_re.measurable).inter
    (measurableSet_Ioi.preimage continuous_im.measurable)).const_smul _

/-- **The area of a horodisc strip.** The horodisc strip of height `A > 0` has hyperbolic area
`width / A`. -/
theorem volume_horodiscStrip {A : ℝ} (hA : 0 < A) :
    volume (horodiscStrip D A) = ENNReal.ofReal (D.width / A) := by
  rw [horodiscStrip_eq_inv_smul, measure_smul, volume_setOf_re_mem_Ico_and_lt_im 0 D.width hA,
    sub_zero]

/-- The horodisc strip whose height is the width has hyperbolic area `1`. -/
@[simp]
theorem volume_horodiscStrip_width : volume (horodiscStrip D D.width) = 1 := by
  rw [volume_horodiscStrip D D.width_pos, div_self D.width_pos.ne', ENNReal.ofReal_one]

/-- **The translates of a high horodisc strip are pairwise disjoint.** Let `D` be a normalized
cusp datum of a discrete `Γ ≤ PSL(2, ℝ)` and let the height `A` be at least the width of `D`. Then
the translates of the horodisc strip of height `A` by distinct elements of `Γ` are disjoint. -/
theorem pairwise_disjoint_smul_horodiscStrip [DiscreteTopology Γ] {A : ℝ} (hA : D.width ≤ A) :
    Pairwise fun g h : Γ ↦ Disjoint (g • horodiscStrip D A) (h • horodiscStrip D A) := by
  intro g h hgh
  by_cases hs : g⁻¹ * h ∈ stabilizer Γ D.cusp
  · -- `g⁻¹ * h` is a power of the generator, which shifts `re (σ • z)` by a multiple of the width
    obtain ⟨n, hn⟩ := D.mem_stabilizer_iff.mp hs
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨y, hy, hyz⟩
    replace hyz : h • y = g • z := hyz
    have hzy : z = D.generator ^ n • y := by rw [hn, mul_smul, hyz, inv_smul_smul]
    rw [mem_horodiscStrip, hzy, scaling_smul_generator_zpow, vadd_re] at hz
    rw [mem_horodiscStrip] at hy
    have h1 : (n : ℝ) * D.width < 1 * D.width := by linarith [hz.1.2, hy.1.1]
    have h2 : (-1 : ℝ) * D.width < n * D.width := by linarith [hz.1.1, hy.1.2]
    have hn1 : (n : ℝ) < 1 := lt_of_mul_lt_mul_right h1 D.width_pos.le
    have hn2 : (-1 : ℝ) < n := lt_of_mul_lt_mul_right h2 D.width_pos.le
    obtain rfl : n = 0 := by
      have : n < 1 := by exact_mod_cast hn1
      have : -1 < n := by exact_mod_cast hn2
      omega
    rw [zpow_zero, eq_comm, inv_mul_eq_one] at hn
    exact hgh hn
  · exact (disjoint_smul_horodisc D hA hs).mono
      (smul_set_mono (horodiscStrip_subset_horodisc D A))
      (smul_set_mono (horodiscStrip_subset_horodisc D A))

/-- **Horodisc strips at inequivalent cusps have disjoint translates.** Let `D` and `D'` be
normalized cusp data of a discrete `Γ ≤ PSL(2, ℝ)` whose cusps are not `Γ`-equivalent, and let the
heights satisfy `0 ≤ A` and `D.width * D'.width ≤ A * A'`. Then every translate of the strip at
`D` is disjoint from every translate of the strip at `D'`. -/
theorem disjoint_smul_horodiscStrip_smul_horodiscStrip [DiscreteTopology Γ] (D' : Γ.CuspDatum)
    (hc : D'.cusp ∉ orbit Γ D.cusp) {A A' : ℝ} (hA : 0 ≤ A)
    (hAA' : D.width * D'.width ≤ A * A')
    (g h : Γ) : Disjoint (g • horodiscStrip D A) (h • horodiscStrip D' A') := by
  have hA' : 0 ≤ A' := (pos_of_mul_pos_right
    ((mul_pos D.width_pos D'.width_pos).trans_le hAA') hA).le
  have hdisj := disjoint_smul_horodisc_horodisc D' D (A := A') (A' := A) hA'
    (by simpa only [mul_comm] using hAA') (g := h⁻¹ * g)
    fun h' ↦ hc (mem_orbit_iff.mpr ⟨_, h'⟩)
  rw [← disjoint_smul_set (a := h⁻¹), smul_smul, inv_smul_smul]
  exact hdisj.mono (smul_set_mono (horodiscStrip_subset_horodisc D A))
    (horodiscStrip_subset_horodisc D' A')

end TauCeti.Subgroup.CuspDatum

namespace Subgroup

open TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- A finite set of cusp orbits of a discrete `Γ` has at most as many elements as the covolume of
`Γ`: its horodisc strips of height equal to the width have area `1` each and pairwise disjoint
translates. -/
private theorem card_finset_cuspOrbit_le_covolume [DiscreteTopology Γ] (s : Finset Γ.CuspOrbit) :
    (s.card : ℝ≥0∞) ≤ covolume Γ ℍ := by
  -- choose a cusp datum at a representative of each cusp orbit
  have hex : ∀ C : Γ.CuspOrbit, ∃ D : Γ.CuspDatum,
      Γ.cuspOrbitMk ⟨D.cusp, mem_cuspPoints.mpr D.isCuspPoint⟩ = C := by
    intro C
    obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
    obtain ⟨D, hD⟩ := (mem_cuspPoints.mp c.2).exists_cuspDatum_cusp_eq
    exact ⟨D, by simp only [hD]⟩
  choose D hD using hex
  have hne : ∀ C C' : Γ.CuspOrbit, C ≠ C' → (D C').cusp ∉ orbit Γ (D C).cusp := by
    intro C C' hCC' hc
    refine hCC' ?_
    rw [← hD C, ← hD C', cuspOrbitMk_eq_iff]
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hc
    exact mem_orbit_iff.mpr ⟨g⁻¹, by simp [← hg]⟩
  set t := ⋃ C ∈ s, horodiscStrip (D C) (D C).width
  have hdisj : ∀ g h : Γ, ∀ C C' : Γ.CuspOrbit, (g, C) ≠ (h, C') →
      Disjoint (g • horodiscStrip (D C) (D C).width) (h • horodiscStrip (D C') (D C').width) := by
    intro g h C C' hne'
    by_cases hCC' : C = C'
    · subst hCC'
      exact pairwise_disjoint_smul_horodiscStrip _ le_rfl fun hgh ↦ hne' (by rw [hgh])
    · exact disjoint_smul_horodiscStrip_smul_horodiscStrip _ _ (hne C C' hCC')
        (D C).width_pos.le le_rfl g h
  obtain ⟨F, -, -, hF⟩ := exists_isFundamentalDomain Γ
  have ht : volume t = s.card := by
    rw [measure_biUnion_finset (fun C _ C' _ hCC' ↦ by
        simpa using hdisj 1 1 C C' (by simpa using hCC'))
      fun C _ ↦ measurableSet_horodiscStrip _ _]
    simp
  rw [← ht, hF.covolume_eq_volume]
  refine hF.measure_le_of_pairwise_disjoint
    (s.measurableSet_biUnion fun C _ ↦ measurableSet_horodiscStrip _ _).nullMeasurableSet
    fun g h hgh ↦ Disjoint.aedisjoint ?_
  refine Disjoint.mono inter_subset_left inter_subset_left ?_
  simp only [t, smul_set_iUnion₂, disjoint_iUnion₂_left, disjoint_iUnion₂_right]
  intro C _ C' _
  exact hdisj g h _ _ fun h' ↦ hgh (congrArg Prod.fst h')

/-- **The number of cusp orbits is at most the covolume.** For a discrete subgroup
`Γ ≤ PSL(2, ℝ)`, the cardinality of the set of cusp orbits is at most the hyperbolic area of the
quotient `Γ \ ℍ`. -/
theorem card_cuspOrbit_le_covolume [DiscreteTopology Γ] :
    (ENat.card Γ.CuspOrbit : ℝ≥0∞) ≤ covolume Γ ℍ := by
  cases finite_or_infinite Γ.CuspOrbit with
  | inl _ =>
    have := Fintype.ofFinite Γ.CuspOrbit
    simpa [ENat.card_eq_coe_fintype_card] using card_finset_cuspOrbit_le_covolume Finset.univ
  | inr _ =>
    rw [ENat.card_eq_top_of_infinite, ENat.toENNReal_top, top_le_iff]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge r
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Γ.CuspOrbit n
    refine le_trans ?_ (card_finset_cuspOrbit_le_covolume s)
    rw [hs]
    exact_mod_cast hn

/-- **A cofinite Fuchsian group has finitely many cusp orbits.** -/
theorem IsCofinite.finite_cuspOrbit (hΓ : Γ.IsCofinite) : Finite Γ.CuspOrbit := by
  have := hΓ.discreteTopology
  rw [← ENat.card_lt_top]
  have h := (card_cuspOrbit_le_covolume (Γ := Γ)).trans_lt hΓ.covolume_ne_top.lt_top
  exact_mod_cast h

end Subgroup
