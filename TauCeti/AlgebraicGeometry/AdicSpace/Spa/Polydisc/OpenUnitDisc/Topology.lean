/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.AlgebraicGeometry.AdicSpace.Cont.DominatingUnit
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The open unit disc is not quasi-compact

For any scalar `c`, `discExhaustion c n` is the subset `|T|^(n+1) ≤ |c| ≠ 0` of the
closed unit disc, and `discExhaustionUnion c` is their increasing open union. For a
pseudouniformiser `c`, this union is the underlying open unit disc. Over `ℚ_[p]`, taking
`c = p` gives the usual exhaustion. This file constructs subsets and proves topological
properties; it does not construct their coordinate rings or their adic-space structures.

Over an ultrametric normed field, for `c ≠ 0` and `‖c‖ < 1`, the Gauss points in the union
are exactly those of radii `0 < r < 1`. Every compact subset is contained in one exhaustion
member, but Gauss points with radii sufficiently close to one escape that member.
Consequently the union is not quasi-compact and cannot be homeomorphic to an affinoid
adic spectrum.

The construction uses valuation inequalities, not real-valued radii for arbitrary points.
The real radius is used only for the existing Gauss points. Independence of the choice of
pseudouniformiser follows from continuity and power comparability. No completeness
assumption is needed for these topological statements.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §9.1, for the open unit disc.

The non-quasi-compactness argument uses `gaussPoint` and its valuation computation rules.
-/

public section

open Filter Topology

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section TopologicalRing

variable {K : Type*} [CommRing K] [TopologicalSpace K] [NonarchimedeanRing K]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-- The `n`-th rational subset `|T|^(n+1) ≤ |c| ≠ 0` of the closed unit disc. -/
def discExhaustion (c : K) (n : ℕ) : Set (closedPolydisc 1 K) :=
  Subtype.val ⁻¹' basicOpen (T ^ (n + 1)) (C c)

/-- Membership in an exhaustion disc is the defining valuation inequality and nonvanishing. -/
@[simp]
theorem mem_discExhaustion (c : K) (n : ℕ) (v : closedPolydisc 1 K) :
    v ∈ discExhaustion c n ↔
      v.1.toValuativeRel.vle (T ^ (n + 1)) (C c) ∧ ¬ v.1.toValuativeRel.vle (C c) 0 := by
  rw [discExhaustion, Set.mem_preimage, mem_basicOpen_iff]

/-- Each exhaustion disc is open in the closed unit disc. -/
theorem isOpen_discExhaustion (c : K) (n : ℕ) : IsOpen (discExhaustion c n) :=
  (isOpen_basicOpen _ _).preimage continuous_subtype_val

open scoped Classical in
/-- The exhaustion disc is the rational subset with numerators `T^(n+1), c` and denominator
`c`. Including the denominator among the numerators makes its unit-ideal admissibility explicit. -/
theorem discExhaustion_eq_rationalSubset (c : K) (n : ℕ) :
    discExhaustion c n = Subtype.val ⁻¹'
      rationalSubset (powerBoundedSubring 𝒯) {T ^ (n + 1), C c} (C c) := by
  classical
  ext v
  rw [mem_discExhaustion, Set.mem_preimage, mem_rationalSubset_iff]
  have hv : v.1 ∈ spa (powerBoundedSubring 𝒯) := closedPolydisc_def 1 K ▸ v.2
  simp [hv]

/-- Exhaustion discs with unit denominator are quasi-compact over a Huber ring. -/
theorem isCompact_discExhaustion [IsHuberRing K] {c : K} (hc : IsUnit c) (n : ℕ) :
    IsCompact (discExhaustion c n) := by
  classical
  have hunit : IsUnit (C c) := hc.map C
  have hspan : Ideal.span (({T ^ (n + 1), C c} : Finset 𝒯) : Set 𝒯) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hunit
  have hcompact := isCompact_of_mem_spaRationalFamily (Aplus := powerBoundedSubring 𝒯)
    (mem_spaRationalFamily_iff.mpr ⟨{T ^ (n + 1), C c}, C c, by rw [hspan]; simp, rfl⟩)
  rw [discExhaustion_eq_rationalSubset]
  exact (Homeomorph.setCongr (closedPolydisc_def 1 K)).isClosedEmbedding.isCompact_preimage
    hcompact

/-- The rational subsets in the exhaustion increase with their index. -/
theorem monotone_discExhaustion (c : K) : Monotone (discExhaustion c) := by
  intro n m hnm v hv
  let : ValuativeRel 𝒯 := v.1.toValuativeRel
  rw [mem_discExhaustion] at hv ⊢
  have hT : v.1.toValuativeRel.vle T 1 :=
    ((mem_closedPolydisc_iff 1 K v.1).mp v.2).2 T
      (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0))
  exact ⟨(ValuativeRel.pow_vle_pow_of_vle_one hT (Nat.add_le_add_right hnm 1)).trans hv.1,
    hv.2⟩

/-- The union of the rational subsets `|T|^(n+1) ≤ |c| ≠ 0`. For a pseudouniformiser `c`,
this is the underlying open unit disc; the definition allows arbitrary scalars. -/
def discExhaustionUnion (c : K) : Set (closedPolydisc 1 K) := ⋃ n, discExhaustion c n

/-- The exhaustion union is the union of its rational subsets. -/
theorem discExhaustionUnion_eq_iUnion (c : K) :
    discExhaustionUnion c = ⋃ n, discExhaustion c n := (rfl)

/-- A point lies in the exhaustion union exactly when some positive power of its coordinate
is dominated by the nonvanishing scalar `c`. -/
@[simp]
theorem mem_discExhaustionUnion (c : K) (v : closedPolydisc 1 K) :
    v ∈ discExhaustionUnion c ↔ ∃ n, v ∈ discExhaustion c n := by
  rw [discExhaustionUnion_eq_iUnion, Set.mem_iUnion]

/-- The exhaustion union is open in the closed unit disc. -/
theorem isOpen_discExhaustionUnion (c : K) : IsOpen (discExhaustionUnion c) := by
  rw [discExhaustionUnion_eq_iUnion]
  exact isOpen_iUnion (isOpen_discExhaustion c)

/-- Every compact subset of the exhaustion union lies in one rational exhaustion subset. -/
theorem exists_subset_discExhaustion_of_isCompact {c : K}
    {S : Set (closedPolydisc 1 K)} (hS : IsCompact S) (hSc : S ⊆ discExhaustionUnion c) :
    ∃ n, S ⊆ discExhaustion c n :=
  hS.elim_directed_cover _ (isOpen_discExhaustion c)
    (by rwa [← discExhaustionUnion_eq_iUnion]) (monotone_discExhaustion c).directed_le

/-- Changing the pseudouniformiser does not change the open unit disc. -/
theorem discExhaustionUnion_eq_of_isPseudoUniformizer {c d : K}
    (hc : IsPseudoUniformizer c) (hd : IsPseudoUniformizer d) :
    discExhaustionUnion c = discExhaustionUnion d := by
  suffices h : ∀ {a b : K}, IsPseudoUniformizer a → IsPseudoUniformizer b →
      discExhaustionUnion a ⊆ discExhaustionUnion b from Set.Subset.antisymm (h hc hd) (h hd hc)
  intro a b ha hb v hv
  obtain ⟨n, hn⟩ := (mem_discExhaustionUnion a v).mp hv
  rw [mem_discExhaustion] at hn
  have hcont := ((mem_closedPolydisc_iff 1 K v.1).mp v.2).1
  have haNil : IsTopologicallyNilpotent (C a) :=
    ha.isTopologicallyNilpotent.map (continuous_weightedC isWeightFamily_one_weight)
  have hbNil : IsTopologicallyNilpotent (C b) :=
    hb.isTopologicallyNilpotent.map (continuous_weightedC isWeightFamily_one_weight)
  have hbSupp : C b ∉ v.1.supp := v.1.supp.notMem_of_isUnit (hb.isUnit.map C)
  obtain ⟨m, hm⟩ := hcont.exists_pow_vlt_of_isTopologicallyNilpotent haNil hbSupp
  have hvalcont := (isContinuous_def v.1).mp hcont
  have hmval : v.1.valuation (C a) ^ m < v.1.valuation (C b) := by
    simpa only [map_pow] using (valuation_lt_iff v.1 _ _).mpr hm
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    rw [hmzero, pow_zero] at hmval
    exact (hvalcont.lt_one_of_isTopologicallyNilpotent hbNil).not_gt hmval
  have hexp : (n + 1) * m - 1 + 1 = (n + 1) * m :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos n) hmpos)
  apply (mem_discExhaustionUnion b v).mpr
  refine ⟨(n + 1) * m - 1, (mem_discExhaustion b _ v).mpr ⟨?_, ?_⟩⟩
  · rw [hexp, pow_mul, ← valuation_le_iff]
    rw [map_pow]
    exact (pow_le_pow_left₀ zero_le ((valuation_le_iff v.1 _ _).mpr hn.1) m).trans hmval.le
  · exact fun h ↦ hbSupp ((mem_supp_iff v.1 _).mpr h)

end TopologicalRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K]

/-- The Gauss point of radius `r` lies in the `n`-th disc exactly when `r^(n+1) ≤ ‖c‖`. -/
theorem gaussPoint_mem_discExhaustion_iff {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (c : K) (n : ℕ) :
    gaussPoint hr₀ hr₁ ∈ discExhaustion c n ↔ r ^ (n + 1) ≤ ‖c‖ ∧ c ≠ 0 := by
  simp only [mem_discExhaustion, gaussPoint_vle_iff, map_pow, map_zero,
    closedDiscGaussValuation_weightedC, nonpos_iff_eq_zero, nnnorm_eq_zero,
    ← NNReal.coe_le_coe, NNReal.coe_pow, coe_closedDiscGaussValuation_weightedX, coe_nnnorm]

end NontriviallyNormedField

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- For `0 < ‖c‖ < 1`, the Gauss points in the exhaustion union are exactly those of radius
 strictly less than one. -/
theorem gaussPoint_mem_discExhaustionUnion_iff {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    let := NontriviallyNormedField.ofNormNeOne ⟨c, hc₀, ne_of_lt hc₁⟩
    gaussPoint hr₀ hr₁ ∈ discExhaustionUnion c ↔ r < 1 := by
  let := NontriviallyNormedField.ofNormNeOne ⟨c, hc₀, ne_of_lt hc₁⟩
  dsimp only
  rw [mem_discExhaustionUnion]
  simp only [gaussPoint_mem_discExhaustion_iff]
  refine ⟨fun ⟨n, hn, _⟩ ↦ ?_, fun hr ↦ ?_⟩
  · exact lt_of_le_of_ne hr₁ (fun h ↦ by simp [h] at hn; linarith)
  · have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr₀.le hr
    obtain ⟨m, hm, hmpos⟩ := ((hpow.eventually
      (eventually_lt_nhds (norm_pos_iff.mpr hc₀))).and (eventually_gt_atTop 0)).exists
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    exact ⟨n, hm.le, hc₀⟩

/-- The open unit disc is not quasi-compact: Gauss points with radii near one escape every
 rational exhaustion disc. -/
theorem not_isCompact_discExhaustionUnion {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    ¬ IsCompact (discExhaustionUnion c) := by
  let := NontriviallyNormedField.ofNormNeOne ⟨c, hc₀, ne_of_lt hc₁⟩
  intro h
  obtain ⟨n, hn⟩ := exists_subset_discExhaustion_of_isCompact h Set.Subset.rfl
  have hp : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), ‖c‖ < r ^ (n + 1) :=
    (continuousAt_id.pow (n + 1)).eventually (by simpa using eventually_gt_nhds hc₁)
  have he : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (0 < r ∧ ‖c‖ < r ^ (n + 1)) ∧ r < 1 :=
    ((eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).and
      (hp.filter_mono nhdsWithin_le_nhds) |>.and self_mem_nhdsWithin
  obtain ⟨r, ⟨hr₀, hrpow⟩, hr₁⟩ := he.exists
  have hrmem := (gaussPoint_mem_discExhaustionUnion_iff hr₀ hr₁.le hc₀ hc₁).mpr hr₁
  exact hrpow.not_ge ((gaussPoint_mem_discExhaustion_iff hr₀ hr₁.le c n).mp
    (hn hrmem)).1

/-- The open unit disc is not homeomorphic to any affinoid adic spectrum, since every such
 spectrum is quasi-compact. This obstruction is independent of the structure sheaf. -/
theorem not_nonempty_homeomorph_discExhaustionUnion_spa {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1)
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    (Aplus : Subring A) : ¬ Nonempty ((discExhaustionUnion c) ≃ₜ spa Aplus) := by
  rintro ⟨e⟩
  have : CompactSpace (discExhaustionUnion c) := e.symm.compactSpace
  exact not_isCompact_discExhaustionUnion hc₀ hc₁ (isCompact_iff_compactSpace.mpr inferInstance)

end NormedField

end TauCeti.ValuationSpectrum
