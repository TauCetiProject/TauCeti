/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount
public import TauCeti.Geometry.Symplectic.JHolomorphic.GoodCycle

/-!
# Weighted counts of curve configurations through generic points

Taubes's invariant of a class `A` of virtual dimension `d(A) = 2k` counts configurations of
embedded pseudoholomorphic curves through `k` fixed generic points. A configuration is a finite
set of distinct, mutually disjoint embedded images `C_a` with positive multiplicities `l_a` and
`∑ l_a [C_a] = A`, and it contributes only if every one of the points lies on one of its images.
No ordering of the components is chosen and nothing is divided by `k!`: the images themselves
decide which component carries which point.

This file adds the point constraints to the abstract count of
`TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount`. The candidate images form a type
`ι`, the points a type `P`, and `pts c` is the finite set of points on the image `c`. A point
configuration is a compatible configuration whose images cover every point
(`TauCeti.pointConfigurations`), and `TauCeti.pointConfigurationCount` is the sum of the weights
of the point configurations. Without points this is the count of index-zero classes
(`TauCeti.pointConfigurationCount_of_isEmpty`). The finiteness, area-cutoff and conditional
comparison statements carry over, and the count does not depend on how the points are labelled
(`TauCeti.pointConfigurationCount_map_equiv`). With at least one point, the count in class zero
vanishes (`TauCeti.pointConfigurationCount_zero`).

The geometry of curves through generic points supplies three numerical facts about the classes
of the candidates in the intersection form `B` on integral homology, with canonical class `κ` and
virtual dimension `d(x) = x · x - κ · x`: compatible (disjoint) images meet nonnegatively, the
points on an embedded image `c` cut its index down to a nonnegative dimension,
`2 |pts c| ≤ d(c)`, and `A · S ≥ -1` for the exceptional spheres `S` when `A` is good. Under these
hypotheses:

* every point configuration satisfies `2 k ≤ d(A)`
  (`TauCeti.two_mul_card_le_of_mem_pointConfigurations`), so the count vanishes when `2 k > d(A)`
  (`TauCeti.pointConfigurationCount_eq_zero_of_lt`);
* when `d(A) = 2 k`, the components of a point configuration form a good cycle
  (`TauCeti.isGoodCycle_of_mem_pointConfigurations`). The structure theorem for good cycles then
  shows that each component `c` carries exactly `d(c) / 2` of the points, each point lies on
  exactly one component, distinct components are homologically disjoint, exceptional spheres
  occur once, and repeated components are square-zero tori orthogonal to `κ` that carry no
  points (see `TauCeti.IsGoodCycle`).

The candidate images, their classes, point incidences and weights, and the three numerical
facts are inputs here; the geometric theorems supplying them are separate.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

variable {ι H P Q R : Type*}

section Configuration

variable [AddCommMonoid H] {r : ι → ι → Prop} {cls : ι → H} {pts : ι → Finset P}
  {s t : Set ι} {A : H} {l : ι →₀ ℕ}

/-- The **point configurations** in class `A` of candidates from `s`: the compatible
configurations (`TauCeti.compatibleConfigurations`) whose images cover all the points, where
`pts c` is the set of points on the image of the candidate `c`. -/
def pointConfigurations (r : ι → ι → Prop) (cls : ι → H) (pts : ι → Finset P) (s : Set ι)
    (A : H) : Set (ι →₀ ℕ) :=
  compatibleConfigurations r cls s A ∩ {l | ∀ p, ∃ c ∈ l.support, p ∈ pts c}

theorem pointConfigurations_eq_inter :
    pointConfigurations r cls pts s A =
      compatibleConfigurations r cls s A ∩ {l | ∀ p, ∃ c ∈ l.support, p ∈ pts c} :=
  (rfl)

@[simp]
theorem mem_pointConfigurations :
    l ∈ pointConfigurations r cls pts s A ↔
      l ∈ compatibleConfigurations r cls s A ∧ ∀ p, ∃ c ∈ l.support, p ∈ pts c :=
  Iff.rfl

theorem pointConfigurations_subset :
    pointConfigurations r cls pts s A ⊆ compatibleConfigurations r cls s A :=
  Set.inter_subset_left

theorem pointConfigurations_mono (h : s ⊆ t) :
    pointConfigurations r cls pts s A ⊆ pointConfigurations r cls pts t A :=
  Set.inter_subset_inter_left _ (compatibleConfigurations_mono h)

/-- Without points, the point configurations are the compatible configurations. -/
@[simp]
theorem pointConfigurations_of_isEmpty [IsEmpty P] :
    pointConfigurations r cls pts s A = compatibleConfigurations r cls s A := by
  simp [pointConfigurations_eq_inter]

/-- The empty configuration is a point configuration exactly in class zero and without points. -/
theorem zero_mem_pointConfigurations_iff :
    0 ∈ pointConfigurations r cls pts s A ↔ A = 0 ∧ IsEmpty P := by
  rw [mem_pointConfigurations, zero_mem_compatibleConfigurations_iff]
  simp [isEmpty_iff]

/-- Relabelling the points along an equivalence does not change the point configurations. -/
theorem pointConfigurations_map_equiv (e : P ≃ Q) :
    pointConfigurations r cls (fun c ↦ (pts c).map e.toEmbedding) s A =
      pointConfigurations r cls pts s A := by
  ext l
  simp only [mem_pointConfigurations, Finset.mem_map_equiv, and_congr_right_iff]
  exact fun _ ↦ (e.forall_congr_left (p := fun p ↦ ∃ c ∈ l.support, p ∈ pts c)).symm

/-- The components of a point configuration are candidates. -/
private theorem mem_of_mem_pointConfigurations (hl : l ∈ pointConfigurations r cls pts s A)
    (c : l.support) : (c : ι) ∈ s :=
  (mem_compatibleConfigurations.1 hl.1).1 c.2

/-- Distinct components of a point configuration are compatible. -/
private theorem rel_of_mem_pointConfigurations (hl : l ∈ pointConfigurations r cls pts s A)
    {c d : l.support} (hcd : c ≠ d) : r c d :=
  (mem_compatibleConfigurations.1 hl.1).2.1 c.2 d.2 (Subtype.coe_ne_coe.2 hcd)

/-- Restricting the candidates to a subset `t` of `s` does not change the point configurations
in class `A` if every point configuration in class `A` from `s` is supported in `t`. -/
theorem pointConfigurations_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ pointConfigurations r cls pts s A, ↑l.support ⊆ t) :
    pointConfigurations r cls pts t A = pointConfigurations r cls pts s A :=
  (pointConfigurations_mono hts).antisymm fun l hl ↦
    ⟨mem_compatibleConfigurations.2 ⟨h l hl, (mem_compatibleConfigurations.1 hl.1).2⟩, hl.2⟩

section Area

variable {ω : H →+ ℝ}

section Nonneg

variable (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c))
include hnonneg

/-- There is no point configuration in a class of negative area. -/
theorem pointConfigurations_eq_empty_of_area_neg (hA : ω A < 0) :
    pointConfigurations r cls pts s A = ∅ := by
  rw [pointConfigurations_eq_inter, compatibleConfigurations_eq_empty_of_area_neg hnonneg hA,
    Set.empty_inter]

/-- **Finite cutoff**: candidates of area larger than that of `A` lie in no point configuration
in class `A`. -/
theorem pointConfigurations_eq_of_area_lt (hts : t ⊆ s)
    (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    pointConfigurations r cls pts t A = pointConfigurations r cls pts s A := by
  rw [pointConfigurations_eq_inter, pointConfigurations_eq_inter,
    compatibleConfigurations_eq_of_area_lt hnonneg hts h]

end Nonneg

variable (hpos : ∀ c ∈ s, 0 < ω (cls c))
include hpos

/-- **Finiteness of point configurations.** If the candidates have positive area and only
finitely many of them have area at most `ω A`, then there are only finitely many point
configurations in class `A`. -/
theorem finite_pointConfigurations (hfin : {c ∈ s | ω (cls c) ≤ ω A}.Finite) :
    (pointConfigurations r cls pts s A).Finite :=
  (finite_compatibleConfigurations hpos hfin).subset pointConfigurations_subset

/-- With at least one point there is no point configuration in class zero: the only
configuration in class zero is empty, and it covers no point. -/
theorem pointConfigurations_zero [Nonempty P] : pointConfigurations r cls pts s 0 = ∅ := by
  rw [pointConfigurations_eq_inter, compatibleConfigurations_zero hpos]
  exact Set.eq_empty_of_forall_notMem fun l ⟨hl, hcov⟩ ↦ by
    obtain ⟨c, hc, -⟩ := hcov (Classical.arbitrary P)
    simp [Set.mem_singleton_iff.1 hl] at hc

end Area

/-! ### The weighted count through the points -/

variable [CommSemiring R]

variable (r cls pts) in
/-- The **weighted count through the points** in class `A`: the sum, over the point
configurations `l` in class `A` of candidates from `s`, of the products
`l.prod w = ∏ c ∈ l.support, w c (l c)` of the weights of their components. As for
`TauCeti.configurationCount`, `finsum` sums the finitely many nonzero weights if only finitely
many point configurations have nonzero weight, and is `0` by convention otherwise. -/
noncomputable def pointConfigurationCount (w : ι → ℕ → R) (s : Set ι) (A : H) : R :=
  ∑ᶠ l ∈ pointConfigurations r cls pts s A, l.prod w

variable {w : ι → ℕ → R}

theorem pointConfigurationCount_def :
    pointConfigurationCount r cls pts w s A =
      ∑ᶠ l ∈ pointConfigurations r cls pts s A, l.prod w := by
  rw [pointConfigurationCount]

/-- When there are finitely many point configurations, the count is a finite sum over them. -/
theorem pointConfigurationCount_eq_sum (h : (pointConfigurations r cls pts s A).Finite) :
    pointConfigurationCount r cls pts w s A = ∑ l ∈ h.toFinset, l.prod w := by
  rw [pointConfigurationCount_def, finsum_mem_eq_finite_toFinset_sum _ h]

/-- Without points, the count through the points is the configuration count. -/
@[simp]
theorem pointConfigurationCount_of_isEmpty [IsEmpty P] :
    pointConfigurationCount r cls pts w s A = configurationCount r cls w s A := by
  rw [pointConfigurationCount_def, configurationCount_def, pointConfigurations_of_isEmpty]

/-- Relabelling the points along an equivalence does not change the count. -/
theorem pointConfigurationCount_map_equiv (e : P ≃ Q) :
    pointConfigurationCount r cls (fun c ↦ (pts c).map e.toEmbedding) w s A =
      pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def, pointConfigurations_map_equiv]

/-- **Conditional comparison**: if every point configuration in class `A` of candidates from
`s` is supported in `t ⊆ s`, then the counts over `t` and over `s` agree. -/
theorem pointConfigurationCount_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ pointConfigurations r cls pts s A, ↑l.support ⊆ t) :
    pointConfigurationCount r cls pts w t A = pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def,
    pointConfigurations_eq_of_forall_support_subset hts h]

section Area

variable {ω : H →+ ℝ}

/-- With at least one point, the count in class zero vanishes. -/
theorem pointConfigurationCount_zero [Nonempty P] (hpos : ∀ c ∈ s, 0 < ω (cls c)) :
    pointConfigurationCount r cls pts w s 0 = 0 := by
  rw [pointConfigurationCount_def, pointConfigurations_zero hpos, finsum_mem_empty]

variable (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c))
include hnonneg

/-- The count vanishes in classes of negative area. -/
theorem pointConfigurationCount_eq_zero_of_area_neg (hA : ω A < 0) :
    pointConfigurationCount r cls pts w s A = 0 := by
  rw [pointConfigurationCount_def, pointConfigurations_eq_empty_of_area_neg hnonneg hA,
    finsum_mem_empty]

/-- **Finite cutoff**: discarding candidates of area larger than that of `A` does not change
the count through the points in class `A`. -/
theorem pointConfigurationCount_eq_of_area_lt (hts : t ⊆ s)
    (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    pointConfigurationCount r cls pts w t A = pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def,
    pointConfigurations_eq_of_area_lt hnonneg hts h]

end Area

end Configuration

/-! ### The intersection algebra of a point configuration -/

section GoodCycle

variable [AddCommGroup H] [Fintype P] {r : ι → ι → Prop} {cls : ι → H} {pts : ι → Finset P}
  {s : Set ι} {A : H} {l : ι →₀ ℕ} {B : BilinForm ℤ H} {κ : H}

/-- The class of a configuration is the sum of the classes of its components, counted with
multiplicity, indexed by the support. -/
private theorem sum_support_smul_eq (hl : l ∈ compatibleConfigurations r cls s A) :
    ∑ c : l.support, l c • cls c = A := by
  rw [← (mem_compatibleConfigurations.1 hl).2.2, Finsupp.linearCombination_apply, Finsupp.sum,
    ← Finset.sum_coe_sort l.support]

/-- The points are covered by the point sets of the components of a point configuration. -/
private theorem card_le_sum_card (hl : l ∈ pointConfigurations r cls pts s A) :
    Fintype.card P ≤ ∑ c ∈ l.support, (pts c).card := by
  classical
  calc Fintype.card P = (l.support.biUnion pts).card := by
        rw [Finset.eq_univ_of_forall fun p ↦ Finset.mem_biUnion.2 (hl.2 p), Finset.card_univ]
    _ ≤ ∑ c ∈ l.support, (pts c).card := Finset.card_biUnion_le

variable (hint : ∀ c ∈ s, ∀ d ∈ s, r c d → 0 ≤ B (cls c) (cls d))
  (hind : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
  (hgood : ∀ c ∈ s, B (cls c) (cls c) < 0 → -1 ≤ B A (cls c))
include hint hind hgood

/-- **Index bound for point configurations.** Suppose compatible candidates meet nonnegatively,
the points on each candidate `c` cut its virtual dimension `d(c) = c · c - κ · c` down to a
nonnegative dimension, `2 |pts c| ≤ d(c)`, and `A` is at least `-1` on every candidate of
negative square. Then a point configuration in class `A` passes through at most `d(A) / 2`
points. -/
theorem two_mul_card_le_of_mem_pointConfigurations
    (hl : l ∈ pointConfigurations r cls pts s A) :
    2 * (Fintype.card P : ℤ) ≤ B A A - B κ A := by
  have hmem := mem_of_mem_pointConfigurations hl
  -- The good-curve component inequality `∑ l c d(c) ≤ d(A)` over the components.
  have hle := sum_mul_apply_self_sub_apply_canonical_le (B := B) (κ := κ)
    (C := fun c : l.support ↦ cls c) (m := fun c ↦ l c) (sum_support_smul_eq hl.1)
    (fun {c d} hcd ↦ hint c (hmem c) d (hmem d) (rel_of_mem_pointConfigurations hl hcd))
    (fun c hc ↦ hgood c (hmem c) hc)
  rw [Finset.sum_coe_sort l.support (fun c ↦ (l c : ℤ) * (B (cls c) (cls c) - B κ (cls c)))]
    at hle
  -- Each component has multiplicity at least one and virtual dimension at least twice the
  -- number of its points, and the components cover the points.
  have hcomp : ∑ c ∈ l.support, 2 * ((pts c).card : ℤ) ≤
      ∑ c ∈ l.support, (l c : ℤ) * (B (cls c) (cls c) - B κ (cls c)) := by
    refine Finset.sum_le_sum fun c hc ↦ ?_
    have h1 : (1 : ℤ) ≤ l c := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by simpa using hc)
    have h2 := hind c (hmem ⟨c, hc⟩)
    nlinarith [Int.natCast_nonneg (pts c).card]
  have hcard : (Fintype.card P : ℤ) ≤ ∑ c ∈ l.support, ((pts c).card : ℤ) := by
    exact_mod_cast card_le_sum_card hl
  rw [← Finset.mul_sum] at hcomp
  linarith

/-- With more than `d(A) / 2` points, there is no point configuration in class `A`. -/
theorem pointConfigurations_eq_empty_of_lt (hA : B A A - B κ A < 2 * Fintype.card P) :
    pointConfigurations r cls pts s A = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hl ↦
    hA.not_ge (two_mul_card_le_of_mem_pointConfigurations hint hind hgood hl)

/-- **Vanishing for too many points**: the count through more than `d(A) / 2` points vanishes. -/
theorem pointConfigurationCount_eq_zero_of_lt [CommSemiring R] {w : ι → ℕ → R}
    (hA : B A A - B κ A < 2 * Fintype.card P) :
    pointConfigurationCount r cls pts w s A = 0 := by
  rw [pointConfigurationCount_def, pointConfigurations_eq_empty_of_lt hint hind hgood hA,
    finsum_mem_empty]

/-- **A point configuration through `d(A) / 2` points is a good cycle.** Under the hypotheses of
`TauCeti.two_mul_card_le_of_mem_pointConfigurations`, if the number of points is half the virtual
dimension of `A`, then the components of a point configuration in class `A`, with their
multiplicities and point sets and with singularity number zero, satisfy `TauCeti.IsGoodCycle`.
Its structure theorem then gives the assignment of the points to the components: each component
`c` carries exactly `d(c) / 2` points and each point lies on exactly one component. -/
theorem isGoodCycle_of_mem_pointConfigurations (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) :
    IsGoodCycle B κ A (fun c : l.support ↦ cls c) (fun c ↦ l c) 0 (fun c ↦ pts c) where
  mult_pos c := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 c.2)
  apply_nonneg {c d} hcd :=
    hint c (mem_of_mem_pointConfigurations hl c) d (mem_of_mem_pointConfigurations hl d)
      (rel_of_mem_pointConfigurations hl hcd)
  two_mul_card_add_le c := by simpa using hind c (mem_of_mem_pointConfigurations hl c)
  neg_one_le_apply c hc := hgood c (mem_of_mem_pointConfigurations hl c) hc
  sum_eq := sum_support_smul_eq hl.1
  exists_mem p := by
    obtain ⟨c, hc, hp⟩ := hl.2 p
    exact ⟨⟨c, hc⟩, hp⟩
  apply_self_sub_apply_canonical := hA

end GoodCycle

end TauCeti
