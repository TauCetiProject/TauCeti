/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount

/-!
# Weighted counts of configurations through generic points

Taubes's invariant of a symplectic four-manifold counts, in a class `A` of virtual dimension
`d(A) = A · A - κ · A = 2 k`, the configurations of embedded pseudoholomorphic curves passing
through `k` fixed generic points. A configuration is a finite set of distinct, mutually disjoint,
embedded connected images `C_a` with positive multiplicities and `∑ m_a [C_a] = A`
(`TauCeti.compatibleConfigurations`); with point constraints it is required to pass through every
point. Since the images are disjoint, each point lies on exactly one component: the image
condition itself assigns the points to the components, with no ordering of the components and
no division by `k!`.

This file sets up that count for an arbitrary type `ι` of candidate images, extending
`TauCeti.configurationCount`, which is the count with no points. The points form a type `P`,
and `pts c` is the finite set of points lying on the candidate `c`. A **point configuration**
(`TauCeti.pointConfigurations`) is a compatible configuration such that every point lies on
exactly one of its components, and `TauCeti.pointConfigurationCount` is the sum of the weights
`l.prod w` of the point configurations. The weight `w c k` of an ordinary component may depend
on the points it passes through, as the sign of its point-constrained normal operator does.

* With no points the point count is the configuration count
  (`TauCeti.pointConfigurationCount_of_isEmpty`). Relabeling the points by a bijection does not
  change it (`TauCeti.pointConfigurationCount_map`), so it depends only on the set of points.
* If compatible candidates contain disjoint sets of points, as disjoint images do, a compatible
  configuration is a point configuration as soon as its components cover the points
  (`TauCeti.mem_pointConfigurations_iff_of_disjoint`). The point sets of the components of a
  point configuration partition the points
  (`TauCeti.pairwiseDisjoint_of_mem_pointConfigurations`,
  `TauCeti.biUnion_eq_univ_of_mem_pointConfigurations`), so the numbers of points on the
  components add up to the number of points
  (`TauCeti.sum_card_eq_of_mem_pointConfigurations`).
* The finiteness and area cutoffs of the configuration count carry over
  (`TauCeti.finite_pointConfigurations`, `TauCeti.pointConfigurationCount_eq_of_area_lt`). In
  class zero only the empty configuration remains, so with at least one point the count
  vanishes (`TauCeti.pointConfigurationCount_zero_of_nonempty`), while with no points it is `1`
  (`TauCeti.configurationCount_zero`).

With an intersection form under which compatible candidates have intersection number zero, the
virtual dimension of the class of a point configuration splits as

`d(A) - 2 #P = ∑ ((d(c) - 2 #(pts c)) + (l c - 1) (d(c) + l c (c · c)))`

over its components (`TauCeti.apply_self_sub_apply_canonical_sub_two_mul_card_eq_sum`). For
generic points a candidate through `#(pts c)` of them satisfies `2 #(pts c) ≤ d(c)`, and only
candidates of nonnegative square, such as square-zero tori, are counted with higher
multiplicity. Then every summand is nonnegative, so:

* `2 #P ≤ d(A)` for every point configuration, and the count vanishes when `d(A) < 2 #P`
  (`TauCeti.pointConfigurationCount_eq_zero_of_apply_self_sub_apply_canonical_lt`); with no
  points this is the vanishing of the count in negative virtual dimension;
* when `d(A) = 2 #P`, every component `c` passes through exactly `d(c) / 2` of the points
  (`TauCeti.apply_self_sub_apply_canonical_eq_two_mul_card_of_mem_pointConfigurations`),
  `d(A) = ∑ d(c)` over the components
  (`TauCeti.apply_self_sub_apply_canonical_eq_sum_of_mem_pointConfigurations`), and a
  component of multiplicity at least two has `d(c) = c · c = κ · c = 0` and contains none of the
  points (`TauCeti.apply_self_sub_apply_canonical_eq_zero_of_mem_pointConfigurations`,
  `TauCeti.apply_self_eq_zero_of_mem_pointConfigurations`,
  `TauCeti.apply_canonical_eq_zero_of_mem_pointConfigurations`,
  `TauCeti.pts_eq_empty_of_mem_pointConfigurations`).

The candidate images, their classes and point incidences, the weights, the area bounds and the
genericity of the points are inputs here; the geometric theorems supplying them are separate.

## Main declarations

* `TauCeti.pointConfigurations r cls pts s A`: the compatible configurations in class `A` of
  candidates from `s` passing through every point, each on exactly one component.
* `TauCeti.pointConfigurationCount r cls pts w s A`: the sum of the weights of these
  configurations.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

namespace TauCeti

variable {ι H P Q R : Type*}

section Configuration

variable [AddCommMonoid H]

/-- The **point configurations** in class `A` of candidates from `s`, through the points of `P`:
the compatible configurations `l` (`TauCeti.compatibleConfigurations`) such that every point
lies on exactly one component, where `pts c` is the set of points lying on the candidate `c`. -/
def pointConfigurations (r : ι → ι → Prop) (cls : ι → H) (pts : ι → Finset P) (s : Set ι)
    (A : H) : Set (ι →₀ ℕ) :=
  {l | l ∈ compatibleConfigurations r cls s A ∧ ∀ p, ∃! c, c ∈ l.support ∧ p ∈ pts c}

variable {r : ι → ι → Prop} {cls : ι → H} {pts : ι → Finset P} {s t : Set ι} {A : H}
  {l : ι →₀ ℕ}

@[simp]
theorem mem_pointConfigurations :
    l ∈ pointConfigurations r cls pts s A ↔
      l ∈ compatibleConfigurations r cls s A ∧ ∀ p, ∃! c, c ∈ l.support ∧ p ∈ pts c :=
  Iff.rfl

theorem pointConfigurations_subset_compatibleConfigurations :
    pointConfigurations r cls pts s A ⊆ compatibleConfigurations r cls s A :=
  fun _ hl ↦ hl.1

theorem pointConfigurations_mono (h : s ⊆ t) :
    pointConfigurations r cls pts s A ⊆ pointConfigurations r cls pts t A :=
  fun _ hl ↦ ⟨compatibleConfigurations_mono h hl.1, hl.2⟩

/-- With no points, the point configurations are the compatible configurations. -/
@[simp]
theorem pointConfigurations_of_isEmpty [IsEmpty P] :
    pointConfigurations r cls pts s A = compatibleConfigurations r cls s A := by
  ext
  simp

/-- If compatible candidates contain disjoint sets of points, as disjoint images do, a compatible
configuration is a point configuration as soon as every point lies on one of its components. -/
theorem mem_pointConfigurations_iff_of_disjoint
    (hdisj : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → Disjoint (pts a) (pts b)) :
    l ∈ pointConfigurations r cls pts s A ↔
      l ∈ compatibleConfigurations r cls s A ∧ ∀ p, ∃ c ∈ l.support, p ∈ pts c := by
  refine ⟨fun hl ↦ ⟨hl.1, fun p ↦ (hl.2 p).exists⟩, fun hl ↦ ⟨hl.1, fun p ↦ ?_⟩⟩
  obtain ⟨hsub, hpair, -⟩ := mem_compatibleConfigurations.1 hl.1
  obtain ⟨c, hc, hpc⟩ := hl.2 p
  refine ⟨c, ⟨hc, hpc⟩, fun b hb ↦ by_contra fun hbc ↦ ?_⟩
  exact Finset.disjoint_left.1 (hdisj b (hsub hb.1) c (hsub hc) hbc (hpair hb.1 hc hbc)) hb.2 hpc

/-- The point sets of distinct components of a point configuration are disjoint. -/
theorem pairwiseDisjoint_of_mem_pointConfigurations
    (hl : l ∈ pointConfigurations r cls pts s A) : (l.support : Set ι).PairwiseDisjoint pts :=
  fun _ ha _ hb hab ↦ Finset.disjoint_left.2 fun p hpa hpb ↦
    hab ((hl.2 p).unique ⟨ha, hpa⟩ ⟨hb, hpb⟩)

/-- The components of a point configuration cover the points. -/
theorem biUnion_eq_univ_of_mem_pointConfigurations [Fintype P] [DecidableEq P]
    (hl : l ∈ pointConfigurations r cls pts s A) : l.support.biUnion pts = Finset.univ :=
  Finset.eq_univ_of_forall fun p ↦ Finset.mem_biUnion.2 (hl.2 p).exists

/-- **The point-label partition.** The numbers of points on the components of a point
configuration add up to the number of points. -/
theorem sum_card_eq_of_mem_pointConfigurations [Fintype P]
    (hl : l ∈ pointConfigurations r cls pts s A) :
    ∑ c ∈ l.support, (pts c).card = Fintype.card P := by
  classical
  rw [← Finset.card_biUnion (pairwiseDisjoint_of_mem_pointConfigurations hl),
    biUnion_eq_univ_of_mem_pointConfigurations hl, Finset.card_univ]

/-- Relabeling the points by a bijection `e` does not change the point configurations. -/
@[simp]
theorem pointConfigurations_map (e : P ≃ Q) :
    pointConfigurations r cls (fun c ↦ (pts c).map e.toEmbedding) s A =
      pointConfigurations r cls pts s A := by
  ext l
  simp only [mem_pointConfigurations, Finset.mem_map_equiv]
  exact and_congr_right fun _ ↦
    (e.forall_congr_left (p := fun p ↦ ∃! c, c ∈ l.support ∧ p ∈ pts c)).symm

/-- Restricting the candidates to a subset `t` of `s` does not change the point configurations
in class `A` if every point configuration in class `A` from `s` is supported in `t`. -/
theorem pointConfigurations_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ pointConfigurations r cls pts s A, ↑l.support ⊆ t) :
    pointConfigurations r cls pts t A = pointConfigurations r cls pts s A :=
  (pointConfigurations_mono hts).antisymm fun l hl ↦
    ⟨mem_compatibleConfigurations.2 ⟨h l hl, (mem_compatibleConfigurations.1 hl.1).2⟩, hl.2⟩

section Area

variable {ω : H →+ ℝ}

/-- **Finite cutoff**: candidates of area larger than that of `A` lie in no point configuration
in class `A`. -/
theorem pointConfigurations_eq_of_area_lt (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c)) (hts : t ⊆ s)
    (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    pointConfigurations r cls pts t A = pointConfigurations r cls pts s A :=
  pointConfigurations_eq_of_forall_support_subset hts fun _ hl c hc ↦ by_contra fun hct ↦
    (h c ((mem_compatibleConfigurations.1 hl.1).1 hc) hct).not_ge
      (area_le_of_mem_compatibleConfigurations hnonneg hl.1 hc)

variable (hpos : ∀ c ∈ s, 0 < ω (cls c))
include hpos

/-- **Finiteness of point configurations.** If the candidates have positive area and only
finitely many of them have area at most `ω A`, then there are only finitely many point
configurations in class `A`. -/
theorem finite_pointConfigurations (hfin : {c ∈ s | ω (cls c) ≤ ω A}.Finite) :
    (pointConfigurations r cls pts s A).Finite :=
  (finite_compatibleConfigurations hpos hfin).subset
    pointConfigurations_subset_compatibleConfigurations

/-- With at least one point, there is no point configuration in class zero: the only
configuration in class zero is empty and passes through no point. -/
theorem pointConfigurations_zero_of_nonempty [Nonempty P] :
    pointConfigurations r cls pts s 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun l hl ↦ ?_
  obtain ⟨c, ⟨hc, -⟩, -⟩ := hl.2 (Classical.arbitrary P)
  rw [eq_zero_of_mem_compatibleConfigurations_of_area_nonpos hpos hl.1 (map_zero ω).le] at hc
  simp at hc

end Area

/-! ### The weighted count -/

variable [CommSemiring R]

variable (r cls pts) in
/-- The **weighted point count** in class `A`: the sum, over the point configurations `l` in
class `A` of candidates from `s`, of the products `l.prod w = ∏ c ∈ l.support, w c (l c)` of the
weights of their components. As for `TauCeti.configurationCount`, `finsum` sums the finitely many
nonzero weights if only finitely many point configurations have nonzero weight, and its value is
`0` by convention otherwise. -/
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

/-- With no points, the point count is the configuration count. -/
@[simp]
theorem pointConfigurationCount_of_isEmpty [IsEmpty P] :
    pointConfigurationCount r cls pts w s A = configurationCount r cls w s A := by
  rw [pointConfigurationCount_def, configurationCount_def, pointConfigurations_of_isEmpty]

/-- Relabeling the points by a bijection `e` does not change the point count. -/
@[simp]
theorem pointConfigurationCount_map (e : P ≃ Q) :
    pointConfigurationCount r cls (fun c ↦ (pts c).map e.toEmbedding) w s A =
      pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def, pointConfigurations_map]

/-- **Conditional comparison**: if every point configuration in class `A` of candidates from
`s` is supported in `t ⊆ s`, then the point counts over `t` and over `s` agree. -/
theorem pointConfigurationCount_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ pointConfigurations r cls pts s A, ↑l.support ⊆ t) :
    pointConfigurationCount r cls pts w t A = pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def,
    pointConfigurations_eq_of_forall_support_subset hts h]

section Area

variable {ω : H →+ ℝ}

/-- With at least one point, the point count in class zero vanishes. -/
theorem pointConfigurationCount_zero_of_nonempty [Nonempty P] (hpos : ∀ c ∈ s, 0 < ω (cls c)) :
    pointConfigurationCount r cls pts w s 0 = 0 := by
  rw [pointConfigurationCount_def, pointConfigurations_zero_of_nonempty hpos, finsum_mem_empty]

/-- If the candidates have positive area, the point count vanishes in nonzero classes of
nonpositive area. -/
theorem pointConfigurationCount_eq_zero_of_area_nonpos (hpos : ∀ c ∈ s, 0 < ω (cls c))
    (hA : ω A ≤ 0) (hA₀ : A ≠ 0) : pointConfigurationCount r cls pts w s A = 0 := by
  have h : pointConfigurations r cls pts s A = ∅ := Set.subset_empty_iff.1 fun _ hl ↦
    compatibleConfigurations_eq_empty_of_area_nonpos hpos hA hA₀ ▸
      pointConfigurations_subset_compatibleConfigurations hl
  rw [pointConfigurationCount_def, h, finsum_mem_empty]

variable (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c))
include hnonneg

/-- The point count vanishes in classes of negative area. -/
theorem pointConfigurationCount_eq_zero_of_area_neg (hA : ω A < 0) :
    pointConfigurationCount r cls pts w s A = 0 := by
  have h : pointConfigurations r cls pts s A = ∅ := Set.subset_empty_iff.1 fun _ hl ↦
    compatibleConfigurations_eq_empty_of_area_neg hnonneg hA ▸
      pointConfigurations_subset_compatibleConfigurations hl
  rw [pointConfigurationCount_def, h, finsum_mem_empty]

/-- **Finite cutoff**: discarding candidates of area larger than that of `A` does not change
the point count in class `A`. -/
theorem pointConfigurationCount_eq_of_area_lt (hts : t ⊆ s)
    (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    pointConfigurationCount r cls pts w t A = pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def,
    pointConfigurations_eq_of_area_lt hnonneg hts h]

end Area

end Configuration

/-! ### The virtual dimension of a point configuration -/

section Intersection

open LinearMap (BilinForm)

variable [AddCommGroup H] [Fintype P] {B : BilinForm ℤ H} {r : ι → ι → Prop} {cls : ι → H}
  {pts : ι → Finset P} {s : Set ι} {A κ : H} {l : ι →₀ ℕ}

/-- **The point budget of a configuration.** If compatible candidates have intersection number
zero, as disjoint images do, the virtual dimension `d(x) = x · x - κ · x` of the class of a
point configuration exceeds twice the number of points by
`∑ ((d(c) - 2 #(pts c)) + (l c - 1) (d(c) + l c (c · c)))` over its components. -/
theorem apply_self_sub_apply_canonical_sub_two_mul_card_eq_sum
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hl : l ∈ pointConfigurations r cls pts s A) :
    B A A - B κ A - 2 * Fintype.card P =
      ∑ c ∈ l.support, ((B (cls c) (cls c) - B κ (cls c) - 2 * (pts c).card) +
        ((l c : ℤ) - 1) * (B (cls c) (cls c) - B κ (cls c) + l c * B (cls c) (cls c))) := by
  rw [apply_self_sub_apply_canonical_eq_sum_of_mem_compatibleConfigurations hr hl.1 κ,
    ← sum_card_eq_of_mem_pointConfigurations hl, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

omit [Fintype P] in
/-- Under the genericity bound `2 #(pts c) ≤ d(c)`, and if a component of multiplicity at least
two has nonnegative square, the contribution of each component to the point budget
`TauCeti.apply_self_sub_apply_canonical_sub_two_mul_card_eq_sum` is a sum of two nonnegative
terms. -/
private theorem budget_terms_nonneg {c : ι}
    (hdim : 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : 2 ≤ l c → 0 ≤ B (cls c) (cls c)) (hc : c ∈ l.support) :
    0 ≤ B (cls c) (cls c) - B κ (cls c) - 2 * (pts c).card ∧
      0 ≤ ((l c : ℤ) - 1) * (B (cls c) (cls c) - B κ (cls c) + l c * B (cls c) (cls c)) := by
  refine ⟨by linarith, ?_⟩
  have hl0 := Finsupp.mem_support_iff.1 hc
  rcases Nat.lt_or_ge (l c) 2 with h | h
  · have h1 : l c = 1 := by omega
    simp [h1]
  · have hsq := hmult h
    have h' : (2 : ℤ) ≤ l c := by exact_mod_cast h
    have hcard : (0 : ℤ) ≤ (pts c).card := Int.natCast_nonneg _
    exact mul_nonneg (by linarith) (by nlinarith)

/-- **Points bound the virtual dimension.** Suppose compatible candidates have intersection
number zero, as disjoint images do, every candidate `c` through `#(pts c)` of the points
satisfies `2 #(pts c) ≤ d(c)`, as for generic points, and every component of multiplicity at least
two has nonnegative square, as square-zero tori do. Then the class `A` of a point configuration
satisfies `2 #P ≤ d(A)`. -/
theorem two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A) :
    2 * (Fintype.card P : ℤ) ≤ B A A - B κ A := by
  have h := apply_self_sub_apply_canonical_sub_two_mul_card_eq_sum (κ := κ) hr hl
  have hnn : 0 ≤ ∑ c ∈ l.support, ((B (cls c) (cls c) - B κ (cls c) - 2 * (pts c).card) +
      ((l c : ℤ) - 1) * (B (cls c) (cls c) - B κ (cls c) + l c * B (cls c) (cls c))) :=
    Finset.sum_nonneg fun c hc ↦ by
      obtain ⟨h₁, h₂⟩ := budget_terms_nonneg
        (hdim c ((mem_compatibleConfigurations.1 hl.1).1 hc)) (hmult c hc) hc
      exact add_nonneg h₁ h₂
  linarith

/-- In the equality case `d(A) = 2 #P` of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, both terms
of the point budget of every component vanish. -/
private theorem budget_terms_eq_zero
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) :
    B (cls c) (cls c) - B κ (cls c) = 2 * (pts c).card ∧
      ((l c : ℤ) - 1) * (B (cls c) (cls c) - B κ (cls c) + l c * B (cls c) (cls c)) = 0 := by
  have h := apply_self_sub_apply_canonical_sub_two_mul_card_eq_sum (κ := κ) hr hl
  have hnn (b : ι) (hb : b ∈ l.support) :=
    budget_terms_nonneg (hdim b ((mem_compatibleConfigurations.1 hl.1).1 hb)) (hmult b hb) hb
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b hb ↦ add_nonneg (hnn b hb).1 (hnn b hb).2).1
    (by linarith) c hc
  obtain ⟨h₁, h₂⟩ := hnn c hc
  exact ⟨by linarith, by linarith⟩

/-- **Assigned points.** In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, then every component `c` of a point configuration in class `A` passes through
exactly `d(c) / 2` of the points. -/
theorem apply_self_sub_apply_canonical_eq_two_mul_card_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) :
    B (cls c) (cls c) - B κ (cls c) = 2 * (pts c).card :=
  (budget_terms_eq_zero hr hdim hmult hl hA hc).1

/-- In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, then the virtual dimension of `A` is the sum of the virtual dimensions of the
components of a point configuration in class `A`. -/
theorem apply_self_sub_apply_canonical_eq_sum_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) :
    B A A - B κ A = ∑ c ∈ l.support, (B (cls c) (cls c) - B κ (cls c)) := by
  rw [Finset.sum_congr rfl fun c hc ↦
      apply_self_sub_apply_canonical_eq_two_mul_card_of_mem_pointConfigurations hr hdim hmult hl
        hA hc,
    hA, ← Finset.mul_sum, ← sum_card_eq_of_mem_pointConfigurations hl, Nat.cast_sum]

/-- In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, a component of multiplicity at least two of a point configuration in class `A`
has virtual dimension zero and square zero. -/
private theorem apply_self_sub_apply_canonical_eq_zero_and_apply_self_eq_zero
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) (h2 : 2 ≤ l c) :
    B (cls c) (cls c) - B κ (cls c) = 0 ∧ B (cls c) (cls c) = 0 := by
  obtain ⟨h₁, h₂⟩ := budget_terms_eq_zero hr hdim hmult hl hA hc
  have hsq := hmult c hc h2
  have h' : (2 : ℤ) ≤ l c := by exact_mod_cast h2
  have hcard : (0 : ℤ) ≤ (pts c).card := Int.natCast_nonneg _
  have hsum : B (cls c) (cls c) - B κ (cls c) + l c * B (cls c) (cls c) = 0 :=
    (mul_eq_zero.1 h₂).resolve_left (by linarith)
  constructor <;> nlinarith

/-- **Repeated components have index zero.** In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, a component of multiplicity at least two of a point configuration in class `A`
has virtual dimension zero. -/
theorem apply_self_sub_apply_canonical_eq_zero_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) (h2 : 2 ≤ l c) :
    B (cls c) (cls c) - B κ (cls c) = 0 :=
  (apply_self_sub_apply_canonical_eq_zero_and_apply_self_eq_zero hr hdim hmult hl hA hc h2).1

/-- **Repeated components have square zero.** In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, a component of multiplicity at least two of a point configuration in class `A`
has square zero. -/
theorem apply_self_eq_zero_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) (h2 : 2 ≤ l c) :
    B (cls c) (cls c) = 0 :=
  (apply_self_sub_apply_canonical_eq_zero_and_apply_self_eq_zero hr hdim hmult hl hA hc h2).2

/-- **Repeated components are orthogonal to `κ`.** In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, a component of multiplicity at least two of a point configuration in class `A`
satisfies `κ · c = 0`. -/
theorem apply_canonical_eq_zero_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) (h2 : 2 ≤ l c) :
    B κ (cls c) = 0 := by
  have h₁ := apply_self_sub_apply_canonical_eq_zero_of_mem_pointConfigurations hr hdim hmult hl
    hA hc h2
  have h₂ := apply_self_eq_zero_of_mem_pointConfigurations hr hdim hmult hl hA hc h2
  linarith

/-- **Repeated components avoid the points.** In the setting of
`TauCeti.two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations`, if
`d(A) = 2 #P`, a component of multiplicity at least two of a point configuration in class `A`
contains none of the points. -/
theorem pts_eq_empty_of_mem_pointConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ l.support, 2 ≤ l c → 0 ≤ B (cls c) (cls c))
    (hl : l ∈ pointConfigurations r cls pts s A)
    (hA : B A A - B κ A = 2 * Fintype.card P) {c : ι} (hc : c ∈ l.support) (h2 : 2 ≤ l c) :
    pts c = ∅ := by
  have h₁ := apply_self_sub_apply_canonical_eq_zero_of_mem_pointConfigurations hr hdim hmult hl
    hA hc h2
  have h₂ := apply_self_sub_apply_canonical_eq_two_mul_card_of_mem_pointConfigurations hr hdim
    hmult hl hA hc
  rw [← Finset.card_eq_zero]
  omega

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Vanishing below the point budget.** Suppose compatible candidates have intersection number
zero, as disjoint images do, every candidate `c` satisfies `2 #(pts c) ≤ d(c)`, as for generic
points, and only candidates of nonnegative square, such as square-zero tori, are counted with
multiplicity at least two. If `d(A) = A · A - κ · A < 2 #P`, then the point count in class `A`
vanishes. With no points this is the vanishing of the configuration count in negative virtual
dimension. -/
theorem pointConfigurationCount_eq_zero_of_apply_self_sub_apply_canonical_lt
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hdim : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ s, ∀ k, 2 ≤ k → w c k ≠ 0 → 0 ≤ B (cls c) (cls c))
    (hA : B A A - B κ A < 2 * Fintype.card P) : pointConfigurationCount r cls pts w s A = 0 := by
  rw [pointConfigurationCount_def]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun l hl ↦ ?_
  rw [Finsupp.prod]
  by_contra hne
  exact hA.not_ge <| two_mul_card_le_apply_self_sub_apply_canonical_of_mem_pointConfigurations hr
    hdim (fun c hc h2 ↦ hmult c ((mem_compatibleConfigurations.1 hl.1).1 hc) _ h2
      fun hw ↦ hne (Finset.prod_eq_zero hc hw)) hl

end Intersection

end TauCeti
