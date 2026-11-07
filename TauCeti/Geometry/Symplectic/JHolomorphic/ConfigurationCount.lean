/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Geometry.Symplectic.JHolomorphic.TorusWeight
public import TauCeti.RingTheory.NovikovSeries.PowerSeries

/-!
# Weighted counts of compatible configurations of pseudoholomorphic curves

In Taubes's count of embedded pseudoholomorphic curves in a symplectic four-manifold, a
configuration in a class `A` is a finite set of distinct embedded connected pseudoholomorphic
images `C_a`, mutually disjoint, with positive multiplicities `l_a` and `∑ l_a [C_a] = A`. Each
component contributes a weight depending on the image and its multiplicity: for an embedded
square-zero torus the coefficient `[t ^ l] f_label(C)` of its local series
(`TauCeti.torusWeight`), for an ordinary component the sign of its determinant line. A
configuration contributes the product of these weights, and the count in class `A` is their
sum over all configurations.

This file sets up that sum for an arbitrary type `ι` of candidate images. An image `c` has a
class `cls c` in an additive monoid `H` (the integral homology), compatibility of two distinct
images is a relation `r` (disjointness of the images), and `w c k` is the weight of `c` taken
with multiplicity `k`. A configuration is a multiplicity assignment `l : ι →₀ ℕ` whose support
lies in a set `s` of admissible candidates and consists of pairwise compatible images, with
total class `∑ l c • cls c = A` (`TauCeti.compatibleConfigurations`). Its weight is
`l.prod w = ∏ c ∈ l.support, w c (l c)`, and `TauCeti.configurationCount` is the sum of these
weights. Point-incidence conditions are not part of the definition: this is the count in
classes of index zero, which carry no point constraints, such as the classes on a square-zero
ray and the pullback classes of a surface mapping torus.

Given a symplectic area `ω : H →+ ℝ` that is nonnegative on the candidates, every configuration
in class `A` uses only candidates of area at most `ω A`, so discarding the candidates of larger
area does not change the count (`TauCeti.configurationCount_eq_of_area_lt`), and the count
vanishes in classes of negative area. If `ω` is positive on the candidates, the multiplicities
are bounded as well. Hence there are finitely many configurations as soon as there are finitely
many candidates of area at most `ω A` (`TauCeti.finite_compatibleConfigurations`), and the
empty configuration is the only one in class `0` (`TauCeti.configurationCount_zero`).

On the ray of a class `A₀` that is not torsion, let `T` be a set of tori with classes
`m c • A₀`. If `A₀ · A₀ = 0`, then distinct images of `T` have intersection number zero, so
positivity of intersections makes them pairwise disjoint
(`LinearMap.BilinForm.pairwise_of_apply_self_eq_zero`). For pairwise compatible `T` the
configurations of class `j • A₀` supported in `T` are exactly the assignments of the weighted
antidiagonal `Finset.weightedFinsuppAntidiag` used by the ray series, so the count is the
`j`-th coefficient of the product of the local series at `t ^ m c`
(`TauCeti.configurationCount_eq_coeff_rayTorusWeightSeries`), and the generating series of the
ray counts is the infinite product `∏_C f_label(C)(t ^ m_C)`
(`TauCeti.mk_configurationCount_eq_tprod`). A total class on the ray does not force the
components of a configuration onto the ray. The count over all candidates agrees with the ray
count in class `j • A₀` under the additional hypothesis that every configuration of that class
consists of ray tori (`TauCeti.configurationCount_eq_of_forall_support_subset`).

For the orbit tori of a surface mapping torus, which are pairwise disjoint and do not lie on a
single ray, the counts are collected over all classes at once. If the candidates have positive
period `N : H →+ ℝ`, for instance the symplectic area, with finitely many below each cutoff, then
only finitely many classes below each cutoff have a nonzero count
(`TauCeti.finite_setOf_configurationCount_ne_zero_lt`), so the counts are the coefficients of a
Novikov series `∑_A Gr(A) e^A`, the generating series `TauCeti.configurationCountSeries`. Adding
to a finite family of pairwise compatible candidates one more candidate `c` multiplies the
generating series by its local series at `e ^ cls c`, so for finitely many candidates the counts
are the coefficients of the product of their local series
(`TauCeti.configurationCount_eq_coeff_prod_ofPowerSeries`). Below each cutoff only finitely many
candidates matter, so for a pairwise compatible family the generating series is the infinite
product `∏_c f c (e ^ cls c)` of the local series in the period topology
(`TauCeti.hasProd_ofPowerSeries_configurationCountSeries`).

The candidate images, their classes, labels and weights, the area bounds and the positivity of
intersections are inputs here; the geometric theorems supplying them are separate.

## Main declarations

* `TauCeti.compatibleConfigurations r cls s A`: the configurations in class `A` of pairwise
  compatible candidates from `s`.
* `TauCeti.configurationCount r cls w s A`: the sum of the weights `l.prod w` of these
  configurations.
* `TauCeti.finite_compatibleConfigurations`: finiteness of the configurations of a class.
* `TauCeti.configurationCount_zero`, `TauCeti.configurationCount_eq_zero_of_area_neg`: the
  counts in class zero and in classes of negative area.
* `TauCeti.configurationCount_eq_of_area_lt`: candidates of area larger than `ω A` do not
  contribute.
* `TauCeti.configurationCount_eq_of_forall_support_subset`: the conditional comparison of the
  counts over two candidate sets.
* `LinearMap.BilinForm.pairwise_of_apply_self_eq_zero`: under positivity of intersections, tori
  on a square-zero ray are pairwise compatible.
* `TauCeti.compatibleConfigurations_eq_weightedFinsuppAntidiag`,
  `TauCeti.configurationCount_eq_coeff_prod_expand`,
  `TauCeti.configurationCount_eq_coeff_rayTorusWeightSeries`,
  `TauCeti.mk_configurationCount_eq_tprod`: the ray count is computed by the ray series.
* `TauCeti.configurationCountSeries`: the generating series of the counts of all classes, as a
  Novikov series.
* `TauCeti.configurationCount_eq_coeff_prod_ofPowerSeries`,
  `TauCeti.hasProd_ofPowerSeries_configurationCountSeries`: for pairwise compatible candidates,
  the generating series is the product of the local series.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

open PowerSeries

namespace TauCeti

variable {ι H R : Type*}

section Configuration

variable [AddCommMonoid H]

/-- The **compatible configurations** in class `A` of candidates from `s`: the multiplicity
assignments `l : ι →₀ ℕ` supported in `s`, whose support consists of pairwise `r`-compatible
candidates, with total class `∑ c, l c • cls c = A`. For pseudoholomorphic images `r` is
disjointness of the images. -/
def compatibleConfigurations (r : ι → ι → Prop) (cls : ι → H) (s : Set ι) (A : H) :
    Set (ι →₀ ℕ) :=
  {l | ↑l.support ⊆ s ∧ (↑l.support : Set ι).Pairwise r ∧ Finsupp.linearCombination ℕ cls l = A}

variable {r : ι → ι → Prop} {cls : ι → H} {s t : Set ι} {A : H} {l : ι →₀ ℕ}

@[simp]
theorem mem_compatibleConfigurations :
    l ∈ compatibleConfigurations r cls s A ↔
      ↑l.support ⊆ s ∧ (↑l.support : Set ι).Pairwise r ∧
        Finsupp.linearCombination ℕ cls l = A :=
  Iff.rfl

theorem compatibleConfigurations_mono (h : s ⊆ t) :
    compatibleConfigurations r cls s A ⊆ compatibleConfigurations r cls t A :=
  fun _ hl ↦ ⟨hl.1.trans h, hl.2⟩

/-- The empty configuration has class zero. -/
theorem zero_mem_compatibleConfigurations_iff :
    0 ∈ compatibleConfigurations r cls s A ↔ A = 0 := by
  simp [eq_comm]

/-- Restricting the candidates to a subset `t` of `s` does not change the configurations in
class `A` if every configuration in class `A` from `s` is supported in `t`. -/
theorem compatibleConfigurations_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ compatibleConfigurations r cls s A, ↑l.support ⊆ t) :
    compatibleConfigurations r cls t A = compatibleConfigurations r cls s A :=
  (compatibleConfigurations_mono hts).antisymm fun l hl ↦ ⟨h l hl, hl.2⟩

section Area

variable {ω : H →+ ℝ}

/-- The area of the class of a configuration is the sum of the areas of its components, counted
with multiplicity. -/
theorem area_eq_sum_of_mem_compatibleConfigurations
    (hl : l ∈ compatibleConfigurations r cls s A) :
    ω A = ∑ c ∈ l.support, (l c : ℝ) * ω (cls c) := by
  rw [← hl.2.2, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp [map_nsmul, nsmul_eq_mul]

section Nonneg

variable (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c))
include hnonneg

/-- A class with a configuration of candidates of nonnegative area has nonnegative area. -/
theorem area_nonneg_of_mem_compatibleConfigurations
    (hl : l ∈ compatibleConfigurations r cls s A) : 0 ≤ ω A := by
  rw [area_eq_sum_of_mem_compatibleConfigurations hl]
  exact Finset.sum_nonneg fun c hc ↦ mul_nonneg (Nat.cast_nonneg _) (hnonneg c (hl.1 hc))

/-- In a configuration of candidates of nonnegative area, each component, counted with its
multiplicity, has area at most that of the total class. -/
theorem mul_area_le_of_mem_compatibleConfigurations
    (hl : l ∈ compatibleConfigurations r cls s A) (c : ι) : (l c : ℝ) * ω (cls c) ≤ ω A := by
  by_cases hc : c ∈ l.support
  · rw [area_eq_sum_of_mem_compatibleConfigurations hl]
    exact Finset.single_le_sum (f := fun c ↦ (l c : ℝ) * ω (cls c))
      (fun d hd ↦ mul_nonneg (Nat.cast_nonneg _) (hnonneg d (hl.1 hd))) hc
  · simpa [Finsupp.notMem_support_iff.1 hc] using
      area_nonneg_of_mem_compatibleConfigurations hnonneg hl

/-- In a configuration of candidates of nonnegative area, each component has area at most that
of the total class. -/
theorem area_le_of_mem_compatibleConfigurations
    (hl : l ∈ compatibleConfigurations r cls s A) {c : ι} (hc : c ∈ l.support) :
    ω (cls c) ≤ ω A := by
  have h1 : (1 : ℝ) ≤ l c := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hc)
  calc ω (cls c) ≤ (l c : ℝ) * ω (cls c) := le_mul_of_one_le_left (hnonneg c (hl.1 hc)) h1
    _ ≤ ω A := mul_area_le_of_mem_compatibleConfigurations hnonneg hl c

/-- There is no configuration in a class of negative area. -/
theorem compatibleConfigurations_eq_empty_of_area_neg (hA : ω A < 0) :
    compatibleConfigurations r cls s A = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hl ↦
    hA.not_ge (area_nonneg_of_mem_compatibleConfigurations hnonneg hl)

/-- **Finite cutoff**: candidates of area larger than that of `A` lie in no configuration in
class `A`. -/
theorem compatibleConfigurations_eq_of_area_lt (hts : t ⊆ s)
    (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    compatibleConfigurations r cls t A = compatibleConfigurations r cls s A :=
  compatibleConfigurations_eq_of_forall_support_subset hts fun _ hl c hc ↦
    by_contra fun hct ↦
      (h c (hl.1 hc) hct).not_ge (area_le_of_mem_compatibleConfigurations hnonneg hl hc)

end Nonneg

variable (hpos : ∀ c ∈ s, 0 < ω (cls c))
include hpos

/-- **Finiteness below an area bound.** If the candidates have positive area and only finitely
many of them have area at most `C`, then only finitely many multiplicity assignments supported
in the candidates have total area at most `C`. -/
theorem finite_setOf_support_subset_area_le {C : ℝ} (hfin : {c ∈ s | ω (cls c) ≤ C}.Finite) :
    {l : ι →₀ ℕ | ↑l.support ⊆ s ∧ ω (Finsupp.linearCombination ℕ cls l) ≤ C}.Finite := by
  classical
  refine (hfin.toFinset.finsupp fun c ↦ Finset.range (⌊C / ω (cls c)⌋₊ + 1)).finite_toSet.subset
    fun l hl ↦ ?_
  -- With no compatibility condition, `l` is a configuration in its own class.
  have hl' : l ∈ compatibleConfigurations (fun _ _ ↦ True) cls s
      (Finsupp.linearCombination ℕ cls l) := ⟨hl.1, fun _ _ _ _ _ ↦ trivial, rfl⟩
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  have hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c) := fun c hc ↦ (hpos c hc).le
  refine ⟨fun c hc ↦ hfin.mem_toFinset.2
    ⟨hl.1 hc, (area_le_of_mem_compatibleConfigurations hnonneg hl' hc).trans hl.2⟩,
    fun c hc ↦ ?_⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.le_floor ((le_div_iff₀ (hpos c (hfin.mem_toFinset.1 hc).1)).2
    ((mul_area_le_of_mem_compatibleConfigurations hnonneg hl' c).trans hl.2))

/-- **Finiteness of configurations.** If the candidates have positive area and only finitely
many of them have area at most `ω A`, then there are only finitely many configurations in
class `A`. -/
theorem finite_compatibleConfigurations (hfin : {c ∈ s | ω (cls c) ≤ ω A}.Finite) :
    (compatibleConfigurations r cls s A).Finite :=
  (finite_setOf_support_subset_area_le hpos hfin).subset fun _ hl ↦ ⟨hl.1, by rw [hl.2.2]⟩

/-- The empty configuration is the only configuration in class zero. -/
theorem compatibleConfigurations_zero : compatibleConfigurations r cls s 0 = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_compatibleConfigurations_iff.2 rfl,
    fun l hl ↦ Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem fun c hc ↦ ?_)⟩
  have := area_le_of_mem_compatibleConfigurations (fun c hc ↦ (hpos c hc).le) hl hc
  rw [map_zero] at this
  exact (hpos c (hl.1 hc)).not_ge this

end Area

/-! ### The weighted count -/

variable [CommSemiring R]

variable (r cls) in
/-- The **weighted configuration count** in class `A`: the sum, over the compatible
configurations `l` in class `A` of candidates from `s`, of the products
`l.prod w = ∏ c ∈ l.support, w c (l c)` of the weights of their components, where `w c k` is the
weight of the candidate `c` taken with multiplicity `k`. This is a finite sum when there are
finitely many configurations (`TauCeti.finite_compatibleConfigurations`). In general `finsum`
sums the finitely many nonzero weights if only finitely many configurations have nonzero
weight, and its value is `0` by convention if infinitely many configurations have nonzero
weight. -/
noncomputable def configurationCount (w : ι → ℕ → R) (s : Set ι) (A : H) : R :=
  ∑ᶠ l ∈ compatibleConfigurations r cls s A, l.prod w

variable {w : ι → ℕ → R}

theorem configurationCount_def :
    configurationCount r cls w s A = ∑ᶠ l ∈ compatibleConfigurations r cls s A, l.prod w := by
  rw [configurationCount]

/-- When there are finitely many configurations, the count is a finite sum over them. -/
theorem configurationCount_eq_sum (h : (compatibleConfigurations r cls s A).Finite) :
    configurationCount r cls w s A = ∑ l ∈ h.toFinset, l.prod w := by
  rw [configurationCount_def, finsum_mem_eq_finite_toFinset_sum _ h]

/-- **Conditional comparison**: if every configuration in class `A` of candidates from `s` is
supported in `t ⊆ s`, then the counts over `t` and over `s` agree. -/
theorem configurationCount_eq_of_forall_support_subset (hts : t ⊆ s)
    (h : ∀ l ∈ compatibleConfigurations r cls s A, ↑l.support ⊆ t) :
    configurationCount r cls w t A = configurationCount r cls w s A := by
  rw [configurationCount_def, configurationCount_def,
    compatibleConfigurations_eq_of_forall_support_subset hts h]

section Area

variable {ω : H →+ ℝ}

/-- The count in class zero is `1`, the weight of the empty configuration. -/
theorem configurationCount_zero (hpos : ∀ c ∈ s, 0 < ω (cls c)) :
    configurationCount r cls w s 0 = 1 := by
  rw [configurationCount_def, compatibleConfigurations_zero hpos, finsum_mem_singleton,
    Finsupp.prod_zero_index]

variable (hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c))
include hnonneg

/-- The count vanishes in classes of negative area. -/
theorem configurationCount_eq_zero_of_area_neg (hA : ω A < 0) :
    configurationCount r cls w s A = 0 := by
  rw [configurationCount_def, compatibleConfigurations_eq_empty_of_area_neg hnonneg hA,
    finsum_mem_empty]

/-- **Finite cutoff**: discarding candidates of area larger than that of `A` does not change
the count in class `A`. -/
theorem configurationCount_eq_of_area_lt (hts : t ⊆ s) (h : ∀ c ∈ s, c ∉ t → ω A < ω (cls c)) :
    configurationCount r cls w t A = configurationCount r cls w s A := by
  rw [configurationCount_def, configurationCount_def,
    compatibleConfigurations_eq_of_area_lt hnonneg hts h]

end Area

end Configuration

end TauCeti

/-! ### Tori on a square-zero ray -/

/-- **Disjointness on a square-zero ray.** Let `B` be the intersection form and let every
candidate of `T` have class `m c • A₀`, where `A₀ · A₀ = 0`. If distinct candidates of `T` with
intersection number zero are compatible, as positivity of intersections gives for distinct
pseudoholomorphic images, then the candidates of `T` are pairwise compatible. -/
theorem LinearMap.BilinForm.pairwise_of_apply_self_eq_zero {ι H : Type*} [AddCommGroup H]
    {r : ι → ι → Prop} {cls : ι → H} {T : Set ι} {A₀ : H} {m : ι → ℕ}
    (B : LinearMap.BilinForm ℤ H) (hA₀ : B A₀ A₀ = 0) (hcls : ∀ c ∈ T, cls c = m c • A₀)
    (hr : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → B (cls a) (cls b) = 0 → r a b) : T.Pairwise r :=
  fun a ha b hb hab ↦ hr a ha b hb hab (by simp [hcls a ha, hcls b hb, hA₀])

namespace TauCeti

variable {ι H R : Type*}

section Ray

variable [AddCommMonoid H] {r : ι → ι → Prop} {cls : ι → H} {T : Set ι} {A₀ : H}
  {m : ι → ℕ+}

/-- On a ray, the compatible configurations in class `j • A₀` of a pairwise compatible family
`T` of tori, the torus `c` having class `m c • A₀`, are the assignments of the weighted
antidiagonal `s.weightedFinsuppAntidiag m j`, for every finite subfamily `s` of `T` containing
the tori of class at most `j • A₀`. The class `A₀` must not be torsion. -/
theorem compatibleConfigurations_eq_weightedFinsuppAntidiag (hT : T.Pairwise r)
    (hcls : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    {s : Finset ι} (hsT : ↑s ⊆ T) {j : ℕ} (hs : ∀ c ∈ T, (m c : ℕ) ≤ j → c ∈ s) :
    compatibleConfigurations r cls T (j • A₀) = ↑(s.weightedFinsuppAntidiag m j) := by
  -- An assignment supported in `T` has class `(∑ c, m c * l c) • A₀`.
  have key {l : ι →₀ ℕ} (hl : ↑l.support ⊆ T) :
      Finsupp.linearCombination ℕ cls l = (∑ c ∈ l.support, (m c : ℕ) * l c) • A₀ := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    rw [hcls c (hl hc), smul_smul, mul_comm]
  ext l
  simp only [mem_compatibleConfigurations, Finset.mem_coe, Finset.mem_weightedFinsuppAntidiag]
  constructor
  · rintro ⟨hlT, -, hlA⟩
    have hsum : ∑ c ∈ l.support, (m c : ℕ) * l c = j :=
      hA₀ ((key hlT).symm.trans hlA)
    have hls : l.support ⊆ s := fun c hc ↦ hs c (hlT hc) <| by
      have := Finset.single_le_sum (f := fun c ↦ (m c : ℕ) * l c) (fun _ _ ↦ Nat.zero_le _) hc
      have := Nat.le_mul_of_pos_right (m c : ℕ) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hc))
      omega
    refine ⟨hls, ?_⟩
    rw [← hsum]
    exact (Finset.sum_subset hls fun c _ hc ↦ by simp [Finsupp.notMem_support_iff.1 hc]).symm
  · rintro ⟨hls, hsum⟩
    have hlT : ↑l.support ⊆ T := (Finset.coe_subset.2 hls).trans hsT
    refine ⟨hlT, hT.mono hlT, ?_⟩
    rw [key hlT, ← hsum,
      Finset.sum_subset hls fun c _ hc ↦ by simp [Finsupp.notMem_support_iff.1 hc]]

variable [CommRing R] {w : ι → ℕ → R}

/-- **Independent-component expansion of the ray count.** For a pairwise compatible family `T`
of tori on the ray of a class `A₀` that is not torsion, the torus `c` having class `m c • A₀` and
weights `w c k = [t ^ k] f c` given by a series `f c` with constant term `1`, the count in class
`j • A₀` of the configurations supported in `T` is the `j`-th coefficient of
`∏ c ∈ s, f c (t ^ m c)`, for every finite subfamily `s` containing the tori of class at most
`j • A₀`. -/
theorem configurationCount_eq_coeff_prod_expand (hT : T.Pairwise r)
    (hcls : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    {f : ι → R⟦X⟧} (hw : ∀ c ∈ T, ∀ k, w c k = coeff k (f c))
    (hf : ∀ c ∈ T, constantCoeff (f c) = 1) {s : Finset ι} (hsT : ↑s ⊆ T) {j : ℕ}
    (hs : ∀ c ∈ T, (m c : ℕ) ≤ j → c ∈ s) :
    configurationCount r cls w T (j • A₀) =
      coeff j (∏ c ∈ s, expand (m c) (m c).ne_zero (f c)) := by
  rw [configurationCount_def,
    compatibleConfigurations_eq_weightedFinsuppAntidiag hT hcls hA₀ hsT hs,
    finsum_mem_coe_finset, coeff_prod_expand]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [Finsupp.prod_of_support_subset l (Finset.mem_weightedFinsuppAntidiag.1 hl).1 w
    fun c hc ↦ by rw [hw c (hsT hc), coeff_zero_eq_constantCoeff_apply, hf c (hsT hc)]]
  exact Finset.prod_congr rfl fun c hc ↦ hw c (hsT hc) (l c)

/-- **The ray count is the ray series.** For a pairwise compatible family `T` of tori on the ray
of a class `A₀` that is not torsion, the torus `c` having class `m c • A₀` and the four-twist
weights `w c = w_(σ c, i c)`, the count in class `j • A₀` of the configurations supported in `T`
is the `j`-th coefficient of the ray series `∏ c ∈ s, f_(σ c, i c)(t ^ m c)`, for every finite
subfamily `s` containing the tori of class at most `j • A₀`. -/
theorem configurationCount_eq_coeff_rayTorusWeightSeries {w : ι → ℕ → ℤ} (hT : T.Pairwise r)
    (hcls : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    {σ : ι → Bool} {i : ι → Fin 4} (hw : ∀ c ∈ T, w c = torusWeight (σ c) (i c))
    {s : Finset ι} (hsT : ↑s ⊆ T) {j : ℕ} (hs : ∀ c ∈ T, (m c : ℕ) ≤ j → c ∈ s) :
    configurationCount r cls w T (j • A₀) = coeff j (rayTorusWeightSeries s m σ i) := by
  rw [rayTorusWeightSeries_def]
  exact configurationCount_eq_coeff_prod_expand hT hcls hA₀
    (fun c hc k ↦ by rw [hw c hc, torusWeight_def])
    (fun c _ ↦ constantCoeff_torusWeightSeries (σ c) (i c)) hsT hs

open scoped PowerSeries.WithPiTopology in
/-- **The generating series of the ray counts.** For a pairwise compatible family `T` of tori
on the ray of a class `A₀` that is not torsion, with finitely many tori in each class, the torus
`c` having class `m c • A₀` and the four-twist weights `w c = w_(σ c, i c)`, the series
`∑ j, N_j t ^ j` of the counts `N_j` in class `j • A₀` of the configurations supported in `T` is
the infinite product `∏_c f_(σ c, i c)(t ^ m c)` over the tori, in the coefficientwise topology
(`PowerSeries.WithPiTopology`). -/
theorem mk_configurationCount_eq_tprod {w : ι → ℕ → ℤ} (hT : T.Pairwise r)
    (hcls : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    {σ : ι → Bool} {i : ι → Fin 4} (hw : ∀ c ∈ T, w c = torusWeight (σ c) (i c))
    (hfin : ∀ n : ℕ, {c ∈ T | (m c : ℕ) ≤ n}.Finite) :
    mk (fun j ↦ configurationCount r cls w T (j • A₀)) =
      ∏' c : T, expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c)) := by
  classical
  ext j
  set s := (hfin j).toFinset
  have hsT : ↑s ⊆ T := fun c hc ↦ ((hfin j).mem_toFinset.1 hc).1
  have hm : ∀ n : ℕ, {c : T | (m c : ℕ) ≤ n}.Finite := fun n ↦
    (hfin n).preimage Subtype.val_injective.injOn |>.subset fun c hc ↦ ⟨c.2, hc⟩
  rw [coeff_mk, configurationCount_eq_coeff_rayTorusWeightSeries hT hcls hA₀ hw hsT
    fun c hc hcj ↦ (hfin j).mem_toFinset.2 ⟨hc, hcj⟩,
    coeff_tprod_expand_torusWeightSeries (m := fun c : T ↦ m c) hm (fun c ↦ σ c) (fun c ↦ i c)
      (s := s.subtype (· ∈ T))
      fun c hcj ↦ Finset.mem_subtype.2 ((hfin j).mem_toFinset.2 ⟨c.2, hcj⟩),
    rayTorusWeightSeries_def, rayTorusWeightSeries_def,
    Finset.prod_subtype_eq_prod_filter (f := fun c ↦ expand (m c) (m c).ne_zero
      (torusWeightSeries (σ c) (i c))), Finset.filter_true_of_mem fun c hc ↦ hsT hc]

end Ray

/-! ### The generating series in the Novikov completion -/

section Series

open NovikovSeries

variable [AddCommMonoid H] {N : H →+ ℝ} {r : ι → ι → Prop} {cls : ι → H} {s : Set ι}

section CommSemiring

variable [CommSemiring R]

/-- If the candidates have positive period `N` and only finitely many of them have period at most
each cutoff, then below each cutoff only finitely many classes have a nonzero count. -/
theorem finite_setOf_configurationCount_ne_zero_lt (hpos : ∀ c ∈ s, 0 < N (cls c))
    (hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite) (w : ι → ℕ → R) (C : ℝ) :
    {A | configurationCount r cls w s A ≠ 0 ∧ N A < C}.Finite := by
  refine ((finite_setOf_support_subset_area_le hpos (hfin C)).image
    (Finsupp.linearCombination ℕ cls)).subset fun A ⟨hA, hAC⟩ ↦ ?_
  rw [configurationCount_def] at hA
  obtain ⟨l, hl, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero hA
  exact ⟨l, ⟨hl.1, by rw [hl.2.2]; exact hAC.le⟩, hl.2.2⟩

variable (r cls) in
/-- The **generating series of the configuration counts**: the Novikov series `∑_A Gr(A) e^A`
whose coefficient at a class `A` is the weighted count of the compatible configurations in class
`A`. The period `N`, for instance the symplectic area, or the period of the orbit for the orbit
tori of a mapping torus, must be positive on the candidates, with finitely many candidates below
each cutoff (`TauCeti.finite_setOf_configurationCount_ne_zero_lt`). -/
noncomputable def configurationCountSeries (w : ι → ℕ → R) (hpos : ∀ c ∈ s, 0 < N (cls c))
    (hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite) : NovikovSeries R H N where
  coeff := configurationCount r cls w s
  finite_lt := finite_setOf_configurationCount_ne_zero_lt hpos hfin w

@[simp]
theorem coeff_configurationCountSeries {w : ι → ℕ → R} {hpos : ∀ c ∈ s, 0 < N (cls c)}
    {hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite} (A : H) :
    (configurationCountSeries r cls w hpos hfin).coeff A = configurationCount r cls w s A :=
  (rfl)

end CommSemiring

variable [CommRing R] {w : ι → ℕ → R} {f : ι → R⟦X⟧}

/-- With no candidates, the empty configuration in class zero is the only configuration. -/
private theorem configurationCount_empty [DecidableEq H] (A : H) :
    configurationCount r cls w ∅ A = if A = 0 then 1 else 0 := by
  split_ifs with hA
  · rw [hA]
    exact configurationCount_zero (ω := 0) fun _ hc ↦ hc.elim
  · rw [configurationCount_def, finsum_mem_eq_zero_of_forall_eq_zero]
    rintro l ⟨hl, -, hlA⟩
    rw [Finsupp.support_eq_empty.1 (Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 hl)),
      map_zero] at hlA
    exact absurd hlA.symm hA

/-- Adding to a configuration a candidate `c` that does not occur in it. -/
private theorem single_add_apply_erase {c : ι} {m : ι →₀ ℕ} (hm : m c = 0) (k : ℕ) :
    (Finsupp.single c k + m) c = k ∧ (Finsupp.single c k + m).erase c = m := by
  refine ⟨by simp [hm], ?_⟩
  rw [Finsupp.erase_add, Finsupp.erase_single, zero_add,
    Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.2 hm)]

/-- A configuration of `t`, together with a candidate `c` compatible with `t` and taken `k`
times, is a configuration of `t ∪ {c}`. -/
private theorem single_add_mem_compatibleConfigurations_insert {c : ι} {t : Set ι}
    (ht : (insert c t).Pairwise r) {m : ι →₀ ℕ} {B : H}
    (hm : m ∈ compatibleConfigurations r cls t B) (k : ℕ) :
    Finsupp.single c k + m ∈ compatibleConfigurations r cls (insert c t) (k • cls c + B) := by
  classical
  have hsupp : ↑(Finsupp.single c k + m).support ⊆ insert c t := fun d hd ↦ by
    rcases Finset.mem_union.1 (Finsupp.support_add hd) with hd | hd
    · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset hd))
    · exact Or.inr (hm.1 hd)
  refine ⟨hsupp, ht.mono hsupp, ?_⟩
  rw [map_add, Finsupp.linearCombination_single, hm.2.2]

/-- Removing a candidate `c` from a configuration of `t ∪ {c}` leaves a configuration of `t`. -/
private theorem erase_mem_compatibleConfigurations {c : ι} {t : Set ι}
    (ht : (insert c t).Pairwise r) {l : ι →₀ ℕ} {A : H}
    (hl : l ∈ compatibleConfigurations r cls (insert c t) A) :
    l.erase c ∈ compatibleConfigurations r cls t (Finsupp.linearCombination ℕ cls (l.erase c)) := by
  classical
  have hsupp : ↑(l.erase c).support ⊆ t := fun d hd ↦ by
    rw [Finset.mem_coe, Finsupp.support_erase, Finset.mem_erase] at hd
    exact (hl.1 hd.2).resolve_left hd.1
  exact ⟨hsupp, ht.mono (hsupp.trans (Set.subset_insert c t)), rfl⟩

/-- The class of a configuration splits into the contribution of `c` and the rest. -/
private theorem smul_add_linearCombination_erase (l : ι →₀ ℕ) (c : ι) :
    l c • cls c + Finsupp.linearCombination ℕ cls (l.erase c) =
      Finsupp.linearCombination ℕ cls l := by
  conv_rhs => rw [← Finsupp.single_add_erase c l]
  rw [map_add, Finsupp.linearCombination_single]

/-- Adding a candidate `c` not occurring in a configuration multiplies its weight by `w c k`. -/
private theorem prod_single_add {c : ι} {m : ι →₀ ℕ} (hm : m c = 0) (hw0 : w c 0 = 1) (k : ℕ) :
    (Finsupp.single c k + m).prod w = w c k * m.prod w := by
  rw [Finsupp.prod_add_index_of_disjoint (Finset.disjoint_of_subset_left
    Finsupp.support_single_subset (Finset.disjoint_singleton_left.2
      (Finsupp.notMem_support_iff.2 hm))), Finsupp.prod_single_index hw0]

/-- **Adding one candidate.** Let `c` be a candidate, not in `t`, compatible with every candidate
of the finite set `t`, and let its weights `w c k = [t ^ k] f c` come from a series with constant
term `1`. If `b` is the generating series of the counts over `t`, then `f c (e ^ cls c) * b` is
that of the counts over `t ∪ {c}`. -/
private theorem coeff_ofPowerSeries_mul_eq_configurationCount_insert {c : ι} {t : Set ι}
    (hct : c ∉ t) (ht : (insert c t).Pairwise r) (htfin : t.Finite)
    (hpos : ∀ d ∈ insert c t, 0 < N (cls d)) (hw : ∀ k, w c k = coeff k (f c))
    (hf : constantCoeff (f c) = 1) {b : NovikovSeries R H N}
    (hb : ∀ B, b.coeff B = configurationCount r cls w t B) (A : H) :
    (ofPowerSeries (cls c) (hpos c (Set.mem_insert c t)) (f c) * b).coeff A =
      configurationCount r cls w (insert c t) A := by
  classical
  have hγ := hpos c (Set.mem_insert c t)
  have hinj : Function.Injective fun k : ℕ ↦ k • cls c := fun k k' h ↦ by
    have h' := congrArg N h
    simp only [map_nsmul, nsmul_eq_mul] at h'
    exact_mod_cast mul_right_cancel₀ hγ.ne' h'
  have hfin (u : Set ι) (hu : u ⊆ insert c t) (B : H) :=
    finite_compatibleConfigurations (r := r) (A := B) (fun d hd ↦ hpos d (hu hd))
      (((htfin.insert c).subset hu).subset fun d hd ↦ hd.1)
  have hw0 : w c 0 = 1 := by rw [hw, coeff_zero_eq_constantCoeff_apply, hf]
  have hmc {m : ι →₀ ℕ} {B : H} (hm : m ∈ compatibleConfigurations r cls t B) : m c = 0 :=
    Finsupp.notMem_support_iff.1 fun h ↦ hct (hm.1 h)
  -- The coefficient of the product at `A` is regrouped along the map sending a configuration of
  -- `t ∪ {c}` to the class of its `c`-part and the class of the rest.
  let φ : (ι →₀ ℕ) → H × H := fun l ↦ (l c • cls c, Finsupp.linearCombination ℕ cls (l.erase c))
  set L := (hfin (insert c t) le_rfl A).toFinset
  rw [configurationCount_eq_sum (hfin (insert c t) le_rfl A),
    coeff_mul_eq_sum (s := L.image φ) (fun p hp ↦ ?_) fun u v huv hu hv ↦ ?_]
  · refine Finset.sum_image' _ fun l hl ↦ ?_
    rw [coeff_ofPowerSeries_nsmul, hb, configurationCount_eq_sum (hfin t (Set.subset_insert c t) _),
      Finset.mul_sum, ← hw]
    refine Finset.sum_nbij' (fun m ↦ Finsupp.single c (l c) + m) (fun l' ↦ l'.erase c)
      (fun m hm ↦ ?_) (fun l' hl' ↦ ?_) (fun m hm ↦ ?_) (fun l' hl' ↦ ?_) fun m hm ↦ ?_
    · rw [Set.Finite.mem_toFinset] at hm
      obtain ⟨hlc, hle⟩ := single_add_apply_erase (hmc hm) (l c)
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨?_, by simp only [φ, hlc, hle, hm.2.2]⟩
      rw [← (Set.Finite.mem_toFinset _).1 hl |>.2.2, ← smul_add_linearCombination_erase]
      exact single_add_mem_compatibleConfigurations_insert ht hm (l c)
    · rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hl'
      rw [Set.Finite.mem_toFinset, ← (Prod.ext_iff.1 hl'.2).2]
      exact erase_mem_compatibleConfigurations ht hl'.1
    · rw [Set.Finite.mem_toFinset] at hm
      exact (single_add_apply_erase (hmc hm) _).2
    · rw [Finset.mem_filter] at hl'
      rw [← hinj (Prod.ext_iff.1 hl'.2).1, Finsupp.single_add_erase]
    · rw [Set.Finite.mem_toFinset] at hm
      exact (prod_single_add (hmc hm) hw0 _).symm
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hp
    exact (smul_add_linearCombination_erase l c).trans ((Set.Finite.mem_toFinset _).1 hl).2.2
  · -- A nonzero pair of coefficients comes from a configuration of `t ∪ {c}`.
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, k • cls c = u := by
      by_contra h
      exact hu (coeff_ofPowerSeries_of_forall_nsmul_ne hγ (fun k hk ↦ h ⟨k, hk⟩) _)
    rw [hb, configurationCount_def] at hv
    obtain ⟨m, hm, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero hv
    obtain ⟨hlc, hle⟩ := single_add_apply_erase (hmc hm) k
    refine Finset.mem_image.2 ⟨Finsupp.single c k + m, (Set.Finite.mem_toFinset _).2 ?_, ?_⟩
    · rw [← huv]
      exact single_add_mem_compatibleConfigurations_insert ht hm k
    · simp only [φ, hlc, hle, hm.2.2]

/-- **Independent-component expansion over finitely many candidates.** Let the candidates of `s`
be pairwise compatible, of positive period `N`, with weights `w c k = [t ^ k] f c` given by series
`f c` with constant term `1`. For every finite family `T` of candidates, the count in class `A` of
the configurations of candidates from `T` is the coefficient at `A` of the product
`∏_{c ∈ T} f c (e ^ cls c)` of the local series at the monomials of the classes. -/
theorem configurationCount_eq_coeff_prod_ofPowerSeries (hs : s.Pairwise r)
    (hpos : ∀ c ∈ s, 0 < N (cls c)) (hw : ∀ c ∈ s, ∀ k, w c k = coeff k (f c))
    (hf : ∀ c ∈ s, constantCoeff (f c) = 1) (T : Finset s) (A : H) :
    configurationCount r cls w (Subtype.val '' (T : Set s)) A =
      (∏ c ∈ T, ofPowerSeries (cls c) (hpos c c.2) (f c)).coeff A := by
  classical
  symm
  induction T using Finset.induction_on generalizing A with
  | empty => simp [configurationCount_empty]
  | @insert c T hc ih =>
    have hsub : insert (c : ι) (Subtype.val '' (T : Set s)) ⊆ s :=
      Set.insert_subset c.2 (Set.image_subset_iff.2 fun e _ ↦ e.2)
    rw [Finset.prod_insert hc, Finset.coe_insert, Set.image_insert_eq]
    exact coeff_ofPowerSeries_mul_eq_configurationCount_insert
      (fun h ↦ hc (Subtype.val_injective.mem_set_image.1 h)) (hs.mono hsub)
      (T.finite_toSet.image _) (fun d hd ↦ hpos d (hsub hd)) (hw c c.2) (hf c c.2) ih A

/-- **The generating series is the product of the local series.** Let the candidates of `s` be
pairwise compatible, as distinct orbit tori of a mapping torus are, of positive period `N` and
finitely many below each cutoff, with weights `w c k = [t ^ k] f c` given by series `f c` with
constant term `1`. Then the generating series `∑_A Gr(A) e^A` of the configuration counts is the
infinite product `∏_c f c (e ^ cls c)` over the candidates, in the period topology. -/
theorem hasProd_ofPowerSeries_configurationCountSeries (hs : s.Pairwise r)
    (hpos : ∀ c ∈ s, 0 < N (cls c)) (hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite)
    (hw : ∀ c ∈ s, ∀ k, w c k = coeff k (f c)) (hf : ∀ c ∈ s, constantCoeff (f c) = 1) :
    HasProd (fun c : s ↦ ofPowerSeries (cls c) (hpos c c.2) (f c))
      (configurationCountSeries r cls w hpos hfin) := by
  refine tendsto_nhds_iff.2 fun C ↦ ?_
  -- Below the cutoff `C`, only the candidates of period less than `C` matter.
  have hC : {c : s | N (cls c) < C}.Finite :=
    ((hfin C).preimage Subtype.val_injective.injOn).subset fun c hc ↦ ⟨c.2, le_of_lt hc⟩
  filter_upwards [Filter.eventually_ge_atTop hC.toFinset] with T hT A hA
  rw [← configurationCount_eq_coeff_prod_ofPowerSeries hs hpos hw hf,
    coeff_configurationCountSeries]
  refine configurationCount_eq_of_area_lt (fun c hc ↦ (hpos c hc).le)
    (Set.image_subset_iff.2 fun c _ ↦ c.2) fun c hc hcT ↦ hA.trans_le (not_lt.1 fun hcC ↦ hcT ?_)
  exact ⟨⟨c, hc⟩, hT (hC.mem_toFinset.2 hcC), rfl⟩

end Series

end TauCeti
