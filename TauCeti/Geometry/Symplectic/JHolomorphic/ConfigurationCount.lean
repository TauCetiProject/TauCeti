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
public import TauCeti.Geometry.Symplectic.JHolomorphic.GoodCycle
public import TauCeti.Geometry.Symplectic.JHolomorphic.TorusWeight

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
empty configuration is the only one in class `0` (`TauCeti.configurationCount_zero`). For
the same reason the count vanishes in every nonzero class of nonpositive area
(`TauCeti.configurationCount_eq_zero_of_area_nonpos`), in particular in every nonzero torsion
class (`TauCeti.configurationCount_eq_zero_of_isOfFinAddOrder`): a torsion class has zero area
but is not the class of the empty configuration.

With an intersection form `B` on `H`, under which compatible candidates have intersection
number zero, a component `c` of a configuration in class `A` satisfies `A · c = l c (c · c)`
(`TauCeti.apply_eq_mul_apply_self_of_mem_compatibleConfigurations`). This gives two further
vanishing theorems. If `S` is an exceptional sphere, which other candidates meet nonnegatively
and which counts only with multiplicity one, then the count vanishes in every class `A` with
`A · S < -1`, that is, in every class that is not good
(`TauCeti.configurationCount_eq_zero_of_apply_lt_neg_one`). If every candidate has nonnegative
virtual dimension `d(c) = c · c - κ · c` and only candidates of nonnegative square count with
higher multiplicity, then `d(A) = ∑ l c (d(c) + (l c - 1) c · c)`, so the count vanishes in
classes of negative virtual dimension
(`TauCeti.configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg`).

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
* `TauCeti.configurationCount_eq_zero_of_area_nonpos`,
  `TauCeti.configurationCount_eq_zero_of_isOfFinAddOrder`: vanishing in nonzero classes of
  nonpositive area and in nonzero torsion classes.
* `TauCeti.apply_eq_sum_of_mem_compatibleConfigurations`,
  `TauCeti.apply_eq_sum_of_mem_compatibleConfigurations'`: the pairing of the class of a
  configuration with any class, in either slot, expanded over the components.
* `TauCeti.apply_eq_mul_apply_self_of_mem_compatibleConfigurations`,
  `TauCeti.apply_self_sub_apply_canonical_eq_sum_of_mem_compatibleConfigurations`: intersection
  numbers and virtual dimension of the class of a configuration.
* `TauCeti.configurationCount_eq_zero_of_apply_lt_neg_one`: vanishing in a class that is not
  good.
* `TauCeti.configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg`: vanishing in negative
  virtual dimension.
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

/-- **Finiteness of configurations.** If the candidates have positive area and only finitely
many of them have area at most `ω A`, then there are only finitely many configurations in
class `A`. -/
theorem finite_compatibleConfigurations (hfin : {c ∈ s | ω (cls c) ≤ ω A}.Finite) :
    (compatibleConfigurations r cls s A).Finite := by
  classical
  refine (hfin.toFinset.finsupp fun c ↦ Finset.range (⌊ω A / ω (cls c)⌋₊ + 1)).finite_toSet.subset
    fun l hl ↦ ?_
  rw [Finset.mem_coe, Finset.mem_finsupp_iff]
  have hnonneg : ∀ c ∈ s, 0 ≤ ω (cls c) := fun c hc ↦ (hpos c hc).le
  refine ⟨fun c hc ↦ hfin.mem_toFinset.2
    ⟨hl.1 hc, area_le_of_mem_compatibleConfigurations hnonneg hl hc⟩, fun c hc ↦ ?_⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.le_floor ((le_div_iff₀ (hpos c (hfin.mem_toFinset.1 hc).1)).2
    (mul_area_le_of_mem_compatibleConfigurations hnonneg hl c))

/-- If the candidates have positive area, a configuration in a class of nonpositive area is
empty. -/
theorem eq_zero_of_mem_compatibleConfigurations_of_area_nonpos
    (hl : l ∈ compatibleConfigurations r cls s A) (hA : ω A ≤ 0) : l = 0 :=
  Finsupp.support_eq_empty.1 <| Finset.eq_empty_of_forall_notMem fun c hc ↦
    (hpos c (hl.1 hc)).not_ge <|
      (area_le_of_mem_compatibleConfigurations (fun c hc ↦ (hpos c hc).le) hl hc).trans hA

/-- The empty configuration is the only configuration in class zero. -/
theorem compatibleConfigurations_zero : compatibleConfigurations r cls s 0 = {0} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_compatibleConfigurations_iff.2 rfl,
    fun _ hl ↦ eq_zero_of_mem_compatibleConfigurations_of_area_nonpos hpos hl (map_zero ω).le⟩

/-- If the candidates have positive area, there is no configuration in a nonzero class of
nonpositive area. -/
theorem compatibleConfigurations_eq_empty_of_area_nonpos (hA : ω A ≤ 0) (hA₀ : A ≠ 0) :
    compatibleConfigurations r cls s A = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hl ↦ hA₀ <| zero_mem_compatibleConfigurations_iff.1 <|
    eq_zero_of_mem_compatibleConfigurations_of_area_nonpos hpos hl hA ▸ hl

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

/-- If the candidates have positive area, the count vanishes in nonzero classes of nonpositive
area. -/
theorem configurationCount_eq_zero_of_area_nonpos (hpos : ∀ c ∈ s, 0 < ω (cls c))
    (hA : ω A ≤ 0) (hA₀ : A ≠ 0) : configurationCount r cls w s A = 0 := by
  rw [configurationCount_def, compatibleConfigurations_eq_empty_of_area_nonpos hpos hA hA₀,
    finsum_mem_empty]

/-- If the candidates have positive area, the count vanishes in every nonzero torsion class. -/
theorem configurationCount_eq_zero_of_isOfFinAddOrder (hpos : ∀ c ∈ s, 0 < ω (cls c))
    (hA : IsOfFinAddOrder A) (hA₀ : A ≠ 0) : configurationCount r cls w s A = 0 :=
  configurationCount_eq_zero_of_area_nonpos hpos (ω.isOfFinAddOrder hA).eq_zero'.le hA₀

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

/-! ### Intersection numbers of configurations -/

section Intersection

open LinearMap (BilinForm)

variable [AddCommGroup H] {B : BilinForm ℤ H} {r : ι → ι → Prop} {cls : ι → H} {s : Set ι}
  {A : H} {l : ι →₀ ℕ}

/-- The pairing of the class of a configuration, in the left slot, with a class `x`, expanded
over the components. -/
theorem apply_eq_sum_of_mem_compatibleConfigurations
    (hl : l ∈ compatibleConfigurations r cls s A) (x : H) :
    B A x = ∑ c ∈ l.support, (l c : ℤ) * B (cls c) x := by
  simp [← hl.2.2, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.sum_apply,
    map_nsmul]

/-- The pairing of a class `x` with the class of a configuration, in the right slot, expanded
over the components: `apply_eq_sum_of_mem_compatibleConfigurations` for the flipped form. -/
theorem apply_eq_sum_of_mem_compatibleConfigurations'
    (hl : l ∈ compatibleConfigurations r cls s A) (x : H) :
    B x A = ∑ c ∈ l.support, (l c : ℤ) * B x (cls c) :=
  apply_eq_sum_of_mem_compatibleConfigurations (B := B.flip) hl x

/-- A component `c` of a configuration meets the class of the configuration only through itself:
if every candidate compatible with `c` has intersection number zero with it, as for disjoint
images, then `A · c = l c (c · c)`. -/
theorem apply_eq_mul_apply_self_of_mem_compatibleConfigurations {c : ι}
    (hr : ∀ b ∈ s, b ≠ c → r b c → B (cls b) (cls c) = 0)
    (hl : l ∈ compatibleConfigurations r cls s A) (hc : c ∈ l.support) :
    B A (cls c) = l c * B (cls c) (cls c) := by
  classical
  rw [apply_eq_sum_of_mem_compatibleConfigurations hl, ← Finset.add_sum_erase _ _ hc,
    add_eq_left]
  refine Finset.sum_eq_zero fun b hb ↦ ?_
  have hbc := Finset.ne_of_mem_erase hb
  rw [hr b (hl.1 (Finset.mem_of_mem_erase hb)) hbc
    (hl.2.1 (Finset.mem_of_mem_erase hb) hc hbc), mul_zero]

/-- If every candidate other than `S` meets `S` nonnegatively, as positivity of intersections
gives for distinct pseudoholomorphic images, then the class of a configuration not containing
`S` meets `S` nonnegatively. -/
theorem apply_nonneg_of_mem_compatibleConfigurations {S : ι}
    (hpos : ∀ c ∈ s, c ≠ S → 0 ≤ B (cls c) (cls S))
    (hl : l ∈ compatibleConfigurations r cls s A) (hS : l S = 0) : 0 ≤ B A (cls S) := by
  rw [apply_eq_sum_of_mem_compatibleConfigurations hl]
  refine Finset.sum_nonneg fun c hc ↦ mul_nonneg (Int.natCast_nonneg _) (hpos c (hl.1 hc) ?_)
  rintro rfl
  exact Finsupp.mem_support_iff.1 hc hS

/-- The virtual dimension `d(A) = A · A - κ · A` of the class of a configuration whose compatible
components have intersection number zero, as for disjoint images, is
`∑ l c (l c (c · c) - κ · c)`. -/
theorem apply_self_sub_apply_canonical_eq_sum_of_mem_compatibleConfigurations
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hl : l ∈ compatibleConfigurations r cls s A) (κ : H) :
    B A A - B κ A =
      ∑ c ∈ l.support, (l c : ℤ) * (l c * B (cls c) (cls c) - B κ (cls c)) := by
  have hA : ∑ c : l.support, l c • cls c = A := by
    rw [← hl.2.2, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_coe_sort l.support fun c ↦ l c • cls c]
  rw [cycle_apply_self_sub_apply_canonical_eq_sum_add_sum (B := B) (κ := κ) hA,
    Finset.sum_coe_sort l.support fun c ↦ (l c : ℤ) * (B (cls c) (cls c) - B κ (cls c)),
    Finset.sum_coe_sort l.support fun c ↦ (l c : ℤ) * (B A (cls c) - B (cls c) (cls c)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [apply_eq_mul_apply_self_of_mem_compatibleConfigurations
    (fun b hb hbc ↦ hr b hb c (hl.1 hc) hbc) hl hc]
  ring

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Vanishing in a bad class.** Let `S` be a candidate of self-intersection at least `-1`, such
as an exceptional sphere, which every other candidate meets nonnegatively and compatible
candidates do not meet, and which is counted only with multiplicity one: `w S k = 0` for
`k ≥ 2`. If `A · S < -1`, that is, if `A` is not good, then the count in class `A`
vanishes. -/
theorem configurationCount_eq_zero_of_apply_lt_neg_one {S : ι}
    (hr : ∀ c ∈ s, c ≠ S → r c S → B (cls c) (cls S) = 0)
    (hpos : ∀ c ∈ s, c ≠ S → 0 ≤ B (cls c) (cls S)) (hS : -1 ≤ B (cls S) (cls S))
    (hw : ∀ k, 2 ≤ k → w S k = 0) (hA : B A (cls S) < -1) :
    configurationCount r cls w s A = 0 := by
  rw [configurationCount_def]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun l hl ↦ ?_
  have hlS : l S ≠ 0 := fun h ↦
    (apply_nonneg_of_mem_compatibleConfigurations hpos hl h).not_gt (by linarith)
  have hSl : S ∈ l.support := Finsupp.mem_support_iff.2 hlS
  have hA' := apply_eq_mul_apply_self_of_mem_compatibleConfigurations hr hl hSl
  have h2 : 2 ≤ l S := by
    by_contra h
    have h1 : l S = 1 := by omega
    rw [h1, Nat.cast_one, one_mul] at hA'
    linarith
  rw [Finsupp.prod]
  exact Finset.prod_eq_zero hSl (hw _ h2)

/-- **Vanishing in negative virtual dimension.** Suppose compatible candidates have intersection
number zero, as for disjoint images, every candidate has nonnegative virtual dimension
`d(c) = c · c - κ · c`, as for the simple curves of a generic almost complex structure, and only
candidates of nonnegative square are counted with multiplicity at least two, such as square-zero
tori. If `d(A) = A · A - κ · A < 0`, then the count in class `A` vanishes. -/
theorem configurationCount_eq_zero_of_apply_self_sub_apply_canonical_neg {κ : H}
    (hr : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b → B (cls a) (cls b) = 0)
    (hind : ∀ c ∈ s, 0 ≤ B (cls c) (cls c) - B κ (cls c))
    (hmult : ∀ c ∈ s, ∀ k, 2 ≤ k → w c k ≠ 0 → 0 ≤ B (cls c) (cls c))
    (hA : B A A - B κ A < 0) : configurationCount r cls w s A = 0 := by
  rw [configurationCount_def]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun l hl ↦ ?_
  rw [Finsupp.prod]
  by_contra hne
  refine hA.not_ge ?_
  rw [apply_self_sub_apply_canonical_eq_sum_of_mem_compatibleConfigurations hr hl]
  refine Finset.sum_nonneg fun c hc ↦ mul_nonneg (Int.natCast_nonneg _) ?_
  have hd := hind c (hl.1 hc)
  have hl0 := Finsupp.mem_support_iff.1 hc
  rcases Nat.lt_or_ge (l c) 2 with h | h
  · have h1 : l c = 1 := by omega
    rw [h1, Nat.cast_one, one_mul]
    exact hd
  · have hsq := hmult c (hl.1 hc) _ h fun hw ↦ hne (Finset.prod_eq_zero hc hw)
    have h' : (2 : ℤ) ≤ l c := by exact_mod_cast h
    nlinarith

end Intersection

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

end TauCeti
