/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Empty-domain, finite-support, and Cauchy-vanishing lemmas for `HasProdUniformlyOn`

This file supplements `Mathlib.Topology.Algebra.InfiniteSum.UniformOn` with three basic pieces of
infrastructure for uniform infinite products and sums on a set `s`:

1. **Empty set**: `HasProdUniformlyOn` and `MultipliableUniformlyOn` hold vacuously on `∅`.
2. **Finite support**: finite index types (`[Fintype ι]`) and families whose factors equal `1` on
   `s` outside a finite set converge uniformly on `s` without any boundedness or completeness
   assumptions on the remaining factors.
3. **Uniform Cauchy vanishing**: `MultipliableUniformlyOn.vanishing` (and its additive counterpart
   `SummableUniformlyOn.vanishing`) lifts `Multipliable.vanishing` to uniform convergence on `s`.

## Main declarations

* `TauCeti.hasProdUniformlyOn_empty`, `TauCeti.multipliableUniformlyOn_empty`: vacuous uniform
  convergence on `∅` (with `@[to_additive]` `hasSumUniformlyOn_empty` and
  `summableUniformlyOn_empty`).
* `TauCeti.hasProdUniformlyOn_fintype`, `TauCeti.hasProdUniformlyOn_prod_of_ne_finset_one`,
  `TauCeti.hasProdUniformlyOn_of_cofinite_eq_one`,
  `TauCeti.multipliableUniformlyOn_of_cofinite_eq_one`: uniform convergence when all but finitely
  many factors are `1` on `s` (and additive `0` counterparts).
* `MultipliableUniformlyOn.vanishing`, `SummableUniformlyOn.vanishing`: uniform disjoint-finset
  tail vanishing into any neighborhood of `1` (resp. `0`).
-/

public section

open Filter Finset Function Set Topology
open scoped BigOperators UniformConvergence

namespace TauCeti

section CommMonoid

variable {ι β α : Type*} [CommMonoid α] [UniformSpace α]

/-- Uniform infinite-product convergence on the empty set holds vacuously. -/
@[to_additive (attr := simp) /-- Uniform infinite-sum convergence on the empty set holds
vacuously. -/]
theorem hasProdUniformlyOn_empty (f : ι → β → α) (g : β → α) :
    HasProdUniformlyOn f g ∅ :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr tendstoUniformlyOn_empty

/-- Every family is uniformly multipliable on the empty set. -/
@[to_additive (attr := simp) /-- Every family is uniformly summable on the empty set. -/]
theorem multipliableUniformlyOn_empty (f : ι → β → α) :
    MultipliableUniformlyOn f ∅ :=
  ⟨1, hasProdUniformlyOn_empty f 1⟩

/-- If every factor outside a finite set `t` equals `1` on `s`, then the partial products converge
uniformly on `s` to `fun x ↦ ∏ i ∈ t, f i x`, even if the factors in `t` are unbounded on `s`. -/
@[to_additive /-- If every term outside a finite set `t` vanishes on `s`, then the partial sums
converge uniformly on `s` to `fun x ↦ ∑ i ∈ t, f i x`, even if the terms in `t` are unbounded on
`s`. -/]
theorem hasProdUniformlyOn_prod_of_ne_finset_one {f : ι → β → α} {s : Set β} {t : Finset ι}
    (hf : ∀ i ∉ t, ∀ x ∈ s, f i x = 1) :
    HasProdUniformlyOn f (fun x ↦ ∏ i ∈ t, f i x) s := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  intro u hu
  refine eventually_atTop.mpr ⟨t, fun b htb x hx ↦ ?_⟩
  dsimp only
  rw [Finset.prod_subset htb fun i _ hit ↦ hf i hit x hx]
  exact refl_mem_uniformity hu

/-- Over a finite index type, finite partial products converge uniformly on any set `s` to the full
product, with no topological separation or boundedness hypotheses. -/
@[to_additive /-- Over a finite index type, finite partial sums converge uniformly on any set `s`
to the full sum, with no topological separation or boundedness hypotheses. -/]
theorem hasProdUniformlyOn_fintype [Fintype ι] (f : ι → β → α) (s : Set β) :
    HasProdUniformlyOn f (fun x ↦ ∏ i, f i x) s :=
  hasProdUniformlyOn_prod_of_ne_finset_one (t := Finset.univ)
    fun i hi ↦ (hi (Finset.mem_univ i)).elim

/-- If cofinitely many factors equal `1` on `s`, then `f` is uniformly multipliable on `s`. -/
@[to_additive /-- If cofinitely many terms vanish on `s`, then `f` is uniformly summable on `s`. -/]
theorem multipliableUniformlyOn_of_cofinite_eq_one {f : ι → β → α} {s : Set β}
    (hf : ∀ᶠ i in cofinite, ∀ x ∈ s, f i x = 1) :
    MultipliableUniformlyOn f s := by
  classical
  have hfin : {i | ¬ ∀ x ∈ s, f i x = 1}.Finite := eventually_cofinite.mp hf
  refine (hasProdUniformlyOn_prod_of_ne_finset_one (t := hfin.toFinset)
    fun i hi ↦ ?_).multipliableUniformlyOn
  by_contra h
  exact hi (hfin.mem_toFinset.mpr h)

/-- If cofinitely many factors equal `1` on `s`, then `∏ i ∈ b, f i x` converges uniformly on `s`
to `∏' i, f i x`. -/
@[to_additive /-- If cofinitely many terms vanish on `s`, then `∑ i ∈ b, f i x` converges uniformly
on `s` to `∑' i, f i x`. -/]
theorem hasProdUniformlyOn_of_cofinite_eq_one {f : ι → β → α} {s : Set β}
    (hf : ∀ᶠ i in cofinite, ∀ x ∈ s, f i x = 1) :
    HasProdUniformlyOn f (fun x ↦ ∏' i, f i x) s :=
  (multipliableUniformlyOn_of_cofinite_eq_one hf).hasProdUniformlyOn

end CommMonoid

end TauCeti

namespace MultipliableUniformlyOn

/-- **Uniform Cauchy vanishing.** If `f : ι → β → G` is uniformly multipliable on `s` into a
uniform commutative group `G`, then for every neighborhood `e ∈ 𝓝 1` there is a finite set `t`
such that every finite product disjoint from `t` lands in `e` uniformly across `x ∈ s`. -/
@[to_additive /-- **Uniform Cauchy vanishing.** If `f : ι → β → G` is uniformly summable on `s`
into a uniform additive commutative group `G`, then for every neighborhood `e ∈ 𝓝 0` there is a
finite set `t` such that every finite sum disjoint from `t` lands in `e` uniformly across
`x ∈ s`. -/]
theorem vanishing {ι β G : Type*} [CommGroup G] [UniformSpace G] [IsUniformGroup G]
    {f : ι → β → G} {s : Set β} (hf : MultipliableUniformlyOn f s) {e : Set G}
    (he : e ∈ 𝓝 (1 : G)) :
    ∃ t : Finset ι, ∀ r : Finset ι, Disjoint r t → ∀ x ∈ s, (∏ i ∈ r, f i x) ∈ e := by
  have hdir : DirectedOn (· ⊆ ·) ({s} : Set (Set β)) := by simp [DirectedOn]
  have he' : {g : β →ᵤ[{s}] G | ∀ x ∈ s, UniformOnFun.toFun {s} g x ∈ e} ∈ 𝓝 (1 : β →ᵤ[{s}] G) :=
    (UniformOnFun.hasBasis_nhds_one_of_basis {s} (singleton_nonempty s) hdir
      (basis_sets _)).mem_iff.mpr ⟨(s, e), ⟨rfl, he⟩, fun _ hg ↦ hg⟩
  obtain ⟨t, ht⟩ := Multipliable.vanishing hf he'
  refine ⟨t, fun r hrt x hx ↦ ?_⟩
  simpa [← UniformOnFun.ofFun_prod, Finset.prod_apply] using ht r hrt x hx

end MultipliableUniformlyOn
