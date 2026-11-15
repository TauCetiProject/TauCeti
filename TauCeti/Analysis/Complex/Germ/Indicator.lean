/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Algebra
public import TauCeti.Topology.Sets.Clopens

/-!
# Indicator germs of clopen parts

For a set `s ⊆ ℂ` and a clopen subset `u` of `s` in its subspace topology,
`holomorphicGerms.indicator u` is the holomorphic germ along `s` which is `1` near `u` and `0`
near the rest of `s`. The two parts of `s` need not be closed in `ℂ`, but they have disjoint
neighbourhoods because `ℂ` is completely normal
(`IsClopen.disjoint_nhdsSet_image_val_compl`), so such a locally constant germ exists. It is
characterized by its local values (`holomorphicGerms.ofFun_eq_indicator_iff`).

These germs realize the Boolean algebra `Clopens s` by idempotents of `holomorphicGerms s`:
meets become products, complements become `1 - ·`, and disjoint finite joins become sums.
Applied through a holomorphic functional calculus near a spectrum, they give the Riesz
idempotents of the clopen parts of the spectrum.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.holomorphicGerms

variable {s : Set ℂ}

/-- Some function is constantly `1` near each point of the clopen part `u` of `s` and constantly
`0` near each other point of `s`. -/
private theorem exists_eventuallyEq_indicator (u : Clopens s) :
    ∃ f : ℂ → ℂ, ∀ x : s, f =ᶠ[𝓝 (x : ℂ)] fun _ ↦ (u : Set s).indicator 1 x := by
  obtain ⟨U, hU, V, hV, hUV⟩ :=
    Filter.disjoint_iff.mp u.isClopen.disjoint_nhdsSet_image_val_compl
  refine ⟨U.indicator 1, fun x ↦ ?_⟩
  by_cases hx : x ∈ u
  · filter_upwards [mem_nhdsSet_iff_forall.mp hU _ (mem_image_of_mem _ hx)] with z hz
    simp [hx, hz]
  · have hx' : x ∈ (u : Set s)ᶜ := hx
    filter_upwards [mem_nhdsSet_iff_forall.mp hV _ (mem_image_of_mem _ hx')] with z hz
    simp [hx, hUV.notMem_of_mem_right hz]

/-- The indicator germ of a clopen part `u` of `s`: the holomorphic germ along `s` that is `1`
near `u` and `0` near the rest of `s`. -/
def indicator (u : Clopens s) : holomorphicGerms s :=
  ofFun (exists_eventuallyEq_indicator u).choose fun x hx ↦
    analyticAt_const.congr ((exists_eventuallyEq_indicator u).choose_spec ⟨x, hx⟩).symm

/-- A holomorphic representative defines the indicator germ of `u` exactly when it is
constantly `1` near each point of `u` and constantly `0` near each other point of `s`. -/
theorem ofFun_eq_indicator_iff {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) (u : Clopens s) :
    ofFun f hf = indicator u ↔ ∀ x : s, f =ᶠ[𝓝 (x : ℂ)] fun _ ↦ (u : Set s).indicator 1 x := by
  have hg := (exists_eventuallyEq_indicator u).choose_spec
  refine (ofFun_eq_iff hf _).trans ?_
  rw [EventuallyEq, eventually_nhdsSet_iff_forall]
  exact ⟨fun h x ↦ EventuallyEq.trans (h x x.2) (hg x),
    fun h x hx ↦ (h ⟨x, hx⟩).trans (hg ⟨x, hx⟩).symm⟩

/-- Every representative of an indicator germ is locally constant with the indicator values. -/
private theorem exists_ofFun_eq_indicator (u : Clopens s) :
    ∃ (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s), ofFun f hf = indicator u ∧
      ∀ x : s, f =ᶠ[𝓝 (x : ℂ)] fun _ ↦ (u : Set s).indicator 1 x := by
  obtain ⟨f, hf, hfu⟩ := exists_ofFun_eq (indicator u)
  exact ⟨f, hf, hfu, (ofFun_eq_indicator_iff hf u).mp hfu⟩

/-- The indicator germ of `u` takes the value `1` on `u` and `0` on the rest of `s`. -/
@[simp]
theorem eval_indicator (x : ℂ) (hx : x ∈ s) (u : Clopens s) :
    eval x hx (indicator u) = (u : Set s).indicator 1 ⟨x, hx⟩ := by
  obtain ⟨f, hf, hfu, hloc⟩ := exists_ofFun_eq_indicator u
  rw [← hfu, eval_ofFun]
  exact (hloc ⟨x, hx⟩).eq_of_nhds

/-- Distinct clopen parts have distinct indicator germs. -/
theorem indicator_injective : Function.Injective (indicator (s := s)) := by
  intro u v huv
  ext x
  have := congrArg (eval x.1 x.2) huv
  simp only [eval_indicator, Subtype.coe_eta] at this
  by_cases hu : x ∈ (u : Set s) <;> by_cases hv : x ∈ (v : Set s) <;> simp_all

@[simp]
theorem indicator_inj {u v : Clopens s} : indicator u = indicator v ↔ u = v :=
  indicator_injective.eq_iff

@[simp]
theorem indicator_top : indicator (⊤ : Clopens s) = 1 := by
  have h : ofFun (fun _ ↦ (1 : ℂ)) analyticOnNhd_const = indicator (⊤ : Clopens s) :=
    (ofFun_eq_indicator_iff _ _).mpr fun x ↦ by simp
  rw [← h, ofFun_const, map_one]

@[simp]
theorem indicator_bot : indicator (⊥ : Clopens s) = 0 := by
  have h : ofFun (fun _ ↦ (0 : ℂ)) analyticOnNhd_const = indicator (⊥ : Clopens s) :=
    (ofFun_eq_indicator_iff _ _).mpr fun x ↦ by simp
  rw [← h, ofFun_const, map_zero]

/-- The indicator germ of a meet is the product of the indicator germs. -/
theorem indicator_inf (u v : Clopens s) : indicator (u ⊓ v) = indicator u * indicator v := by
  obtain ⟨f, hf, hfu, hlf⟩ := exists_ofFun_eq_indicator u
  obtain ⟨g, hg, hgv, hlg⟩ := exists_ofFun_eq_indicator v
  rw [← hfu, ← hgv, ← ofFun_mul, eq_comm, ofFun_eq_indicator_iff]
  intro x
  filter_upwards [hlf x, hlg x] with z hfz hgz
  rw [Pi.mul_apply, hfz, hgz, Clopens.coe_inf, Set.inter_indicator_one, Pi.mul_apply]

/-- The indicator germ of a join of disjoint clopen parts is the sum of their indicator germs. -/
theorem indicator_sup_of_disjoint {u v : Clopens s} (huv : Disjoint u v) :
    indicator (u ⊔ v) = indicator u + indicator v := by
  obtain ⟨f, hf, hfu, hlf⟩ := exists_ofFun_eq_indicator u
  obtain ⟨g, hg, hgv, hlg⟩ := exists_ofFun_eq_indicator v
  rw [← hfu, ← hgv, ← ofFun_add, eq_comm, ofFun_eq_indicator_iff]
  have hd : Disjoint (u : Set s) v := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Clopens.coe_inf, huv.eq_bot, Clopens.coe_bot]
  intro x
  filter_upwards [hlf x, hlg x] with z hfz hgz
  rw [Pi.add_apply, hfz, hgz, Clopens.coe_sup, Set.indicator_union_of_disjoint hd]

/-- The indicator germ of a complement is one minus the indicator germ. -/
theorem indicator_compl (u : Clopens s) : indicator uᶜ = 1 - indicator u := by
  rw [eq_sub_iff_add_eq', ← indicator_sup_of_disjoint disjoint_compl_right, sup_compl_eq_top,
    indicator_top]

/-- The indicator germ of a join, by inclusion–exclusion. -/
theorem indicator_sup (u v : Clopens s) :
    indicator (u ⊔ v) = indicator u + indicator v - indicator u * indicator v := by
  rw [← compl_compl (u ⊔ v), indicator_compl, compl_sup, indicator_inf, indicator_compl,
    indicator_compl]
  ring

/-- Indicator germs are idempotent. -/
theorem isIdempotentElem_indicator (u : Clopens s) : IsIdempotentElem (indicator u) := by
  rw [IsIdempotentElem, ← indicator_inf, inf_idem]

/-- Indicator germs of disjoint clopen parts are orthogonal. -/
theorem indicator_mul_indicator_of_disjoint {u v : Clopens s} (huv : Disjoint u v) :
    indicator u * indicator v = 0 := by
  rw [← indicator_inf, huv.eq_bot, indicator_bot]

/-- The indicator germ of a finite join of pairwise disjoint clopen parts is the sum of their
indicator germs. -/
theorem indicator_finset_sup {ι : Type*} (I : Finset ι) (u : ι → Clopens s)
    (hu : (I : Set ι).PairwiseDisjoint u) : indicator (I.sup u) = ∑ i ∈ I, indicator (u i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.coe_insert] at hu
    rw [Finset.sup_insert, Finset.sum_insert hi, indicator_sup_of_disjoint, ih (hu.subset
      (subset_insert _ _))]
    exact Finset.disjoint_sup_right.mpr fun j hj ↦
      hu (mem_insert i _) (mem_insert_of_mem _ hj) fun h ↦ hi (h ▸ hj)

end TauCeti.holomorphicGerms
