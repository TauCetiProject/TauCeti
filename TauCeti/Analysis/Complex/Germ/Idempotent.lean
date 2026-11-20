/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Algebra
public import Mathlib.Topology.Sets.Closeds

/-!
# Idempotent holomorphic germs

For a set `s ⊆ ℂ`, a clopen subset `K` of `s` (for the subspace topology) determines the
*indicator germ* `holomorphicGerms.indicator K`. It is represented by a function holomorphic near
`s` that equals `1` near `K` and `0` near the rest of `s`; such a function exists because `ℂ` is
completely normal, so `K` and its complement in `s` have disjoint open neighbourhoods. When `s` is
the spectrum of a Banach-algebra element, the holomorphic calculus sends these germs to the Riesz
idempotents.

The indicator germs are exactly the idempotents of `holomorphicGerms s`. An idempotent germ is
determined by its values on `s`, because a continuous function satisfying `f² = f` near a point
is constant near that point. Hence the indicator germs form a copy of the Boolean algebra
`Clopens s`: the indicator of `K ⊓ L` is the product, the indicator of `Kᶜ` is `1` minus the
indicator of `K`, and a finite pairwise disjoint supremum has the sum of the indicators as its
indicator.

## Main results

* `TauCeti.holomorphicGerms.indicator`: the indicator germ of a clopen part of `s`, with its
  values `TauCeti.holomorphicGerms.eval_indicator`.
* `TauCeti.holomorphicGerms.eq_of_isIdempotentElem`: idempotent germs with the same values on `s`
  are equal; `TauCeti.holomorphicGerms.isIdempotentElem_ofFun_iff` characterizes idempotence of a
  represented germ.
* `TauCeti.holomorphicGerms.indicator_eq_ofFun`: any idempotent representative taking the value
  `1` on `s` exactly at `K` represents the indicator germ of `K`.
* `TauCeti.holomorphicGerms.isIdempotentElem_iff_exists_indicator_eq`: the idempotent germs are
  exactly the indicator germs, and `TauCeti.holomorphicGerms.indicator_injective`.
* `TauCeti.holomorphicGerms.indicator_inf`, `TauCeti.holomorphicGerms.indicator_compl`,
  `TauCeti.holomorphicGerms.indicator_sup_of_disjoint` and
  `TauCeti.holomorphicGerms.indicator_finsetSup`: compatibility with the Boolean operations.
-/

public noncomputable section

open Filter Function Set Topology TopologicalSpace

namespace TauCeti.holomorphicGerms

variable {s : Set ℂ}

/-- A clopen part `K` of `s` is represented by a function that is holomorphic near `s`, takes
only the values `0` and `1`, and equals `1` exactly at the points of `K`. -/
private theorem exists_indicator_rep (K : Clopens s) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f s ∧ (∀ z, IsIdempotentElem (f z)) ∧
      ∀ x (hx : x ∈ s), f x = 1 ↔ (⟨x, hx⟩ : s) ∈ K := by
  -- `K` and its complement in `s` are separated sets in `ℂ`.
  set P : Set ℂ := (↑) '' (K : Set s)
  set Q : Set ℂ := (↑) '' ((Kᶜ : Clopens s) : Set s)
  have hPQ : Disjoint (closure P) Q := by
    refine disjoint_left.mpr ?_
    rintro _ hy ⟨y, hyK, rfl⟩
    exact hyK (K.isClosed.closure_subset (closure_subtype.mpr hy))
  have hQP : Disjoint P (closure Q) := by
    refine disjoint_right.mpr ?_
    rintro _ hy ⟨y, hyK, rfl⟩
    exact (Kᶜ).isClosed.closure_subset (closure_subtype.mpr hy) hyK
  obtain ⟨U, V, hU, hV, hPU, hQV, hUV⟩ :=
    separatedNhds_iff_disjoint.mpr (completely_normal hPQ hQP)
  classical
  refine ⟨U.indicator 1, fun x hx ↦ ?_, fun z ↦ ?_, fun x hx ↦ ?_⟩
  · by_cases hxK : (⟨x, hx⟩ : s) ∈ K
    · have hxU : U ∈ 𝓝 x := hU.mem_nhds (hPU ⟨_, hxK, rfl⟩)
      exact (analyticAt_const (v := (1 : ℂ))).congr <|
        Filter.mem_of_superset hxU fun z hz ↦ by simp [hz]
    · have hxV : V ∈ 𝓝 x := hV.mem_nhds (hQV ⟨_, hxK, rfl⟩)
      exact (analyticAt_const (v := (0 : ℂ))).congr <|
        Filter.mem_of_superset hxV fun z hz ↦ by simp [hUV.notMem_of_mem_right hz]
  · by_cases hz : z ∈ U <;> simp [hz, IsIdempotentElem]
  · by_cases hxK : (⟨x, hx⟩ : s) ∈ K
    · simp [hPU ⟨_, hxK, rfl⟩, hxK]
    · simp [hUV.notMem_of_mem_right (hQV ⟨_, hxK, rfl⟩), hxK]

/-- The indicator germ of a clopen part `K` of `s`: it is represented by a function holomorphic
near `s` that equals `1` near `K` and `0` near the rest of `s`. -/
def indicator (K : Clopens s) : holomorphicGerms s :=
  ofFun _ (exists_indicator_rep K).choose_spec.1

@[simp]
theorem eval_indicator_of_mem {K : Clopens s} {x : ℂ} {hx : x ∈ s} (hxK : (⟨x, hx⟩ : s) ∈ K) :
    eval x hx (indicator K) = 1 := by
  rw [indicator, eval_ofFun]
  exact ((exists_indicator_rep K).choose_spec.2.2 x hx).mpr hxK

@[simp]
theorem eval_indicator_of_notMem {K : Clopens s} {x : ℂ} {hx : x ∈ s}
    (hxK : (⟨x, hx⟩ : s) ∉ K) : eval x hx (indicator K) = 0 := by
  obtain ⟨-, hidem, hK⟩ := (exists_indicator_rep K).choose_spec
  rw [indicator, eval_ofFun]
  exact (hidem x).eq_zero_or_one.resolve_right fun h ↦ hxK ((hK x hx).mp h)

/-- The indicator germ of `K` takes the value `1` on `K` and `0` on the rest of `s`. -/
theorem eval_indicator (K : Clopens s) (x : ℂ) (hx : x ∈ s) :
    eval x hx (indicator K) = (K : Set s).indicator 1 ⟨x, hx⟩ := by
  by_cases hxK : (⟨x, hx⟩ : s) ∈ K
  · simp [hxK]
  · simp [hxK]

@[simp]
theorem eval_indicator_eq_one_iff {K : Clopens s} {x : ℂ} {hx : x ∈ s} :
    eval x hx (indicator K) = 1 ↔ (⟨x, hx⟩ : s) ∈ K := by
  by_cases hxK : (⟨x, hx⟩ : s) ∈ K <;> simp [hxK]

@[simp]
theorem eval_indicator_eq_zero_iff {K : Clopens s} {x : ℂ} {hx : x ∈ s} :
    eval x hx (indicator K) = 0 ↔ (⟨x, hx⟩ : s) ∉ K := by
  by_cases hxK : (⟨x, hx⟩ : s) ∈ K <;> simp [hxK]

/-- A represented germ is idempotent exactly when its representative is idempotent near `s`. -/
theorem isIdempotentElem_ofFun_iff {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) :
    IsIdempotentElem (ofFun f hf) ↔ ∀ᶠ z in 𝓝ˢ s, IsIdempotentElem (f z) := by
  simp only [IsIdempotentElem, ← ofFun_mul, ofFun_eq_iff, EventuallyEq, Pi.mul_apply]

theorem isIdempotentElem_indicator (K : Clopens s) : IsIdempotentElem (indicator K) := by
  obtain ⟨-, hidem, -⟩ := (exists_indicator_rep K).choose_spec
  rw [indicator, isIdempotentElem_ofFun_iff]
  exact .of_forall hidem

/-- Idempotent holomorphic germs are determined by their values on the base set. -/
theorem eq_of_isIdempotentElem {g h : holomorphicGerms s} (hg : IsIdempotentElem g)
    (hh : IsIdempotentElem h) (hgh : ∀ (x : ℂ) (hx : x ∈ s), eval x hx g = eval x hx h) :
    g = h := by
  -- A function that is continuous at `x` and idempotent near `x` is constant near `x`.
  have hconst {φ : ℂ → ℂ} {x : ℂ} (hφ : ContinuousAt φ x)
      (h : ∀ᶠ z in 𝓝 x, IsIdempotentElem (φ z)) : φ =ᶠ[𝓝 x] fun _ ↦ φ x := by
    rcases h.self_of_nhds.eq_zero_or_one with hx | hx
    · filter_upwards [h, hφ.eventually_ne (hx ▸ zero_ne_one)] with z hz hz1
      exact hx ▸ hz.eq_zero_or_one.resolve_right hz1
    · filter_upwards [h, hφ.eventually_ne (hx ▸ one_ne_zero)] with z hz hz0
      exact hx ▸ hz.eq_zero_or_one.resolve_left hz0
  obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
  obtain ⟨k, hk, rfl⟩ := exists_ofFun_eq h
  have hf' := eventually_nhdsSet_iff_forall.mp ((isIdempotentElem_ofFun_iff hf).mp hg)
  have hk' := eventually_nhdsSet_iff_forall.mp ((isIdempotentElem_ofFun_iff hk).mp hh)
  rw [ofFun_eq_iff]
  refine eventually_nhdsSet_iff_forall.mpr fun x hx ↦ ?_
  filter_upwards [hconst (hf x hx).continuousAt (hf' x hx),
    hconst (hk x hx).continuousAt (hk' x hx)] with z hfz hkz
  simpa [hfz, hkz] using hgh x hx

/-- An idempotent germ is the indicator germ of `K` as soon as it takes the value `1` exactly at
the points of `K`. -/
theorem eq_indicator_of_isIdempotentElem {g : holomorphicGerms s} (hg : IsIdempotentElem g)
    {K : Clopens s} (hgK : ∀ (x : ℂ) (hx : x ∈ s), eval x hx g = 1 ↔ (⟨x, hx⟩ : s) ∈ K) :
    g = indicator K := by
  refine eq_of_isIdempotentElem hg (isIdempotentElem_indicator K) fun x hx ↦ ?_
  by_cases hxK : (⟨x, hx⟩ : s) ∈ K
  · rw [eval_indicator_of_mem hxK, hgK x hx]
    exact hxK
  · rw [eval_indicator_of_notMem hxK]
    exact (hg.map (eval x hx)).eq_zero_or_one.resolve_right fun h ↦ hxK ((hgK x hx).mp h)

/-- The indicator germ of `K` is represented by any function `χ` holomorphic near `s` that is
idempotent near `s` and takes the value `1` on `s` exactly at the points of `K`. -/
theorem indicator_eq_ofFun {χ : ℂ → ℂ} (hχ : AnalyticOnNhd ℂ χ s)
    (hidem : ∀ᶠ z in 𝓝ˢ s, IsIdempotentElem (χ z)) {K : Clopens s}
    (hK : ∀ (x : ℂ) (hx : x ∈ s), χ x = 1 ↔ (⟨x, hx⟩ : s) ∈ K) :
    indicator K = ofFun χ hχ :=
  (eq_indicator_of_isIdempotentElem ((isIdempotentElem_ofFun_iff hχ).mpr hidem)
    fun x hx ↦ by rw [eval_ofFun]; exact hK x hx).symm

/-- The idempotents of `holomorphicGerms s` are exactly the indicator germs of the clopen parts
of `s`. -/
theorem isIdempotentElem_iff_exists_indicator_eq {g : holomorphicGerms s} :
    IsIdempotentElem g ↔ ∃ K : Clopens s, indicator K = g := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := exists_ofFun_eq g
    have hidem (y : s) : IsIdempotentElem (f y) :=
      (eventually_nhdsSet_iff_forall.mp ((isIdempotentElem_ofFun_iff hf).mp hg) y y.2).self_of_nhds
    have hc : Continuous (s.domRestrict f) := hf.continuousOn.domRestrict
    -- The points where `f = 1` are also the points where `f ≠ 0`, so they form a clopen set.
    have hK : IsClopen (s.domRestrict f ⁻¹' {1}) := by
      refine ⟨isClosed_singleton.preimage hc, ?_⟩
      convert (isOpen_compl_singleton (x := (0 : ℂ))).preimage hc using 1
      ext y
      rcases (hidem y).eq_zero_or_one with h | h <;> simp [h]
    exact ⟨⟨_, hK⟩, (eq_indicator_of_isIdempotentElem hg fun x hx ↦ by simp).symm⟩
  · rintro ⟨K, rfl⟩
    exact isIdempotentElem_indicator K

theorem indicator_injective : Injective (indicator : Clopens s → holomorphicGerms s) := by
  intro K L hKL
  ext ⟨x, hx⟩
  have h := congrArg (eval x hx) hKL
  by_cases hK : (⟨x, hx⟩ : s) ∈ K <;> by_cases hL : (⟨x, hx⟩ : s) ∈ L <;> simp [hK, hL] at h ⊢

@[simp]
theorem indicator_inj {K L : Clopens s} : indicator K = indicator L ↔ K = L :=
  indicator_injective.eq_iff

@[simp]
theorem indicator_bot : indicator (⊥ : Clopens s) = 0 :=
  (eq_indicator_of_isIdempotentElem .zero fun x hx ↦ by simp [← SetLike.mem_coe]).symm

@[simp]
theorem indicator_top : indicator (⊤ : Clopens s) = 1 :=
  (eq_indicator_of_isIdempotentElem .one fun x hx ↦ by simp [← SetLike.mem_coe]).symm

@[simp]
theorem indicator_inf (K L : Clopens s) :
    indicator (K ⊓ L) = indicator K * indicator L := by
  refine (eq_indicator_of_isIdempotentElem
    ((isIdempotentElem_indicator K).mul (isIdempotentElem_indicator L)) fun x hx ↦ ?_).symm
  by_cases hK : (⟨x, hx⟩ : s) ∈ (K : Set s) <;> by_cases hL : (⟨x, hx⟩ : s) ∈ (L : Set s) <;>
    simp [hK, hL, ← SetLike.mem_coe]

@[simp]
theorem indicator_compl (K : Clopens s) : indicator Kᶜ = 1 - indicator K := by
  refine (eq_indicator_of_isIdempotentElem (isIdempotentElem_indicator K).one_sub
    fun x hx ↦ ?_).symm
  by_cases hK : (⟨x, hx⟩ : s) ∈ (K : Set s) <;> simp [hK, ← SetLike.mem_coe]

theorem indicator_sup (K L : Clopens s) :
    indicator (K ⊔ L) = indicator K + indicator L - indicator K * indicator L := by
  rw [← compl_compl (K ⊔ L), compl_sup, indicator_compl, indicator_inf, indicator_compl,
    indicator_compl]
  ring

theorem indicator_mul_indicator_of_disjoint {K L : Clopens s} (h : Disjoint K L) :
    indicator K * indicator L = 0 := by
  rw [← indicator_inf, h.eq_bot, indicator_bot]

theorem indicator_sup_of_disjoint {K L : Clopens s} (h : Disjoint K L) :
    indicator (K ⊔ L) = indicator K + indicator L := by
  rw [indicator_sup, indicator_mul_indicator_of_disjoint h, sub_zero]

/-- The indicator germ of a finite pairwise disjoint union of clopen parts is the sum of their
indicator germs. -/
theorem indicator_finsetSup {ι : Type*} {t : Finset ι} {K : ι → Clopens s}
    (hK : (t : Set ι).PairwiseDisjoint K) :
    indicator (t.sup K) = ∑ i ∈ t, indicator (K i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih =>
    rw [Finset.coe_insert] at hK
    rw [Finset.sup_insert, Finset.sum_insert hit,
      indicator_sup_of_disjoint (Finset.disjoint_sup_right.mpr fun j hj ↦
        hK (mem_insert i _) (mem_insert_of_mem _ hj) (ne_of_mem_of_not_mem hj hit).symm),
      ih (hK.subset (subset_insert _ _))]

/-- For a finite family of pairwise disjoint clopen parts covering `s`, the indicator germs sum
to `1`. -/
theorem sum_indicator_eq_one {ι : Type*} [Fintype ι] {K : ι → Clopens s}
    (hK : Pairwise (Disjoint on K)) (hcover : ∀ y : s, ∃ i, y ∈ K i) :
    ∑ i, indicator (K i) = 1 := by
  rw [← indicator_finsetSup (hK.set_pairwise _), ← indicator_top]
  congr 1
  ext y
  simpa using hcover y

end TauCeti.holomorphicGerms
