/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Extending totally real subspaces to maximal ones

Let `J` be an endomorphism of a finite-dimensional vector space `E` over a linearly ordered field
with `J² = -1`. Every totally real subspace `L` of `E` (one meeting `J(L)` only in `0`) is contained
in a maximal totally real subspace, one complementary to its `J`-image
(`TauCeti.IsTotallyReal.exists_le_isMaximalTotallyReal`). In particular maximal totally real
subspaces exist, and any vector `v ≠ 0` lies in one, since the line through `v` is totally real.

The proof enlarges a totally real subspace `L` by a vector `e` outside `L ⊔ J(L)`. The subspace
`L ⊔ J(L)` is `J`-invariant, and on it `t - s J` is invertible for `(t, s) ≠ 0`, with inverse
`(t + s J) / (t² + s²)`; so `t e - s J e ∈ L ⊔ J(L)` forces `t = s = 0`, which is what keeps
`L ⊔ K e` totally real. In the real case this is the statement that a complex vector space has a
basis over `ℂ` extending any `ℂ`-independent family, read through its real points.

## Main results

* `TauCeti.IsTotallyReal.sup_span_singleton`: a totally real subspace stays totally real after
  adding a vector outside `L ⊔ J(L)`.
* `TauCeti.IsTotallyReal.exists_le_isMaximalTotallyReal`: every totally real subspace lies in a
  maximal totally real subspace.
* `TauCeti.exists_mem_isMaximalTotallyReal`: every vector lies in a maximal totally real subspace.
-/

public section

namespace TauCeti

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E] {J : E →ₗ[K] E} {L : Submodule K E}

/-- If `J² = -1` and `t e - s J e` lies in a `J`-invariant subspace `M` not containing `e`, then
`t = s = 0`. -/
private theorem eq_zero_of_sub_smul_mem (hJ : J.comp J = -LinearMap.id) {M : Submodule K E}
    (hM : ∀ m ∈ M, J m ∈ M) {e : E} (he : e ∉ M) {t s : K} (h : t • e - s • J e ∈ M) :
    t = 0 ∧ s = 0 := by
  have hJJ : J (J e) = -e := by simpa using LinearMap.congr_fun hJ e
  -- Applying `t + s J` gives `(t² + s²) e ∈ M`.
  have hsum : (t * t + s * s) • e ∈ M := by
    have h' := M.add_mem (M.smul_mem t h) (M.smul_mem s (hM _ h))
    convert h' using 1
    simp only [map_sub, map_smul, hJJ]
    module
  by_contra hts
  have hpos : t * t + s * s ≠ 0 := by
    rw [not_and_or] at hts
    rcases hts with ht | hs
    · exact (add_pos_of_pos_of_nonneg (mul_self_pos.2 ht) (mul_self_nonneg s)).ne'
    · exact (add_pos_of_nonneg_of_pos (mul_self_nonneg t) (mul_self_pos.2 hs)).ne'
  exact he ((M.smul_mem_iff hpos).1 hsum)

/-- Adding to a totally real subspace `L` a vector outside `L ⊔ J(L)` keeps it totally real,
when `J² = -1`. -/
theorem IsTotallyReal.sup_span_singleton (hJ : J.comp J = -LinearMap.id) (hL : IsTotallyReal J L)
    {e : E} (he : e ∉ L ⊔ L.map J) : IsTotallyReal J (L ⊔ K ∙ e) := by
  have hJJ : ∀ v, J (J v) = -v := fun v ↦ by simpa using LinearMap.congr_fun hJ v
  have hM : ∀ m ∈ L ⊔ L.map J, J m ∈ L ⊔ L.map J := by
    intro m hm
    obtain ⟨l, hl, _, ⟨l', hl', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hm
    rw [map_add, hJJ]
    exact Submodule.mem_sup.2 ⟨-l', L.neg_mem hl', J l, Submodule.mem_map_of_mem hl, add_comm _ _⟩
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  intro z hz hzJ
  obtain ⟨l, hl, _, hte, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hte
  obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.1 hzJ
  obtain ⟨l', hl', _, hse, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hse
  -- From `l + t e = J l' + s J e`, the vector `t e - s J e = J l' - l` lies in `L ⊔ J(L)`.
  have hmem : t • e - s • J e ∈ L ⊔ L.map J := by
    have : t • e - s • J e = -l + J l' := by
      rw [map_add, map_smul] at hwz
      rw [← sub_eq_zero] at hwz ⊢
      convert congrArg Neg.neg hwz using 1 <;> abel
    rw [this]
    exact Submodule.add_mem_sup (L.neg_mem hl) (Submodule.mem_map_of_mem hl')
  obtain ⟨rfl, rfl⟩ := eq_zero_of_sub_smul_mem hJ hM he hmem
  simp only [zero_smul, add_zero] at hwz ⊢
  exact Submodule.disjoint_def.1 hL.disjoint l hl (hwz ▸ Submodule.mem_map_of_mem hl')

variable [FiniteDimensional K E]

/-- **Totally real subspaces extend to maximal ones.** If `J² = -1` on a finite-dimensional
space, every totally real subspace is contained in a maximal totally real subspace. -/
theorem IsTotallyReal.exists_le_isMaximalTotallyReal (hJ : J.comp J = -LinearMap.id)
    (hL : IsTotallyReal J L) : ∃ L', L ≤ L' ∧ IsMaximalTotallyReal J L' := by
  obtain ⟨L', ⟨hLL', hL'⟩, hmax⟩ := (wellFounded_gt (α := Submodule K E)).has_min
    {L' | L ≤ L' ∧ IsTotallyReal J L'} ⟨L, le_rfl, hL⟩
  refine ⟨L', hLL', (isMaximalTotallyReal_iff J L').2
    (isCompl_iff.2 ⟨hL'.disjoint, codisjoint_iff.2 ?_⟩)⟩
  by_contra hne
  obtain ⟨e, -, he⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  refine hmax (L' ⊔ K ∙ e) ⟨hLL'.trans le_sup_left, hL'.sup_span_singleton hJ he⟩ ?_
  exact lt_of_le_of_ne le_sup_left fun h ↦
    he (Submodule.mem_sup_left (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self e)))

/-- If `J² = -1` on a finite-dimensional space, every vector lies in a maximal totally real
subspace. -/
theorem exists_mem_isMaximalTotallyReal (hJ : J.comp J = -LinearMap.id) (v : E) :
    ∃ L, v ∈ L ∧ IsMaximalTotallyReal J L := by
  have hJJ : ∀ w, J (J w) = -w := fun w ↦ by simpa using LinearMap.congr_fun hJ w
  have hline : IsTotallyReal J (K ∙ v) := by
    rw [isTotallyReal_iff, Submodule.disjoint_def]
    intro z hz hzJ
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.1 hzJ
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hmem : t • v - s • J v ∈ (⊥ : Submodule K E) := by
      rw [map_smul] at hwz
      rw [hwz, sub_self]
      exact Submodule.zero_mem _
    by_cases hv : v = 0
    · simp [hv]
    · have := eq_zero_of_sub_smul_mem hJ (M := ⊥) (by simp) (by simpa using hv) hmem
      simp [this.1]
  obtain ⟨L, hle, hL⟩ := hline.exists_le_isMaximalTotallyReal hJ
  exact ⟨L, hle (Submodule.mem_span_singleton_self v), hL⟩

end TauCeti
