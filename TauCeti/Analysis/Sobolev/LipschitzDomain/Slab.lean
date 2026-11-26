/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic

/-!
# The slab between two parallel hyperplanes

For `a < b`, the open slab `{x | a < x.fst < b}` of the model space `WithLp 2 (ℝ × E)` lies
between the hyperplanes `{a} × E` and `{b} × E`. This file proves that it is a Lipschitz domain
with constant `0` for every `E` (`Set.isLipschitzDomainWith_setOf_fst_mem_Ioo`): at a point of
the lower face a translation is a chart with the flat graph `0`, and at a point of the upper face
a translation followed by the reflection `(t, y) ↦ (-t, y)` of the normal coordinate is one.

When `E` is the zero space the slab is the interval `(a, b)` itself, embedded in
`WithLp 2 (ℝ × E) ≃ ℝ`, and it is bounded (`TauCeti.isBounded_setOf_fst_mem_Ioo`). This is how the
trace theory of bounded Lipschitz domains of `ℝ × E` covers intervals, in dimension `dim E = 0`.
-/

public section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] {a b : ℝ}

/-- The slab `{x | a < x.fst < b}` is open. -/
theorem isOpen_setOf_fst_mem_Ioo : IsOpen {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b} :=
  isOpen_Ioo.preimage (WithLp.continuous_fst ..)

/-- A frontier point of the slab `{x | a < x.fst < b}` lies on one of its two faces. -/
theorem fst_eq_or_fst_eq_of_mem_frontier_setOf_fst_mem_Ioo {x : WithLp 2 (ℝ × E)}
    (hx : x ∈ frontier {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b}) : x.fst = a ∨ x.fst = b := by
  have hclosed : IsClosed {x : WithLp 2 (ℝ × E) | x.fst ∈ Icc a b} :=
    isClosed_Icc.preimage (WithLp.continuous_fst ..)
  rw [isOpen_setOf_fst_mem_Ioo.frontier_eq] at hx
  have hsub : {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b} ⊆ {x | x.fst ∈ Icc a b} :=
    fun y hy => Ioo_subset_Icc_self hy
  have hIcc : x.fst ∈ Icc a b := closure_minimal hsub hclosed hx.1
  have hIoo : x.fst ∉ Ioo a b := hx.2
  simp only [mem_Icc, mem_Ioo, not_and_or, not_lt] at hIcc hIoo
  rcases hIoo with h | h
  · exact .inl (le_antisymm h hIcc.1)
  · exact .inr (le_antisymm hIcc.2 h)

/-- Over the zero space the slab `{x | a < x.fst < b}` is bounded: it is the interval `(a, b)`
inside `WithLp 2 (ℝ × E) ≃ ℝ`. -/
theorem isBounded_setOf_fst_mem_Ioo [Subsingleton E] :
    Bornology.IsBounded {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b} :=
  (WithLp.prod_antilipschitzWith_ofLp 2 ℝ E).isBounded_preimage
    ((isBounded_Ioo a b).prod (Bornology.IsBounded.all (univ : Set E))) |>.subset
      fun _ hx => ⟨hx, mem_univ _⟩

end TauCeti

namespace Set

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

/-- **The slab between two parallel hyperplanes is a Lipschitz domain**, with constant `0`. At
a point `x` of the lower face `{a} × E` the translation by `-x` is a chart, and at a point of the
upper face `{b} × E` the translation followed by the reflection of the normal coordinate is one;
both have the flat graph `0` and cylinders of half-height `b - a`. -/
theorem isLipschitzDomainWith_setOf_fst_mem_Ioo (hab : a < b) :
    {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b}.IsLipschitzDomainWith 0 := by
  refine (isLipschitzDomainWith_iff ..).2
    ⟨isOpen_setOf_fst_mem_Ioo, fun x hx => ?_⟩
  rcases fst_eq_or_fst_eq_of_mem_frontier_setOf_fst_mem_Ioo hx with hxa | hxb
  · -- On the lower face, `x + z` lies in the slab exactly when `0 < z.fst`.
    refine (isLipschitzDomainAtWith_iff ..).2 ⟨AffineIsometryEquiv.constVAdd ℝ _ (-x), 0, b - a,
      1, by simp,
      (isLipschitzChartWith_iff ..).2 ⟨sub_pos.2 hab, one_pos, rfl, LipschitzWith.const 0,
        fun z hz => ?_⟩⟩
    rw [mem_normalCylinder] at hz
    have hsymm : (AffineIsometryEquiv.constVAdd ℝ _ (-x)).symm z =
        WithLp.toLp 2 (a + z.fst, x.snd + z.snd) := by
      rw [AffineIsometryEquiv.symm_apply_eq]
      obtain ⟨⟨t, y⟩⟩ := z
      obtain ⟨⟨s, w⟩⟩ := x
      simp only [WithLp.toLp_fst] at hxa
      simp [hxa, ← WithLp.toLp_neg, ← WithLp.toLp_add]
    rw [hsymm, mem_ofPred_eq, WithLp.toLp_fst, mem_Ioo, Pi.zero_apply]
    constructor <;> intro h
    · linarith [h.1]
    · constructor <;> linarith
  · -- On the upper face, `x + (-z.fst, z.snd)` lies in the slab exactly when `0 < z.fst`.
    refine (isLipschitzDomainAtWith_iff ..).2 ⟨(AffineIsometryEquiv.constVAdd ℝ _ (-x)).trans
      (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (LinearIsometryEquiv.refl ℝ E)).toAffineIsometryEquiv, 0, b - a, 1, by simp,
      (isLipschitzChartWith_iff ..).2 ⟨sub_pos.2 hab, one_pos, rfl, LipschitzWith.const 0,
        fun z hz => ?_⟩⟩
    rw [mem_normalCylinder] at hz
    have hsymm : ((AffineIsometryEquiv.constVAdd ℝ _ (-x)).trans
        (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ (E := ℝ))
          (LinearIsometryEquiv.refl ℝ E)).toAffineIsometryEquiv).symm z =
        WithLp.toLp 2 (b - z.fst, x.snd + z.snd) := by
      rw [AffineIsometryEquiv.symm_apply_eq]
      obtain ⟨⟨t, y⟩⟩ := z
      obtain ⟨⟨s, w⟩⟩ := x
      simp only [WithLp.toLp_fst] at hxb
      simp [hxb]
    rw [hsymm, mem_ofPred_eq, WithLp.toLp_fst, mem_Ioo, Pi.zero_apply]
    constructor <;> intro h
    · linarith [h.2]
    · constructor <;> linarith

end Set
