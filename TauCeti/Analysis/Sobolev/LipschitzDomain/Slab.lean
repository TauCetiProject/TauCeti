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
with constant `0` for every `E` (`TauCeti.isLipschitzDomainWith_setOf_fst_mem_Ioo`): at a point of
the lower face a translation is a chart with the flat graph `0`, and at a point of the upper face
a translation followed by the reflection `(t, y) ↦ (-t, y)` of the normal coordinate is one.

When `E` is the zero space the slab is the interval `(a, b)` itself, embedded in
`WithLp 2 (ℝ × E) ≃ ℝ`: its preimage under `t ↦ (t, 0)` is `(a, b)`
(`TauCeti.withLpProdUnique_symm_preimage_setOf_fst_mem_Ioo`), and it is bounded
(`TauCeti.isBounded_setOf_fst_mem_Ioo`). This is how the trace theory of bounded Lipschitz
domains of `ℝ × E` covers intervals, in dimension `dim E = 0`.
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
  have h := (WithLp.continuous_fst ..).frontier_preimage_subset (Ioo a b) hx
  rw [mem_preimage, isOpen_Ioo.frontier_eq] at h
  have hIcc : x.fst ∈ Icc a b := closure_minimal Ioo_subset_Icc_self isClosed_Icc h.1
  rcases not_and_or.1 h.2 with h | h
  · exact .inl (le_antisymm (not_lt.1 h) hIcc.1)
  · exact .inr (le_antisymm hIcc.2 (not_lt.1 h))

/-- Over the zero space the slab `{x | a < x.fst < b}` is bounded: it is the interval `(a, b)`
inside `WithLp 2 (ℝ × E) ≃ ℝ`. -/
theorem isBounded_setOf_fst_mem_Ioo [Subsingleton E] :
    Bornology.IsBounded {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b} :=
  (WithLp.prod_antilipschitzWith_ofLp 2 ℝ E).isBounded_preimage
    ((isBounded_Ioo a b).prod (Bornology.IsBounded.all (univ : Set E))) |>.subset
      fun _ hx => ⟨hx, mem_univ _⟩

section LipschitzDomain

variable [NormedSpace ℝ E]

/-- An isometry `e` with `e x = 0` is a chart of the slab at `x` with the flat graph `0` if a
point `y` with `|(e y).fst| < b - a` lies in the slab exactly when `0 < (e y).fst`. Both faces of
the slab use it. -/
private theorem isLipschitzDomainAtWith_setOf_fst_mem_Ioo_of_chart (hab : a < b)
    {x : WithLp 2 (ℝ × E)} (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hex : e x = 0)
    (hmem : ∀ y : WithLp 2 (ℝ × E), -(b - a) < (e y).fst → (e y).fst < b - a →
      (y.fst ∈ Ioo a b ↔ 0 < (e y).fst)) :
    {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b}.IsLipschitzDomainAtWith (E := E) 0 x :=
  (isLipschitzDomainAtWith_iff ..).2 ⟨e, 0, b - a, 1, hex,
    (isLipschitzChartWith_iff ..).2 ⟨sub_pos.2 hab, one_pos, rfl, LipschitzWith.const 0,
      fun z hz => by
        rw [mem_normalCylinder] at hz
        have h := hmem (e.symm z)
        rw [e.apply_symm_apply] at h
        exact h hz.1 hz.2.1⟩⟩

/-- **The slab between two parallel hyperplanes is a Lipschitz domain**, with constant `0`. At
a point `x` of the lower face `{a} × E` the translation by `-x` is a chart, and at a point of the
upper face `{b} × E` the translation followed by the reflection of the normal coordinate is one;
both have the flat graph `0` and cylinders of half-height `b - a`. -/
theorem isLipschitzDomainWith_setOf_fst_mem_Ioo (hab : a < b) :
    {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b}.IsLipschitzDomainWith 0 := by
  refine (isLipschitzDomainWith_iff ..).2
    ⟨isOpen_setOf_fst_mem_Ioo, fun x hx => ?_⟩
  rcases fst_eq_or_fst_eq_of_mem_frontier_setOf_fst_mem_Ioo hx with hxa | hxb
  · -- On the lower face, `y` lies in the slab exactly when `0 < y.fst - a`.
    refine isLipschitzDomainAtWith_setOf_fst_mem_Ioo_of_chart hab
      (AffineIsometryEquiv.constVAdd ℝ _ (-x)) (by simp) fun y h₁ h₂ => ?_
    simp [hxa] at h₁ h₂ ⊢
    grind
  · -- On the upper face, `y` lies in the slab exactly when `0 < b - y.fst`.
    refine isLipschitzDomainAtWith_setOf_fst_mem_Ioo_of_chart hab
      ((AffineIsometryEquiv.constVAdd ℝ _ (-x)).trans
        (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ (E := ℝ))
          (LinearIsometryEquiv.refl ℝ E)).toAffineIsometryEquiv) (by simp) fun y h₁ h₂ => ?_
    simp [hxb] at h₁ h₂ ⊢
    grind

/-- Over the zero space the slab `{x | a < x.fst < b}` is the interval `(a, b)`: its preimage
under the isometry `t ↦ (t, 0)` of the line onto `WithLp 2 (ℝ × E)`. -/
theorem withLpProdUnique_symm_preimage_setOf_fst_mem_Ioo [Unique E] :
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ ℝ E).symm ⁻¹'
      {x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b} = Ioo a b := by
  ext t
  simp

end LipschitzDomain

end TauCeti
