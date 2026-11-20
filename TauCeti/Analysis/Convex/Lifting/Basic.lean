/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import TauCeti.Order.CompositionLift

/-!
# Convexity and auxiliary bounds for exact composition lifts

This file complements `TauCeti.Order.CompositionLift` with convexity results and auxiliary domain
and objective-bound transfer lemmas for `TauCeti.CompositionLift.originalSet` and
`TauCeti.CompositionLift.liftedSet`.

When `g` is convex on `D` and `h` is quasiconvex on `E` (in particular, when `h` is convex on `E`),
the lifted set is convex with no `MapsTo g D E` or monotonicity requirement
(`TauCeti.CompositionLift.convex_liftedSet`). When additionally `h` is monotone on `E` and
`MapsTo g D E` holds, the original feasible set is also convex without requiring `g '' D` to be
convex (`TauCeti.CompositionLift.convex_originalSet`).

## Main statements

* `TauCeti.CompositionLift.liftedSet_subset_prod` — `liftedSet D E g h b ⊆ D ×ˢ E`.
* `TauCeti.CompositionLift.originalSet_empty`, `TauCeti.CompositionLift.liftedSet_empty_left`,
  `TauCeti.CompositionLift.liftedSet_empty_right` — emptiness `simp` lemmas.
* `TauCeti.CompositionLift.convex_liftedSet` — convexity of `liftedSet` assuming only
  `ConvexOn 𝕜 D g` and `QuasiconvexOn 𝕜 E h` (no `MapsTo` or monotonicity needed).
* `TauCeti.CompositionLift.convex_originalSet` — convexity of `originalSet` under `ConvexOn 𝕜 D g`,
  `QuasiconvexOn 𝕜 E h`, `MapsTo g D E`, and `MonotoneOn h E`.
* `TauCeti.CompositionLift.forall_mem_liftedSet_le_apply_iff` and
  `TauCeti.CompositionLift.exists_mem_liftedSet_apply_le_iff` — exact transfer of lower bounds and
  sublevel objective-value witnesses for any pullback objective `f ∘ Prod.fst`.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Mathematical Programming 103 (2005), 225–249, §2, Proposition 1, pp. 226–227.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Extended Formulations in Mixed-integer Convex
  Programming*, IPCO 2016, arXiv:1511.06710v3 §4, p. 9.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Polyhedral approximation in mixed-integer
  convex optimization*, Mathematical Programming 172 (2018), arXiv:1607.03566v2 §4, p. 12,
  Eqs. (8)–(10).
-/

public section

open Set

namespace TauCeti.CompositionLift

section DomainAndEmpty

variable {X Y β : Type*} [Preorder β]

/-- Every point of `liftedSet` lies in the product domain `D ×ˢ E`. -/
theorem liftedSet_subset_prod [Preorder Y] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β)
    (b : β) : liftedSet D E g h b ⊆ D ×ˢ E :=
  fun _ hp => ⟨(mem_liftedSet.1 hp).1, (mem_liftedSet.1 hp).2.1⟩

/-- The original set over an empty domain is empty. -/
@[simp]
theorem originalSet_empty (g : X → Y) (h : Y → β) (b : β) :
    originalSet (∅ : Set X) g h b = ∅ := by
  ext x
  simp

/-- The lifted set over an empty original domain is empty. -/
@[simp]
theorem liftedSet_empty_left [Preorder Y] (E : Set Y) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet (∅ : Set X) E g h b = ∅ := by
  ext p
  simp

/-- The lifted set over an empty height domain is empty. -/
@[simp]
theorem liftedSet_empty_right [Preorder Y] (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet D (∅ : Set Y) g h b = ∅ := by
  ext p
  simp

end DomainAndEmpty

section Convex

variable {𝕜 X Y β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid Y] [PartialOrder Y]

/-- When `g` is convex on `D` and `h` is quasiconvex on `E` (in particular, when `h` is convex on
`E`, via `ConvexOn.quasiconvexOn`), the lifted set `liftedSet D E g h b` is convex. Neither
`MapsTo g D E` nor monotonicity of `h` is required here. -/
theorem convex_liftedSet [Preorder β] [IsOrderedAddMonoid Y] [Module 𝕜 Y] [PosSMulMono 𝕜 Y]
    {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}
    (hg : ConvexOn 𝕜 D g) (hh : QuasiconvexOn 𝕜 E h) : Convex 𝕜 (liftedSet D E g h b) := by
  have hEq :
      liftedSet D E g h b =
        {p : X × Y | p.1 ∈ D ∧ g p.1 ≤ p.2} ∩ ((univ : Set X) ×ˢ {y ∈ E | h y ≤ b}) := by
    ext p
    simp only [mem_liftedSet, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ, true_and]
    tauto
  rw [hEq]
  exact hg.convex_epigraph.inter (convex_univ.prod (hh b))

/-- When `g` is convex on `D`, `h` is quasiconvex and monotone on `E` (in particular, when `h` is
convex and monotone on `E`, via `ConvexOn.quasiconvexOn`), and `g` maps `D` into `E`, the original
feasible set `originalSet D g h b` is convex (even when `g '' D` itself is not convex). -/
theorem convex_originalSet [SMul 𝕜 Y] [Preorder β] {D : Set X} {E : Set Y} {g : X → Y}
    {h : Y → β} {b : β} (hg : ConvexOn 𝕜 D g) (hh : QuasiconvexOn 𝕜 E h) (hDE : MapsTo g D E)
    (hm : MonotoneOn h E) : Convex 𝕜 (originalSet D g h b) := by
  intro x hx x' hx' a c ha hc hac
  rw [mem_originalSet] at hx hx' ⊢
  have hcomb := hh b ⟨hDE hx.1, hx.2⟩ ⟨hDE hx'.1, hx'.2⟩ ha hc hac
  exact ⟨hg.1 hx.1 hx'.1 ha hc hac,
    (hm (hDE (hg.1 hx.1 hx'.1 ha hc hac)) hcomb.1 (hg.2 hx.1 hx'.1 ha hc hac)).trans hcomb.2⟩

end Convex

section Bounds

variable {X Y β α : Type*} [Preorder Y] [Preorder β]
variable {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

/-- Lower bounds on `f` transfer identically between `liftedSet` and `originalSet`. -/
theorem forall_mem_liftedSet_le_apply_iff [LE α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (c : α) :
    (∀ p ∈ liftedSet D E g h b, c ≤ f p.1) ↔ ∀ x ∈ originalSet D g h b, c ≤ f x := by
  rw [← fst_image_liftedSet (b := b) hg hm, forall_mem_image]

/-- Existence of a feasible point with objective value at most `c` transfers identically between
`liftedSet` and `originalSet`. -/
theorem exists_mem_liftedSet_apply_le_iff [LE α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (c : α) :
    (∃ p ∈ liftedSet D E g h b, f p.1 ≤ c) ↔ ∃ x ∈ originalSet D g h b, f x ≤ c := by
  rw [← fst_image_liftedSet (b := b) hg hm, exists_mem_image]

end Bounds

end TauCeti.CompositionLift
