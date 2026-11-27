/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Closed lifts through coverings with ordered fibers

A lift of a loop is closed if the initial fiber is finite and a continuous height in a
linearly ordered space with closed order separates points in each fiber along the loop.
Distinct lifts never meet, so their heights keep their order. A strictly monotone self-map of a
finite linear order fixes each point.

Adapted from Giada Franz's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/b30e86b2c963e206ab7ee1435ab5665fe7db0cce/ForTauCeti/Topology/Covering/ClosedLift.lean).

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed genus
  in a 3-manifold II; Multi-valued graphs in disks*, Ann. of Math. 160 (2004), 69–92,
  proof of Lemma 1.10. The real-valued height is the coordinate normal to the projection plane.
-/

public section

open Set unitInterval

namespace IsCoveringMap

/-- A lift of a loop is closed when its initial fiber is finite and a continuous height in a
linearly ordered space with closed order separates points in each fiber along the loop. -/
theorem apply_one_eq_apply_zero_of_injOn_fiber {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p) {Γ : C(I, E)}
    (hΓ : p (Γ 1) = p (Γ 0)) (hfin : (p ⁻¹' {p (Γ 0)}).Finite)
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {h : E → α} (hh : Continuous h) (hsep : ∀ t, InjOn h (p ⁻¹' {p (Γ t)})) :
    Γ 1 = Γ 0 := by
  let S := p ⁻¹' {p (Γ 0)}
  let γ : C(I, B) := ⟨p ∘ Γ, hp.continuous.comp Γ.continuous⟩
  let L (y : S) := hp.liftPath γ y (mem_singleton_iff.mp y.property).symm
  have hLp (y : S) : p ∘ L y = γ := hp.liftPath_lifts ..
  have hL0 (y : S) : L y 0 = y := hp.liftPath_zero ..
  have hpL (y : S) (t : I) : p (L y t) = p (Γ t) := congrFun (hLp y) t
  let τ (y : S) : S := ⟨L y 1, (hpL y 1).trans hΓ⟩
  let : Finite S := hfin.to_subtype
  let : LinearOrder S := LinearOrder.lift' (fun y : S ↦ h y) (hsep 0).injective
  have hmono : StrictMono τ := by
    intro x y hxy
    -- The order on S is pulled back along h by LinearOrder.lift', so its comparisons unfold.
    change h x < h y at hxy
    -- Unfold the same pulled-back order and τ, whose underlying endpoint is L · 1.
    change h (L x 1) < h (L y 1)
    by_contra! hle
    obtain ⟨t, ht⟩ := intermediate_value_univ₂ (a := 0) (b := 1)
      (hh.comp (L x).continuous) (hh.comp (L y).continuous)
      (by simpa only [Function.comp_apply, hL0] using hxy.le) hle
    have heq := hsep t (hpL x t) (hpL y t) ht
    have hl := hp.eq_of_comp_eq (L x).continuous (L y).continuous
      ((hLp x).trans (hLp y).symm) t heq
    exact hxy.ne (by rw [← hL0 x, ← hL0 y, hl])
  let y₀ : S := ⟨Γ 0, rfl⟩
  have hΓL : Γ = L y₀ := (hp.eq_liftPath_iff' _).mpr ⟨rfl, rfl⟩
  exact (congrArg (fun f : C(I, E) ↦ f 1) hΓL).trans
    (congrArg Subtype.val (hmono.apply_eq (x := y₀)))

end IsCoveringMap
