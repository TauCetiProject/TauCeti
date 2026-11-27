/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Evenly covered points from continuous labellings of the fibres

Let `P : B → X → Prop` be a relation and consider the projection `(b, x) ↦ b` from the subtype
`{q : B × X // P q.1 q.2}` to `B`. Suppose that over an open set `U` of `B` its fibres are labelled
continuously: there are maps `σ i : B → X`, indexed by a finite discrete type `ι` and continuous on
`U`, which are pairwise distinct at every `b ∈ U` and whose values at `b` are exactly the `x` with
`P b x`. Then over `U` the subtype is the disjoint union of the graphs of the `σ i`, and the
projection is evenly covered, with fibre `ι`, at every point of `U`
(`IsEvenlyCovered.subtype_fst_of_continuousOn`).

The label of a point `(b, x)` over `U` is the unique `i` with `σ i b = x`. It is locally constant,
because the `σ i` are continuous and pairwise distinct and `X` is Hausdorff, so the projection
together with the label is a homeomorphism from the part of the subtype over `U` onto `U × ι`.

This is how the roots of a family of separable polynomials
(`TauCeti.Polynomial.isEvenlyCovered_fst_isRoot`) and the points of a family of unordered tuples
without repeated points (`Sym.isEvenlyCovered_fst_mem`) form covering spaces.
-/

public section

open Set

variable {B X ι : Type*} [TopologicalSpace B] [TopologicalSpace X] [T2Space X]
  [TopologicalSpace ι] [DiscreteTopology ι] [Finite ι]

/-- **Continuous labellings of the fibres give an evenly covered point.** If, over an open set `U`
containing `b₀`, the `x` with `P b x` are exactly the values `σ i b` of maps `σ i` continuous on `U`
and pairwise distinct at every `b ∈ U`, then the projection `(b, x) ↦ b` from the pairs with
`P b x` is evenly covered at `b₀`, with fibre the finite discrete index type `ι`. -/
theorem IsEvenlyCovered.subtype_fst_of_continuousOn {P : B → X → Prop} {U : Set B}
    (hU : IsOpen U) {b₀ : B} (hb₀ : b₀ ∈ U) {σ : ι → B → X} (hσc : ∀ i, ContinuousOn (σ i) U)
    (hσ : ∀ b ∈ U, Function.Injective (fun i => σ i b) ∧ ∀ x, P b x ↔ ∃ i, σ i b = x) :
    IsEvenlyCovered (fun q : {q : B × X // P q.1 q.2} => q.val.1) b₀ ι := by
  set f := fun q : {q : B × X // P q.1 q.2} => q.val.1
  -- the label of a point over `U`: the graph it lies on
  choose idx hidx using fun q : f ⁻¹' U => ((hσ _ q.property).2 q.val.val.2).1 q.val.property
  have hidx_iff (q : f ⁻¹' U) (i : ι) : idx q = i ↔ σ i q.val.val.1 = q.val.val.2 :=
    ⟨fun h => h ▸ hidx q, fun h => (hσ _ q.property).1 ((hidx q).trans h.symm)⟩
  have hσq (i : ι) : Continuous fun q : f ⁻¹' U => σ i q.val.val.1 :=
    (hσc i).comp_continuous (by fun_prop) fun q => q.property
  -- the label is locally constant, since the graphs are pairwise disjoint and continuous
  have hidx_cont : Continuous idx := by
    refine continuous_discrete_rng.2 fun i => ?_
    have h : idx ⁻¹' {i} = ⋂ j, {q | j ≠ i → σ j q.val.val.1 ≠ q.val.val.2} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro rfl j hj h
        exact hj ((hidx_iff q j).2 h).symm
      · intro h
        by_contra hne
        exact h _ hne (hidx q)
    rw [h]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j = i
    · simp [hj]
    · simpa [hj] using isOpen_ne_fun (hσq j) (by fun_prop)
  refine ⟨inferInstance, U, hb₀, hU, hU.preimage (by fun_prop),
    { toFun q := (⟨q.val.val.1, q.property⟩, idx q)
      invFun p := ⟨⟨(p.1.val, σ p.2 p.1.val), ((hσ _ p.1.property).2 _).2 ⟨p.2, rfl⟩⟩,
        p.1.property⟩
      left_inv q := Subtype.ext (Subtype.ext (Prod.ext rfl (hidx q)))
      right_inv p := Prod.ext rfl ((hidx_iff _ _).2 rfl)
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        refine (continuous_subtypeVal.comp continuous_fst).prodMk ?_
        exact continuous_prod_of_discrete_right.2 fun i =>
          (hσc i).comp_continuous continuous_subtypeVal fun x => x.property }, fun _ => rfl⟩
