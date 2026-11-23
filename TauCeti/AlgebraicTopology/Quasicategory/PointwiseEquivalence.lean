/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Parametrized
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Equivalences in functor quasicategories are detected pointwise

Let `C` be a quasicategory and `K` a simplicial set. An edge `α : F ⟶ G` of the functor
quasicategory `Fun(K, C) = (ihom K).obj C` is a natural transformation between two maps `K ⟶ C`,
and its component at a vertex `x` of `K` is its image under evaluation at `x`
(`SSet.evalAt x C`). The main result of this file is that `α` is an equivalence of `Fun(K, C)`
exactly when all of its components are equivalences of `C`. This is the input for treating
natural transformations with invertible components as equivalences of functors, as needed for
mapping spaces of functor quasicategories and for the comparison of categorical equivalences with
fully faithful and essentially surjective maps.

The proof uses Joyal's characterization of equivalences by special outer horns
(`SSet.Edge.isEquivalence_iff_hornFilling_zero`): a horn `Λ[m + 2, 0] ⟶ Fun(K, C)` with initial
edge `α` is a family of horns of `C` parametrized by `K`, and the initial edge of the horn at `x`
is the component of `α` at `x`. Such families can be filled when every member has an invertible
initial edge, by the parametrized form of Joyal's theorem
(`SSet.Quasicategory.exists_lift_pre_horn_zero`).

## Main results

* `SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt`: an edge of `Fun(K, C)` is an
  equivalence exactly when its components at all vertices of `K` are.

## References

* J. Lurie, *Kerodon*, Theorem 4.4.4.4.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Simplicial

namespace SSet

variable {C : SSet.{u}}

namespace Edge

/-- **Equivalences of functors are detected pointwise** (Kerodon Theorem 4.4.4.4). Let `C` be a
quasicategory and `K` a simplicial set. An edge `α` of the functor quasicategory `Fun(K, C)`, that
is a natural transformation between maps `K ⟶ C`, is an equivalence exactly when its component
at every vertex `x` of `K`, its image under evaluation at `x`, is an equivalence of `C`. -/
theorem isEquivalence_iff_forall_isEquivalence_map_evalAt [Quasicategory C] {K : SSet.{u}}
    {F G : ((ihom K).obj C) _⦋0⦌} (α : Edge F G) :
    α.IsEquivalence ↔ ∀ x : K _⦋0⦌, (α.map (evalAt x C)).IsEquivalence := by
  refine ⟨fun h x ↦ h.map _, fun h ↦ (isEquivalence_iff_hornFilling_zero α).2 fun m σ₀ hσ₀ ↦ ?_⟩
  -- The horn `σ₀` of `Fun(K, C)` is a family of horns of `C` parametrized by `K`; the horn at a
  -- vertex `x` is `σ₀` followed by evaluation at `x`, whose initial edge is `α` at `x`.
  let φ : K ⟶ (ihom (Λ[m + 2, 0] : SSet.{u})).obj C := curry ((β_ _ _).hom ≫ uncurry σ₀)
  have hφ (x : K _⦋0⦌) : ihomObj₀Equiv _ C (φ.app _ x) = σ₀ ≫ evalAt x C := by
    rw [ihomObj₀Equiv_app, uncurry_curry, CartesianMonoidalCategory.lift_braiding_hom_assoc,
      ← curry_evalAt, curry_uncurry]
  obtain ⟨l, -, hl⟩ := Quasicategory.exists_lift_pre_horn_zero (initial.to K) (initial.to _) φ
    (initial.hom_ext _ _) fun x ↦ (isEquivalence_iff_of_edge_eq (e := Edge.mk' _)
      (e' := α.map (evalAt x C)) (by rw [hφ]; exact congrArg ((evalAt x C).app _) hσ₀)).2 (h x)
  refine ⟨curry ((β_ _ _).hom ≫ uncurry l), ?_⟩
  rw [← curry_natural_left, BraidedCategory.braiding_naturality_right_assoc, ← uncurry_pre_app,
    hl, uncurry_curry, SymmetricCategory.symmetry_assoc, curry_uncurry]

end Edge

end SSet
