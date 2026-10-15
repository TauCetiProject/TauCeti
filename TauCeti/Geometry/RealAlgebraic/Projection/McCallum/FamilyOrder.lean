/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Order
public import TauCeti.Geometry.RealAlgebraic.OrderInvariant
public import TauCeti.Topology.Algebra.MvPolynomial.OrderAt

/-!
# Ambient order in a McCallum family stack

Suppose an irreducible basis has a common delineation over a preconnected base. If the ambient
order of the product of the basis members is constant on every root section, then the ambient
order of each basis member is constant there as well. This is a topological consequence of
product order constancy: a factor's order can only jump upwards, and the sum of all factor
orders is fixed. The content and basis factorization then give constant ambient order for
every original input. On sectors the order is determined by content alone.

This transfers the conclusion of a single-polynomial discriminant theorem for the active
basis product to the whole family. The hypothesis concerns ambient Taylor order in all
variables. Fiber root multiplicity is not a substitute for it. Members of the basis must
have nonzero fibers over the base, as in well-oriented McCallum lifting; contents and
original inputs may vanish.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Sections 2–3.
-/

public section

open MvPolynomial Polynomial Set

namespace Finset.IsIrreducibleBasis

variable {n : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- If the active basis product has constant ambient order on each section of a common
delineation, then every original input has constant ambient order and sign on every stack
cell. Content order is required to be constant on the base, and basis fibers must be
nonzero. The product order need only be controlled on sections: on sectors, every basis
member has ambient order zero. -/
theorem orderAt_eq_of_prod_delineation (hB : F.IsIrreducibleBasis B)
    (hS : IsPreconnected S)
    (D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1))
    (hfiber : ∀ b ∈ B, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    (hcontent : ∀ f ∈ F, ∀ x ∈ S, ∀ y ∈ S,
      f.content.orderAt x = f.content.orderAt y)
    (hprod : ∀ i, ∀ a ∈ TauCeti.cylinder S '' TauCeti.sectionSet D.root i,
      ∀ a' ∈ TauCeti.cylinder S '' TauCeti.sectionSet D.root i,
        (∏ b ∈ B, ((finSuccEquiv ℝ n).symm b)).orderAt a =
          (∏ b ∈ B, ((finSuccEquiv ℝ n).symm b)).orderAt a') :
    ∀ E ∈ TauCeti.stackCells S D.root, ∀ f ∈ F,
      (∀ a ∈ E, ∀ a' ∈ E,
        ((finSuccEquiv ℝ n).symm f).orderAt a =
          ((finSuccEquiv ℝ n).symm f).orderAt a') ∧
      TauCeti.SignInvariant
        (fun a ↦ MvPolynomial.eval a ((finSuccEquiv ℝ n).symm f)) E := by
  classical
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hnonzero : (∏ b ∈ B, ((finSuccEquiv ℝ n).symm b)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb hz
    exact (hB.irreducible b hb).ne_zero
      ((finSuccEquiv ℝ n).symm.injective (by simpa only [map_zero] using hz))
  intro E hE f hf
  have horder : ∀ a ∈ E, ∀ a' ∈ E,
      ((finSuccEquiv ℝ n).symm f).orderAt a =
        ((finSuccEquiv ℝ n).symm f).orderAt a' := by
    rcases TauCeti.mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · intro a ha a' ha'
      apply hB.orderAt_eq hf (hcontent f hf _ (TauCeti.mem_image_cylinder.mp ha).1
        _ (TauCeti.mem_image_cylinder.mp ha').1)
      intro b hb
      exact ((TauCeti.isPreconnected_sectionSet (D.continuous_root i)).image _
        TauCeti.continuous_cylinder.continuousOn).orderAt_eq_of_prod
        (fun b ↦ ((finSuccEquiv ℝ n).symm b)) B hnonzero continuous_id.continuousOn
        (hprod i) hb ha ha'
    · intro a ha a' ha'
      exact hB.orderAt_eq_of_mem_sectorSet D hf (hcontent f hf) hfiber ha ha'
  refine ⟨horder, ?_⟩
  have hpreconn : IsPreconnected E := by
    rcases TauCeti.mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (TauCeti.isPreconnected_sectionSet (D.continuous_root i)).image _
        TauCeti.continuous_cylinder.continuousOn
    · exact (TauCeti.isPreconnected_sectorSet D.continuous_root D.strictMono_root j).image _
        TauCeti.continuous_cylinder.continuousOn
  exact hpreconn.signInvariant_eval_of_orderAt_eq horder

end Finset.IsIrreducibleBasis
