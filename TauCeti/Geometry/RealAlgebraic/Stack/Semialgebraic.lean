/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Geometry.RealAlgebraic.Stack.RootCount
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.SharedRoots
import TauCeti.FieldTheory.IsRealClosed.Real

/-!
# Semialgebraicity of polynomial delineations

Every delineation of a finite polynomial family over a semialgebraic base is a semialgebraic
stack. No closure under differentiation is needed. The sections and sectors are described by
membership in the shared distinct root set and the number of shared roots strictly below the
height, using the uniform formulas of
`Finset.isSemialgebraic_setOf_mem_biUnion_roots_card_lt` and
`Finset.isSemialgebraic_setOf_notMem_biUnion_roots_card_lt`.

Coefficients may come from any commutative ring equipped with a homomorphism to `ℝ`.
Nullified fibers contribute no roots to the finite shared root set; they do not contribute
their entire zero set. Repeated roots and roots shared by several members are counted once.
The empty family and a stack with no sections are included.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapters 10 and 11 (uniform shared-root descriptions and semialgebraic stacks).
-/

public section

open Set MvPolynomial
open scoped Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {C : Set (Fin n → ℝ)}

/-- A delineation of a finite polynomial family over a semialgebraic base is a semialgebraic
stack. The family need not be closed under differentiation. Nullified members are allowed. -/
theorem Delineation.isSemialgebraicStack (hC : IsSemialgebraic C)
    (D : Delineation fun (p : F) (x : C) ↦ p.1.map (eval₂Hom φ x.1)) :
    IsSemialgebraicStack C D.root := by
  classical
  -- Pass the coefficients to ℝ; the homomorphism may identify different family members.
  let G := F.image fun p ↦ p.map (MvPolynomial.map φ)
  have hmap (p : (MvPolynomial (Fin n) A)[X]) (x : Fin n → ℝ) :
      (p.map (MvPolynomial.map φ)).map (MvPolynomial.eval x) = p.map (eval₂Hom φ x) := by
    ext j
    simp [Polynomial.coeff_map, MvPolynomial.eval_map]
  have hroots (x : C) :
      G.biUnion (fun p ↦ (p.map (MvPolynomial.eval x.1)).roots.toFinset) =
        Finset.univ.image (fun i ↦ D.root i x) := by
    ext t
    simp only [G, Finset.image_biUnion, hmap, Finset.mem_biUnion,
      Multiset.mem_toFinset, Polynomial.mem_roots', Finset.mem_image, Finset.mem_univ,
      true_and]
    simpa only [mem_range, mem_ofPred_eq, Subtype.exists, exists_prop] using
      (Set.ext_iff.1 (D.range_root x) t).symm
  -- Identify the ambient cells with the shared-root rank formulas on the base.
  have hsection (i : Fin D.count) : cylinder C '' sectionSet D.root i =
      {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C} ∩ {y : Fin (n + 1) → ℝ |
        y 0 ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
        {r ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
          r < y 0}.card = i.val} := by
    ext y
    simp only [mem_image_cylinder, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hi⟩
      refine ⟨hy, ?_⟩
      rw [hroots ⟨Fin.tail y, hy⟩]
      exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).1 hi
    · rintro ⟨hy, hi⟩
      refine ⟨hy, ?_⟩
      rw [hroots ⟨Fin.tail y, hy⟩] at hi
      exact (mem_sectionSet_iff_mem_image_card_lt i _ (D.strictMono_root _)).2 hi
  have hsector (j : Fin (D.count + 1)) : cylinder C '' sectorSet D.root j =
      {y : Fin (n + 1) → ℝ | Fin.tail y ∈ C} ∩ {y : Fin (n + 1) → ℝ |
        y 0 ∉ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
        {r ∈ G.biUnion (fun p ↦ (p.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
          r < y 0}.card = j.val} := by
    ext y
    simp only [mem_image_cylinder, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hj⟩
      refine ⟨hy, ?_⟩
      rw [hroots ⟨Fin.tail y, hy⟩]
      exact (mem_sectorSet_iff_notMem_image_card_lt j _ (D.strictMono_root _)).1 hj
    · rintro ⟨hy, hj⟩
      refine ⟨hy, ?_⟩
      rw [hroots ⟨Fin.tail y, hy⟩] at hj
      exact (mem_sectorSet_iff_notMem_image_card_lt j _ (D.strictMono_root _)).2 hj
  refine ⟨D.continuous_root, D.strictMono_root, fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [hsection]
    exact hC.preimage_tail.inter (G.isSemialgebraic_setOf_mem_biUnion_roots_card_lt i.val)
  · rw [hsector]
    exact hC.preimage_tail.inter (G.isSemialgebraic_setOf_notMem_biUnion_roots_card_lt j.val)

end TauCeti
