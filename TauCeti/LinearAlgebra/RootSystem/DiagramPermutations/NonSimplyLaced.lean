/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Basic
import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.Classical

/-!
# Rigidity of nonsimply-laced numbered diagrams

The oriented Cartan matrices of `Bₙ`, `Cₙ`, `F₄`, and `G₂` have no nontrivial node
symmetries. The classical cases come from chain rigidity; the exceptional cases are
finite calculations. These results concern Cartan-preserving permutations, not the
length exchanges that transpose the matrices.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, plates II–III, VIII–IX.
-/

public section

namespace TauCeti.DynkinType

/-- The identity is the only permutation of the two `G₂` nodes preserving its Cartan matrix, the
`G₂` matrix being asymmetric. -/
theorem eq_one_of_cartanMatrix_G2 {ρ : Equiv.Perm (Fin 2)}
    (h : ∀ i j : Fin 2, G2.cartanMatrix (ρ i) (ρ j) = G2.cartanMatrix i j) : ρ = 1 := by
  have key : ∀ f : Fin 2 → Fin 2,
      (∀ p : Fin 2 × Fin 2, CartanMatrix.G₂.transpose (f p.1) (f p.2) =
        CartanMatrix.G₂.transpose p.1 p.2) →
      ∀ i, f i = i := by decide
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  exact key ρ (fun p => by simpa using h p.1 p.2) i

/-- The identity is the only permutation of the four `F₄` nodes preserving its Cartan matrix.

The entry `-2` occurs once, at the double bond `(1, 2)`, so a Cartan-preserving permutation fixes
both of those nodes; the two end nodes are then pinned by the entries `-1` beside them. -/
theorem eq_one_of_cartanMatrix_F4 {ρ : Equiv.Perm (Fin 4)}
    (h : ∀ i j : Fin 4, F4.cartanMatrix (ρ i) (ρ j) = F4.cartanMatrix i j) : ρ = 1 := by
  have h' : ∀ i j : Fin 4, CartanMatrix.F₄ (ρ i) (ρ j) = CartanMatrix.F₄ i j := by
    intro i j; simpa using h i j
  have hneg : ∀ p : Fin 4 × Fin 4, CartanMatrix.F₄ p.1 p.2 = -2 → p.1 = 1 ∧ p.2 = 2 := by decide
  have hneg' : ∀ x y : Fin 4, CartanMatrix.F₄ x y = -2 → x = 1 ∧ y = 2 := fun x y => hneg (x, y)
  obtain ⟨hρ₁, hρ₂⟩ := hneg' (ρ 1) (ρ 2) (by rw [h' 1 2]; decide)
  have hcol : ∀ x : Fin 4, CartanMatrix.F₄ x 1 = -1 → x = 0 ∨ x = 2 := by decide
  have hrow : ∀ y : Fin 4, CartanMatrix.F₄ 2 y = -1 → y = 1 ∨ y = 3 := by decide
  have hρ₀ : ρ 0 = 0 := by
    have h01 := h' 0 1
    rw [hρ₁] at h01
    rcases hcol (ρ 0) (by rw [h01]; decide) with h0 | h0
    · exact h0
    · exact absurd (ρ.injective (h0.trans hρ₂.symm)) (by decide)
  have hρ₃ : ρ 3 = 3 := by
    have h23 := h' 2 3
    rw [hρ₂] at h23
    rcases hrow (ρ 3) (by rw [h23]; decide) with h3 | h3
    · exact absurd (ρ.injective (h3.trans hρ₁.symm)) (by decide)
    · exact h3
  refine Equiv.ext fun i => ?_
  simp only [Equiv.Perm.one_apply]
  fin_cases i
  exacts [hρ₀, hρ₁, hρ₂, hρ₃]

/-- A nonsimply-laced numbered Dynkin diagram has no nonidentity permutation
preserving its oriented Cartan matrix. -/
theorem eq_one_of_cartanMatrix_of_not_isSimplyLaced {t : DynkinType}
    (hsl : ¬ t.IsSimplyLaced) {ρ : Equiv.Perm (Fin t.rank)}
    (h : ∀ i j, t.cartanMatrix (ρ i) (ρ j) = t.cartanMatrix i j) : ρ = 1 := by
  cases t with
  | A n => exact (hsl (isSimplyLaced_A n)).elim
  | B n => exact eq_one_of_cartanMatrix_B h
  | C n => exact eq_one_of_cartanMatrix_C h
  | D n => exact (hsl (isSimplyLaced_D n)).elim
  | E6 => exact (hsl isSimplyLaced_E6).elim
  | E7 => exact (hsl isSimplyLaced_E7).elim
  | E8 => exact (hsl isSimplyLaced_E8).elim
  | F4 => exact eq_one_of_cartanMatrix_F4 h
  | G2 => exact eq_one_of_cartanMatrix_G2 h

/-- Every nonsimply-laced numbered Dynkin diagram has trivial symmetry group. -/
theorem diagramSymmetry_eq_bot_of_not_isSimplyLaced {t : DynkinType}
    (hsl : ¬ t.IsSimplyLaced) : t.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ h ↦
    eq_one_of_cartanMatrix_of_not_isSimplyLaced hsl (mem_diagramSymmetry_iff.mp h)

/-- The numbered type-F₄ diagram has trivial symmetry group. -/
@[simp] theorem diagramSymmetry_F4_eq_bot : F4.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ h ↦
    eq_one_of_cartanMatrix_F4 (mem_diagramSymmetry_iff.mp h)

/-- The numbered type-G₂ diagram has trivial symmetry group. -/
@[simp] theorem diagramSymmetry_G2_eq_bot : G2.diagramSymmetry = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ h ↦
    eq_one_of_cartanMatrix_G2 (mem_diagramSymmetry_iff.mp h)

end TauCeti.DynkinType
