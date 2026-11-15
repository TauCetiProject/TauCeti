/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import Mathlib.Algebra.Group.Graph

/-!
# Graphs of opposite-form isometries

An isometry from a finite quadratic module `A` to the negative of `B` has a
quadratic-isotropic graph in `A ⊥ B`. When `A` is nondegenerate, this graph equals its
orthogonal complement and is therefore Lagrangian. These graphs are the glue subgroups
used to place two even lattices with opposite discriminant forms in a unimodular overlattice.

The subgroup is Mathlib's `AddMonoidHom.graph`; no separate graph carrier is introduced.
Quadratic isotropy is characterized for arbitrary additive homomorphisms, including
degenerate modules, before the nondegenerate Lagrangian theorem.

Conversely, a quadratic Lagrangian of `A ⊥ B` meeting both factors only in zero is such a graph:
both factors are then nondegenerate, its two coordinate projections are injective, the order of a
Lagrangian forces them to be bijective, and Mathlib's Goursat lemma
`AddSubgroup.exists_addEquiv_eq_graph` then produces the isometry. This identifies the glue
subgroup of an even unimodular overlattice in which both summands are primitive.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.6.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable (A B : FiniteQuadraticModule)

/-- A homomorphism's graph is quadratic-isotropic exactly when it reverses quadratic values. -/
@[simp]
theorem isIsotropic_graph_iff (f : A →+ B) :
    (A.prod B).IsIsotropic f.graph ↔ ∀ x, B.quadratic (f x) = -A.quadratic x := by
  rw [isIsotropic_def]
  constructor
  · intro h x
    have hx := h (x, f x) (AddMonoidHom.mem_graph.mpr rfl)
    rw [prod_quadratic] at hx
    exact eq_neg_of_add_eq_zero_right hx
  · intro h ⟨x, y⟩ hx
    simp only [AddMonoidHom.mem_graph] at hx
    rw [prod_quadratic, ← hx, h, add_neg_cancel]

/-- An opposite-form equivalence's graph equals its orthogonal complement when the source
is nondegenerate. -/
@[simp]
theorem orthogonalComplement_graph (e : A ≃+ B)
    (he : ∀ x, B.quadratic (e x) = -A.quadratic x) (hA : A.IsNondegenerate) :
    (A.toFiniteBilinearModule.prod B.toFiniteBilinearModule).orthogonalComplement
        (e : A →+ B).graph =
      (e : A →+ B).graph := by
  apply le_antisymm
  · intro x hx
    apply AddMonoidHom.mem_graph.mpr
    have heq : x.1 = e.symm x.2 := by
      apply hA.injective
      ext y
      have h : A.toFiniteBilinearModule.pairing x.1 y +
          B.toFiniteBilinearModule.pairing x.2 (e y) = 0 :=
        ((A.prod B).toFiniteBilinearModule.mem_orthogonalComplement_iff _ x).mp hx
          (y, e y) (AddMonoidHom.mem_graph.mpr rfl)
      have hi := ((A.prod B).toFiniteBilinearModule.isIsotropic_def).mp
        (((A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he).toFiniteBilinearModule)
      have hp : A.toFiniteBilinearModule.pairing (e.symm x.2) y +
          B.toFiniteBilinearModule.pairing x.2 (e y) = 0 :=
        hi (e.symm x.2, x.2) (AddMonoidHom.mem_graph.mpr (e.apply_symm_apply x.2))
          (y, e y) (AddMonoidHom.mem_graph.mpr rfl)
      exact add_right_cancel (h.trans hp.symm)
    rw [heq]
    exact e.apply_symm_apply _
  · exact ((A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he).le_orthogonalComplement

/-- An additive equivalence's graph is Lagrangian exactly when it reverses quadratic values.
Nondegeneracy is required only of the source. -/
@[simp]
theorem isLagrangian_graph_iff (e : A ≃+ B) (hA : A.IsNondegenerate) :
    (A.prod B).IsLagrangian (e : A →+ B).graph ↔
      ∀ x, B.quadratic (e x) = -A.quadratic x := by
  constructor
  · intro h
    exact (A.isIsotropic_graph_iff B e.toAddMonoidHom).mp h.isIsotropic
  · intro he
    apply ((A.prod B).isLagrangian_def _).mpr
    exact ⟨(A.isIsotropic_graph_iff B e.toAddMonoidHom).mpr he,
      ((A.prod B).toFiniteBilinearModule.isLagrangian_def _).mpr
        (A.orthogonalComplement_graph B e he hA).symm⟩

/-- **A Lagrangian meeting both factors trivially is a graph.** If a quadratic Lagrangian `H` of
`A ⊥ B` meets `A ⊥ 0` and `0 ⊥ B` only in zero, then `H` is the graph of an isometry from `A` to
the negative of `B`. Both factors are then nondegenerate, since `H` is its own orthogonal
complement. This is the converse of `TauCeti.FiniteQuadraticModule.isLagrangian_graph_iff`. -/
theorem exists_isometry_neg_mem_iff_of_isLagrangian {H : AddSubgroup (A × B)}
    (hH : (A.prod B).IsLagrangian H)
    (hleft : ∀ x : A, (x, 0) ∈ H → x = 0) (hright : ∀ y : B, (0, y) ∈ H → y = 0) :
    ∃ e : Isometry A B.neg, ∀ x y, (x, y) ∈ H ↔ e x = y := by
  -- A radical vector of either factor is orthogonal to `H`, hence lies in `H`, hence vanishes.
  have hHo := ((A.prod B).toFiniteBilinearModule.isLagrangian_def H).mp hH.toFiniteBilinearModule
  have hA : A.IsNondegenerate := A.toFiniteBilinearModule.isNondegenerate_of_radical_eq_bot <|
    (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx ↦ hleft x <| hHo ▸
      ((A.prod B).toFiniteBilinearModule.mem_orthogonalComplement_iff H _).mpr fun z _ ↦ by
        rw [prod_pairing, (A.toFiniteBilinearModule.mem_radical_iff x).mp hx,
          FiniteBilinearModule.pairing_zero_left, add_zero]
  have hB : B.IsNondegenerate := B.toFiniteBilinearModule.isNondegenerate_of_radical_eq_bot <|
    (AddSubgroup.eq_bot_iff_forall _).mpr fun y hy ↦ hright y <| hHo ▸
      ((A.prod B).toFiniteBilinearModule.mem_orthogonalComplement_iff H _).mpr fun z _ ↦ by
        rw [prod_pairing, (B.toFiniteBilinearModule.mem_radical_iff y).mp hy,
          FiniteBilinearModule.pairing_zero_left, zero_add]
  let π₁ : H →+ A := (AddMonoidHom.fst A B).comp H.subtype
  let π₂ : H →+ B := (AddMonoidHom.snd A B).comp H.subtype
  -- Each projection is injective on `H`, because `H` meets the other factor trivially.
  have h₁ : Function.Injective π₁ := by
    refine (injective_iff_map_eq_zero π₁).mpr fun ⟨⟨x, y⟩, hxy⟩ hx ↦ ?_
    obtain rfl : x = 0 := hx
    obtain rfl := hright y hxy
    rfl
  have h₂ : Function.Injective π₂ := by
    refine (injective_iff_map_eq_zero π₂).mpr fun ⟨⟨x, y⟩, hxy⟩ hy ↦ ?_
    obtain rfl : y = 0 := hy
    obtain rfl := hleft x hxy
    rfl
  -- A Lagrangian has `#H² = #A·#B`, so both injective projections are bijective.
  have hsq : Nat.card H * Nat.card H = Nat.card A * Nat.card B := by
    rw [← pow_two, FiniteBilinearModule.IsLagrangian.card_sq _ hH.toFiniteBilinearModule
      ((A.isNondegenerate_prod B).mpr ⟨hA, hB⟩)]
    exact Nat.card_prod A B
  have hHA := Nat.card_le_card_of_injective π₁ h₁
  have hHB := Nat.card_le_card_of_injective π₂ h₂
  have hpos : 0 < Nat.card H := Nat.card_pos
  obtain ⟨e, hHe⟩ := AddSubgroup.exists_addEquiv_eq_graph
    ((Nat.bijective_iff_injective_and_card π₁).mpr ⟨h₁, by nlinarith⟩)
    ((Nat.bijective_iff_injective_and_card π₂).mpr ⟨h₂, by nlinarith⟩)
  rw [hHe] at hH
  refine ⟨{ toLinearEquiv := e.toIntLinearEquiv, map_app' := fun x ↦ ?_ }, fun x y ↦ ?_⟩
  · exact (B.neg_quadratic _).trans
      (neg_eq_iff_eq_neg.mpr ((A.isLagrangian_graph_iff B e hA).mp hH x))
  · rw [hHe]
    exact AddMonoidHom.mem_graph

end TauCeti.FiniteQuadraticModule
