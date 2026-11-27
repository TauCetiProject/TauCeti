/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.HomotopySequence
import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.Basic

/-!
# Homotopy groups of fibres of Kan fibrations

For a Kan fibration over a Kan complex, injectivity on homotopy groups in degree `n` and
surjectivity in degree `n + 1` force the fibre's degree-`n` homotopy set to be a singleton.
This includes pointed degree zero. Consequently, injectivity on connected components and
surjectivity on fundamental groups make every nonempty fibre connected. Surjectivity on
connected components ensures that the fibres are nonempty, by lifting an edge in the base.

In particular, a Kan fibration inducing bijections on components and all positive homotopy
groups has nonempty connected fibres with trivial positive homotopy groups. These are the
fibrewise inputs to the homotopy-group criterion for trivial fibrations.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I, §7,
  the long exact sequence of a Kan fibration.
-/

public section

universe u

open CategoryTheory Simplicial HomotopicalAlgebra

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}}

/-- A right fibration over a Kan complex which is surjective on connected components has a
nonempty fibre over every vertex. -/
lemma nonempty_fiber_of_surjective_mapπ₀ (p : X ⟶ Y) [RightFibration p] [KanComplex Y]
    (hp : Function.Surjective (mapπ₀ p)) (y : Y _⦋0⦌) : (fiber p y : SSet).Nonempty := by
  obtain ⟨c, hc⟩ := hp (π₀.mk y)
  obtain ⟨x, rfl⟩ := π₀.mk_surjective c
  obtain ⟨e⟩ := (π₀.mk_eq_mk_iff_nonempty_edge y (p.app _ x)).1 hc.symm
  have := (rightFibration_iff_hasLiftingProperty p).1 inferInstance (1 : Fin 2) (by decide)
  obtain ⟨g, -, hgp⟩ := Edge.exists_edge_of_hasLiftingProperty_horn₁₁ p x e.edge e.tgt_eq
  exact ⟨fiber.basePoint p (x := X.δ 1 g)
    (by rw [δ_naturality_apply p 1 g, hgp, e.src_eq])⟩

namespace KanComplex.HomotopySequence

variable {p : X ⟶ Y} [Fibration p] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (hx : p.app _ x = y)

/-- If a Kan fibration is injective on the degree-`n` homotopy set and surjective in degree
`n + 1` at a chosen vertex, its fibre's degree-`n` homotopy set is a singleton. The statement
includes degree zero, where exactness is exactness of pointed sets. -/
lemma subsingleton_π_fiber {n : ℕ}
    (hi : Function.Injective (π.map (n := n) p hx))
    (hs : Function.Surjective (π.map (n := n + 1) p hx)) :
    Subsingleton (π n (fiber p y : SSet) (fiber.basePoint p hx)) := by
  have h (a : π n (fiber p y : SSet) (fiber.basePoint p hx)) : a = 1 := by
    have ha : π.map (fiber p y).ι (fiber.ι_app_basePoint p hx) a = 1 :=
      hi (by simp)
    obtain ⟨b, rfl⟩ := (map_fiber_ι_eq_one_iff a).1 ha
    obtain ⟨c, rfl⟩ := hs b
    exact δ_map c
  exact ⟨fun a b ↦ (h a).trans (h b).symm⟩

/-- Injectivity on components and surjectivity on the fundamental group at a vertex make the
fibre over its image preconnected. No nonemptiness assumption on other fibres is needed. -/
lemma isPreconnected_fiber (hi : Function.Injective (mapπ₀ p))
    (hs : Function.Surjective (π.map (n := 1) p hx)) :
    (fiber p y : SSet).IsPreconnected := by
  have h₀ : Function.Injective (π.map (n := 0) p hx) := by
    intro a b hab
    apply (π.zeroEquiv X x).injective
    apply hi
    simpa only [π.zeroEquiv_map] using congrArg (π.zeroEquiv Y y) hab
  have := subsingleton_π_fiber hx h₀ hs
  exact (π.zeroEquiv (fiber p y : SSet) (fiber.basePoint p hx)).symm.injective.subsingleton

end KanComplex.HomotopySequence

open KanComplex

/-- A Kan fibration over a Kan complex which is bijective on components and surjective on
fundamental groups at every source vertex has connected fibres. -/
lemma isConnected_fiber_of_bijective_mapπ₀ (p : X ⟶ Y) [Fibration p] [KanComplex Y]
    (h₀ : Function.Bijective (mapπ₀ p))
    (h₁ : ∀ x : X _⦋0⦌, Function.Surjective (π.map (n := 1) p (y := p.app _ x) rfl))
    (y : Y _⦋0⦌) : (fiber p y : SSet).IsConnected := by
  have := nonempty_fiber_of_surjective_mapπ₀ p h₀.2 y
  obtain ⟨z⟩ := ‹(fiber p y : SSet).Nonempty›
  have hz : p.app _ z.val = y := by
    simpa only [SimplexCategory.const_eq_id, op_id, Functor.map_id_apply] using
      (mem_fiber_iff p y z.val).1 z.property
  have hs (x : X _⦋0⦌) (y : Y _⦋0⦌) (hx : p.app _ x = y) :
      Function.Surjective (π.map (n := 1) p hx) := by
    subst y
    exact h₁ x
  have := HomotopySequence.isPreconnected_fiber hz h₀.1 (hs _ _ hz)
  exact ⟨inferInstance⟩

/-- Bijections on positive homotopy groups of a Kan fibration over a Kan complex force all
positive homotopy groups of its fibres to be trivial, at every fibre vertex. -/
lemma subsingleton_π_fiber_of_bijective (p : X ⟶ Y) [Fibration p] [KanComplex Y]
    (h : ∀ (x : X _⦋0⦌) (n : ℕ),
      Function.Bijective (π.map (n := n + 1) p (y := p.app _ x) rfl))
    (y : Y _⦋0⦌) (z : (fiber p y : SSet) _⦋0⦌) (n : ℕ) :
    Subsingleton (π (n + 1) (fiber p y : SSet) z) := by
  have hz : p.app _ z.val = y := by
    simpa only [SimplexCategory.const_eq_id, op_id, Functor.map_id_apply] using
      (mem_fiber_iff p y z.val).1 z.property
  have h' (x : X _⦋0⦌) (y : Y _⦋0⦌) (hx : p.app _ x = y) (n : ℕ) :
      Function.Bijective (π.map (n := n + 1) p hx) := by
    subst y
    exact h x n
  have he : fiber.basePoint p hz = z := Subtype.ext (fiber.coe_basePoint p hz)
  rw [← he]
  exact HomotopySequence.subsingleton_π_fiber hz (h' _ _ hz n).1 (h' _ _ hz (n + 1)).2

end SSet
