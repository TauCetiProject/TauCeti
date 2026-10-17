/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The simplicial circle as `Δ[1]/∂Δ[1]`

Mathlib defines the simplicial circle `SSet.S1` as the coequalizer of the two vertex inclusions
`Δ[0] ⟶ Δ[1]`. This file names its quotient map `SSet.S1.quotient` and its basepoint
`SSet.S1.basepoint`, shows that both vertices of the interval are sent to the basepoint, and
proves `SSet.S1.isPushout`: the circle is the pushout of the boundary inclusion `∂Δ[1] ⟶ Δ[1]`
along the collapse `∂Δ[1] ⟶ Δ[0]`, i.e. the interval with its boundary collapsed to the
basepoint.
-/

public section

open CategoryTheory Limits
open scoped Simplicial

namespace TauCeti

namespace SSet.S1

/-- The map which collapses the boundary of the simplicial interval to `Δ[0]`. -/
def boundaryCollapse : (SSet.boundary 1 : SSet.{0}) ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- The quotient map from the simplicial interval to the simplicial circle. -/
noncomputable def quotient : Δ[1] ⟶ SSet.S1 :=
  coequalizer.π (SSet.stdSimplex.δ 0) (SSet.stdSimplex.δ 1)

noncomputable instance : Epi quotient :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The distinguished vertex of the simplicial circle. -/
noncomputable def basepoint : Δ[0] ⟶ SSet.S1 :=
  SSet.stdSimplex.δ 0 ≫ quotient

/-- Both vertices of the simplicial interval map to the basepoint of the circle. -/
@[reassoc]
lemma vertex_quotient (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ quotient = basepoint := by
  fin_cases i
  · rfl
  · exact (coequalizer.condition (SSet.stdSimplex.δ 0) (SSet.stdSimplex.δ 1)).symm

private lemma boundary_ι_boundaryCollapse (i : Fin 2) :
    SSet.boundary.ι i ≫ boundaryCollapse = 𝟙 Δ[0] :=
  SSet.stdSimplex.ext₀

/-- The quotient map agrees with the basepoint after collapsing the boundary. -/
@[reassoc]
lemma boundary_quotient :
    (SSet.boundary 1).ι ≫ quotient = boundaryCollapse ≫ basepoint := by
  apply SSet.boundary.hom_ext
  intro i
  rw [SSet.boundary.ι_ι_assoc, vertex_quotient, ← Category.assoc,
    boundary_ι_boundaryCollapse, Category.id_comp]

/-- Maps from the simplicial circle are determined by their composites with the quotient map. -/
@[ext]
lemma hom_ext {X : SSet} {f g : SSet.S1 ⟶ X} (h : quotient ≫ f = quotient ≫ g) : f = g :=
  coequalizer.hom_ext h

private lemma vertex_inl (s : PushoutCocone (SSet.boundary 1).ι boundaryCollapse) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ s.inl = s.inr := by
  rw [← SSet.boundary.ι_ι i, Category.assoc, s.condition, ← Category.assoc,
    boundary_ι_boundaryCollapse, Category.id_comp]

/-- The simplicial circle is `Δ[1]/∂Δ[1]`: the pushout of the boundary inclusion along the
collapse of the boundary to the basepoint. -/
lemma isPushout : IsPushout (SSet.boundary 1).ι boundaryCollapse quotient basepoint where
  w := boundary_quotient
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ coequalizer.desc s.inl ((vertex_inl s 0).trans (vertex_inl s 1).symm))
    (fun _ ↦ coequalizer.π_desc _ _)
    (fun s ↦ (Category.assoc _ _ _).trans
      ((congrArg _ (coequalizer.π_desc _ _)).trans (vertex_inl s 0)))
    (fun _ _ hm _ ↦ hom_ext (hm.trans (coequalizer.π_desc _ _).symm))⟩

end SSet.S1

end TauCeti
