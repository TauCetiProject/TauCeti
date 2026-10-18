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
`Δ[0] ⟶ Δ[1]`. This file names its quotient map `TauCeti.SSet.S1.quotient`, its descent
`TauCeti.SSet.S1.desc` and its basepoint `TauCeti.SSet.S1.basepoint`, shows that both vertices
of the interval are sent to the basepoint, and proves `TauCeti.SSet.S1.isPushout`: the circle is
the pushout of the boundary inclusion `∂Δ[1] ⟶ Δ[1]` along the collapse `∂Δ[1] ⟶ Δ[0]`, i.e. the
interval with its boundary collapsed to the basepoint.

Like Mathlib's `SSet.S1`, everything in this file lives in universe `0`.
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

/-- A map from the simplicial interval which identifies its two vertices descends to the
simplicial circle. -/
noncomputable def desc {X : SSet} (f : Δ[1] ⟶ X)
    (h : SSet.stdSimplex.δ 0 ≫ f = SSet.stdSimplex.δ 1 ≫ f) : SSet.S1 ⟶ X :=
  coequalizer.desc f h

/-- The descent of `f` to the circle restricts back to `f` along the quotient map. -/
@[reassoc (attr := simp)]
lemma quotient_desc {X : SSet} (f : Δ[1] ⟶ X)
    (h : SSet.stdSimplex.δ 0 ≫ f = SSet.stdSimplex.δ 1 ≫ f) : quotient ≫ desc f h = f :=
  coequalizer.π_desc f h

/-- The distinguished vertex of the simplicial circle. -/
noncomputable def basepoint : Δ[0] ⟶ SSet.S1 :=
  SSet.stdSimplex.δ 0 ≫ quotient

/-- Both vertices of the simplicial interval map to the basepoint of the circle. -/
@[reassoc (attr := simp)]
lemma δ_quotient (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ quotient = basepoint := by
  fin_cases i
  · rfl
  · exact (coequalizer.condition (SSet.stdSimplex.δ 0) (SSet.stdSimplex.δ 1)).symm

@[reassoc]
private lemma boundary_ι_boundaryCollapse (i : Fin 2) :
    SSet.boundary.ι i ≫ boundaryCollapse = 𝟙 Δ[0] :=
  SSet.stdSimplex.ext₀

/-- The quotient map agrees with the basepoint after collapsing the boundary. -/
@[reassoc (attr := simp)]
lemma boundary_ι_quotient :
    (SSet.boundary 1).ι ≫ quotient = boundaryCollapse ≫ basepoint := by
  apply SSet.boundary.hom_ext
  intro i
  simp [boundary_ι_boundaryCollapse_assoc]

/-- Maps from the simplicial circle are determined by their composites with the quotient map. -/
@[ext]
lemma hom_ext {X : SSet} {f g : SSet.S1 ⟶ X} (h : quotient ≫ f = quotient ≫ g) : f = g :=
  coequalizer.hom_ext h

private lemma δ_inl (s : PushoutCocone (SSet.boundary 1).ι boundaryCollapse) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ s.inl = s.inr := by
  simpa [boundary_ι_boundaryCollapse_assoc] using SSet.boundary.ι i ≫= s.condition

/-- The simplicial circle is `Δ[1]/∂Δ[1]`: the pushout of the boundary inclusion along the
collapse of the boundary to the basepoint. -/
lemma isPushout : IsPushout (SSet.boundary 1).ι boundaryCollapse quotient basepoint where
  w := boundary_ι_quotient
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc s.inl ((δ_inl s 0).trans (δ_inl s 1).symm))
    (fun _ ↦ quotient_desc _ _)
    (fun s ↦ by rw [basepoint, Category.assoc, quotient_desc, δ_inl])
    (fun _ _ hm _ ↦ hom_ext (by simpa using hm))⟩

end SSet.S1

end TauCeti
