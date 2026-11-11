/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice

/-!
# Limits and colimits in simplicial sets

Let `p : K ⟶ C` be a diagram in a simplicial set `C`, typically a quasicategory. The cones over
`p` are the vertices of the slice `C_{/p}` (`SSet.slice`), that is, the maps `Δ[0] ⋆ K ⟶ C`
extending `p`, and the edges of `C_{/p}` are the morphisms of cones. Following Joyal and Lurie, a
cone is a *limit cone* (`SSet.slice.IsLimit`) if it is a terminal vertex of `C_{/p}`. Dually, the
cocones under `p` are the vertices of the coslice `C_{p/}` (`SSet.coslice`), the maps
`K ⋆ Δ[0] ⟶ C` extending `p`, and a cocone is a *colimit cocone* (`SSet.coslice.IsColimit`) if
it is an initial vertex of `C_{p/}`.

Limit cones are unique up to equivalence: every cone has a morphism to a limit cone
(`SSet.slice.IsLimit.nonempty_edge`), and every morphism between limit cones is an equivalence of
`C_{/p}` (`SSet.slice.IsLimit.isEquivalence`), and dually for colimit cocones. Colimits in `C` are
limits in the opposite simplicial set `Cᵒᵖ` (`SSet.coslice.isColimit_iff_isLimit_op`), since the
coslice `C_{p/}` is the opposite of the slice `Cᵒᵖ_{/pᵒᵖ}`. For the empty diagram, the slice and
the coslice are `C` itself, so that its limits are the terminal vertices of `C`
(`SSet.slice.isLimit_iff_isTerminalVertex_π`) and its colimits the initial vertices
(`SSet.coslice.isColimit_iff_isInitialVertex_π`). In the nerve of a category these are the
terminal and the initial objects (`SSet.slice.isLimit_iff_nonempty_isTerminal`,
`SSet.coslice.isColimit_iff_nonempty_isInitial`).

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
* J. Lurie, *Higher Topos Theory*, Definition 1.2.13.4.
-/

public section

universe v u u'

open CategoryTheory Limits Simplicial

namespace SSet

variable {K C : SSet.{u}} (p : K ⟶ C)

namespace slice

/-- A cone `c` over a diagram `p : K ⟶ C`, that is a vertex of the slice `C_{/p}`, is a *limit
cone* if it is a terminal vertex of `C_{/p}`. -/
def IsLimit (c : (slice p) _⦋0⦌) : Prop :=
  (slice p).IsTerminalVertex c

variable {p}

lemma isLimit_iff (c : (slice p) _⦋0⦌) : IsLimit p c ↔ (slice p).IsTerminalVertex c :=
  Iff.rfl

namespace IsLimit

variable {c c' : (slice p) _⦋0⦌}

/-- Every cone has a morphism to a limit cone. -/
lemma nonempty_edge (hc : IsLimit p c) (d : (slice p) _⦋0⦌) : Nonempty ((slice p).Edge d c) :=
  IsTerminalVertex.nonempty_edge hc d

/-- Every morphism between limit cones is an equivalence. Thus limit cones are unique up to
equivalence. -/
lemma isEquivalence (hc : IsLimit p c) (hc' : IsLimit p c') (e : (slice p).Edge c c') :
    e.IsEquivalence :=
  let ⟨I⟩ := IsTerminalVertex.nonempty_invStruct hc hc' e
  I.isEquivalence

end IsLimit

variable (p) in
/-- The limit cones of the empty diagram are the terminal vertices: when `K` is empty, a cone over
`p` is a limit cone exactly when its cone point is a terminal vertex of `C`. -/
lemma isLimit_iff_isTerminalVertex_π (hK : ¬ K.Nonempty) (c : (slice p) _⦋0⦌) :
    IsLimit p c ↔ C.IsTerminalVertex ((π p).app _ c) :=
  have := isIso_π p hK
  (isTerminalVertex_iff_of_iso (asIso (π p)) c).symm

/-- In the nerve of a category `D`, the limit cones of the empty diagram are the cones whose cone
point is a terminal object of `D`. -/
lemma isLimit_iff_nonempty_isTerminal {D : Type u'} [Category.{v} D] {L : SSet.{max u' v}}
    (q : L ⟶ nerve D) (hL : ¬ L.Nonempty) (c : (slice q) _⦋0⦌) :
    IsLimit q c ↔ Nonempty (IsTerminal (nerveEquiv ((π q).app _ c))) := by
  rw [isLimit_iff_isTerminalVertex_π q hL]
  generalize (π q).app _ c = v
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective v
  rw [nerve.isTerminalVertex_iff, Equiv.apply_symm_apply]

end slice

namespace coslice

/-- A cocone `c` under a diagram `p : K ⟶ C`, that is a vertex of the coslice `C_{p/}`, is a
*colimit cocone* if it is an initial vertex of `C_{p/}`. -/
def IsColimit (c : (coslice p) _⦋0⦌) : Prop :=
  (coslice p).IsInitialVertex c

variable {p}

lemma isColimit_iff (c : (coslice p) _⦋0⦌) : IsColimit p c ↔ (coslice p).IsInitialVertex c :=
  Iff.rfl

/-- Colimit cocones under `p` are the limit cones over the opposite diagram `pᵒᵖ` in the
opposite simplicial set `Cᵒᵖ`, under the identification of `C_{p/}` with `(Cᵒᵖ_{/pᵒᵖ})ᵒᵖ`. -/
lemma isColimit_iff_isLimit_op (c : (coslice p) _⦋0⦌) :
    IsColimit p c ↔ slice.IsLimit (opFunctor.map p)
      ((slice (opFunctor.map p)).opObjEquiv ((opSliceIso p).hom.app _ c)) := by
  have h := isInitialVertex_op_iff
    ((slice (opFunctor.map p)).opObjEquiv ((opSliceIso p).hom.app _ c))
  rw [Equiv.symm_apply_apply] at h
  rw [isColimit_iff, ← isInitialVertex_iff_of_iso (opSliceIso p), h, slice.isLimit_iff]

namespace IsColimit

variable {c c' : (coslice p) _⦋0⦌}

/-- Every cocone has a morphism from a colimit cocone. -/
lemma nonempty_edge (hc : IsColimit p c) (d : (coslice p) _⦋0⦌) :
    Nonempty ((coslice p).Edge c d) :=
  IsInitialVertex.nonempty_edge hc d

/-- Every morphism between colimit cocones is an equivalence. Thus colimit cocones are unique up
to equivalence. -/
lemma isEquivalence (hc : IsColimit p c) (hc' : IsColimit p c') (e : (coslice p).Edge c c') :
    e.IsEquivalence :=
  let ⟨I⟩ := IsInitialVertex.nonempty_invStruct hc hc' e
  I.isEquivalence

end IsColimit

variable (p) in
/-- The colimit cocones of the empty diagram are the initial vertices: when `K` is empty, a cocone
under `p` is a colimit cocone exactly when its cone point is an initial vertex of `C`. -/
lemma isColimit_iff_isInitialVertex_π (hK : ¬ K.Nonempty) (c : (coslice p) _⦋0⦌) :
    IsColimit p c ↔ C.IsInitialVertex ((π p).app _ c) :=
  have := isIso_π p hK
  (isInitialVertex_iff_of_iso (asIso (π p)) c).symm

/-- In the nerve of a category `D`, the colimit cocones of the empty diagram are the cocones whose
cone point is an initial object of `D`. -/
lemma isColimit_iff_nonempty_isInitial {D : Type u'} [Category.{v} D] {L : SSet.{max u' v}}
    (q : L ⟶ nerve D) (hL : ¬ L.Nonempty) (c : (coslice q) _⦋0⦌) :
    IsColimit q c ↔ Nonempty (IsInitial (nerveEquiv ((π q).app _ c))) := by
  rw [isColimit_iff_isInitialVertex_π q hL]
  generalize (π q).app _ c = v
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective v
  rw [nerve.isInitialVertex_iff, Equiv.apply_symm_apply]

end coslice

end SSet
