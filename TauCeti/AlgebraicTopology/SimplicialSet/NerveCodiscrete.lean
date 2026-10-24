/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete

/-!
# Homotopies into codiscrete nerves

Any two simplicial maps into the nerve of a codiscrete category are simplicially homotopic.
The same assertion after universe lifting lets arbitrarily large codiscrete nerves be
compared with small models. The homotopy chooses the first or second vertex list according
to the corresponding vertex of the interval. This uses Mathlib's
`CategoryTheory.Codiscrete.equivFun` description of the simplices of a codiscrete nerve.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter I, §1.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

universe u v

namespace TauCeti

/-- Any two maps into a universe lift of a codiscrete nerve are simplicially homotopic.
The type of objects may be empty; existence of the maps already gives all required vertices. -/
lemma nonempty_homotopy_ulift_nerveCodiscrete {A : Type v} {Z : SSet.{max u v}}
    (f g : Z ⟶ SSet.uliftFunctor.{u, v}.obj (nerve (Codiscrete A))) :
    Nonempty (SSet.Homotopy f g) := by
  refine ⟨{ h := ?_, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · exact
    { app n := ↾fun p ↦ ULift.up (Codiscrete.equivFun.symm fun k ↦
        if (SSet.stdSimplex.objEquiv p.2).toOrderHom k = 0 then ((f.app n p.1).down.obj k).as
        else ((g.app n p.1).down.obj k).as)
      naturality n m a := by
        ext p
        apply ULift.ext
        apply Codiscrete.equivFun.injective
        funext k
        -- The lifted nerve operator reindexes the list of vertices.
        change (if (SSet.stdSimplex.objEquiv ((Δ[1] : SSet).map a p.2)).toOrderHom k = 0 then
            ((f.app m (Z.map a p.1)).down.obj k).as
            else ((g.app m (Z.map a p.1)).down.obj k).as) =
          (if (SSet.stdSimplex.objEquiv p.2).toOrderHom (a.unop.toOrderHom k) = 0 then
            ((f.app n p.1).down.obj (a.unop.toOrderHom k)).as
            else ((g.app n p.1).down.obj (a.unop.toOrderHom k)).as)
        have hf := congrArg (fun s ↦ (s.down.obj k).as) (f.naturality_apply a p.1)
        have hg := congrArg (fun s ↦ (s.down.obj k).as) (g.naturality_apply a p.1)
        rw [hf, hg]
        rfl }
  · ext n p
    apply ULift.ext
    apply Codiscrete.equivFun.injective
    funext k
    rcases n with ⟨⟨n⟩⟩
    -- The initial endpoint selects the first list of vertices.
    change (if (SSet.ι₀.app _ p).2 k = 0 then
      ((f.app _ (SSet.ι₀.app _ p).1).down.obj k).as
      else ((g.app _ (SSet.ι₀.app _ p).1).down.obj k).as) = _
    simp
    rfl
  · ext n p
    apply ULift.ext
    apply Codiscrete.equivFun.injective
    funext k
    rcases n with ⟨⟨n⟩⟩
    -- The final endpoint selects the second list of vertices.
    change (if (SSet.ι₁.app _ p).2 k = 0 then
      ((f.app _ (SSet.ι₁.app _ p).1).down.obj k).as
      else ((g.app _ (SSet.ι₁.app _ p).1).down.obj k).as) = _
    simp
    rfl
  · ext n ⟨⟨x, hx⟩, t⟩
    exact hx.elim

end TauCeti
