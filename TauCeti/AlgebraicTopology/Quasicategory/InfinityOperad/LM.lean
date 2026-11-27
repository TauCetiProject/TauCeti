/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad.Nerve
public import TauCeti.CategoryTheory.CategoryOfOperators.LM

/-!
# The `∞`-operad of left modules

The nerve of the functor `LM^⊗ ⥤ Fin_*` from the category of operators of the operad `LM` of left
modules is an `∞`-operad (`TauCeti.LM.infinityOperad`), over which left-tensored quasicategories
are fibred. It satisfies the criterion `SSet.InfinityOperad.of_nerveMap`: inert maps lift to
strongly coCartesian morphisms (`TauCeti.LM.Hom.ofInert`), the objects over `⟨1⟩` are the words
of one color, and the morphisms over the inert projections are the projections `LM.ρ`, so the
Segal condition is the decomposition `TauCeti.LM.homLiftEquiv` of a morphism into colored
single-output lifts.

## Main results

* `TauCeti.LM.infinityOperad`: the nerve of `LM^⊗ ⥤ Fin_*` is an `∞`-operad.

## References

* J. Lurie, *Higher Algebra*, §2.1.1 and Definition 4.2.1.7 (the `∞`-operad `LM`).
-/

public section

universe u

open CategoryTheory Functor TauCeti

namespace TauCeti

namespace LM

/-- A family of objects of `LM^⊗` of length one is determined by their colors. -/
private lemma exists_eq_mk_one {ι : Type*} {c : ι → LM.{u}} (h : ∀ i, (c i).len = 1) :
    ∃ col : ι → Color, c = fun i ↦ ⟨1, fun _ ↦ col i⟩ :=
  ⟨fun i ↦ (c i).color (Fin.cast (h i).symm 0), funext fun i ↦ LM.ext (h i) fun j ↦
    congrArg (c i).color (Fin.ext (by have := j.isLt; have := h i; simp; omega))⟩

/-- **The `∞`-operad of left modules**: the nerve of the functor `LM^⊗ ⥤ Fin_*` from the category
of operators of the operad `LM` is an `∞`-operad. Its colors are the algebra color `a` and the
module color `m`. -/
instance infinityOperad : SSet.InfinityOperad.{u} (nerveMap toFinPointed.{u}) :=
  SSet.InfinityOperad.of_nerveMap _
    (fun {x n} g hg ↦ ⟨⟨n.len, x.pushforwardColor g⟩, Hom.ofInert x g hg,
      isStronglyCocartesian_ofInert x g hg⟩)
    (fun n c hc ↦ by
      -- The objects over `⟨1⟩` are the words of one color.
      obtain ⟨col, rfl⟩ := exists_eq_mk_one fun i ↦ congrArg FinPointed.len (hc i)
      exact ⟨⟨n.len, col⟩, fun i ↦ ρ (Y := ⟨n.len, col⟩) i, rfl, fun i ↦ by
        simpa using isStronglyCocartesian_of_isInert (ρ (Y := ⟨n.len, col⟩) i)
          (by simpa using FinPointed.isInert_ρ i)⟩)
    (fun {x y c} φ hφ e ↦ by
      -- The morphisms over the inert projections are the projections `LM.ρ`, so the
      -- postcomposition is the decomposition `LM.homLiftEquiv` into colored single-output lifts.
      obtain ⟨col, rfl⟩ := exists_eq_mk_one fun i ↦
        congrArg FinPointed.len (IsHomLift.codomain_eq toFinPointed (FinPointed.ρ i) (φ i))
      have hφ' (i : Fin y.len) : (φ i).toAssoc = Assoc.ρ (Y := y.toAssocObj) i :=
        Assoc.Hom.ext_of_isInert
          ((isHomLift_iff.1 (hφ i)).trans (Assoc.ρ_base (Y := y.toAssocObj) i).symm)
          (by rw [isHomLift_iff.1 (hφ i)]; exact FinPointed.isInert_ρ (n := FinPointed.mk y.len) i)
      -- The color of the target of `φ i` is the color of `i`.
      obtain rfl : col = y.color := funext fun i : Fin y.len ↦
        (φ i).color_eq_of_word_eq_singleton (j := 0) (by rw [hφ' i, Assoc.ρ_word])
      obtain rfl : φ = fun i ↦ ρ (Y := y) i := funext fun i : Fin y.len ↦
        hom_ext ((hφ' i).trans (ρ_toAssoc i).symm)
      exact ⟨homLiftEquiv e, homLiftEquiv_apply_val e⟩)

end LM

end TauCeti
