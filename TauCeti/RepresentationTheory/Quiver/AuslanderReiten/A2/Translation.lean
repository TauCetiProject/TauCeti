/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Translation
import TauCeti.RepresentationTheory.Quiver.Kronecker.Translate

/-!
# The Auslander–Reiten translation of `A₂`

In the coordinates `S₁`, `S₂`, `P₁` of `a2VertexEquiv`, the partial translation sends
vertex `0` to vertex `1` and is undefined at vertices `1` and `2`. Together with the
arrow computation in `A2.Basic`, this describes the three-vertex mesh `S₂ → P₁ → S₁`
with `τ S₁ = S₂`, over every field. The translation is the existing construction by
minimal projective presentations and scalar duality, computed on actual isomorphism classes.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras* (1995), IV.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type) [Unique A]

/-- The complete partial translation of the one-arrow quiver: `τ[S₁] = [S₂]`, while
translation is undefined at the projective vertices `[S₂]` and `[P₁]`. -/
@[simp↓]
theorem translate_a2VertexEquiv (i : Fin 3) :
    translate (a2VertexEquiv k A i) =
      if i = 0 then some (a2VertexEquiv k A 1) else none := by
  classical
  have cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases cases i with rfl | rfl | rfl
  · simp only [a2VertexEquiv_zero, a2VertexEquiv_one, ↓reduceIte]
    rw [translate_of_eq_some_of_iff]
    exact ⟨(isAlmostSplit_kroneckerARSequence k A).not_projective_X₃,
      nonempty_iso_arTranslate_simpleRep_src_kronecker k A _⟩
  · simp only [a2VertexEquiv_one, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte,
      translate_of_eq_none_iff]
    -- The target projective has dimension vector (0,1), so the three-object
    -- classification identifies it with the target simple.
    rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
      (indecProjRep k (Quiver.Kronecker A) tgt)
      (indecomposable_indecProjRep_of_isAcyclic Quiver.Kronecker.isAcyclic tgt) with h | h | h
    · obtain ⟨e⟩ := h
      have h := congrFun (dimVector_eq_of_iso e) src
      rw [dimVector_indecProjRep, dimVector_simpleRep] at h
      simp at h
    · obtain ⟨e⟩ := h
      exact Projective.of_iso e inferInstance
    · obtain ⟨e⟩ := h
      have h := congrFun (dimVector_eq_of_iso e) src
      rw [dimVector_indecProjRep, dimVector_indecProjRep] at h
      simp at h
  · simp only [a2VertexEquiv_two, show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte,
      translate_of_eq_none_iff]
    infer_instance

end TauCeti.irreducibleMorphismQuiver
