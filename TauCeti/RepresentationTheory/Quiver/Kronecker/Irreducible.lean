/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Irreducible
public import TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit

/-!
# The irreducible maps of the `A₂` Auslander--Reiten sequence

The inclusion `S₂ ⟶ P₁` and projection `P₁ ⟶ S₁` in the almost-split sequence of the
one-arrow quiver are irreducible. They supply the two displayed arrows in the three-vertex
Auslander--Reiten mesh of `A₂`. The results apply the general criteria for minimal almost-split
maps; this file does not construct the Auslander--Reiten quiver or count all of its arrows.

See Assem, Simson and Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, IV.1, for this mesh and its irreducible maps.
-/

public section

namespace TauCeti

open CategoryTheory Quiver.Kronecker

universe u

variable {k : Type u} [Field k] {A : Type} [Unique A]

private abbrev srcObj (A : Type) := (Paths.of (Quiver.Kronecker A)).obj src
private abbrev tgtObj (A : Type) := (Paths.of (Quiver.Kronecker A)).obj tgt

private theorem end_eq_id_of_comp_kroneckerARSequence_f
    (u : (kroneckerARSequence k A).X₂ ⟶ (kroneckerARSequence k A).X₂)
    (hu : (kroneckerARSequence k A).f ≫ u = (kroneckerARSequence k A).f) :
    u = 𝟙 _ := by
  have htgt : ∀ y : (indecProjRep k (Quiver.Kronecker A) src).obj tgt,
      u.app (tgtObj A) y = y := by
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, (kroneckerARSequence k A).f.app (tgtObj A) x = y := by
      refine ⟨(simpleRepSelfEquiv k tgt).symm (kroneckerProjTgtEquiv k A y), ?_⟩
      exact (kroneckerSimpleTgtToIndecProjRep_app_tgt_apply
        ((simpleRepSelfEquiv k tgt).symm (kroneckerProjTgtEquiv k A y))).trans (by simp)
    have happ := congrArg (fun m : (kroneckerARSequence k A).X₁ ⟶
      (kroneckerARSequence k A).X₂ => m.app (tgtObj A) x) hu
    -- The categorical composite must be read on an element of the vertex module.
    change u.app (tgtObj A) ((kroneckerARSequence k A).f.app (tgtObj A) x) =
      (kroneckerARSequence k A).f.app (tgtObj A) x at happ
    exact happ
  apply eq_id_of_app_indecProjRepBasis_nil_eq_self k u
  have hnat := congrArg (fun m : (indecProjRep k (Quiver.Kronecker A) src).obj (srcObj A) ⟶
      (indecProjRep k (Quiver.Kronecker A) src).obj (tgtObj A) =>
      m (indecProjRepBasis k src src Quiver.Path.nil))
    (u.naturality (arrowPath (default : A)))
  apply indecProjRep_map_arrowPath_injective (k := k) (A := A) default
  -- Evaluate naturality on the trivial-path basis vector; the right vertex map is the identity.
  exact hnat.symm.trans (htgt _)

private theorem end_eq_id_of_kroneckerARSequence_g_comp
    (u : (kroneckerARSequence k A).X₂ ⟶ (kroneckerARSequence k A).X₂)
    (hu : u ≫ (kroneckerARSequence k A).g = (kroneckerARSequence k A).g) :
    u = 𝟙 _ := by
  apply eq_id_of_app_indecProjRepBasis_nil_eq_self k u
  have happ := congrArg (fun m : (kroneckerARSequence k A).X₂ ⟶
      (kroneckerARSequence k A).X₃ =>
      m.app (srcObj A) (indecProjRepBasis k src src Quiver.Path.nil)) hu
  apply (kroneckerProjSrcEquiv k A).injective
  have hproj := simpleRepSelfEquiv_kroneckerARSequence_g_app_src
    (k := k) (A := A) (u.app (srcObj A) (indecProjRepBasis k src src Quiver.Path.nil))
  have hproj' := simpleRepSelfEquiv_kroneckerARSequence_g_app_src
    (k := k) (A := A) (indecProjRepBasis k src src Quiver.Path.nil)
  exact hproj.symm.trans
    ((congrArg (simpleRepSelfEquiv k src) happ).trans hproj')

/-- The inclusion `S₂ ⟶ P₁` in the `A₂` almost-split sequence is irreducible. -/
theorem isIrreducibleMorphism_kroneckerARSequence_f :
    IsIrreducibleMorphism (kroneckerARSequence k A).f := by
  have hf := isLeftAlmostSplit_kroneckerARSequence_f k A
  exact hf.isIrreducibleMorphism_of_minimal hf.not_isSplitEpi
    (fun u hu => by rw [end_eq_id_of_comp_kroneckerARSequence_f u hu]; infer_instance)

/-- The projection `P₁ ⟶ S₁` in the `A₂` almost-split sequence is irreducible. -/
theorem isIrreducibleMorphism_kroneckerARSequence_g :
    IsIrreducibleMorphism (kroneckerARSequence k A).g := by
  have hg := isRightAlmostSplit_kroneckerARSequence_g k A
  exact hg.isIrreducibleMorphism_of_minimal hg.not_isSplitMono
    (fun u hu => by rw [end_eq_id_of_kroneckerARSequence_g_comp u hu]; infer_instance)

end TauCeti
