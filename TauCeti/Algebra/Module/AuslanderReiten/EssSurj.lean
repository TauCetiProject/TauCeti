/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Basic

/-!
# Essential surjectivity of the stable transpose

Every finitely presented right module is the transpose of a finite projective presentation
of a finitely presented left module. Dualizing a right presentation with values in the
regular module `A` produces the left presentation; evaluation recovers the original right
module when that presentation is transposed.

Consequently the stable transpose functor is essentially surjective for every choice of
finite projective presentations, over an arbitrary ring. This is the object-level part of
the Auslander–Bridger duality between finitely presented stable left and right modules.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]

namespace FiniteProjectivePresentation

variable {N : ModuleCat.{v} Aᵐᵒᵖ}

/-- Every finite projective right presentation is recovered by transposing a finite projective
left presentation. The recovered module is linearly isomorphic before passing to the stable
category. -/
theorem exists_transpose_linearEquiv (Q : FiniteProjectivePresentation N) :
    ∃ (M : ModuleCat.{max u v} A) (_ : Module.FinitePresentation A M)
      (P : FiniteProjectivePresentation M), Nonempty (AuslanderReitenTranspose P.p ≃ₗ[Aᵐᵒᵖ] N) :=
  ⟨Q.rightTranspose, inferInstance, Q.rightTransposePresentation,
    ⟨rightDoubleTransposePresentationEquiv A Q.p Q.π Q.exact Q.surjective⟩⟩

end FiniteProjectivePresentation

variable (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
  FiniteProjectivePresentation M.obj.as)

/-- The stable transpose attached to any family of finite projective presentations is
essentially surjective onto the opposite category of finitely presented stable right modules. -/
instance stableTransposeFunctor_essSurj : (stableTransposeFunctor P).EssSurj where
  mem_essImage N := by
    let := N.unop.property
    let Q := FiniteProjectivePresentation.ofFinitePresentation (M := N.unop.obj.as)
    obtain ⟨M, hM, R, ⟨e⟩⟩ := Q.exists_transpose_linearEquiv
    let X : FinitelyPresentedStableModule.{u, max u v} A :=
      ⟨(ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))).obj M,
        hM⟩
    let T := ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))
    let i : R.stableTransposeObj ≅ N.unop := ObjectProperty.isoMk _ (T.mapIso e.toModuleIso)
    refine ⟨X, ⟨?_⟩⟩
    exact eqToIso (stableTransposeFunctor_obj P X) ≪≫
      ((P X).stableTransposeIso R ≪≫ i).symm.op

/-- The stable transpose formed using chosen finite projective presentations is essentially
surjective. -/
instance stableTranspose_essSurj : (stableTranspose.{u, v} A).EssSurj := by
  rw [stableTranspose_def]
  infer_instance

end TauCeti
