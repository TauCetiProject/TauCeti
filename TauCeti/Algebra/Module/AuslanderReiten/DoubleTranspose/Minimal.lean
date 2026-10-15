/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.ProjectiveSummand
public import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.Isomorphism
public import TauCeti.Algebra.Module.AuslanderReiten.Translate
import TauCeti.LinearAlgebra.Dual.Equivalence

/-!
# Recovery by minimal transposition

Let `Q` present a right module `N`, and let `P` present its right transpose `Tr N`,
the cokernel of the `A`-valued dual of the presenting map of `Q`.
Transposing `P` recovers `N` up to actual isomorphism
exactly when `N` has no nonzero projective retracts, provided `N` and the transpose of `P`
have finite length.
The first map of `P` must have superfluous kernel, as it does for a minimal presentation.
The presentation `Q` need not be minimal. The scalar-dual characterization gives the
corresponding recovery by the Auslander–Reiten translate.

This removes the projective ambiguity from one composite of the Auslander–Bridger
correspondence. Applied to a scalar dual, it is the recovery step for the inverse `Tr D`
of the Auslander–Reiten translate. Using the `A`-valued right transpose keeps the recovery
linear over `Aᵐᵒᵖ`, even for a noncommutative ring.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory CategoryTheory.Limits

universe u v

variable {A : Type u} [Ring A] {N : ModuleCat.{max u v} Aᵐᵒᵖ}

local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

/-- Transposition of a right transpose, using a presenting map with superfluous kernel,
recovers the original right module exactly when it has no nonzero projective retracts.
In particular this applies to a minimal presentation; the right presentation is arbitrary. -/
theorem nonempty_linearEquiv_transpose_rightTranspose_iff_isZero_projective_retract
    (Q : FiniteProjectivePresentation N) (P : FiniteProjectivePresentation Q.rightTranspose)
    (hP : IsSuperfluous (LinearMap.ker P.p))
    (hN : IsFiniteLength Aᵐᵒᵖ N)
    (hTr : IsFiniteLength Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) :
    Nonempty (AuslanderReitenTranspose P.p ≃ₗ[Aᵐᵒᵖ] N) ↔
      ∀ {R : ModuleCat.{max u v} Aᵐᵒᵖ}, Retract R N → Projective R → IsZero R := by
  have hPT : ∀ {R : ModuleCat.{max u v} Aᵐᵒᵖ},
      Retract R (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) →
        Projective R → IsZero R := by
    intro R r hR
    let := hR
    exact hP.isZero_of_retract_auslanderReitenTranspose r
  constructor
  · rintro ⟨e⟩ R r hR
    exact hPT (r.trans (Retract.ofIso e.symm.toModuleIso)) hR
  · intro hRN
    let c := P.stableTransposeIso Q.rightTransposePresentation
    let i := (ObjectProperty.ι _).mapIso c
    let e := rightDoubleTransposePresentationEquiv A Q.p Q.π Q.exact Q.surjective
    obtain ⟨j⟩ :=
      (ModuleCat.nonempty_iso_projectiveStableFunctor_obj_iff_of_isZero_projective_retract
        (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) N hTr hN hPT hRN).mp
          ⟨i ≪≫ (T).mapIso e.toModuleIso⟩
    exact ⟨j.toLinearEquiv⟩

variable {k : Type*} [CommSemiring k] [Algebra k A]
  [Module k N] [IsScalarTower k Aᵐᵒᵖ N] [Module.IsReflexive k N]
  {E : Type*} [AddCommGroup E] [Module A E] [Module k E]

/-- Applying `D Tr` to a presentation of the right transpose of `N` recovers the scalar
dual `D N` exactly when `N` has no nonzero projective retracts. The scalar dual is specified by
an equivariant pairing, and reflexivity suffices in place of a finite-dimensional field
hypothesis. This is the recovery composite for the inverse `Tr D` correspondence. -/
theorem nonempty_linearEquiv_translate_rightTranspose_iff_isZero_projective_retract
    (Q : FiniteProjectivePresentation N) (P : FiniteProjectivePresentation Q.rightTranspose)
    (hP : IsSuperfluous (LinearMap.ker P.p))
    (hN : IsFiniteLength Aᵐᵒᵖ N)
    (hTr : IsFiniteLength Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    [Module.IsReflexive k (AuslanderReitenTranspose P.p)]
    (e : E ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (x : E) (n : N), e (a • x) n = e x (MulOpposite.op a • n)) :
    Nonempty (AuslanderReitenTranslate k P.p ≃ₗ[A] E) ↔
      ∀ {R : ModuleCat.{max u v} Aᵐᵒᵖ}, Retract R N → Projective R → IsZero R := by
  rw [← Q.nonempty_linearEquiv_transpose_rightTranspose_iff_isZero_projective_retract P hP hN hTr]
  constructor
  · rintro ⟨f⟩
    exact ⟨((LinearEquiv.refl k (AuslanderReitenTranslate k P.p)).ofEquivariantDual e
      (fun a φ n ↦ AuslanderReitenTranslate.smul_apply a φ n) he f).symm⟩
  · rintro ⟨d⟩
    exact ⟨(LinearEquiv.refl k (AuslanderReitenTranslate k P.p)).toEquivariantDual e
      (fun a φ n ↦ AuslanderReitenTranslate.smul_apply a φ n) he d.symm⟩

end TauCeti.FiniteProjectivePresentation
