/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Minimal
import TauCeti.Algebra.Module.AuslanderReiten.Inverse
import TauCeti.Algebra.Module.AuslanderReiten.Isomorphism
import TauCeti.Algebra.Module.MinimalProjectivePresentation.Finite
import TauCeti.LinearAlgebra.Dual.Equivalence
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Recovering a module from the transpose of its transpose

Let `M` be a non-projective indecomposable module over a finite-dimensional algebra. If `P`
is a finite minimal presentation of `M` and `Q` is a finite minimal right presentation of
`Tr P`, the left-valued right transpose of `Q` is isomorphic to `M`. Thus minimal
transposition recovers actual indecomposable modules, rather than only stable objects.

The scalar-dual form proves the recovery composite `Tr D (D Tr M) ≅ M`: the right scalar
dual of `D Tr M` is specified by an equivariant pairing, so no global module action on
unbundled scalar duals is introduced. Both presentations may be chosen independently.
The transpose recovery holds for rings Artinian on both sides. The scalar-dual
form holds over an arbitrary field, without algebraic closedness.

The construction uses the right-module recovery criterion of `DoubleTranspose.Minimal`,
reflection of isomorphism classes by `Isomorphism`, and Mathlib's finite-length module API.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

universe u v w

variable {A : Type v} [Ring A] {M : ModuleCat.{max v w} A}

/-- Minimally transposing the transpose of a non-projective indecomposable module recovers
that module. The right transpose has values in `A`, so the equivalence is `A`-linear even
when `A` is noncommutative. -/
theorem nonempty_linearEquiv_rightTranspose_transpose
    [IsArtinianRing A] [IsArtinianRing Aᵐᵒᵖ]
    (P : FiniteProjectivePresentation M) (hP : IsMinimalProjectivePresentation P.p P.π)
    (Q : FiniteProjectivePresentation (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)))
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (hiM : IsIndecomposableModule A M) (hpM : ¬ Module.Projective A M) :
    Nonempty (Q.rightTranspose ≃ₗ[A] M) := by
  have : Module.Finite A M := Module.Finite.of_surjective P.π P.surjective
  have hM : IsFiniteLength A M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hT : IsFiniteLength Aᵐᵒᵖ (AuslanderReitenTranspose P.p) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hiT := (P.isIndecomposableModule_auslanderReitenTranspose_iff hP hM hiM).mpr hpM
  have hpT : ¬ Module.Projective Aᵐᵒᵖ (AuslanderReitenTranspose P.p) := by
    intro hp
    exact hpM (hP.subsingleton_auslanderReitenTranspose_iff_projective.mp
      (hP.isSuperfluous_ker.projective_auslanderReitenTranspose_iff_subsingleton.mp hp))
  have hiQ := (Q.isIndecomposableModule_rightTranspose_iff hQ hT hiT).mpr hpT
  have hQT : IsFiniteLength A Q.rightTranspose :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨R, hR⟩ := exists_isMinimal (M := Q.rightTranspose)
  have hRT : IsFiniteLength Aᵐᵒᵖ (AuslanderReitenTranspose R.p) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  -- The right recovery comparison identifies Tr R with Tr P. Minimality of P removes
  -- the projective retracts, and reflection of transposed isomorphisms then recovers M.
  obtain ⟨e⟩ := (Q.nonempty_linearEquiv_transpose_rightTranspose_iff_isZero_projective_retract
    R hR.isSuperfluous_ker hT hRT).mpr (fun r h ↦ by
      let := h
      exact hP.isSuperfluous_ker.isZero_of_retract_auslanderReitenTranspose r)
  exact (P.nonempty_linearEquiv_of_auslanderReitenTranspose R hM hQT hiM hiQ hpM e.symm).map
    LinearEquiv.symm

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
  {N : ModuleCat.{max v w} Aᵐᵒᵖ} [Module k N] [IsScalarTower k Aᵐᵒᵖ N]
  [FiniteDimensional k N]

/-- The inverse translate `Tr D` recovers a non-projective indecomposable module from its
`D Tr` translate. An equivariant pairing specifies the right scalar dual `N`, and its finite
minimal presentation may be chosen independently of the presentation of the original module. -/
theorem nonempty_linearEquiv_rightTranspose_dual_translate
    (P : FiniteProjectivePresentation M) (hP : IsMinimalProjectivePresentation P.p P.π)
    (Q : FiniteProjectivePresentation N) (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (e : AuslanderReitenTranslate k P.p ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (y : AuslanderReitenTranslate k P.p) (x : N),
      e (a • y) x = e y (MulOpposite.op a • x))
    (hiM : IsIndecomposableModule A M) (hpM : ¬ Module.Projective A M) :
    Nonempty (Q.rightTranspose ≃ₗ[A] M) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  have : FiniteDimensional k (AuslanderReitenTranspose P.p) := Module.Finite.trans Aᵐᵒᵖ _
  let d := (LinearEquiv.refl k (AuslanderReitenTranslate k P.p)).ofEquivariantDual e
    (fun a y x ↦ AuslanderReitenTranslate.smul_apply a y x) he
    (LinearEquiv.refl A (AuslanderReitenTranslate k P.p))
  -- Only the augmentation changes under d; the dual presenting map, and hence the
  -- right transpose, is the same. Keep these maps explicit in the transported presentation.
  let Q' : FiniteProjectivePresentation
      (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) :=
    { Q with
      π := d.toLinearMap ∘ₗ Q.π
      exact := LinearEquiv.postcomp_exact_iff_exact.mpr Q.exact
      surjective := d.surjective.comp Q.surjective }
  exact P.nonempty_linearEquiv_rightTranspose_transpose hP Q' (hQ.comp_linearEquiv d) hiM hpM

end TauCeti.FiniteProjectivePresentation
