/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.AuslanderReiten.Indecomposable
public import TauCeti.Algebra.Module.Dual.Indecomposable
public import TauCeti.Algebra.Module.Dual.ProjectiveInjective

/-!
# Indecomposability and projectivity of the inverse Auslander–Reiten translate

The inverse translate `Tr D` takes non-injective indecomposable modules over a
finite-dimensional algebra to non-projective indecomposable modules. Here `D E` is specified
by an equivariant scalar-dual pairing, and `Tr` is the `A`-valued right transpose of a finite
minimal projective presentation. This gives an actual left `A`-module, with no change of its
scalars to the double opposite.

The underlying right-transpose results hold over any ring: a minimal right transpose is
projective exactly when its source is projective, and for a finite-length indecomposable
source it is indecomposable exactly when the source is not projective. The scalar-dual
specializations characterize projectivity by injectivity of `E`, and indecomposability by
non-injectivity of an indecomposable `E`. Algebraic closedness is not required.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

universe u v w z

section RightTranspose

variable {A : Type u} [Ring A] {N : ModuleCat.{v} Aᵐᵒᵖ}

/-- Minimal right presentations of isomorphic modules compute isomorphic left transposes. -/
theorem nonempty_linearEquiv_rightTranspose (Q : FiniteProjectivePresentation N)
    {N' : ModuleCat.{w} Aᵐᵒᵖ} (P : FiniteProjectivePresentation N')
    (f : N ≃ₗ[Aᵐᵒᵖ] N')
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (Q.rightTranspose ≃ₗ[A] P.rightTranspose) := by
  obtain ⟨e⟩ := (hQ.comp_linearEquiv f).nonempty_linearEquiv_auslanderReitenTranspose hP
  exact ⟨(Q.rightTransposeEquiv.trans e).trans P.rightTransposeEquiv.symm⟩

/-- A minimal right transpose vanishes exactly on projective right modules. -/
theorem subsingleton_rightTranspose_iff_projective (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π) :
    Subsingleton Q.rightTranspose ↔ Module.Projective Aᵐᵒᵖ N :=
  Q.rightTransposeEquiv.toEquiv.subsingleton_congr.trans
    hQ.subsingleton_auslanderReitenTranspose_iff_projective

/-- A finite minimal right transpose is projective exactly when its source is projective.
Neither finite length nor indecomposability of the source is required. -/
@[simp]
theorem projective_rightTranspose_iff (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π) :
    Module.Projective A Q.rightTranspose ↔ Module.Projective Aᵐᵒᵖ N := by
  have he : Module.Projective A Q.rightTranspose ↔
      Module.Projective Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p) := by
    constructor <;> intro h <;> let := h
    · exact Module.Projective.of_equiv Q.rightTransposeEquiv
    · exact Module.Projective.of_equiv Q.rightTransposeEquiv.symm
  exact he.trans (hQ.isSuperfluous_ker.projective_auslanderReitenTranspose_iff_subsingleton.trans
    hQ.subsingleton_auslanderReitenTranspose_iff_projective)

/-- The finite minimal right transpose of a finite-length indecomposable module is
indecomposable exactly when the source is not projective. -/
@[simp]
theorem isIndecomposableModule_rightTranspose_iff (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    [Small.{v} Aᵐᵒᵖ] (hN : IsFiniteLength Aᵐᵒᵖ N)
    (hiN : IsIndecomposableModule Aᵐᵒᵖ N) :
    IsIndecomposableModule A Q.rightTranspose ↔ ¬ Module.Projective Aᵐᵒᵖ N := by
  have he : IsIndecomposableModule A Q.rightTranspose ↔
      IsIndecomposableModule Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p) :=
    ⟨fun h ↦ h.of_linearEquiv Q.rightTransposeEquiv,
      fun h ↦ h.of_linearEquiv Q.rightTransposeEquiv.symm⟩
  exact he.trans (Q.isIndecomposableModule_auslanderReitenTranspose_iff hQ hN hiN)

end RightTranspose

section ScalarDual

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] {N : ModuleCat.{w} Aᵐᵒᵖ} [Module k N]
  [IsScalarTower k Aᵐᵒᵖ N] [FiniteDimensional k N]
  {E : Type z} [AddCommGroup E] [Module A E] [Module k E] [Small.{z} A]

/-- The inverse translate `Tr D E`, formed from a finite minimal presentation of the
right scalar dual of `E`, is projective exactly when `E` is injective.
The equivariant pairing specifies the scalar dual without a competing global dual action. -/
theorem projective_rightTranspose_iff_injective (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (e : E ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (y : E) (x : N), e (a • y) x = e y (MulOpposite.op a • x)) :
    Module.Projective A Q.rightTranspose ↔ Module.Injective A E :=
  (Q.projective_rightTranspose_iff hQ).trans
    (e.moduleInjective_iff_projective_of_dual he).symm

/-- For an indecomposable `E`, its inverse translate `Tr D E` is indecomposable exactly
when `E` is not injective. Together with `projective_rightTranspose_iff_injective`, this
places the inverse translate of a non-injective indecomposable among the non-projective
indecomposables. -/
theorem isIndecomposableModule_rightTranspose_iff_not_injective
    (Q : FiniteProjectivePresentation N) (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    [Small.{w} Aᵐᵒᵖ] (e : E ≃ₗ[k] Module.Dual k N)
    (he : ∀ (a : A) (y : E) (x : N), e (a • y) x = e y (MulOpposite.op a • x))
    (hiE : IsIndecomposableModule A E) :
    IsIndecomposableModule A Q.rightTranspose ↔ ¬ Module.Injective A E := by
  have hiN := (e.isIndecomposableModule_iff_of_dual he).mp hiE
  have hN : IsFiniteLength Aᵐᵒᵖ N :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  exact (Q.isIndecomposableModule_rightTranspose_iff hQ hN hiN).trans
    (not_congr (e.moduleInjective_iff_projective_of_dual he)).symm

end ScalarDual

end TauCeti.FiniteProjectivePresentation
