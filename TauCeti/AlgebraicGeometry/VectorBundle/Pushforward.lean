/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.RingTheory.Flat.Projective

/-!
# Finite locally free morphisms and pushforward of the structure sheaf

A quasi-coherent `𝒪_X`-module `M` is finite locally free if and only if, over every affine open
`U` of `X`, its module of sections `Γ(M, U)` is a finitely generated projective `Γ(X, U)`-module
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen`). For a
module-finite commutative `Γ(X, U)`-algebra `S`, projectivity as a module is equivalent to flatness
and finite presentation as an algebra (`TauCeti.moduleProjective_iff_flat_and_finitePresentation`).

Applied to a quasi-coherent commutative `𝒪_X`-algebra `A`, this shows that the underlying
`𝒪_X`-module `A.X` is finite locally free if and only if the relative spectrum
`Spec_X(A) ⟶ X` is finite, flat, and locally of finite presentation (Stacks, Lemma 29.48.2
(02KB)). Via the recovery isomorphism `Spec_X(f_* 𝒪_Y) ≅ Y` of an affine morphism `f : Y ⟶ X`,
the pushforward `f_* 𝒪_Y` of the structure sheaf is finite locally free if and only if `f` is
finite, flat, and locally of finite presentation; in particular this holds for every finite étale
morphism.

## Main results

* `CategoryTheory.CommMon.isFiniteLocallyFree_X_iff`: for a quasi-coherent commutative
  `𝒪_X`-algebra `A`, the module `A.X` is finite locally free if and only if `Spec_X(A) ⟶ X` is
  finite, flat, and locally of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit_iff`: for an affine morphism
  `f : Y ⟶ X`, the pushforward `f_* 𝒪_Y` of the structure sheaf is finite locally free if and only
  if `f` is finite, flat, and locally of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit`: `f_* 𝒪_Y` is finite locally
  free when `f` is finite, flat, and locally of finite presentation.

## References

* [The Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory.CommMon

open AlgebraicGeometry

/-- For a quasi-coherent commutative `𝒪_X`-algebra `A`, the underlying `𝒪_X`-module `A.X` is
finite locally free if and only if the relative spectrum `Spec_X(A) ⟶ X` is finite, flat, and
locally of finite presentation. Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_X_iff {X : Scheme.{u}} (A : CommMon X.Modules)
    [A.X.IsQuasicoherent] :
    Scheme.Modules.isFiniteLocallyFree X A.X ↔
      IsFinite A.relativeSpecToBase ∧ Flat A.relativeSpecToBase ∧
        LocallyOfFinitePresentation A.relativeSpecToBase := by
  rw [Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen, A.relativeSpec_finite_iff,
    A.relativeSpec_flat_iff, A.relativeSpec_finitePresentation_iff]
  have hiff (U : X.Opens) :
      (Module.Finite Γ(X, U) Γ(A.X, U) ∧ Module.Projective Γ(X, U) Γ(A.X, U)) ↔
        Module.Finite Γ(X, U) Γ(A.X, U) ∧ Module.Flat Γ(X, U) Γ(A.X, U) ∧
          Algebra.FinitePresentation Γ(X, U) Γ(A.X, U) :=
    and_congr_right fun _ ↦
      TauCeti.moduleProjective_iff_flat_and_finitePresentation Γ(X, U) Γ(A.X, U)
  exact ⟨fun h ↦ ⟨fun U hU ↦ ((hiff U).mp (h U hU)).1, fun U hU ↦ ((hiff U).mp (h U hU)).2.1,
      fun U hU ↦ ((hiff U).mp (h U hU)).2.2⟩,
    fun ⟨hfin, hflat, hfp⟩ U hU ↦ (hiff U).mpr ⟨hfin U hU, hflat U hU, hfp U hU⟩⟩

end CategoryTheory.CommMon

namespace AlgebraicGeometry.Scheme.Hom

/-- For an affine morphism `f : Y ⟶ X`, the pushforward `f_* 𝒪_Y` of the structure sheaf is
finite locally free if and only if `f` is finite, flat, and locally of finite presentation.
Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit_iff {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] :
    Modules.isFiniteLocallyFree X ((Modules.pushforward f).obj (𝟙_ Y.Modules)) ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  rw [← f.pushforwardStructureAlgebra_X, f.pushforwardStructureAlgebra.isFiniteLocallyFree_X_iff,
    ← f.relativeSpecFunctionsToScheme_comp]
  refine ⟨fun ⟨_, _, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ⟨inferInstance, inferInstance, inferInstance⟩⟩
  -- `f` is isomorphic on the source to `f.relativeSpecFunctionsToScheme ≫ f`.
  have hf : f = inv f.relativeSpecFunctionsToScheme ≫ (f.relativeSpecFunctionsToScheme ≫ f) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [hf]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- If `f : Y ⟶ X` is finite, flat, and locally of finite presentation, then `f_* 𝒪_Y` is a
finite locally free `𝒪_X`-module. In particular this applies when `f` is finite and étale.
Stacks, Lemma 29.48.2 (02KB). -/
@[stacks 02KB]
theorem isFiniteLocallyFree_pushforward_unit {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    Modules.isFiniteLocallyFree X ((Modules.pushforward f).obj (𝟙_ Y.Modules)) :=
  f.isFiniteLocallyFree_pushforward_unit_iff.mpr ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
