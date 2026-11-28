/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.PieceQuotient
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Functoriality of degreewise quotients by the positive-degree action

For a graded `𝒜`-module `M`, `M.grading.PieceQuotient 𝒜 p := (M / A₊ M)ₚ` is functorial in
`M : GradedModuleCat 𝒜` into `ModuleCat A₀` via `Submodule.mapQ`, where
`A₀ = SetLike.GradeZero.subalgebra 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.pieceQuotientHom`: the `A₀`-linear map on `PieceQuotient` induced by a
  morphism in `GradedModuleCat 𝒜`.
* `TauCeti.GradedModuleCat.pieceQuotientFunctor`: functoriality of `M.grading.PieceQuotient 𝒜 p`
  into `ModuleCat A₀`.

## Main results

* `TauCeti.GradedModuleCat.pieceQuotientHom_apply`,
  `TauCeti.GradedModuleCat.pieceQuotientHom_pieceQuotientMap`: evaluation and naturality of
  `pieceQuotientHom`.
* `TauCeti.GradedModuleCat.mem_positive_smul_top_of_injective_pieceQuotientHom`: a morphism
  inducing an injective map on `PieceQuotient` in every degree has kernel contained in `A₊ M`.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory _root_.DirectSum

universe uk uA v

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [SetLike.GradedMonoid 𝒜]

private def pieceMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    M.grading.pieceSubmodule 𝒜 p →ₗ[SetLike.GradeZero.subalgebra 𝒜]
      N.grading.pieceSubmodule 𝒜 p :=
  (f.hom.restrictScalars (SetLike.GradeZero.subalgebra 𝒜)).restrict fun _ hx ↦
    InternalGrading.mem_pieceSubmodule.mpr (map_mem f (InternalGrading.mem_pieceSubmodule.mp hx))

/-- The `A₀`-linear map `M.grading.PieceQuotient 𝒜 p →ₗ[A₀] N.grading.PieceQuotient 𝒜 p` induced
by a graded morphism `f : M ⟶ N`. -/
def pieceQuotientHom {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    M.grading.PieceQuotient 𝒜 p →ₗ[SetLike.GradeZero.subalgebra 𝒜]
      N.grading.PieceQuotient 𝒜 p :=
  Submodule.mapQ _ _ (pieceMap f p) fun _ hx ↦
    InternalGrading.mem_positiveSubmodule.mpr <|
      InternalGrading.map_mem_positive_smul_top f.hom <|
        InternalGrading.mem_positiveSubmodule.mp hx

/-- `pieceQuotientHom f p` acts on quotient classes by applying `f.hom`. -/
@[simp]
theorem pieceQuotientHom_apply {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (x : M.grading.pieceSubmodule 𝒜 p) :
    pieceQuotientHom f p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨f.hom x.val, InternalGrading.mem_pieceSubmodule.mpr
          (map_mem f (InternalGrading.mem_pieceSubmodule.mp x.property))⟩ := by
  rw [pieceQuotientHom, Submodule.mapQ_apply]
  rfl

/-- `pieceQuotientHom f p` commutes with the quotient projections `pieceQuotientMap`. -/
@[simp]
theorem pieceQuotientHom_pieceQuotientMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (x : M) :
    pieceQuotientHom f p (M.grading.pieceQuotientMap 𝒜 p x) =
      N.grading.pieceQuotientMap 𝒜 p (f.hom x) := by
  rw [InternalGrading.pieceQuotientMap_apply, InternalGrading.pieceQuotientMap_apply,
    pieceQuotientHom_apply]
  congr 1
  ext
  have h := f.isHomogeneous.map_decompose p x
  rw [add_zero] at h
  exact h

/-- `pieceQuotientHom` sends the identity morphism to the identity linear map. -/
@[simp]
theorem pieceQuotientHom_id (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    pieceQuotientHom (𝟙 M) p = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
  simp [Submodule.mkQ_apply]

/-- `pieceQuotientHom` respects composition of graded morphisms. -/
@[simp]
theorem pieceQuotientHom_comp {M N P : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (g : N ⟶ P) (p : ℤ) :
    pieceQuotientHom (f ≫ g) p = (pieceQuotientHom g p).comp (pieceQuotientHom f p) := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
  simp [Submodule.mkQ_apply]

/-- If a graded morphism `f : M ⟶ N` induces an injective map on `PieceQuotient` in every degree,
then `LinearMap.ker f.hom` lies in the positive-degree action `A₊ M`. -/
theorem mem_positive_smul_top_of_injective_pieceQuotientHom
    {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N)
    (hinj : ∀ q : ℤ, Function.Injective (pieceQuotientHom f q))
    {z : M} (hz : f.hom z = 0) :
    z ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  classical
  rw [← DirectSum.sum_support_decompose M.grading.piece z]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  have hcomp : f.hom (DirectSum.decompose M.grading.piece z q : M) = 0 := by
    have := f.isHomogeneous.isHomogeneous_ker q hz
    simpa [LinearMap.mem_ker] using this
  have hmap : M.grading.pieceQuotientMap 𝒜 q
      (DirectSum.decompose M.grading.piece z q : M) = 0 :=
    hinj q <| by rw [pieceQuotientHom_pieceQuotientMap, hcomp, map_zero, map_zero]
  exact (InternalGrading.pieceQuotientMap_eq_zero_iff_of_mem
    (DirectSum.decompose M.grading.piece z q).property).mp hmap

/-- The degree-`p` quotient `(M / A₊ M)ₚ` as a functor from graded `𝒜`-modules to
`A₀`-modules. -/
@[expose, simps]
def pieceQuotientFunctor (p : ℤ) :
    GradedModuleCat.{v} 𝒜 ⥤ ModuleCat.{v} (SetLike.GradeZero.subalgebra 𝒜) where
  obj M := ModuleCat.of (SetLike.GradeZero.subalgebra 𝒜) (M.grading.PieceQuotient 𝒜 p)
  map f := ModuleCat.ofHom (pieceQuotientHom f p)
  map_id M := ModuleCat.hom_ext (pieceQuotientHom_id M p)
  map_comp f g := ModuleCat.hom_ext (pieceQuotientHom_comp f g p)

end TauCeti.GradedModuleCat
