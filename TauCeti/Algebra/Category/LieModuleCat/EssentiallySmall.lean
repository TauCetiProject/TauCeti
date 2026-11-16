/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Category.LieModuleCat.Basic
public import TauCeti.Algebra.Lie.Matrix.Equiv

/-!
# Finite-dimensional Lie modules form an essentially small category

For a field `K : Type u` and a Lie algebra `L : Type v` over `K`, the category
`TauCeti.FGLieModuleCat K L` of finite-dimensional `L`-modules is essentially small in the
universe `max u v`, whatever the universe of the carriers.

A module of dimension `n` is determined up to isomorphism by the matrices of the action of `L` in
a basis indexed by `Fin n`: transporting the action along the coordinate isomorphism `M ≃ Kⁿ`
identifies `M` with `Kⁿ` carrying the action given by those matrices, and two modules with the
same matrices are isomorphic through their coordinate isomorphisms
(`TauCeti.nonempty_lieModuleEquiv_of_toMatrix_eq`). So the isomorphism classes
inject into `Σ n, L → Matrix (Fin n) (Fin n) K`, a type in `Type (max u v)`, and the morphisms
inject into matrices over `K`.

Essential smallness is the hypothesis of the split Grothendieck group `TauCeti.SplitK0`, whose
elements are the virtual finite-dimensional representations of `L`.

## Main results

* `TauCeti.FGLieModuleCat.essentiallySmall`: finite-dimensional Lie modules form an essentially
  small category.
-/

public section

open CategoryTheory Module

universe w u v

namespace TauCeti

namespace FGLieModuleCat

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]

/-- The dimension and the matrices of the action in the standard basis of a finite-dimensional Lie
module: a complete invariant of its isomorphism class. -/
private noncomputable def actionMatrices (M : FGLieModuleCat.{w} K L) :
    Σ n : ℕ, L → Matrix (Fin n) (Fin n) K :=
  ⟨Module.finrank K M.obj, fun x ↦
    LinearMap.toMatrix (Module.finBasis K M.obj) (Module.finBasis K M.obj)
      (LieModule.toEnd K L M.obj x)⟩

private theorem nonempty_iso_of_sigma_eq {M N : FGLieModuleCat.{w} K L} {n m : ℕ}
    (b : Basis (Fin n) K M.obj) (c : Basis (Fin m) K N.obj)
    (h : (⟨n, fun x ↦ LinearMap.toMatrix b b (LieModule.toEnd K L M.obj x)⟩ :
        Σ k : ℕ, L → Matrix (Fin k) (Fin k) K) =
      ⟨m, fun x ↦ LinearMap.toMatrix c c (LieModule.toEnd K L N.obj x)⟩) :
    Nonempty (M ≅ N) := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_of_toMatrix_eq b c fun x ↦ congrFun (eq_of_heq h) x
  exact ⟨e.toFGLieModuleCatIso⟩

private theorem nonempty_iso_of_actionMatrices_eq {M N : FGLieModuleCat.{w} K L}
    (h : actionMatrices M = actionMatrices N) : Nonempty (M ≅ N) :=
  nonempty_iso_of_sigma_eq _ _ h

/-- **Finite-dimensional Lie modules form an essentially small category**, in the universe
`max u v` of the field `K : Type u` and the Lie algebra `L : Type v`. -/
instance essentiallySmall : EssentiallySmall.{max u v} (FGLieModuleCat.{w} K L) := by
  refine (essentiallySmall_iff _).2 ⟨?_, ⟨fun M N ↦ ?_⟩⟩
  · refine small_of_injective
      (f := fun s : Skeleton (FGLieModuleCat.{w} K L) ↦ actionMatrices ((fromSkeleton _).obj s))
      fun s t hst ↦ ?_
    obtain ⟨e⟩ := nonempty_iso_of_actionMatrices_eq hst
    rw [← toSkeleton_fromSkeleton_obj s, ← toSkeleton_fromSkeleton_obj t]
    exact congr_toSkeleton_of_iso e
  · refine small_of_injective (f := fun f : M ⟶ N ↦
      LinearMap.toMatrix (Module.finBasis K M.obj) (Module.finBasis K N.obj)
        (f.hom.hom : M.obj →ₗ[K] N.obj))
      fun f g hfg ↦ hom_ext <| LieModuleHom.ext fun m ↦
        LinearMap.congr_fun ((LinearMap.toMatrix _ _).injective hfg) m

end FGLieModuleCat

end TauCeti
