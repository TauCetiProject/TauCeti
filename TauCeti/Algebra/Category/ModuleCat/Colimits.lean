/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Natural transformations out of modules are determined at the ring

Every `R`-module is the cokernel of a morphism between direct sums of copies of `R`. Hence a
natural transformation `α : F ⟶ G` between colimit-preserving functors out of `ModuleCat R` is an
isomorphism as soon as its component at `R` is: its components at direct sums of copies of `R`
are then isomorphisms, and so are its components at their cokernels.

This is the standard way of checking that a comparison map between two right exact
constructions on modules is invertible, for instance that the sheaf associated with a tensor
product of modules is the tensor product of the associated sheaves.

## Main declarations

* `TauCeti.ModuleCat.isIso_of_isIso_app_self`: a natural transformation between
  colimit-preserving functors out of `ModuleCat R` whose component at `R` is invertible is an
  isomorphism.
-/

public section

namespace TauCeti

open CategoryTheory Limits DirectSum

universe u v w

namespace ModuleCat

open _root_.ModuleCat

variable {R : Type u} [Ring R] {D : Type v} [Category.{w} D]

/-- A natural transformation between colimit-preserving functors out of `ModuleCat R` is an
isomorphism as soon as its component at `R` is. -/
theorem isIso_of_isIso_app_self {F G : ModuleCat.{u} R ⥤ D}
    [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G] (α : F ⟶ G)
    [IsIso (α.app (ModuleCat.of R R))] : IsIso α := by
  classical
  -- The component at a direct sum of copies of `R` is the induced map between coproducts.
  have hfree (ι : Type u) : IsIso (α.app (ModuleCat.of R (⨁ _ : ι, R))) := by
    have (j : Discrete ι) : IsIso ((Functor.whiskerLeft
        (Discrete.functor fun _ : ι ↦ ModuleCat.of R R) α).app j) :=
      inferInstanceAs (IsIso (α.app (ModuleCat.of R R)))
    have : IsIso (Functor.whiskerLeft (Discrete.functor fun _ : ι ↦ ModuleCat.of R R) α) :=
      NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit _ α _
      (coproductCoconeIsColimit fun _ : ι ↦ ModuleCat.of R R)
  have := preservesSmallestColimits_of_preservesColimits F
  have := preservesSmallestColimits_of_preservesColimits G
  have (M : ModuleCat.{u} R) : IsIso (α.app M) := by
    -- `M` is the cokernel of `f`, where `g` sends the basis vector at `m` to `m` and `f` sends
    -- the basis vector at an element of the kernel of `g` to that element.
    let g : ModuleCat.of R (⨁ _ : M, R) ⟶ M :=
      ofHom (toModule R M M fun m ↦ LinearMap.toSpanSingleton R M m)
    let f : ModuleCat.of R (⨁ _ : LinearMap.ker g.hom, R) ⟶ ModuleCat.of R (⨁ _ : M, R) :=
      ofHom (toModule R _ _ fun k ↦ LinearMap.toSpanSingleton R _ k.1)
    have hg (m : M) : g.hom (lof R M (fun _ ↦ R) m 1) = m := by simp [g]
    have hf (k : LinearMap.ker g.hom) : f.hom (lof R _ (fun _ ↦ R) k 1) = k := by simp [f]
    have hgf : g.hom ∘ₗ f.hom = 0 := linearMap_ext R fun k ↦ LinearMap.ext_ring (by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf]
      exact k.2)
    have hfg : Function.Exact f.hom g.hom := fun y ↦ ⟨fun hy ↦ ⟨_, hf ⟨y, hy⟩⟩, by
      rintro ⟨x, rfl⟩
      exact LinearMap.congr_fun hgf x⟩
    have hc := isColimitCokernelCofork f g hfg fun m ↦ ⟨_, hg m⟩
    have (j : WalkingParallelPair) :
        IsIso ((Functor.whiskerLeft (parallelPair f 0) α).app j) := by
      cases j <;> exact hfree _
    have : IsIso (Functor.whiskerLeft (parallelPair f 0) α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit _ α _ hc
  exact NatIso.isIso_of_isIso_app α

end ModuleCat

end TauCeti
