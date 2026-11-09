/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.OneLoop.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Polynomial modules of one-loop representations

A representation of the one-loop quiver is a vector space with an endomorphism.
Letting `X` act by that endomorphism gives a polynomial module. The resulting
functor is fully faithful: its morphisms are exactly the linear maps commuting
with the loop. This allows module structure theorems over `k[X]` to be applied to
loop representations without changing their morphisms or decompositions.

The construction uses Mathlib's `Module.AEval'` and `LinearMap.ofAEval`.

## References

* P. Etingof et al., *Introduction to Representation Theory*, Section 2.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory Polynomial

universe u v

variable {k : Type u} [Field k]

/-- The polynomial module of a loop representation: `X` acts by the loop. -/
abbrev oneLoopModule (M : QuiverRep.{u, 0, 0, v} k Quiver.OneLoop) :=
  Module.AEval' (M.map Quiver.OneLoop.loop.toPath).hom

/-- Regard a one-loop representation as a polynomial module. -/
-- Expose the functor so its object carrier reduces to oneLoopModule M in
-- element-level statements. A sealed object assignment would require transports.
@[expose]
noncomputable def oneLoopPolynomialFunctor :
    QuiverRep.{u, 0, 0, v} k Quiver.OneLoop ⥤ ModuleCat.{v} k[X] where
  obj M := ModuleCat.of k[X] (oneLoopModule M)
  map {M N} f := ModuleCat.ofHom <|
    LinearMap.ofAEval (M.map Quiver.OneLoop.loop.toPath).hom
      ((Module.AEval'.of (N.map Quiver.OneLoop.loop.toPath).hom).toLinearMap.comp
        (f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom) fun x ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.smul_def]
      rw [Module.AEval'.X_smul_of]
      exact congrArg (Module.AEval'.of _) (NatTrans.naturality_apply f _ x)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The functor acts on morphisms by the component at the unique vertex. -/
@[simp]
theorem oneLoopPolynomialFunctor_map_apply
    {M N : QuiverRep.{u, 0, 0, v} k Quiver.OneLoop} (f : M ⟶ N)
    (x : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)) :
    (oneLoopPolynomialFunctor.map f).hom
        (Module.AEval'.of (M.map Quiver.OneLoop.loop.toPath).hom x) =
      Module.AEval'.of (N.map Quiver.OneLoop.loop.toPath).hom
        ((f.app (Quiver.OneLoop.vertex : Paths Quiver.OneLoop)).hom x) := (rfl)

instance : (oneLoopPolynomialFunctor.{u, v} (k := k)).Faithful where
  map_injective {M N} f g h := by
    apply NatTrans.ext
    funext a
    cases a
    apply ModuleCat.hom_ext
    ext x
    exact (Module.AEval'.of (N.map Quiver.OneLoop.loop.toPath).hom).injective
      (congrArg (fun h ↦ h.hom
        (Module.AEval'.of (M.map Quiver.OneLoop.loop.toPath).hom x)) h)

instance : (oneLoopPolynomialFunctor.{u, v} (k := k)).Full where
  map_surjective {M N} f := by
    -- Name the polynomial carriers before restricting scalars to use their
    -- inherited k-module structures.
    let f' : oneLoopModule M →ₗ[k[X]] oneLoopModule N := f.hom
    let g : M.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) →ₗ[k]
        N.obj (Quiver.OneLoop.vertex : Paths Quiver.OneLoop) :=
      (Module.AEval'.of (N.map Quiver.OneLoop.loop.toPath).hom).symm.toLinearMap.comp
        ((f'.restrictScalars k).comp
          (Module.AEval'.of (M.map Quiver.OneLoop.loop.toPath).hom).toLinearMap)
    let h : M ⟶ N := Paths.liftNatTrans (fun a ↦ by
      cases a
      exact ModuleCat.ofHom g) fun {a b} e ↦ by
        cases a
        cases b
        rw [Subsingleton.elim e Quiver.OneLoop.loop]
        apply ModuleCat.hom_ext
        ext x
        apply (Module.AEval'.of (N.map Quiver.OneLoop.loop.toPath).hom).injective
        simp [g, ← Module.AEval'.X_smul_of]
    refine ⟨h, ?_⟩
    ext x
    -- At the unique vertex, liftNatTrans selects g, and AEval'.of and its inverse
    -- are identity maps on the underlying carrier, so the two transports cancel.
    rfl

end TauCeti.QuiverRep
