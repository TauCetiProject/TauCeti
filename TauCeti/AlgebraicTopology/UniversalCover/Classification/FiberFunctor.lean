/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction
public import TauCeti.CategoryTheory.Action.Tannaka

/-!
# The fundamental group is the automorphism group of the fibre functor

Let `X` be path connected, locally path connected and semilocally simply connected, and fix a
basepoint `x₀`. Sending a covering space of `X` to its fibre over `x₀` is a functor

  `TauCeti.CoveringSpace.fiberFunctor x₀ : CoveringSpace X ⥤ Type u`,

and this file identifies its automorphism group:

  `TauCeti.CoveringSpace.autFiberFunctorMulEquiv x₀ :`
  `  FundamentalGroup X x₀ ≃* Aut (fiberFunctor x₀)`.

A loop class acts on each fibre by monodromy, and `autFiberFunctorMulEquiv_hom_app_apply` records
that the automorphism attached to it is exactly that action.

This is the fibre-functor reading of the classification. The classification itself is already
available as an equivalence of categories with `π₁(X, x₀)`-sets, and the fibre functor is that
equivalence followed by the forgetful functor to types, so the identification is Tannaka duality
for `G`-sets, `TauCeti.autCompForgetActionMulEquiv`.

The statement is about *all* covering spaces of `X`, not just the finite ones, and this is what
makes it clean. On the finite covers `TauCeti.FiniteCoveringSpace.fiberFunctor` is a fibre functor
for a Galois category, and Mathlib's recognition interface there,
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`, asks for a *compact* topological group,
which a discrete `π₁(X, x₀)` is only when it is finite. Keeping all covers removes that
restriction.

## Main declarations

* `TauCeti.CoveringSpace.fiberFunctor`: the fibre over `x₀`, as a functor to types, with
  `fiberFunctor_obj` and `fiberFunctor_map` computing it.
* `TauCeti.CoveringSpace.autFiberFunctorMulEquiv`: **the fundamental group of `X` at `x₀` is the
  automorphism group of the fibre functor over `x₀`**, with
  `autFiberFunctorMulEquiv_hom_app_apply` computing the automorphism attached to a loop class.
* `TauCeti.CoveringSpace.endFiberFunctorMulEquiv`: the same for natural *endo*morphisms of the
  fibre functor, which are therefore all invertible.
* `TauCeti.CoveringSpace.existsUnique_monodromy_eq`: every natural automorphism of the fibre
  functor is monodromy along a unique loop class.
* `TauCeti.CoveringSpace.monodromy_eq_self_iff`: a loop class acting trivially on every fibre is
  trivial.

## References

* Hatcher, *Algebraic Topology*, Section 1.3, for the monodromy description of covers.
* Lenstra, *Galois theory for schemes*, Section 3, for the automorphism group of a fibre functor.
-/

-- Provenance: the Tau Ceti `UniversalCovers` roadmap, `README.md`, section "Stage 2: lifting
-- criterion and Galois correspondence", which asks for the classification of covers to be phrased
-- through `Mathlib/CategoryTheory/Galois` and its fibre-functor interface.

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}} (x₀ : X)

/-- The functor taking a covering space of `X` to its fibre over `x₀`.

It is the fibre-action functor followed by the forgetful functor from `π₁(X, x₀)`-sets to types,
and is `@[expose]`d so that its values hold by `rfl` in downstream modules. -/
@[expose] def fiberFunctor : CoveringSpace X ⥤ Type u :=
  fiberActionFunctor x₀ ⋙ Action.forget (Type u) (FundamentalGroup X x₀)

@[simp]
theorem fiberFunctor_obj (p : CoveringSpace X) :
    (fiberFunctor x₀).obj p = ↥(⇑p.proj ⁻¹' {x₀}) :=
  (rfl)

/-- A map of covering spaces acts on the fibre over the basepoint by restriction. -/
@[simp]
theorem fiberFunctor_map {p q : CoveringSpace X} (f : p ⟶ q) :
    (fiberFunctor x₀).map f =
      ↾(IsCoveringMap.fiberMap f.hom.left.hom (proj_hom_comp_hom_left_hom f) x₀) :=
  fiberActionFunctor_map_hom x₀ f

section Classification

variable [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The fundamental group of `X` at `x₀` is the monoid of natural endomorphisms of the fibre
functor over `x₀`. Since the fundamental group is a group, so is this endomorphism monoid: every
natural endomorphism of the fibre functor is invertible. -/
def endFiberFunctorMulEquiv : FundamentalGroup X x₀ ≃* End (fiberFunctor x₀) :=
  endCompForgetActionMulEquiv _ (fiberActionFunctor x₀)

variable {x₀}

/-- The natural endomorphism of the fibre functor attached to a loop class acts on each fibre by
monodromy along that loop. -/
@[simp]
theorem endFiberFunctorMulEquiv_app_apply (g : FundamentalGroup X x₀) (p : CoveringSpace X)
    (e : ⇑p.proj ⁻¹' {x₀}) :
    (endFiberFunctorMulEquiv x₀ g).app p e = p.isCoveringMap_proj.monodromy g e :=
  endCompForgetActionMulEquiv_app_apply (fiberActionFunctor x₀) g p e

variable (x₀)

/-- **The fundamental group of `X` at `x₀` is the automorphism group of the fibre functor over
`x₀`.**

A loop class is sent to the natural automorphism acting on every fibre by monodromy; that this is
a bijection onto all natural automorphisms is Tannaka duality for `π₁(X, x₀)`-sets, transported
along the classification of covering spaces by `π₁(X, x₀)`-sets. -/
def autFiberFunctorMulEquiv : FundamentalGroup X x₀ ≃* Aut (fiberFunctor x₀) :=
  autCompForgetActionMulEquiv _ (fiberActionFunctor x₀)

variable {x₀}

/-- The automorphism of the fibre functor attached to a loop class acts on each fibre by
monodromy along that loop. -/
@[simp]
theorem autFiberFunctorMulEquiv_hom_app_apply (g : FundamentalGroup X x₀) (p : CoveringSpace X)
    (e : ⇑p.proj ⁻¹' {x₀}) :
    (autFiberFunctorMulEquiv x₀ g).hom.app p e = p.isCoveringMap_proj.monodromy g e :=
  autCompForgetActionMulEquiv_hom_app_apply (fiberActionFunctor x₀) g p e

/-- Every natural automorphism of the fibre functor is monodromy along a unique loop class. -/
theorem existsUnique_monodromy_eq (η : Aut (fiberFunctor x₀)) :
    ∃! g : FundamentalGroup X x₀, ∀ (p : CoveringSpace X) (e : ⇑p.proj ⁻¹' {x₀}),
      p.isCoveringMap_proj.monodromy g e = η.hom.app p e := by
  refine ⟨(autFiberFunctorMulEquiv x₀).symm η, fun p e => ?_, fun g hg => ?_⟩
  · rw [← autFiberFunctorMulEquiv_hom_app_apply, MulEquiv.apply_symm_apply]
  · refine (autFiberFunctorMulEquiv x₀).injective (Aut.ext (NatTrans.ext (funext fun p => ?_)))
    ext e
    rw [MulEquiv.apply_symm_apply]
    exact (autFiberFunctorMulEquiv_hom_app_apply g p e).trans (hg p e)

/-- A loop class acting trivially by monodromy on the fibre of *every* covering space of `X` is
trivial. This is the faithfulness condition that
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup` calls `non_trivial'`. -/
theorem monodromy_eq_self_iff (g : FundamentalGroup X x₀) :
    (∀ (p : CoveringSpace X) (e : ⇑p.proj ⁻¹' {x₀}), p.isCoveringMap_proj.monodromy g e = e) ↔
      g = 1 := by
  refine ⟨fun hg => ?_, fun hg p e => ?_⟩
  · rw [← (autFiberFunctorMulEquiv x₀).map_eq_one_iff]
    refine Aut.ext (NatTrans.ext (funext fun p => ?_))
    ext e
    exact (autFiberFunctorMulEquiv_hom_app_apply g p e).trans (hg p e)
  · subst hg
    exact one_smul (FundamentalGroup X x₀) (show ToType ((fiberActionFunctor x₀).obj p) from e)

end Classification

end TauCeti.CoveringSpace
