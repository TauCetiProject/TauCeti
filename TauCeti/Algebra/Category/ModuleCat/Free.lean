/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.LinearAlgebra.FreeModule.Filtration
public import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Freeness of sequential colimits of modules

Let `F₀ → F₁ → F₂ → ⋯` be a sequence of modules whose transition maps `φⱼ : Fⱼ → Fⱼ₊₁` are
injective. Its colimit `M` is then the increasing union of the images of the `Fⱼ`, each leg
`Fⱼ → M` being injective (`ModuleCat.injective_ι_app_of_isColimit`). If moreover `F₀` and every
cokernel `Fⱼ₊₁ ⧸ φⱼ(Fⱼ)` are free, then `M` is free
(`ModuleCat.free_of_isColimit_of_injective`): the images of the `Fⱼ` form an exhaustive
filtration of `M` whose subquotients are `F₀` and these cokernels, so
`Module.Free.of_filtration` applies.

Over a principal ideal ring without zero divisors it suffices that each `φⱼ` is followed by a map
into a projective module in an exact sequence `Fⱼ → Fⱼ₊₁ → Qⱼ`
(`ModuleCat.free_of_isColimit_of_exact`), since a module embedding in a projective module is then
free.

This is how freeness passes to the homology of a space exhausted by an increasing sequence of
subspaces, when the homology of each subspace injects into that of the next one, followed by the
free relative homology of the pair; for instance to the top-degree homology of a manifold filtered
by the sublevels of a proper Morse function. No finiteness is assumed, so the colimit may have
infinite rank.

## Main results

* `ModuleCat.injective_ι_app_of_isColimit`: the legs of the colimit of a sequence of injections
  are injective.
* `ModuleCat.free_of_isColimit_of_injective`: a sequential colimit of injections with free first
  term and free cokernels is free.
* `ModuleCat.free_of_isColimit_of_exact`: the version over a principal ideal ring, with cokernels
  embedded in projective modules.
-/

public section

namespace ModuleCat

open CategoryTheory Limits

universe u

variable {R : Type u} [Ring R] {F : ℕ ⥤ ModuleCat.{u} R} {c : Cocone F}

/-- The legs of a colimit cocone over a sequence of modules with injective transition maps are
injective. -/
theorem injective_ι_app_of_isColimit (hc : IsColimit c)
    (hF : ∀ j, Function.Injective (F.map (homOfLE (Nat.le_succ j))).hom) (j : ℕ) :
    Function.Injective (c.ι.app j).hom := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  -- Every transition map is a composite of the successive ones.
  have hmap {i k : ℕ} (hik : i ≤ k) : Function.Injective (F.map (homOfLE hik)).hom := by
    induction k, hik using Nat.le_induction with
    | base => simpa [homOfLE_refl] using Function.injective_id
    | succ k hik ih =>
      rw [← homOfLE_comp hik (Nat.le_succ k), F.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp]
      exact (hF k).comp ih
  intro x y hxy
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc x y hxy
  obtain rfl : g = f := Subsingleton.elim _ _
  exact hmap (leOfHom g) hfg

/-- **A sequential colimit of free modules with free cokernels is free.** Let `F₀ → F₁ → ⋯` be a
sequence of modules with injective transition maps `φⱼ`, such that `F₀` and every cokernel
`Fⱼ₊₁ ⧸ φⱼ(Fⱼ)` are free. Then the colimit of the sequence is free. -/
theorem free_of_isColimit_of_injective (hc : IsColimit c) [Module.Free R (F.obj 0)]
    (hF : ∀ j, Function.Injective (F.map (homOfLE (Nat.le_succ j))).hom)
    (hfree : ∀ j, Module.Free R
      (F.obj (j + 1) ⧸ LinearMap.range (F.map (homOfLE (Nat.le_succ j))).hom)) :
    Module.Free R c.pt := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hι := injective_ι_app_of_isColimit hc hF
  have hw (j : ℕ) (x : F.obj j) :
      (c.ι.app (j + 1)).hom ((F.map (homOfLE (Nat.le_succ j))).hom x) = (c.ι.app j).hom x :=
    ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_succ j))) x
  -- The filtration of the colimit by the images of the legs, starting from `0`.
  let N : ℕ → Submodule R c.pt
    | 0 => ⊥
    | j + 1 => LinearMap.range (c.ι.app j).hom
  refine Module.Free.of_filtration N (monotone_nat_of_le_succ fun j ↦ ?_) rfl
    (eq_top_iff.2 fun x _ ↦ ?_) fun j ↦ ?_
  · cases j with
    | zero => exact bot_le
    | succ j =>
      rintro _ ⟨x, rfl⟩
      exact ⟨_, hw j x⟩
  · obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    exact Submodule.mem_iSup_of_mem (j + 1) (LinearMap.mem_range_self _ y)
  · cases j with
    | zero =>
      -- The first subquotient is the image of `F₀`.
      have h : (N 0).submoduleOf (N 1) = ⊥ := by simp [N, Submodule.submoduleOf]
      exact .of_equiv ((LinearEquiv.ofInjective _ (hι 0)).trans
        (Submodule.quotEquivOfEqBot _ h).symm)
    | succ j =>
      -- The later subquotients are the cokernels of the transition maps.
      have := hfree j
      let e := LinearEquiv.ofInjective _ (hι (j + 1))
      refine .of_equiv (Submodule.Quotient.equiv
        (LinearMap.range (F.map (homOfLE (Nat.le_succ j))).hom)
        ((N (j + 1)).submoduleOf (N (j + 2))) e ?_)
      ext ⟨y, x, rfl⟩
      simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.submoduleOf,
        Submodule.mem_comap, Submodule.subtype_apply, N]
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, hz⟩
        exact ⟨z, (hw j z).symm.trans
          ((LinearEquiv.ofInjective_apply _ _).symm.trans (congrArg Subtype.val hz))⟩
      · rintro ⟨z, hz⟩
        refine ⟨_, ⟨z, rfl⟩, Subtype.ext ?_⟩
        exact (LinearEquiv.ofInjective_apply _ _).trans ((hw j z).trans hz)

/-- **A sequential colimit of free modules over a principal ideal ring is free** as soon as every
transition map `φⱼ : Fⱼ → Fⱼ₊₁` is injective and is followed, in an exact sequence
`Fⱼ → Fⱼ₊₁ → Qⱼ`, by a map into a projective module `Qⱼ`, and `F₀` is free. The cokernel of `φⱼ`
then embeds in `Qⱼ`, hence is free. This is the shape in which the long exact sequences of pairs
supply the hypotheses. -/
theorem free_of_isColimit_of_exact {R : Type u} [CommRing R] [NoZeroDivisors R]
    [IsPrincipalIdealRing R] {F : ℕ ⥤ ModuleCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    [Module.Free R (F.obj 0)]
    (hF : ∀ j, Function.Injective (F.map (homOfLE (Nat.le_succ j))).hom)
    {Q : ℕ → Type*} [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]
    [∀ j, Module.Projective R (Q j)] (g : ∀ j, F.obj (j + 1) →ₗ[R] Q j)
    (hg : ∀ j, Function.Exact (F.map (homOfLE (Nat.le_succ j))).hom (g j)) :
    Module.Free R c.pt :=
  free_of_isColimit_of_injective hc hF fun j ↦
    -- The cokernel of the transition map is the coimage of `g j`.
    let e := (Submodule.quotEquivOfEq _ _ (hg j).linearMap_ker_eq.symm).trans
      (g j).quotKerEquivRange
    .of_injective_of_projective_of_isPrincipalIdealRing ((LinearMap.range (g j)).subtype ∘ₗ e)
      ((LinearMap.range (g j)).injective_subtype.comp e.injective)

end ModuleCat
