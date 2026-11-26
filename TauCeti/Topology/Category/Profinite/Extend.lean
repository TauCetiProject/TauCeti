/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.Profinite.Extend

/-!
# Common refinements of maps from a profinite set to finite sets

Limits over `StructuredArrow S FintypeCat.toProfinite`, the category of maps from a profinite set
`S` to finite sets, are computed by comparing maps through a common refinement. This file shows
that any two such maps factor through a common surjection onto a finite set
(`Profinite.exists_structuredArrow_surjective_refinement`); the surjection is the projection of
`S` onto a discrete quotient, as an object `(Profinite.Extend.functor S.asLimitCone).obj Q`.
Every locally constant function on `S` is pulled back along such a map
(`Profinite.liftOfDiscreteQuotient`, `Profinite.comap_liftOfDiscreteQuotient`,
`Profinite.exists_structuredArrow_comap_eq`), finitely many of them along a common surjection
(`Profinite.exists_structuredArrow_surjective_forall_comap_eq`), and pulling back is compatible
with morphisms of `StructuredArrow S FintypeCat.toProfinite`
(`Profinite.comap_comap_of_structuredArrow_hom`).
-/

public section

universe u

open CategoryTheory

namespace Profinite

/-- Any two maps from a profinite set `S` to finite sets factor through a common surjection from
`S` onto a finite set. -/
theorem exists_structuredArrow_surjective_refinement (S : Profinite.{u})
    (j₁ j₂ : StructuredArrow S FintypeCat.toProfinite) :
    ∃ (j : StructuredArrow S FintypeCat.toProfinite) (_ : j ⟶ j₁) (_ : j ⟶ j₂),
      Function.Surjective j.hom := by
  have := FintypeCat.discreteTopology j₁.right
  have := FintypeCat.discreteTopology j₂.right
  let f : LocallyConstant S
      (FintypeCat.toProfinite.obj j₁.right × FintypeCat.toProfinite.obj j₂.right) :=
    ⟨fun x ↦ (j₁.hom x, j₂.hom x),
      ((IsLocallyConstant.iff_continuous _).mpr j₁.hom.hom.hom.continuous).prodMk
        ((IsLocallyConstant.iff_continuous _).mpr j₂.hom.hom.hom.continuous)⟩
  refine ⟨(Extend.functor S.asLimitCone).obj f.discreteQuotient,
    StructuredArrow.homMk (FintypeCat.homMk fun q ↦ (f.lift q).1) ?_,
    StructuredArrow.homMk (FintypeCat.homMk fun q ↦ (f.lift q).2) ?_,
    f.discreteQuotient.proj_surjective⟩
  -- The object of `Extend.functor` at `Q` is the projection `S → Q`, and
  -- `FintypeCat.toProfinite.map (FintypeCat.homMk g)` applies `g`, both by definition; so both
  -- triangles reduce to `f.lift ∘ f.discreteQuotient.proj = f`.
  · ext x
    exact congrArg Prod.fst (congrFun f.lift_comp_proj x)
  · ext x
    exact congrArg Prod.snd (congrFun f.lift_comp_proj x)


/-- A locally constant function on a profinite set `S`, as a function on its discrete quotient by
fibres, the target of the object `(Extend.functor S.asLimitCone).obj f.discreteQuotient`. -/
noncomputable def liftOfDiscreteQuotient (S : Profinite.{u}) {Z : Type*} (f : LocallyConstant S Z) :
    LocallyConstant (FintypeCat.toProfinite.obj
      ((Extend.functor S.asLimitCone).obj f.discreteQuotient).right) Z :=
  ⟨(f.lift : _ → Z), IsLocallyConstant.of_discrete _⟩

theorem comap_liftOfDiscreteQuotient (S : Profinite.{u}) {Z : Type*} (f : LocallyConstant S Z) :
    LocallyConstant.comap ((Extend.functor S.asLimitCone).obj f.discreteQuotient).hom.hom.hom
      (S.liftOfDiscreteQuotient f) = f :=
  -- The object of `Extend.functor` at `Q` is the projection `S → Q` by definition, so this is
  -- `f.lift ∘ f.discreteQuotient.proj = f`.
  LocallyConstant.coe_injective f.lift_comp_proj

/-- Every locally constant function on a profinite set `S` is pulled back from a finite set. -/
theorem exists_structuredArrow_comap_eq (S : Profinite.{u}) {Z : Type*}
    (f : LocallyConstant S Z) :
    ∃ (j : StructuredArrow S FintypeCat.toProfinite)
      (φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) Z),
      LocallyConstant.comap j.hom.hom.hom φ = f :=
  ⟨_, _, S.comap_liftOfDiscreteQuotient f⟩

/-- Finitely many locally constant functions on a profinite set `S` are pulled back along a common
surjection from `S` onto a finite set. -/
theorem exists_structuredArrow_surjective_forall_comap_eq (S : Profinite.{u}) {Z : Type*}
    (s : Finset (LocallyConstant S Z)) :
    ∃ j : StructuredArrow S FintypeCat.toProfinite, Function.Surjective j.hom ∧
      ∀ f ∈ s, ∃ φ : LocallyConstant (FintypeCat.toProfinite.obj j.right) Z,
        LocallyConstant.comap j.hom.hom.hom φ = f := by
  let F : LocallyConstant S (s → Z) := LocallyConstant.unflip fun f ↦ f.val
  refine ⟨(Extend.functor S.asLimitCone).obj F.discreteQuotient, F.discreteQuotient.proj_surjective,
    fun f hf ↦ ⟨(S.liftOfDiscreteQuotient F).map (· ⟨f, hf⟩), ?_⟩⟩
  ext x
  exact congrFun (LocallyConstant.congr_fun (S.comap_liftOfDiscreteQuotient F) x) ⟨f, hf⟩

/-- Pulling back along a morphism `k : j ⟶ j'` of maps from `S` to finite sets and then along `j`
is pulling back along `j'`. -/
theorem comap_comap_of_structuredArrow_hom {S : Profinite.{u}}
    {j j' : StructuredArrow S FintypeCat.toProfinite} (k : j ⟶ j') {Z : Type*}
    (φ : LocallyConstant (FintypeCat.toProfinite.obj j'.right) Z) :
    LocallyConstant.comap j.hom.hom.hom
        (LocallyConstant.comap (FintypeCat.toProfinite.map k.right).hom.hom φ) =
      LocallyConstant.comap j'.hom.hom.hom φ := by
  ext x
  exact congrArg φ (congrArg (fun f ↦ f.hom.hom x) (StructuredArrow.w k))

end Profinite
