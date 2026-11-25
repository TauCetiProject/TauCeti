/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Module.Generator
public import TauCeti.CategoryTheory.Generator.GeneratorCogenerator
-- Private: the comparison of separators with generators in `ModuleCat R`, and the regular module
-- as a projective object of `FGModuleCat R`, and finite intersections in Artinian modules.
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.Generator
import TauCeti.RingTheory.Artinian.Module

/-!
# Separators of finitely generated modules

A finitely generated module `M` is a separator of `mod R = FGModuleCat R` exactly when it is a
separator of the whole module category `ModuleCat R`
(`FGModuleCat.isSeparator_iff_isSeparator_obj`). A separator of `ModuleCat R` lying in `mod R` is
one of `mod R` because the inclusion is fully faithful. Conversely, a morphism of modules `f` killed
by every morphism out of `M` restricts, on each cyclic submodule `R ∙ x`, to a morphism of `mod R`
onto `f (R ∙ x)`; morphisms out of `M` into `R ∙ x` kill this restriction, so it vanishes and
`f x = 0`. No Noetherian hypothesis is needed, since cyclic modules and their images are finitely
generated.

So the description of the separators of `ModuleCat R` as the generators in the sense of
`TauCeti.Module.IsGenerator` (`ModuleCat.isSeparator_iff_isGenerator`) carries over to `mod R`
(`FGModuleCat.isSeparator_iff_isGenerator`), in any universe of modules in which `R` is small; a
generator is a separator in every universe (`FGModuleCat.isSeparator_of_isGenerator`). In
particular the regular module is a separator of `mod R`, the analogue of Mathlib's
`ModuleCat.isSeparator`.

Over any ring `R`, `M` is also a separator of `mod R` exactly when `R` is a direct summand of a
finite sum `Mⁿ`, that is, `R ∈ add M` (`FGModuleCat.isSeparator_iff_exists_retract`). One direction
holds in any preadditive category with finite biproducts: a separator in `add M` makes `M` a
separator. For the other, a generator `M` maps onto every finitely generated module from a finite
power `Mⁿ` (`TauCeti.Module.IsGenerator.exists_surjective_of_finite`), and such a surjection onto a
projective object of `mod R`, such as `R`, splits.

## Main results

* `FGModuleCat.isSeparator_iff_isSeparator_obj`: the separators of `mod R` are the finitely
  generated separators of `ModuleCat R`.
* `FGModuleCat.isSeparator_iff_isGenerator`: the separators of `mod R` are the generators of the
  module category.
* `FGModuleCat.isSeparator_of_isGenerator`: a generator is a separator, in any universe.
* `FGModuleCat.isSeparator`: the regular module is a separator of `FGModuleCat R`.
* `FGModuleCat.additiveClosure_of_isGenerator_of_projective`: a finitely generated projective
  module lies in the additive closure `add M` of every finitely generated generator `M`, in any
  universe.
* `FGModuleCat.isCoseparator_iff`: `M` is a coseparator of `mod R` exactly when linear maps into
  `M` separate the points of every finitely generated module.
* `CategoryTheory.IsCoseparator.additiveClosure_of_injective`: dually, an injective object of
  `mod R` that is Artinian as a module lies in `add M` for every coseparator `M`.
* `FGModuleCat.isSeparator_iff_additiveClosure` and `FGModuleCat.isSeparator_iff_exists_retract`:
  `M` is a separator of `mod R` exactly when `R ∈ add M`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R]

/-- **Separators of `mod R` are separators of `Mod R`**: a finitely generated module is a separator
of `FGModuleCat R` exactly when it is a separator of `ModuleCat R`. One direction holds since the
inclusion is fully faithful. Conversely, a morphism of modules killed by every morphism out of `M`
restricts, on each cyclic submodule `R ∙ x`, to a morphism of `mod R` onto its image with the same
property; that restriction vanishes, so the morphism vanishes at `x`. -/
theorem _root_.FGModuleCat.isSeparator_iff_isSeparator_obj (M : FGModuleCat.{v} R) :
    IsSeparator M ↔ IsSeparator M.obj := by
  refine ⟨fun hM ↦ (Preadditive.isSeparator_iff _).2 fun X Y f hf ↦ ModuleCat.hom_ext <|
      LinearMap.ext fun x ↦ ?_, (·.of_fullyFaithful (ObjectProperty.fullyFaithfulι _))⟩
  -- The restriction of `f` to `R ∙ x`, a morphism between finitely generated modules.
  let f' : FGModuleCat.of R (R ∙ x) ⟶ FGModuleCat.of R ((R ∙ x).map f.hom) :=
    FGModuleCat.ofHom (f.hom.submoduleMap _)
  have hf' : f' = 0 := (Preadditive.isSeparator_iff _).1 hM f' fun g ↦ by
    ext y
    simpa [f'] using congr(($(hf (g.hom ≫ ModuleCat.ofHom (R ∙ x).subtype))).hom y)
  simpa [f'] using congr((($hf').hom.hom ⟨x, Submodule.mem_span_singleton_self x⟩ : Y))

/-- **A generator of the module category is a separator of `mod R`**, in any universe of modules.
-/
theorem _root_.FGModuleCat.isSeparator_of_isGenerator (M : FGModuleCat.{v} R)
    [Module.IsGenerator R M] : IsSeparator M :=
  (FGModuleCat.isSeparator_iff_isSeparator_obj M).2 (ModuleCat.isSeparator_of_isGenerator M.obj)

/-- **A separator of `mod R` is a generator of the module category**. The modules may live in any
universe in which `R` is small. -/
theorem _root_.FGModuleCat.isGenerator_of_isSeparator [Small.{v} R] {M : FGModuleCat.{v} R}
    (hM : IsSeparator M) : Module.IsGenerator R M :=
  ModuleCat.isGenerator_of_isSeparator ((FGModuleCat.isSeparator_iff_isSeparator_obj M).1 hM)

/-- **The separators of `mod R` are the generators of the module category**, in any universe of
modules in which `R` is small. -/
theorem _root_.FGModuleCat.isSeparator_iff_isGenerator [Small.{v} R] (M : FGModuleCat.{v} R) :
    IsSeparator M ↔ Module.IsGenerator R M :=
  (FGModuleCat.isSeparator_iff_isSeparator_obj M).trans (ModuleCat.isSeparator_iff_isGenerator _)

variable (R) in
/-- The regular module is a separator of the finitely generated modules, the analogue of Mathlib's
`ModuleCat.isSeparator`: a morphism vanishes when its composite with every morphism out of the
regular module does. -/
theorem _root_.FGModuleCat.isSeparator : IsSeparator (FGModuleCat.of R R) :=
  FGModuleCat.isSeparator_of_isGenerator _

/-- **Finitely generated projective modules are summands of finite sums of a generator**: if `M`
is a generator of the module category, then a projective object of `FGModuleCat R` lies in `add M`.
The modules may live in any universe. -/
theorem _root_.FGModuleCat.additiveClosure_of_isGenerator_of_projective (M P : FGModuleCat.{v} R)
    [Module.IsGenerator R M] [Projective P] : additiveClosure M P := by
  -- A surjection `Mⁿ → P` gives an epimorphism from a finite sum of copies of `M`, which splits
  -- since `P` is projective.
  obtain ⟨n, f, hf⟩ := Module.IsGenerator.exists_surjective_of_finite (R := R) (M := M) P
  let p : (⨁ fun _ : Fin n ↦ M) ⟶ P := biproduct.desc fun i ↦
    ObjectProperty.homMk (ModuleCat.ofHom (f ∘ₗ LinearMap.single R (fun _ ↦ M) i))
  have : Epi p := Preadditive.epi_of_cancel_zero p fun {Z} g hg ↦ by
    refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext ((LinearMap.cancel_right hf).1 ?_))
    refine LinearMap.pi_ext' fun i ↦ ?_
    simpa [p, LinearMap.comp_assoc] using congr((biproduct.ι _ i ≫ $hg).hom.hom)
  exact (additiveClosure M).prop_of_retract ⟨Projective.factorThru (𝟙 P) p, p, by simp⟩
    ((additiveClosure M).prop_of_isLimit (biproduct.isLimit _) fun _ ↦ additiveClosure_self M)

/-- **The coseparators of `mod R`, elementwise**: `M` is a coseparator of `mod R` exactly when
every nonzero element of every finitely generated module `X` is sent to a nonzero element by some
linear map `X → M`. -/
theorem _root_.FGModuleCat.isCoseparator_iff (M : FGModuleCat.{v} R) :
    IsCoseparator M ↔
      ∀ (X : FGModuleCat.{v} R) (x : X.obj), x ≠ 0 → ∃ f : X.obj →ₗ[R] M.obj, f x ≠ 0 := by
  refine ⟨fun hM X x hx0 ↦ ?_, fun h ↦ (Preadditive.isCoseparator_iff M).2 fun {X Y} f hf ↦ ?_⟩
  · -- Test on the inclusion of the cyclic submodule `R ∙ x`, which every map to `M` kills.
    by_contra! hx
    exact hx0 <| (X.span_singleton_subtype_eq_zero_iff x).1 <|
      (Preadditive.isCoseparator_iff M).1 hM _ fun g ↦
        (X.span_singleton_subtype_comp_eq_zero_iff x g).2 (hx g.hom.hom)
  · refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
    by_contra hx
    obtain ⟨g, hg⟩ := h Y (f.hom.hom x) (by simpa using hx)
    have hfg := hf (ObjectProperty.homMk (ModuleCat.ofHom g))
    exact hg (by simpa using congr(($hfg).hom.hom x))

/-- **Artinian injective modules are summands of finite sums of a coseparator**: if `M` is a
coseparator of `mod R`, then an injective object of `mod R` that is Artinian as a module lies in
`add M`. This is dual to `FGModuleCat.additiveClosure_of_isGenerator_of_projective`. The modules
may live in any universe. -/
theorem _root_.CategoryTheory.IsCoseparator.additiveClosure_of_injective {M : FGModuleCat.{v} R}
    (hM : IsCoseparator M) (I : FGModuleCat.{v} R) [Injective I] [IsArtinian R I.obj] :
    additiveClosure M I := by
  -- As `I` is Artinian, it embeds into a finite power `Mⁿ`, and the embedding splits.
  obtain ⟨n, g, hg⟩ :=
    IsArtinian.exists_injective_linearMap_pi ((FGModuleCat.isCoseparator_iff M).1 hM I)
  let ι : I ⟶ ⨁ fun _ : Fin n ↦ M :=
    biproduct.lift fun j ↦ ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj j ∘ₗ g))
  -- The `j`-th coordinate of `ι` is `proj j ∘ g`, so `ι` is injective because `g` is.
  have : Mono ι := ConcreteCategory.mono_of_injective ι fun x y hxy ↦ hg <| funext fun j ↦ by
    have hπ : ι ≫ biproduct.π _ j =
        ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj j ∘ₗ g)) := biproduct.lift_π _ j
    have h := congrArg (ConcreteCategory.hom (biproduct.π (fun _ : Fin n ↦ M) j)) hxy
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hπ] at h
    exact h
  exact (additiveClosure M).prop_of_retract ⟨ι, Injective.factorThru (𝟙 I) ι, by simp⟩
    ((additiveClosure M).prop_of_isLimit (biproduct.isLimit _) fun _ ↦ additiveClosure_self M)

/-- **The regular module lies in the additive closure of a generator**: if `M` is a generator of
the module category, then the regular module lies in `add M`. -/
theorem _root_.FGModuleCat.additiveClosure_of_isGenerator (M : FGModuleCat.{u} R)
    [Module.IsGenerator R M] : additiveClosure M (FGModuleCat.of R R) :=
  have := FGModuleCat.projective_of_free R (FGModuleCat.of R R)
  FGModuleCat.additiveClosure_of_isGenerator_of_projective M _

/-- **The separators of `mod R`, through additive closures**: `M` is a separator of `mod R` exactly
when the regular module lies in `add M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_additiveClosure (M : FGModuleCat.{u} R) :
    IsSeparator M ↔ additiveClosure M (FGModuleCat.of R R) :=
  ⟨fun h ↦ have := FGModuleCat.isGenerator_of_isSeparator h
    FGModuleCat.additiveClosure_of_isGenerator M,
    (FGModuleCat.isSeparator R).of_additiveClosure⟩

/-- Over any ring `R`, `M` is a separator of `mod R` exactly when the regular module is a direct
summand of a finite biproduct of copies of `M`, that is, `R ∈ add M`. -/
theorem _root_.FGModuleCat.isSeparator_iff_exists_retract (M : FGModuleCat.{u} R) :
    IsSeparator M ↔ ∃ n : ℕ, Nonempty (Retract (FGModuleCat.of R R) (⨁ fun _ : Fin n ↦ M)) :=
  (FGModuleCat.isSeparator_iff_additiveClosure M).trans additiveClosure_iff

end TauCeti
