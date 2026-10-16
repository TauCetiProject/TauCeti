/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The exact sequence of a closed subscheme

Let `I ⊆ 𝒪_X` be an ideal sheaf on a scheme `X`, cutting out the closed subscheme
`ι : V(I) ⟶ X`. Restricting regular functions to `V(I)` is the morphism of `𝒪_X`-modules
`𝒪_X ⟶ ι_* 𝒪_{V(I)}`, whose kernel is `I` by definition of the sections of `I`. It is an
epimorphism because on every affine open `U` the restriction `Γ(X, U) ⟶ Γ(V(I), U ∩ V(I))` is the
quotient map by `I(U)`. This gives the short exact sequence of `𝒪_X`-modules

  `0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0`,

through which the cohomology of `I` is compared with the cohomology of `𝒪_X` and of the closed
subscheme `V(I)`.

## Main declarations

* `Scheme.IdealSheafData.shortExact_toPushforwardSubscheme`: the sequence
  `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}` is short exact.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.5: the ideal sheaf `𝓘_Y` of a closed subscheme
  `Y` is the kernel of `𝒪_X ⟶ i_* 𝒪_Y`, which is surjective (Proposition II.5.9).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A section of `𝒪_X` restricts to zero on `V(I)` exactly when it is a section of `I`, stated
in the sections of `ι_* 𝒪_{V(I)}`, whose zero is not reducibly the zero of
`Γ(V(I), ι⁻¹ U)`. -/
@[simp]
lemma subschemeι_app_eq_zero_iff {U : X.Opens} {s : Γ(X, U)} :
    -- The target is pinned to `Scheme.Modules.pushforward`, as in `sheafι_toPushforwardSubscheme`
    -- below. `simp` does not identify these sections with those of the defeq target
    -- `SheafOfModules.pushforward` that Mathlib gives `unitToPushforwardObjUnit`.
    Scheme.Modules.Hom.app
        (N := (Scheme.Modules.pushforward I.subschemeι).obj
          (SheafOfModules.unit I.subscheme.ringCatSheaf))
        (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) U s = 0 ↔
      s ∈ I.sections U :=
  I.mem_sections_iff.symm

/-- Regular functions in `I` vanish on `V(I)`. -/
@[simp, reassoc]
lemma sheafι_toPushforwardSubscheme :
    -- The target is pinned to `Scheme.Modules.pushforward`: at Mathlib's
    -- `SheafOfModules.pushforward` target no zero morphism is synthesized for `0`.
    (I.sheafι ≫ SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom :
      I.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  -- The components of a composite and of the zero morphism are computed sectionwise
  -- (`Scheme.Modules.Hom.comp_app` and `Scheme.Modules.Hom.zero_app` hold by `rfl`). Neither
  -- `rw` nor `simp` can apply `comp_app` here: the goal is ill-typed at `implicit` transparency,
  -- where the ring sheaf of `V(I)` is a `TopCat.Sheaf` rather than a sheaf on the site.
  exact (I.subschemeι_app_eq_zero_iff).mpr (I.sheafι_app_mem U t)

/-- `I` is the kernel of the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}`. -/
def isLimitKernelForkSheafι :
    IsLimit (KernelFork.ofι I.sheafι I.sheafι_toPushforwardSubscheme) :=
  KernelFork.IsLimit.ofι _ _
    -- The components of a composite, and of the zero morphism, are computed sectionwise.
    (fun φ hφ ↦ I.sheafLift φ fun U s ↦
      (I.subschemeι_app_eq_zero_iff).mp
        (ConcreteCategory.congr_hom (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) hφ) s))
    (fun φ hφ ↦ I.sheafLift_ι _ _)
    (fun φ hφ m hm ↦ by
      rw [← cancel_mono I.sheafι, sheafLift_ι]
      exact hm)

/-- The restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` is an epimorphism: on an affine open it is the
quotient map `Γ(X, U) ⟶ Γ(X, U) ⧸ I(U)`, and affine opens form a basis. -/
instance epi_toPushforwardSubscheme :
    Epi (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) :=
  Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U hU ↦
    I.subschemeι_app_surjective ⟨U, hU⟩

/-- **The exact sequence of a closed subscheme**
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0`. -/
theorem shortExact_toPushforwardSubscheme :
    (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelForkSheafι
  mono_f := inferInstanceAs (Mono I.sheafι)
  epi_g := I.epi_toPushforwardSubscheme

end

end AlgebraicGeometry.Scheme.IdealSheafData
