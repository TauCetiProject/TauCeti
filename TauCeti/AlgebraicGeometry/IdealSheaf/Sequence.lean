/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Unit
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
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
subscheme `V(I)`. Since `ι` is affine, `ι_* 𝒪_{V(I)}` is quasi-coherent, and hence so is the kernel
`I` of a morphism between quasi-coherent sheaves.

## Main declarations

* `Scheme.IdealSheafData.pushforwardSubscheme`: the direct image `ι_* 𝒪_{V(I)}`, with the
  restriction `Scheme.IdealSheafData.toPushforwardSubscheme : 𝒪_X ⟶ ι_* 𝒪_{V(I)}`, given on
  sections by restriction of functions (`Scheme.IdealSheafData.toPushforwardSubscheme_app`).
* `Scheme.IdealSheafData.sheafι_toPushforwardSubscheme_of_le`: for `I ≤ J`, the composite
  `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(J)}` vanishes.
* `Scheme.IdealSheafData.shortExact_toPushforwardSubscheme`: the sequence
  `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}` is short exact.
* `Scheme.IdealSheafData.isQuasicoherent_sheaf`: the ideal sheaf `I` is quasi-coherent.

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

/-- The direct image `ι_* 𝒪_{V(I)}` on `X` of the structure sheaf of the closed subscheme
`V(I)`. -/
abbrev pushforwardSubscheme : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

/-- The restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` of regular functions to the closed subscheme `V(I)`, as
a morphism of `𝒪_X`-modules. Its target is pinned to `Scheme.Modules.pushforward`: `simp` does not
identify sections of it with those of the defeq target `SheafOfModules.pushforward` that Mathlib
gives `SheafOfModules.unitToPushforwardObjUnit`, and no zero morphism is synthesized there. -/
def toPushforwardSubscheme : Scheme.Modules.unit X ⟶ I.pushforwardSubscheme :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- The restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` is Mathlib's unit map `𝒪_X ⟶ ι_* 𝒪_{V(I)}` of the
direct image along `ι`, through which its `SheafOfModules.unitToPushforwardObjUnit` API applies. -/
lemma toPushforwardSubscheme_def :
    I.toPushforwardSubscheme =
      SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom := by
  rfl

/-- On sections over `U`, the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` is the restriction
`Γ(X, U) ⟶ Γ(V(I), ι⁻¹ U)` of regular functions. It is not `@[simp]`: rewriting with it would
preempt the simp lemma `subschemeι_app_eq_zero_iff`. -/
lemma toPushforwardSubscheme_app {U : X.Opens} (s : Γ(X, U)) :
    Scheme.Modules.Hom.app I.toPushforwardSubscheme U s = I.subschemeι.app U s := by
  rfl

/-- A section of `𝒪_X` restricts to zero on `V(I)` exactly when it is a section of `I`. -/
@[simp]
lemma subschemeι_app_eq_zero_iff {U : X.Opens} {s : Γ(X, U)} :
    Scheme.Modules.Hom.app I.toPushforwardSubscheme U s = 0 ↔ s ∈ I.sections U :=
  I.mem_sections_iff.symm

/-- Regular functions in `I` vanish on `V(I)`. -/
@[simp, reassoc]
lemma sheafι_toPushforwardSubscheme : I.sheafι ≫ I.toPushforwardSubscheme = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  -- The components of a composite and of the zero morphism are computed sectionwise
  -- (`Scheme.Modules.Hom.comp_app` and `Scheme.Modules.Hom.zero_app` hold by `rfl`). Neither
  -- `rw` nor `simp` can apply `comp_app` here: the goal is ill-typed at `implicit` transparency,
  -- where the ring sheaf of `V(I)` is a `TopCat.Sheaf` rather than a sheaf on the site.
  exact (I.subschemeι_app_eq_zero_iff).mpr (I.sheafι_app_mem U t)

variable {I} in
/-- For `I ≤ J`, regular functions in `I` vanish on the smaller closed subscheme `V(J)`. -/
@[simp, reassoc]
lemma sheafι_toPushforwardSubscheme_of_le {J : X.IdealSheafData} (h : I ≤ J) :
    (I.sheafι : I.sheaf ⟶ Scheme.Modules.unit X) ≫ J.toPushforwardSubscheme = 0 :=
  Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦
    (J.subschemeι_app_eq_zero_iff).mpr (sections_mono h U (I.sheafι_app_mem U t))

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
instance epi_toPushforwardSubscheme : Epi I.toPushforwardSubscheme :=
  Scheme.Modules.Hom.epi_of_surjective_on_affineOpens _ fun U hU ↦
    I.subschemeι_app_surjective ⟨U, hU⟩

/-- **The exact sequence of a closed subscheme**
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)} ⟶ 0`. -/
theorem shortExact_toPushforwardSubscheme :
    (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelForkSheafι
  mono_f := inferInstanceAs (Mono I.sheafι)
  epi_g := I.epi_toPushforwardSubscheme

/-- An ideal sheaf is quasi-coherent: it is the kernel of the morphism `𝒪_X ⟶ ι_* 𝒪_{V(I)}`
between quasi-coherent sheaves, the target being quasi-coherent as `ι` is affine. -/
instance isQuasicoherent_sheaf : I.sheaf.IsQuasicoherent := by
  -- The quasi-coherence of the target `ι_* 𝒪_{V(I)}` is supplied by hand, as instance search
  -- does not find `Scheme.Modules.isQuasicoherent_pushforward` for it.
  have : I.pushforwardSubscheme.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward _ I.subschemeι
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel _) I.isLimitKernelForkSheafι)
    (Scheme.Modules.isQuasicoherent_kernel (N := I.pushforwardSubscheme) I.toPushforwardSubscheme)

end

end AlgebraicGeometry.Scheme.IdealSheafData
