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

* `Scheme.IdealSheafData.toPushforwardSubscheme`: the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}`;
* `Scheme.IdealSheafData.shortComplex`: the sequence `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}`;
* `Scheme.IdealSheafData.shortComplex_shortExact`: it is short exact.

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

/-- The restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` of regular functions to the closed subscheme cut out
by `I`, as a morphism of `𝒪_X`-modules. Its kernel is `I` and it is an epimorphism
(`shortComplex_shortExact`). -/
def toPushforwardSubscheme :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- On sections over `U`, the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}` is the map of sections of the
closed immersion `ι : V(I) ⟶ X`. -/
@[simp]
lemma toPushforwardSubscheme_app (U : X.Opens) (s : Γ(X, U)) :
    Scheme.Modules.Hom.app I.toPushforwardSubscheme U s = I.subschemeι.app U s :=
  (rfl)

/-- A section of `𝒪_X` restricts to zero on `V(I)` exactly when it is a section of `I`. -/
lemma toPushforwardSubscheme_app_eq_zero_iff {U : X.Opens} {s : Γ(X, U)} :
    Scheme.Modules.Hom.app I.toPushforwardSubscheme U s = 0 ↔ s ∈ I.sections U :=
  I.mem_sections_iff.symm

/-- Regular functions in `I` vanish on `V(I)`. -/
@[simp, reassoc]
lemma sheafι_toPushforwardSubscheme : I.sheafι ≫ I.toPushforwardSubscheme = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  exact (I.toPushforwardSubscheme_app_eq_zero_iff).mpr (I.sheafι_app_mem U t)

/-- The sequence `I ⟶ 𝒪_X ⟶ ι_* 𝒪_{V(I)}` of `𝒪_X`-modules attached to the closed subscheme cut
out by `I`. It is short exact (`shortComplex_shortExact`). -/
@[expose] def shortComplex : ShortComplex X.Modules :=
  ShortComplex.mk I.sheafι I.toPushforwardSubscheme I.sheafι_toPushforwardSubscheme

@[simp]
lemma shortComplex_X₁ : I.shortComplex.X₁ = I.sheaf := (rfl)

@[simp]
lemma shortComplex_X₂ : I.shortComplex.X₂ = SheafOfModules.unit X.ringCatSheaf := (rfl)

@[simp]
lemma shortComplex_X₃ :
    I.shortComplex.X₃ =
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) := (rfl)

/-- The first arrow of `I.shortComplex` is the inclusion `I ⟶ 𝒪_X`. -/
@[simp]
lemma shortComplex_f : I.shortComplex.f = I.sheafι := (rfl)

/-- The second arrow of `I.shortComplex` is the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}`. -/
@[simp]
lemma shortComplex_g : I.shortComplex.g = I.toPushforwardSubscheme := (rfl)

/-- `I` is the kernel of the restriction `𝒪_X ⟶ ι_* 𝒪_{V(I)}`. -/
def isLimitKernelForkSheafι :
    IsLimit (KernelFork.ofι I.sheafι I.sheafι_toPushforwardSubscheme) :=
  KernelFork.IsLimit.ofι _ _
    -- The components of a composite, and of the zero morphism, are computed sectionwise.
    (fun φ hφ ↦ I.sheafLift φ fun U s ↦ (I.toPushforwardSubscheme_app_eq_zero_iff).mp
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
theorem shortComplex_shortExact : I.shortComplex.ShortExact :=
  have : Epi I.shortComplex.g := I.epi_toPushforwardSubscheme
  have : Mono I.shortComplex.f := inferInstanceAs (Mono I.sheafι)
  { exact := ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelForkSheafι }

end

end AlgebraicGeometry.Scheme.IdealSheafData
