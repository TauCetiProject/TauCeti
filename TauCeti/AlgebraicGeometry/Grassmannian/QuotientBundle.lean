/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.AffineSubmodule
public import TauCeti.AlgebraicGeometry.Modules.Tilde.PullbackSections
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# The universal quotient bundle on the Grassmannian scheme

Let `R` be a commutative ring, `M` an `R`-module and `k` a natural number, and write
`π : G(k, M) ⟶ Spec R` for the Grassmannian scheme `Module.Grassmannian.scheme R M k`. This file
constructs the **universal quotient** of `π^* M~` on `G(k, M)`: a finite locally free
`𝒪_{G(k, M)}`-module `Q` with an epimorphism `π^* M~ ⟶ Q`
(`Module.Grassmannian.schemeUniversalQuotientπ`), the cokernel of the inclusion of the
**universal kernel** (`Module.Grassmannian.schemeUniversalKernelι`), whose sections over every
affine open `U` are `(Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`, where `N_U` is the point of
`G(k, Γ(G(k, M), U) ⊗[R] M)` classified by the inclusion `Spec Γ(G(k, M), U) ⟶ G(k, M)`
(`Module.Grassmannian.sectionsPoint`), so that `Q` is locally free of rank `k`.

The construction needs no gluing of modules along the charts. The points `N_U` are compatible with
restriction: for affine opens `V ≤ U`, `N_V` is the base change of `N_U` along
`Γ(G(k, M), U) → Γ(G(k, M), V)` (`Module.Grassmannian.map_sectionsPoint`), by naturality of the
functor of points. Over an affine open `U`, pulling back sections exhibits `Γ(π^* M~, U)` as
`Γ(G(k, M), U) ⊗[R] M` (`AlgebraicGeometry.Scheme.Hom.pullbackTildeSectionsEquiv`), so the `N_U`
form submodules of the sections of `π^* M~` over the affine opens, compatible with restriction.
They are the sections of the quasi-coherent universal kernel
(`AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData`), and the universal quotient is the
cokernel of its inclusion.

## Main definitions

* `Module.Grassmannian.schemeUniversalKernelData R M k`: the submodules `N_U` of the sections of
  `π^* M~` over the affine opens `U`.
* `Module.Grassmannian.schemeUniversalKernel R M k`: the universal kernel, with its inclusion
  `Module.Grassmannian.schemeUniversalKernelι R M k` into `π^* M~`.
* `Module.Grassmannian.schemeUniversalQuotient R M k`: the universal quotient `Q`, with its
  projection `Module.Grassmannian.schemeUniversalQuotientπ R M k : π^* M~ ⟶ Q`.
* `Module.Grassmannian.sectionsSchemeUniversalQuotientEquiv U`: over an affine open `U`, the
  sections of `Q` are `(Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`.

## Main results

* `Module.Grassmannian.isColimitSchemeUniversalQuotient`: the universal quotient is the cokernel of
  the universal kernel.
* `Module.Grassmannian.isFiniteLocallyFree_schemeUniversalQuotient`: the universal quotient is
  finite locally free, and its sections over every affine open have rank `k` at every prime
  (`Module.Grassmannian.rankAtStalk_sectionsSchemeUniversalQuotient`).

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its universal quotient.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (k : ℕ)

/-- The functions on an open `U` of the Grassmannian scheme `G(k, M)` form an `R`-algebra through
its structure morphism to `Spec R`. -/
local instance (U : (scheme R M k).Opens) : Algebra R Γ(scheme R M k, U) :=
  (toSpec R M k).sectionsAlgebra U

variable (R) in
/-- The pullback `π^* M~` along the structure morphism `π : G(k, M) ⟶ Spec R` of the
quasi-coherent module `M~` on `Spec R`. The universal quotient is a quotient of it. -/
abbrev pullbackTilde : (scheme R M k).Modules :=
  (Scheme.Modules.pullback (toSpec R M k)).obj (tilde M)

/-- The point `N_U` of `G(k, Γ(G(k, M), U) ⊗[R] M)` classified by the inclusion of an affine open
`U` of `G(k, M)`, carried into `Γ(π^* M~, U)` by the identification
`Γ(G(k, M), U) ⊗[R] M ≃ Γ(π^* M~, U)` (`Scheme.Hom.pullbackTildeSectionsEquiv`). -/
def sectionsKernel (U : (scheme R M k).affineOpens) :
    Submodule Γ(scheme R M k, U) Γ(pullbackTilde R M k, U) :=
  (sectionsPoint (𝟙 _) (Category.id_comp _) U.property).toSubmodule.map
    ((toSpec R M k).pullbackTildeSectionsEquiv M U.property).toLinearMap

/-- Pulling `N_U` back along `Γ(G(k, M), U) ⊗[R] M ≃ Γ(π^* M~, U)` recovers the point classified by
`U`. -/
theorem sectionsKernel_map_symm (U : (scheme R M k).affineOpens) :
    (sectionsKernel M k U).map
        (((toSpec R M k).pullbackTildeSectionsEquiv M U.property).symm :
          Γ(pullbackTilde R M k, U) →ₗ[Γ(scheme R M k, U)] Γ(scheme R M k, U) ⊗[R] M) =
      (sectionsPoint (𝟙 _) (Category.id_comp _) U.property).toSubmodule :=
  (Submodule.map_symm_eq_iff _).2 (rfl)

/-- For affine opens `V ≤ U`, the submodule `N_V` is spanned by the restrictions of `N_U`. -/
theorem sectionsKernel_eq_span {U V : (scheme R M k).affineOpens}
    (h : (V : (scheme R M k).Opens) ≤ U) :
    sectionsKernel M k V = Submodule.span Γ(scheme R M k, V)
      ((pullbackTilde R M k).presheaf.map (homOfLE h).op '' sectionsKernel M k U) := by
  rw [sectionsKernel, ← map_sectionsPoint (𝟙 _) (Category.id_comp _) U.property V.property h,
    map_toSubmodule_eq_span, Submodule.map_span, sectionsKernel, Submodule.map_coe,
    Set.image_image, Set.image_image]
  exact congrArg _ (Set.image_congr fun x _ ↦
    (toSpec R M k).pullbackTildeSectionsEquiv_rTensor M U.property V.property h x)

variable (R) in
/-- The submodules `N_U` of the sections of `π^* M~` over the affine opens `U` of `G(k, M)`,
compatible with restriction. They are the sections of the kernel of the universal quotient
(`Module.Grassmannian.schemeUniversalKernel`). -/
def schemeUniversalKernelData : (pullbackTilde R M k).AffineSubmoduleData where
  submodule U := sectionsKernel M k U
  submodule_eq_span h := sectionsKernel_eq_span M k h

/-- Over an affine open `U`, the submodule of `schemeUniversalKernelData` is `N_U`. -/
@[simp]
theorem schemeUniversalKernelData_submodule (U : (scheme R M k).affineOpens) :
    (schemeUniversalKernelData R M k).submodule U = sectionsKernel M k U :=
  (rfl)

variable (R) in
/-- The **universal kernel** on the Grassmannian scheme `G(k, M)`: the quasi-coherent submodule of
`π^* M~` whose sections over each affine open `U` are the point `N_U` classified by `U`. -/
def schemeUniversalKernel : (scheme R M k).Modules :=
  (schemeUniversalKernelData R M k).sheaf

variable (R) in
/-- The inclusion of the universal kernel into `π^* M~`. -/
def schemeUniversalKernelι : schemeUniversalKernel R M k ⟶ pullbackTilde R M k :=
  (schemeUniversalKernelData R M k).ι

instance : Mono (schemeUniversalKernelι R M k) :=
  inferInstanceAs (Mono (schemeUniversalKernelData R M k).ι)

/-- The universal kernel is quasi-coherent. -/
instance isQuasicoherent_schemeUniversalKernel : (schemeUniversalKernel R M k).IsQuasicoherent :=
  inferInstanceAs (schemeUniversalKernelData R M k).sheaf.IsQuasicoherent

variable (R) in
/-- The **universal quotient** on the Grassmannian scheme `G(k, M)`: the quotient of `π^* M~` by
the universal kernel, whose sections over each affine open `U` are the point `N_U` classified by
`U`. It is finite locally free (`Module.Grassmannian.isFiniteLocallyFree_schemeUniversalQuotient`),
of rank `k` (`Module.Grassmannian.rankAtStalk_sectionsSchemeUniversalQuotient`). -/
def schemeUniversalQuotient : (scheme R M k).Modules :=
  (schemeUniversalKernelData R M k).quotient

variable (R) in
/-- The projection `π^* M~ ⟶ Q` onto the universal quotient. -/
def schemeUniversalQuotientπ : pullbackTilde R M k ⟶ schemeUniversalQuotient R M k :=
  (schemeUniversalKernelData R M k).π

instance : Epi (schemeUniversalQuotientπ R M k) :=
  inferInstanceAs (Epi (schemeUniversalKernelData R M k).π)

/-- The projection onto the universal quotient kills the universal kernel. -/
@[reassoc (attr := simp)]
theorem schemeUniversalKernelι_schemeUniversalQuotientπ :
    schemeUniversalKernelι R M k ≫ schemeUniversalQuotientπ R M k = 0 :=
  (schemeUniversalKernelData R M k).ι_π

/-- **The universal quotient is the cokernel of the universal kernel.** -/
def isColimitSchemeUniversalQuotient :
    IsColimit (CokernelCofork.ofπ (schemeUniversalQuotientπ R M k)
      (schemeUniversalKernelι_schemeUniversalQuotientπ M k)) :=
  (schemeUniversalKernelData R M k).isColimit

/-- The universal quotient is quasi-coherent. -/
instance isQuasicoherent_schemeUniversalQuotient :
    (schemeUniversalQuotient R M k).IsQuasicoherent :=
  inferInstanceAs (schemeUniversalKernelData R M k).quotient.IsQuasicoherent

/-- **Sections of the universal quotient over an affine open.** Over an affine open `U` of
`G(k, M)`, the sections of the universal quotient are the quotient of `Γ(G(k, M), U) ⊗[R] M` by the
point `N_U` classified by `U`. -/
def sectionsSchemeUniversalQuotientEquiv (U : (scheme R M k).affineOpens) :
    Γ(schemeUniversalQuotient R M k, U) ≃ₗ[Γ(scheme R M k, U)]
      (Γ(scheme R M k, U) ⊗[R] M) ⧸
        (sectionsPoint (𝟙 _) (Category.id_comp _) U.property).toSubmodule :=
  (schemeUniversalKernelData R M k).sectionsQuotientEquiv U ≪≫ₗ
    Submodule.Quotient.equiv _ _ ((toSpec R M k).pullbackTildeSectionsEquiv M U.property).symm
      (sectionsKernel_map_symm M k U)

/-- Under `sectionsSchemeUniversalQuotientEquiv`, the projection `π^* M~ ⟶ Q` is the quotient map
`Γ(G(k, M), U) ⊗[R] M → (Γ(G(k, M), U) ⊗[R] M) ⧸ N_U`. -/
@[simp]
theorem sectionsSchemeUniversalQuotientEquiv_π_app (U : (scheme R M k).affineOpens)
    (x : Γ(scheme R M k, U) ⊗[R] M) :
    sectionsSchemeUniversalQuotientEquiv M k U ((schemeUniversalQuotientπ R M k).app U
        ((toSpec R M k).pullbackTildeSectionsEquiv M U.property x)) =
      Submodule.Quotient.mk x := by
  have h := (schemeUniversalKernelData R M k).sectionsQuotientEquiv_π_app U
    ((toSpec R M k).pullbackTildeSectionsEquiv M U.property x)
  -- `Submodule.Quotient.equiv` sends the class of `y` to the class of the image of `y`
  -- (`Submodule.Quotient.equiv_apply` and `Submodule.mapQ_apply`, both by definition)
  exact (congrArg (Submodule.Quotient.equiv _ _ _ (sectionsKernel_map_symm M k U)) h).trans
    (congrArg Submodule.Quotient.mk (LinearEquiv.symm_apply_apply _ x))

/-- **The universal quotient is finite locally free**: over every affine open `U` its sections are
the quotient of `Γ(G(k, M), U) ⊗[R] M` by a point of the Grassmannian, which is finitely generated
and projective. -/
theorem isFiniteLocallyFree_schemeUniversalQuotient :
    Scheme.Modules.isFiniteLocallyFree _ (schemeUniversalQuotient R M k) :=
  (Scheme.Modules.isFiniteLocallyFree_iff_forall_isAffineOpen _).2 fun U hU ↦
    let e := sectionsSchemeUniversalQuotientEquiv M k ⟨U, hU⟩
    ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- **The universal quotient has rank `k`**: over every affine open `U`, its sections have rank `k`
at every prime of `Γ(G(k, M), U)`. -/
theorem rankAtStalk_sectionsSchemeUniversalQuotient (U : (scheme R M k).affineOpens)
    (p : PrimeSpectrum Γ(scheme R M k, U)) :
    Module.rankAtStalk (R := Γ(scheme R M k, U)) Γ(schemeUniversalQuotient R M k, U) p = k := by
  rw [Module.rankAtStalk_eq_of_equiv (sectionsSchemeUniversalQuotientEquiv M k U)]
  exact (sectionsPoint (𝟙 _) (Category.id_comp _) U.property).rankAtStalk_eq p

end Module.Grassmannian
