/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import TauCeti.AlgebraicGeometry.Modules.Stalk
import Mathlib.AlgebraicGeometry.Properties
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.Algebra.Module.Projective.Vanishing

/-!
# Sections of finite locally free sheaves on reduced schemes

On a reduced scheme `X`, a section of a finite locally free sheaf `E` whose germs vanish at the
points of a dense subset of `X` is zero (`FiniteLocallyFreeSheaf.eq_zero_of_germ_eq_zero`), and so
is a morphism of `𝒪_X`-modules into `E` whose stalk maps vanish at the points of a dense subset
(`FiniteLocallyFreeSheaf.hom_eq_zero_of_stalkₗ_eq_zero`); in particular a morphism into `E`
vanishing over a dense open subscheme is zero. Consequently a morphism into `E` factors uniquely
through any epimorphism that is injective on the stalks at a dense subset
(`FiniteLocallyFreeSheaf.existsUnique_comp_eq`), and two such epimorphisms onto finite locally
free sheaves differ by a unique isomorphism (`FiniteLocallyFreeSheaf.existsUnique_iso_comp_eq`).

On an affine open `W`, the sections `Γ(E, W)` form a projective `Γ(X, W)`-module, hence a direct
summand of a free module, so a section vanishes as soon as each of its coordinates does. A nonzero
coordinate `a` has a nonempty basic open `D(a)`, because `X` is reduced; `D(a)` meets the dense
subset at a point `y`, where the section is killed by an element outside the prime of `y`, which
is impossible as `a` is a unit at `y` (`Module.Projective.eq_zero_of_forall_ne_zero`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

variable {X : Scheme.{u}} [IsReduced X] (E : FiniteLocallyFreeSheaf X) {D : Set X}

/-- **Sections vanishing on a dense set.** On a reduced scheme, a section of a finite locally free
sheaf whose germs vanish at the points of a dense subset is zero. -/
theorem eq_zero_of_germ_eq_zero (hD : Dense D) {V : X.Opens} (s : Γ(E.obj, V))
    (h : ∀ x (hx : x ∈ V), x ∈ D → E.obj.presheaf.germ V x hx s = 0) : s = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext E.obj.isSheaf fun x hxV ↦ ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := V) hxV
  obtain ⟨-, _⟩ :=
    E.obj.isFiniteLocallyFree_iff_forall_isAffineOpen.mp E.property W hW
  refine ⟨W, hWV, hxW, ?_⟩
  rw [map_zero]
  refine Module.Projective.eq_zero_of_forall_ne_zero (A := Γ(X, W)) fun a ha ↦ ?_
  have hne : (X.basicOpen a : Set X).Nonempty :=
    (Opens.ne_bot_iff_nonempty _).mp ((basicOpen_eq_bot_iff a).not.mpr ha)
  obtain ⟨y, hya, hyD⟩ := hD.inter_open_nonempty _ (X.basicOpen a).isOpen hne
  have hyW : y ∈ W := X.basicOpen_le a hya
  have := E.obj.isLocalizedModule_germₗ ⟨y, hyW⟩ hW
  refine ⟨_, inferInstance, (hW.mem_basicOpen_iff_notMem_primeIdealOf ⟨y, hyW⟩ a).mp hya, ?_⟩
  obtain ⟨c, hc⟩ := this.exists_of_eq (x₁ := E.obj.presheaf.map (homOfLE hWV).op s) (x₂ := 0) <| by
    rw [map_zero, Scheme.Modules.germₗ_apply]
    exact (E.obj.presheaf.germ_res_apply (homOfLE hWV) y hyW s).trans (h y (hWV hyW) hyD)
  rw [smul_zero] at hc
  exact ⟨c, c.property, hc⟩

/-- **Morphisms vanishing on a dense set.** On a reduced scheme, a morphism of `𝒪_X`-modules into
a finite locally free sheaf whose stalk maps vanish at the points of a dense subset is zero. -/
theorem hom_eq_zero_of_stalkₗ_eq_zero (hD : Dense D) {M : X.Modules} (φ : M ⟶ E.obj)
    (h : ∀ x ∈ D, φ.stalkₗ x = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext m
  refine (E.eq_zero_of_germ_eq_zero hD _ fun x hx hxD ↦ ?_).trans (by simp)
  rw [← Scheme.Modules.Hom.stalkₗ_germ, h x hxD, LinearMap.zero_apply]

variable {E}

/-- **Comparison of quotients.** On a reduced scheme, let `q₁ : M ⟶ N` be an epimorphism of
`𝒪_X`-modules that is injective on the stalks at the points of a dense subset, and
`q₂ : M ⟶ E` a morphism into a finite locally free sheaf. Then `q₂` factors uniquely through
`q₁`. -/
theorem existsUnique_comp_eq (hD : Dense D) {M N : X.Modules} (q₁ : M ⟶ N) [Epi q₁]
    (hq₁ : ∀ x ∈ D, Function.Injective (q₁.stalkₗ x)) (q₂ : M ⟶ E.obj) :
    ∃! e : N ⟶ E.obj, q₁ ≫ e = q₂ := by
  -- The kernel of `q₁` vanishes on the stalks at the dense subset, so its image under `q₂` does.
  have h : Limits.kernel.ι q₁ ≫ q₂ = 0 := by
    refine E.hom_eq_zero_of_stalkₗ_eq_zero hD _ fun x hx ↦ ?_
    have hz : (Limits.kernel.ι q₁ ≫ q₁).stalkₗ x = 0 := by
      rw [Limits.kernel.condition, Scheme.Modules.Hom.stalkₗ_zero]
    rw [Scheme.Modules.Hom.stalkₗ_comp] at hz ⊢
    ext m
    have hm : (Limits.kernel.ι q₁).stalkₗ x m = 0 :=
      hq₁ x hx (by simpa using LinearMap.congr_fun hz m)
    simp [hm]
  exact ⟨Abelian.epiDesc q₁ q₂ h, Abelian.comp_epiDesc q₁ q₂ h,
    fun e he ↦ (cancel_epi q₁).mp (he.trans (Abelian.comp_epiDesc q₁ q₂ h).symm)⟩

/-- **Uniqueness of locally free quotients.** On a reduced scheme, two epimorphisms
`q₁ : M ⟶ E₁` and `q₂ : M ⟶ E₂` onto finite locally free sheaves that are injective on the stalks
at the points of dense subsets have the same kernel: there is a unique isomorphism `E₁ ≅ E₂`
carrying `q₁` to `q₂`. -/
theorem existsUnique_iso_comp_eq {E₁ E₂ : FiniteLocallyFreeSheaf X} {D₁ D₂ : Set X}
    (hD₁ : Dense D₁) (hD₂ : Dense D₂) {M : X.Modules} (q₁ : M ⟶ E₁.obj) (q₂ : M ⟶ E₂.obj)
    [Epi q₁] [Epi q₂] (hq₁ : ∀ x ∈ D₁, Function.Injective (q₁.stalkₗ x))
    (hq₂ : ∀ x ∈ D₂, Function.Injective (q₂.stalkₗ x)) :
    ∃! e : E₁.obj ≅ E₂.obj, q₁ ≫ e.hom = q₂ := by
  obtain ⟨e, he, -⟩ := existsUnique_comp_eq hD₁ q₁ hq₁ q₂
  obtain ⟨f, hf, -⟩ := existsUnique_comp_eq hD₂ q₂ hq₂ q₁
  refine ⟨⟨e, f, (cancel_epi q₁).mp ?_, (cancel_epi q₂).mp ?_⟩, he, fun g hg ↦ ?_⟩
  · rw [← Category.assoc, he, hf, Category.comp_id]
  · rw [← Category.assoc, hf, he, Category.comp_id]
  · exact Iso.ext ((cancel_epi q₁).mp (hg.trans he.symm))

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
