/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Ext
public import TauCeti.Algebra.Homology.Ext.BaerSum

/-!
# Additivity of derivation extension classes

For continuous derivations `δ` and `η` of a topological algebra `A` and a discrete `A`-module
`M`, the native `Ext¹` class of the self-extension `E_(δ + η)(M)` is the sum of the classes of
`E_δ(M)` and `E_η(M)`. Equivalently, the Baer sum of `E_δ(M)` and `E_η(M)` has the same class
as `E_(δ + η)(M)`. Together with the invariance under inner changes
(`TauCeti.DerivationExtension.extClass_eq_of_inner`), this shows the class depends only on the
outer class of the derivation and is additive in it.

The comparison uses the fibre product `E_δ(M) ×_M E_η(M)` of the two projections. It is the
middle term of an extension of `M` by `M × M`, which maps onto `E_δ(M)` and `E_η(M)` over the two
projections `M × M → M`, and onto `E_(δ + η)(M)` over the addition map `M × M → M`, by
`((u, v), (u', v)) ↦ (u + u', v)`. Naturality of native extension classes and additivity of
composition in `Ext` then give the sum formula. This is the pullback step of the Baer sum,
carried out concretely in modules.

## Main results

* `TauCeti.DerivationExtension.extClass_add`: the class of `E_(δ + η)(M)` is the sum of the
  classes of `E_δ(M)` and `E_η(M)`.
* `TauCeti.DerivationExtension.extClass_baerSum`: the Baer sum of `E_δ(M)` and `E_η(M)`, formed
  by `CategoryTheory.ShortComplex.baerSum`, has the class of `E_(δ + η)(M)`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, for first-order deformations of modules
  over the completed enveloping algebra at the critical level.
* Saunders Mac Lane, *Homology*, Grundlehren der mathematischen Wissenschaften 114,
  Springer, 1963, Chapter III, for the Baer sum of extensions.
-/

public section

namespace TauCeti.DerivationExtension

open CategoryTheory CategoryTheory.Abelian

universe u v w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]

section FiberProduct

variable (δ η : derivationLieAlgebra R A) (M : Type v) [AddCommGroup M] [Module A M]

/-- The fibre product `E_δ(M) ×_M E_η(M)` of the two projections onto the quotient `M`. -/
private def fiberProd : Submodule A (DerivationExtension δ M × DerivationExtension η M) :=
  LinearMap.eqLocus ((sndHom δ M).comp (LinearMap.fst A _ _))
    ((sndHom η M).comp (LinearMap.snd A _ _))

private theorem mem_fiberProd {x : DerivationExtension δ M × DerivationExtension η M} :
    x ∈ fiberProd δ η M ↔ x.1.snd = x.2.snd := by
  simp [fiberProd]

/-- The inclusion `(u, u') ↦ ((u, 0), (u', 0))` of `M × M` into the fibre product. -/
private def fiberInl : (M × M) →ₗ[A] fiberProd δ η M :=
  LinearMap.codRestrict _ ((inlHom δ M).prodMap (inlHom η M)) fun _ => by
    simp [mem_fiberProd]

private theorem coe_fiberInl (x : M × M) :
    (fiberInl δ η M x : DerivationExtension δ M × DerivationExtension η M) =
      (inlHom δ M x.1, inlHom η M x.2) :=
  (rfl)

/-- The common projection `((u, v), (u', v)) ↦ v` of the fibre product onto `M`. -/
private def fiberSnd : fiberProd δ η M →ₗ[A] M :=
  (sndHom δ M).comp ((LinearMap.fst A _ _).comp (fiberProd δ η M).subtype)

/-- The map `((u, v), (u', v)) ↦ (u + u', v)` from the fibre product to `E_(δ + η)(M)`. -/
private def fiberAdd : fiberProd δ η M →ₗ[A] DerivationExtension (δ + η) M where
  toFun x := ⟨x.1.1.fst + x.1.2.fst, x.1.1.snd⟩
  map_add' x y := by
    ext
    · simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, fst_add]
      abel
    · simp
  map_smul' a x := by
    have hx : x.1.2.snd = x.1.1.snd := ((mem_fiberProd δ η M).1 x.2).symm
    ext
    · simp only [SetLike.val_smul, Prod.smul_fst, Prod.smul_snd, fst_smul, hx,
        AddMemClass.coe_add, LinearMap.add_apply, smul_add, add_smul, RingHom.id_apply]
      abel
    · simp

private theorem fiberAdd_comp_fiberInl :
    fiberAdd δ η M ∘ₗ fiberInl δ η M =
      inlHom (δ + η) M ∘ₗ (LinearMap.fst A M M + LinearMap.snd A M M) := by
  ext x <;> simp [fiberAdd, coe_fiberInl]

private theorem sndHom_comp_fiberAdd : sndHom (δ + η) M ∘ₗ fiberAdd δ η M = fiberSnd δ η M := by
  ext x
  simp [fiberAdd, fiberSnd]

private theorem fiberSnd_comp_fiberInl : fiberSnd δ η M ∘ₗ fiberInl δ η M = 0 :=
  LinearMap.ext fun _ => by simp [fiberSnd, coe_fiberInl]

private theorem exact_fiberInl_fiberSnd : Function.Exact (fiberInl δ η M) (fiberSnd δ η M) := by
  rintro ⟨⟨x, y⟩, hxy⟩
  have hxy : x.snd = y.snd := (mem_fiberProd δ η M).1 hxy
  refine ⟨fun hx => ⟨(x.fst, y.fst), ?_⟩, ?_⟩
  · have hx : x.snd = 0 := by simpa [fiberSnd] using hx
    have hy : y.snd = 0 := hxy ▸ hx
    apply Subtype.ext
    ext <;> simp [coe_fiberInl, hx, hy]
  · rintro ⟨u, hu⟩
    rw [← hu]
    exact LinearMap.congr_fun (fiberSnd_comp_fiberInl δ η M) u

private theorem fiberInl_injective : Function.Injective (fiberInl δ η M) :=
  fun _ _ h => Prod.ext (by simpa [coe_fiberInl] using congrArg (fun x => x.1.1.fst) h)
    (by simpa [coe_fiberInl] using congrArg (fun x => x.1.2.fst) h)

private theorem fiberSnd_surjective : Function.Surjective (fiberSnd δ η M) :=
  fun v => ⟨⟨(⟨0, v⟩, ⟨0, v⟩), (mem_fiberProd δ η M).2 rfl⟩, by simp [fiberSnd]⟩

end FiberProduct

variable [TopologicalSpace A] {δ η : derivationLieAlgebra R A}

/-- The extension `0 → M × M → E_δ(M) ×_M E_η(M) → M → 0` in the category of discrete modules. -/
private def fiberShortComplex (hδ : Continuous (δ : Module.End R A))
    (hη : Continuous (η : Module.End R A)) (M : (discreteModules.{v} A).FullSubcategory) :
    ShortComplex (discreteModules.{v} A).FullSubcategory where
  X₁ := ⟨ModuleCat.of A (M.obj × M.obj), discreteModules_prod M.property M.property⟩
  X₂ := ⟨ModuleCat.of A (fiberProd δ η M.obj), by
    have : Mono (ModuleCat.ofHom (fiberProd δ η M.obj).subtype) :=
      (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    exact (discreteModules A).prop_of_mono (ModuleCat.ofHom (fiberProd δ η M.obj).subtype)
      (discreteModules_prod (discreteModules_derivationExtension hδ M.property)
        (discreteModules_derivationExtension hη M.property))⟩
  X₃ := M
  f := ObjectProperty.homMk (ModuleCat.ofHom (fiberInl δ η M.obj))
  g := ObjectProperty.homMk (ModuleCat.ofHom (fiberSnd δ η M.obj))
  zero := InducedCategory.hom_ext (ModuleCat.hom_ext (fiberSnd_comp_fiberInl δ η M.obj))

private theorem shortExact_fiberShortComplex (hδ : Continuous (δ : Module.End R A))
    (hη : Continuous (η : Module.End R A)) (M : (discreteModules.{v} A).FullSubcategory) :
    (fiberShortComplex hδ hη M).ShortExact :=
  ShortExact.reflects_shortExact_of_faithful (discreteModules.{v} A).ι
    (ModuleCat.shortComplex_shortExact _ (exact_fiberInl_fiberSnd δ η M.obj)
      (fiberInl_injective δ η M.obj) (fiberSnd_surjective δ η M.obj))

variable [SeparatelyContinuousAdd A]

/-- Pushing the fibre-product extension forward along a map `M × M → M` gives the
self-extension along `γ`, when there is a middle map over the identity of `M`. -/
private theorem extClass_eq_comp_fiberShortComplex (hδ : Continuous (δ : Module.End R A))
    (hη : Continuous (η : Module.End R A)) {γ : derivationLieAlgebra R A}
    (hγ : Continuous (γ : Module.End R A)) (M : (discreteModules.{max u w} A).FullSubcategory)
    (φ : fiberShortComplex hδ hη M ⟶ discreteShortComplex hγ M) (h₃ : φ.τ₃ = 𝟙 M) :
    extClass hγ M = (shortExact_fiberShortComplex hδ hη M).extClass.comp
      (Ext.mk₀ φ.τ₁) (add_zero 1) := by
  have hn := (shortExact_fiberShortComplex hδ hη M).extClass_naturality
    (shortExact_discreteShortComplex hγ M) φ
  rw [h₃] at hn
  rw [extClass_def]
  exact (hn.trans (Ext.mk₀_id_comp _)).symm

/-- **Additivity of derivation extension classes.** The native `Ext¹` class of the
self-extension along `δ + η` is the sum of the classes along `δ` and along `η`. Continuity of
`δ + η` is a separate hypothesis, since addition on `A` is only assumed separately
continuous. -/
theorem extClass_add (hδ : Continuous (δ : Module.End R A))
    (hη : Continuous (η : Module.End R A))
    (hδη : Continuous ((δ + η : derivationLieAlgebra R A) : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass hδη M = extClass hδ M + extClass hη M := by
  let S := fiberShortComplex hδ hη M
  let p₁ : S.X₁ ⟶ M := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.fst A M.obj M.obj))
  let p₂ : S.X₁ ⟶ M := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd A M.obj M.obj))
  let φ₁ : S ⟶ discreteShortComplex hδ M :=
    { τ₁ := p₁
      τ₂ := ObjectProperty.homMk (ModuleCat.ofHom
        ((LinearMap.fst A _ _).comp (fiberProd δ η M.obj).subtype))
      τ₃ := 𝟙 M
      comm₁₂ := InducedCategory.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun _ => (rfl)))
      comm₂₃ := InducedCategory.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun _ => (rfl))) }
  let φ₂ : S ⟶ discreteShortComplex hη M :=
    { τ₁ := p₂
      τ₂ := ObjectProperty.homMk (ModuleCat.ofHom
        ((LinearMap.snd A _ _).comp (fiberProd δ η M.obj).subtype))
      τ₃ := 𝟙 M
      comm₁₂ := InducedCategory.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun _ => (rfl)))
      comm₂₃ := InducedCategory.hom_ext (ModuleCat.hom_ext
        (LinearMap.ext fun x => (LinearMap.mem_eqLocus.1 x.2).symm)) }
  let φ : S ⟶ discreteShortComplex hδη M :=
    { τ₁ := p₁ + p₂
      τ₂ := ObjectProperty.homMk (ModuleCat.ofHom (fiberAdd δ η M.obj))
      τ₃ := 𝟙 M
      comm₁₂ := InducedCategory.hom_ext
        (ModuleCat.hom_ext (fiberAdd_comp_fiberInl δ η M.obj).symm)
      comm₂₃ := InducedCategory.hom_ext (ModuleCat.hom_ext (sndHom_comp_fiberAdd δ η M.obj)) }
  rw [extClass_eq_comp_fiberShortComplex hδ hη hδη M φ rfl,
    extClass_eq_comp_fiberShortComplex hδ hη hδ M φ₁ rfl,
    extClass_eq_comp_fiberShortComplex hδ hη hη M φ₂ rfl]
  exact (congrArg (fun f => Ext.comp _ f (add_zero 1)) (Ext.mk₀_add p₁ p₂)).trans
    (Ext.comp_add _ _ _ _)

/-- **The Baer sum of derivation self-extensions.** The Baer sum of `E_δ(M)` and `E_η(M)`, the
pushout along the codiagonal of their pullback along the diagonal, has the native `Ext¹` class
of `E_(δ + η)(M)`. -/
theorem extClass_baerSum (hδ : Continuous (δ : Module.End R A))
    (hη : Continuous (η : Module.End R A))
    (hδη : Continuous ((δ + η : derivationLieAlgebra R A) : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    ((shortExact_discreteShortComplex hδ M).baerSum
        (shortExact_discreteShortComplex hη M)).extClass = extClass hδη M := by
  rw [extClass_add hδ hη hδη, extClass_def, extClass_def]
  exact ShortComplex.ShortExact.extClass_baerSum _ _

end TauCeti.DerivationExtension
