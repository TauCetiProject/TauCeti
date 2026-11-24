/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Artinian
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.RingTheory.MatlisDuality.Completion.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory
import TauCeti.LinearAlgebra.Exact
import TauCeti.RingTheory.AdicCompletion.Small

/-!
# Categorical Matlis duality over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ`. Because `E` is
an injective `R`-module and (with its canonical `R̂`-action) also an injective `R̂`-module
(`TauCeti.IsInjectiveEnvelope.adicCompletion`), the Matlis dual functors

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R̂`
  (`M ↦ Hom_R(M, E)`), and
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion : (ModuleCat R̂)ᵒᵖ ⥤ ModuleCat R`
  (`N ↦ Hom_{R̂}(N, E)`)

are contravariant additive functors that turn every short exact sequence into a short exact
sequence (`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
`TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`).

Restricting to Artinian `R`-modules and finitely generated `R̂`-modules yields the exact Matlis
anti-equivalence
`TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`
between `(ModuleCat.isArtinian R).FullSubcategoryᵒᵖ` and `FGModuleCat R̂`, together with
short-exactness equivalences in both directions
(`TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_functor_iff` and
`TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_inverse_iff`).

## Main definitions

* `TauCeti.IsInjectiveEnvelope.matlisDualAdicCompletion`: the contravariant Matlis dual functor
  `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂`.
* `TauCeti.IsInjectiveEnvelope.matlisDualOfAdicCompletion`: the contravariant Matlis dual functor
  `Hom_{R̂}(-, E)` from `ModuleCat R̂` to `ModuleCat R`.
* `TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality`: the contravariant equivalence
  between Artinian `R`-modules and finitely generated `R̂`-modules.

## Main results

* `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualAdicCompletion` and
  `TauCeti.IsInjectiveEnvelope.shortExact_map_matlisDualOfAdicCompletion`: both Matlis dual
  functors reverse short exact sequences of modules.
* `TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_functor`,
  `TauCeti.IsInjectiveEnvelope.shortExact_map_adicCompletionMatlisDuality_inverse`, and their
  `_iff` / `_leftOp` forms: the Matlis anti-equivalence reverses short exact sequences in both
  directions.

## References

* The Stacks Project, Remark 47.7.9, Tag 0EGL.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite TauCeti

section Helpers

universe u v w

private theorem exact_injective_surjective_lcomp {A : Type u} {B : Type*} [Ring A] [Ring B]
    {E : Type v} [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E]
    [Small.{v} A] [Module.Injective A E]
    {X₁ X₂ X₃ : Type w} [AddCommGroup X₁] [Module A X₁]
    [AddCommGroup X₂] [Module A X₂] [AddCommGroup X₃] [Module A X₃]
    {f : X₁ →ₗ[A] X₂} {g : X₂ →ₗ[A] X₃}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Function.Exact (g.lcomp B E) (f.lcomp B E) ∧
      Function.Injective (g.lcomp B E) ∧
      Function.Surjective (f.lcomp B E) :=
  ⟨Function.Exact.lcomp_of_surjective E hfg hg,
   LinearMap.lcomp_injective_of_surjective _ hg,
   fun φ ↦ Module.Injective.extension_property A E X₁ X₂ f hf φ⟩

private theorem shortExact_op_map_of_lcomp {A : Type u} {B : Type*} [Ring A] [Ring B]
    {E : Type v} [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E]
    [Small.{v} A] [Module.Injective A E]
    {F : (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max v w} B} [F.PreservesZeroMorphisms]
    (e : ∀ M : ModuleCat.{w} A, F.obj (op M) ≃ₗ[B] (M →ₗ[A] E))
    (he : ∀ {M M' : ModuleCat.{w} A} (g : M ⟶ M') (φ : F.obj (op M')) (x : M),
      e M (F.map g.op φ) x = e M' φ (g x))
    {S : ShortComplex (ModuleCat.{w} A)} (hS : S.ShortExact) :
    (S.op.map F).ShortExact := by
  have ⟨hex, hinj, hsurj⟩ := exact_injective_surjective_lcomp (B := B) (E := E)
    hS.moduleCat_injective_f hS.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro φ
    constructor
    · intro hφ
      have hφ' : S.f.hom.lcomp B E (e S.X₂ φ) = 0 := by
        ext x
        simpa [ShortComplex.map_g, he] using congrArg (fun f ↦ e S.X₁ f x) hφ
      obtain ⟨ψ, hψ⟩ := (hex (e S.X₂ φ)).mp hφ'
      refine ⟨(e S.X₃).symm ψ, (e S.X₂).injective ?_⟩
      ext x
      simpa [ShortComplex.map_f, he] using LinearMap.congr_fun hψ x
    · rintro ⟨ψ, rfl⟩
      apply (e S.X₁).injective
      ext x
      have hfg : S.g (S.f x) = 0 := by
        rw [← ConcreteCategory.comp_apply, S.zero]
        simp
      simp [ShortComplex.map_f, ShortComplex.map_g, he, hfg]
  · intro φ₁ φ₂ hφ
    apply (e S.X₃).injective
    apply hinj
    ext x
    simpa [ShortComplex.map_f, he] using congrArg (fun f ↦ e S.X₂ f x) hφ
  · intro φ
    obtain ⟨ψ, hψ⟩ := hsurj (e S.X₁ φ)
    refine ⟨(e S.X₂).symm ψ, (e S.X₁).injective ?_⟩
    ext x
    simpa [ShortComplex.map_g, he] using LinearMap.congr_fun hψ x

end Helpers

namespace TauCeti.IsInjectiveEnvelope

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

section Functors

/-- The Matlis dual `Hom_R(M, E)` of a bundled `R`-module `M`, as a bundled `R̂`-module via the
canonical completion action on `E`. -/
def matlisDualAdicCompletionObj (M : ModuleCat.{w} R) :
    ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.of (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E)

/-- The underlying `R̂`-module of `matlisDualAdicCompletionObj hι M` is `M →ₗ[R] E`. -/
def matlisDualAdicCompletionObjEquiv (M : ModuleCat.{w} R) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualAdicCompletionObj M ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R] (M →ₗ[R] E) :=
  LinearEquiv.refl _ _

/-- Precomposition along an `R`-linear morphism `M ⟶ M'` induces an `R̂`-linear morphism between
their Matlis duals. -/
def matlisDualAdicCompletionMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') :
    hι.matlisDualAdicCompletionObj M' ⟶ hι.matlisDualAdicCompletionObj M :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.ofHom ((hι.matlisDualAdicCompletionObjEquiv M).symm.toLinearMap ∘ₗ
    g.hom.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E ∘ₗ
    (hι.matlisDualAdicCompletionObjEquiv M').toLinearMap)

@[simp]
theorem matlisDualAdicCompletionObjEquiv_map_apply {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (φ : hι.matlisDualAdicCompletionObj M') (x : M) :
    hι.matlisDualAdicCompletionObjEquiv M (hι.matlisDualAdicCompletionMap g φ) x =
      hι.matlisDualAdicCompletionObjEquiv M' φ (g x) :=
  (rfl)

/-- The contravariant Matlis dual functor `Hom_R(-, E)` from `ModuleCat R` to `ModuleCat R̂`. -/
def matlisDualAdicCompletion :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) where
  obj M := hι.matlisDualAdicCompletionObj M.unop
  map g := hι.matlisDualAdicCompletionMap g.unop
  map_id M := by
    let := AdicCompletion.torsionModule hι.mem_primaryComponent
    ext φ
    apply (hι.matlisDualAdicCompletionObjEquiv M.unop).injective
    ext x
    simp
  map_comp g h := by
    let := AdicCompletion.torsionModule hι.mem_primaryComponent
    ext φ
    apply (hι.matlisDualAdicCompletionObjEquiv _).injective
    ext x
    simp

@[simp]
theorem matlisDualAdicCompletion_obj (M : (ModuleCat.{w} R)ᵒᵖ) :
    hι.matlisDualAdicCompletion.obj M = hι.matlisDualAdicCompletionObj M.unop :=
  (rfl)

@[simp]
theorem matlisDualAdicCompletion_map {M M' : (ModuleCat.{w} R)ᵒᵖ} (g : M ⟶ M') :
    hι.matlisDualAdicCompletion.map g =
      eqToHom (hι.matlisDualAdicCompletion_obj M) ≫
        hι.matlisDualAdicCompletionMap g.unop ≫
        eqToHom (hι.matlisDualAdicCompletion_obj M').symm :=
  (rfl)

theorem matlisDualAdicCompletionMap_add {M M' : ModuleCat.{w} R} (g h : M ⟶ M') :
    hι.matlisDualAdicCompletionMap (g + h) =
      hι.matlisDualAdicCompletionMap g + hι.matlisDualAdicCompletionMap h := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext φ
  apply (hι.matlisDualAdicCompletionObjEquiv _).injective
  ext x
  simp [ModuleCat.hom_add]

instance : (hι.matlisDualAdicCompletion :
    (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)).Additive
    where
  map_add := hι.matlisDualAdicCompletionMap_add _ _

/-- The Matlis dual `Hom_{R̂}(N, E)` of a bundled `R̂`-module `N`, as a bundled `R`-module. -/
def matlisDualOfAdicCompletionObj
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    ModuleCat.{max v w} R :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.of R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)

/-- The underlying `R`-module of `matlisDualOfAdicCompletionObj hι N` is `N →ₗ[R̂] E`. -/
def matlisDualOfAdicCompletionObjEquiv
    (N : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.matlisDualOfAdicCompletionObj N ≃ₗ[R]
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  LinearEquiv.refl _ _

/-- Precomposition along an `R̂`-linear morphism `N ⟶ N'` induces an `R`-linear morphism between
their Matlis duals. -/
def matlisDualOfAdicCompletionMap
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletionObj N' ⟶ hι.matlisDualOfAdicCompletionObj N :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  ModuleCat.ofHom ((hι.matlisDualOfAdicCompletionObjEquiv N).symm.toLinearMap ∘ₗ
    g.hom.lcomp R E ∘ₗ (hι.matlisDualOfAdicCompletionObjEquiv N').toLinearMap)

@[simp]
theorem matlisDualOfAdicCompletionObjEquiv_map_apply
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (φ : hι.matlisDualOfAdicCompletionObj N') (x : N) :
    hι.matlisDualOfAdicCompletionObjEquiv N (hι.matlisDualOfAdicCompletionMap g φ) x =
      hι.matlisDualOfAdicCompletionObjEquiv N' φ (g x) :=
  (rfl)

/-- The contravariant Matlis dual functor `Hom_{R̂}(-, E)` from `ModuleCat R̂` to `ModuleCat R`. -/
def matlisDualOfAdicCompletion :
    (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤ ModuleCat.{max v w} R where
  obj N := hι.matlisDualOfAdicCompletionObj N.unop
  map g := hι.matlisDualOfAdicCompletionMap g.unop
  map_id N := by
    let := AdicCompletion.torsionModule hι.mem_primaryComponent
    ext φ
    apply (hι.matlisDualOfAdicCompletionObjEquiv N.unop).injective
    ext x
    simp
  map_comp g h := by
    let := AdicCompletion.torsionModule hι.mem_primaryComponent
    ext φ
    apply (hι.matlisDualOfAdicCompletionObjEquiv _).injective
    ext x
    simp

@[simp]
theorem matlisDualOfAdicCompletion_obj
    (N : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ) :
    hι.matlisDualOfAdicCompletion.obj N = hι.matlisDualOfAdicCompletionObj N.unop :=
  (rfl)

@[simp]
theorem matlisDualOfAdicCompletion_map
    {N N' : (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ} (g : N ⟶ N') :
    hι.matlisDualOfAdicCompletion.map g =
      eqToHom (hι.matlisDualOfAdicCompletion_obj N) ≫
        hι.matlisDualOfAdicCompletionMap g.unop ≫
        eqToHom (hι.matlisDualOfAdicCompletion_obj N').symm :=
  (rfl)

theorem matlisDualOfAdicCompletionMap_add
    {N N' : ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R)} (g h : N ⟶ N') :
    hι.matlisDualOfAdicCompletionMap (g + h) =
      hι.matlisDualOfAdicCompletionMap g + hι.matlisDualOfAdicCompletionMap h := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext φ
  apply (hι.matlisDualOfAdicCompletionObjEquiv _).injective
  ext x
  simp [ModuleCat.hom_add]

instance : (hι.matlisDualOfAdicCompletion :
    (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))ᵒᵖ ⥤ ModuleCat.{max v w} R).Additive
    where
  map_add := hι.matlisDualOfAdicCompletionMap_add _ _

section SmallFunctors

variable [Small.{v} R]

/-- **Exactness of `Hom_R(-, E)`**: applying `matlisDualAdicCompletion` reverses every short exact
sequence of `R`-modules into a short exact sequence of `R̂`-modules. -/
theorem shortExact_map_matlisDualAdicCompletion {S : ShortComplex (ModuleCat.{w} R)}
    (hS : S.ShortExact) : (S.op.map hι.matlisDualAdicCompletion).ShortExact := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  refine shortExact_op_map_of_lcomp
    (fun M ↦ (eqToIso (hι.matlisDualAdicCompletion_obj (op M))).toLinearEquiv.trans
      (hι.matlisDualAdicCompletionObjEquiv M))
    (fun g φ x ↦ ?_) hS
  simp only [LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, eqToIso.hom]
  rw [← ConcreteCategory.comp_apply, matlisDualAdicCompletion_map, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, ConcreteCategory.comp_apply]
  simp

/-- **Exactness of `Hom_{R̂}(-, E)`**: applying `matlisDualOfAdicCompletion` reverses every short
exact sequence of `R̂`-modules into a short exact sequence of `R`-modules. -/
theorem shortExact_map_matlisDualOfAdicCompletion
    {T : ShortComplex (ModuleCat.{w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.op.map hι.matlisDualOfAdicCompletion).ShortExact := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.moduleInjective
  refine shortExact_op_map_of_lcomp
    (fun N ↦ (eqToIso (hι.matlisDualOfAdicCompletion_obj (op N))).toLinearEquiv.trans
      (hι.matlisDualOfAdicCompletionObjEquiv N))
    (fun g φ x ↦ ?_) hT
  simp only [LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, eqToIso.hom]
  rw [← ConcreteCategory.comp_apply, matlisDualOfAdicCompletion_map, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, ConcreteCategory.comp_apply]
  simp

end SmallFunctors

end Functors

section EvalIso

variable [Small.{v} R]

/-- General Matlis biduality for a bundled Artinian `R`-module `M`, as an isomorphism
`M ≅ Hom_{R̂}(Hom_R(M, E), E)`. -/
def evalIsoAdicCompletion (M : ModuleCat.{max v w} R) (hM : IsArtinian R M) :
    M ≅ hι.matlisDualOfAdicCompletionObj (hι.matlisDualAdicCompletionObj M) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hM
  let eArrow := LinearEquiv.congrLeft E R (hι.matlisDualAdicCompletionObjEquiv M).symm
  exact ((hι.evalEquivAdicCompletionOfIsArtinian M).trans
    (eArrow.trans (hι.matlisDualOfAdicCompletionObjEquiv _).symm)).toModuleIso

@[simp]
theorem evalIsoAdicCompletion_hom_apply (M : ModuleCat.{max v w} R) (hM : IsArtinian R M)
    (m : M) (f : hι.matlisDualAdicCompletionObj M) :
    hι.matlisDualOfAdicCompletionObjEquiv _ ((hι.evalIsoAdicCompletion M hM).hom m) f =
      hι.matlisDualAdicCompletionObjEquiv M f m := by
  simp [evalIsoAdicCompletion, LinearEquiv.congrLeft_apply]

/-- General Matlis biduality for a bundled finitely generated `R̂`-module `N`, as an isomorphism
`N ≅ Hom_R(Hom_{R̂}(N, E), E)`. -/
def evalIsoOfFiniteAdicCompletion
    (N : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N) :
    N ≅ hι.matlisDualAdicCompletionObj (hι.matlisDualOfAdicCompletionObj N) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hN
  let eArrow := LinearEquiv.congrLeft E (_root_.AdicCompletion (maximalIdeal R) R)
    (hι.matlisDualOfAdicCompletionObjEquiv N).symm
  exact ((hι.evalEquivOfFiniteAdicCompletion N).trans
    (eArrow.trans (hι.matlisDualAdicCompletionObjEquiv _).symm)).toModuleIso

@[simp]
theorem evalIsoOfFiniteAdicCompletion_hom_apply
    (N : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N)
    (x : N) (f : hι.matlisDualOfAdicCompletionObj N) :
    hι.matlisDualAdicCompletionObjEquiv _ ((hι.evalIsoOfFiniteAdicCompletion N hN).hom x) f =
      hι.matlisDualOfAdicCompletionObjEquiv N f x := by
  simp [evalIsoOfFiniteAdicCompletion, LinearEquiv.congrLeft_apply]

/-- `evalIsoAdicCompletion` is natural in `M`. -/
theorem evalIsoAdicCompletion_hom_naturality {M M' : ModuleCat.{max v w} R} (g : M ⟶ M')
    (hM : IsArtinian R M) (hM' : IsArtinian R M') :
    g ≫ (hι.evalIsoAdicCompletion M' hM').hom =
      (hι.evalIsoAdicCompletion M hM).hom ≫
        hι.matlisDualOfAdicCompletionMap (hι.matlisDualAdicCompletionMap g) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext x
  apply (hι.matlisDualOfAdicCompletionObjEquiv _).injective
  ext φ
  simp

/-- `evalIsoOfFiniteAdicCompletion` is natural in `N`. -/
theorem evalIsoOfFiniteAdicCompletion_hom_naturality
    {N N' : ModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N')
    (hN : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N)
    (hN' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N') :
    g ≫ (hι.evalIsoOfFiniteAdicCompletion N' hN').hom =
      (hι.evalIsoOfFiniteAdicCompletion N hN).hom ≫
        hι.matlisDualAdicCompletionMap (hι.matlisDualOfAdicCompletionMap g) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext x
  apply (hι.matlisDualAdicCompletionObjEquiv _).injective
  ext φ
  simp

/-- Triangle identity: evaluation on `Hom_R(M, E)` is precomposition with the inverse of
evaluation on `M`. -/
theorem evalIsoOfFiniteAdicCompletion_matlisDualAdicCompletionObj_hom
    (M : ModuleCat.{max v w} R) (hM : IsArtinian R M)
    (hM' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R)
      (hι.matlisDualAdicCompletionObj M)) :
    (hι.evalIsoOfFiniteAdicCompletion (hι.matlisDualAdicCompletionObj M) hM').hom =
      hι.matlisDualAdicCompletionMap (hι.evalIsoAdicCompletion M hM).inv := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext φ
  apply (hι.matlisDualAdicCompletionObjEquiv _).injective
  ext Ψ
  obtain ⟨x, rfl⟩ : ∃ x, (hι.evalIsoAdicCompletion M hM).hom x = Ψ :=
    ⟨(hι.evalIsoAdicCompletion M hM).inv Ψ, (hι.evalIsoAdicCompletion M hM).inv_hom_id_apply Ψ⟩
  simp

end EvalIso

section Equivalence

variable [Small.{v} R]

/-- **General Matlis duality over the completion**: `Hom_R(-, E)` and `Hom_{R̂}(-, E)` form a
contravariant equivalence between Artinian `R`-modules and finitely generated `R̂`-modules, whose
unit and counit are evaluation. -/
def adicCompletionMatlisDuality :
    (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ ≌
      FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) where
  functor := ObjectProperty.lift _
    ((ModuleCat.isArtinian.{max v w} R).ι.op ⋙ hι.matlisDualAdicCompletion)
    fun M ↦ by
      let := AdicCompletion.torsionModule hι.mem_primaryComponent
      have : IsArtinian R M.unop.obj := (ModuleCat.isArtinian_iff _).mp M.unop.property
      have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M.unop.obj →ₗ[R] E) :=
        hι.finite_adicCompletion_linearMap_of_isArtinian
      exact (ModuleCat.isFG_iff _).mpr
        (Module.Finite.equiv (hι.matlisDualAdicCompletionObjEquiv M.unop.obj).symm)
  inverse := (ObjectProperty.lift _
    ((ModuleCat.isFG.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)).ι.op ⋙
      hι.matlisDualOfAdicCompletion)
    fun N ↦ by
      have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N.unop.obj :=
        (ModuleCat.isFG_iff _).mp N.unop.property
      let := AdicCompletion.torsionModule hι.mem_primaryComponent
      have : IsArtinian R (N.unop.obj →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
        hι.isArtinian_adicCompletion_linearMap_of_finite N.unop.obj
      exact (ModuleCat.isArtinian_iff _).mpr
        (isArtinian_of_linearEquiv
          (hι.matlisDualOfAdicCompletionObjEquiv N.unop.obj).symm)).rightOp
  unitIso := NatIso.ofComponents (fun M ↦
      (ObjectProperty.isoMk _ (hι.evalIsoAdicCompletion M.unop.obj
        ((ModuleCat.isArtinian_iff _).mp M.unop.property))).symm.op)
    (fun {X Y} g ↦ Quiver.Hom.unop_inj <| (Iso.inv_comp_eq _).mpr <|
      ((Iso.eq_comp_inv _).mpr <| ObjectProperty.hom_ext _ <|
        hι.evalIsoAdicCompletion_hom_naturality g.unop.hom
          ((ModuleCat.isArtinian_iff _).mp Y.unop.property)
          ((ModuleCat.isArtinian_iff _).mp X.unop.property)).trans (Category.assoc _ _ _))
  counitIso := NatIso.ofComponents (fun N ↦
      (ObjectProperty.isoMk _ (hι.evalIsoOfFiniteAdicCompletion N.obj
        ((ModuleCat.isFG_iff _).mp N.property))).symm)
    (fun {X Y} g ↦ (Iso.comp_inv_eq _).mpr <| ((Iso.eq_inv_comp _).mpr <|
      (ObjectProperty.hom_ext _ <|
        (hι.evalIsoOfFiniteAdicCompletion_hom_naturality g.hom
          ((ModuleCat.isFG_iff _).mp X.property)
          ((ModuleCat.isFG_iff _).mp Y.property)).symm)).trans (Category.assoc _ _ _).symm)
  functor_unitIso_comp M := by
    refine ObjectProperty.hom_ext _ ?_
    have : IsArtinian R M.unop.obj := (ModuleCat.isArtinian_iff _).mp M.unop.property
    let := AdicCompletion.torsionModule hι.mem_primaryComponent
    have : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M.unop.obj →ₗ[R] E) :=
      hι.finite_adicCompletion_linearMap_of_isArtinian
    have hM' : Module.Finite (_root_.AdicCompletion (maximalIdeal R) R)
        (hι.matlisDualAdicCompletionObj M.unop.obj) :=
      Module.Finite.equiv (hι.matlisDualAdicCompletionObjEquiv M.unop.obj).symm
    exact (Iso.comp_inv_eq_id (hι.evalIsoOfFiniteAdicCompletion
      (hι.matlisDualAdicCompletionObj M.unop.obj) hM')).mpr
      (hι.evalIsoOfFiniteAdicCompletion_matlisDualAdicCompletionObj_hom M.unop.obj
        ((ModuleCat.isArtinian_iff _).mp M.unop.property) hM').symm

@[simp]
theorem adicCompletionMatlisDuality_functor_obj_obj
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.adicCompletionMatlisDuality.functor.obj M).obj =
      hι.matlisDualAdicCompletionObj M.unop.obj :=
  (rfl)

@[simp]
theorem adicCompletionMatlisDuality_functor_map_hom
    {M M' : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    (hι.adicCompletionMatlisDuality.functor.map g).hom =
      eqToHom (hι.adicCompletionMatlisDuality_functor_obj_obj M) ≫
        hι.matlisDualAdicCompletionMap g.unop.hom ≫
        eqToHom (hι.adicCompletionMatlisDuality_functor_obj_obj M').symm := by
  simp [adicCompletionMatlisDuality]

@[simp]
theorem adicCompletionMatlisDuality_inverse_obj_unop_obj
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.adicCompletionMatlisDuality.inverse.obj N).unop.obj =
      hι.matlisDualOfAdicCompletionObj N.obj :=
  (rfl)

@[simp]
theorem adicCompletionMatlisDuality_inverse_map_unop_hom
    {N N' : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    (hι.adicCompletionMatlisDuality.inverse.map g).unop.hom =
      eqToHom (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N') ≫
        hι.matlisDualOfAdicCompletionMap g.hom ≫
        eqToHom (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N).symm := by
  simp [adicCompletionMatlisDuality]

/-- The inverse of the unit of `adicCompletionMatlisDuality` is evaluation
`M → Hom_{R̂}(Hom_R(M, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_unitIso_inv_app
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.adicCompletionMatlisDuality.unitIso.inv.app M).unop.hom =
      (hι.evalIsoAdicCompletion M.unop.obj ((ModuleCat.isArtinian_iff _).mp M.unop.property)).hom ≫
        eqToHom ((congrArg hι.matlisDualOfAdicCompletionObj
          (hι.adicCompletionMatlisDuality_functor_obj_obj M)).symm.trans
          (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj _).symm) :=
  (rfl)

/-- The inverse of the counit of `adicCompletionMatlisDuality` is evaluation
`N → Hom_R(Hom_{R̂}(N, E), E)`. -/
@[simp]
theorem adicCompletionMatlisDuality_counitIso_inv_app
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.adicCompletionMatlisDuality.counitIso.inv.app N).hom =
      (hι.evalIsoOfFiniteAdicCompletion N.obj ((ModuleCat.isFG_iff _).mp N.property)).hom ≫
        eqToHom ((congrArg hι.matlisDualAdicCompletionObj
          (hι.adicCompletionMatlisDuality_inverse_obj_unop_obj N)).symm.trans
          (hι.adicCompletionMatlisDuality_functor_obj_obj _).symm) :=
  (rfl)

/-- Applying `adicCompletionMatlisDuality.functor` reverses a short exact sequence of Artinian
`R`-modules into a short exact sequence of finitely generated `R̂`-modules. -/
theorem shortExact_map_adicCompletionMatlisDuality_functor
    {S : ShortComplex (ModuleCat.isArtinian.{max v w} R).FullSubcategory} (hS : S.ShortExact) :
    (S.op.map hι.adicCompletionMatlisDuality.functor).ShortExact := by
  have : IsNoetherianRing (_root_.AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.isNoetherianRing_adicCompletion_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  exact hS.op.map_of_exact hι.adicCompletionMatlisDuality.functor

/-- A short complex of Artinian `R`-modules is short exact iff its image under
`adicCompletionMatlisDuality.functor` is short exact. -/
theorem shortExact_map_adicCompletionMatlisDuality_functor_iff
    {S : ShortComplex (ModuleCat.isArtinian.{max v w} R).FullSubcategory} :
    (S.op.map hι.adicCompletionMatlisDuality.functor).ShortExact ↔ S.ShortExact := by
  refine ⟨fun h ↦ ?_, hι.shortExact_map_adicCompletionMatlisDuality_functor⟩
  have : IsNoetherianRing (_root_.AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.isNoetherianRing_adicCompletion_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  exact ShortComplex.ShortExact.unop
    ((ShortComplex.shortExact_iff_of_iso
      (S.op.mapNatIso hι.adicCompletionMatlisDuality.unitIso)).mpr
      (h.map_of_exact hι.adicCompletionMatlisDuality.inverse))

/-- Applying `adicCompletionMatlisDuality.inverse` reverses a short exact sequence of finitely
generated `R̂`-modules into a short exact sequence of Artinian `R`-modules. -/
theorem shortExact_map_adicCompletionMatlisDuality_inverse
    {T : ShortComplex (FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.map hι.adicCompletionMatlisDuality.inverse).unop.ShortExact := by
  have : IsNoetherianRing (_root_.AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.isNoetherianRing_adicCompletion_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  exact (hT.map_of_exact hι.adicCompletionMatlisDuality.inverse).unop

/-- Applying `adicCompletionMatlisDuality.inverse.leftOp` reverses a short exact sequence of
finitely generated `R̂`-modules into a short exact sequence of Artinian `R`-modules. -/
theorem shortExact_map_adicCompletionMatlisDuality_inverse_leftOp
    {T : ShortComplex (FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))}
    (hT : T.ShortExact) :
    (T.op.map hι.adicCompletionMatlisDuality.inverse.leftOp).ShortExact :=
  hι.shortExact_map_adicCompletionMatlisDuality_inverse hT

/-- A short complex of finitely generated `R̂`-modules is short exact iff its dual under
`adicCompletionMatlisDuality.inverse` is short exact. -/
theorem shortExact_map_adicCompletionMatlisDuality_inverse_iff
    {T : ShortComplex (FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R))} :
    (T.map hι.adicCompletionMatlisDuality.inverse).unop.ShortExact ↔ T.ShortExact := by
  refine ⟨fun h ↦ ?_, hι.shortExact_map_adicCompletionMatlisDuality_inverse⟩
  have : IsNoetherianRing (_root_.AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.isNoetherianRing_adicCompletion_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  exact (ShortComplex.shortExact_iff_of_iso
    (T.mapNatIso hι.adicCompletionMatlisDuality.counitIso)).mp
    (h.op.map_of_exact hι.adicCompletionMatlisDuality.functor)

end Equivalence

end TauCeti.IsInjectiveEnvelope
