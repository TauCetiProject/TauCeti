/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import TauCeti.Algebra.Category.FiniteIsocrystal.Basic
public import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear

/-!
# The abelian category of finite isocrystals

Let `D` be a finite isocrystal over `(L, σ)`. A subspace `W` of `D` is *Frobenius-stable* if
`Φ x ∈ W` for every `x ∈ W`. Since `Φ` is injective and `σ`-semilinear for an automorphism `σ`,
and `W` is finite-dimensional, `Φ` then maps `W` bijectively onto itself. So `W` carries the
sub-isocrystal `D.sub W hW` and `D ⧸ W` carries the quotient isocrystal `D.quotient W hW`.

The kernel and the range of the underlying linear map of a morphism of finite isocrystals are
Frobenius-stable, and the corresponding sub-isocrystal and quotient isocrystal are a kernel and a
cokernel in the category of finite isocrystals. The forgetful functor to `L`-vector spaces
preserves them; as it is faithful and reflects isomorphisms, the coimage-image comparison
morphisms are isomorphisms, so the category of finite isocrystals is abelian. This is the
setting of the Dieudonné–Manin classification: simplicity of the standard blocks, vanishing of
morphisms between different slopes and the splitting of short exact sequences are statements in
this abelian category.

## Main definitions

* `TauCeti.FiniteIsocrystal.sub` and `TauCeti.FiniteIsocrystal.quotient`: the sub-isocrystal on
  a Frobenius-stable subspace and the quotient isocrystal by it, with the inclusion
  `TauCeti.FiniteIsocrystal.subι` and the projection `TauCeti.FiniteIsocrystal.quotientπ`.
* `TauCeti.FiniteIsocrystal.kernelFork` and `TauCeti.FiniteIsocrystal.cokernelCofork`: the
  concrete kernel and cokernel of a morphism.

## Main results

* `TauCeti.FiniteIsocrystal.frobenius_restrict_bijective`: the Frobenius maps a Frobenius-stable
  subspace bijectively onto itself.
* `TauCeti.FiniteIsocrystal.kernelIsLimit` and `TauCeti.FiniteIsocrystal.cokernelIsColimit`: the
  concrete kernel and cokernel are a kernel and a cokernel.
* `TauCeti.FiniteIsocrystal.mono_iff_injective` and
  `TauCeti.FiniteIsocrystal.epi_iff_surjective`: monomorphisms and epimorphisms are the morphisms
  with injective and surjective underlying linear maps.
* The category of finite isocrystals is abelian, and the forgetful functor to `ModuleCat L`
  preserves kernels and cokernels.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti

namespace FiniteIsocrystal

variable {E L : Type*} [CommRing E] [Field L] [Algebra E L] {σ : L ≃ₐ[E] L}

/-! ### Frobenius-stable subspaces -/

section Stable

variable (D : FiniteIsocrystal.{u} σ) (W : Submodule L D) (hW : ∀ x ∈ W, D.frobenius x ∈ W)

/-- The Frobenius of a finite isocrystal restricts to a bijection of every Frobenius-stable
subspace. -/
theorem frobenius_restrict_bijective : Function.Bijective (D.frobenius.restrict hW) := by
  have hinj : Function.Injective (D.frobenius.restrict hW) := fun x y h =>
    Subtype.ext (D.frobenius_injective (congrArg Subtype.val h))
  have : RingHomSurjective (σ : L →+* L) := ⟨σ.surjective⟩
  exact ⟨hinj, LinearMap.surjective_of_injectiveₛₗ hinj⟩

include hW in
/-- A Frobenius-stable subspace contains every vector whose Frobenius it contains. -/
theorem mem_of_frobenius_mem {x : D} (hx : D.frobenius x ∈ W) : x ∈ W := by
  obtain ⟨y, hy⟩ := (D.frobenius_restrict_bijective W hW).surjective ⟨_, hx⟩
  rw [D.frobenius_injective (congrArg Subtype.val hy).symm]
  exact y.property

/-- The sub-isocrystal on a Frobenius-stable subspace, with the restricted Frobenius. -/
abbrev sub : FiniteIsocrystal.{u} σ :=
  of σ W (D.frobenius.restrict hW) (D.frobenius_restrict_bijective W hW)

/-- The inclusion of the sub-isocrystal on a Frobenius-stable subspace. -/
def subι : D.sub W hW ⟶ D := ofHom W.subtype fun _ => rfl

@[simp]
theorem subι_hom : (D.subι W hW).hom = W.subtype := (rfl)

instance : Mono (D.subι W hW) := ConcreteCategory.mono_of_injective _ W.injective_subtype

/-- The Frobenius induced on the quotient by a Frobenius-stable subspace. -/
def quotientFrobenius : (D ⧸ W) →ₛₗ[(σ : L →+* L)] (D ⧸ W) := W.mapQ W D.frobenius hW

@[simp]
theorem quotientFrobenius_mk (x : D) :
    D.quotientFrobenius W hW (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.frobenius x) :=
  (rfl)

/-- The Frobenius induced on the quotient by a Frobenius-stable subspace is bijective. -/
theorem quotientFrobenius_bijective : Function.Bijective (D.quotientFrobenius W hW) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [quotientFrobenius_mk, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero W).2 (D.mem_of_frobenius_mem W hW hx)
  · induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, rfl⟩ := D.frobenius_surjective y
      exact ⟨Submodule.Quotient.mk x, quotientFrobenius_mk _ _ _ _⟩

/-- The quotient isocrystal by a Frobenius-stable subspace, with the induced Frobenius. -/
abbrev quotient : FiniteIsocrystal.{u} σ :=
  of σ (D ⧸ W) (D.quotientFrobenius W hW) (D.quotientFrobenius_bijective W hW)

/-- The projection onto the quotient isocrystal by a Frobenius-stable subspace. -/
def quotientπ : D ⟶ D.quotient W hW := ofHom W.mkQ fun _ => rfl

@[simp]
theorem quotientπ_hom : (D.quotientπ W hW).hom = W.mkQ := (rfl)

instance : Epi (D.quotientπ W hW) := ConcreteCategory.epi_of_surjective _ W.mkQ_surjective

end Stable

/-! ### Kernels and cokernels -/

section KernelCokernel

variable {D D' : FiniteIsocrystal.{u} σ} (f : D ⟶ D')

/-- The kernel of a morphism of finite isocrystals is Frobenius-stable. -/
theorem frobenius_mem_ker {x : D} (hx : x ∈ LinearMap.ker f.hom) :
    D.frobenius x ∈ LinearMap.ker f.hom := by
  simp_all

/-- The range of a morphism of finite isocrystals is Frobenius-stable. -/
theorem frobenius_mem_range {y : D'} (hy : y ∈ LinearMap.range f.hom) :
    D'.frobenius y ∈ LinearMap.range f.hom := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨D.frobenius x, f.hom_frobenius x⟩

@[reassoc (attr := simp)]
theorem subι_ker_comp : D.subι _ (fun _ => frobenius_mem_ker f) ≫ f = 0 := by
  ext x
  exact x.property

@[reassoc (attr := simp)]
theorem comp_quotientπ_range : f ≫ D'.quotientπ _ (fun _ => frobenius_mem_range f) = 0 := by
  ext x
  simp

/-- The kernel fork of a morphism of finite isocrystals: the inclusion of the sub-isocrystal on
the kernel of the underlying linear map. -/
@[expose]
def kernelFork : KernelFork f :=
  KernelFork.ofι (D.subι _ fun _ => frobenius_mem_ker f) (subι_ker_comp f)

@[simp]
theorem kernelFork_pt : (kernelFork f).pt = D.sub _ fun _ => frobenius_mem_ker f := (rfl)

@[simp]
theorem kernelFork_ι : (kernelFork f).ι = D.subι _ fun _ => frobenius_mem_ker f := (rfl)

/-- The kernel of the underlying linear map is a kernel in the category of finite isocrystals. -/
def kernelIsLimit : IsLimit (kernelFork f) :=
  KernelFork.IsLimit.ofι _ (subι_ker_comp f)
    (fun g hg => ofHom (LinearMap.codRestrict _ g.hom fun x => by
        simpa using LinearMap.congr_fun (congrArg Hom.hom hg) x)
      fun x => Subtype.ext (g.hom_frobenius x))
    (fun _ _ => hom_ext (LinearMap.subtype_comp_codRestrict _ _ _))
    (fun _ _ m hm => Mono.right_cancellation (f := D.subι _ _) m _ hm)

/-- The cokernel cofork of a morphism of finite isocrystals: the projection onto the quotient
isocrystal by the range of the underlying linear map. -/
@[expose]
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (D'.quotientπ _ fun _ => frobenius_mem_range f) (comp_quotientπ_range f)

@[simp]
theorem cokernelCofork_pt : (cokernelCofork f).pt = D'.quotient _ fun _ => frobenius_mem_range f :=
  (rfl)

@[simp]
theorem cokernelCofork_π : (cokernelCofork f).π = D'.quotientπ _ fun _ => frobenius_mem_range f :=
  (rfl)

/-- The quotient by the range of the underlying linear map is a cokernel in the category of
finite isocrystals. -/
def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ _ (comp_quotientπ_range f)
    (fun g hg => ofHom (D := D'.quotient _ fun _ => frobenius_mem_range f)
      ((LinearMap.range f.hom).liftQ g.hom <| by
        rintro _ ⟨x, rfl⟩
        simpa using LinearMap.congr_fun (congrArg Hom.hom hg) x)
      fun x => by
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        simp)
    (fun _ _ => hom_ext (Submodule.liftQ_mkQ _ _ _))
    (fun _ _ m hm => Epi.left_cancellation (f := D'.quotientπ _ _) m _ hm)

instance : HasKernels (FiniteIsocrystal.{u} σ) := ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

instance : HasCokernels (FiniteIsocrystal.{u} σ) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- A morphism of finite isocrystals is a monomorphism iff its underlying linear map is
injective. -/
theorem mono_iff_injective : Mono f ↔ Function.Injective f.hom := by
  refine ⟨fun _ => (injective_iff_map_eq_zero _).2 fun x hx => ?_,
    ConcreteCategory.mono_of_injective f⟩
  have h : D.subι _ (fun _ => frobenius_mem_ker f) = 0 :=
    (cancel_mono f).1 (by simp)
  simpa using LinearMap.congr_fun (congrArg Hom.hom h) ⟨x, hx⟩

/-- A morphism of finite isocrystals is an epimorphism iff its underlying linear map is
surjective. -/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f.hom := by
  refine ⟨fun _ => ?_, ConcreteCategory.epi_of_surjective f⟩
  have h : D'.quotientπ _ (fun _ => frobenius_mem_range f) = 0 :=
    (cancel_epi f).1 (by simp)
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  exact fun y => (Submodule.Quotient.mk_eq_zero _).1 <| by
    simpa using LinearMap.congr_fun (congrArg Hom.hom h) y

end KernelCokernel

section Preserves

variable {D D' : FiniteIsocrystal.{u} σ} (f : D ⟶ D')

-- The image of `kernelFork f` under the forgetful functor and Mathlib's concrete kernel cone of
-- the underlying linear map have the same point and inclusion by definition, so `Iso.refl` and
-- `rfl` compare them; the same holds for the cokernels below.
instance : PreservesLimit (parallelPair f 0) (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)) :=
  preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm
      (IsLimit.ofIsoLimit (ModuleCat.kernelIsLimit _) (Fork.ext (Iso.refl _) (by ext; rfl))))

instance :
    PreservesColimit (parallelPair f 0) (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)) :=
  preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit _)
        (Cofork.ext (Iso.refl _) (by ext; rfl))))

end Preserves

/-- The coimage-image comparison morphisms of finite isocrystals are isomorphisms: the forgetful
functor to `ModuleCat L` preserves kernels and cokernels, so it carries them to the comparison
isomorphisms of the abelian category `ModuleCat L`, and it reflects isomorphisms. -/
instance isIso_coimageImageComparison {D D' : FiniteIsocrystal.{u} σ} (f : D ⟶ D') :
    IsIso (Abelian.coimageImageComparison f) := by
  let F := forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)
  have : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso (Abelian.PreservesCoimageImageComparison.iso F f).hom]
    infer_instance
  exact isIso_of_reflects_iso _ F

/-- Finite isocrystals form an abelian category, with kernels and cokernels computed on the
underlying vector spaces. -/
noncomputable instance : Abelian (FiniteIsocrystal.{u} σ) :=
  Abelian.ofCoimageImageComparisonIsIso

end FiniteIsocrystal

end TauCeti
