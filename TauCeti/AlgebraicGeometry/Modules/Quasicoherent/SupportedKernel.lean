/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.Algebra.Category.ModuleCat.Kernels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Sections vanishing on an open subscheme

Let `j : V ⟶ Y` be an open immersion and `N` an `𝒪_Y`-module. The **supported kernel** of `N`
along `j` is the kernel of the unit `N ⟶ j_* (N|_V)` of the adjunction between restriction and
pushforward: its sections over an open `W` are the sections of `N` over `W` that vanish on
`W ∩ V`. The quotient of `N` by it is the image of `N` in `j_* (N|_V)`; for `N` the pullback of a
module along a base change, this quotient is the strict transform of the module.

When `j` is quasi-compact and `N` is quasi-coherent, both the supported kernel and the quotient
are quasi-coherent, because `j_* (N|_V)` is. If `W` is quasi-compact and `W ∩ V` is the union of
the basic opens of finitely many sections `a₁, …, aᵣ` of `𝒪_Y` over `W`, then the supported
kernel over `W` consists of the sections killed by a power of the ideal `(a₁, …, aᵣ)`: vanishing
on each `D(aᵢ)` means being killed by a power of `aᵢ`, and finite generation gives one power of
the ideal.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.supportedKernel N j`: the kernel of `N ⟶ j_* (N|_V)`, with
  inclusion `AlgebraicGeometry.Scheme.Modules.supportedKernelι N j`.
* `AlgebraicGeometry.Scheme.Modules.supportedQuotient N j`: the quotient of `N` by its supported
  kernel.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_supportedKernel` and
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_supportedQuotient`: for quasi-compact `j` and
  quasi-coherent `N`, both are quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.injective_supportedKernelι_app` and
  `AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff`: over any open `W`, the
  supported kernel is the submodule of sections of `N` vanishing on `j ''ᵁ (j ⁻¹ᵁ W)`.
* `AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_primaryComponent`:
  over a quasi-compact open whose intersection with `V` is cut out by finitely many sections, the
  supported kernel is the power torsion of the ideal they generate.

## References

* [Stacks, Lemma 26.24.1 (01LC)](https://stacks.math.columbia.edu/tag/01LC) for the kernel of
  `𝒪_Y ⟶ j_* 𝒪_V`.
* [Stacks, Lemma 47.9.1 (0A6R)](https://stacks.math.columbia.edu/tag/0A6R) for the comparison
  with power torsion.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {Y V : Scheme.{u}} (N : Y.Modules) (j : V ⟶ Y) [IsOpenImmersion j]

/-- The **supported kernel** of an `𝒪_Y`-module `N` along an open immersion `j : V ⟶ Y`: the
kernel of the unit `N ⟶ j_* (N|_V)`, the subsheaf of sections of `N` vanishing on `V`
(`AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff`). -/
def supportedKernel : Y.Modules :=
  kernel ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j))

/-- The inclusion of the supported kernel of `N` along `j` into `N`. -/
def supportedKernelι : N.supportedKernel j ⟶ N :=
  kernel.ι ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j))

/-- The quotient of an `𝒪_Y`-module `N` by its supported kernel along an open immersion `j`, the
module of strict transforms. -/
def supportedQuotient : Y.Modules :=
  cokernel (N.supportedKernelι j)

/-- The supported kernel is the kernel of the unit `N ⟶ j_* (N|_V)`. -/
theorem supportedKernel_def :
    N.supportedKernel j =
      kernel ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) :=
  (rfl)

/-- The quotient by the supported kernel is the cokernel of its inclusion. -/
theorem supportedQuotient_def : N.supportedQuotient j = cokernel (N.supportedKernelι j) :=
  (rfl)

/-- The supported kernel is killed by the unit `N ⟶ j_* (N|_V)`. -/
@[reassoc (attr := simp)]
theorem supportedKernelι_comp_unit :
    N.supportedKernelι j ≫ (restrictAdjunction j).unit.app N = 0 :=
  by exact kernel.condition _

instance mono_supportedKernelι :
    Mono (N.supportedKernelι j) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- **The supported kernel is quasi-coherent** for a quasi-compact open immersion and a
quasi-coherent module. -/
instance isQuasicoherent_supportedKernel
    [N.IsQuasicoherent] [QuasiCompact j] : (N.supportedKernel j).IsQuasicoherent :=
  have : ((pushforward j).obj (N.restrict j)).IsQuasicoherent := inferInstance
  isQuasicoherent_kernel (M := N) (N := (pushforward j).obj (N.restrict j))
    ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j))

/-- **The quotient by the supported kernel is quasi-coherent** for a quasi-compact open immersion
and a quasi-coherent module. -/
instance isQuasicoherent_supportedQuotient
    [N.IsQuasicoherent] [QuasiCompact j] : (N.supportedQuotient j).IsQuasicoherent :=
  inferInstanceAs (cokernel (N.supportedKernelι j)).IsQuasicoherent

/-! ### Sections of the supported kernel -/

/-- Taking sections over an open preserves kernels of `𝒪_Y`-modules. -/
private instance preservesLimit_sectionsFunctor (W : Y.Opens) {A B : Y.Modules} (f : A ⟶ B) :
    PreservesLimit (parallelPair f 0) (sectionsFunctor W) :=
  SheafOfModules.evaluationPreservesLimit _ _

/-- Over every open `W`, the inclusion of the supported kernel is injective on sections. -/
theorem injective_supportedKernelι_app (W : Y.Opens) :
    Function.Injective ((N.supportedKernelι j).app W) := by
  let φ : N ⟶ (pushforward j).obj (N.restrict j) := (restrictAdjunction j).unit.app N
  change Function.Injective ((sectionsFunctor W).map (kernel.ι φ)).hom
  rw [← kernelComparison_comp_ι, ← PreservesKernel.iso_hom, ModuleCat.hom_comp,
    LinearMap.coe_comp]
  exact ((ModuleCat.mono_iff_injective _).mp inferInstance).comp
    (PreservesKernel.iso (sectionsFunctor W) φ).toLinearEquiv.injective

/-- **The sections of the supported kernel.** Over an open `W`, a section of `N` comes from the
supported kernel exactly when it vanishes on `j ''ᵁ (j ⁻¹ᵁ W)`, the intersection of `W` with
the image of `j`. -/
theorem mem_range_supportedKernelι_app_iff
    {W : Y.Opens} (s : Γ(N, W)) :
    s ∈ Set.range ((N.supportedKernelι j).app W) ↔
      N.presheaf.map (homOfLE (j.image_preimage_le W)).op s = 0 := by
  let φ : N ⟶ (pushforward j).obj (N.restrict j) := (restrictAdjunction j).unit.app N
  change s ∈ Set.range ((sectionsFunctor W).map (kernel.ι φ)).hom ↔ _
  refine ⟨?_, fun hs ↦ (sectionsFunctor W).exists_map_kernel_ι_eq φ s hs⟩
  rintro ⟨t, rfl⟩
  have h : ((sectionsFunctor W).map (kernel.ι φ ≫ φ)).hom t =
      ((sectionsFunctor W).map 0).hom t := by
    rw [kernel.condition]
  simp only [Functor.map_comp, Functor.map_zero, ModuleCat.hom_comp, ModuleCat.hom_zero,
    LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact h

/-- **The supported kernel is power torsion.** Let `W` be a quasi-compact open of `Y` and `G` a
finite set of sections of `𝒪_Y` over `W` whose basic opens cover the intersection
`j ''ᵁ (j ⁻¹ᵁ W)` of `W` with the image of `j`. For quasi-coherent `N`, a section of `N` over `W`
comes from the supported kernel exactly when it is killed by a power of the ideal generated
by `G`. -/
theorem mem_range_supportedKernelι_app_iff_mem_primaryComponent
    [N.IsQuasicoherent] {W : Y.Opens} (hW : IsCompact (W : Set Y)) (G : Finset Γ(Y, W))
    (hG : j ''ᵁ (j ⁻¹ᵁ W) = ⨆ g : G, Y.basicOpen g.val) (s : Γ(N, W)) :
    s ∈ Set.range ((N.supportedKernelι j).app W) ↔
      s ∈ (Ideal.span (G : Set Γ(Y, W))).primaryComponent Γ(N, W) := by
  rw [mem_range_supportedKernelι_app_iff, Ideal.mem_primaryComponent_span_iff]
  have hle (g : G) : Y.basicOpen g.val ≤ j ''ᵁ (j ⁻¹ᵁ W) :=
    hG ▸ le_iSup (fun g : G ↦ Y.basicOpen g.val) g
  -- the restriction of `s` to `D(g)` factors through `j ''ᵁ (j ⁻¹ᵁ W)`
  have hres (g : G) : N.basicOpenRestrict g.val s = N.presheaf.map (homOfLE (hle g)).op
      (N.presheaf.map (homOfLE (j.image_preimage_le W)).op s) := by
    rw [basicOpenRestrict_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  refine ⟨fun hs g hg ↦ N.exists_pow_smul_eq_zero_of_isCompact hW g s
    (by rw [hres ⟨g, hg⟩, hs, map_zero]), fun h ↦ ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Y)
    (fun g : G ↦ Y.basicOpen g.val) _ (fun g ↦ homOfLE (hle g)) hG.le _ _ fun g ↦ ?_
  change N.presheaf.map _ _ = N.presheaf.map _ _
  rw [map_zero, ← hres, basicOpenRestrict_apply]
  -- `g` is invertible on `D(g)`, so a section killed by a power of `g` vanishes there
  obtain ⟨n, hn⟩ := h g.val g.property
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le g.val)).op g.val) :=
    Y.toRingedSpace.isUnit_res_basicOpen g.val
  have h' := congrArg (N.presheaf.map (homOfLE (Y.basicOpen_le g.val)).op) hn
  rw [Scheme.Modules.map_smul, map_zero, map_pow] at h'
  exact (hu.pow n).smul_eq_zero.mp h'

omit N in
/-- **The supported kernel of `𝒪_Y` is the ideal of the scheme-theoretic image.** For a
quasi-compact open immersion `j`, over an affine open `U` the sections of the supported kernel of
`𝒪_Y` along `j` are the elements of the ideal of `j.ker`, which cuts out the scheme-theoretic image
of `j`, the scheme-theoretic closure of `V`. -/
theorem mem_range_supportedKernelι_unit_app_iff
    [QuasiCompact j] (U : Y.affineOpens) (s : Γ(Y, U)) :
    s ∈ Set.range ((supportedKernelι (SheafOfModules.unit Y.ringCatSheaf) j).app U) ↔
      s ∈ j.ker.ideal U := by
  refine (mem_range_supportedKernelι_app_iff (SheafOfModules.unit Y.ringCatSheaf) j
    (W := U) s).trans ?_
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker,
    ← (ConcreteCategory.bijective_of_isIso (j.appIso (j ⁻¹ᵁ U)).inv).injective.eq_iff, map_zero,
    ← ConcreteCategory.comp_apply, Scheme.Hom.app_appIso_inv]
  rfl

end

end AlgebraicGeometry.Scheme.Modules
