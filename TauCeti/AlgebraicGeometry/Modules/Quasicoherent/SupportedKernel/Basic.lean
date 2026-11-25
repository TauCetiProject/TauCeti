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
public import TauCeti.AlgebraicGeometry.Modules.Unit
public import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Sections vanishing on an open subscheme

Let `j : V ⟶ Y` be an open immersion and `N` an `𝒪_Y`-module. The **supported kernel** of `N`
along `j` is the kernel of the unit `N ⟶ j_* (N|_V)` of the adjunction between restriction and
pushforward: its sections over an open `W` are the sections of `N` over `W` that vanish on
`W ∩ V`. The quotient of `N` by it is the image of `N` in `j_* (N|_V)`. When `N` is the pullback
`pr_X^* M` of a module `M` to `X ×_S S'` and `j` is the inclusion of the preimage `X ×_S φ⁻¹(U)`
of the witness open `U`, this quotient is the strict transform of `M`; this file does not make that
identification.

When `j` is quasi-compact and `N` is quasi-coherent, both the supported kernel and the quotient
are quasi-coherent, because `j_* (N|_V)` is. For quasi-coherent `N`, if `W` is quasi-compact and
`W ∩ V` is the union of the basic opens of finitely many sections `a₁, …, aᵣ` of `𝒪_Y` over `W`,
then the supported kernel over `W` consists of the sections killed by a power of the ideal
`(a₁, …, aᵣ)`: vanishing on each `D(aᵢ)` means being killed by a power of `aᵢ`, and finite
generation gives one power of the ideal.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.supportedKernel N j`: the kernel of `N ⟶ j_* (N|_V)`, with
  inclusion `AlgebraicGeometry.Scheme.Modules.supportedKernelι N j` and factorization
  `AlgebraicGeometry.Scheme.Modules.supportedKernelLift`.
* `AlgebraicGeometry.Scheme.Modules.supportedQuotient N j`: the quotient of `N` by its supported
  kernel, Mathlib's `CategoryTheory.Abelian.coimage` of `N ⟶ j_* (N|_V)`, with projection
  `AlgebraicGeometry.Scheme.Modules.supportedQuotientπ N j` and factorization
  `AlgebraicGeometry.Scheme.Modules.supportedQuotientDesc`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_supportedKernel` and
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_supportedQuotient`: for quasi-compact `j` and
  quasi-coherent `N`, both are quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.supportedKernelι_app_injective` and
  `AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff`: over any open `W`, the
  supported kernel is the submodule of sections of `N` vanishing on `j ''ᵁ (j ⁻¹ᵁ W)`.
* `AlgebraicGeometry.Scheme.Modules.supportedQuotientπ_app_eq_zero_iff`: over any open `W`, a
  section of `N` maps to zero in the supported quotient exactly when it comes from the supported
  kernel.
* `AlgebraicGeometry.Scheme.Modules.map_eq_zero_iff_mem_primaryComponent`: for quasi-coherent
  `N`, a section over a quasi-compact open `W` vanishes on the union of the basic opens of a
  finite set `G` of functions on `W` exactly when it is power torsion for the ideal of `G`.
* `AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_primaryComponent`:
  for quasi-coherent `N`, over a quasi-compact open whose intersection with `V` is the union of
  the basic opens of finitely many sections, the supported kernel is the power torsion of the
  ideal they generate; `mem_range_supportedKernelι_app_iff_mem_primaryComponent_of_inf_eq` is the
  same statement with `W ⊓ j.opensRange` in place of `j ''ᵁ (j ⁻¹ᵁ W)`.
* `AlgebraicGeometry.Scheme.Modules.isZero_supportedQuotient_of_isZero_restrict`: if `N|_V` is
  zero, so is the supported quotient.
* `AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_ker_ideal`: for
  quasi-compact `j`, over an affine open `U` the supported kernel of `𝒪_Y` has the same sections
  as the ideal of `j.ker`, which cuts out the scheme-theoretic image of `j`.

## References

* [Stacks, Lemma 26.24.1 (01LC)](https://stacks.math.columbia.edu/tag/01LC) for the
  quasi-coherence of `j_*`.
* [Stacks, Section 29.6 (01R5)](https://stacks.math.columbia.edu/tag/01R5), *Scheme theoretic
  image*, for the kernel of `𝒪_Y ⟶ j_* 𝒪_V`.
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

/-- The quotient of an `𝒪_Y`-module `N` by its supported kernel along an open immersion `j`:
Mathlib's `CategoryTheory.Abelian.coimage` of the unit `N ⟶ j_* (N|_V)`, the cokernel of
`AlgebraicGeometry.Scheme.Modules.supportedKernelι`. Its projection from `N` is
`AlgebraicGeometry.Scheme.Modules.supportedQuotientπ`, and
`CategoryTheory.Abelian.factorThruCoimage` is a monomorphism into `j_* (N|_V)` through which the
unit factors, so it is the image of `N` there.
When `N` is the pullback `pr_X^* M` of a module `M` to `X ×_S S'` and `j` is the inclusion of the
preimage `X ×_S φ⁻¹(U)` of the witness open `U`, it gives the strict transform of `M`. -/
abbrev supportedQuotient : Y.Modules :=
  Abelian.coimage ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j))

/-- The supported kernel is the kernel of the unit `N ⟶ j_* (N|_V)`. -/
theorem supportedKernel_def :
    N.supportedKernel j =
      kernel ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) :=
  (rfl)

/-- The supported kernel is killed by the unit `N ⟶ j_* (N|_V)`. -/
@[reassoc (attr := simp)]
theorem supportedKernelι_comp_unit :
    N.supportedKernelι j ≫ (restrictAdjunction j).unit.app N = 0 :=
  kernel.condition _

instance mono_supportedKernelι :
    Mono (N.supportedKernelι j) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- A morphism into `N` killed by the unit `N ⟶ j_* (N|_V)` factors through the supported
kernel. -/
def supportedKernelLift {M : Y.Modules} (f : M ⟶ N)
    (hf : f ≫ (restrictAdjunction j).unit.app N = 0) : M ⟶ N.supportedKernel j :=
  kernel.lift _ f hf

/-- The factorization through the supported kernel recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem supportedKernelLift_ι {M : Y.Modules} (f : M ⟶ N)
    (hf : f ≫ (restrictAdjunction j).unit.app N = 0) :
    N.supportedKernelLift j f hf ≫ N.supportedKernelι j = f :=
  kernel.lift_ι _ f hf

/-- The projection of `N` onto its quotient by the supported kernel along `j`, Mathlib's
`CategoryTheory.Abelian.coimage.π` of the unit `N ⟶ j_* (N|_V)`. -/
def supportedQuotientπ : N ⟶ N.supportedQuotient j :=
  Abelian.coimage.π _

/-- The projection onto the supported quotient is Mathlib's `CategoryTheory.Abelian.coimage.π`
of the unit `N ⟶ j_* (N|_V)`. -/
theorem supportedQuotientπ_def :
    N.supportedQuotientπ j =
      Abelian.coimage.π ((restrictAdjunction j).unit.app N :
        N ⟶ (pushforward j).obj (N.restrict j)) :=
  (rfl)

instance epi_supportedQuotientπ :
    Epi (N.supportedQuotientπ j) :=
  inferInstanceAs (Epi (Abelian.coimage.π _))

/-- The supported kernel is killed by the projection onto the supported quotient. -/
@[reassoc (attr := simp)]
theorem supportedKernelι_comp_supportedQuotientπ :
    N.supportedKernelι j ≫ N.supportedQuotientπ j = 0 :=
  cokernel.condition _

/-- A morphism out of `N` killing the supported kernel factors through the supported quotient. -/
def supportedQuotientDesc {P : Y.Modules} (g : N ⟶ P) (hg : N.supportedKernelι j ≫ g = 0) :
    N.supportedQuotient j ⟶ P :=
  cokernel.desc _ g hg

/-- The factorization through the supported quotient recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem supportedQuotientπ_desc {P : Y.Modules} (g : N ⟶ P)
    (hg : N.supportedKernelι j ≫ g = 0) :
    N.supportedQuotientπ j ≫ N.supportedQuotientDesc j g hg = g :=
  cokernel.π_desc _ g hg

/-- The projection onto the supported quotient, followed by the monomorphism
`CategoryTheory.Abelian.factorThruCoimage` into `j_* (N|_V)`, is the unit `N ⟶ j_* (N|_V)`. -/
@[reassoc (attr := simp)]
theorem supportedQuotientπ_comp_factorThruCoimage :
    N.supportedQuotientπ j ≫ Abelian.factorThruCoimage
      ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) =
      (restrictAdjunction j).unit.app N :=
  Abelian.coimage.fac _

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

/-- Over every open `W`, the inclusion of the supported kernel is injective on sections. -/
theorem supportedKernelι_app_injective (W : Y.Opens) :
    Function.Injective ((N.supportedKernelι j).app W) := fun s t h ↦
  (ModuleCat.mono_iff_injective _).mp ((sectionsFunctor W).map_mono (N.supportedKernelι j))
    (by rwa [sectionsFunctor_map_hom_apply, sectionsFunctor_map_hom_apply])

/-- **The sections of the supported kernel.** Over an open `W`, a section of `N` comes from the
supported kernel exactly when it vanishes on `j ''ᵁ (j ⁻¹ᵁ W)`, the intersection of `W` with
the image of `j`. -/
theorem mem_range_supportedKernelι_app_iff
    {W : Y.Opens} (s : Γ(N, W)) :
    s ∈ Set.range ((N.supportedKernelι j).app W) ↔
      N.presheaf.map (homOfLE (j.image_preimage_le W)).op s = 0 := by
  let φ : N ⟶ (pushforward j).obj (N.restrict j) := (restrictAdjunction j).unit.app N
  have hφ : N.presheaf.map (homOfLE (j.image_preimage_le W)).op s = φ.app W s := by
    rw [restrictAdjunction_unit_app_app]
    -- the section types of `N` and of the source `(𝟭 _).obj N` of the unit differ in how they
    -- are written
    rfl
  rw [hφ]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, supportedKernelι_comp_unit, Hom.zero_app]
    -- the zero morphism sends `t` to zero
    rfl
  · obtain ⟨t, ht⟩ := (sectionsFunctor W).exists_map_kernel_ι_eq φ s
      (by rwa [sectionsFunctor_map_hom_apply])
    exact ⟨t, (sectionsFunctor_map_hom_apply W (kernel.ι φ) t).symm.trans ht⟩

/-- **The kernel of the projection onto the supported quotient.** Over an open `W`, a section of
`N` maps to zero in the supported quotient exactly when it comes from the supported kernel. -/
theorem supportedQuotientπ_app_eq_zero_iff {W : Y.Opens} (s : Γ(N, W)) :
    (N.supportedQuotientπ j).app W s = 0 ↔ s ∈ Set.range ((N.supportedKernelι j).app W) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (sectionsFunctor W).exists_map_kernel_ι_eq
      ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) s (by
        rw [sectionsFunctor_map_hom_apply, ← supportedQuotientπ_comp_factorThruCoimage,
          Hom.comp_app, ConcreteCategory.comp_apply, h, map_zero]
        -- the zero sections of `j_* (N|_V)` over `W` are written in two ways
        rfl)
    exact ⟨t, (sectionsFunctor_map_hom_apply W (kernel.ι _) t).symm.trans ht⟩
  · rintro ⟨t, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, supportedKernelι_comp_supportedQuotientπ,
      Hom.zero_app]
    -- the zero morphism sends `t` to zero
    rfl

/-- **Sections vanishing on a union of basic opens are power torsion.** Let `W` be a
quasi-compact open of `Y` and `G` a finite set of sections of `𝒪_Y` over `W`. For quasi-coherent
`N`, a section of `N` over `W` vanishes on the union of the basic opens of `G` exactly when it is
killed by a power of the ideal generated by `G`. -/
theorem map_eq_zero_iff_mem_primaryComponent [N.IsQuasicoherent] {W : Y.Opens}
    (hW : IsCompact (W : Set Y)) (G : Finset Γ(Y, W)) (s : Γ(N, W)) :
    N.presheaf.map (homOfLE (iSup_le fun g : G ↦ Y.basicOpen_le g.val)).op s = 0 ↔
      s ∈ (Ideal.span (G : Set Γ(Y, W))).primaryComponent Γ(N, W) := by
  rw [Ideal.mem_primaryComponent_span_iff]
  have hle (g : G) : Y.basicOpen g.val ≤ ⨆ g : G, Y.basicOpen g.val :=
    le_iSup (fun g : G ↦ Y.basicOpen g.val) g
  -- the restriction of `s` to `D(g)` factors through the union of the basic opens
  have hres (g : G) : N.basicOpenRestrict g.val s = N.presheaf.map (homOfLE (hle g)).op
      (N.presheaf.map (homOfLE (iSup_le fun g : G ↦ Y.basicOpen_le g.val)).op s) := by
    simp only [basicOpenRestrict_apply, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
  refine ⟨fun hs g hg ↦ N.exists_pow_smul_eq_zero_of_isCompact hW g s
    (by rw [hres ⟨g, hg⟩, hs, map_zero]), fun h ↦ ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Y)
    (fun g : G ↦ Y.basicOpen g.val) _ (fun g ↦ homOfLE (hle g)) le_rfl _ _ fun g ↦ ?_
  -- The restriction maps of the sheaf `⟨N.presheaf, N.isSheaf⟩` are those of `N`.
  change N.presheaf.map _ _ = N.presheaf.map _ _
  rw [map_zero, ← hres, basicOpenRestrict_apply]
  -- `g` is invertible on `D(g)`, so a section killed by a power of `g` vanishes there
  obtain ⟨n, hn⟩ := h g.val g.property
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le g.val)).op g.val) :=
    Y.toRingedSpace.isUnit_res_basicOpen g.val
  have h' := congrArg (N.presheaf.map (homOfLE (Y.basicOpen_le g.val)).op) hn
  rw [Scheme.Modules.map_smul, map_zero, map_pow] at h'
  exact (hu.pow n).smul_eq_zero.mp h'

/-- **The supported kernel is power torsion.** Let `W` be a quasi-compact open of `Y` and `G` a
finite set of sections of `𝒪_Y` over `W` whose basic opens have union equal to the intersection
`j ''ᵁ (j ⁻¹ᵁ W)` of `W` with the image of `j`. For quasi-coherent `N`, a section of `N` over `W`
comes from the supported kernel exactly when it is killed by a power of the ideal generated
by `G`. -/
theorem mem_range_supportedKernelι_app_iff_mem_primaryComponent
    [N.IsQuasicoherent] {W : Y.Opens} (hW : IsCompact (W : Set Y)) (G : Finset Γ(Y, W))
    (hG : j ''ᵁ (j ⁻¹ᵁ W) = ⨆ g : G, Y.basicOpen g.val) (s : Γ(N, W)) :
    s ∈ Set.range ((N.supportedKernelι j).app W) ↔
      s ∈ (Ideal.span (G : Set Γ(Y, W))).primaryComponent Γ(N, W) := by
  rw [mem_range_supportedKernelι_app_iff, ← N.map_eq_zero_iff_mem_primaryComponent hW G s]
  -- both sides restrict `s` to the same open, written as `j ''ᵁ (j ⁻¹ᵁ W)` and via `G`
  generalize_proofs h₁ h₂
  revert h₁
  rw [hG]
  exact fun _ ↦ Iff.rfl

/-- **The supported kernel is power torsion**, stated with the open `W ⊓ j.opensRange`. Let `W` be
a quasi-compact open of `Y` and `G` a finite set of sections of `𝒪_Y` over `W` whose basic opens
have union the intersection `W ⊓ j.opensRange` of `W` with the image of `j`. For quasi-coherent
`N`, a section of `N` over `W` comes from the supported kernel exactly when it is killed by a power
of the ideal generated by `G`. -/
theorem mem_range_supportedKernelι_app_iff_mem_primaryComponent_of_inf_eq
    [N.IsQuasicoherent] {W : Y.Opens} (hW : IsCompact (W : Set Y))
    (G : Finset Γ(Y, W)) (hG : W ⊓ j.opensRange = ⨆ g : G, Y.basicOpen g.val) (s : Γ(N, W)) :
    s ∈ Set.range ((N.supportedKernelι j).app W) ↔
      s ∈ (Ideal.span (G : Set Γ(Y, W))).primaryComponent Γ(N, W) := by
  refine N.mem_range_supportedKernelι_app_iff_mem_primaryComponent _ hW G ?_ s
  rw [← hG, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]

/-- **A module vanishing on `V` has zero supported quotient**: if `N|_V` is zero, every section of
`N` vanishes on `V`, so the supported kernel is all of `N`. -/
theorem isZero_supportedQuotient_of_isZero_restrict (h : IsZero (N.restrict j)) :
    IsZero (N.supportedQuotient j) := by
  have h₀ : ((restrictAdjunction j).unit.app N : N ⟶ (pushforward j).obj (N.restrict j)) = 0 :=
    ((pushforward j).map_isZero h).eq_of_tgt _ _
  have : IsIso (kernel.ι ((restrictAdjunction j).unit.app N :
      N ⟶ (pushforward j).obj (N.restrict j))) :=
    KernelFork.IsLimit.isIso_ι _ (limit.isLimit _) h₀
  exact isZero_cokernel_of_epi _

omit N in
/-- **The supported kernel of `𝒪_Y` is the ideal of the scheme-theoretic image.** For a
quasi-compact open immersion `j`, over an affine open `U` the sections of the supported kernel of
`𝒪_Y` along `j` are the elements of the ideal of `j.ker`, which cuts out the scheme-theoretic image
of `j`, the scheme-theoretic closure of `V`. -/
theorem mem_range_supportedKernelι_app_iff_mem_ker_ideal
    [QuasiCompact j] (U : Y.affineOpens) (s : Γ(Y, U)) :
    s ∈ Set.range ((supportedKernelι (unit Y) j).app U) ↔ s ∈ j.ker.ideal U := by
  refine (mem_range_supportedKernelι_app_iff (unit Y) j (W := U) s).trans ?_
  rw [presheaf_unit_map_apply, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.app_eq_zero_iff]
  -- `s` is the same element, typed as a section of `𝒪_Y` or of the module `𝒪_Y`
  exact Iff.rfl

end

end AlgebraicGeometry.Scheme.Modules
