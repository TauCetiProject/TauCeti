/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.ShortExact

import TauCeti.Algebra.Module.PseudoCoherent.TwoOutOfThree
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
import TauCeti.CategoryTheory.ObjectProperty

/-!
# Two-out-of-three and retract stability for pseudo-coherent module sheaves

In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in the abelian category `X.Modules` of all
`𝒪_X`-modules on a scheme `X`, if any two of `M₁`, `M₂`, `M₃` are pseudo-coherent then so is the
third, without assuming quasi-coherence of the remaining term in advance. Moreover, pseudo-coherent
`𝒪_X`-modules are stable under retracts (direct summands) and closed under finite direct sums and
finite products.

Because `IsQuasicoherent` is closed in `X.Modules` under ambient kernels
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel`), cokernels
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`), and extensions
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_X₂_of_shortExact`), quasi-coherence of the third
term in any short exact sequence (or of any retract, realized as the kernel of an idempotent)
follows from quasi-coherence of the other terms. Once `M₁` is known to be quasi-coherent, Serre's
affine vanishing theorem ensures that sections over every affine open `U` preserve exactness of
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` (`AlgebraicGeometry.Scheme.Modules.shortExact_sections_of_isAffineOpen`).
Applying the module-level two-out-of-three and retract theorems
(`TauCeti.Huber.IsPseudoCoherentOver.extension`, `cokernel`, `kernel`, `of_retract`) on every
affine open and assembling via
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_forall_affineOpens` completes the proof.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent`: `IsPseudoCoherent` as an `ObjectProperty`
  on `X.Modules`.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.extension`,
  `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.cokernel`,
  `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.kernel`: two-out-of-three for pseudo-coherent
  module sheaves along short exact sequences in `X.Modules`.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.kernel_of_epi` and
  `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.cokernel_of_mono`: kernels of epimorphisms and
  cokernels of monomorphisms between pseudo-coherent sheaves are pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.of_retract`: retracts (direct summands) of
  pseudo-coherent sheaves are pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.biprod`,
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_biprod_iff`,
  `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.biproduct`,
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_biproduct_iff`: closure under binary and finite
  biproducts, together with `IsStableUnderRetracts`, `ContainsZero`, `IsClosedUnderExtensions`,
  `IsClosedUnderBinaryProducts`, and `IsClosedUnderFiniteProducts` instances on
  `isPseudoCoherent X`.

## References

* The Stacks Project, Lemma 36.10.3 (Tag 08E8) and Lemma 36.10.4 (Tag 08E9).
-/

public section

open CategoryTheory Limits ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- `IsPseudoCoherent` viewed as an `ObjectProperty` on `X.Modules`. -/
abbrev isPseudoCoherent (X : Scheme.{u}) : ObjectProperty X.Modules :=
  IsPseudoCoherent

/-- Evaluation of a morphism of `𝒪_X`-modules on sections over `U`, as a `Γ(X, U)`-linear map. -/
private def appLinear {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := φ.app_smul

private theorem shortExact_appLinear_of_isAffineOpen {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (appLinear S.f U) ∧
      Function.Exact (appLinear S.f U) (appLinear S.g U) ∧
      Function.Surjective (appLinear S.g U) :=
  shortExact_sections_of_isAffineOpen hS U hU

section ShortExact

variable {X : Scheme.{u}}

/-- **Extensions of pseudo-coherent sheaves are pseudo-coherent.** In a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in `X.Modules`, if `M₁` and `M₃` are pseudo-coherent then `M₂` is
pseudo-coherent (Stacks, Lemma 36.10.4, Tag 08E9). -/
theorem IsPseudoCoherent.extension {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsPseudoCoherent) (h₃ : S.X₃.IsPseudoCoherent) :
    S.X₂.IsPseudoCoherent := by
  have : S.X₁.IsQuasicoherent := h₁.isQuasicoherent
  have : S.X₃.IsQuasicoherent := h₃.isQuasicoherent
  refine (isPseudoCoherent_iff_forall_affineOpens S.X₂).mpr
    ⟨isQuasicoherent_X₂_of_shortExact hS, fun U ↦ ?_⟩
  obtain ⟨hf, hfg, hg⟩ := shortExact_appLinear_of_isAffineOpen hS U.2
  exact TauCeti.Huber.IsPseudoCoherentOver.extension hf hfg hg
    (h₁.isPseudoCoherentOver_sections U.2) (h₃.isPseudoCoherentOver_sections U.2)

/-- **Cokernels of monomorphisms between pseudo-coherent sheaves are pseudo-coherent.** In a short
exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in `X.Modules`, if `M₁` and `M₂` are pseudo-coherent then
`M₃` is pseudo-coherent (Stacks, Lemma 36.10.4, Tag 08E9). -/
theorem IsPseudoCoherent.cokernel {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsPseudoCoherent) (h₂ : S.X₂.IsPseudoCoherent) :
    S.X₃.IsPseudoCoherent := by
  have : S.X₁.IsQuasicoherent := h₁.isQuasicoherent
  have hqc₃ : S.X₃.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit_cokernelCofork
      hS.gIsCokernel h₁.isQuasicoherent h₂.isQuasicoherent
  refine (isPseudoCoherent_iff_forall_affineOpens S.X₃).mpr ⟨hqc₃, fun U ↦ ?_⟩
  obtain ⟨hf, hfg, hg⟩ := shortExact_appLinear_of_isAffineOpen hS U.2
  exact TauCeti.Huber.IsPseudoCoherentOver.cokernel hf hfg hg
    (fun _ ↦ by simpa using h₁.isPseudoCoherentOver_sections U.2)
    (h₂.isPseudoCoherentOver_sections U.2)

/-- **Kernels of epimorphisms between pseudo-coherent sheaves are pseudo-coherent.** In a short
exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in `X.Modules`, if `M₂` and `M₃` are pseudo-coherent then
`M₁` is pseudo-coherent (Stacks, Lemma 36.10.4, Tag 08E9). -/
theorem IsPseudoCoherent.kernel {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : S.X₂.IsPseudoCoherent) (h₃ : S.X₃.IsPseudoCoherent) :
    S.X₁.IsPseudoCoherent := by
  have : S.X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
      hS.fIsKernel h₂.isQuasicoherent h₃.isQuasicoherent
  refine (isPseudoCoherent_iff_forall_affineOpens S.X₁).mpr ⟨‹_›, fun U ↦ ?_⟩
  obtain ⟨hf, hfg, hg⟩ := shortExact_appLinear_of_isAffineOpen hS U.2
  exact TauCeti.Huber.IsPseudoCoherentOver.kernel hf hfg hg
    (h₂.isPseudoCoherentOver_sections U.2)
    (by simpa using h₃.isPseudoCoherentOver_sections U.2)

/-- The kernel of an epimorphism between pseudo-coherent `𝒪_X`-modules is pseudo-coherent
(Stacks, Lemma 36.10.4, Tag 08E9). -/
theorem IsPseudoCoherent.kernel_of_epi {F G : X.Modules} (f : F ⟶ G) [Epi f]
    (hF : F.IsPseudoCoherent) (hG : G.IsPseudoCoherent) :
    (Limits.kernel f).IsPseudoCoherent :=
  IsPseudoCoherent.kernel
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel
        (ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f))
        (Limits.kernelIsKernel f))
      inferInstance inferInstance)
    hF hG

/-- The cokernel of a monomorphism between pseudo-coherent `𝒪_X`-modules is pseudo-coherent
(Stacks, Lemma 36.10.4, Tag 08E9). -/
theorem IsPseudoCoherent.cokernel_of_mono {F G : X.Modules} (f : F ⟶ G) [Mono f]
    (hF : F.IsPseudoCoherent) (hG : G.IsPseudoCoherent) :
    (Limits.cokernel f).IsPseudoCoherent :=
  IsPseudoCoherent.cokernel
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel
        (ShortComplex.mk f (Limits.cokernel.π f) (Limits.cokernel.condition f))
        (Limits.cokernelIsCokernel f))
      inferInstance inferInstance)
    hF hG

/-- Pseudo-coherent `𝒪_X`-modules are closed under extensions in `X.Modules`
(Stacks, Lemma 36.10.4, Tag 08E9). -/
instance isClosedUnderExtensions_isPseudoCoherent (X : Scheme.{u}) :
    (isPseudoCoherent X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := IsPseudoCoherent.extension hS h₁ h₃

end ShortExact

section RetractAndProducts

variable {X : Scheme.{u}}

/-- **A retract (direct summand) of a pseudo-coherent sheaf is pseudo-coherent**
(Stacks, Lemma 36.10.3, Tag 08E8). Quasi-coherence of `F` is deduced automatically by realizing `F`
as the kernel of the complementary idempotent `𝟙 G - r.r ≫ r.i`. -/
theorem IsPseudoCoherent.of_retract {F G : X.Modules} (r : Retract F G)
    (hG : G.IsPseudoCoherent) : F.IsPseudoCoherent := by
  let hk : IsLimit
      (KernelFork.ofι r.i (f := 𝟙 G - r.r ≫ r.i) (by simp [reassoc_of% r.retract])) :=
    KernelFork.IsLimit.ofι _ _ (fun g' _ ↦ g' ≫ r.r)
      (fun g' hg' ↦ (sub_eq_zero.mp (by simpa using hg')).symm)
      (fun g' _ m hm ↦ by rw [← hm, Category.assoc, r.retract, Category.comp_id])
  have hqc : F.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork hk
      hG.isQuasicoherent hG.isQuasicoherent
  refine (isPseudoCoherent_iff_forall_affineOpens F).mpr ⟨hqc, fun U ↦ ?_⟩
  have hri : appLinear r.r U.1 ∘ₗ appLinear r.i U.1 = LinearMap.id := by
    ext x
    change (r.i ≫ r.r).app U.1 x = x
    simp [r.retract]
  exact TauCeti.Huber.IsPseudoCoherentOver.of_retract hri (hG.isPseudoCoherentOver_sections U.2)

/-- Pseudo-coherent `𝒪_X`-modules are stable under retracts (Stacks, Lemma 36.10.3, Tag 08E8). -/
instance isStableUnderRetracts_isPseudoCoherent (X : Scheme.{u}) :
    (isPseudoCoherent X).IsStableUnderRetracts where
  of_retract r hG := hG.of_retract r

/-- The zero `𝒪_X`-module is pseudo-coherent. -/
instance containsZero_isPseudoCoherent (X : Scheme.{u}) :
    (isPseudoCoherent X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsPseudoCoherent.of_isZero (isZero_zero _)⟩

/-- The direct sum of two pseudo-coherent `𝒪_X`-modules is pseudo-coherent
(Stacks, Lemma 36.10.3, Tag 08E8). -/
theorem IsPseudoCoherent.biprod {F G : X.Modules} (hF : F.IsPseudoCoherent)
    (hG : G.IsPseudoCoherent) : (F ⊞ G).IsPseudoCoherent :=
  (isPseudoCoherent X).prop_biprod hF hG

/-- If `F ⊞ G` is pseudo-coherent, then `F` is pseudo-coherent
(Stacks, Lemma 36.10.3, Tag 08E8). -/
theorem IsPseudoCoherent.of_biprod_left {F G : X.Modules} (h : (F ⊞ G).IsPseudoCoherent) :
    F.IsPseudoCoherent :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_left (isPseudoCoherent X) h

/-- If `F ⊞ G` is pseudo-coherent, then `G` is pseudo-coherent
(Stacks, Lemma 36.10.3, Tag 08E8). -/
theorem IsPseudoCoherent.of_biprod_right {F G : X.Modules} (h : (F ⊞ G).IsPseudoCoherent) :
    G.IsPseudoCoherent :=
  ObjectProperty.IsStableUnderRetracts.of_biprod_right (isPseudoCoherent X) h

/-- A binary biproduct `F ⊞ G` of `𝒪_X`-modules is pseudo-coherent if and only if both `F` and `G`
are pseudo-coherent (Stacks, Lemma 36.10.3, Tag 08E8). -/
@[simp]
theorem isPseudoCoherent_biprod_iff {F G : X.Modules} :
    (F ⊞ G).IsPseudoCoherent ↔ F.IsPseudoCoherent ∧ G.IsPseudoCoherent :=
  ⟨fun h ↦ ⟨h.of_biprod_left, h.of_biprod_right⟩, fun ⟨hF, hG⟩ ↦ hF.biprod hG⟩

/-- Pseudo-coherent `𝒪_X`-modules are closed under binary products. -/
instance isClosedUnderBinaryProducts_isPseudoCoherent (X : Scheme.{u}) :
    (isPseudoCoherent X).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ hF hG ↦ hF.biprod hG

/-- Pseudo-coherent `𝒪_X`-modules are closed under finite products. -/
instance isClosedUnderFiniteProducts_isPseudoCoherent (X : Scheme.{u}) :
    (isPseudoCoherent X).IsClosedUnderFiniteProducts := .mk'

/-- A finite biproduct of pseudo-coherent `𝒪_X`-modules is pseudo-coherent. -/
theorem IsPseudoCoherent.biproduct {J : Type*} [Finite J] {f : J → X.Modules} [HasBiproduct f]
    (h : ∀ j, (f j).IsPseudoCoherent) : (⨁ f).IsPseudoCoherent :=
  ((isPseudoCoherent X).prop_product h).of_iso (biproduct.isoProduct f).symm

/-- Every summand of a pseudo-coherent biproduct of `𝒪_X`-modules is pseudo-coherent. -/
theorem IsPseudoCoherent.of_biproduct {J : Type*} {f : J → X.Modules} [HasBiproduct f]
    (h : (⨁ f).IsPseudoCoherent) (j : J) : (f j).IsPseudoCoherent :=
  ObjectProperty.IsStableUnderRetracts.of_biproduct (isPseudoCoherent X) f h j

/-- A finite biproduct `⨁ f` of `𝒪_X`-modules is pseudo-coherent if and only if every summand `f j`
is pseudo-coherent. -/
@[simp]
theorem isPseudoCoherent_biproduct_iff {J : Type*} [Finite J] {f : J → X.Modules} [HasBiproduct f] :
    (⨁ f).IsPseudoCoherent ↔ ∀ j, (f j).IsPseudoCoherent :=
  ⟨fun h j ↦ h.of_biproduct j, IsPseudoCoherent.biproduct⟩

end RetractAndProducts

end

end AlgebraicGeometry.Scheme.Modules
