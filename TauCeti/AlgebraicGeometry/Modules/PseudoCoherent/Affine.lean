/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
import TauCeti.Algebra.Module.PseudoCoherent.Descent
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Images
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Affine characterization of pseudo-coherent module sheaves

An `𝒪_X`-module `F` on a scheme `X` is pseudo-coherent
(`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent`) if and only if `F` is quasi-coherent and,
for every affine open `U` of `X`, the `Γ(X, U)`-module `Γ(F, U)` is pseudo-coherent
(`TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤`). Equivalently, it suffices to check
pseudo-coherence of `Γ(F, U i)` on any cover of `X` by affine opens `U i`. On an affine scheme `X`,
`F` is pseudo-coherent if and only if `F` admits a global resolution by free `𝒪_X`-modules of
finite rank (`AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution`).

To extract an algebraic resolution from a sheaf resolution on `Spec R`, we first show that taking
global sections preserves exactness of any `ShortComplex (Spec R).Modules` whose first two terms
are quasi-coherent (`TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent`).
Applying this degree-by-degree to a finite free resolution `P ⟶ F[0]` on `Spec R` produces a
coordinate resolution of `Γ(F, ⊤)` over `R`. On an arbitrary scheme `X` and an affine open `U`, any
family of open subsets carrying finite free resolutions of `F` refines to a standard open cover of
`U` by basic opens `X.basicOpen f`; the sections over each `X.basicOpen f` are pseudo-coherent by
the spectrum calculation, and `TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan'` descends
pseudo-coherence back to `Γ(F, U)`. Conversely, when `F` is quasi-coherent and `Γ(F, U)` is
pseudo-coherent over `Γ(X, U)`, the tilde functor carries a coordinate resolution of `Γ(F, U)` to a
finite free resolution of `F|_U`.

Quasi-coherence cannot be omitted from the affine-open criterion: over the spectrum of any local
integral domain `R` that is not a field (for example, any discrete valuation ring), the subsheaf of
`𝒪_{Spec R}` vanishing at the closed point and equal to `𝒪_{Spec R}` on proper opens has free
sections of rank `0` or `1` over every affine open, hence pseudo-coherent sections everywhere, yet
fails to be quasi-coherent and is therefore not pseudo-coherent.

## Main results

* `TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent`: global sections on
  `Spec R` preserve exactness of short complexes whose first two terms are quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution.isPseudoCoherentOver_moduleSpecΓ`: a
  finite free resolution on `Spec R` gives a pseudo-coherent module of global sections.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.isPseudoCoherentOver_sections`: sections of a
  pseudo-coherent sheaf over any affine open `U` are pseudo-coherent over `Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_forall_affineOpens` and
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_of_iSup_eq_top`: characterization of
  pseudo-coherent module sheaves on affine opens and on affine open covers.
* `AlgebraicGeometry.Scheme.Modules.hasFiniteFreeResolution_iff_isPseudoCoherent`: on an affine
  scheme, local finite free resolutions lift to a global finite free resolution.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.of_isFiniteLocallyFree`: finite locally free
  sheaves are pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.exists_not_isPseudoCoherent_of_forall_affineOpens`: negative
  control showing that quasi-coherence is indispensable in the affine-open characterization.

## References

* The Stacks Project, Section 36.10 (Tag 08E4), Lemma 36.10.1 (Tag 08E5), and
  Lemma 36.10.2 (Tag 08E7).
-/

public section

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Taking global sections on `Spec R` preserves an exact short complex in `(Spec R).Modules` as
soon as its first two terms are quasi-coherent; no condition on `S.X₃` is required. -/
theorem _root_.TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {R : CommRingCat.{u}} {S : ShortComplex (Spec R).Modules} (hS : S.Exact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).Exact := by
  let F := moduleSpecΓFunctor (R := R)
  have : F.Additive := F.additive_of_preserves_binary_products
  have : (Abelian.image S.f).IsQuasicoherent :=
    inferInstanceAs (kernel (cokernel.π S.f)).IsQuasicoherent
  have : Epi (F.map (Abelian.factorThruImage S.f)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (TauCeti.AlgebraicGeometry.moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
        (Abelian.factorThruImage S.f))
  let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  let φ : S.map F ⟶ T.map F :=
    { τ₁ := F.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [T]
        rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (((S.exact_iff_exact_image_ι).1 hS).map_of_mono_of_preservesKernel F
      inferInstance inferInstance)

section Spec

variable {R : CommRingCat.{u}}

/-- A sheaf on `Spec R` with a global finite free resolution has pseudo-coherent global sections
over `R` (Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem HasFiniteFreeResolution.isPseudoCoherentOver_moduleSpecΓ {F : (Spec R).Modules}
    (h : F.HasFiniteFreeResolution) :
    TauCeti.Huber.IsPseudoCoherentOver R ((moduleSpecΓFunctor (R := R)).obj F) ⊤ := by
  have : F.IsQuasicoherent := h.isPseudoCoherent.isQuasicoherent
  obtain ⟨P, π, hP, hπ⟩ := hasFiniteFreeResolution_iff.mp h
  have hqc (n : ℕ) : (P.X n).IsQuasicoherent := by
    obtain ⟨ι, _, ⟨e⟩⟩ := hP n
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm inferInstance
  let G := moduleSpecΓFunctor (R := R)
  have hcoord (n : ℕ) : ∃ k : ℕ, Nonempty ((Fin k → R) ≃ₗ[R] G.obj (P.X n)) := by
    obtain ⟨ι, _, ⟨e⟩⟩ := hP n
    have := Fintype.ofFinite ι
    let e_mod : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι →₀ R) :=
      (Finsupp.linearEquivFunOnFinite R R (Fin (Fintype.card ι))).symm.trans
        (Finsupp.domLCongr (Fintype.equivFin ι).symm)
    let e_Γ : ModuleCat.of R (ι →₀ R) ≅ G.obj (P.X n) :=
      (tilde.toTildeΓNatIso (R := R)).app (ModuleCat.of R (ι →₀ R)) ≪≫
        G.mapIso (tildeFinsupp ι ≪≫ e.symm)
    exact ⟨Fintype.card ι, ⟨e_mod.trans e_Γ.toLinearEquiv⟩⟩
  choose k hk using hcoord
  let e (n : ℕ) : (Fin (k n) → R) ≃ₗ[R] G.obj (P.X n) := (hk n).some
  let ε : (Fin (k 0) → R) →ₗ[R] G.obj F := (G.map (π.f 0)).hom ∘ₗ (e 0).toLinearMap
  let d (i : ℕ) : (Fin (k (i + 1)) → R) →ₗ[R] (Fin (k i) → R) :=
    ((e i).symm.toLinearMap ∘ₗ (G.map (P.d (i + 1) i)).hom) ∘ₗ (e (i + 1)).toLinearMap
  have : QuasiIsoAt π 0 := hπ.1 0
  let S₀ : ShortComplex (Spec R).Modules :=
    ShortComplex.mk (P.d 1 0) (π.f 0) (by rw [← π.comm 1 0, single_obj_d, comp_zero])
  obtain ⟨hS₀_ex, hπ₀_epi⟩ :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel S₀).mpr
      ⟨P.isColimitCokernelCoforkOfQuasiIsoAt π⟩
  have : Epi (π.f 0) := hπ₀_epi
  have : (P.X 0).IsQuasicoherent := hqc 0
  have : (((ChainComplex.single₀ (Spec R).Modules).obj F).X 0).IsQuasicoherent :=
    ‹F.IsQuasicoherent›
  have hε : Function.Surjective ε :=
    (TauCeti.AlgebraicGeometry.moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
      (π.f 0)).comp (e 0).surjective
  refine (TauCeti.Huber.isPseudoCoherentOver_iff R (G.obj F) ⊤).mpr ⟨k, d, ε, hε, fun _ ↦ ?_,
    fun i _ ↦ ?_⟩
  · have : S₀.X₁.IsQuasicoherent := hqc 1
    have : S₀.X₂.IsQuasicoherent := hqc 0
    have hΓ₀ : Function.Exact (G.map (P.d 1 0)).hom (G.map (π.f 0)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S₀.map G)).mp
        (TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent hS₀_ex)
    change Function.Exact (((e 0).symm.comp (G.map (P.d 1 0)).hom).comp (e 1).toLinearMap)
      ((G.map (π.f 0)).hom.comp (e 0).toLinearMap)
    rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]
  · have hexact : P.ExactAt (i + 1) :=
      (exactAt_iff_of_quasiIsoAt π (i + 1)).mpr (ChainComplex.exactAt_succ_single_obj _ _)
    have hSi : (P.sc' (i + 2) (i + 1) i).Exact :=
      (exactAt_iff' P (i + 2) (i + 1) i (by simp) (by simp)).mp hexact
    have : (P.sc' (i + 2) (i + 1) i).X₁.IsQuasicoherent := hqc (i + 2)
    have : (P.sc' (i + 2) (i + 1) i).X₂.IsQuasicoherent := hqc (i + 1)
    have hΓi : Function.Exact (G.map (P.d (i + 2) (i + 1))).hom (G.map (P.d (i + 1) i)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        ((P.sc' (i + 2) (i + 1) i).map G)).mp
        (TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent hSi)
    change Function.Exact
      (((e (i + 1)).symm.comp (G.map (P.d (i + 2) (i + 1))).hom).comp (e (i + 2)).toLinearMap)
      ((e i).symm.comp ((G.map (P.d (i + 1) i)).hom.comp (e (i + 1)).toLinearMap))
    rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
      LinearEquiv.conj_symm_exact_iff_exact]

/-- For an `R`-module `M`, the associated sheaf `M~` on `Spec R` has a finite free resolution if and
only if `M` is pseudo-coherent over `R` (Stacks, Lemma 36.10.1, Tag 08E5). -/
@[simp]
theorem hasFiniteFreeResolution_tilde_iff (M : ModuleCat.{u} R) :
    (tilde M).HasFiniteFreeResolution ↔ TauCeti.Huber.IsPseudoCoherentOver R M ⊤ :=
  ⟨fun h ↦ h.isPseudoCoherentOver_moduleSpecΓ.of_equiv
    ((tilde.toTildeΓNatIso (R := R)).app M).symm.toLinearEquiv, hasFiniteFreeResolution_tilde⟩

end Spec

section AffineOpens

variable {X : Scheme.{u}} {F : X.Modules}

/-- On an affine open `U` of `X`, a quasi-coherent module `F` whose `Γ(X, U)`-module of sections
`Γ(F, U)` is pseudo-coherent admits a finite free resolution after restriction to `U`. -/
theorem hasFiniteFreeResolution_restrict_of_isAffineOpen [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (h : TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤) :
    (F.restrict U.ι).HasFiniteFreeResolution := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let N := F.restrict hU.fromSpec
  have hN_Γ : TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) (moduleSpecΓFunctor.obj N) ⊤ :=
    h.of_equiv (F.fromSpecSectionsEquiv hU)
  have hN : N.HasFiniteFreeResolution :=
    (hasFiniteFreeResolution_tilde hN_Γ).of_iso (asIso N.fromTildeΓ)
  exact (hN.restrict hU.isoSpec.hom).of_iso
    (((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
      (restrictFunctorCongr (by rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc])).app F)

/-- On an affine scheme `X`, a sheaf with a global finite free resolution has pseudo-coherent
global sections over `Γ(X, ⊤)` (Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem HasFiniteFreeResolution.isPseudoCoherentOver_sections [IsAffine X]
    (h : F.HasFiniteFreeResolution) :
    TauCeti.Huber.IsPseudoCoherentOver Γ(X, ⊤) Γ(F, ⊤) ⊤ := by
  have : IsOpenImmersion (isAffineOpen_top X).fromSpec :=
    (isAffineOpen_top X).isOpenImmersion_fromSpec
  exact (h.restrict (isAffineOpen_top X).fromSpec).isPseudoCoherentOver_moduleSpecΓ.of_equiv
    (F.fromSpecSectionsEquiv (isAffineOpen_top X)).symm

/-- On an affine scheme `X`, a quasi-coherent module whose `Γ(X, ⊤)`-module of global sections is
pseudo-coherent admits a global finite free resolution (Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem hasFiniteFreeResolution_of_isPseudoCoherentOver_sections [IsAffine X] [F.IsQuasicoherent]
    (h : TauCeti.Huber.IsPseudoCoherentOver Γ(X, ⊤) Γ(F, ⊤) ⊤) :
    F.HasFiniteFreeResolution := by
  have : IsOpenImmersion (isAffineOpen_top X).fromSpec :=
    (isAffineOpen_top X).isOpenImmersion_fromSpec
  let e := moduleSpecΓFunctor.mapIso
    ((restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := X))).app F)
  exact hasFiniteFreeResolution_of_isPseudoCoherentOver_moduleSpecΓ F
    ((h.of_equiv (F.fromSpecSectionsEquiv (isAffineOpen_top X))).of_equiv e.toLinearEquiv)

/-- On an affine scheme `X`, `F` has a global finite free resolution if and only if `F` is
quasi-coherent and `Γ(F, ⊤)` is pseudo-coherent over `Γ(X, ⊤)`
(Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem hasFiniteFreeResolution_iff_isQuasicoherent_and_isPseudoCoherentOver [IsAffine X]
    (F : X.Modules) :
    F.HasFiniteFreeResolution ↔
      F.IsQuasicoherent ∧ TauCeti.Huber.IsPseudoCoherentOver Γ(X, ⊤) Γ(F, ⊤) ⊤ :=
  ⟨fun h ↦ ⟨h.isPseudoCoherent.isQuasicoherent, h.isPseudoCoherentOver_sections⟩,
    fun ⟨hqc, hΓ⟩ ↦ by
      have := hqc
      exact hasFiniteFreeResolution_of_isPseudoCoherentOver_sections hΓ⟩

/-- **Sections of a pseudo-coherent sheaf over an affine open are pseudo-coherent.** For any
pseudo-coherent `𝒪_X`-module `F` and any affine open `U` of `X`, the `Γ(X, U)`-module `Γ(F, U)` is
pseudo-coherent (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem IsPseudoCoherent.isPseudoCoherentOver_sections (hF : F.IsPseudoCoherent) {U : X.Opens}
    (hU : IsAffineOpen U) :
    TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  classical
  have : F.IsQuasicoherent := hF.isQuasicoherent
  let s : Set Γ(X, U) :=
    {f | ∃ V : X.Opens, X.basicOpen f ≤ V ∧ (F.restrict V.ι).HasFiniteFreeResolution}
  have hs : Ideal.span s = ⊤ := by
    apply hU.iSup_basicOpen_eq_self_iff.mp
    refine le_antisymm (iSup_le fun f : s ↦ X.basicOpen_le f.1) fun x hxU ↦ ?_
    obtain ⟨V, hxV, hV⟩ := isPseudoCoherent_iff.mp hF x
    obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨f, V, hf, hV⟩, hxf⟩
  have (f : s) : IsLocalization.Away f.1 Γ(X, X.basicOpen f.1) :=
    hU.isLocalization_basicOpen f.1
  have (f : s) : IsLocalizedModule.Away f.1 (F.basicOpenRestrict f.1) :=
    F.isLocalizedModule_basicOpenRestrict hU f.1
  refine TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan' s hs
    (Rₚ := fun f ↦ Γ(X, X.basicOpen f.1))
    (Mₚ := fun f ↦ Γ(F, X.basicOpen f.1)) (fun f ↦ F.basicOpenRestrict f.1) fun f ↦ ?_
  obtain ⟨V, hfV, hV⟩ := f.2
  let D : X.Opens := X.basicOpen f.1
  let hD : IsAffineOpen D := hU.basicOpen f.1
  have : IsOpenImmersion hD.fromSpec := hD.isOpenImmersion_fromSpec
  have hres : (F.restrict hD.fromSpec).HasFiniteFreeResolution :=
    (hV.restrict (hD.isoSpec.inv ≫ X.homOfLE hfV)).of_iso
      (((restrictFunctorComp (hD.isoSpec.inv ≫ X.homOfLE hfV) V.ι).app F).symm ≪≫
        (restrictFunctorCongr
          (by rw [Category.assoc, X.homOfLE_ι, hD.isoSpec_inv_ι])).app F)
  exact hres.isPseudoCoherentOver_moduleSpecΓ.of_equiv (F.fromSpecSectionsEquiv hD).symm

/-- **Affine-open characterization of pseudo-coherent module sheaves.** An `𝒪_X`-module `F` on a
scheme `X` is pseudo-coherent if and only if `F` is quasi-coherent and, for every affine open `U`
of `X`, the `Γ(X, U)`-module `Γ(F, U)` is pseudo-coherent (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem isPseudoCoherent_iff_forall_affineOpens (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ U : X.affineOpens, TauCeti.Huber.IsPseudoCoherentOver Γ(X, U.1) Γ(F, U.1) ⊤ := by
  refine ⟨fun h ↦ ⟨h.isQuasicoherent, fun U ↦ h.isPseudoCoherentOver_sections U.2⟩,
    fun ⟨hqc, h⟩ ↦ isPseudoCoherent_iff.mpr fun x ↦ ?_⟩
  have := hqc
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  exact ⟨U, hxU, hasFiniteFreeResolution_restrict_of_isAffineOpen hU (h ⟨U, hU⟩)⟩

/-- Unbundled form of `isPseudoCoherent_iff_forall_affineOpens` quantifying over `U : X.Opens` and
`IsAffineOpen U`. -/
theorem isPseudoCoherent_iff_forall_isAffineOpen (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ U : X.Opens, IsAffineOpen U → TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  rw [isPseudoCoherent_iff_forall_affineOpens]
  exact and_congr_right' ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- **Affine open cover criterion for pseudo-coherence.** For any cover `⨆ i, U i = ⊤` of `X` by
affine opens, `F` is pseudo-coherent if and only if `F` is quasi-coherent and each `Γ(F, U i)` is
pseudo-coherent over `Γ(X, U i)` (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem isPseudoCoherent_iff_of_iSup_eq_top {ι : Type*} {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ i, TauCeti.Huber.IsPseudoCoherentOver Γ(X, U i) Γ(F, U i) ⊤ := by
  refine ⟨fun h ↦ ⟨h.isQuasicoherent, fun i ↦ h.isPseudoCoherentOver_sections (hU i)⟩,
    fun ⟨hqc, h⟩ ↦ isPseudoCoherent_iff.mpr fun x ↦ ?_⟩
  have := hqc
  have hx : x ∈ ⨆ i, U i := by simp [hcov]
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, hxi, hasFiniteFreeResolution_restrict_of_isAffineOpen (hU i) (h i)⟩

/-- On an affine scheme `X`, `F` is pseudo-coherent if and only if `F` is quasi-coherent and
`Γ(F, ⊤)` is pseudo-coherent over `Γ(X, ⊤)` (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem isPseudoCoherent_iff_of_isAffine [IsAffine X] (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧ TauCeti.Huber.IsPseudoCoherentOver Γ(X, ⊤) Γ(F, ⊤) ⊤ := by
  simpa using isPseudoCoherent_iff_of_iSup_eq_top (U := fun _ : Unit ↦ ⊤)
    (fun _ ↦ isAffineOpen_top X) (by simp) F

/-- On an affine scheme `X`, local finite free resolutions lift to a global finite free resolution:
`F` has a finite free resolution if and only if `F` is pseudo-coherent
(Stacks, Lemma 36.10.2, Tag 08E7). -/
@[simp]
theorem hasFiniteFreeResolution_iff_isPseudoCoherent [IsAffine X] (F : X.Modules) :
    F.HasFiniteFreeResolution ↔ F.IsPseudoCoherent :=
  (hasFiniteFreeResolution_iff_isQuasicoherent_and_isPseudoCoherentOver F).trans
    (isPseudoCoherent_iff_of_isAffine F).symm

/-- For an `R`-module `M`, the associated sheaf `M~` on `Spec R` is pseudo-coherent if and only if
`M` is pseudo-coherent over `R` (Stacks, Lemma 36.10.2, Tag 08E7). -/
@[simp]
theorem isPseudoCoherent_tilde_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsPseudoCoherent ↔ TauCeti.Huber.IsPseudoCoherentOver R M ⊤ :=
  (hasFiniteFreeResolution_iff_isPseudoCoherent (tilde M)).symm.trans
    (hasFiniteFreeResolution_tilde_iff M)

/-- Every finite locally free `𝒪_X`-module is pseudo-coherent. -/
theorem IsPseudoCoherent.of_isFiniteLocallyFree (F : X.Modules) [F.IsLocallyFree]
    [F.IsFinitePresentation] : F.IsPseudoCoherent := by
  obtain ⟨q, hq, hq'⟩ :=
    (SheafOfModules.isFiniteLocallyFree_iff_exists_isLocallyFreeData_isFiniteType F).mp
      ⟨‹_›, ‹_›⟩
  refine isPseudoCoherent_iff.mpr fun x ↦ ?_
  have hx : x ∈ ⨆ i, q.X i := by
    rw [((Opens.coversTop_iff _ q.X).mp q.coversTop).iSup_eq_top]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have := hq.isIso i
  have : Finite (q.generators i).I := (hq'.isFiniteType i).finite
  exact ⟨q.X i, hxi, (hasFiniteFreeResolution_free (q.generators i).I).of_iso
    (restrictIsoFreeOfOverIsoFree F (q.X i) (asIso (q.generators i).π).symm).symm⟩

end AffineOpens

section NegativeControl

/-- **Quasi-coherence cannot be omitted from `isPseudoCoherent_iff_forall_affineOpens`.** On the
spectrum of any local integral domain `R` that is not a field, there exists an `𝒪_{Spec R}`-module
`F` whose sections over every affine open `W` are pseudo-coherent over `Γ(Spec R, W)` (in fact free
of rank `0` on `⊤` and rank `1` on proper opens), yet `F` is neither quasi-coherent nor
pseudo-coherent. -/
theorem exists_not_isPseudoCoherent_of_forall_affineOpens (R : Type u) [CommRing R] [IsDomain R]
    [IsLocalRing R] (hR : ¬ IsField R) :
    ∃ F : (Spec (.of R)).Modules,
      (∀ W : (Spec (.of R)).affineOpens,
        TauCeti.Huber.IsPseudoCoherentOver Γ(Spec (.of R), W.1) Γ(F, W.1) ⊤) ∧
      ¬ F.IsQuasicoherent ∧ ¬ F.IsPseudoCoherent := by
  classical
  let X : Scheme.{u} := Spec (.of R)
  let M₀ : SheafOfModules.{u} X.ringCatSheaf := SheafOfModules.unit X.ringCatSheaf
  let N₀ : M₀.val.Submodule :=
    { obj := fun W ↦ if W.unop = ⊤ then ⊥ else ⊤
      map := fun {V W} f ↦ by
        by_cases hW : W.unop = ⊤
        · have hV : V.unop = ⊤ := top_unique (hW ▸ leOfHom f.unop)
          simp [hV]
        · simp [hW] }
  let N : M₀.Submodule :=
    { toSubmodule := N₀
      isSheaf := fun ⟨W⟩ s hs ↦ by
        by_cases hW : W = ⊤
        · subst hW
          obtain ⟨V, iVW, hsV, hxV⟩ := hs (IsLocalRing.closedPoint R) trivial
          have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hxV
          subst hV
          have hs1 : (N₀.toSubfunctor.sieveOfSection s).arrows (𝟙 ⊤) :=
            Subsingleton.elim iVW (𝟙 ⊤) ▸ hsV
          change (M₀.val.presheaf.map (op (𝟙 ⊤))) s ∈ N₀.obj (op ⊤) at hs1
          have hid : (M₀.val.presheaf.map (op (𝟙 ⊤))) s = s :=
            (congrArg (fun φ ↦ φ s)
              ((congrArg M₀.val.presheaf.map (op_id (X := (⊤ : X.Opens)))).trans
                (M₀.val.presheaf.map_id (op ⊤)))).trans
              (AddCommGrpCat.id_apply (M₀.val.presheaf.obj (op ⊤)) s)
          exact hid ▸ hs1
        · simp [N₀, hW] }
  let F : X.Modules := N.toSheafOfModules
  have hF_sections : ∀ W : X.affineOpens,
      TauCeti.Huber.IsPseudoCoherentOver Γ(X, W.1) Γ(F, W.1) ⊤ := fun W ↦ by
    by_cases hW : W.1 = ⊤
    · have : Subsingleton Γ(F, W.1) := by
        change Subsingleton ↥(if W.1 = ⊤ then (⊥ : Submodule _ _) else ⊤)
        simp only [hW, ↓reduceIte]
        infer_instance
      let e₀ : (Fin 0 → Γ(X, W.1)) ≃ₗ[Γ(X, W.1)] Γ(F, W.1) :=
        { toFun := 0, map_add' := by simp, map_smul' := by simp,
          invFun := 0, left_inv := fun _ ↦ Subsingleton.elim _ _,
          right_inv := fun _ ↦ Subsingleton.elim _ _ }
      exact TauCeti.Huber.IsPseudoCoherentOver.of_projective.of_equiv e₀
    · have htop : N.toSubmodule.obj (op W.1) = ⊤ :=
        ite_eq_right_iff.mpr fun h ↦ (hW h).elim
      let e₁ : Γ(F, W.1) ≃ₗ[Γ(X, W.1)] Γ(X, W.1) :=
        LinearEquiv.ofTop (N.toSubmodule.obj (op W.1)) htop
      exact TauCeti.Huber.IsPseudoCoherentOver.of_projective.of_equiv e₁.symm
  have hnot_qc : ¬ F.IsQuasicoherent := fun hqc ↦ by
    have : F.IsQuasicoherent := hqc
    have hm_ne : IsLocalRing.maximalIdeal R ≠ ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hR
    obtain ⟨r, hr_mem, hr_ne⟩ := (Submodule.ne_bot_iff _).mp hm_ne
    let f : Γ(X, ⊤) := (Scheme.ΓSpecIso (.of R)).inv r
    have hD_eq : X.basicOpen f = PrimeSpectrum.basicOpen r :=
      basicOpen_eq_of_affine (R := .of R) r
    have hclosed_not_mem : IsLocalRing.closedPoint R ∉ PrimeSpectrum.basicOpen r := by
      rwa [PrimeSpectrum.mem_basicOpen, not_not]
    have hD_ne_top : X.basicOpen f ≠ ⊤ := by
      intro htop
      apply hclosed_not_mem
      rw [← hD_eq, htop]
      trivial
    have : Subsingleton Γ(F, ⊤) := by
      change Subsingleton ↥(if (⊤ : X.Opens) = ⊤ then (⊥ : Submodule _ _) else ⊤)
      simp only [↓reduceIte]
      infer_instance
    have hf_ne : f ≠ 0 := by
      intro hf0
      apply hr_ne
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
        (hf0.trans (map_zero _).symm)
    have : IsDomain Γ(X, ⊤) :=
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain R
    have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
      (isAffineOpen_top X).isLocalization_basicOpen f
    have : Nontrivial Γ(X, X.basicOpen f) := by
      refine ⟨⟨0, 1, fun h01 ↦ ?_⟩⟩
      have h10 : algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) 1 =
          algebraMap Γ(X, ⊤) Γ(X, X.basicOpen f) 0 := by simp [h01.symm]
      obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f)
        Γ(X, X.basicOpen f)).mp h10
      simp only [mul_one, mul_zero] at hk
      exact pow_ne_zero k hf_ne hk
    have : IsLocalizedModule.Away f (F.basicOpenRestrict f) :=
      F.isLocalizedModule_basicOpenRestrict (isAffineOpen_top X) f
    have hzero : ∀ a : Γ(F, X.basicOpen f), a = 0 := fun a ↦ by
      obtain ⟨⟨x, s⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers f) (F.basicOpenRestrict f) a
      have hs0 : s.1 • a = 0 := by
        change s • a = 0
        rw [ha, Subsingleton.elim x 0, map_zero]
      obtain ⟨u, hu⟩ := IsLocalizedModule.map_units (F.basicOpenRestrict f) s
      have hua : (u : Module.End Γ(X, ⊤) Γ(F, X.basicOpen f)) a = 0 := by
        rw [hu]
        exact hs0
      calc a = (1 : Module.End Γ(X, ⊤) Γ(F, X.basicOpen f)) a := rfl
        _ = (↑(u⁻¹ * u) : Module.End Γ(X, ⊤) Γ(F, X.basicOpen f)) a := by
              rw [inv_mul_cancel, Units.val_one]
        _ = (↑u⁻¹ : Module.End Γ(X, ⊤) Γ(F, X.basicOpen f))
              ((↑u : Module.End Γ(X, ⊤) Γ(F, X.basicOpen f)) a) := rfl
        _ = 0 := by rw [hua, map_zero]
    have : Subsingleton Γ(F, X.basicOpen f) :=
      ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩
    let eD : Γ(F, X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)] Γ(X, X.basicOpen f) :=
      LinearEquiv.ofTop (N.toSubmodule.obj (op (X.basicOpen f)))
        (ite_eq_right_iff.mpr fun h ↦ (hD_ne_top h).elim)
    have : Subsingleton Γ(X, X.basicOpen f) := eD.symm.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton Γ(X, X.basicOpen f)
  exact ⟨F, hF_sections, hnot_qc, fun hpc ↦ hnot_qc hpc.isQuasicoherent⟩

/-- Over the spectrum of any discrete valuation ring `R`, there exists an `𝒪_{Spec R}`-module whose
sections over every affine open are pseudo-coherent, yet which is neither quasi-coherent nor
pseudo-coherent. -/
theorem exists_not_isPseudoCoherent_of_isDiscreteValuationRing (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ F : (Spec (.of R)).Modules,
      (∀ W : (Spec (.of R)).affineOpens,
        TauCeti.Huber.IsPseudoCoherentOver Γ(Spec (.of R), W.1) Γ(F, W.1) ⊤) ∧
      ¬ F.IsQuasicoherent ∧ ¬ F.IsPseudoCoherent :=
  exists_not_isPseudoCoherent_of_forall_affineOpens R (IsDiscreteValuationRing.not_isField R)

end NegativeControl

end

end AlgebraicGeometry.Scheme.Modules
