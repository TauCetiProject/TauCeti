/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation

import TauCeti.Algebra.Module.PseudoCoherent.Descent

/-!
# Affine characterization of pseudo-coherent module sheaves

An `𝒪_X`-module `F` on a scheme `X` is pseudo-coherent
(`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent`) if and only if `F` is quasi-coherent and,
for every affine open `U` of `X`, the `Γ(X, U)`-module `Γ(F, U)` is pseudo-coherent
(`TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤`). Equivalently, it suffices to check
pseudo-coherence of `Γ(F, U i)` on any cover of `X` by affine opens `U i`. On an affine scheme `X`,
`F` is pseudo-coherent if and only if `F` admits a global resolution by free `𝒪_X`-modules of
finite rank (`AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution`).

These characterizations reduce sheaf-level pseudo-coherence to purely algebraic module
pseudo-coherence on affine charts: once `F` is known to be quasi-coherent, checking
`F.IsPseudoCoherent` requires testing `TauCeti.Huber.IsPseudoCoherentOver` only on the modules of
sections over an affine open cover, and conversely every affine open of a pseudo-coherent sheaf
carries pseudo-coherent sections. On an affine scheme, the local definition automatically upgrades
to a global finite free resolution, matching the correspondence `M ↦ M~` between pseudo-coherent
`R`-modules and pseudo-coherent `𝒪_{Spec R}`-modules. The quasi-coherence hypothesis is essential
in the affine-open criteria (see `TauCeti/Examples/AlgebraicGeometry/Modules/PseudoCoherent.lean`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution.isPseudoCoherentOver_moduleSpecΓ`: a
  finite free resolution on `Spec R` gives a pseudo-coherent module of global sections.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.isPseudoCoherentOver_sections`: sections of a
  pseudo-coherent sheaf over any affine open `U` are pseudo-coherent over `Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_of_iSup_eq_top` and
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_forall_affineOpens`: characterization of
  pseudo-coherent module sheaves on affine open covers and on all affine opens.
* `AlgebraicGeometry.Scheme.Modules.hasFiniteFreeResolution_iff_isPseudoCoherent`: on an affine
  scheme, local finite free resolutions lift to a global finite free resolution.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_tilde_iff`: on `Spec R`, `M~` is
  pseudo-coherent if and only if `M` is pseudo-coherent over `R`.

## References

* The Stacks Project, Section 36.10 (Tag 08E4), Lemma 36.10.1 (Tag 08E5), and
  Lemma 36.10.2 (Tag 08E7).
-/

public section

open CategoryTheory Limits HomologicalComplex TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

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
    exact ⟨Fintype.card ι, ⟨((Finsupp.linearEquivFunOnFinite R R _).symm.trans
      (Finsupp.domLCongr (Fintype.equivFin ι).symm)).trans
      ((TauCeti.AlgebraicGeometry.moduleSpecΓFunctorFreeIso (R := R) ι).symm ≪≫
        G.mapIso e.symm).toLinearEquiv⟩⟩
  choose k hk using hcoord
  let e (n : ℕ) : (Fin (k n) → R) ≃ₗ[R] G.obj (P.X n) := (hk n).some
  -- Transport the augmentation and differentials to finite coordinate modules.
  let iF : ((ChainComplex.single₀ (Spec R).Modules).obj F).X 0 ≅ F :=
    singleObjXSelf (ComplexShape.down ℕ) 0 F
  let ε : (Fin (k 0) → R) →ₗ[R] G.obj F :=
    (G.mapIso iF).toLinearEquiv.toLinearMap ∘ₗ ((G.map (π.f 0)).hom ∘ₗ (e 0).toLinearMap)
  let d (i : ℕ) : (Fin (k (i + 1)) → R) →ₗ[R] (Fin (k i) → R) :=
    (e i).symm.toLinearMap ∘ₗ ((G.map (P.d (i + 1) i)).hom ∘ₗ (e (i + 1)).toLinearMap)
  have : QuasiIsoAt π 0 := hπ.quasiIsoAt 0
  let S₀ : ShortComplex (Spec R).Modules :=
    ShortComplex.mk (P.d 1 0) (π.f 0) (by rw [← π.comm 1 0, single_obj_d, comp_zero])
  obtain ⟨hS₀_ex, hπ₀_epi⟩ :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel S₀).mpr
      ⟨P.isColimitCokernelCoforkOfQuasiIsoAt π⟩
  have : Epi (π.f 0) := hπ₀_epi
  have : (P.X 0).IsQuasicoherent := hqc 0
  have : (((ChainComplex.single₀ (Spec R).Modules).obj F).X 0).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso iF.symm inferInstance
  have hε : Function.Surjective ε :=
    (G.mapIso iF).toLinearEquiv.surjective.comp
      ((TauCeti.AlgebraicGeometry.moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
        (π.f 0)).comp (e 0).surjective)
  refine (TauCeti.Huber.isPseudoCoherentOver_iff R (G.obj F) ⊤).mpr ⟨k, d, ε, hε, fun _ ↦ ?_,
    fun i _ ↦ ?_⟩
  · -- Exactness at degree 0.
    have : S₀.X₁.IsQuasicoherent := hqc 1
    have : S₀.X₂.IsQuasicoherent := hqc 0
    have hΓ₀ : Function.Exact (G.map (P.d 1 0)).hom (G.map (π.f 0)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S₀.map G)).mp
        (TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent hS₀_ex)
    dsimp only [d, ε]
    rwa [LinearEquiv.postcomp_exact_iff_exact, ← LinearMap.comp_assoc,
      LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]
  · -- Exactness in positive degrees.
    have hexact : P.ExactAt (i + 1) :=
      (exactAt_iff_of_quasiIsoAt π (i + 1)).mpr (ChainComplex.exactAt_succ_single_obj _ _)
    have hSi : (P.sc' (i + 2) (i + 1) i).Exact :=
      (exactAt_iff' P (i + 2) (i + 1) i (by simp) (by simp)).mp hexact
    have : (P.sc' (i + 2) (i + 1) i).X₁.IsQuasicoherent := hqc (i + 2)
    have : (P.sc' (i + 2) (i + 1) i).X₂.IsQuasicoherent := hqc (i + 1)
    have hΓi : Function.Exact (G.map (P.d (i + 2) (i + 1))).hom (G.map (P.d (i + 1) i)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        ((P.sc' (i + 2) (i + 1) i).map G)).mp
        (TauCeti.AlgebraicGeometry.exact_map_moduleSpecΓFunctor_of_isQuasicoherent hSi)
    dsimp only [d]
    rwa [LinearEquiv.postcomp_exact_iff_exact, ← LinearMap.comp_assoc,
      LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]

/-- For an `R`-module `M`, the associated sheaf `M~` on `Spec R` has a finite free resolution if and
only if `M` is pseudo-coherent over `R` (Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem hasFiniteFreeResolution_tilde_iff (M : ModuleCat.{u} R) :
    (tilde M).HasFiniteFreeResolution ↔ TauCeti.Huber.IsPseudoCoherentOver R M ⊤ :=
  ⟨fun h ↦ h.isPseudoCoherentOver_moduleSpecΓ.of_equiv
    ((tilde.toTildeΓNatIso (R := R)).app M).symm.toLinearEquiv, hasFiniteFreeResolution_tilde⟩

end Spec

section AffineOpens

variable {X : Scheme.{u}} {F : X.Modules}

/-- On an affine open `U` of `X`, if `F|_U` is quasi-coherent and the `Γ(X, U)`-module of sections
`Γ(F, U)` is pseudo-coherent, then `F|_U` admits a finite free resolution. -/
theorem hasFiniteFreeResolution_restrict_of_isAffineOpen_of_isPseudoCoherentOver {U : X.Opens}
    (hU : IsAffineOpen U) [(F.restrict U.ι).IsQuasicoherent]
    (h : TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤) :
    (F.restrict U.ι).HasFiniteFreeResolution := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let N := F.restrict hU.fromSpec
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
      (((restrictFunctorComp hU.isoSpec.inv U.ι).app F).symm ≪≫
        (restrictFunctorCongr hU.isoSpec_inv_ι).app F)
      (isQuasicoherent_restrictFunctor hU.isoSpec.inv (F.restrict U.ι))
  have hN_Γ : TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) (moduleSpecΓFunctor.obj N) ⊤ :=
    h.of_equiv (F.fromSpecSectionsEquiv hU)
  have hN : N.HasFiniteFreeResolution :=
    (hasFiniteFreeResolution_tilde hN_Γ).of_iso (asIso N.fromTildeΓ)
  exact (hN.restrict hU.isoSpec.hom).of_iso
    (((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
      (restrictFunctorCongr (by rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc])).app F)

/-- Over any affine open `U` of a scheme `X`, a sheaf with a global finite free resolution has
pseudo-coherent sections over `Γ(X, U)` (Stacks, Lemma 36.10.1, Tag 08E5). -/
theorem HasFiniteFreeResolution.isPseudoCoherentOver_sections
    (h : F.HasFiniteFreeResolution) {U : X.Opens} (hU : IsAffineOpen U) :
    TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  exact (h.restrict hU.fromSpec).isPseudoCoherentOver_moduleSpecΓ.of_equiv
    (F.fromSpecSectionsEquiv hU).symm

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
  ⟨fun h ↦ ⟨h.isPseudoCoherent.isQuasicoherent,
      h.isPseudoCoherentOver_sections (isAffineOpen_top X)⟩,
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
    refine le_antisymm (iSup_le fun f : s ↦ X.basicOpen_le f.val) fun x hxU ↦ ?_
    obtain ⟨V, hxV, hV⟩ := isPseudoCoherent_iff.mp hF x
    obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨f, V, hf, hV⟩, hxf⟩
  have (f : s) : IsLocalization.Away f.val Γ(X, X.basicOpen f.val) :=
    hU.isLocalization_basicOpen f.val
  have (f : s) : IsLocalizedModule.Away f.val (F.basicOpenRestrict f.val) :=
    F.isLocalizedModule_basicOpenRestrict hU f.val
  refine TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan' s hs
    (Rₚ := fun f ↦ Γ(X, X.basicOpen f.val))
    (Mₚ := fun f ↦ Γ(F, X.basicOpen f.val)) (fun f ↦ F.basicOpenRestrict f.val) fun f ↦ ?_
  obtain ⟨V, hfV, hV⟩ := f.property
  let D : X.Opens := X.basicOpen f.val
  let hD : IsAffineOpen D := hU.basicOpen f.val
  have : IsOpenImmersion hD.fromSpec := hD.isOpenImmersion_fromSpec
  have hres : (F.restrict hD.fromSpec).HasFiniteFreeResolution :=
    (hV.restrict (hD.isoSpec.inv ≫ X.homOfLE hfV)).of_iso
      (((restrictFunctorComp (hD.isoSpec.inv ≫ X.homOfLE hfV) V.ι).app F).symm ≪≫
        (restrictFunctorCongr
          (by rw [Category.assoc, X.homOfLE_ι, hD.isoSpec_inv_ι])).app F)
  exact hres.isPseudoCoherentOver_moduleSpecΓ.of_equiv (F.fromSpecSectionsEquiv hD).symm

/-- **Affine open cover criterion for pseudo-coherence.** For any cover `⨆ i, U i = ⊤` of `X` by
affine opens, `F` is pseudo-coherent if and only if `F` is quasi-coherent and each `Γ(F, U i)` is
pseudo-coherent over `Γ(X, U i)` (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem isPseudoCoherent_iff_of_iSup_eq_top {ι : Sort*} {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ i, TauCeti.Huber.IsPseudoCoherentOver Γ(X, U i) Γ(F, U i) ⊤ := by
  refine ⟨fun h ↦ ⟨h.isQuasicoherent, fun i ↦ h.isPseudoCoherentOver_sections (hU i)⟩,
    fun ⟨hqc, h⟩ ↦ isPseudoCoherent_iff.mpr fun x ↦ ?_⟩
  have := hqc
  have hx : x ∈ ⨆ i, U i := by simp [hcov]
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have : (F.restrict (U i).ι).IsQuasicoherent := isQuasicoherent_restrictFunctor (U i).ι F
  exact ⟨U i, hxi,
    hasFiniteFreeResolution_restrict_of_isAffineOpen_of_isPseudoCoherentOver (hU i) (h i)⟩

/-- **Affine-open characterization of pseudo-coherent module sheaves.** An `𝒪_X`-module `F` on a
scheme `X` is pseudo-coherent if and only if `F` is quasi-coherent and, for every affine open `U`
of `X`, the `Γ(X, U)`-module `Γ(F, U)` is pseudo-coherent (Stacks, Lemma 36.10.2, Tag 08E7). -/
theorem isPseudoCoherent_iff_forall_affineOpens (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ U : X.affineOpens, TauCeti.Huber.IsPseudoCoherentOver Γ(X, U.val) Γ(F, U.val) ⊤ :=
  isPseudoCoherent_iff_of_iSup_eq_top (U := fun U : X.affineOpens ↦ U.val)
    (fun U ↦ U.property) (iSup_affineOpens_eq_top X) F

/-- Unbundled form of `isPseudoCoherent_iff_forall_affineOpens` quantifying over `U : X.Opens` and
`IsAffineOpen U`. -/
theorem isPseudoCoherent_iff_forall_isAffineOpen (F : X.Modules) :
    F.IsPseudoCoherent ↔
      F.IsQuasicoherent ∧
        ∀ U : X.Opens, IsAffineOpen U → TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  rw [isPseudoCoherent_iff_forall_affineOpens]
  exact and_congr_right' ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.val U.property⟩

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

end AffineOpens

end

end AlgebraicGeometry.Scheme.Modules
