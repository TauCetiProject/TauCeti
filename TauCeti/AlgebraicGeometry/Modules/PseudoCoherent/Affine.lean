/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Localization

import TauCeti.Algebra.Module.PseudoCoherent.Descent
import TauCeti.Algebra.Module.PseudoCoherent.RestrictScalars
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Exact
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# The affine criterion for pseudo-coherent sheaves

A module sheaf `F` on a scheme `X` is pseudo-coherent (finite free resolutions locally on `X`)
exactly when it is quasi-coherent and, for every affine open `U`, the `Γ(X, U)`-module `Γ(F, U)`
is pseudo-coherent in the sense of `TauCeti.Huber.IsPseudoCoherentOver`. This connects the sheaf
predicate `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent` with the module theory of
`TauCeti/Algebra/Module/PseudoCoherent/`, so that pseudo-coherent sheaves can be studied through
their modules of sections over affine opens.

The quasi-coherence clause cannot be dropped. For a discrete valuation ring `R` that is not a
field, with fraction field `K`, the extension by zero of the structure sheaf of the generic point
of `Spec R` has sections `0` over `Spec R` and `K` over the generic point, both pseudo-coherent
modules, but it is not quasi-coherent and hence not pseudo-coherent.

Sections over an affine open are exact on quasi-coherent modules
(`AlgebraicGeometry.Scheme.Modules.exact_app_of_isAffineOpen`) and send free modules of finite
rank to finite free modules, so a global finite free resolution gives a finite free resolution of
the sections. A pseudo-coherent sheaf only has such resolutions locally. Over an affine open `U`
they exist on basic opens `X.basicOpen g` covering `U`, so the sections over these basic opens are
pseudo-coherent. These sections are the localizations of `Γ(F, U)` at the `g`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`), and pseudo-coherence
descends from such a cover (`TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan'`).
Conversely, on the affine chart `Spec Γ(X, U) ⟶ X` a quasi-coherent module is the sheaf
associated with its module of sections, so a resolution of the sections gives a resolution of the
sheaf (`AlgebraicGeometry.Scheme.Modules.hasFiniteFreeResolution_tilde`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution.isPseudoCoherentOver`: a module
  sheaf with a global finite free resolution has pseudo-coherent sections over every affine open.
* `AlgebraicGeometry.Scheme.Modules.hasFiniteFreeResolution_restrict_fromSpec_iff`: a
  quasi-coherent module has a finite free resolution on the affine chart of an affine open `U`
  exactly when its sections over `U` are pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.isPseudoCoherentOver`: a pseudo-coherent
  module sheaf has pseudo-coherent sections over every affine open.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_isQuasicoherent_and_forall_affineOpens`:
  the affine criterion.

## References

* The Stacks Project, Lemmas 36.10.1 (Tag 08E5) and 36.10.2 (Tag 08E7), pseudo-coherence on
  schemes in terms of affine opens.
* The Stacks Project, Tag 066D, pseudo-coherence is local on `Spec R`.
-/

public section

open CategoryTheory Limits HomologicalComplex Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}} {F : X.Modules} {U : X.Opens}

/-- A module sheaf with a global finite free resolution has pseudo-coherent sections over every
affine open `U`: taking sections over `U` carries the resolution to a resolution of `Γ(F, U)` by
finite free `Γ(X, U)`-modules. -/
theorem HasFiniteFreeResolution.isPseudoCoherentOver (h : F.HasFiniteFreeResolution)
    (hU : IsAffineOpen U) : TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  obtain ⟨P, π, hP, hπ⟩ := hasFiniteFreeResolution_iff.mp h
  have : F.IsQuasicoherent := h.isPseudoCoherent.isQuasicoherent
  choose ι hι e using hP
  have hfree (n : ℕ) : (P.X n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (e n).some.symm inferInstance
  -- Coordinates on the sections of the resolving terms, from the basis of a finite free sheaf.
  let E (n : ℕ) : Γ(P.X n, U) ≃ₗ[Γ(X, U)] (Fin (Nat.card (ι n)) → Γ(X, U)) :=
    (sectionsLinearEquiv (e n).some U).trans
      ((TauCeti.SheafOfModules.freeBasis (R := X.sheaf) (ι n) (op U)).reindex
        (Finite.equivFin (ι n))).equivFun
  let app {M N : X.Modules} (φ : M ⟶ N) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := φ.app U, map_add' := map_add _, map_smul' := Hom.app_smul φ }
  -- The augmentation presents `F`, placed in degree zero, as the cokernel of the first
  -- differential. The degree-zero term of the single complex on `F` is `F` itself.
  have : ((ChainComplex.single₀ X.Modules).obj F).X 0 |>.IsQuasicoherent := ‹F.IsQuasicoherent›
  obtain ⟨h₀, hε⟩ := (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
    (ShortComplex.mk (P.d 1 0) (π.f 0) (by rw [← π.comm 1 0, single_obj_d, comp_zero]))).mpr
      ⟨P.isColimitCokernelCoforkOfQuasiIsoAt π⟩
  -- The maps `app φ` are the components `φ.app U`, so the exactness of the coordinate resolution
  -- reduces to `exact_app_of_isAffineOpen` after cancelling the coordinate equivalences.
  refine (TauCeti.Huber.isPseudoCoherentOver_iff _ _ ⊤).mpr ⟨fun n ↦ Nat.card (ι n),
    fun i ↦ ((E i).toLinearMap ∘ₗ app (P.d (i + 1) i)) ∘ₗ (E (i + 1)).symm.toLinearMap,
    app (π.f 0) ∘ₗ (E 0).symm.toLinearMap, ?_, fun _ ↦ ?_, fun i _ ↦ ?_⟩
  · exact (Hom.app_surjective_of_epi_of_isAffineOpen (π.f 0) U hU).comp (E 0).symm.surjective
  · rw [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact]
    have : (P.X 1).IsQuasicoherent := hfree 1
    have : (P.X 0).IsQuasicoherent := hfree 0
    exact exact_app_of_isAffineOpen h₀ U hU
  · rw [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact,
      LinearEquiv.postcomp_exact_iff_exact]
    have hexact : P.ExactAt (i + 1) :=
      (exactAt_iff_of_quasiIsoAt π (i + 1)).mpr (ChainComplex.exactAt_succ_single_obj _ _)
    have : (P.sc' (i + 2) (i + 1) i).X₁.IsQuasicoherent := hfree (i + 2)
    have : (P.sc' (i + 2) (i + 1) i).X₂.IsQuasicoherent := hfree (i + 1)
    have : (P.sc' (i + 2) (i + 1) i).X₃.IsQuasicoherent := hfree i
    exact exact_app_of_isAffineOpen
      ((exactAt_iff' P (i + 2) (i + 1) i (by simp) (by simp)).mp hexact) U hU

/-- On `Spec R`, a module sheaf with a finite free resolution has global sections that are
pseudo-coherent over `R`, which acts on them through `R ≅ Γ(Spec R, ⊤)`. -/
theorem HasFiniteFreeResolution.isPseudoCoherentOver_Spec {R : CommRingCat.{u}}
    {N : (Spec R).Modules} (h : N.HasFiniteFreeResolution) :
    TauCeti.Huber.IsPseudoCoherentOver R Γ(N, ⊤) ⊤ := by
  -- `Γ(Spec R, ⊤)` is free of rank one over `R`, so pseudo-coherence over it and over `R` agree.
  have hS : TauCeti.Huber.IsPseudoCoherentOver R Γ(Spec R, ⊤) ⊤ :=
    TauCeti.Huber.IsPseudoCoherentOver.of_projective (R := R) (M := R) |>.of_equiv
      (LinearEquiv.ofBijective (Algebra.linearMap R Γ(Spec R, ⊤)) (by
        simpa [Algebra.coe_linearMap] using
          ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
  exact (TauCeti.Huber.isPseudoCoherentOver_restrictScalars_iff hS).mpr
    (h.isPseudoCoherentOver (isAffineOpen_top _))

/-- A quasi-coherent module sheaf has a finite free resolution on the affine chart
`Spec Γ(X, U) ⟶ X` of an affine open `U` exactly when its sections over `U` are pseudo-coherent
over `Γ(X, U)`. -/
theorem hasFiniteFreeResolution_restrict_fromSpec_iff (hU : IsAffineOpen U)
    [F.IsQuasicoherent] :
    (F.restrict hU.fromSpec).HasFiniteFreeResolution ↔
      TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  refine ⟨fun h ↦ h.isPseudoCoherentOver_Spec.of_equiv (F.fromSpecSectionsEquiv hU).symm,
    fun h ↦ ?_⟩
  -- On the chart, the quasi-coherent restriction is the sheaf associated with its sections.
  let N := F.restrict hU.fromSpec
  exact (hasFiniteFreeResolution_tilde (M := moduleSpecΓFunctor.obj N)
    (h.of_equiv (F.fromSpecSectionsEquiv hU))).of_iso (asIso N.fromTildeΓ)

/-- A pseudo-coherent module sheaf has pseudo-coherent sections over every affine open `U`
(Stacks, Lemma 36.10.2 (08E7)). -/
theorem IsPseudoCoherent.isPseudoCoherentOver (h : F.IsPseudoCoherent) (hU : IsAffineOpen U) :
    TauCeti.Huber.IsPseudoCoherentOver Γ(X, U) Γ(F, U) ⊤ := by
  have : F.IsQuasicoherent := h.isQuasicoherent
  -- The functions `g` on `U` whose basic open carries a finite free resolution generate the unit
  -- ideal: these basic opens cover `U`.
  let s : Set Γ(X, U) := {g | (F.restrict (X.basicOpen g).ι).HasFiniteFreeResolution}
  have hs : Ideal.span s = ⊤ := by
    refine hU.self_le_iSup_basicOpen_iff.mp fun x hx ↦ ?_
    obtain ⟨V, hxV, hV⟩ := isPseudoCoherent_iff.mp h x
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hV.restrict_of_le hgV⟩, hxg⟩
  have (g : s) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) := hU.isLocalization_basicOpen g.1
  have (g : s) : IsLocalizedModule (Submonoid.powers g.1) (F.basicOpenRestrict g.1) :=
    isLocalizedModule_basicOpenRestrict F hU g.1
  refine TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan' s hs
    (Rₚ := fun g ↦ Γ(X, X.basicOpen g.1)) (Mₚ := fun g ↦ Γ(F, X.basicOpen g.1))
    (fun g ↦ F.basicOpenRestrict g.1) fun g ↦ ?_
  -- Move the resolution on `X.basicOpen g` to its affine chart, which factors through it.
  have hW := hU.basicOpen g.1
  exact (hasFiniteFreeResolution_restrict_fromSpec_iff hW).mp
    ((g.2.restrict hW.isoSpec.inv).of_iso
      (((restrictFunctorComp hW.isoSpec.inv _).app F).symm ≪≫
        (restrictFunctorCongr hW.isoSpec_inv_ι).app F))

/-- **The affine criterion for pseudo-coherence.** A module sheaf on a scheme is pseudo-coherent
exactly when it is quasi-coherent and its sections over every affine open `U` are pseudo-coherent
over `Γ(X, U)` (Stacks, Lemmas 36.10.1 (08E5) and 36.10.2 (08E7)). The quasi-coherence clause is
needed: pseudo-coherent modules of sections alone do not make a sheaf pseudo-coherent. -/
theorem isPseudoCoherent_iff_isQuasicoherent_and_forall_affineOpens :
    F.IsPseudoCoherent ↔ F.IsQuasicoherent ∧
      ∀ U : X.affineOpens, TauCeti.Huber.IsPseudoCoherentOver Γ(X, U.1) Γ(F, U.1) ⊤ := by
  refine ⟨fun h ↦ ⟨h.isQuasicoherent, fun U ↦ h.isPseudoCoherentOver U.2⟩, fun ⟨_, h⟩ ↦ ?_⟩
  refine isPseudoCoherent_iff_exists_isOpenImmersion.mpr fun x ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  exact ⟨_, hU.fromSpec, inferInstance, by rwa [hU.opensRange_fromSpec],
    (hasFiniteFreeResolution_restrict_fromSpec_iff hU).mpr (h ⟨U, hU⟩)⟩

end

end AlgebraicGeometry.Scheme.Modules
