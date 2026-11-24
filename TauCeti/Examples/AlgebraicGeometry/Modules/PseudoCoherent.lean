/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.Affine

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.Pullback

/-!
# Tests for pseudo-coherent modules on schemes

Free modules of finite rank and zero modules are pseudo-coherent on every scheme. Over a
noetherian ring `R`, the sheaf on `Spec R` associated with any cyclic module `R ⧸ I` is
pseudo-coherent. Its resolution gives a finite global presentation; local resolutions on an
arbitrary scheme give finite presentation and quasi-coherence. Conversely, a sheaf associated
to a module that is not finitely presented cannot be pseudo-coherent.

Flat pullback preserves the full resolutions as well as local pseudo-coherence. In particular,
cyclic sheaves over Noetherian rings stay pseudo-coherent after flat base change to schemes
that need not be Noetherian. A polynomial algebra in infinitely many variables over `ℤ/4`
exercises this without requiring the target ring of the algebra map to be Noetherian.

Finally, a negative-control construction over the spectrum of any local integral domain that is
not a field (in particular, any discrete valuation ring) shows that the quasi-coherence clause
cannot be dropped from `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_forall_affineOpens`:
the subsheaf of `𝒪_{Spec R}` vanishing on `⊤` and agreeing with `𝒪_{Spec R}` on proper opens has
pseudo-coherent sections over every affine open, yet fails to be quasi-coherent or pseudo-coherent.
-/

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- *IsPseudoCoherentSheaf_free*: on every scheme, the free module of rank `n` is
pseudo-coherent. -/
example (X : Scheme.{u}) (n : ℕ) :
    IsPseudoCoherent (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) :=
  isPseudoCoherent_free _

/-- *IsPseudoCoherentSheaf_zero*: on every scheme, the zero module is pseudo-coherent. -/
example (X : Scheme.{u}) : IsPseudoCoherent (0 : X.Modules) :=
  .of_isZero (isZero_zero _)

/-- An additional cyclic example: over a noetherian ring `R`, the sheaf associated with
`R ⧸ I` is pseudo-coherent for every ideal `I`. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) :
    (tilde (ModuleCat.of R (R ⧸ I))).IsPseudoCoherent :=
  isPseudoCoherent_tilde .of_isNoetherianRing

/-- Local resolutions give finite presentation on every open restriction, even when there is
no single resolving open for the whole scheme. -/
example {X : Scheme.{u}} {F : X.Modules} (h : F.IsPseudoCoherent) (U : X.Opens) :
    (F.restrict U.ι).IsFinitePresentation :=
  (h.restrict U.ι).isFinitePresentation

/-- The quasi-coherence consequence is available without unfolding the resolution predicate. -/
example {X : Scheme.{u}} {F : X.Modules} (h : F.IsPseudoCoherent) : F.IsQuasicoherent :=
  h.isQuasicoherent

/-- A cyclic module over a Noetherian ring gives a finite global sheaf presentation by
extracting the first two terms of its finite free resolution. This includes nonreduced rings
and modules of infinite projective dimension. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R) :
    ∃ p : (tilde (ModuleCat.of R (R ⧸ I))).Presentation, p.IsFinite :=
  (hasFiniteFreeResolution_tilde (M := ModuleCat.of R (R ⧸ I))
    TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing).exists_isFinite_presentation

/-- On an affine scheme, failure of finite presentation of a module rules out local
finite free resolutions of its associated sheaf. -/
example {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (hM : ¬ Module.FinitePresentation R M) : ¬ (tilde M).IsPseudoCoherent := by
  intro h
  exact hM ((ModuleCat.isFinitePresentation_tilde_iff M).mp h.isFinitePresentation)

/-- Zero sheaves on arbitrary schemes also satisfy the finite-presentation consequence. -/
example (X : Scheme.{u}) : (0 : X.Modules).IsFinitePresentation :=
  (IsPseudoCoherent.of_isZero (isZero_zero _)).isFinitePresentation

/-- Flat pullback preserves the full finite free resolution of a cyclic sheaf, even if
its source scheme is not Noetherian. -/
example (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f] :
    ((pullback f).obj (tilde (ModuleCat.of R (R ⧸ I)))).HasFiniteFreeResolution :=
  (hasFiniteFreeResolution_tilde (M := ModuleCat.of R (R ⧸ I))
    TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing).pullback f

/-- Pullback also preserves local resolutions; it does not require a globally chosen one. -/
example {X Y Z : Scheme.{u}} {F : Z.Modules} (h : F.IsPseudoCoherent)
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    ((pullback (f ≫ g)).obj F).IsPseudoCoherent :=
  ((h.pullback g).pullback f).of_iso ((pullbackComp f g).app F)

/-- Infinitely many polynomial variables and nilpotents are allowed on the new base. -/
example :
    ((pullback (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ZMod 4 →+* MvPolynomial ℕ (ZMod 4))))).obj
        (tilde (ModuleCat.of (ZMod 4) (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)})))).IsPseudoCoherent := by
  have : Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ZMod 4 →+* MvPolynomial ℕ (ZMod 4)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
      RingHom.flat_algebraMap_iff]
    infer_instance
  exact (isPseudoCoherent_tilde (R := CommRingCat.of (ZMod 4)) (M := ModuleCat.of (ZMod 4)
    (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}))
      TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing).pullback _

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

noncomputable section

section NegativeControl

open Classical in
/-- The presheaf submodule of `𝒪_{Spec R}` vanishing on `⊤` and equal to `⊤` on proper opens. -/
private def nonQuasicoherentPresheafSubmodule (R : Type u) [CommRing R] :
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf).val.Submodule where
  obj W := if W.unop = ⊤ then ⊥ else ⊤
  map {V W} f := by
    by_cases hW : W.unop = ⊤
    · have hV : V.unop = ⊤ := top_unique (hW ▸ leOfHom f.unop)
      simp [hV]
    · simp [hW]

/-- Over a local ring `R`, `nonQuasicoherentPresheafSubmodule R` is a subsheaf of `𝒪_{Spec R}`. -/
private def nonQuasicoherentSubmodule (R : Type u) [CommRing R] [IsLocalRing R] :
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf).Submodule where
  toSubmodule := nonQuasicoherentPresheafSubmodule R
  isSheaf := fun ⟨W⟩ s hs ↦ by
    classical
    by_cases hW : W = ⊤
    · subst hW
      -- In `Spec R` for a local ring `R`, the only open containing the closed point is `⊤`.
      obtain ⟨V, iVW, hsV, hxV⟩ := hs (IsLocalRing.closedPoint R) trivial
      have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hxV
      subst hV
      have hid : ∀ x, ((nonQuasicoherentPresheafSubmodule R).toSubfunctor.sieveOfSection x).arrows
          (𝟙 ⊤) → x ∈ (nonQuasicoherentPresheafSubmodule R).toSubfunctor.obj (op ⊤) :=
        fun _ hx ↦ by
          simpa only [Subfunctor.sieveOfSection, op_id, CategoryTheory.Functor.map_id,
            types_id_apply] using hx
      exact (PresheafOfModules.Submodule.mem_toSubfunctor_obj _ s).mp
        (hid s (Subsingleton.elim iVW (𝟙 ⊤) ▸ hsV))
    · simp [nonQuasicoherentPresheafSubmodule, hW]

/-- The `𝒪_{Spec R}`-module underlying `nonQuasicoherentSubmodule R`. -/
private abbrev nonQuasicoherentSheaf (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (.of R)).Modules :=
  (nonQuasicoherentSubmodule R).toSheafOfModules

/-- Global sections of `nonQuasicoherentSheaf R` vanish. -/
private theorem subsingleton_sections_top_nonQuasicoherentSheaf (R : Type u) [CommRing R]
    [IsLocalRing R] : Subsingleton Γ(nonQuasicoherentSheaf R, ⊤) := by
  have hbot : (nonQuasicoherentSubmodule R).toSubmodule.obj (op ⊤) = ⊥ := by
    simp [nonQuasicoherentSubmodule, nonQuasicoherentPresheafSubmodule]
  -- `Γ(N.toSheafOfModules, U)` is definitionally the carrier of `N.toSubmodule.obj (op U)`.
  let e : Γ(nonQuasicoherentSheaf R, ⊤) ≃ₗ[Γ(Spec (.of R), ⊤)]
      (⊥ : Submodule Γ(Spec (.of R), ⊤) Γ(Spec (.of R), ⊤)) :=
    LinearEquiv.ofEq ((nonQuasicoherentSubmodule R).toSubmodule.obj (op ⊤)) ⊥ hbot
  exact e.injective.subsingleton

/-- Over any proper open `U ≠ ⊤` of `Spec R`, sections of `nonQuasicoherentSheaf R` are
`Γ(Spec R, U)`-linearly equivalent to `Γ(Spec R, U)`. -/
private def sectionsEquivOfNeTop_nonQuasicoherentSheaf (R : Type u) [CommRing R] [IsLocalRing R]
    {U : (Spec (.of R)).Opens} (hU : U ≠ ⊤) :
    Γ(nonQuasicoherentSheaf R, U) ≃ₗ[Γ(Spec (.of R), U)] Γ(Spec (.of R), U) :=
  -- `Γ(N.toSheafOfModules, U)` is definitionally the carrier of `N.toSubmodule.obj (op U)`.
  LinearEquiv.ofTop ((nonQuasicoherentSubmodule R).toSubmodule.obj (op U))
    (by simp [nonQuasicoherentSubmodule, nonQuasicoherentPresheafSubmodule, hU])

/-- Sections of `nonQuasicoherentSheaf R` over every affine open of `Spec R` are pseudo-coherent. -/
private theorem isPseudoCoherentOver_sections_nonQuasicoherentSheaf (R : Type u) [CommRing R]
    [IsLocalRing R] (W : (Spec (.of R)).affineOpens) :
    TauCeti.Huber.IsPseudoCoherentOver Γ(Spec (.of R), W.val)
      Γ(nonQuasicoherentSheaf R, W.val) ⊤ := by
  by_cases hW : W.val = ⊤
  · have : Subsingleton Γ(nonQuasicoherentSheaf R, W.val) :=
      hW ▸ subsingleton_sections_top_nonQuasicoherentSheaf R
    exact TauCeti.Huber.IsPseudoCoherentOver.of_projective
  · exact TauCeti.Huber.IsPseudoCoherentOver.of_projective.of_equiv
      (sectionsEquivOfNeTop_nonQuasicoherentSheaf R hW).symm

/-- When `R` is a local integral domain that is not a field, `nonQuasicoherentSheaf R` is not
quasi-coherent. -/
private theorem not_isQuasicoherent_nonQuasicoherentSheaf (R : Type u) [CommRing R] [IsDomain R]
    [IsLocalRing R] (hR : ¬ IsField R) : ¬ (nonQuasicoherentSheaf R).IsQuasicoherent := by
  intro hqc
  let X : Scheme.{u} := Spec (.of R)
  let F : X.Modules := nonQuasicoherentSheaf R
  have hm_ne : IsLocalRing.maximalIdeal R ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hR
  obtain ⟨r, hr_mem, hr_ne⟩ := (Submodule.ne_bot_iff _).mp hm_ne
  let f : Γ(X, ⊤) := (Scheme.ΓSpecIso (.of R)).inv r
  have hD_ne_top : X.basicOpen f ≠ ⊤ := by
    intro htop
    have hclosed : IsLocalRing.closedPoint R ∈ PrimeSpectrum.basicOpen r := by
      rw [← basicOpen_eq_of_affine (R := .of R) r, htop]
      trivial
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hclosed hr_mem
  have hf_ne : f ≠ 0 := fun hf0 ↦
    hr_ne ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
      (hf0.trans (map_zero _).symm))
  have : IsDomain Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain R
  have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    (isAffineOpen_top X).isLocalization_basicOpen f
  have : IsDomain Γ(X, X.basicOpen f) :=
    IsLocalization.Away.isDomain Γ(X, X.basicOpen f) hf_ne
  have : Subsingleton Γ(F, ⊤) := subsingleton_sections_top_nonQuasicoherentSheaf R
  have : IsLocalizedModule.Away f (F.basicOpenRestrict f) :=
    F.isLocalizedModule_basicOpenRestrict (isAffineOpen_top X) f
  have : Subsingleton Γ(F, X.basicOpen f) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers f) (F.basicOpenRestrict f)
  have : Subsingleton Γ(X, X.basicOpen f) :=
    (sectionsEquivOfNeTop_nonQuasicoherentSheaf R hD_ne_top).symm.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton Γ(X, X.basicOpen f)

/-- **Quasi-coherence cannot be omitted from `isPseudoCoherent_iff_forall_affineOpens`.** On the
spectrum of any local integral domain `R` that is not a field, there exists an `𝒪_{Spec R}`-module
`F` whose sections over every affine open `W` are pseudo-coherent over `Γ(Spec R, W)`, yet `F` is
neither quasi-coherent nor pseudo-coherent. -/
public theorem exists_isPseudoCoherentOver_and_not_isQuasicoherent_of_not_isField (R : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] (hR : ¬ IsField R) :
    ∃ F : (Spec (.of R)).Modules,
      (∀ W : (Spec (.of R)).affineOpens,
        TauCeti.Huber.IsPseudoCoherentOver Γ(Spec (.of R), W.val) Γ(F, W.val) ⊤) ∧
      ¬ F.IsQuasicoherent ∧ ¬ F.IsPseudoCoherent :=
  ⟨nonQuasicoherentSheaf R,
    isPseudoCoherentOver_sections_nonQuasicoherentSheaf R,
    not_isQuasicoherent_nonQuasicoherentSheaf R hR,
    fun hpc ↦ not_isQuasicoherent_nonQuasicoherentSheaf R hR hpc.isQuasicoherent⟩

/-- Over the spectrum of any discrete valuation ring `R`, there exists an `𝒪_{Spec R}`-module whose
sections over every affine open are pseudo-coherent, yet which is neither quasi-coherent nor
pseudo-coherent. -/
public theorem exists_isPseudoCoherentOver_and_not_isQuasicoherent_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ F : (Spec (.of R)).Modules,
      (∀ W : (Spec (.of R)).affineOpens,
        TauCeti.Huber.IsPseudoCoherentOver Γ(Spec (.of R), W.val) Γ(F, W.val) ⊤) ∧
      ¬ F.IsQuasicoherent ∧ ¬ F.IsPseudoCoherent :=
  exists_isPseudoCoherentOver_and_not_isQuasicoherent_of_not_isField R
    (IsDiscreteValuationRing.not_isField R)

end NegativeControl

end

end TauCeti.AlgebraicGeometry
