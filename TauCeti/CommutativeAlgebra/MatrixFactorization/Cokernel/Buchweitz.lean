/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Hypersurface
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface
public import TauCeti.RingTheory.RegularLocalRing.AuslanderBuchsbaum
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Buchweitz's hypersurface comparison for maximal Cohen–Macaulay modules

Over a commutative ring `S` of bounded projective dimension with `w ∈ nonZeroDivisors S`, a
finitely presented `S ⧸ (w)`-module is Gorenstein-projective iff `pd_S M ≤ 1`
(`TauCeti.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`). Over a local hypersurface
`R = S ⧸ (w)` in a regular local ring `S`, combining this with
`TauCeti.hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth` yields the
Buchweitz–Eisenbud four-way equivalence (`TauCeti.isGorensteinProjective_quotient_tfae`). Since
Gorenstein-projective modules are finitely generated, the Gorenstein-projective `S ⧸ (w)`-modules
are exactly the finitely generated maximal Cohen–Macaulay ones, with no finiteness hypothesis on
the module (`TauCeti.isGorensteinProjective_quotient_iff_finite_and_ringKrullDim_le_depth`).

Over a Cohen–Macaulay local ring `S`, the cokernel of the reduction modulo `w` of a
finite-projective matrix factorization of `w` is already maximal Cohen–Macaulay
(`TauCeti.MatrixFactorization.ringKrullDim_quotient_le_depth_quotientCokernel`).

For a nonzero element `w` in a regular local ring `S` with local quotient `R = S ⧸ (w)`, this file
establishes **Buchweitz's hypersurface identification**: `IsGorensteinProjective R` agrees with
`IsFiniteMaximalCohenMacaulay R`
(`isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay`), making
`MaximalCohenMacaulayModuleCat R` Frobenius
(`MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius`) and triangulatedly stably equivalent to
`GorensteinProjectiveModuleCat R` (`MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence`,
`MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence`,
`MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_isTriangulated`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6 and Corollary 6.3.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4,
  Lemma 4.2.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

section UpstreamCharacterizations

open Ideal

section FiniteGlobalDimension

variable {S : Type u} [CommRing S] {w : S}

/-- Over a commutative ring `S` of projective dimension bounded by `d`, a finitely presented
`S ⧸ (w)`-module (`w ∈ nonZeroDivisors S`) is Gorenstein-projective iff `pd_S M ≤ 1`. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE
    (hw : w ∈ nonZeroDivisors S) (d : ℕ) (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.FinitePresentation (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have : Module.FinitePresentation S (S ⧸ span {w}) :=
    Module.finitePresentation_of_surjective (span {w}).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span_singleton w)
  let : Module S M := Module.compHom M (algebraMap S (S ⧸ span {w}))
  have : IsScalarTower S (S ⧸ span {w}) M := .of_compHom S (S ⧸ span {w}) M
  have : Module.FinitePresentation S M := .trans (R := S) (M := M) (S ⧸ span {w})
  have : Module.FinitePresentation S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M) :=
    .of_equiv (ModuleCat.restrictScalarsAlgebraMapIso M).symm.toLinearEquiv
  exact ⟨fun hM ↦ hM.hasProjectiveDimensionLE_restrictScalars_quotient hw d hd,
    MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hw M⟩

/-- Noetherian specialization of `isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isNoetherianRing
    [IsNoetherianRing (S ⧸ span {w})] (hw : w ∈ nonZeroDivisors S) (d : ℕ)
    (hd : ∀ N : ModuleCat.{u} S, HasProjectiveDimensionLE N d)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  have := Module.finitePresentation_of_finite (S ⧸ span {w}) M
  exact isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE hw d hd M

end FiniteGlobalDimension

namespace MatrixFactorization

/-- **Cokernels of matrix factorizations are maximal Cohen–Macaulay.** Let `S` be a
Cohen–Macaulay Noetherian local ring and `w` a non-zero-divisor with `S ⧸ (w)` local. The cokernel
of the reduction modulo `w` of a finite-projective matrix factorization of `w` has depth at least
`dim S ⧸ (w)`. -/
theorem ringKrullDim_quotient_le_depth_quotientCokernel {S : Type u} [CommRing S]
    [_root_.IsLocalRing S] [IsNoetherianRing S] {w : S} [_root_.IsLocalRing (S ⧸ span {w})]
    (hS : Module.IsCohenMacaulay S S) (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    ringKrullDim (S ⧸ span {w}) ≤
      _root_.IsLocalRing.depth (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (span {w}))).obj X)).obj :=
  ringKrullDim_le_depth_of_hasProjectiveDimensionLE_restrictScalars_quotient
    hS hw _
    ((exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw _).1
      ⟨X, ⟨Iso.refl _⟩⟩)

end MatrixFactorization

namespace IsRegularRing

variable {S : Type u} [CommRing S] [IsRegularRing S] {w : S}

/-- Regular-ring specialization (`ringKrullDim S < ⊤`) of
`isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`. -/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    (hdim : ringKrullDim S < ⊤) (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ span {w})) [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim S ≤ d := by
    cases h : ringKrullDim S with
    | bot => exact ⟨0, bot_le⟩
    | coe e => lift e to ℕ using fun he ↦ hdim.ne (by simp [h, he]); exact ⟨e, le_rfl⟩
  exact isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isNoetherianRing hw d
    (IsRegularRing.hasProjectiveDimensionLE hd) M

end IsRegularRing

section RegularLocalRing

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}

/-- Regular-local specialization of `isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE`.
-/
theorem isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
        1 :=
  IsRegularRing.isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_ringKrullDim_lt_top
    ringKrullDim_lt_top hw M

variable [_root_.IsLocalRing (S ⧸ span {w})]

/-- **Buchweitz–Eisenbud characterization:** over the local hypersurface `S ⧸ (w)` in a regular
local ring `S`, a finitely generated module `M` is Gorenstein-projective iff
`dim (S ⧸ (w)) ≤ depth M`. -/
theorem isGorensteinProjective_quotient_iff_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) :=
  (isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M).trans
    (hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M)

/-- Over the local hypersurface `S ⧸ (w)` in a regular local ring `S`, an `S ⧸ (w)`-module is
Gorenstein-projective iff it is finitely generated and `dim (S ⧸ (w)) ≤ depth M`. Unlike
`isGorensteinProjective_quotient_iff_ringKrullDim_le_depth`, no finiteness is assumed. -/
theorem isGorensteinProjective_quotient_iff_finite_and_ringKrullDim_le_depth
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w})) :
    IsGorensteinProjective (S ⧸ span {w}) M ↔
      Module.Finite (S ⧸ span {w}) M ∧
        ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞) := by
  refine ⟨fun hM ↦ ?_, fun ⟨_, hM⟩ ↦ ?_⟩
  · have := hM.finite
    exact ⟨this, (isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).1 hM⟩
  · exact (isGorensteinProjective_quotient_iff_ringKrullDim_le_depth hw M).2 hM

/-- **Four-way characterization of maximal Cohen–Macaulay modules over a local hypersurface**
(Eisenbud, Corollary 6.3; Buchweitz, Lemma 4.2.2). -/
theorem isGorensteinProjective_quotient_tfae
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ span {w}))
    [Module.Finite (S ⧸ span {w}) M] :
    List.TFAE
      [IsGorensteinProjective (S ⧸ span {w}) M,
        HasProjectiveDimensionLE ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {w}))).obj M)
          1,
        ∃ X : MatrixFactorization S w, Nonempty ((MatrixFactorization.cokernelFunctor.obj
          ((MatrixFactorization.baseChangeFunctor (Ideal.Quotient.mk (span {w}))).obj X)).obj ≅ M),
        ringKrullDim (S ⧸ span {w}) ≤ (_root_.IsLocalRing.depth M : WithBot ℕ∞)] := by
  tfae_have 1 ↔ 2 :=
    isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing hw M
  tfae_have 3 ↔ 2 :=
    MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE_of_isNoetherianRing
      hw M
  tfae_have 2 ↔ 4 :=
    hasProjectiveDimensionLE_restrictScalars_quotient_iff_ringKrullDim_le_depth hw M
  tfae_finish

end RegularLocalRing

end UpstreamCharacterizations

section BuchweitzComparison

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- **Buchweitz's hypersurface identification.** Over `R = S ⧸ (w)` (`w ≠ 0`), finitely generated
Gorenstein-projective `R`-modules coincide with finite maximal Cohen–Macaulay `R`-modules. -/
theorem isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay (hw : w ≠ 0)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w})) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) M ↔
      IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w}) M := by
  have := TauCeti.IsRegularLocalRing.isDomain (R := S)
  have hreg : w ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hw
  rw [isFiniteMaximalCohenMacaulay_iff]
  refine ⟨fun hM ↦ ?_, fun ⟨hfin, hmcm⟩ ↦ ?_⟩
  · have := hM.finite
    exact ⟨‹_›, (IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE
      hw M).2 ((isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing
        hreg M).1 hM)⟩
  · have := hfin
    exact (isGorensteinProjective_quotient_iff_hasProjectiveDimensionLE_of_isRegularLocalRing
      hreg M).2
      ((IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE hw M).1
        hmcm)

/-- Over `R = S ⧸ (w)` (`w ≠ 0`), `IsGorensteinProjective R = IsFiniteMaximalCohenMacaulay R`. -/
theorem isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay (hw : w ≠ 0) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) =
      IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w}) :=
  funext fun M ↦ propext (isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay hw M)

namespace MaximalCohenMacaulayModuleCat

/-- The additive equivalence `MCM-(S ⧸ (w)) ≌ Gproj-(S ⧸ (w))` induced by the identity. -/
def gorensteinProjectiveEquivalence (hw : w ≠ 0) :
    MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w}) ≌
      GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w}) where
  functor := ObjectProperty.ιOfLE
    (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).ge
  inverse := ObjectProperty.ιOfLE
    (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance (hw : w ≠ 0) : (gorensteinProjectiveEquivalence hw).functor.Additive :=
  inferInstanceAs (ObjectProperty.ιOfLE
    (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).ge).Additive

instance (hw : w ≠ 0) : (gorensteinProjectiveEquivalence hw).inverse.Additive :=
  inferInstanceAs (ObjectProperty.ιOfLE
    (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).le).Additive

/-- On underlying modules, `gorensteinProjectiveEquivalence` is the identity. -/
@[simp]
theorem gorensteinProjectiveEquivalence_functor_obj_obj (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    ((gorensteinProjectiveEquivalence hw).functor.obj X).obj = X.obj := (rfl)

/-- On underlying modules, `(gorensteinProjectiveEquivalence hw).inverse` is the identity. -/
@[simp]
theorem gorensteinProjectiveEquivalence_inverse_obj_obj (hw : w ≠ 0)
    (Y : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})) :
    ((gorensteinProjectiveEquivalence hw).inverse.obj Y).obj = Y.obj := (rfl)

/-- On underlying morphisms, `gorensteinProjectiveEquivalence.functor` is the identity. -/
@[simp]
theorem gorensteinProjectiveEquivalence_functor_map_hom (hw : w ≠ 0)
    {X Y : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})} (f : X ⟶ Y) :
    ((gorensteinProjectiveEquivalence hw).functor.map f).hom =
      eqToHom (gorensteinProjectiveEquivalence_functor_obj_obj hw X) ≫ f.hom ≫
        eqToHom (gorensteinProjectiveEquivalence_functor_obj_obj hw Y).symm :=
  eq_of_heq <|
    (by unfold gorensteinProjectiveEquivalence; rfl :
      ((gorensteinProjectiveEquivalence hw).functor.map f).hom ≍ f.hom).trans
    ((eqToHom_comp_heq
        (f.hom ≫ eqToHom (gorensteinProjectiveEquivalence_functor_obj_obj hw Y).symm)
        (gorensteinProjectiveEquivalence_functor_obj_obj hw X)).trans
      (comp_eqToHom_heq f.hom
        (gorensteinProjectiveEquivalence_functor_obj_obj hw Y).symm)).symm

/-- On underlying morphisms, `gorensteinProjectiveEquivalence.inverse` is the identity. -/
@[simp]
theorem gorensteinProjectiveEquivalence_inverse_map_hom (hw : w ≠ 0)
    {X Y : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})} (f : X ⟶ Y) :
    ((gorensteinProjectiveEquivalence hw).inverse.map f).hom =
      eqToHom (gorensteinProjectiveEquivalence_inverse_obj_obj hw X) ≫ f.hom ≫
        eqToHom (gorensteinProjectiveEquivalence_inverse_obj_obj hw Y).symm :=
  eq_of_heq <|
    (by unfold gorensteinProjectiveEquivalence; rfl :
      ((gorensteinProjectiveEquivalence hw).inverse.map f).hom ≍ f.hom).trans
    ((eqToHom_comp_heq
        (f.hom ≫ eqToHom (gorensteinProjectiveEquivalence_inverse_obj_obj hw Y).symm)
        (gorensteinProjectiveEquivalence_inverse_obj_obj hw X)).trans
      (comp_eqToHom_heq f.hom
        (gorensteinProjectiveEquivalence_inverse_obj_obj hw Y).symm)).symm

/-- `gorensteinProjectiveEquivalence.functor` commutes with the subcategory inclusions. -/
theorem gorensteinProjectiveEquivalence_functor_comp_ι (hw : w ≠ 0) :
    (gorensteinProjectiveEquivalence hw).functor ⋙ (IsGorensteinProjective _).ι =
      (IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})).ι := (rfl)

/-- `gorensteinProjectiveEquivalence.inverse` commutes with the subcategory inclusions. -/
theorem gorensteinProjectiveEquivalence_inverse_comp_ι (hw : w ≠ 0) :
    (gorensteinProjectiveEquivalence hw).inverse ⋙ (IsFiniteMaximalCohenMacaulay.{u} _).ι =
      (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι := (rfl)

/-- `gorensteinProjectiveEquivalence.functor` preserves conflations. -/
theorem isConflationExact_gorensteinProjectiveEquivalence_functor (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).IsConflationExact
      (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).functor where
  map_conflation {T} hT := by
    rw [GorensteinProjectiveModuleCat.exactStructure_conflation_iff, ← ShortComplex.map_comp]
    exact ShortComplex.shortExact_of_iso
      (T.mapNatIso (eqToIso (gorensteinProjectiveEquivalence_functor_comp_ι hw).symm))
      ((exactStructure_conflation_iff _ T).1 hT)

/-- `gorensteinProjectiveEquivalence.inverse` preserves conflations. -/
theorem isConflationExact_gorensteinProjectiveEquivalence_inverse (hw : w ≠ 0) :
    (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w})).IsConflationExact
      (exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).inverse where
  map_conflation {T} hT := by
    rw [exactStructure_conflation_iff, ← ShortComplex.map_comp]
    exact ShortComplex.shortExact_of_iso
      (T.mapNatIso (eqToIso (gorensteinProjectiveEquivalence_inverse_comp_ι hw).symm))
      ((GorensteinProjectiveModuleCat.exactStructure_conflation_iff _ T).1 hT)

/-- Relative projectives of `MaximalCohenMacaulayModuleCat (S ⧸ (w))` are the projective modules. -/
@[simp]
theorem exactStructure_isProjective_iff (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (exactStructure (S ⧸ Ideal.span {w})).isProjective X ↔ Projective X.obj := by
  rw [← (exactStructure _).isProjective_map_equivalence_iff _ (gorensteinProjectiveEquivalence hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw) X,
    GorensteinProjectiveModuleCat.exactStructure_isProjective_iff,
    gorensteinProjectiveEquivalence_functor_obj_obj]

/-- Relative injectives of `MaximalCohenMacaulayModuleCat (S ⧸ (w))` are the projective modules. -/
@[simp]
theorem exactStructure_isInjective_iff (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (exactStructure (S ⧸ Ideal.span {w})).isInjective X ↔ Projective X.obj := by
  rw [← (exactStructure _).isInjective_map_equivalence_iff _ (gorensteinProjectiveEquivalence hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw) X,
    GorensteinProjectiveModuleCat.exactStructure_isInjective_iff,
    gorensteinProjectiveEquivalence_functor_obj_obj]

/-- **Frobenius structure on `MaximalCohenMacaulayModuleCat (S ⧸ (w))`** (`w ≠ 0`). -/
theorem exactStructure_isFrobenius (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).IsFrobenius :=
  have : (gorensteinProjectiveEquivalence hw).symm.functor.Additive :=
    inferInstanceAs (gorensteinProjectiveEquivalence hw).inverse.Additive
  (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).of_equivalence (gorensteinProjectiveEquivalence hw).symm
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)

/-- `gorensteinProjectiveEquivalence.functor` is stable conflation-exact. -/
theorem stableConflationExact_gorensteinProjectiveEquivalence_functor (hw : w ≠ 0) :
    StableConflationExact (exactStructure.{u} (S ⧸ Ideal.span {w}))
      (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).functor :=
  (isConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableConflationExact_of_equivalence
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw)

/-- `gorensteinProjectiveEquivalence.inverse` is stable conflation-exact. -/
theorem stableConflationExact_gorensteinProjectiveEquivalence_inverse (hw : w ≠ 0) :
    StableConflationExact (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (exactStructure.{u} (S ⧸ Ideal.span {w})) (gorensteinProjectiveEquivalence hw).inverse :=
  have : (gorensteinProjectiveEquivalence hw).symm.functor.Additive :=
    inferInstanceAs (gorensteinProjectiveEquivalence hw).inverse.Additive
  (isConflationExact_gorensteinProjectiveEquivalence_inverse
    hw).stableConflationExact_of_equivalence (e := (gorensteinProjectiveEquivalence hw).symm)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)

/-- **Buchweitz's stable equivalence** `stable(MCM-(S ⧸ (w))) ≌ stable(Gproj-(S ⧸ (w)))`. -/
def gorensteinProjectiveStableEquivalence (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).ProjectiveStableCategory ≌
      (GorensteinProjectiveModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (gorensteinProjectiveEquivalence hw)
    (stableConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw)
    (exactStructure_isFrobenius hw) GorensteinProjectiveModuleCat.exactStructure_isFrobenius

/-- The forward functor of `gorensteinProjectiveStableEquivalence` is the descended forward functor
of `gorensteinProjectiveEquivalence`. -/
@[simp]
theorem gorensteinProjectiveStableEquivalence_functor (hw : w ≠ 0) :
    (gorensteinProjectiveStableEquivalence hw).functor =
      (stableConflationExact_gorensteinProjectiveEquivalence_functor hw).stableFunctor
        (exactStructure_isFrobenius hw) :=
  StableConflationExact.stableEquivalence_functor _ _ _ _ _

/-- The inverse functor of `gorensteinProjectiveStableEquivalence` is the descended inverse
functor of `gorensteinProjectiveEquivalence`. -/
@[simp]
theorem gorensteinProjectiveStableEquivalence_inverse (hw : w ≠ 0) :
    (gorensteinProjectiveStableEquivalence hw).inverse =
      (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw).stableFunctor
        GorensteinProjectiveModuleCat.exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_inverse _ _ _ _ _

/-- Shift compatibility for the forward functor of `gorensteinProjectiveStableEquivalence`. -/
@[instance_reducible]
def gorensteinProjectiveStableEquivalenceFunctorCommShift (hw : w ≠ 0) :
    letI := (exactStructure_isFrobenius hw).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    (gorensteinProjectiveStableEquivalence hw).functor.CommShift ℤ :=
  letI := (exactStructure_isFrobenius hw).stableHasShift
  letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  letI := (stableConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableFunctorCommShift (exactStructure_isFrobenius hw)
    GorensteinProjectiveModuleCat.exactStructure_isFrobenius
  Functor.CommShift.ofIso (eqToIso (gorensteinProjectiveStableEquivalence_functor hw).symm) ℤ

/-- `gorensteinProjectiveStableEquivalence_functor` commutes with integral shifts. -/
theorem gorensteinProjectiveStableEquivalence_functor_commShift (hw : w ≠ 0) :
    letI := (exactStructure_isFrobenius hw).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := (stableConflationExact_gorensteinProjectiveEquivalence_functor
      hw).stableFunctorCommShift (exactStructure_isFrobenius hw)
      GorensteinProjectiveModuleCat.exactStructure_isFrobenius
    letI := gorensteinProjectiveStableEquivalenceFunctorCommShift hw
    NatTrans.CommShift (eqToIso (gorensteinProjectiveStableEquivalence_functor hw).symm).hom ℤ := by
  let := (exactStructure_isFrobenius hw).stableHasShift
  let := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  let := (stableConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableFunctorCommShift (exactStructure_isFrobenius hw)
    GorensteinProjectiveModuleCat.exactStructure_isFrobenius
  exact Functor.CommShift.ofIso_compatibility
    (eqToIso (gorensteinProjectiveStableEquivalence_functor hw).symm) ℤ

/-- **Buchweitz's stable equivalence is triangulated.** -/
theorem gorensteinProjectiveStableEquivalence_isTriangulated (hw : w ≠ 0) :
    letI := (exactStructure_isFrobenius hw).stableHasShift
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := (exactStructure_isFrobenius hw).stableShiftFunctor_additive
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius hw).stablePretriangulated
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stablePretriangulated
    letI := gorensteinProjectiveStableEquivalenceFunctorCommShift hw
    letI := (gorensteinProjectiveStableEquivalence hw).commShiftInverse ℤ
    letI := (gorensteinProjectiveStableEquivalence hw).commShift_of_functor ℤ
    (gorensteinProjectiveStableEquivalence hw).IsTriangulated := by
  have hE := exactStructure_isFrobenius hw
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE.stableHasShift; let := hE'.stableHasShift
  let := hE.stableShiftFunctor_additive; let := hE'.stableShiftFunctor_additive
  let := hE.stablePretriangulated; let := hE'.stablePretriangulated
  let := (stableConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableFunctorCommShift hE hE'
  let := gorensteinProjectiveStableEquivalenceFunctorCommShift hw
  let := (gorensteinProjectiveStableEquivalence hw).commShiftInverse ℤ
  let := (gorensteinProjectiveStableEquivalence hw).commShift_of_functor ℤ
  have := (stableConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableFunctorIsTriangulated hE hE'
  have := gorensteinProjectiveStableEquivalence_functor_commShift hw
  exact Equivalence.IsTriangulated.mk' _
    (Functor.isTriangulated_of_iso
      (eqToIso (gorensteinProjectiveStableEquivalence_functor hw).symm))

end MaximalCohenMacaulayModuleCat
end BuchweitzComparison
end TauCeti
