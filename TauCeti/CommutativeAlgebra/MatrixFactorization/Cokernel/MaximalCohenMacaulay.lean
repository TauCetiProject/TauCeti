/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Equivalence
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence
import TauCeti.RingTheory.LocalRing.Module

/-!
# Matrix factorizations and stable maximal Cohen–Macaulay modules over a local hypersurface

Let `(S, 𝔪)` be a commutative regular local ring and let `w ∈ S` be a nonzero element with local
quotient `R = S ⧸ (w)` (equivalently, `0 ≠ w ∈ 𝔪`, a nonzero nonunit non-zero-divisor in `S`).
Over `S`, finitely generated projective modules are finite free, so `MatrixFactorization S w` is the
category of finite free matrix factorizations of `w` (`isProjective_iff_free`).

This file establishes both halves of the local hypersurface comparison for maximal Cohen–Macaulay
modules:

1. **Buchweitz's hypersurface identification.** A finitely generated `R`-module has projective
   dimension at most one over `S` if and only if it is maximal Cohen–Macaulay over `R`
   (`TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE`), and
   also if and only if it is Gorenstein-projective over `R`. Consequently, the object properties
   `IsGorensteinProjective R` and `IsFiniteMaximalCohenMacaulay R` coincide
   (`TauCeti.isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay`), the category
   `MaximalCohenMacaulayModuleCat R` with its inherited exact structure is Frobenius with the
   projective `R`-modules as projective-injectives (`exactStructure_isFrobenius`), and the identity
   on `ModuleCat R` induces an exact equivalence `MCM-R ≌ Gproj-R` descending to a triangulated
   equivalence `stable(MCM-R) ≌ stable(Gproj-R)` (`gorensteinProjectiveStableEquivalence`).
2. **Eisenbud's cokernel equivalence.** Reducing a finite free matrix factorization of `w` modulo
   `w` and taking the cokernel of `d₀'` defines an exact additive functor
   `quotientMaximalCohenMacaulayCokernel` from `MatrixFactorization S w` to
   `MaximalCohenMacaulayModuleCat R` which is essentially surjective already before passing to
   stable categories, and descends to a triangulated equivalence
   `quotientMaximalCohenMacaulayStableCokernelEquivalence : HMF(S, w) ≌ stable(MCM-R)`
   compatible with `quotientGorensteinProjectiveStableCokernel` along the Buchweitz comparison.

## Main definitions

* `TauCeti.MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence`: the exact additive
  equivalence `MCM-(S ⧸ (w)) ≌ Gproj-(S ⧸ (w))`.
* `TauCeti.MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence`: the induced
  triangulated equivalence `stable(MCM-(S ⧸ (w))) ≌ stable(Gproj-(S ⧸ (w)))`.
* `TauCeti.MatrixFactorization.quotientMaximalCohenMacaulayCokernel`: the reduced cokernel functor
  `MatrixFactorization S w ⥤ MaximalCohenMacaulayModuleCat (S ⧸ (w))`.
* `TauCeti.MatrixFactorization.HomotopyCategory.quotientMaximalCohenMacaulayStableCokernel` and
  `quotientMaximalCohenMacaulayStableCokernelEquivalence`: the descended triangle functor and
  Eisenbud's triangulated equivalence `HMF(S, w) ≌ stable(MCM-(S ⧸ (w)))`.

## Main results

* `TauCeti.MatrixFactorization.isProjective_iff_free`: over a local ring `S`,
  `MatrixFactorization S w` consists of curved duplexes of finite free `S`-modules.
* `TauCeti.isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay`: over a local
  hypersurface `S ⧸ (w)` in a regular local ring `S`, finitely generated Gorenstein-projective
  modules coincide with finite maximal Cohen–Macaulay modules.
* `TauCeti.MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius`: finite maximal Cohen–Macaulay
  modules over `S ⧸ (w)` form a Frobenius exact category.
* `quotientMaximalCohenMacaulayStableCokernelEquivalence_isTriangulated`: Eisenbud's equivalence
  `HMF(S, w) ≌ stable(MCM-(S ⧸ (w)))` is triangulated.

## References

* David Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace TauCeti

/-! ### Finite free components over a local ring -/

namespace MatrixFactorization

section LocalRing

variable {S : Type u} [CommRing S] [IsLocalRing S] {w : S}

/-- Over a local ring, a curved duplex of finitely generated modules lies in
`MatrixFactorization S w` if and only if both components are free `S`-modules. -/
theorem isProjective_iff_free (X : CurvedDuplex (FGModuleCat.{u} S) w) :
    isProjective S w X ↔ Module.Free S X.X₀ ∧ Module.Free S X.X₁ :=
  ⟨fun ⟨h₀, h₁⟩ ↦
    ⟨by have := h₀; exact Module.free_of_projective_of_isLocalRing,
     by have := h₁; exact Module.free_of_projective_of_isLocalRing⟩,
   fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- Over a local ring, the even component of any matrix factorization is a finite free module. -/
instance free_X₀ (X : MatrixFactorization S w) : Module.Free S X.obj.X₀ :=
  have : Module.Projective S X.obj.X₀ := X.property.1
  Module.free_of_projective_of_isLocalRing

/-- Over a local ring, the odd component of any matrix factorization is a finite free module. -/
instance free_X₁ (X : MatrixFactorization S w) : Module.Free S X.obj.X₁ :=
  have : Module.Projective S X.obj.X₁ := X.property.2
  Module.free_of_projective_of_isLocalRing

end LocalRing

end MatrixFactorization

/-! ### Buchweitz's hypersurface identification: Gorenstein-projectives vs. MCM modules -/

section BuchweitzComparison

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- **Buchweitz's hypersurface identification.** Over a local hypersurface `R = S ⧸ (w)` cut out by
`w ≠ 0` in a regular local ring `S`, an `R`-module is finitely generated Gorenstein-projective if
and only if it is finitely generated and maximal Cohen–Macaulay. -/
theorem isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay (hw : w ≠ 0)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w})) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) M ↔
      IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w}) M := by
  have hreg : w ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hw
  rw [isFiniteMaximalCohenMacaulay_iff]
  constructor
  · intro hM
    have : Module.Finite (S ⧸ Ideal.span {w}) M := hM.finite
    exact ⟨inferInstance,
      (IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE hw M).2
        (hM.hasProjectiveDimensionLE_restrictScalars_quotient_of_isRegularLocalRing hreg)⟩
  · rintro ⟨hfin, hmcm⟩
    have : Module.Finite (S ⧸ Ideal.span {w}) M := hfin
    have : Module.Finite S
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) :=
      ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
        Ideal.Quotient.mk_surjective M).2 hfin
    have := Module.finitePresentation_of_finite S
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M)
    exact MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE hreg M
      ((IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE hw M).1
        hmcm)

/-- Over a local hypersurface `R = S ⧸ (w)` in a regular local ring `S` (`w ≠ 0`), the object
properties `IsGorensteinProjective R` and `IsFiniteMaximalCohenMacaulay R` are equal. -/
theorem isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay (hw : w ≠ 0) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) =
      IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w}) :=
  funext fun M ↦ propext (isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay hw M)

namespace MaximalCohenMacaulayModuleCat

/-- The additive equivalence `MCM-(S ⧸ (w)) ≌ Gproj-(S ⧸ (w))` induced by the identity on
`ModuleCat (S ⧸ (w))` over a local hypersurface in a regular local ring. -/
@[expose, simps]
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
  inferInstanceAs
    (ObjectProperty.ιOfLE
      (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).ge).Additive

instance (hw : w ≠ 0) : (gorensteinProjectiveEquivalence hw).inverse.Additive :=
  inferInstanceAs
    (ObjectProperty.ιOfLE
      (isGorensteinProjective_quotient_eq_isFiniteMaximalCohenMacaulay hw).le).Additive

/-- On underlying modules, `gorensteinProjectiveEquivalence` is the identity. -/
theorem gorensteinProjectiveEquivalence_functor_obj_obj (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    ((gorensteinProjectiveEquivalence hw).functor.obj X).obj = X.obj :=
  (rfl)

/-- On underlying modules, the inverse of `gorensteinProjectiveEquivalence` is the identity. -/
theorem gorensteinProjectiveEquivalence_inverse_obj_obj (hw : w ≠ 0)
    (Y : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})) :
    ((gorensteinProjectiveEquivalence hw).inverse.obj Y).obj = Y.obj :=
  (rfl)

/-- Followed by the inclusion into `ModuleCat`, `gorensteinProjectiveEquivalence.functor` is the
inclusion of `MaximalCohenMacaulayModuleCat`. -/
theorem gorensteinProjectiveEquivalence_functor_comp_ι (hw : w ≠ 0) :
    (gorensteinProjectiveEquivalence hw).functor ⋙
        (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι =
      (IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})).ι :=
  (rfl)

/-- Followed by the inclusion into `ModuleCat`, `gorensteinProjectiveEquivalence.inverse` is the
inclusion of `GorensteinProjectiveModuleCat`. -/
theorem gorensteinProjectiveEquivalence_inverse_comp_ι (hw : w ≠ 0) :
    (gorensteinProjectiveEquivalence hw).inverse ⋙
        (IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})).ι =
      (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι :=
  (rfl)

/-- The forward functor `MCM-(S ⧸ (w)) ⥤ Gproj-(S ⧸ (w))` preserves conflations. -/
theorem isConflationExact_gorensteinProjectiveEquivalence_functor (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).IsConflationExact
      (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).functor where
  map_conflation {T} hT := by
    rw [GorensteinProjectiveModuleCat.exactStructure_conflation_iff, ← ShortComplex.map_comp]
    exact ShortComplex.shortExact_of_iso
      (T.mapNatIso (eqToIso (gorensteinProjectiveEquivalence_functor_comp_ι hw).symm))
      ((exactStructure_conflation_iff _ T).1 hT)

/-- The inverse functor `Gproj-(S ⧸ (w)) ⥤ MCM-(S ⧸ (w))` preserves conflations. -/
theorem isConflationExact_gorensteinProjectiveEquivalence_inverse (hw : w ≠ 0) :
    (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w})).IsConflationExact
      (exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).inverse where
  map_conflation {T} hT := by
    rw [exactStructure_conflation_iff, ← ShortComplex.map_comp]
    exact ShortComplex.shortExact_of_iso
      (T.mapNatIso (eqToIso (gorensteinProjectiveEquivalence_inverse_comp_ι hw).symm))
      ((GorensteinProjectiveModuleCat.exactStructure_conflation_iff _ T).1 hT)

/-- Over a local hypersurface `S ⧸ (w)` in a regular local ring, the relative projectives of
`MaximalCohenMacaulayModuleCat (S ⧸ (w))` are exactly the projective (hence finite free) modules. -/
@[simp]
theorem exactStructure_isProjective_iff (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (exactStructure (S ⧸ Ideal.span {w})).isProjective X ↔ Projective X.obj := by
  rw [← (exactStructure _).isProjective_map_equivalence_iff _ (gorensteinProjectiveEquivalence hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw) X,
    GorensteinProjectiveModuleCat.exactStructure_isProjective_iff]
  rfl

/-- Over a local hypersurface `S ⧸ (w)` in a regular local ring, the relative injectives of
`MaximalCohenMacaulayModuleCat (S ⧸ (w))` are also the projective modules. -/
@[simp]
theorem exactStructure_isInjective_iff (hw : w ≠ 0)
    (X : MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (exactStructure (S ⧸ Ideal.span {w})).isInjective X ↔ Projective X.obj := by
  rw [← (exactStructure _).isInjective_map_equivalence_iff _ (gorensteinProjectiveEquivalence hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw) X,
    GorensteinProjectiveModuleCat.exactStructure_isInjective_iff]
  rfl

/-- **Frobenius structure on maximal Cohen–Macaulay modules.** Over a local hypersurface `S ⧸ (w)`
(`w ≠ 0`) in a regular local ring `S`, `MaximalCohenMacaulayModuleCat (S ⧸ (w))` with its inherited
exact structure is a Frobenius exact category. -/
theorem exactStructure_isFrobenius (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).IsFrobenius :=
  have : (gorensteinProjectiveEquivalence hw).symm.functor.Additive :=
    inferInstanceAs (gorensteinProjectiveEquivalence hw).inverse.Additive
  (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).of_equivalence (gorensteinProjectiveEquivalence hw).symm
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)

/-- The forward functor `MCM-(S ⧸ (w)) ⥤ Gproj-(S ⧸ (w))` is stable conflation-exact. -/
theorem stableConflationExact_gorensteinProjectiveEquivalence_functor (hw : w ≠ 0) :
    StableConflationExact (exactStructure.{u} (S ⧸ Ideal.span {w}))
      (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).functor :=
  (isConflationExact_gorensteinProjectiveEquivalence_functor
    hw).stableConflationExact_of_equivalence
    (isConflationExact_gorensteinProjectiveEquivalence_inverse hw)

/-- The inverse functor `Gproj-(S ⧸ (w)) ⥤ MCM-(S ⧸ (w))` is stable conflation-exact. -/
theorem stableConflationExact_gorensteinProjectiveEquivalence_inverse (hw : w ≠ 0) :
    StableConflationExact (GorensteinProjectiveModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (exactStructure.{u} (S ⧸ Ideal.span {w}))
      (gorensteinProjectiveEquivalence hw).inverse :=
  have : (gorensteinProjectiveEquivalence hw).symm.functor.Additive :=
    inferInstanceAs (gorensteinProjectiveEquivalence hw).inverse.Additive
  (isConflationExact_gorensteinProjectiveEquivalence_inverse
    hw).stableConflationExact_of_equivalence
    (e := (gorensteinProjectiveEquivalence hw).symm)
    (isConflationExact_gorensteinProjectiveEquivalence_functor hw)

/-- **Buchweitz's stable hypersurface equivalence.** Over a local hypersurface `S ⧸ (w)` (`w ≠ 0`)
in a regular local ring `S`, the stable category of finite maximal Cohen–Macaulay modules is
equivalent to the stable category of finitely generated Gorenstein-projective modules. -/
abbrev gorensteinProjectiveStableEquivalence (hw : w ≠ 0) :
    (exactStructure.{u} (S ⧸ Ideal.span {w})).ProjectiveStableCategory ≌
      (GorensteinProjectiveModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (gorensteinProjectiveEquivalence hw)
    (stableConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw)
    (exactStructure_isFrobenius hw)
    (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w}))

/-- **Buchweitz's stable equivalence is triangulated.** Both directions of
`gorensteinProjectiveStableEquivalence` are triangle functors for Happel's triangulations. -/
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
    letI := StableConflationExact.stableEquivalenceFunctorCommShift
      (stableConflationExact_gorensteinProjectiveEquivalence_functor hw)
      (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw)
      (exactStructure_isFrobenius hw) GorensteinProjectiveModuleCat.exactStructure_isFrobenius
    letI := StableConflationExact.stableEquivalenceInverseCommShift
      (stableConflationExact_gorensteinProjectiveEquivalence_functor hw)
      (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw)
      (exactStructure_isFrobenius hw) GorensteinProjectiveModuleCat.exactStructure_isFrobenius
    letI := (gorensteinProjectiveStableEquivalence hw).commShift_of_functor ℤ
    (gorensteinProjectiveStableEquivalence hw).IsTriangulated :=
  StableConflationExact.stableEquivalenceIsTriangulated
    (stableConflationExact_gorensteinProjectiveEquivalence_functor hw)
    (stableConflationExact_gorensteinProjectiveEquivalence_inverse hw)
    (exactStructure_isFrobenius hw)
    (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u} (A := S ⧸ Ideal.span {w}))

end MaximalCohenMacaulayModuleCat

/-! ### Eisenbud's cokernel functor and triangulated equivalence for MCM modules -/

namespace MatrixFactorization

/-- Over a local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a regular local ring `S`, the cokernel of the
reduction modulo `w` of any finite free matrix factorization of `w` is a finite maximal
Cohen–Macaulay `S ⧸ (w)`-module. -/
theorem isFiniteMaximalCohenMacaulay_cokernelFunctor_obj_baseChangeFunctor_obj (hw : w ≠ 0)
    (X : MatrixFactorization S w) :
    IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay hw _).1
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj
      (mem_nonZeroDivisors_of_ne_zero hw) X)

/-- **Eisenbud's cokernel functor.** Over a local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a regular
local ring `S`, reducing a finite free matrix factorization modulo `w` and taking the cokernel of
`d₀'` defines an additive functor to finite maximal Cohen–Macaulay `S ⧸ (w)`-modules. -/
def quotientMaximalCohenMacaulayCokernel (hw : w ≠ 0) :
    MatrixFactorization S w ⥤ MaximalCohenMacaulayModuleCat.{u} (S ⧸ Ideal.span {w}) :=
  ObjectProperty.lift _ (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙
      cokernelFunctor ⋙ forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _))
    (isFiniteMaximalCohenMacaulay_cokernelFunctor_obj_baseChangeFunctor_obj hw)

/-- The underlying module of `quotientMaximalCohenMacaulayCokernel` is the reduced cokernel. -/
@[simp]
theorem quotientMaximalCohenMacaulayCokernel_obj_obj (hw : w ≠ 0) (X : MatrixFactorization S w) :
    ((quotientMaximalCohenMacaulayCokernel hw).obj X).obj =
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (rfl)

/-- Followed by the inclusion into `ModuleCat (S ⧸ (w))`, the maximal Cohen–Macaulay cokernel
functor is the cokernel of the reduction modulo `w`. -/
theorem quotientMaximalCohenMacaulayCokernel_comp_ι (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayCokernel hw ⋙
        (IsFiniteMaximalCohenMacaulay.{u} (S ⧸ Ideal.span {w})).ι =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _) :=
  (rfl)

instance (hw : w ≠ 0) : (quotientMaximalCohenMacaulayCokernel hw).Additive := by
  unfold quotientMaximalCohenMacaulayCokernel
  infer_instance

/-- Natural isomorphism identifying `quotientMaximalCohenMacaulayCokernel` followed by
`gorensteinProjectiveEquivalence.functor` with `quotientGorensteinProjectiveCokernel`. -/
def quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence hw).functor ≅
      quotientGorensteinProjectiveCokernel (mem_nonZeroDivisors_of_ne_zero hw) :=
  ((IsGorensteinProjective (S ⧸ Ideal.span {w})).fullyFaithfulι.whiskeringRight _).preimageIso <|
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence_functor_comp_ι hw)) ≪≫
      eqToIso ((quotientMaximalCohenMacaulayCokernel_comp_ι hw).trans
        (quotientGorensteinProjectiveCokernel_comp_ι (mem_nonZeroDivisors_of_ne_zero hw)).symm)

/-- Natural isomorphism identifying `quotientGorensteinProjectiveCokernel` followed by
`gorensteinProjectiveEquivalence.inverse` with `quotientMaximalCohenMacaulayCokernel`. -/
def quotientGorensteinProjectiveCokernelCompInverseIso (hw : w ≠ 0) :
    quotientGorensteinProjectiveCokernel (mem_nonZeroDivisors_of_ne_zero hw) ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence hw).inverse ≅
      quotientMaximalCohenMacaulayCokernel hw :=
  ((IsFiniteMaximalCohenMacaulay.{u}
    (S ⧸ Ideal.span {w})).fullyFaithfulι.whiskeringRight _).preimageIso <|
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence_inverse_comp_ι hw)) ≪≫
      eqToIso ((quotientGorensteinProjectiveCokernel_comp_ι
        (mem_nonZeroDivisors_of_ne_zero hw)).trans
        (quotientMaximalCohenMacaulayCokernel_comp_ι hw).symm)

/-- The maximal Cohen–Macaulay cokernel functor preserves conflations and projective-injectives. -/
theorem stableConflationExact_quotientMaximalCohenMacaulayCokernel (hw : w ≠ 0) :
    StableConflationExact (splitExact S w)
      (MaximalCohenMacaulayModuleCat.exactStructure.{u} (S ⧸ Ideal.span {w}))
      (quotientMaximalCohenMacaulayCokernel hw) :=
  ((stableConflationExact_quotientGorensteinProjectiveCokernel
    (mem_nonZeroDivisors_of_ne_zero hw)).comp
    (MaximalCohenMacaulayModuleCat.stableConflationExact_gorensteinProjectiveEquivalence_inverse
      hw)).of_iso
    (quotientGorensteinProjectiveCokernelCompInverseIso hw)

/-- **Essential surjectivity before stabilization.** Every finite maximal Cohen–Macaulay
`S ⧸ (w)`-module is isomorphic to the reduced cokernel of a finite free matrix factorization of
`w`. -/
theorem quotientMaximalCohenMacaulayCokernel_essSurj (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayCokernel hw).EssSurj := by
  have := quotientGorensteinProjectiveCokernel_essSurj (mem_nonZeroDivisors_of_ne_zero hw)
    (IsLocalRing.maximalIdeal S).spanFinrank
    (IsRegularLocalRing.hasProjectiveDimensionLE
      (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).ge)
  exact Functor.essSurj_of_iso (quotientGorensteinProjectiveCokernelCompInverseIso hw)

/-- Null-homotopic morphisms of matrix factorizations map into the projective stable ideal of
`MaximalCohenMacaulayModuleCat (S ⧸ (w))`. -/
theorem quotientMaximalCohenMacaulayCokernel_map_mem_projectiveStableIdeal (hw : w ≠ 0)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (quotientMaximalCohenMacaulayCokernel hw).map g ∈
      (MaximalCohenMacaulayModuleCat.exactStructure
        (S ⧸ Ideal.span {w})).projectiveStableIdeal.hom _ _ := by
  have hmem :=
    (MaximalCohenMacaulayModuleCat.stableConflationExact_gorensteinProjectiveEquivalence_inverse
      hw).projectiveStableIdeal_le_comap GorensteinProjectiveModuleCat.exactStructure_isFrobenius
      _ _ (quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal
        (mem_nonZeroDivisors_of_ne_zero hw) hg)
  rw [← MorphismIdeal.mem_comap_hom, ← MorphismIdeal.comap_eq_of_iso
    (MaximalCohenMacaulayModuleCat.exactStructure (S ⧸ Ideal.span {w})).projectiveStableIdeal
    (quotientGorensteinProjectiveCokernelCompInverseIso hw), MorphismIdeal.comap_comp,
    MorphismIdeal.mem_comap_hom]
  exact hmem

namespace HomotopyCategory

/-- **Eisenbud's stable cokernel functor.** Over a local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a
regular local ring `S`, reducing a finite free matrix factorization modulo `w` and taking the
cokernel of `d₀'` descends to an additive functor `HMF(S, w) ⥤ stable(MCM-(S ⧸ (w)))`. -/
def quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    HomotopyCategory (S := S) (w := w) ⥤
      (MaximalCohenMacaulayModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  (nullHomotopic (S := S) (w := w)).lift
    (quotientMaximalCohenMacaulayCokernel hw ⋙
      (MaximalCohenMacaulayModuleCat.exactStructure
        (S ⧸ Ideal.span {w})).projectiveStableFunctor)
    (by
      intro X Y g hg
      rw [Functor.mem_kerIdeal_hom, Functor.comp_map,
        MorphismIdeal.quotientFunctor_map_eq_zero_iff]
      exact quotientMaximalCohenMacaulayCokernel_map_mem_projectiveStableIdeal hw hg)

instance (hw : w ≠ 0) : (quotientMaximalCohenMacaulayStableCokernel hw).Additive := by
  unfold quotientMaximalCohenMacaulayStableCokernel
  infer_instance

/-- The stable maximal Cohen–Macaulay cokernel functor is induced by
`quotientMaximalCohenMacaulayCokernel`. -/
theorem quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientMaximalCohenMacaulayStableCokernel hw =
      quotientMaximalCohenMacaulayCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.exactStructure
          (S ⧸ Ideal.span {w})).projectiveStableFunctor := by
  unfold quotientMaximalCohenMacaulayStableCokernel
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- Composed with `gorensteinProjectiveStableEquivalence`, the maximal Cohen–Macaulay stable
cokernel functor is naturally isomorphic to the Gorenstein-projective stable cokernel functor. -/
def quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso (hw : w ≠ 0) :
    quotientMaximalCohenMacaulayStableCokernel hw ⋙
        (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence hw).functor ≅
      quotientGorensteinProjectiveStableCokernel (mem_nonZeroDivisors_of_ne_zero hw) :=
  CategoryTheory.Quotient.natIsoLift (nullHomotopic (S := S) (w := w)).rel <|
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso (quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel hw)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (eqToIso (by
          rw [MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence,
            StableConflationExact.stableEquivalence_functor,
            StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map])) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (quotientMaximalCohenMacaulayCokernelCompGorensteinProjectiveIso hw) _ ≪≫
      eqToIso (quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel
        (mem_nonZeroDivisors_of_ne_zero hw)).symm

/-- Along `stableToHomotopy`, `quotientMaximalCohenMacaulayStableCokernel` is the stable functor
induced by `quotientMaximalCohenMacaulayCokernel`. -/
theorem stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel (hw : w ≠ 0) :
    stableToHomotopy S w ⋙ quotientMaximalCohenMacaulayStableCokernel hw =
      (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctor
        (splitExact_isFrobenius S w) := by
  apply CategoryTheory.Quotient.lift_unique' (splitExact S w).projectiveStableIdeal.rel
  rw [StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map,
    ← Functor.assoc, projectiveStableFunctor_comp_stableToHomotopy,
    quotientFunctor_comp_quotientMaximalCohenMacaulayStableCokernel]

/-- Natural isomorphism identifying `quotientMaximalCohenMacaulayStableCokernel` with the inverse
of `stableToHomotopy` followed by the descended exact cokernel functor. -/
def stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso (hw : w ≠ 0) :
    (stableToHomotopy S w).asEquivalence.inverse ⋙
        (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctor
          (splitExact_isFrobenius S w) ≅
      quotientMaximalCohenMacaulayStableCokernel hw :=
  Iso.inverseCompIso
    (eqToIso (stableToHomotopy_comp_quotientMaximalCohenMacaulayStableCokernel hw).symm)

/-- Shift compatibility of `quotientMaximalCohenMacaulayStableCokernel` with the parity shift on
`HMF(S, w)` and Happel's suspension shift on `stable(MCM-(S ⧸ (w)))`. -/
@[instance_reducible]
def quotientMaximalCohenMacaulayStableCokernelCommShift (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    (quotientMaximalCohenMacaulayStableCokernel hw).CommShift ℤ :=
  have hE := splitExact_isFrobenius S w
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  letI := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  letI := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
    hE hE'
  Functor.CommShift.ofIso (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw) ℤ

/-- **The maximal Cohen–Macaulay stable cokernel functor is a triangle functor.** -/
theorem quotientMaximalCohenMacaulayStableCokernel_isTriangulated (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius
      hw).stableShiftFunctor_additive
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stablePretriangulated
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    (quotientMaximalCohenMacaulayStableCokernel hw).IsTriangulated := by
  have hE := splitExact_isFrobenius S w
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let : (stableToHomotopy S w).asEquivalence.functor.CommShift ℤ := stableToHomotopyCommShift S w
  let := (stableToHomotopy S w).asEquivalence.commShiftInverse ℤ
  let := (stableToHomotopy S w).asEquivalence.commShift_of_functor ℤ
  let := (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorCommShift
    hE hE'
  let := quotientMaximalCohenMacaulayStableCokernelCommShift hw
  have : (stableToHomotopy S w).asEquivalence.IsTriangulated :=
    CategoryTheory.Equivalence.IsTriangulated.mk' _ (stableToHomotopy_isTriangulated S w)
  have :=
    (stableConflationExact_quotientMaximalCohenMacaulayCokernel hw).stableFunctorIsTriangulated
      hE hE'
  have := Functor.CommShift.ofIso_compatibility
    (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw) ℤ
  exact Functor.isTriangulated_of_iso
    (stableToHomotopyInverseCompMaximalCohenMacaulayStableFunctorIso hw)

/-- **Eisenbud's equivalence.** Over a local hypersurface `S ⧸ (w)` (`w ≠ 0`) in a regular local
ring `S`, the reduced cokernel functor `HMF(S, w) ⥤ stable(MCM-(S ⧸ (w)))` is an equivalence of
categories. -/
theorem quotientMaximalCohenMacaulayStableCokernel_isEquivalence (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayStableCokernel hw).IsEquivalence := by
  have := quotientGorensteinProjectiveStableCokernel_isEquivalence_of_isRegularLocalRing
    (mem_nonZeroDivisors_of_ne_zero hw)
  have : (quotientMaximalCohenMacaulayStableCokernel hw ⋙
      (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence
        hw).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (quotientMaximalCohenMacaulayStableCokernelCompGorensteinProjectiveStableIso hw).symm
  exact Functor.isEquivalence_of_comp_right _
    (MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence hw).functor

/-- **Eisenbud's equivalence** `HMF(S, w) ≌ stable(MCM-(S ⧸ (w)))` between the homotopy category of
finite free matrix factorizations of `w` and the stable category of finite maximal Cohen–Macaulay
`S ⧸ (w)`-modules, over a regular local ring `S` with local quotient `S ⧸ (w)` and `w ≠ 0`. -/
def quotientMaximalCohenMacaulayStableCokernelEquivalence (hw : w ≠ 0) :
    HomotopyCategory (S := S) (w := w) ≌
      (MaximalCohenMacaulayModuleCat.exactStructure.{u}
        (S ⧸ Ideal.span {w})).ProjectiveStableCategory :=
  haveI := quotientMaximalCohenMacaulayStableCokernel_isEquivalence hw
  (quotientMaximalCohenMacaulayStableCokernel hw).asEquivalence

/-- The forward functor of `quotientMaximalCohenMacaulayStableCokernelEquivalence` is
`quotientMaximalCohenMacaulayStableCokernel`. -/
@[simp]
theorem quotientMaximalCohenMacaulayStableCokernelEquivalence_functor (hw : w ≠ 0) :
    (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).functor =
      quotientMaximalCohenMacaulayStableCokernel hw :=
  (rfl)

/-- **Eisenbud's local hypersurface equivalence is triangulated.** Over a regular local ring `S`
with local hypersurface quotient `S ⧸ (w)` (`w ≠ 0`), `HMF(S, w) ≌ stable(MCM-(S ⧸ (w)))` is a
triangulated equivalence for the parity-shift triangulation of `HMF(S, w)` and Happel's
triangulation of `stable(MCM-(S ⧸ (w)))`. -/
theorem quotientMaximalCohenMacaulayStableCokernelEquivalence_isTriangulated (hw : w ≠ 0) :
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stableHasShift
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius
      hw).stableShiftFunctor_additive
    letI := (MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw).stablePretriangulated
    letI := quotientMaximalCohenMacaulayStableCokernelCommShift hw
    letI : (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).functor.CommShift ℤ :=
      Functor.CommShift.ofIso
        (eqToIso (quotientMaximalCohenMacaulayStableCokernelEquivalence_functor hw).symm) ℤ
    letI := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShiftInverse ℤ
    letI := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShift_of_functor ℤ
    (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).IsTriangulated := by
  have hE' := MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius hw
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let := quotientMaximalCohenMacaulayStableCokernelCommShift hw
  let e := eqToIso (quotientMaximalCohenMacaulayStableCokernelEquivalence_functor hw).symm
  let : (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).functor.CommShift ℤ :=
    Functor.CommShift.ofIso e ℤ
  let := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShiftInverse ℤ
  let := (quotientMaximalCohenMacaulayStableCokernelEquivalence hw).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := quotientMaximalCohenMacaulayStableCokernel_isTriangulated hw
  exact CategoryTheory.Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

end HomotopyCategory

end MatrixFactorization

end BuchweitzComparison

end TauCeti
