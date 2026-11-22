/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence
public import TauCeti.RingTheory.CohenMacaulay.Maximal.Exact
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Buchweitz
import TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Buchweitz's comparison for maximal Cohen–Macaulay modules

For a nonzero element `w` in a regular local ring `S` with local hypersurface quotient
`R = S ⧸ (w)`, this file establishes **Buchweitz's hypersurface identification**: the finitely
generated Gorenstein-projective `R`-modules coincide with the finite maximal Cohen–Macaulay
`R`-modules (`TauCeti.isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay`), making
`MaximalCohenMacaulayModuleCat R` a Frobenius exact category
(`MaximalCohenMacaulayModuleCat.exactStructure_isFrobenius`) triangulatedly stably equivalent to
`GorensteinProjectiveModuleCat R` (`MaximalCohenMacaulayModuleCat.gorensteinProjectiveEquivalence`,
`MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence`,
`MaximalCohenMacaulayModuleCat.gorensteinProjectiveStableEquivalence_isTriangulated`).

As an application to minimal syzygies, a projective retract of a minimal syzygy of a finite
maximal Cohen–Macaulay module over `S ⧸ (w)` must vanish
(`TauCeti.isZero_projective_retract_minimal_syzygy_of_isMaximalCohenMacaulay`), proved by
factoring through the injective property of projectives in `MaximalCohenMacaulayModuleCat R` and
applying Nakayama's lemma (`TauCeti.isZero_of_range_le_jacobson_smul_of_retract_comp_eq`).

## References

* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4,
  Lemma 4.2.2.
* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6 and Corollary 6.3.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

noncomputable section

universe u v

open CategoryTheory Limits IsLocalRing

namespace TauCeti

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

section MinimalSyzygy

/-- **Nakayama criterion for retracts of syzygies.** If `ret : Retract P K` has retraction
extending across an inclusion `i : K ⟶ F` whose range lies in `Ring.jacobson R • ⊤`, and `P` is
finitely generated, then `P` is zero. -/
theorem isZero_of_range_le_jacobson_smul_of_retract_comp_eq
    {R : Type u} [CommRing R] {K F P : ModuleCat.{v} R} [Module.Finite R P]
    {i : K ⟶ F} (hi_min : LinearMap.range i.hom ≤ Ring.jacobson R • ⊤)
    (ret : Retract P K) (g : F ⟶ P) (hg : i ≫ g = ret.r) : IsZero P := by
  have htop : (⊤ : Submodule R P) ≤ Ring.jacobson R • ⊤ := fun x _ ↦ by
    have hx : g.hom (i.hom (ret.i.hom x)) = x := by
      have hcomp : ret.i ≫ i ≫ g = 𝟙 P := by rw [hg, ret.retract]
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using congrArg (fun f : P ⟶ P ↦ f.hom x) hcomp
    exact hx ▸ Submodule.smul_top_le_comap_smul_top (Ring.jacobson R) g.hom
      (hi_min ⟨ret.i.hom x, rfl⟩)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ Module.Finite.fg_top htop le_rfl
  have : Subsingleton P :=
    subsingleton_of_forall_eq 0 fun x ↦ (Submodule.mem_bot R).1 (hbot ▸ Submodule.mem_top)
  exact ModuleCat.isZero_of_subsingleton P

/-- A projective retract of a minimal syzygy of a finite maximal Cohen–Macaulay module over a
regular-local hypersurface quotient `S ⧸ (w)` (`w ≠ 0`) is zero. -/
theorem isZero_projective_retract_minimal_syzygy_of_isMaximalCohenMacaulay
    {S : Type u} [CommRing S] [IsRegularLocalRing S] {w : S}
    [_root_.IsLocalRing (S ⧸ Ideal.span {w})] (hw : w ≠ 0)
    {M F K : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M] [Module.Finite (S ⧸ Ideal.span {w}) F]
    [Module.Free (S ⧸ Ideal.span {w}) F] [Module.Finite (S ⧸ Ideal.span {w}) K]
    {i : K ⟶ F} {p : F ⟶ M} (hi : Function.Injective i.hom) (hip : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom)
    (hi_min : LinearMap.range i.hom ≤ maximalIdeal (S ⧸ Ideal.span {w}) • ⊤)
    (hM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (P : ModuleCat.{u} (S ⧸ Ideal.span {w})) [Projective P] (ret : Retract P K) :
    IsZero P := by
  let R := S ⧸ Ideal.span {w}
  have hF := (TauCeti.IsRegularLocalRing.isCohenMacaulay_quotient_span_singleton
    hw).isMaximalCohenMacaulay_of_free F
  have hK := Module.IsMaximalCohenMacaulay.of_exact_left hip hi hp hF
    (hM.ringKrullDim_le_depth.trans (le_add_of_nonneg_right zero_le_one))
  have hK_fin : IsFiniteMaximalCohenMacaulay.{u} R K := (isFiniteMaximalCohenMacaulay_iff R K).2
    ⟨‹_›, hK⟩
  have hP_mcm := hK_fin.of_retract ret
  have : Module.Finite R P := ((isFiniteMaximalCohenMacaulay_iff R P).1 hP_mcm).1
  let K' : MaximalCohenMacaulayModuleCat.{u} R := ⟨K, hK_fin⟩
  let F' : MaximalCohenMacaulayModuleCat.{u} R :=
    ⟨F, (isFiniteMaximalCohenMacaulay_iff R F).2 ⟨‹_›, hF⟩⟩
  let M' : MaximalCohenMacaulayModuleCat.{u} R :=
    ⟨M, (isFiniteMaximalCohenMacaulay_iff R M).2 ⟨‹_›, hM⟩⟩
  let P' : MaximalCohenMacaulayModuleCat.{u} R := ⟨P, hP_mcm⟩
  let T : ShortComplex (MaximalCohenMacaulayModuleCat.{u} R) :=
    ShortComplex.mk (X₁ := K') (X₂ := F') (X₃ := M') (ObjectProperty.homMk i)
      (ObjectProperty.homMk p)
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext hip.apply_apply_eq_zero)))
  have hT : (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).Conflation T :=
    (MaximalCohenMacaulayModuleCat.exactStructure_conflation_iff R T).2
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hip
        mono_f := (ModuleCat.mono_iff_injective i).2 hi
        epi_g := (ModuleCat.epi_iff_surjective p).2 hp }
  have hInj : (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).isInjective P' :=
    (MaximalCohenMacaulayModuleCat.exactStructure_isInjective_iff hw P').2 inferInstance
  have hinfl := (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).isInflation_f hT
  let r' : K' ⟶ P' := ObjectProperty.homMk ret.r
  let g := hInj.factorThru hinfl r'
  have hg : i ≫ g.hom = ret.r := congrArg InducedCategory.Hom.hom (hInj.comp_factorThru hinfl r')
  exact isZero_of_range_le_jacobson_smul_of_retract_comp_eq
    ((ringJacobson_eq_maximalIdeal (R := R)).symm ▸ hi_min) ret g.hom hg

end MinimalSyzygy

end TauCeti
