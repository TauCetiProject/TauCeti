/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Germ
public import TauCeti.Analysis.Meromorphic.PointTwist
public import TauCeti.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
import TauCeti.Geometry.Manifold.ChartedSpace
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order

/-!
# Point twists of divisor sheaves

This file constructs the actual short exact sequence of complex-vector-space sheaves
`0 → O(D) → O(D+x) → C_x → 0` for every divisor `D` on a Riemann surface. It uses the
preferred coordinate `chartAt ℂ x` to extract the coefficient of exponent `-D(x)-1`.
The target is Mathlib's skyscraper sheaf with universe-lifted complex coefficients.

Divisor sections are functions normalized to zero at allowed poles. The inclusion can therefore
change their centre values; it preserves their punctured coordinate germs. The kernel argument
uses the native order-filtration coefficient criterion, then fills removable singularities
with their holomorphic values and pins allowed poles to zero. Surjectivity is local: coordinate
monomials realize every new coefficient. No compactness, connectedness or effectiveness
assumption on the divisor is needed, and negative coefficients are included.

## Main declarations

* `divisorSections.toChartGerm`: the coordinate meromorphic germ of a normalized local section,
  compatible with restriction and divisor inclusions.
* `divisorSections.pointTwistCoefficient`: extraction of the newly permitted coefficient.
* `exists_section_toChartGerm_eq`: every meromorphic coordinate germ satisfying the divisor
  bound has an actual local divisor-section representative.
* `pointTwistMap` and `pointTwistCoefficientStalk`: the coefficient morphisms of sheaves and
  stalks; `pointTwistMap_stalk_surjective` proves local surjectivity.
* `pointTwistSequence_shortExact`: the actual divisor-sheaf short exact sequence. This supplies
  the sheaf-theoretic input to the Riemann–Roch induction, not its cohomology sequence or
  analytic finiteness theorem.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16.
-/

public noncomputable section

open CategoryTheory Limits Filter IsManifold Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]



namespace divisorSections

variable {D : WeilDivisor X} {U : Opens X} {x : X}

/-- The coefficient of the newly permitted pole or zero term at a point twist. -/
def pointTwistCoefficient (D : WeilDivisor X) (U : Opens X) (x : U) :
    divisorSections (D + WeilDivisor.ofPoint x.1) U →ₗ[ℂ] ℂ := by
  classical
  exact (meromorphicGerms.coeff (chartAt ℂ x.1 x.1) (-D x.1 - 1)).comp
    ((toChartGerm (D + WeilDivisor.ofPoint x.1) U x).codRestrict _ fun f ↦ by
      have hp : (WeilDivisor.ofPoint x.1) x.1 = 1 := WeilDivisor.coeff_ofPoint_self _
      simpa only [Finsupp.add_apply, hp, neg_add, sub_eq_add_neg] using
        toChartGerm_mem_orderGE f x)

/-- The point-twist coefficient is the meromorphic coefficient of its order-bounded
coordinate germ. -/
@[simp]
theorem pointTwistCoefficient_apply (D : WeilDivisor X) (U : Opens X) (x : U)
    (f : divisorSections (D + WeilDivisor.ofPoint x.1) U) :
    pointTwistCoefficient D U x f =
      meromorphicGerms.coeff (chartAt ℂ x.1 x.1) (-D x.1 - 1)
        ⟨toChartGerm (D + WeilDivisor.ofPoint x.1) U x f, by
          have hp : (WeilDivisor.ofPoint x.1) x.1 = 1 := WeilDivisor.coeff_ofPoint_self _
          simpa only [Finsupp.add_apply, hp, neg_add, sub_eq_add_neg] using
            toChartGerm_mem_orderGE f x⟩ := by
  rfl

/-- The new coefficient is zero precisely when the coordinate germ satisfies the old order
bound. This statement includes divisors with negative coefficients. -/
theorem pointTwistCoefficient_eq_zero_iff (f : divisorSections (D + WeilDivisor.ofPoint x) U)
    (hx : x ∈ U) :
    pointTwistCoefficient D U ⟨x, hx⟩ f = 0 ↔
      toChartGerm (D + WeilDivisor.ofPoint x) U ⟨x, hx⟩ f ∈
        meromorphicGerms.orderGE (chartAt ℂ x x) (-D x) := by
  classical
  rw [pointTwistCoefficient_apply, meromorphicGerms.coeff_eq_zero_iff]
  simp only [sub_add_cancel]

/-- The point-twist coefficient depends only on the germ, so it commutes with restriction. -/
theorem pointTwistCoefficient_restrict {V : Opens X} (h : V ≤ U) (hx : x ∈ V)
    (f : divisorSections (D + WeilDivisor.ofPoint x) U) :
    pointTwistCoefficient D V ⟨x, hx⟩
      ⟨f.1 ∘ Opens.inclusion h, comp_inclusion_mem_divisorSections h f.2⟩ =
        pointTwistCoefficient D U ⟨x, h hx⟩ f := by
  classical
  unfold pointTwistCoefficient
  simp only [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  simpa only [LinearMap.codRestrict_apply] using toChartGerm_restrict h hx f


/-- A section from the old divisor has zero newly permitted coefficient. -/
private theorem pointTwistCoefficient_mapOfLE (D : WeilDivisor X) (U : Opens X) (x : U)
    (f : (divisorSheaf D).obj.obj (op U)) :
    pointTwistCoefficient D U x (divisorSheafSectionsEquiv _ U
      ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x.1)).hom.app (op U) f)) = 0 := by
  apply (pointTwistCoefficient_eq_zero_iff _ x.2).2
  rw [toChartGerm_mapOfLE]
  exact toChartGerm_mem_orderGE _ x

end divisorSections




/-- Coefficient extraction on a section, with universe-lifted scalar target. -/
private def sectionPointTwistCoefficient (D : WeilDivisor X) (x : X) (U : Opens X)
    (hx : x ∈ U) :
    (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U) ⟶
      ModuleCat.of ℂ (ULift.{u} ℂ) :=
  ModuleCat.ofHom ((ULift.moduleEquiv.symm : ℂ ≃ₗ[ℂ] ULift.{u} ℂ).toLinearMap.comp
    ((divisorSections.pointTwistCoefficient D U ⟨x, hx⟩).comp
      (divisorSheafSectionsEquiv (D + WeilDivisor.ofPoint x) U).toLinearMap))

private theorem sectionPointTwistCoefficient_restrict (D : WeilDivisor X) (x : X)
    {U V : Opens X} (h : V ⟶ U) (hx : x ∈ V) :
    (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.map h.op ≫
      sectionPointTwistCoefficient D x V hx =
        sectionPointTwistCoefficient D x U (h.le hx) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  -- The module morphism is the lifted scalar coefficient after the section equivalence.
  change ULift.up (divisorSections.pointTwistCoefficient D V ⟨x, hx⟩
    (divisorSheafSectionsEquiv _ V ((divisorSheaf _).obj.map h.op f))) =
      ULift.up (divisorSections.pointTwistCoefficient D U ⟨x, h.le hx⟩
        (divisorSheafSectionsEquiv _ U f))
  congr 1
  have hs : divisorSheafSectionsEquiv (D + WeilDivisor.ofPoint x) V
      ((divisorSheaf (D + WeilDivisor.ofPoint x)).obj.map h.op f) =
      ⟨(divisorSheafSectionsEquiv _ U f).1 ∘ Opens.inclusion h.le,
        comp_inclusion_mem_divisorSections h.le (divisorSheafSectionsEquiv _ U f).2⟩ :=
    Subtype.ext (divisorSheafSectionsEquiv_map _ h f)
  rw [hs]
  exact divisorSections.pointTwistCoefficient_restrict h.le hx _

/-- Extract the newly permitted coefficient from the actual divisor-sheaf stalk. -/
def pointTwistCoefficientStalk (D : WeilDivisor X) (x : X) :
    TopCat.Presheaf.stalk (divisorSheaf (D + WeilDivisor.ofPoint x)).obj x ⟶
      ModuleCat.of ℂ (ULift.{u} ℂ) :=
  colimit.desc ((OpenNhds.inclusion (X := TopCat.of X) x).op ⋙
      (divisorSheaf (D + WeilDivisor.ofPoint x)).obj)
    { pt := ModuleCat.of ℂ (ULift.{u} ℂ)
      ι :=
        { app := fun U ↦ sectionPointTwistCoefficient D x (unop U).1 (unop U).2
          naturality := by
            intro U V h
            exact sectionPointTwistCoefficient_restrict D x
              ((OpenNhds.inclusion (X := TopCat.of X) x).map h.unop) (unop V).2 } }

/-- The stalk coefficient is computed on any section representing a germ. -/
private theorem germ_pointTwistCoefficientStalk (D : WeilDivisor X) (x : X) {U : Opens X}
    (hx : x ∈ U) :
    TopCat.Presheaf.germ (divisorSheaf (D + WeilDivisor.ofPoint x)).obj U x hx ≫
      pointTwistCoefficientStalk D x = sectionPointTwistCoefficient D x U hx :=
  colimit.ι_desc _ _


/-- The stalk coefficient on a section germ is the lifted divisor coefficient. -/
@[simp]
theorem pointTwistCoefficientStalk_germ (D : WeilDivisor X) (x : X) {U : Opens X}
    (hx : x ∈ U) (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U)) :
    pointTwistCoefficientStalk D x
        (TopCat.Presheaf.germ (divisorSheaf (D + WeilDivisor.ofPoint x)).obj U x hx f) =
      ULift.up (divisorSections.pointTwistCoefficient D U ⟨x, hx⟩
        (divisorSheafSectionsEquiv _ U f)) := by
  exact ConcreteCategory.congr_hom (germ_pointTwistCoefficientStalk D x hx) f


/-- The coefficient morphism from the actual point-twisted divisor sheaf to the skyscraper
sheaf at the twist point. -/
def pointTwistMap (D : WeilDivisor X) (x : X) [∀ U : Opens X, Decidable (x ∈ U)] :
    divisorSheaf (D + WeilDivisor.ofPoint x) ⟶
      skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ)) :=
  (stalkSkyscraperSheafAdjunction (X := TopCat.of X) (C := ModuleCat.{u} ℂ) x).homEquiv
    _ _ (pointTwistCoefficientStalk D x)

private theorem pointTwistMap_app_of_mem (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] {U : Opens X} (hx : x ∈ U) :
    (pointTwistMap D x).hom.app (op U) ≫ eqToHom (ite_eq_left hx) =
      sectionPointTwistCoefficient D x U hx := by
  erw [pointTwistMap, Adjunction.homEquiv_unit]
  -- The hom-equivalence unit is the presheaf unit followed by the skyscraper map.
  change (((stalkSkyscraperSheafAdjunction
    (X := TopCat.of X) (C := ModuleCat.{u} ℂ) x).unit.app
      (divisorSheaf (D + WeilDivisor.ofPoint x))).hom.app (op U) ≫
    (SkyscraperPresheafFunctor.map' (X := TopCat.of X) x
      (pointTwistCoefficientStalk D x)).app (op U)) ≫
      eqToHom (ite_eq_left hx) = _
  erw [TauCeti.Topology.stalkSkyscraperSheafAdjunction_unit_app_hom_app
    (C := ModuleCat.{u} ℂ) (X := TopCat.of X) x (divisorSheaf _) hx,
    SkyscraperPresheafFunctor.map'_app, dite_eq_left hx]
  erw [← germ_pointTwistCoefficientStalk D x hx]
  let G := TopCat.Presheaf.germ (divisorSheaf (D + WeilDivisor.ofPoint x)).obj U x hx
  let C := pointTwistCoefficientStalk D x
  let p : (skyscraperPresheaf (X := TopCat.of X) x
      (TopCat.Presheaf.stalk (divisorSheaf (D + WeilDivisor.ofPoint x)).obj x)).obj (op U) =
      TopCat.Presheaf.stalk (divisorSheaf (D + WeilDivisor.ofPoint x)).obj x := ite_eq_left hx
  let q : (skyscraperPresheaf (X := TopCat.of X) x
      (ModuleCat.of ℂ (ULift.{u} ℂ))).obj (op U) = ModuleCat.of ℂ (ULift.{u} ℂ) := ite_eq_left hx
  -- The local abbreviations isolate the transports between the two conditional fibres.
  change ((G ≫ eqToHom p.symm) ≫ (eqToHom p ≫ C ≫ eqToHom q.symm)) ≫ eqToHom q = G ≫ C
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]



/-- Coefficient extraction on a section containing the twist point is the lifted scalar
coefficient, after identifying the nonzero skyscraper fibre. -/
theorem pointTwistMap_app_apply_of_mem (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] {U : Opens X} (hx : x ∈ U)
    (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U)) :
    (eqToHom (ite_eq_left hx) :
      (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ))).obj.obj (op U) ⟶
        ModuleCat.of ℂ (ULift.{u} ℂ)) ((pointTwistMap D x).hom.app (op U) f) =
      ULift.up (divisorSections.pointTwistCoefficient D U ⟨x, hx⟩
        (divisorSheafSectionsEquiv _ U f)) := by
  exact ConcreteCategory.congr_hom (pointTwistMap_app_of_mem D x hx) f


/-- The divisor inclusion followed by the new-coefficient morphism is zero. -/
@[reassoc (attr := simp)]
theorem divisorSheafMapOfLE_comp_pointTwistMap (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) ≫ pointTwistMap D x = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  by_cases hx : x ∈ unop U
  · let e : (skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ))).obj.obj U ⟶
        ModuleCat.of ℂ (ULift.{u} ℂ) := eqToHom (ite_eq_left hx)
    have : IsIso e := Iso.isIso_hom (eqToIso (ite_eq_left hx))
    apply (cancel_mono e).1
    have h0 : (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U ≫
        sectionPointTwistCoefficient D x (unop U) hx = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      -- Unfolding the local section coefficient exposes its lifted scalar formula.
      change ULift.up (divisorSections.pointTwistCoefficient D (unop U) ⟨x, hx⟩
        (divisorSheafSectionsEquiv _ (unop U)
          ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U f))) = 0
      rw [divisorSections.pointTwistCoefficient_mapOfLE]
      rfl
    have hz : (0 : divisorSheaf D ⟶ skyscraperSheaf (X := TopCat.of X) x
        (ModuleCat.of ℂ (ULift.{u} ℂ))).hom.app U = 0 := by rfl
    calc
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) ≫ pointTwistMap D x).hom.app U ≫ e =
          ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U ≫
            (pointTwistMap D x).hom.app U) ≫ e :=
        congrArg (· ≫ e) (TopCat.Sheaf.comp_app (ModuleCat.{u} ℂ) (TopCat.of X) _ _ U)
      _ = (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U ≫
          ((pointTwistMap D x).hom.app U ≫ e) := Category.assoc _ _ _
      _ = (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U ≫
          sectionPointTwistCoefficient D x (unop U) hx :=
        congrArg ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app U ≫ ·)
          (pointTwistMap_app_of_mem D x hx)
      _ = 0 := h0
      _ = (0 : divisorSheaf D ⟶ skyscraperSheaf (X := TopCat.of X) x
          (ModuleCat.of ℂ (ULift.{u} ℂ))).hom.app U ≫ e :=
        ((congrArg (· ≫ e) hz).trans zero_comp).symm
  · exact ((ite_eq_right hx).symm.ndrec terminalIsTerminal).hom_ext _ _


section LocalLifting

variable [IsManifold 𝓘(ℂ) 1 X]

/-- A section whose germ satisfies the stronger divisor bound lifts locally through the
actual divisor inclusion, including its normalization at allowed poles. -/
private theorem exists_local_divisorLift (D : WeilDivisor X) (x : X) (U : Opens X)
    (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U)) (y : U)
    (hb : ((-D y.1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (Subtype.val.extend (divisorSheafSectionsEquiv _ U f).1 0) y.1) :
    ∃ (V : Opens X) (_hyV : y.1 ∈ V) (hVU : V ≤ U)
      (t : (divisorSheaf D).obj.obj (op V)),
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom.app (op V) t =
        (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.map (homOfLE hVU).op f := by
  have := ChartedSpace.t1Space ℂ X
  let A := D + WeilDivisor.ofPoint x
  let F := Subtype.val.extend (divisorSheafSectionsEquiv A U f).1 (0 : X → ℂ)
  have hf : IsDivisorSectionAt A F y.1 :=
    isDivisorSectionAt_extend (divisorSheafSectionsEquiv A U f).2 y
  obtain ⟨g, hg, hFg⟩ := exists_isDivisorSectionAt hf.meromorphicAt hb
  have hk : {z | A z ≤ 0}.indicator g =ᶠ[𝓝[≠] y.1] g := by
    filter_upwards [A.eventually_eq_zero_nhdsNE y.1] with z hz
    exact Set.indicator_of_mem (s := {z | A z ≤ 0}) hz.le g
  have hEq := hf.eventuallyEq_of_nhdsNE (hg.indicator (WeilDivisor.le_add_ofPoint D x))
    (hFg.trans hk.symm)
  obtain ⟨v, hv, hvo, hyv⟩ := eventually_nhds_iff.1
    ((hg.eventually.and (U.isOpen.mem_nhds y.2)).and hEq)
  let V : Opens X := ⟨v, hvo⟩
  have hVU : V ≤ U := fun z hz ↦ (hv z hz).1.2
  let s : divisorSections D V := ⟨g ∘ Subtype.val,
    comp_val_mem_divisorSections fun z hz ↦ (hv z hz).1.1⟩
  refine ⟨V, hyv, hVU, (divisorSheafSectionsEquiv D V).symm s, ?_⟩
  apply (divisorSheafSectionsEquiv A V).injective
  apply Subtype.ext
  funext z
  rw [divisorSheafMapOfLE_app, divisorSheafSectionsEquiv_map]
  simp only [LinearEquiv.apply_symm_apply]
  -- Divisor inclusion is defined by normalization with this indicator on the open carrier.
  change {z : V | A z ≤ 0}.indicator (g ∘ Subtype.val) z =
    (divisorSheafSectionsEquiv A U f).1 ⟨z.1, hVU z.2⟩
  calc
    _ = {z | A z ≤ 0}.indicator g z.1 := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply]
    _ = F z.1 := (hv z.1 z.2).2.symm
    _ = (divisorSheafSectionsEquiv A U f).1 ⟨z.1, hVU z.2⟩ :=
      Subtype.val_injective.extend_apply (divisorSheafSectionsEquiv A U f).1
        (0 : X → ℂ) (⟨z.1, hVU z.2⟩ : U)


/-- The old and point-twisted divisor sheaves, followed by coefficient extraction. -/
def pointTwistSequence (D : WeilDivisor X) (x : X) [∀ U : Opens X, Decidable (x ∈ U)] :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)) :=
  ShortComplex.mk (divisorSheafMapOfLE (D := D) (E := D + WeilDivisor.ofPoint x)
    (by exact WeilDivisor.le_add_ofPoint D x)) (pointTwistMap D x)
    (by exact divisorSheafMapOfLE_comp_pointTwistMap D x)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The first object of the point-twist sequence is the original divisor sheaf. -/
@[simp]
theorem pointTwistSequence_X₁ (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    (pointTwistSequence D x).X₁ = divisorSheaf D := by rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The middle object is the point-twisted divisor sheaf. -/
@[simp]
theorem pointTwistSequence_X₂ (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    (pointTwistSequence D x).X₂ = divisorSheaf (D + WeilDivisor.ofPoint x) := by rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The final object is the coefficient skyscraper sheaf. -/
@[simp]
theorem pointTwistSequence_X₃ (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    (pointTwistSequence D x).X₃ =
      skyscraperSheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ)) := by rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A section annihilated by the new-coefficient morphism satisfies the old order bound at
every point, so it comes locally from the old divisor sheaf. -/
private theorem old_order_bound_of_pointTwistMap_eq_zero (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] {U : Opens X}
    (f : (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.obj (op U))
    (hf : (pointTwistMap D x).hom.app (op U) f = 0) (y : U) :
    ((-D y.1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (Subtype.val.extend (divisorSheafSectionsEquiv _ U f).1 0) y.1 := by
  by_cases hy : y.1 = x
  · have hx : x ∈ U := hy ▸ y.2
    have hc : sectionPointTwistCoefficient D x U hx f = 0 := by
      rw [← pointTwistMap_app_of_mem D x hx, ConcreteCategory.comp_apply, hf, map_zero]
    have hcoef : divisorSections.pointTwistCoefficient D U ⟨x, hx⟩
        (divisorSheafSectionsEquiv _ U f) = 0 := by
      have h := congrArg ULift.down hc
      exact h
    have ho := (divisorSections.pointTwistCoefficient_eq_zero_iff _ hx).1 hcoef
    rw [meromorphicGerms.mem_orderGE, divisorSections.order_toChartGerm] at ho
    simpa only [hy] using ho
  · have hp : (WeilDivisor.ofPoint x) y.1 = 0 := WeilDivisor.coeff_ofPoint_of_ne hy
    have ho :=
      (isDivisorSectionAt_extend (divisorSheafSectionsEquiv _ U f).2 y).neg_le_meromorphicOrderAt
    simpa only [Finsupp.add_apply, hp, add_zero] using ho


/-- **Exactness at the middle of the point-twist sequence.** A zero new coefficient is exactly
the local lifting condition through the old divisor sheaf. -/
theorem pointTwistSequence_exact (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] : (pointTwistSequence D x).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro y
  rw [ShortComplex.moduleCat_exact_iff]
  -- The short-complex objects and arrows are exactly the displayed divisor stalks and maps.
  change ∀ s, (TopCat.Presheaf.stalkFunctor _ y).map (pointTwistMap D x).hom s = 0 →
    ∃ t, (TopCat.Presheaf.stalkFunctor _ y).map
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)).hom t = s
  intro s hs
  obtain ⟨U, hyU, f, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (divisorSheaf (D + WeilDivisor.ofPoint x)).obj s
  have hg : TopCat.Presheaf.germ (skyscraperSheaf (X := TopCat.of X) x
        (ModuleCat.of ℂ (ULift.{u} ℂ))).obj U y hyU ((pointTwistMap D x).hom.app (op U) f) =
      TopCat.Presheaf.germ (skyscraperSheaf (X := TopCat.of X) x
        (ModuleCat.of ℂ (ULift.{u} ℂ))).obj U y hyU 0 := by
    rw [map_zero, ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact hs
  obtain ⟨V, hyV, iVU, _, heq⟩ := TopCat.Presheaf.germ_eq _ y hyU hyU _ _ hg
  let fV := (divisorSheaf (D + WeilDivisor.ofPoint x)).obj.map iVU.op f
  have hz : (pointTwistMap D x).hom.app (op V) fV = 0 := by
    rw [← ConcreteCategory.comp_apply, (pointTwistMap D x).hom.naturality,
      ConcreteCategory.comp_apply]
    exact heq.trans (map_zero _)
  obtain ⟨W, hyW, hWV, t, ht⟩ := exists_local_divisorLift D x V fV ⟨y, hyV⟩
    (old_order_bound_of_pointTwistMap_eq_zero D x fV hz ⟨y, hyV⟩)
  refine ⟨TopCat.Presheaf.germ (divisorSheaf D).obj W y hyW t, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]


/-- Every scalar coefficient lifts to a germ of the point-twisted divisor sheaf. The lift is
represented by the local coordinate monomial of exponent `-D(x)-1`. -/
theorem pointTwistCoefficientStalk_surjective (D : WeilDivisor X) (x : X) :
    Function.Surjective (pointTwistCoefficientStalk D x) := by
  classical
  intro c
  let a := chartAt ℂ x x
  let n := -D x - 1
  have hn : -(D + WeilDivisor.ofPoint x) x = n := by
    have hp : (WeilDivisor.ofPoint x) x = 1 := WeilDivisor.coeff_ofPoint_self _
    simp only [Finsupp.add_apply, hp, n, neg_add, sub_eq_add_neg]
  obtain ⟨U, hx, f, hφ⟩ := exists_section_toChartGerm_eq (D + WeilDivisor.ofPoint x) x
    (meromorphicGerms.monomial a n c.down).1 (by
      rw [hn]
      exact (meromorphicGerms.monomial a n c.down).2)
  have hc : divisorSections.pointTwistCoefficient D U ⟨x, hx⟩ f = c.down := by
    unfold divisorSections.pointTwistCoefficient
    simp only [LinearMap.comp_apply]
    calc
      _ = meromorphicGerms.coeff a n (meromorphicGerms.monomial a n c.down) :=
        congrArg (meromorphicGerms.coeff a n) (Subtype.ext hφ)
      _ = c.down := meromorphicGerms.coeff_monomial n c.down
  let sf := (divisorSheafSectionsEquiv (D + WeilDivisor.ofPoint x) U).symm f
  refine ⟨TopCat.Presheaf.germ (divisorSheaf (D + WeilDivisor.ofPoint x)).obj U x hx sf, ?_⟩
  have he := ConcreteCategory.congr_hom (germ_pointTwistCoefficientStalk D x hx) sf
  rw [ConcreteCategory.comp_apply] at he
  -- The representing section is obtained by the inverse section equivalence.
  exact he.trans (show sectionPointTwistCoefficient D x U hx sf = c from by
    -- The section coefficient reduces to the lifted linear-map composite.
    change ULift.up (divisorSections.pointTwistCoefficient D U ⟨x, hx⟩
      (divisorSheafSectionsEquiv _ U sf)) = c
    rw [LinearEquiv.apply_symm_apply, hc])


/-- The coefficient morphism is surjective on every stalk, with the only nonzero target stalk
at the twist point. -/
theorem pointTwistMap_stalk_surjective (D : WeilDivisor X) (x y : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor _ y).map (pointTwistMap D x).hom) := by
  have := ChartedSpace.t1Space ℂ X
  by_cases hy : y = x
  · subst y
    let e := skyscraperPresheafStalkOfSpecializes (X := TopCat.of X) x
      (ModuleCat.of ℂ (ULift.{u} ℂ)) (specializes_refl x)
    intro z
    obtain ⟨t, ht⟩ := pointTwistCoefficientStalk_surjective D x (e.hom z)
    refine ⟨t, (ModuleCat.mono_iff_injective e.hom).1 inferInstance ?_⟩
    have hstalk : (TopCat.Presheaf.stalkFunctor _ x).map (pointTwistMap D x).hom ≫
        e.hom = pointTwistCoefficientStalk D x := by
      exact ((stalkSkyscraperSheafAdjunction
        (X := TopCat.of X) (C := ModuleCat.{u} ℂ) x).homEquiv _ _).symm_apply_apply
          (pointTwistCoefficientStalk D x)
    have he := ConcreteCategory.congr_hom hstalk t
    exact (ModuleCat.comp_apply _ _ _).symm.trans (he.trans ht)
  · have hn : ¬x ⤳ y := fun h ↦ hy (specializes_iff_eq.1 h).symm
    have hT := skyscraperPresheafStalkOfNotSpecializesIsTerminal (X := TopCat.of X) x
      (ModuleCat.of ℂ (ULift.{u} ℂ)) hn
    have hz : IsZero (TopCat.Presheaf.stalk
        (skyscraperPresheaf (X := TopCat.of X) x (ModuleCat.of ℂ (ULift.{u} ℂ))) y) :=
      (isZero_zero _).of_iso (hT.uniqueUpToIso (isZero_zero _).isTerminal)
    intro z
    have hs := ModuleCat.subsingleton_of_isZero hz
    exact ⟨0, hs.elim _ z⟩

/-- The point-twist coefficient morphism is an epimorphism of actual sheaves. -/
instance pointTwistMap_epi (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] : Epi (pointTwistMap D x) := by
  have : CategoryTheory.Sheaf.IsLocallySurjective (pointTwistMap D x) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks (pointTwistMap D x).hom).2
      (fun y ↦ pointTwistMap_stalk_surjective D x y)
  infer_instance

/-- **The point-twist short exact sequence** of divisor sheaves on a Riemann surface,
`0 → O(D) → O(D+x) → C_x → 0`, using local coefficient extraction at `x`. -/
theorem pointTwistSequence_shortExact (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] : (pointTwistSequence D x).ShortExact := by
  have : Mono (pointTwistSequence D x).f := inferInstanceAs
    (Mono (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)))
  have : Epi (pointTwistSequence D x).g := inferInstanceAs (Epi (pointTwistMap D x))
  exact { exact := pointTwistSequence_exact D x }


omit [IsManifold 𝓘(ℂ) 1 X] in
/-- After identifying its source and target, the first map is the native divisor inclusion. -/
@[simp]
theorem pointTwistSequence_f (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    eqToHom (pointTwistSequence_X₁ D x).symm ≫ (pointTwistSequence D x).f ≫
      eqToHom (pointTwistSequence_X₂ D x) =
        divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x) := by rfl

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The second map of the point-twist sequence extracts the new coefficient. -/
@[simp]
theorem pointTwistSequence_g (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    eqToHom (pointTwistSequence_X₂ D x).symm ≫ (pointTwistSequence D x).g ≫
      eqToHom (pointTwistSequence_X₃ D x) = pointTwistMap D x := by rfl

/-- Identify the point-twist sequence with its displayed divisor inclusion and coefficient
morphism, so functors can use its maps without unfolding the sequence construction. -/
def pointTwistSequenceIso (D : WeilDivisor X) (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)] :
    pointTwistSequence D x ≅ ShortComplex.mk
      (divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint D x)) (pointTwistMap D x)
      (divisorSheafMapOfLE_comp_pointTwistMap D x) :=
  ShortComplex.isoMk (eqToIso (pointTwistSequence_X₁ D x))
    (eqToIso (pointTwistSequence_X₂ D x)) (eqToIso (pointTwistSequence_X₃ D x))
    (by simpa only [eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
          eqToHom_refl, Category.id_comp] using congrArg (eqToHom (pointTwistSequence_X₁ D x) ≫ ·)
            (pointTwistSequence_f D x).symm)
    (by simpa only [eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
          eqToHom_refl, Category.id_comp] using congrArg (eqToHom (pointTwistSequence_X₂ D x) ≫ ·)
            (pointTwistSequence_g D x).symm)

end LocalLifting

end TauCeti.RiemannSurface
