/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Unit
public import TauCeti.AlgebraicTopology.Cohomology.Cap.MayerVietoris.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Signed connecting maps and degree-zero duality

The original oriented circle gives an integral sign test with `2 • δ(D 1) ≠ 0`.
Finite zero-dimensional manifolds test the native degree-zero duality map, including the empty
space and the disconnected two-point space.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module MonoidalCategory Topology TopologicalSpace
open scoped Manifold

namespace TauCeti.Examples.CapMayerVietoris

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)
local notation "S¹" => sphere (0 : ℂ) 1

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

instance : Fact (finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

/-- The original complex unit circle, with the outward-normal homological orientation. -/
def circleOrientation :
    HomologicalOrientation (S¹) (EuclideanSpace ℝ (Fin 1)) 1 :=
  Complex.orientation.sphereOrientation.toHomologicalOrientation (by simp)

/-- Twice the actual fundamental class is nonzero, as seen in its local integral generator. -/
theorem two_smul_circleFundamentalClass_ne_zero :
    (2 : ℤ) • circleOrientation.fundamentalClass (by simp) ≠ 0 := by
  let x : S¹ := ⟨1, by simp⟩
  let e := singularHomologyComplSingletonIsoOfFinrankEq
    (A := ModuleCat.{0} ℤ) ℤₘ
    (chartAt (EuclideanSpace ℝ (Fin 1)) x)
    (mem_chart_source (EuclideanSpace ℝ (Fin 1)) x) (by simp :
      finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 0 + 1)
  intro h
  have hl := congrArg
    (singularHomologyToLocalHomology ℤₘ x 1) h
  simp only [map_zsmul, circleOrientation.singularHomologyToLocalHomology_fundamentalClass,
    map_zero] at hl
  exact (by norm_num : (2 : ℤ) ≠ 0)
    (((circleOrientation x).property.zsmul_eq_zero_iff e).1 hl)

/-- The integral two-arc connecting image of the fundamental class distinguishes opposite signs. -/
theorem two_smul_circleMV_fundamentalClass_ne_zero (p : S¹) :
    (2 : ℤ) • (TopCat.mayerVietorisδ ℤₘ
          (X := TopCat.of (S¹))
          (U := {p}ᶜ) (V := {-p}ᶜ) isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg one_ne_zero p) 1 0)
          (circleOrientation.fundamentalClass (by simp)) ≠ 0 := by
  have := isIso_reducedMayerVietorisδ_sphere ℤₘ p 0
  have hm : Mono (TopCat.mayerVietorisδ ℤₘ
      (X := TopCat.of (S¹))
      (U := {p}ᶜ) (V := {-p}ᶜ) isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg one_ne_zero p) 1 0) := by
    rw [← TopCat.reducedMayerVietorisδ_comp_ι, reducedSingularHomologyι_zero_app]
    apply mono_comp' (by infer_instance)
    exact mono_comp' (by infer_instance) equalizer.ι_mono
  intro h
  apply two_smul_circleFundamentalClass_ne_zero
  apply (ModuleCat.mono_iff_injective _).1 hm
  simpa only [map_zsmul, map_zero] using h

/-- The compactly supported degree-zero class of the constant integral unit on the circle. -/
def circleUnitClass :
    (TopCat.of (S¹)).compactSupportCohomology ℤₘ ℤ ℤₘ 0 :=
  (TopCat.compactSupportCohomologyIsoOfCompactSpace 0).inv
    (((TopCat.of (S¹)).singularCochainComplex ℤₘ ℤ ℤₘ).homologyπ 0
      ((TopCat.of (S¹)).constSingularCocycle ℤ
        (𝟙 ℤₘ)))

/-- The native duality map of the integral unit is the actual oriented fundamental class. -/
theorem circle_duality_unit :
    circleOrientation.dualityMap (by simp) ℤₘ 0 1 rfl
        circleUnitClass = circleOrientation.fundamentalClass (by simp) := by
  rw [circleUnitClass,
    circleOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv]
  have hc := singularCap_constSingularCocycle
    (X := TopCat.of (S¹)) ℤ (ρ_ ℤₘ).inv (ρ_ ℤₘ).hom
    (𝟙 ℤₘ) 1
  rw [hc]
  simp only [MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, ModuleCat.hom_id]
  exact LinearMap.id_apply (R := ℤ) _

/-- The native two-arc connecting image of `D 1` cannot equal its negative. -/
theorem two_smul_circleMV_duality_unit_ne_zero (p : S¹) :
    (2 : ℤ) • (TopCat.mayerVietorisδ ℤₘ
          (X := TopCat.of (S¹))
          (U := {p}ᶜ) (V := {-p}ᶜ) isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg one_ne_zero p) 1 0)
          (circleOrientation.dualityMap (by simp) ℤₘ
            0 1 rfl circleUnitClass) ≠ 0 := by
  rw [circle_duality_unit]
  exact two_smul_circleMV_fundamentalClass_ne_zero p

/-- The global native square on the two arcs of the original circle has the negative sign. -/
theorem circle_signed_square (L : ModuleCat.{0} ℤ) (pole : S¹) :
    let U : Opens (TopCat.of (S¹)) := ⟨{pole}ᶜ, isOpen_compl_singleton⟩
    let V : Opens (TopCat.of (S¹)) := ⟨{-pole}ᶜ, isOpen_compl_singleton⟩
    let hUV : U ⊔ V = ⊤ :=
      SetLike.coe_injective (compl_singleton_union_compl_singleton_neg one_ne_zero pole)
    circleOrientation.dualityMap (by simp) L 0 1 rfl ≫
        TopCat.mayerVietorisδ L U.isOpen V.isOpen
          (congrArg (fun W : Opens (TopCat.of (S¹)) ↦
            (W : Set (S¹))) hUV) 1 0 rfl =
      -(TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV 0 1 rfl ≫
        (circleOrientation.comap (j := (Opens.inclusion' (U ⊓ V)).hom)
          (U ⊓ V).isOpenEmbedding).dualityMap (by simp) L 1 0 (by omega)) := by
  dsimp only
  have h := TauCeti.HomologicalOrientation.dualityMap_mayerVietorisδ L circleOrientation (by simp)
      ⟨{pole}ᶜ, isOpen_compl_singleton⟩ ⟨{-pole}ᶜ, isOpen_compl_singleton⟩
      (SetLike.coe_injective (compl_singleton_union_compl_singleton_neg one_ne_zero pole))
      0 0 rfl
  simp only [Nat.zero_add, pow_one, neg_one_zsmul] at h
  exact h

-- The native integral, zero and characteristic-two coefficient endpoints use the global square.
example (pole : S¹) := circle_signed_square ℤₘ pole
example (pole : S¹) :=
  circle_signed_square (ModuleCat.of ℤ (Fin 0 → ℤ)) pole

example (pole : S¹) :=
  circle_signed_square (ModuleCat.of ℤ (ZMod 2)) pole

section ZeroDimension

local notation "E0" => EuclideanSpace ℝ (Fin 0)

/-- The discrete native atlas on the finite zero-dimensional manifold. -/
local instance finiteChartedSpace (m : ℕ) : ChartedSpace E0 (Fin m) :=
  ChartedSpace.ofDiscreteTopology

/-- The positive point generator, transported along native path classes. -/
def finiteOrientation (m : ℕ) : HomologicalOrientation (Fin m) E0 0 where
  toFun x := localOrientationOfZeroDimChart (chartAt E0 x) (mem_chart_source E0 x) (by simp)
  localOrientationTransport_toFun' := by
    rintro ⟨x⟩ ⟨y⟩ f
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
    have hc := γ.continuous.isConst_of_preconnectedSpace
    have hxy : x = y := by simpa only [γ.source, γ.target] using hc 0 1
    subst y
    have hγ : γ = Path.refl x := by
      apply Path.ext
      funext t
      exact (hc t 0).trans γ.source
    subst γ
    -- The identity of the native fundamental groupoid is the constant-path class.
    change localOrientationTransport (Fin m) E0 0 (𝟙 (FundamentalGroupoid.mk x)) _ = _
    rw [localOrientationTransport_id]
    rfl

/-- The compactly supported degree-zero class of the integral unit on the finite space. -/
def finiteUnitClass (m : ℕ) :
    (TopCat.of (Fin m)).compactSupportCohomology ℤₘ ℤ ℤₘ 0 :=
  (TopCat.compactSupportCohomologyIsoOfCompactSpace 0).inv
    (((TopCat.of (Fin m)).singularCochainComplex ℤₘ ℤ ℤₘ).homologyπ 0
      ((TopCat.of (Fin m)).constSingularCocycle ℤ (𝟙 ℤₘ)))

/-- Degree-zero duality of the actual unit is the native fundamental class, including no points. -/
theorem finite_duality_unit (m : ℕ) :
    (finiteOrientation m).dualityMap (by simp) ℤₘ 0 0 rfl (finiteUnitClass m) =
      (finiteOrientation m).fundamentalClass (by simp) := by
  rw [finiteUnitClass,
    (finiteOrientation m).dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv]
  rw [singularCap_constSingularCocycle (X := TopCat.of (Fin m)) ℤ (ρ_ ℤₘ).inv (ρ_ ℤₘ).hom (𝟙 ℤₘ) 0]
  simp only [MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, ModuleCat.hom_id]
  exact LinearMap.id_apply (R := ℤ) _

-- Empty, one-point and disconnected two-point native degree-zero tests are nonnegative-degree D.
example := finite_duality_unit 0
example := finite_duality_unit 1
example := finite_duality_unit 2

end ZeroDimension

-- The global equation also applies when the intersection is empty.
example (L : ModuleCat.{0} ℤ) :=
  TauCeti.HomologicalOrientation.dualityMap_mayerVietorisδ L circleOrientation (by simp)
    ⊥ ⊤ (bot_sup_eq _) 0 0 rfl

/-- The native empty atlas over the real line. -/
local instance emptyChartedSpace : ChartedSpace ℝ Empty := ChartedSpace.empty ℝ Empty

/-- The native orientation on the empty one-dimensional manifold. -/
def emptyOrientation : HomologicalOrientation Empty ℝ 1 where
  toFun x := (isEmptyElim x : False).elim
  localOrientationTransport_toFun' := by
    intro x y f
    exact (isEmptyElim x.as : False).elim

example (L : ModuleCat.{0} ℤ) :=
  TauCeti.HomologicalOrientation.dualityMap_mayerVietorisδ L emptyOrientation (by simp)
    ⊥ ⊤ (bot_sup_eq _) 0 0 rfl

end TauCeti.Examples.CapMayerVietoris
