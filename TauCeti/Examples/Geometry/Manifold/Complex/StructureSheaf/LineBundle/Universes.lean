/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Basic
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Holomorphic bundle sections in independent universes

The lifted Riemann sphere and a trivial complex line in an independent universe have a nonzero
native holomorphic section. Restriction, linear bundle maps and bundle isomorphisms act on its
original fibre values. The scalar trivialization, zero-rank, literal-empty and disconnected
examples use the same native section sheaves.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Bundle
open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Examples.HolomorphicSectionUniverses

/-- The Riemann sphere in an arbitrary successor universe, with its native topology. -/
abbrev SphereBase := ULift.{u + 1} (OnePoint ℂ)

instance sphereChartedSpace : ChartedSpace ℂ SphereBase.{u} :=
  (Homeomorph.ulift.isLocalHomeomorph).chartedSpaceComap

instance sphereIsManifold : IsManifold 𝓘(ℂ) ω SphereBase.{u} :=
  (Homeomorph.ulift.isLocalHomeomorph).isManifold_chartedSpaceComap

/-- A complex line in a universe independent of the base. -/
abbrev LineFibre := ULift.{v + 1} ℂ

/-- The original model fibre is a complex line. -/
theorem finrank_lineFibre : Module.finrank ℂ LineFibre.{v} = 1 := by
  rw [finrank_ulift, Module.finrank_self]

/-- The constant section with original fibre value `1`. -/
def bundleOne :
    (holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
      (Trivial SphereBase.{u} LineFibre.{v}) :
        TopCat.Sheaf (ModuleCat.{max (u + 1) (v + 1)} ℂ) (TopCat.of SphereBase.{u})).obj.obj
          (op ⊤) :=
  holomorphicSectionSheaf.ofContMDiff (fun _ ↦ ULift.up (1 : ℂ))
    (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_subtypeVal, contMDiff_const⟩)

@[simp]
theorem bundleOne_apply (x : SphereBase.{u}) :
    bundleOne.{u,v} ⟨x, trivial⟩ = ULift.up (1 : ℂ) :=
  holomorphicSectionSheaf.ofContMDiff_apply _ _ _

/-- The actual section is nonzero at native infinity. -/
theorem bundleOne_ne_zero : bundleOne.{u,v} ≠ 0 := by
  intro h
  let p : SphereBase.{u} := ULift.up OnePoint.infty
  have he := congrArg (fun s ↦ s ⟨p, trivial⟩) h
  have hv := (bundleOne_apply.{u,v} p).symm.trans
    (he.trans (holomorphicSectionSheaf.zero_apply ⟨p, trivial⟩))
  exact one_ne_zero (congrArg ULift.down hv)

/-- The native restriction preserves the original fibre value on every open set. -/
theorem restrict_bundleOne_apply (U : Opens SphereBase.{u}) (x : U) :
    (holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
      (Trivial SphereBase.{u} LineFibre.{v})).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        bundleOne.{u,v} x = ULift.up (1 : ℂ) := by
  rw [holomorphicSectionSheaf.map_apply, bundleOne_apply]

/-- Native gluing works for a cover indexed in a third independent universe. -/
theorem exists_gluing_bundleOne :
    ∃ t : (holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
        (Trivial SphereBase.{u} LineFibre.{v})).obj.obj
          (op (iSup (fun _ : ULift.{w} (Fin 2) ↦ (⊤ : Opens SphereBase.{u})))),
      ∀ (i : ULift.{w} (Fin 2)) (x : (⊤ : Opens SphereBase.{u})),
        t ⟨x, le_iSup (fun _ : ULift.{w} (Fin 2) ↦ (⊤ : Opens SphereBase.{u})) i x.property⟩ =
          ULift.up (1 : ℂ) := by
  obtain ⟨t, ht, _⟩ := holomorphicSectionSheaf.existsUnique_gluing
    (I := 𝓘(ℂ)) (F := LineFibre.{v}) (V := Trivial SphereBase.{u} LineFibre.{v})
    (fun _ : ULift.{w} (Fin 2) ↦ (⊤ : Opens SphereBase.{u}))
    (fun _ ↦ bundleOne.{u,v}) (fun _ _ _ _ _ ↦ rfl)
  exact ⟨t, fun i x ↦ (ht i x).trans (bundleOne_apply x)⟩

private theorem contMDiff_fibre :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, LineFibre.{v})) 𝓘(ℂ, LineFibre.{v}) ω
      (fun p : TotalSpace LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) ↦ p.snd) := by
  simpa only [Function.comp_def, Trivial.diffeomorphProd_apply] using
    contMDiff_snd.comp (Trivial.diffeomorphProd 𝓘(ℂ) SphereBase.{u} LineFibre.{v} ω).contMDiff

private theorem contMDiff_twice :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, LineFibre.{v})) (𝓘(ℂ).prod 𝓘(ℂ, LineFibre.{v})) ω
      (fun p : TotalSpace LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) ↦
        TotalSpace.mk' LineFibre.{v} p.proj ((2 : ℂ) • p.snd)) :=
  Trivial.contMDiff_mk_iff.mpr
    ⟨Bundle.contMDiff_proj _,
      ((2 : ℂ) • ContinuousLinearMap.id ℂ LineFibre.{v}).contMDiff.comp contMDiff_fibre⟩

/-- The sheaf map induced by actual multiplication by `2` in each original fibre. -/
def twiceHom :
    holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) ⟶
      holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) :=
  holomorphicSectionSheaf.homOfLinearMap
    (fun _ ↦ (2 : ℂ) • (LinearMap.id : LineFibre.{v} →ₗ[ℂ] LineFibre.{v})) contMDiff_twice

/-- The native sheaf morphism acts on the nonzero section by multiplication by `2`. -/
@[simp]
theorem twiceHom_bundleOne_apply (x : SphereBase.{u}) :
    (twiceHom.{u,v}).hom.app (op ⊤) bundleOne.{u,v} ⟨x, trivial⟩ = ULift.up (2 : ℂ) := by
  rw [twiceHom, holomorphicSectionSheaf.homOfLinearMap_app_apply,
    LinearMap.smul_apply, LinearMap.id_apply, bundleOne_apply]
  exact congrArg ULift.up (mul_one (2 : ℂ))

private theorem contMDiff_neg :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, LineFibre.{v})) (𝓘(ℂ).prod 𝓘(ℂ, LineFibre.{v})) ω
      (fun p : TotalSpace LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) ↦
        TotalSpace.mk' LineFibre.{v} p.proj (-p.snd)) :=
  Trivial.contMDiff_mk_iff.mpr ⟨Bundle.contMDiff_proj _, contMDiff_fibre.neg⟩

/-- Negation is an actual analytic complex-linear bundle isomorphism. -/
def negIso :
    holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) ≅
      holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v} (Trivial SphereBase.{u} LineFibre.{v}) :=
  holomorphicSectionSheaf.isoOfLinearEquiv (fun _ ↦ LinearEquiv.neg ℂ)
    contMDiff_neg contMDiff_neg

/-- The native isomorphism preserves the original fibre while negating the section. -/
@[simp]
theorem negIso_bundleOne_apply (x : SphereBase.{u}) :
    (negIso.{u,v}).hom.hom.app (op ⊤) bundleOne.{u,v} ⟨x, trivial⟩ = ULift.up (-1 : ℂ) := by
  have h := holomorphicSectionSheaf.isoOfLinearEquiv_hom_app_apply
    (I := 𝓘(ℂ)) (fun _ : SphereBase.{u} ↦
      (LinearEquiv.neg ℂ : LineFibre.{v} ≃ₗ[ℂ] LineFibre.{v}))
    contMDiff_neg contMDiff_neg bundleOne.{u,v} ⟨x, trivial⟩
  exact h.trans (congrArg Neg.neg (bundleOne_apply x))

/-- A scalar section uses the original complex coefficients on the large base. -/
def scalarOne : (holomorphicStructureSheafModules 𝓘(ℂ) SphereBase.{u}).obj.obj (op ⊤) :=
  holomorphicStructureSheafModules.ofContMDiff (fun _ ↦ 1) contMDiff_const

/-- A section of the ordinary trivial line over the large base. -/
def ordinaryBundleOne :
    (holomorphicSectionSheaf 𝓘(ℂ) ℂ (Trivial SphereBase.{u} ℂ)).obj.obj (op ⊤) :=
  holomorphicSectionSheaf.ofContMDiff (fun _ ↦ (1 : ℂ))
    (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_subtypeVal, contMDiff_const⟩)

/-- The canonical trivial-bundle isomorphism recovers the original scalar section. -/
theorem trivialIso_ordinaryBundleOne :
    (holomorphicSectionSheaf.trivialIso 𝓘(ℂ) SphereBase.{u}).hom.hom.app (op ⊤)
      ordinaryBundleOne = scalarOne := by
  apply holomorphicStructureSheafModules.ext
  intro x
  rw [holomorphicSectionSheaf.trivialIso_hom_app_apply,
    ordinaryBundleOne, scalarOne, holomorphicSectionSheaf.ofContMDiff_apply,
    holomorphicStructureSheafModules.ofContMDiff_apply]

/-- The affine part of the actual large sphere. -/
def finiteOpen : Opens SphereBase.{u} :=
  ⟨ULift.down ⁻¹' {(OnePoint.infty : OnePoint ℂ)}ᶜ,
    (Homeomorph.ulift.continuous.isOpen_preimage _ OnePoint.isClosed_infty.isOpen_compl)⟩

/-- A finite point of the large sphere lies in its affine part. -/
def finitePoint (z : ℂ) : finiteOpen.{u} :=
  ⟨ULift.up (z : OnePoint ℂ), OnePoint.coe_ne_infty z⟩

private theorem contMDiff_affineCoordinate :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : finiteOpen.{u} ↦ OnePoint.affineChart x.val.down) := by
  have hdown : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : finiteOpen.{u} ↦ x.val.down) :=
    Homeomorph.ulift.isLocalHomeomorph.contMDiff_chartedSpaceComap.comp contMDiff_subtypeVal
  have hchart : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (OnePoint.affineChart : OnePoint ℂ → ℂ) OnePoint.affineChart.source :=
    contMDiffOn_of_mem_maximalAtlas OnePoint.affineChart_mem_maximalAtlas
  exact contMDiffOn_univ.mp (hchart.comp hdown.contMDiffOn (fun x _ ↦ by
    rw [OnePoint.affineChart_source]
    exact x.property))

/-- A nonconstant native local section whose analyticity uses the pulled-back affine chart. -/
def coordinateSection :
    (holomorphicSectionSheaf 𝓘(ℂ) ℂ (Trivial SphereBase.{u} ℂ)).obj.obj (op finiteOpen) :=
  holomorphicSectionSheaf.ofContMDiff (fun x ↦ OnePoint.affineChart x.val.down)
    (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_subtypeVal, contMDiff_affineCoordinate⟩)

@[simp]
theorem coordinateSection_finitePoint (z : ℂ) :
    coordinateSection.{u} (finitePoint z) = z := by
  rw [coordinateSection, holomorphicSectionSheaf.ofContMDiff_apply]
  exact OnePoint.affineChart_coe z

/-- The local section takes different values at the actual finite points `0` and `1`. -/
theorem coordinateSection_not_constant :
    ¬ ∃ c : ℂ, ∀ x : finiteOpen.{u}, coordinateSection x = c := by
  rintro ⟨c, hc⟩
  have h := (hc (finitePoint 0)).trans (hc (finitePoint 1)).symm
  rw [coordinateSection_finitePoint, coordinateSection_finitePoint] at h
  exact zero_ne_one h

/-- The original universe-zero trivial line also has its native constant section. -/
def typeZeroBundleOne :
    (holomorphicSectionSheaf 𝓘(ℂ) ℂ (Trivial (OnePoint ℂ) ℂ)).obj.obj (op ⊤) :=
  holomorphicSectionSheaf.ofContMDiff (fun _ ↦ (1 : ℂ))
    (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_subtypeVal, contMDiff_const⟩)

/-- On a universe-zero base, scalar trivialization followed by `sectionsLinearEquiv`
sends the constant bundle section to the constant function `1`. -/
theorem typeZero_ring_reading (x : OnePoint ℂ) :
    holomorphicStructureSheafModules.sectionsLinearEquiv 𝓘(ℂ) (OnePoint ℂ) (op ⊤)
      ((holomorphicSectionSheaf.trivialIso 𝓘(ℂ) (OnePoint ℂ)).hom.hom.app (op ⊤)
        typeZeroBundleOne) ⟨x, trivial⟩ = 1 := by
  rw [holomorphicStructureSheafModules.sectionsLinearEquiv_apply,
    holomorphicSectionSheaf.trivialIso_hom_app_apply, typeZeroBundleOne,
    holomorphicSectionSheaf.ofContMDiff_apply]

/-- The module of holomorphic sections of a rank-zero trivial bundle is zero over every open. -/
theorem isZero_rankZero_sections (U : Opens SphereBase.{u}) :
    IsZero ((holomorphicSectionSheaf 𝓘(ℂ) (Fin 0 → ℂ)
      (Trivial SphereBase.{u} (Fin 0 → ℂ))).obj.obj (op U)) := by
  let : Subsingleton ((holomorphicSectionSheaf 𝓘(ℂ) (Fin 0 → ℂ)
      (Trivial SphereBase.{u} (Fin 0 → ℂ))).obj.obj (op U)) :=
    ⟨fun s t ↦ holomorphicSectionSheaf.ext fun _ ↦ Subsingleton.elim _ _⟩
  exact ModuleCat.isZero_of_subsingleton _

section Empty

/-- The literal empty base has its native empty complex atlas. -/
local instance emptyChartedSpace : ChartedSpace ℂ PEmpty.{u + 2} :=
  ChartedSpace.empty ℂ PEmpty.{u + 2}

/-- On the literal empty manifold the native section module is zero, with an independent fibre. -/
theorem isZero_empty_sections (U : Opens PEmpty.{u + 2}) :
    IsZero ((holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
      (Trivial PEmpty.{u + 2} LineFibre.{v})).obj.obj (op U)) := by
  let : Subsingleton ((holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
      (Trivial PEmpty.{u + 2} LineFibre.{v})).obj.obj (op U)) :=
    ⟨fun s t ↦ holomorphicSectionSheaf.ext fun x ↦ PEmpty.elim x.val⟩
  exact ModuleCat.isZero_of_subsingleton _

end Empty

/-- An actual holomorphic section has values `0` and `1` on different compact components. -/
def disconnectedSection :
    (holomorphicSectionSheaf 𝓘(ℂ) LineFibre.{v}
      (Trivial (SphereBase.{u} ⊕ SphereBase.{u}) LineFibre.{v})).obj.obj (op ⊤) :=
  holomorphicSectionSheaf.ofContMDiff
    (fun x ↦ Sum.elim (fun _ ↦ (0 : LineFibre.{v})) (fun _ ↦ ULift.up (1 : ℂ)) x.val)
    (Trivial.contMDiff_mk_iff.mpr ⟨contMDiff_subtypeVal,
      (contMDiff_const.sumElim contMDiff_const).comp contMDiff_subtypeVal⟩)

@[simp]
theorem disconnectedSection_inl (x : SphereBase.{u}) :
    disconnectedSection.{u,v} ⟨Sum.inl x, trivial⟩ = 0 :=
  holomorphicSectionSheaf.ofContMDiff_apply _ _ _

@[simp]
theorem disconnectedSection_inr (x : SphereBase.{u}) :
    disconnectedSection.{u,v} ⟨Sum.inr x, trivial⟩ = ULift.up (1 : ℂ) :=
  holomorphicSectionSheaf.ofContMDiff_apply _ _ _

/-- The section on the disconnected base is nonzero despite vanishing on a whole component. -/
theorem disconnectedSection_ne_zero : disconnectedSection.{u,v} ≠ 0 := by
  intro h
  let p : SphereBase.{u} := ULift.up OnePoint.infty
  have he := congrArg (fun s ↦ s ⟨Sum.inr p, trivial⟩) h
  have hv := (disconnectedSection_inr.{u,v} p).symm.trans
    (he.trans (holomorphicSectionSheaf.zero_apply ⟨Sum.inr p, trivial⟩))
  exact one_ne_zero (congrArg ULift.down hv)

end TauCeti.Examples.HolomorphicSectionUniverses
